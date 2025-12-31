package Test::Deep::Hashbag;
# ABSTRACT: A Test::Deep hash comparator ignoring hash keys

use strict;
use warnings;

use Test::Deep::Cmp;

use Data::Dumper;
use Graph::Directed;
use Graph::MaxFlow qw(max_flow);
use Scalar::Util qw(blessed reftype);
use Test::Deep::Hash ();

use Exporter 'import';
our @EXPORT = qw(hashbag);

sub init {
  my $self = shift;
  my @want = @_;

  unless (@want % 2 == 0) {
    require Carp;
    Carp::croak("hashbag needs an even list of pairs.");
  }

  my %seen;

  for my $i (0 .. (@want / 2 - 1)) {
    my $idx = $i * 2;
    my $k = $want[$idx];

    # Ignore ignore() and other things
    if (ref $k) {
      unless ((blessed($k) // "") eq 'Test::Deep::Ignore') {
        # Prevent mistakes?
        require Carp;
        Carp::croak("hashbag keys must be simple scalars or a Test::Deep::Ignore (ignore()) object, got: " . reftype($k));
      }

      next;
    }

    if ($seen{$k}++) {
      require Carp;
      Carp::croak("Duplicate key '$k' passed to hashbag()");
    }
  }

  $self->{val} = \@want;
}

sub descend {
  my $self = shift;
  my $have = shift;

  unless (ref $have eq 'HASH') {
    my $got = Test::Deep::render_val($have);
    $self->data->{diag} = <<EOM;
got    : $got
expect : A hashref
EOM

    return 0;
  }

  my $want_count = (0 + @{$self->{val}}) / 2;
  my $have_count = keys %$have;

  my %required;
  my @unkeyed;

  # Sort the incoming hashbag into a list of required keys/values, and values
  # who's keys are ignore()
  for my $i (0 .. $want_count - 1) {
    my $idx = $i * 2;

    my $k = $self->{val}->[$idx];
    my $v = $self->{val}->[$idx + 1];

    if (ref $k) {
      push @unkeyed, $v;
    } else {
      $required{$k} = $v;
    }
  }

  # Check all our required stuff first
  my %got = map {
    $_ => $have->{$_}
  } grep {
    exists $have->{$_}
  } keys %required;

  # First check required keys/values simply
  my $hcompare = Test::Deep::Hash->new(\%required);
  return 0 unless $hcompare->descend(\%got);

  # Now check every hash value that has an ignore() key
  my @tocheck = map {
    +{
      k => $_,
      v => $have->{$_}
    }
  } grep { ! exists $required{$_} } keys %$have;

  if (@tocheck != @unkeyed) {
    my $ecount = 0+@unkeyed;
    my $gcount = 0+@tocheck;

    # Turn keys into sorted list of keys with single quotes around them,
    # escape \ and ' so "foo'bar" looks like 'foo\'bar'. This should make
    # understanding output easier if we need to diag something.
    my $tocheck_desc = join(", ",
      map {
        my $k = $_->{k};
        $k =~ s/(\\|')/\\$1/g;
        "'$k'"
      } sort { $a->{k} cmp $b->{k} } @tocheck
    );

    $self->data->{diag} = <<EOM;
We expected $ecount ignored() keys, but we found $gcount keys left?
Remaining keys: $tocheck_desc
EOM

    return 0;
  }

  if (@tocheck == 0) {
    return 1;
  }

  my %match_by_got;
  my %match_by_want;

  # Expensiveish ... check every expect against every got once
  for my $i (0..$#unkeyed) {
    my $want = $unkeyed[$i];

    for my $j (0..$#tocheck) {
      if (Test::Deep::eq_deeply_cache($tocheck[$j]->{v}, $unkeyed[$i])) {
        $match_by_got{$j}{$i} = 1;
        $match_by_want{$i}{$j} = 1;
      }
    }
  }

  # Now, imagine we have:
  #
  #   cmp_deeply(
  #     {
  #       laksdjfaf  => 'bob',
  #       xlaksdjfaf => 'bobby',
  #     },
  #     hashbag(
  #       ignore() => re('.*b'),
  #       ignore() => re('.*b.*bb'),
  #     ),
  #     'got our matching resp',
  #   );
  #
  # %match_by_got might look like:
  #
  #   {
  #     0 => {    # 0th got  (bob)
  #       0 => 1, # 1st want ('.*b')
  #     },
  #     1 => {    # 1st got  (bobby)
  #       0 => 1, # 0th want ('.*b')
  #       1 => 1, # 1st want ('.*b.*bb')
  #     },
  #   }
  #
  # Sometimes, matches can match multiple things, and we need to be sure
  # that each matcher is used only once. To do this we, we'll create a
  # directed graph, and then use the Edmonds-Karp algorithm to find the
  # maximum flow of the graph. If the maximum flow is equal to our number of
  # items, we know we found a case where each item matched at least once.
  #
  # In the data above, our gots are g0 (bob) and g1 (bobby), and our matchers
  # are m0 ('.*b'), and m1 ('.*b.*bb'). Our graph will look like
  #
  #            -> g0
  #          /       \
  #   source           -> m0 --> sink
  #          \       /       /
  #            -> g1 ---> m1

  my $max_flow_found = 0;

  my %matchers_used = map { $_ => 0 } 0..$#unkeyed;

  if (%match_by_got) {
    my $graph = Graph::Directed->new;

    for my $g (keys %match_by_got) {
      $graph->add_weighted_edge("source", "g$g", 1);

      for my $m (keys %{$match_by_got{$g}}) {
        $graph->add_weighted_edge("g$g", "m$m", 1);
      }
    }

    for my $m (keys %match_by_want) {
      $graph->add_weighted_edge("m$m", "sink", 1);
    }

    # Generate a flow graph where each edge from the source *should* have
    # a weight of 1 if it was used
    my $flow_graph = max_flow($graph, "source", "sink");

    for my $v ($flow_graph->successors("source")) {
      my $used = $flow_graph->get_edge_weight("source", $v);
      $max_flow_found += $used;

      if ($used) {
        my $k = $v;
        $k =~ s/^g//;

        # Record that in our best case (highest flow) this key matched; to be
        # used in diagnostics later
        $tocheck[$k]{matched} = 1;
      }
    }

    for my $v ($flow_graph->predecessors("sink")) {
      my $used = $flow_graph->get_edge_weight($v, "sink");

      if ($used) {
        my $k = $v;
        $k =~ s/^m//;

        # Record that in our best case (highest flow) this matcher matched; to be
        # used in diagnostics later
        $matchers_used{$k} = 1;
      }
    }

    return 1 if $max_flow_found == @unkeyed;
  }

  my @keys_had_no_match = map { $_->{k} } grep { ! $_->{matched} } @tocheck;

  # Turn keys into sorted list of keys with single quotes around them,
  # escape \ and ' so "foo'bar" looks like 'foo\'bar'. This should make
  # understanding output easier
  my $keys_desc = join(", ",
    map {
      my $k = $_;
      $k =~ s/(\\|')/\\$1/g;
      "'$k'"
    } sort @keys_had_no_match
  );

  my @matchers_had_no_match = map { $unkeyed[$_] } grep {
    ! $matchers_used{$_}
  } keys %matchers_used;

  my $matchers_desc = "\n" . Dumper(\@matchers_had_no_match);

  my $wanted_flow = @unkeyed;

  $self->data->{diag} = <<EOM;
Failed to find all required items in the remaining hash keys.
Expected to match $wanted_flow items, best case match was $max_flow_found.
Keys with no match: $keys_desc
Matchers that failed to match:$matchers_desc
EOM

  return 0;
}

sub diagnostics {
  my ($self, $where, $last) = @_;
  my $diag;

  if ($self->data->{diag}) {
    $diag = "Comparing $where\n" . $self->data->{diag};
  } else {
    $diag = $last->{diag};
    $diag =~ s/\$data/$where what/;
  }

  return $diag;
}

sub hashbag {
  return Test::Deep::Hashbag->new(@_);
}

1;
__END__

=head1 SYNOPSIS

  use strict;
  use warnings;

  use Test::More;
  use Test::Deep;
  use Test::Deep::Hashbag;

  cmp_deeply(
    {
      cat  => 'meow',
      dog  => 'bark bark',
      fish => 'blub',
    },
    hashbag(
      ignore() => 'meow',
      ignore() => re('.*bark.*'),
      fish     => 'blub',
    ),
    'our animals sound about right',
  );

  done_testing;

=head1 DESCRIPTION

This module provides C<hashbag>, which is like L<Test::Deep>'s C<bag()> but
for B<hashes>.

The idea is it lets you test that a hash has certain B<values>, but you don't
know or care what the keys are for those specic values.

=head1 EXPORTS

=head2 hashbag

  cmp_deeply(\%got, hashbag(key => 'val', ignore() => 'val2', ...), $desc);

Takes a list of pairs that are expected to be keys and values. For any keys
that aren't C<ignore()>, those keys must exist and have the values provided
(this will be checked first).

The remaining values (where the keys are C<ignore()>) will then be checked
against the left over values in the input hash.

On failure, the diagnostics will show how many unkeyed items were expected to
match, and how many did match in the best possible case. Any keys that
matches could not be found for will be printed out, as will any matchers that
were not used in this best case.

B<NOTE:>

With complex matches, the printed information may seem misleading can provide
different lists of keys or matchers that didn't match on reruns of the test.
This indicates that some of the matchers can match multiple keys, and during
different test runs they did so in the best case scenario as the matching
order is not deterministic.

=head1 SEE ALSO

L<Test::Deep>

=head1 THANKS

Thanks to rjbs for pointing out a better algorithm than what I had
originally, and to waltman for Graph::MaxFlow which implemented the harder
bits of it.

=cut
