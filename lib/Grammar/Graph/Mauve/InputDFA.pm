package Grammar::Graph::Mauve::InputDFA;
use Modern::Perl;
use YAML::XS;
use Unicode::SetAutomaton;
use Storable;
use Set::IntSpan;

use Set::IntSpan::Partition qw/intspan_partition_map/;

use Data::Dumper;
use List::UtilsBy qw/sort_by nsort_by partition_by max_by/;
use List::Util qw/uniq/;
use List::Util qw/min max shuffle/;
use List::MoreUtils qw/last_index/;

use Data::AutoBimap;

local $Storable::canonical = 1;

sub add_input_dfa_to_data {
  my ($m) = @_;

  my @spans = ([]);

  my %spans_offset_to_list_index;

  for (my $ix = 0; $ix < @{ $m->{spans} }; $ix += 2) {
    my $min_inclusive = $m->{spans}[$ix];
    my $max_exclusive = $m->{spans}[$ix+1];

    next if $min_inclusive  < 0;

    if ($min_inclusive == 0 and $max_exclusive == 0) {
      push @spans, [];
      $spans_offset_to_list_index{ $ix + 2 } = $#spans;
      next;
    }

    push @{ $spans[-1] }, [ $min_inclusive, $max_exclusive - 1 ];
  }

  pop @spans;

  my @int_spans = map {
    Set::IntSpan->new(@$_);
  } @spans;

  die "Spans are not disjoint" if
    grep { @$_ > 1 }
    values %{{ intspan_partition_map(@int_spans) }};

  my $dfa = Unicode::SetAutomaton->new(classes => \@int_spans);

  my $max_state = max map {
    $_->[0], $_->[3]
  } @{ $dfa->{transitions} };

  my @transitions = @{ $dfa->{transitions} };

  my @start_transitions = grep {
    $_->[0] eq $dfa->{start_state}
  } @transitions;

  # Copy transitions from the start state to all accepting states
  # to ensure that the automaton does not need to be reset in loops
  for my $state (0 .. $max_state) {
    next if $state eq $dfa->{start_state};
    next unless exists $dfa->{state_to_disjoint}->{$state};
    push @transitions, map {
      [ $state, @{$_}[1,2,3] ];
    } @start_transitions;
  }

  my @sorted = sort_by {
    my $state = $_;
    my $sets;

    if (exists $dfa->{state_to_disjoint}->{$state}) {
      my $dset = $dfa->{state_to_disjoint}->{$state};
      $sets = $dfa->{disjoint_to_input}->[$dset];
      die unless @$sets == 1;
    }

    # This works because we always more states than inputs
    $sets ? @$sets : ":$state";

  } 0 .. $max_state;

  my $last_class_index = last_index {
    exists $dfa->{state_to_disjoint}->{$_}
  } @sorted;

  my $r = Data::AutoBimap->new(start => 0);

  # 0 = dead state 
  $r->s2n(""); # dead state

  # 1 = start state
  $r->s2n( $dfa->{start_state} ); 

  # 2 = 1st disjoint set, ... then intermediate states
  $r->s2n($_) for @sorted;

  my $num_states = $max_state + 2;

  my @big = ((0) x (256 * $num_states)); 

  for my $t (@transitions) {
    for my $ord ($t->[1] .. $t->[2]) {
      my $src = $r->s2n($t->[0]);
      my $dst = $r->s2n($t->[3]);
      $big[ $src * 256 + $ord ] = $dst;
    }
  }

  $m->{input_dfa_table} = \@big;
  $m->{input_dfa} = {
    dead_state => 0,
    start_state => 1,
    last_accepting_state => $last_class_index,
  };

  for my $vd (@{ $m->{vertices} }) {
    next unless $vd and %$vd;
    next unless $vd->{spans};
    $vd->{input_dfa_class_id} =
      $spans_offset_to_list_index{ $vd->{spans} };
  }

  return;
}

1;

__END__

