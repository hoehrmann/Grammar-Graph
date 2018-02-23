package Grammar::Graph;
use 5.012000;
use Modern::Perl;
use Grammar::Formal;
use List::UtilsBy qw/partition_by/;
use List::MoreUtils qw/uniq/;
use List::Util qw/shuffle sum max/;
use Storable qw/freeze thaw/;
use Graph::SomeUtils qw/:all/;
use Graph::Directed;
use Graph::Feather;
use Moo;
use Types::Standard qw/:all/;

#####################################################################
# Helper function to write some forms of repetition to the graph
#####################################################################
sub _bound_repetition {
  my ($min, $max, $child, $fa, $root) = @_;

  # FIXME: rename because it also handles unbounded repetition?

  die if defined $max and $min > $max;
  
  if ($min <= 1 and not defined $max) {
    my $s1 = $fa->fa_add_state;
    my $s2 = $fa->fa_add_state;
    my $s3 = $fa->fa_add_state;
    my $s4 = $fa->fa_add_state;
    my ($ps, $pf) = _add_to_automaton($child, $fa, $root);
    $fa->g->add_edge($s1, $s2);
    $fa->g->add_edge($s2, $ps);
    $fa->g->add_edge($pf, $s3);
    $fa->g->add_edge($s3, $s4);
    $fa->g->add_edge($s2, $s3) if $min == 0;
    $fa->g->add_edge($s3, $s2); # loop
    return ($s1, $s4);
  }
  
  my $s1 = $fa->fa_add_state;
  my $first = $s1;
  
  while ($min--) {
    my ($src, $dst) = _add_to_automaton($child, $fa, $root);
    $fa->g->add_edge($s1, $src);
    $s1 = $dst;
    $max-- if defined $max;
  }

  if (defined $max and $max == 0) {
    my $s2 = $fa->fa_add_state;
    $fa->g->add_edge($s1, $s2);
    return ($first, $s2);
  }  

  do {
    my ($src, $dst) = _add_to_automaton($child, $fa, $root);
    $fa->g->add_edge($s1, $src);
    my $sx = $fa->fa_add_state;
    $fa->g->add_edge($dst, $sx);
    $fa->g->add_edge($s1, $sx); # optional because min <= 0 now
    $fa->g->add_edge($sx, $s1) if not defined $max; # loop
    $s1 = $sx;
  } while (defined $max and --$max);

  my $s2 = $fa->fa_add_state;
  $fa->g->add_edge($s1, $s2);

  return ($first, $s2);
}

#####################################################################
# Helper functions
#####################################################################

sub _pattern_p1 {
  my ($pattern) = @_;

  my $result = eval {
    $pattern->[2]->[0]
  };

  return $result unless $@;

  use Data::Dumper;
  die Dumper $pattern;
}

sub _pattern_p2       { my ($pattern) = @_; $pattern->[2]->[1] }
sub _pattern_p        { my ($pattern) = @_; $pattern->[2]->[0] }
sub _pattern_min      { my ($pattern) = @_; $pattern->[1]->{min} }
sub _pattern_max      { my ($pattern) = @_; $pattern->[1]->{max} }

sub _pattern_first      { my ($pattern) = @_; $pattern->[1]->{first} }
sub _pattern_last      { my ($pattern) = @_; $pattern->[1]->{last} }

sub _pattern_name     { my ($pattern) = @_; $pattern->[1]->{name} }
sub _pattern_position { my ($pattern) = @_; $pattern->[1]->{position} }

sub _pattern_type     { my ($pattern) = @_; $pattern->[0] }

sub _pattern_rules    { my ($pattern) = @_;
  return {
    map { $_->[1]->{name}, $_ }
    grep { $_->[0] eq 'rule' }
    @{ $pattern->[2] }
  };
}

sub _pattern_value    { my ($pattern) = @_;
  return $pattern->[1]->{text} if $pattern->[0] eq 'asciiInsensitiveString';
  return $pattern->[1]->{text} if $pattern->[0] eq 'string';
  die "trying to get value for " . $pattern->[0]
}

#####################################################################
# Collection of sub routines that write patterns to the graph
#####################################################################
sub convert_prose_value {
    ...;

    my ($pattern, $fa, $root) = @_;
    my $s1 = $fa->fa_add_state;
    my $s2 = $fa->fa_add_state(p => $pattern);
    my $s3 = $fa->fa_add_state;
    $fa->g->add_edges(
      [ $s1, $s2 ],
      [ $s2, $s3 ],
    );
    return ($s1, $s3);
  }

sub convert_reference {
    my ($pattern, $fa, $root) = @_;
    my $s1 = $fa->fa_add_state;
    my $s2 = $fa->fa_add_state();

    # FIXME !!!!!!!!!!!!!!!!!!
    $fa->vp_type($s2, 'Reference');
    $fa->vp_name($s2, _pattern_name($pattern));

    my $s3 = $fa->fa_add_state;
    $fa->g->add_edges(
      [ $s1, $s2 ],
      [ $s2, $s3 ],
    );
    return ($s1, $s3);
  }

sub convert_not_allowed {
    my ($pattern, $fa, $root) = @_;
    my $s1 = $fa->fa_add_state;
#    my $s2 = $fa->fa_add_state(p => $pattern);
    my $s3 = $fa->fa_add_state;
#    $fa->g->add_edge($s1, $s2);
#    $fa->g->add_edge($s2, $s3);
    return ($s1, $s3);
  }

sub convert_range {
  my ($pattern, $fa, $root) = @_;

  my $spans = Set::IntSpan->new([[
    _pattern_first($pattern),
    _pattern_last($pattern),
  ]]);

  my $s1 = $fa->fa_add_state;
  my $s2 = $fa->fa_add_state();

  $fa->vp_type($s2, 'Grammar::Formal::CharClass');
  $fa->vp_run_list($s2, $spans->run_list);

  my $s3 = $fa->fa_add_state;
  $fa->g->add_edges(
    [ $s1, $s2 ],
    [ $s2, $s3 ],
  );
  return ($s1, $s3);
}

sub convert_ascii_insensitive_string {
    my ($pattern, $fa, $root) = @_;

    use bytes;

    my @spans = map {
      ["choice", {}, [
        ["range", { first => ord(lc), last => ord(lc) }, []],
        ["range", { first => ord(uc), last => ord(uc) }, []]]]
    } split//, _pattern_value($pattern);

    my $group = ["empty", {}, []];

    while (@spans) {
      $group = ["group", {
        position => _pattern_position($pattern)
      }, [ pop(@spans), $group ] ];
    }

    return _add_to_automaton($group, $fa, $root);
  }

sub convert_case_sensitive_string {
    my ($pattern, $fa, $root) = @_;

    my @spans = map {
      ["range", { first => ord(), last => ord() }, []]
    } split//, _pattern_value($pattern);

    my $group = ["empty", {}, []];

    while (@spans) {
      $group = ["group", {
        position => _pattern_position($pattern)
      }, [ pop(@spans), $group ] ];
    }

    return _add_to_automaton($group, $fa, $root);
  }

sub convert_grammar_root {
  my ($pattern, $fa, $root) = @_;

  my $self = $fa;

  my %map = map {
    $_ => [ _add_to_automaton(_pattern_rules($pattern)->{$_}, $fa) ]
  } keys %{ _pattern_rules($pattern) };

  my $s1 = $self->fa_add_state();
  my $s2 = $self->fa_add_state();

  my $sS = $self->fa_add_state();
  my $sF = $self->fa_add_state();

  $self->vp_type($s1, 'Prelude');
  $self->vp_partner($s1, $s2);

  $self->vp_type($s2, 'Postlude');
  $self->vp_partner($s2, $s1);

  $self->vp_type($sS, 'Start');
  $self->vp_name($sS, '');
  $self->vp_partner($sS, $sF);

  $self->vp_type($sF, 'Final');
  $self->vp_name($sF, '');
  $self->vp_partner($sF, $sS);

  my $shortname = $self->root_name;
  my $id = _find_id_by_shortname($self, $shortname);
  die unless defined $id;
  my $rd = $self->symbol_table->{$id};

=pod

  _copy_predecessors($self, $rd->{start_vertex}, $s1);
  _copy_successors($self, $rd->{start_vertex}, $s1);
  graph_isolate_vertex($self->g, $rd->{start_vertex});

  _copy_predecessors($self, $rd->{final_vertex}, $s2);
  _copy_successors($self, $rd->{final_vertex}, $s2);
  graph_isolate_vertex($self->g, $rd->{final_vertex});

  $self->g->add_edge($rd->{start_vertex}, $s1);
  $self->g->add_edge($s2, $rd->{final_vertex});

=cut

  $fa->g->add_edges(
    [ $sS, $s1 ],
    [ $s1, $rd->{start_vertex} ],
    [ $rd->{final_vertex}, $s2 ],
    [ $s2, $sF ],
  );

  $self->_set_start_vertex($sS);
  $self->_set_final_vertex($sF);
}

sub convert_rule {
  my ($pattern, $fa, $root) = @_;
  my $s1 = $fa->fa_add_state;
  my $s2 = $fa->fa_add_state;

  # FIXME(bh): error if already defined?

  my $name = _pattern_name($pattern);

  $fa->symbol_table->{ $name } //= {};
  $fa->symbol_table->{ $name }{start_vertex} = $s1;
  $fa->symbol_table->{ $name }{final_vertex} = $s2;
  $fa->symbol_table->{ $name }{shortname} = _pattern_name($pattern);

  $fa->vp_type($s1, 'Start');
  $fa->vp_name($s1, $name);
  $fa->vp_partner($s1, $s2);
  $fa->vp_position($s1, _pattern_position($pattern));

  $fa->vp_type($s2, 'Final');
  $fa->vp_name($s2, $name);
  $fa->vp_partner($s2, $s1);
  $fa->vp_position($s2, _pattern_position($pattern));

  my ($ps, $pf) = _add_to_automaton(
    _pattern_p($pattern), $fa, [$pattern, $s1, $s2]);
    
  $fa->g->add_edges(
    [ $s1, $ps ],
    [ $pf, $s2 ],
  );

  return ($s1, $s2);
}

sub convert_bounded_repetition {
  my ($pattern, $fa, $root) = @_;
  return _bound_repetition(
    _pattern_min($pattern),
    _pattern_max($pattern),
    _pattern_p($pattern),
    $fa,
    $root
  );
}

sub convert_some_or_more {
  my ($pattern, $fa, $root) = @_;
  return _bound_repetition(
    _pattern_min($pattern),
    undef,
    _pattern_p($pattern),
    $fa,
    $root
  );
}


sub convert_empty {
  my ($pattern, $fa, $root) = @_;
  my $s1 = $fa->fa_add_state;
  my $s2 = $fa->fa_add_state;
  $fa->g->add_edge($s1, $s2);
  return ($s1, $s2);
}

sub convert_choice {
  my ($pattern, $fa, $root) = @_;
  my $s1 = $fa->fa_add_state;
  my $s2 = $fa->fa_add_state;

  my @options;
  my @todo = ( $pattern );

  while (my $current = shift @todo) {
    if ($current->[0] eq 'choice') {
      push @todo, 
        _pattern_p1($current),
        _pattern_p2($current);
    } else {
      push @options, $current;
    }
  }

  while (my $current = shift @options) {
    my ($p1s, $p1f) = _add_to_automaton($current, $fa, $root);

    $fa->g->add_edges(
      [ $s1, $p1s ],
      [ $p1f, $s2 ],
    );
  }

  return ($s1, $s2);
}

sub convert_group {
  my ($pattern, $fa, $root) = @_;
  my $s1 = $fa->fa_add_state;
  my $s2 = $fa->fa_add_state;
  my ($p1s, $p1f) = _add_to_automaton(_pattern_p1($pattern), $fa, $root);
  my ($p2s, $p2f) = _add_to_automaton(_pattern_p2($pattern), $fa, $root);
  $fa->g->add_edges(
    [ $p1f, $p2s ],
    [ $s1, $p1s ],
    [ $p2f, $s2 ],
  );
  return ($s1, $s2);
}

sub convert_conjunction {
  my ($pattern, $fa, $root) = @_;

  return _convert_binary_operation($pattern,
    $fa, $root, "#conjunction");
}

sub convert_ordered_conjunction {
  my ($pattern, $fa, $root) = @_;

  return _convert_binary_operation($pattern,
    $fa, $root, "#ordered_conjunction");
}

sub convert_ordered_choice {
  my ($pattern, $fa, $root) = @_;

  return _convert_binary_operation($pattern,
    $fa, $root, "#ordered_choice");
}

sub convert_optional {
  my ($pattern, $fa, $root) = @_;
  return _add_to_automaton(
    ["choice", {}, [
      ["empty", {}, []],
      _pattern_p($pattern), ]],
    $fa, $root);
}

sub convert_lazy_optional {
  my ($pattern, $fa, $root) = @_;
  return _add_to_automaton(
    ["orderedChoice", {}, [
      ["empty", {}, []],
      _pattern_p($pattern) ]],
    $fa, $root);
}

sub convert_greedy_optional {
  my ($pattern, $fa, $root) = @_;
  return _add_to_automaton(
    ["orderedChoice", {}, [
      _pattern_p($pattern),
      ["empty", {}, []], ]],
    $fa, $root);
}

sub convert_zero_or_more {
  my ($pattern, $fa, $root) = @_;
  return _add_to_automaton(
    ["oneOrMore", {}, [
      ["optional", {}, [
        _pattern_p($pattern) ]]]],
    $fa, $root);
}

sub convert_lazy_zero_or_more {
  my ($pattern, $fa, $root) = @_;
  return _add_to_automaton(
    ["lazyOneOrMore", {}, [
      ["lazyOptional", {}, [
        _pattern_p($pattern) ]]]],
    $fa, $root);
}

sub convert_greedy_zero_or_more {
  my ($pattern, $fa, $root) = @_;
  return _add_to_automaton(
    ["greedyOneOrMore", {}, [
      ["greedyOptional", {}, [
        _pattern_p($pattern) ]]]],
    $fa, $root);
}

sub convert_one_or_more {
  my ($pattern, $fa, $root) = @_;
  return _convert_choosy_one_or_more(
    _pattern_p($pattern), $fa, $root, _pattern_type($pattern));
}

sub convert_greedy_one_or_more {
  my ($pattern, $fa, $root) = @_;
  return _convert_choosy_one_or_more(
    _pattern_p($pattern), $fa, $root, _pattern_type($pattern));
}

sub convert_lazy_one_or_more {
  my ($pattern, $fa, $root) = @_;
  return _convert_choosy_one_or_more(
    _pattern_p($pattern), $fa, $root, _pattern_type($pattern));
}

sub _convert_choosy_one_or_more {
  my ($pattern, $fa, $root, $op) = @_;

  ###################################################################
  # Handles greedyOneOrMore, lazyOneOrMore, and oneOrMore directly,
  # and indirectly greedyZeroOrMore, lazyZeroOrMore, zeroOrMore (call
  # with child pattern wrapped in lazy/greedy Optional pattern). For
  # plain oneOrMore the vertices for the conditional structure stay
  # unlabeled and would simply be removed during cleanup.

  my $start = $fa->fa_add_state();
  my $if = $fa->fa_add_state();
  my $if1 = $fa->fa_add_state();
  my $if2 = $fa->fa_add_state();

  my ($xs, $xf) =
    _add_to_automaton($pattern, $fa, $root);

  my $fi2 = $fa->fa_add_state();
  my $fi1 = $fa->fa_add_state();
  my $fi = $fa->fa_add_state();
  my $final = $fa->fa_add_state();

  if ($op =~ /^lazy/) {
    ($if1, $if2) = ($if2, $if1);
    ($fi1, $fi2) = ($fi2, $fi1);
  }

  if ($op =~ /^(lazy|greedy)/) {

    $fa->vp_name($if, '#ordered_choice');
    $fa->vp_name($fi, '#ordered_choice');

    $fa->vp_type($if, 'If');
    $fa->vp_type($if1, 'If1');
    $fa->vp_type($if2, 'If2');
    $fa->vp_type($fi2, 'Fi2');
    $fa->vp_type($fi1, 'Fi1');
    $fa->vp_type($fi, 'Fi');

    $fa->vp_partner($if, $fi);
    $fa->vp_partner($if1, $fi1);
    $fa->vp_partner($if2, $fi2);
    $fa->vp_partner($fi2, $if2);
    $fa->vp_partner($fi1, $if1);
    $fa->vp_partner($fi, $if);

    $fa->vp_p1($if, $if1);
    $fa->vp_p2($if, $if2);
    $fa->vp_p1($fi, $fi1);
    $fa->vp_p2($fi, $fi2);
  }

  $fa->g->add_edges(
    [ $start, $if ],
    [ $if, $if1 ],
    [ $if, $if2 ],
    [ $fi1, $fi ],
    [ $fi2, $fi ],
    [ $if1, $if ],
    [ $if2, $xs ],
    [ $xf, $fi2 ],
    [ $fi, $fi1 ],
    [ $fi, $if ],
    [ $fi, $final ],
  );

  return ($start, $final);  
}

sub _convert_binary_operation {
  my ($pattern, $fa, $root, $op) = @_;
  my $anon_start = $fa->fa_add_state();
  my $anon_final = $fa->fa_add_state();
  my $if = $fa->fa_add_state();
  my $fi = $fa->fa_add_state();

  my $if_p1 = $fa->fa_add_state();
  my $if_p2 = $fa->fa_add_state();
  my $p1_fi = $fa->fa_add_state();
  my $p2_fi = $fa->fa_add_state();

  $fa->vp_type($if_p1, 'If1');
  $fa->vp_type($if_p2, 'If2');
  $fa->vp_type($p1_fi, 'Fi1');
  $fa->vp_type($p2_fi, 'Fi2');

  $fa->vp_partner($if_p1, $p1_fi);
  $fa->vp_partner($if_p2, $p2_fi);
  $fa->vp_partner($p1_fi, $if_p1);
  $fa->vp_partner($p2_fi, $if_p2);

  $fa->vp_position($if_p1, _pattern_position($pattern));
  $fa->vp_position($if_p2, _pattern_position($pattern));
  $fa->vp_position($p1_fi, _pattern_position($pattern));
  $fa->vp_position($p2_fi, _pattern_position($pattern));

  my ($p1s, $p1f) = _add_to_automaton(_pattern_p1($pattern), $fa, $root);
  my ($p2s, $p2f) = _add_to_automaton(_pattern_p2($pattern), $fa, $root);

  $fa->vp_position($if, _pattern_position($pattern));
  $fa->vp_partner($if, $fi);
  $fa->vp_p1($if, $if_p1);
  $fa->vp_p2($if, $if_p2);
  $fa->vp_name($if, $op);
  $fa->vp_type($if, 'If');

  $fa->vp_position($fi, _pattern_position($pattern));
  $fa->vp_partner($fi, $if);
  $fa->vp_p1($fi, $p1_fi);
  $fa->vp_p2($fi, $p2_fi);
  $fa->vp_name($fi, $op);
  $fa->vp_type($fi, 'Fi');

  $fa->g->add_edges(
    [$if_p1, $p1s],
    [$if_p2, $p2s],
    [$p1f, $p1_fi],
    [$p2f, $p2_fi],

    [$if, $if_p1],
    [$if, $if_p2],
    [$p1_fi, $fi],
    [$p2_fi, $fi],

    [$anon_start, $if],
    [$fi, $anon_final],
  );

  return ($anon_start, $anon_final);
}

sub convert_subtraction {
  my ($pattern, $fa, $root) = @_;
  return _convert_binary_operation($pattern, $fa, $root, "#exclusion");
}

1;

__END__

