#####################################################################
# Grammar::Graph
#####################################################################
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
# Globals
#####################################################################

local $Storable::canonical = 1;

our $VERSION = '0.21';

our %EXPORT_TAGS = ( 'all' => [ qw(
	
) ] );

our @EXPORT_OK = ( @{ $EXPORT_TAGS{'all'} } );

our @EXPORT = qw(
);

#####################################################################
# Attributes
#####################################################################

has 'g' => (
  is       => 'ro',
  required => 1,
#  isa      => 'Graph::Feather',
  default  => sub { Graph::Feather->new },
#  isa      => 'Graph::Directed',
#  default  => sub { Graph::Directed->new },
);

has 'symbol_table' => (
  is       => 'ro',
  required => 1,
  isa      => HashRef,
  default  => sub { {} },
);

has 'start_vertex' => (
  is       => 'ro',
  required => 0, # FIXME?
  writer   => '_set_start_vertex',
#  isa      => Grammar::Graph::Types::Vertex(),
);

has 'final_vertex' => (
  is       => 'ro',
  required => 0, # FIXME?
  writer   => '_set_final_vertex',
#  isa      => Grammar::Graph::Types::Vertex(),
);

has 'pattern_converters' => (
  is       => 'ro',
  required => 1,
  isa      => HashRef[CodeRef],
  default  => sub { {
#    'Grammar::Formal::NotAllowed' => \&convert_not_allowed,
    'Grammar::Formal::CharClass' => \&convert_char_class,

    'ref'                    => \&convert_reference,
    'range'                  => \&convert_range,
    'asciiInsensitiveString' => \&convert_ascii_insensitive_string,
    'string'                 => \&convert_case_sensitive_string,
    'grammar'                => \&convert_grammar_root,
    'rule'                   => \&convert_rule,
    'repetition'             => \&convert_bounded_repetition,
    'someOrMore'             => \&convert_some_or_more,
    'oneOrMore'              => \&convert_one_or_more,
    'zeroOrMore'             => \&convert_zero_or_more,
    'empty'                  => \&convert_empty,
    'group'                  => \&convert_group,
    'choice'                 => \&convert_choice,
    'conjunction'            => \&convert_conjunction,
    'exclusion'              => \&convert_subtraction,
    'orderedChoice'          => \&convert_ordered_choice,
    'orderedConjunction'     => \&convert_ordered_conjunction,
  } },
);

#####################################################################
# Helper functions
#####################################################################
sub _copy_predecessors {
  my ($self, $src, $dst) = @_;
  $self->g->add_edge($_, $dst)
    for $self->g->predecessors($src);
}

sub _copy_successors {
  my ($self, $src, $dst) = @_;
  $self->g->add_edge($dst, $_)
    for $self->g->successors($src);
}

sub _find_endpoints {
  my ($self, $id) = @_;

  my $symbols = $self->symbol_table;
  my $start = $symbols->{$id}{start_vertex};
  my $final = $symbols->{$id}{final_vertex};
  
  return ($start, $final);
}

#####################################################################
# ...
#####################################################################

sub register_converter {
  my ($self, $class, $code) = @_;
  $self->pattern_converters->{$class} = $code;
}

sub find_converter { 
  my ($self, $pkg) = @_;
  return unless defined $pkg;
  return $self->pattern_converters->{$pkg};
}

#####################################################################
# ...
#####################################################################

sub _fa_next_id {
  my ($self) = @_;
  
  my $next_id = $self->g->get_graph_attribute('fa_next_id');
  
  $next_id = do {
    my $max = max(grep { /^[0-9]+$/ } $self->g->vertices) // 0;
    $max + 1;
  } if not defined $next_id or $self->g->has_vertex($next_id);

  $self->g->set_graph_attribute('fa_next_id', $next_id + 1);

  return $next_id;
}

sub fa_add_state {
  my ($self, %o) = @_;
  
  my $expect = $o{p};
  
  my $id = $self->_fa_next_id();
  $self->g->add_vertex($id);

  die if defined $expect;

  return $id;
}

#####################################################################
# Helper function to clone label when cloning subgraph
#####################################################################
sub _clone_label_to {
  my ($self, $k, $to, $want, $map) = @_;

  for my $att ($self->g->get_vertex_attribute_names($k)) {

    my $value = $self->g->get_vertex_attribute($k, $att);

    # Copy first, override later
    $self->g->set_vertex_attribute($to, $att, $value);

    next unless $att =~ /^(p1|p2|partner)$/;

    warn "Trying to clone subgraph without cloning label vertices (" . $att . ")"
      unless $want->{ $value };

    $map->{ $value } //= $self->fa_add_state();

    $self->g->set_vertex_attribute($to, $att, $map->{ $value });
  }
}

#####################################################################
# Clone a subgraph between two vertices
#####################################################################
sub _clone_subgraph_between {
  my ($self, $src, $dst) = @_;

  my %want = map { $_ => 1 }
    graph_vertices_between($self->g, $src, $dst);

  my %map;
  
  for my $k (keys %want) {

    $map{$k} //= $self->fa_add_state();

    _clone_label_to($self, $k, $map{$k}, \%want, \%map);
  }

  while (my ($old, $new) = each %map) {
    for (grep { $want{$_} } $self->g->successors($old)) {
      $self->g->add_edge($new, $map{$_});
    }
  }
  
  return ($map{$src}, $map{$dst}, \%map);
}

sub _clone_non_terminal {
  my ($self, $id) = @_;
  return $self->_clone_subgraph_between(
    $self->symbol_table->{$id}{start_vertex},
    $self->symbol_table->{$id}{final_vertex},
  );
}

#####################################################################
# Generate a graph with all rules with edges over ::References
#####################################################################
sub _fa_ref_graph {
  my ($self) = @_;
  my $symbols = $self->symbol_table;
  my $ref_graph = Graph::Directed->new;

  for my $r1 (keys %$symbols) {
    my $v = $symbols->{$r1};
    for (graph_all_successors_and_self($self->g, $v->{start_vertex})) {
      next unless $self->vertex_isa_reference($_);

      my $r2 = $self->vp_name($_);

      $ref_graph->add_edge("$r1", "$r2");
#      $ref_graph->add_edge("$r1", "$_");
#      $ref_graph->add_edge("$_", "$r2");
    }
  }

  return $ref_graph;
}

#####################################################################
# ...
#####################################################################
sub fa_expand_one_by_copying {
  my ($self, $id) = @_;

  # FIXME(bh): It is evil to steal private variable
  my @ref_vertices = map { @$_ } $self->g->{dbh}->selectall_array(q{
    SELECT
      vertex
    FROM
      Vertex_Attribute
    WHERE
      attribute_name = "type"
      AND attribute_value = "Reference"
  });

  my %id_to_refs = partition_by {
    $self->vp_name($_);
  } @ref_vertices;

  for my $v (@{ $id_to_refs{$id} }) {
    my ($src, $dst) = $self->_clone_non_terminal($id);

    $self->_copy_predecessors($v, $src);
    $self->_copy_successors($v, $dst);
    $self->g->delete_vertex($v);
  }
}

sub fa_expand_references {
  my ($self) = @_;

  my $ref_graph = $self->_fa_ref_graph;
  my $scg = $ref_graph->strongly_connected_graph;

  my @topo = grep { not $ref_graph->has_edge($_, $_) }
    reverse $scg->toposort;

  for my $id (@topo) {
    # NOTE: Relies on @topo containing invalid a+b+c+... IDs
    $self->fa_expand_one_by_copying($id);
  }

  for my $v ($self->g->vertices) {

    next unless $self->vertex_isa_reference($v);

    my $id = $self->vp_name( $v );

    # TODO: explain
    # TODO: remove
#    next if $scg->has_vertex("$id")
#      && !$ref_graph->has_edge("$id", "$id");

    my $v1 = $self->fa_add_state();
    my $v2 = $self->fa_add_state();

    my $name = $self->vp_name($v);

    $self->vp_type($v1, 'Start');
    $self->vp_partner($v1, $v2);
    $self->vp_name($v1, $name);

    $self->vp_type($v2, 'Final');
    $self->vp_partner($v2, $v1);
    $self->vp_name($v2, $name);

    my ($start, $final) = $self->_find_endpoints($id);

    $self->_copy_predecessors($v, $v1);
    $self->_copy_successors($start, $v1);

    $self->_copy_successors($v, $v2);
    $self->_copy_predecessors($final, $v2);
    
    $self->g->delete_vertex($v);
  }

  # FIXME: replace with SQL
  for my $v ($self->g->vertices) {
    die if $self->vertex_isa_reference($v);
  }

}

#####################################################################
# Encapsulate ...
#####################################################################

sub _find_id_by_shortname {
  my ($self, $shortname) = @_;

  for my $k (keys %{ $self->symbol_table }) {
    next unless $self->symbol_table->{$k}{shortname} eq $shortname;
    return $k;
  }
}

sub fa_prelude_postlude {
  my ($self, $shortname) = @_;

  # TODO: move to pattern conversion

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

  $self->g->add_edge($sS, $s1);
  $self->g->add_edge($s1, $rd->{start_vertex});
  $self->g->add_edge($rd->{final_vertex}, $s2);
  $self->g->add_edge($s2, $sF);

  $self->_set_start_vertex($sS);
  $self->_set_final_vertex($sF);
}

#####################################################################
# Remove unlabeled vertices
#####################################################################
sub fa_remove_useless_epsilons {
  my ($graph, @todo) = @_;
  my %deleted;

  for my $v (sort @todo) {
    next unless $graph->vertex_is_useless($v);
    next unless $graph->g->successors($v); # FIXME(bh): why?
    next unless $graph->g->predecessors($v); # FIXME(bh): why?
    for my $src ($graph->g->predecessors($v)) {
      for my $dst ($graph->g->successors($v)) {
        $graph->g->add_edge($src, $dst);
      }
    }
    $deleted{$v}++;
  }
  $graph->g->delete_vertices(keys %deleted);
};

#####################################################################
# Merge character classes
#####################################################################
sub fa_merge_character_classes {
  my ($self) = @_;
  
  my %groups = partition_by {
    freeze [
      [sort $self->g->predecessors($_)],
      [sort $self->g->successors($_)]
    ];
  } grep {
    $self->vertex_isa_charclass($_)
  } $self->g->vertices;
  
  require Set::IntSpan;

  while (my ($k, $v) = each %groups) {
    next unless @$v > 1;
    my $union = Set::IntSpan->new;
    my $min_pos;

    for my $vertex (@$v) {
      my $char_obj = $self->get_vertex_char_object($vertex);
      $union->U($char_obj->spans);
      $min_pos //= $char_obj->position;
      $min_pos = $char_obj->position if defined $char_obj->position
        and $char_obj->position < $min_pos;
    }

    my $class = Grammar::Formal::CharClass->new(
      spans => $union,
      position => $min_pos
    );

    my $state = $self->fa_add_state();
    $self->vp_type($state, ref $class);
    $self->vp_char_obj($state, $class);

    $self->_copy_predecessors($v->[0], $state);
    $self->_copy_successors($v->[0], $state);

    $self->g->delete_vertices(@$v);
  }
}

#####################################################################
# Separate character classes
#####################################################################
sub fa_separate_character_classes {
  my ($self) = @_;
  
  require Set::IntSpan::Partition;
  
  my @vertices = grep {
    $self->vertex_isa_charclass($_)
  } $self->g->vertices;

  my @classes = map {
    $self->get_vertex_char_object($_)->spans;
  } @vertices;
  
  my %map = Set::IntSpan::Partition::intspan_partition_map(@classes);
  
  for (my $ix = 0; $ix < @vertices; ++$ix) {
    for (@{ $map{$ix} }) {
    
      my $char_obj = $self->get_vertex_char_object($vertices[$ix]);

      my $class = Grammar::Formal::CharClass->new(spans => $_,
          position => $char_obj->position);

      my $state = $self->fa_add_state();

      $self->vp_type($state, ref $class);
      $self->vp_char_obj($state, $class);
      $self->vp_position($state, $char_obj->position);

      $self->_copy_predecessors($vertices[$ix], $state);
      $self->_copy_successors($vertices[$ix], $state);
    }
    
    $self->g->delete_vertex($vertices[$ix]);
  }
  
}

#####################################################################
# ...
#####################################################################
sub _delete_unreachables {
  my ($self) = @_;
  my %keep;
  
  $keep{$_}++ for map {
    my @suc = graph_all_successors_and_self($self->g, $_->{start_vertex});
    # Always keep final vertices
    my @fin = $_->{final_vertex};
    (@suc, @fin);
  } values %{ $self->symbol_table };

  $self->g->delete_vertices(grep {
    not $keep{$_}
  } $self->g->vertices);
}

#####################################################################
# Utils
#####################################################################

sub get_vertex_char_object {
  my ($self, $v) = @_;
  return unless $self->vertex_isa_charclass($v);
  my $label = $self->g->get_vertex_attribute($v, 'char_obj');
  die unless defined $label;
  die unless ref $label eq 'Grammar::Formal::CharClass';
  return $label;
}

sub vertex_isa {
  my ($self, $v, $pkg) = @_;

  my $type = $self->vp_type($v);

  return (($type // '') eq $pkg);
}

sub vertex_isa_reference { vertex_isa(@_, 'Reference') };
sub vertex_isa_charclass { vertex_isa(@_, 'Grammar::Formal::CharClass') };

sub vertex_isa_prelude { vertex_isa(@_, 'Prelude') };
sub vertex_isa_postlude { vertex_isa(@_, 'Postlude') };

sub vertex_is_useless {
  my ($self, $v) = @_;
  return ($self->vp_type($v) // 'Empty') eq 'Empty';
}

sub is_terminal_vertex {
  my ($self, $v) = @_;
  # TODO(bh): anomaly with Reference?
  return 1 if $self->vertex_isa_prelude($v);
  return 1 if $self->vertex_isa_postlude($v);
  return 1 if $self->vertex_isa_charclass($v);
  return 0;
}

#####################################################################
# ...
#####################################################################

sub _vp_property {
  my ($name, $self, $vertex, $value) = @_;

  my $old = $self->g->get_vertex_attribute($vertex, $name);

  if (@_ > 3) {
    $self->g->set_vertex_attribute($vertex, $name, $value);
  }

  return $old;
}

sub vp_partner { _vp_property('partner', @_) }
sub vp_p1 { _vp_property('p1', @_) }
sub vp_p2 { _vp_property('p2', @_) }
sub vp_name { _vp_property('name', @_) }
sub vp_type { _vp_property('type', @_) }
sub vp_char_obj { _vp_property('char_obj', @_) }
sub vp_position { _vp_property('position', @_) }

#####################################################################
# Constructor
#####################################################################

#####################################################################
# ...
#####################################################################

sub fa_drop_rules_not_needed_for {
  my ($self, $shortname) = @_;

  my $ref_graph = $self->_fa_ref_graph();
  my $id = $self->_find_id_by_shortname($shortname);
  my %keep = map { $_ => 1 } $id, $ref_graph->all_successors($id);

  delete $self->symbol_table->{$_} for grep {
    not $keep{$_}
  } keys %{ $self->symbol_table };
}

#####################################################################
# ...
#####################################################################
sub fa_truncate {
  my ($self) = @_;

  graph_delete_vertices_except($self->g,
    graph_vertices_between($self->g,
      $self->start_vertex,
      $self->final_vertex),
    $self->start_vertex,
    $self->final_vertex,
  );
}

#####################################################################
# Constructor
#####################################################################
sub from_jet {
  my ($class, $formal, $shortname, %options) = @_;
  my $cloned = Storable::dclone $formal;
  require Parse::ABNF;
  # FIXME(bh): it is evil to call private methods
  Parse::ABNF::_make_jet_binary($cloned);
  return from_binary_jet($class, $cloned, $shortname, %options);
}

sub from_binary_jet {
  my ($class, $formal, $shortname, %options) = @_;
  my $self = $class->new;

  _add_to_automaton($formal, $self);
  fa_remove_useless_epsilons($self, $self->g->vertices);
  _delete_unreachables($self);

  my $id = _find_id_by_shortname($self, $shortname);

  my ($start_vertex, $final_vertex) = _find_endpoints($self, $id);

  $self->_set_start_vertex($start_vertex);
  $self->_set_final_vertex($final_vertex);

  $self->fa_prelude_postlude($shortname);

  return $self;
}

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
sub convert_char_class {
    my ($pattern, $fa, $root) = @_;
    my $s1 = $fa->fa_add_state;
    my $s2 = $fa->fa_add_state();

    $fa->vp_type($s2, ref $pattern);
    $fa->vp_char_obj($s2, $pattern);

    my $s3 = $fa->fa_add_state;
    $fa->g->add_edge($s1, $s2);
    $fa->g->add_edge($s2, $s3);
    return ($s1, $s3);
  }

sub convert_prose_value {
    ...;

    my ($pattern, $fa, $root) = @_;
    my $s1 = $fa->fa_add_state;
    my $s2 = $fa->fa_add_state(p => $pattern);
    my $s3 = $fa->fa_add_state;
    $fa->g->add_edge($s1, $s2);
    $fa->g->add_edge($s2, $s3);
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
    $fa->g->add_edge($s1, $s2);
    $fa->g->add_edge($s2, $s3);
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

    my $char_class = Grammar::Formal::CharClass->new(
      position => _pattern_position($pattern),
      spans => $spans,
    );

    return _add_to_automaton($char_class, $fa, $root);
  }

sub convert_ascii_insensitive_string {
    my ($pattern, $fa, $root) = @_;

    use bytes;

    my @spans = map {
      Grammar::Formal::CharClass
        ->from_numbers_pos(
          _pattern_position($pattern), ord(lc), ord(uc))
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
      Grammar::Formal::CharClass
        ->from_numbers_pos(_pattern_position($pattern), ord)
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

    my %map = map {
      $_ => [ _add_to_automaton(_pattern_rules($pattern)->{$_}, $fa) ]
    } keys %{ _pattern_rules($pattern) };
    
    # root, so we do not return src and dst
    return;
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
      
    $fa->g->add_edge($s1, $ps);
    $fa->g->add_edge($pf, $s2);
    
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

sub convert_one_or_more {
    my ($self, $fa, $root) = @_;
    my $s1 = $fa->add_state;
    my $s2 = $fa->add_state;
    my $s3 = $fa->add_state;
    my $s4 = $fa->add_state;
    ...;
    my ($ps, $pf) = $self->p->add_to_automaton($fa, $root);
    $fa->add_e_transition($s1, $s2);
    $fa->add_e_transition($s2, $ps);
    $fa->add_e_transition($pf, $s3);
    $fa->add_e_transition($s3, $s4);
    $fa->add_e_transition($s3, $s2);
    
    return ($s1, $s4);
  }

sub convert_zero_or_more {
    my ($self, $fa, $root) = @_;
    my $s1 = $fa->add_state;
    my $s2 = $fa->add_state;
    my $s3 = $fa->add_state;
    my $s4 = $fa->add_state;
    ...;
    my ($ps, $pf) = $self->p->add_to_automaton($fa, $root);
    $fa->add_e_transition($s1, $s2);
    $fa->add_e_transition($s2, $ps);
    $fa->add_e_transition($pf, $s3);
    $fa->add_e_transition($s3, $s4);
    $fa->add_e_transition($s3, $s2);
    $fa->add_e_transition($s2, $s3); # zero
    
    return ($s1, $s4);
  }

sub convert_empty {
    my ($pattern, $fa, $root) = @_;
    my $s1 = $fa->fa_add_state;
    my $s3 = $fa->fa_add_state;
#    my $s2 = $fa->fa_add_state;
    $fa->g->add_edge($s1, $s3);
#    $fa->g->add_edge($s2, $s3);
    return ($s1, $s3);
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
      $fa->g->add_edge($s1, $p1s);
      $fa->g->add_edge($p1f, $s2);
    }

    return ($s1, $s2);
  }

sub convert_group {
    my ($pattern, $fa, $root) = @_;
    my $s1 = $fa->fa_add_state;
    my $s2 = $fa->fa_add_state;
    my ($p1s, $p1f) = _add_to_automaton(_pattern_p1($pattern), $fa, $root);
    my ($p2s, $p2f) = _add_to_automaton(_pattern_p2($pattern), $fa, $root);
    $fa->g->add_edge($p1f, $p2s);
    $fa->g->add_edge($s1, $p1s);
    $fa->g->add_edge($p2f, $s2);
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

    $fa->g->add_edge($if_p1, $p1s);
    $fa->g->add_edge($if_p2, $p2s);
    $fa->g->add_edge($p1f, $p1_fi);
    $fa->g->add_edge($p2f, $p2_fi);

    $fa->g->add_edge($if, $if_p1);
    $fa->g->add_edge($if, $if_p2);
    $fa->g->add_edge($p1_fi, $fi);
    $fa->g->add_edge($p2_fi, $fi);

    $fa->g->add_edge($anon_start, $if);
    $fa->g->add_edge($fi, $anon_final);
    
    return ($anon_start, $anon_final);
}

sub convert_subtraction {
  my ($pattern, $fa, $root) = @_;
  return _convert_binary_operation($pattern, $fa, $root, "#exclusion");
}

sub _add_to_automaton {
  my ($pattern, $self, $root) = @_;
#  die $pattern unless ref $pattern eq 'ARRAY';


  my $converter = $self->find_converter(ref $pattern)
    // $self->find_converter($pattern->[0]);
  if ($converter) {
    return $converter->($pattern, $self, $root);
  }

  use Data::Dumper;
  use JSON;
  warn Dumper $root;
  warn JSON->new->pretty(1)->encode($root);
  
  die "no converter for " . $pattern->[0];

  ...;

  my $s1 = $self->fa_add_state;
  my $s2 = $self->fa_add_state(p => $pattern);
  my $s3 = $self->fa_add_state;
  $self->g->add_edge($s1, $s2);
  $self->g->add_edge($s2, $s3);
  return ($s1, $s3);
}

1;

__END__

=head1 NAME

Grammar::Graph - Graph representation of formal grammars

=head1 SYNOPSIS

  use Grammar::Graph;
  my $g = Grammar::Graph->from_grammar_formal($formal);
  my $symbols = $g->symbol_table;
  my $new_state = $g->fa_add_state();
  ...

=head1 DESCRIPTION

Graph representation of formal grammars.

=head1 METHODS

=over

=item C<from_grammar_formal($grammar_formal)>

Constructs a new C<Grammar::Graph> object from a L<Grammar::Formal>
object. C<Grammar::Graph> derives from L<Graph>. The graph has a
graph attribute C<symbol_table> with an entry for each rule identifying
C<start_vertex>, C<final_vertex>, C<shortname>, and other properties.

=item C<fa_add_state(p => $label)>

Adds a new vertex to the graph and optionally labeles it with the
supplied label. The vertex should be assumed to be a random integer.
Care should be taken when adding vertices to the graph through other
means to avoid clashes.

=item C<fa_expand_references()>

Modifies the graph such that vertices are no longer labeled with 
C<Grammar::Formal::Reference> nodes provided there is an entry for
the referenced symbol in the Graph's C<symbol_table>. Recursive and
cyclic references are linearised by vertices labeled with special
C<Grammar::Graph::Start> and C<Grammar::Graph::Final> nodes, and
they in turn are protected by C<Grammar::Graph::Prefix> and linked
C<Grammar::Graph::Suffix> nodes (the former identify the rule, the
latter identify the reference) to ensure the nesting relationship
can be fully recovered.

=item C<fa_merge_character_classes()>

Vertices labeled with a C<Grammar::Formal::CharClass> node that share
the same set of predecessors and successors are merged into a single
vertex labeled with a C<Grammar::Formal::CharClass> node that is the
union of original vertices.

=item C<fa_separate_character_classes()>

Collects all vertices labeled with a C<Grammar::Formal::CharClass> node
in the graph and replaces them with vertices labeled with
C<Grammar::Formal::CharClass> nodes such that an input symbol matches
at most a single C<Grammar::Formal::CharClass>.

=item C<fa_remove_useless_epsilons()>

Removes vertices labeled with nothing or C<Grammar::Formal::Empty> nodes
by connecting all predecessors to all successors directly. The check for
C<Grammar::Formal::Empty> is exact, derived classes do not match.

=back

=head1 EXPORTS

None.

=head1 AUTHOR / COPYRIGHT / LICENSE

  Copyright (c) 2014-2017 Bjoern Hoehrmann <bjoern@hoehrmann.de>.
  This module is licensed under the same terms as Perl itself.

=cut

