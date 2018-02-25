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

use Grammar::Graph::JET;

# Mixins
use Grammar::Graph::Converters;
use Grammar::Graph::Cloning;
use Grammar::Graph::RefHandling;
use Grammar::Graph::ClassHandling;

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

has 'root_name' => (
  is       => 'ro',
  required => 1,
  isa      => Str,
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
);

has 'final_vertex' => (
  is       => 'ro',
  required => 0, # FIXME?
  writer   => '_set_final_vertex',
);

has 'pattern_converters' => (
  is       => 'ro',
  required => 1,
  isa      => HashRef[CodeRef],
  default  => sub { {
#    'Grammar::Formal::NotAllowed' => \&convert_not_allowed,
#    'Grammar::Formal::CharClass' => \&convert_char_class,

    'ref'                    => \&convert_reference,
    'range'                  => \&convert_range,
    'asciiInsensitiveString' => \&convert_ascii_insensitive_string,
    'string'                 => \&convert_case_sensitive_string,
    'grammar'                => \&convert_grammar_root,
    'rule'                   => \&convert_rule,
    'repetition'             => \&convert_bounded_repetition,
    'someOrMore'             => \&convert_some_or_more,
    'empty'                  => \&convert_empty,
    'group'                  => \&convert_group,
    'choice'                 => \&convert_choice,
    'conjunction'            => \&convert_conjunction,
    'exclusion'              => \&convert_subtraction,
    'orderedChoice'          => \&convert_ordered_choice,
    'orderedConjunction'     => \&convert_ordered_conjunction,

    'optional'               => \&convert_optional,
    'oneOrMore'              => \&convert_one_or_more,
    'zeroOrMore'             => \&convert_zero_or_more,
    'greedyOptional'         => \&convert_greedy_optional,
    'greedyOneOrMore'        => \&convert_greedy_one_or_more,
    'greedyZeroOrMore'       => \&convert_greedy_zero_or_more,
    'lazyOptional'           => \&convert_lazy_optional,
    'lazyOneOrMore'          => \&convert_lazy_one_or_more,
    'lazyZeroOrMore'         => \&convert_lazy_zero_or_more,
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
# Encapsulate ...
#####################################################################

sub _find_id_by_shortname {
  my ($self, $shortname) = @_;

  for my $k (keys %{ $self->symbol_table }) {
    next unless $self->symbol_table->{$k}{shortname} eq $shortname;
    return $k;
  }
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
# Utils
#####################################################################

sub get_vertex_char_object {
  my ($self, $v) = @_;
  return unless $self->vertex_isa_charclass($v);
  my $label = $self->vp_run_list($v);
  die unless defined $label;
  die if ref $label;

  return Set::IntSpan->new($label);
}

sub vertex_isa {
  my ($self, $v, $pkg) = @_;

  my $type = $self->vp_type($v);

  return (($type // '') eq $pkg);
}

sub vertex_isa_reference { vertex_isa(@_, 'Reference') };
sub vertex_isa_charclass { vertex_isa(@_, 'charClass') };

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
sub vp_run_list { _vp_property('run_list', @_) }
sub vp_position { _vp_property('position', @_) }

#####################################################################
# Constructor
#####################################################################

#####################################################################
# ...
#####################################################################

sub fa_drop_rules_not_needed_for {
  my ($self, $shortname) = @_;

  # TODO: Just ignore these when expanding references?

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

  my $cloned = Grammar::Graph::JET
    ->from_tree($formal)
    ->make_binary()
    ->to_tree();

  return from_binary_jet($class, $cloned, $shortname, %options);
}

sub from_binary_jet {
  my ($class, $formal, $shortname, %options) = @_;
  my $self = $class->new(root_name => $shortname);

  _add_to_automaton(undef, $formal, $self);
  fa_remove_useless_epsilons($self, $self->g->vertices);

  return $self;
}

sub _add_to_automaton {
  my ($parent, $pattern, $self, $after) = @_;
#  die $pattern unless ref $pattern eq 'ARRAY';

#  warn join "\t", "parent", $parent->[0], "child", $pattern->[0];

  my $converter = $self->find_converter(ref $pattern)
    // $self->find_converter($pattern->[0]);

#  my $parent_arity = $Grammar::Graph::JET::arity{ $parent->[0] // '' };
#  my $pattern_arity = $Grammar::Graph::JET::arity{ $pattern->[0] };

#  warn join "\t", "parent", $parent->[0], "child", $pattern->[0], "parent_arity", $parent_arity->[0] // '';

  my %child_is_independent_sequence = map { $_ => 1 } (
    'rule',
    'choice',
    'orderedChoice',
    'conjunction',
    'orderedConjunction',
    'exclusion',
  );

  if ($converter) {
    if ($child_is_independent_sequence{$parent->[0] // ''}) {

      my $after = [];
      my ($ps, $pf) = $converter->($pattern, $self, $after);

      return ($ps, $pf) unless @$after;

      while (@$after) {
        my ($finalAfter, $final) = @{ pop @$after };
        $self->g->add_edges(
          [ $pf, $finalAfter ],
        );
        $pf = $final;
      }

      return ($ps, $pf);

#      my $x1 = $self->fa_add_state();
#      my $x2 = $self->fa_add_state();

#      $self->vp_type($x1, 'Start');
#      $self->vp_name($x1, "START GROUP " . $after . ' ' . $pattern->[0]);
#      $self->vp_type($x2, 'Final');
#      $self->vp_name($x2, "FINAL GROUP " . $after . ' ' . $pattern->[0]);
#      $self->g->add_edges(
#        [ $x1, $ps ],
#        [ $pf, $x2 ],
#      );
#      return ($x1, $x2);

    } else {
      my ($ps, $pf) = $converter->($pattern, $self, $after);
      my $x1 = $self->fa_add_state();
      my $x2 = $self->fa_add_state();
      return ($ps, $pf);
      
    }
  }

  use Data::Dumper;
  use JSON;
  warn Dumper $pattern;
  warn JSON->new->pretty(1)->encode($pattern);
  
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

