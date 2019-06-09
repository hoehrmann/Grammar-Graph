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
use Log::Any;
use XML::LibXML;

use Grammar::Graph::JET;

# Mixins
use Grammar::Graph::Converters;
use Grammar::Graph::Cloning;
use Grammar::Graph::RefHandling;
use Grammar::Graph::ClassHandling;
use Grammar::Graph::Simplify;

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

has '_log' => (
  is       => 'rw',
  required => 0,
  default  => sub {
    Log::Any->get_logger()
  },
);

has 'g' => (
  is       => 'ro',
  required => 1,
  default  => sub { Graph::Feather->new },
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
  default  => sub {
    return {
      'grammar'                => \&convert_grammar_root,
      'rule'                   => \&convert_rule,

      'ref'                    => \&convert_reference,

      'charClass'              => \&convert_char_class,
      'empty'                  => \&convert_empty,
      'group'                  => \&convert_group,
      'choice'                 => \&convert_choice,

      'conjunction'            => \&convert_binary_helper,
      'exclusion'              => \&convert_binary_helper,
      'orderedChoice'          => \&convert_binary_helper,
      'orderedConjunction'     => \&convert_binary_helper,

      'oneOrMore'              => \&convert_one_or_more_helper,
      'greedyOneOrMore'        => \&convert_one_or_more_helper,
      'lazyOneOrMore'          => \&convert_one_or_more_helper,

      'notAllowed'             => \&convert_not_allowed,
    }
  },
);

#####################################################################
# Helper functions
#####################################################################
sub _copy_predecessors {
  my ($self, $src, $dst) = @_;
  $self->g->add_edges(map {
    [ $_, $dst ]
  } $self->g->predecessors($src));
}

sub _copy_successors {
  my ($self, $src, $dst) = @_;
  $self->g->add_edges(map {
    [ $dst, $_ ]
  } $self->g->successors($src));
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

  $graph->_log->debugf("begin fa_remove_useless_epsilons");

  my @filtered = grep {
    $graph->vertex_is_useless($_)
    and
    $graph->g->successors($_)   # FIXME(bh): why? start/final?
    and
    $graph->g->predecessors($_) # FIXME(bh): why? start/final?
  } @todo;

  $graph->_log->debugf("will remove %u vertices", 
    scalar(@filtered));

  for my $v (sort @filtered) {

#    $graph->_log->debugf("removing vertex %s", $v); 

    my @edges;
    my @pred = $graph->g->predecessors($v);
    my @succ = $graph->g->successors($v);

    for my $src (@pred) {
      for my $dst (@succ) {
        push @edges, [ $src, $dst ];
      }
    }

    $graph->g->add_edges(@edges);
    $graph->g->delete_vertex($v);

  }

  $graph->_log->debugf("finished fa_remove_useless_epsilons");

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

  return Set::IntSpan->new(split/,/, $label);
}

sub vertex_isa {
  my ($self, $v, $pkg) = @_;

  my $type = $self->vp_type($v);

  return (($type // '') eq $pkg);
}

sub vertex_isa_reference { vertex_isa(@_, 'Reference') };
sub vertex_isa_charclass { vertex_isa(@_, 'charClass') };

sub vertex_is_useless {
  my ($self, $v) = @_;
  return ($self->vp_type($v) // 'Empty') eq 'Empty';
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
sub vp_name { warn "vp_name for rule called" if ($_[2] // '') eq 'rule'; _vp_property('name', @_) }
sub vp_type { _vp_property('type', @_) }
sub vp_run_list { _vp_property('run_list', @_) }

#####################################################################
# Constructor
#####################################################################

#####################################################################
# ...
#####################################################################

sub fa_drop_rules_not_needed_for {
  my ($self, $shortname) = @_;

  # leftover
  return;
}

#####################################################################
# ...
#####################################################################
sub fa_truncate {
  my ($self) = @_;

  my %keep = map { $_ => 1 } (
    graph_vertices_between($self->g,
      $self->start_vertex,
      $self->final_vertex),
    $self->start_vertex,
    $self->final_vertex,
  );

  for my $v (keys %keep) {
    next unless $self->vp_partner($v);
    delete $keep{ $v }
      unless $keep{ $self->vp_partner($v) };
  }

  $self->g->delete_vertices(grep {
    not $keep{ $_ }
#    and
#    not $keep{ $self->vp_partner($_) // '' }
  } $self->g->vertices);

  return;

  # TODO: remove
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

sub _xml2jet {
  my ($elem) = @_;

  my %attr;

  # TODO: check name, munge name

  for my $x ($elem->attributes) {
    $attr{ $x->nodeName } = $x->nodeValue;
  }

  if (grep { $_ eq $elem->nodeName } 'rule', 'ref') {
    $attr{ def_path } = $elem->nodePath;
  }

  my @kids = map {
    _xml2jet($_)
  } $elem->getChildrenByTagName('*');

  return [ $elem->nodeName, \%attr, \@kids ];
}

sub from_xlx_file {

  my ($class, $path, $shortname) = @_;

  my $doc = XML::LibXML->load_xml(location => $path);

  my $jet = _xml2jet($doc->documentElement);

  return from_jet($class, $jet, $shortname);

}

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

  my $simple = Grammar::Graph::Simplify::simplify({}, $formal);

  _add_to_automaton(undef, $simple, $self);
  fa_remove_useless_epsilons($self, $self->g->vertices);

  return $self;
}

sub _add_to_automaton {
  my ($parent, $pattern, $self, $after) = @_;

#  die $pattern unless ref $pattern eq 'ARRAY';

  my $converter = $self->find_converter(ref $pattern)
    // $self->find_converter($pattern->[0]);

  # TODO: This should not be defined here locally, should be some
  # more global pattern type meta data thingy.
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

    } else {
      my ($ps, $pf) = $converter->($pattern, $self, $after);
      my $x1 = $self->fa_add_state();
      my $x2 = $self->fa_add_state();
      return ($ps, $pf);
      
    }
  }

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

