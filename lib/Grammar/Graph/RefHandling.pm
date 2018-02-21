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

1;

__END__

