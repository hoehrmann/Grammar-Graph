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

1;

__END__

