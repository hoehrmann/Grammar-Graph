package Grammar::Graph::Stormcloud;
use Modern::Perl;
use Graph::Directed;
use Moo;

has '_g' => (
  is       => 'ro',
  required => 0,
#  isa      => 'Graph::Directed',
  default  => sub {
    return Graph::Directed->new
  },
);

has '_edge_labels' => (
  is       => 'ro',
  required => 0,
  default  => sub { { } },
);

sub from_edge_list {
  my ($class, @edges) = @_;
  my $self = $class->new();
  $self->_g->add_edges(@edges);
  return $self;
}

sub edges {
  my ($self) = @_;
  return $self->_g->edges;
}

sub vertex_pos_id {
  my ($self, $v) = @_;
  my ($pos, $id) = unpack 'N2', $v;
  return $pos, $id;
}

sub vertex_pos {
  my ($self, $v) = @_;
  my ($pos, $id) = $self->vertex_pos_id($v);
  return $pos;
}

sub vertex_id {
  my ($self, $v) = @_;
  my ($pos, $id) = $self->vertex_pos_id($v);
  return $id;
}

sub vertex_from_pos_id {
  my ($self, $pos, $id) = @_;
  return pack 'N2', $pos, $id;
}

sub successors {
  my ($self, $v) = @_;
  return $self->_g->successors($v);
}

sub predecessors {
  my ($self, $v) = @_;
  return $self->_g->predecessors($v);
}

sub has_edge {
  my ($self, $src, $dst) = @_;
  return $self->_g->has_edge($src, $dst);
}

sub has_vertex {
  my ($self, $v) = @_;
  return !!$self->_g->has_vertex($v);
}

sub add_edge {
  my ($self, $src, $dst) = @_;

  warn join "\t", "adding edge",
    $self->vertex_pos_id($src),
    $self->vertex_pos_id($dst) if 1;

  return $self->_g->add_edge($src, $dst);
}

sub delete_edge {
  my ($self, $src, $dst) = @_;
  # TODO: remove label
  return $self->_g->delete_edge($src, $dst);
}

sub delete_vertex {
  my ($self, $v) = @_;
  $self->delete_edge($v, $_) for $self->successors($v);
  return $self->_g->delete_vertex($v);
}

sub edge_to_4tuple {
  my ($self, $src, $dst) = @_;
  return 
    $self->vertex_pos_id($src),
    $self->vertex_pos_id($dst)
  ;
}

sub get_edge_label {
  my ($self, $src, $dst) = @_;
  my $label = $self->_edge_labels->{$src}{$dst};
  $label //= [] if $self->has_edge($src, $dst);
  return $label;
}

sub merge_edge_label {
  my ($self, $src, $dst, $label) = @_;

  $self->add_edge($src, $dst);
  # TODO: for now we just overwrite
  $self->_edge_labels->{$src}{$dst} = $label;
}



1;

__END__

