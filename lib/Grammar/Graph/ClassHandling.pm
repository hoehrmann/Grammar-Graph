package Grammar::Graph;
use 5.012000;
use Modern::Perl;
use List::UtilsBy qw/partition_by/;
use Storable qw/freeze thaw/;
use Set::IntSpan::Partition;
use Set::IntSpan;

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
  
  while (my ($k, $v) = each %groups) {
    next unless @$v > 1;
    my $union = Set::IntSpan->new;

    for my $vertex (@$v) {
      my $char_obj = $self->get_vertex_char_object($vertex);
      $union->U($char_obj);
    }

    my $state = $self->fa_add_state();
    $self->vp_type($state, 'charClass');
    $self->vp_run_list($state, $union->run_list);

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
  # disabled, about to become obsolete
  return;
}

1;

__END__

