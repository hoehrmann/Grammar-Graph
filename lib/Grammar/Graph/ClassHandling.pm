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
use Set::IntSpan::Partition;

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

    for my $vertex (@$v) {
      my $char_obj = $self->get_vertex_char_object($vertex);
      $union->U($char_obj);
    }

    my $class = Grammar::Formal::CharClass->new(
      spans => $union,
    );

    my $state = $self->fa_add_state();
    $self->vp_type($state, 'charClass');
    $self->vp_run_list($state, $class->spans->run_list);

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
    $self->get_vertex_char_object($_);
  } @vertices;
  
  my %map = Set::IntSpan::Partition::intspan_partition_map(@classes);
  
  for (my $ix = 0; $ix < @vertices; ++$ix) {
    for (@{ $map{$ix} }) {
    
      my $char_obj = $self->get_vertex_char_object($vertices[$ix]);

      my $class = Grammar::Formal::CharClass->new(spans => $_,
          );

      my $state = $self->fa_add_state();

      $self->vp_type($state, 'charClass');
      $self->vp_run_list($state, $class->spans->run_list);

      $self->_copy_predecessors($vertices[$ix], $state);
      $self->_copy_successors($vertices[$ix], $state);
    }
    
    $self->g->delete_vertex($vertices[$ix]);
  }
  
}

1;

__END__

