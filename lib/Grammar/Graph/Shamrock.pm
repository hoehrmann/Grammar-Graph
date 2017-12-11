package Grammar::Graph::Shamrock;
use Modern::Perl;
use Data::AutoBimap;
use Graph::Directed;
use Graph::SomeUtils ':all';
use List::Util qw/min max shuffle/;
use List::MoreUtils qw/uniq first_index/;
use List::UtilsBy qw/partition_by sort_by nsort_by uniq_by/;
use List::OrderBy;
use Set::IntSpan;
use Storable qw/freeze thaw retrieve dclone/;
use YAML::XS;
use Data::Dumper;
use Grammar::Graph::Mauve::Data;
use Grammar::Graph::Peachpuff;

sub encode_edge {
  die unless @_ == 4;
  my ($srcpos, $src, $dstpos, $dst) = @_;
#  return [ $srcpos, $src, $dstpos, $dst ];
  return [
    pack('N2', $srcpos, $src),
    pack('N2', $dstpos, $dst),
  ];
}

sub decode_edge {
  my ($e) = @_;
#  return @$e;
  die unless @_ == 1;

  return map { unpack 'N2', $_ } @$e;
}

sub _process_heads {
  my ($self, $vertex_matches, $m, $terminal, @heads) = @_;
  my @todo;

  for my $head (@heads) {
    my ($pos1, $src1, $pos2, $dst1) = decode_edge($head);

    unless ($vertex_matches->($m, $dst1, $terminal)) {
      next;
    }

    my @successors = $m->shrunk_successors($dst1);
    my $first = shift @successors;

    # TODO: prefer not to edit
    @$head = @{ encode_edge( $pos1, $src1, $pos2 + 1, $first ) };

    push @todo, $head;

    # This is what makes the process O(N^2)
    for (@successors) {
      push @todo, encode_edge($pos1, $src1, $pos2 + 1, $_);
    }
  }

  return @todo;
}

sub _process_todos {
  my ($self, $m, $todo) = @_;

  my @scc;

  for (my $todo_ix = 0; $todo_ix < @$todo; ++$todo_ix) {
    my $v = $todo->[$todo_ix];
    my ($pos1, $src1, $pos2, $dst1) = decode_edge($v);

    if ($m->is_terminal_vertex($dst1)) {

      # nothing

    } elsif ($m->epsilon_loop($dst1)) {
      for my $r ($m->scc_vertices($dst1)) {
        push @scc, encode_edge( $pos2, $dst1, $pos2, $_ )
          for $m->shrunk_successors($r);
      }

    } else {
      push @$todo, encode_edge( $pos2, $dst1, $pos2, $_ )
        for $m->shrunk_successors($dst1);
    }
  }

  # TODO: why
  push @$todo, @scc;
}

sub _process_step {
  my ($self, $vertex_matches, $m, $terminal, @heads) = @_;

  my @todo = _process_heads($self, $vertex_matches, $m, $terminal, @heads);
  _process_todos($self, $m, \@todo);
  
  return @todo;
}

sub _sort_uniq_first_index {
  my ($m, @todo) = @_;

  @todo = uniq_by {
    my ($srcpos, $src, $dstpos, $dst) = decode_edge($_);
    pack 'N*', $srcpos, $src, $dstpos, $dst;
  } @todo;

  # TODO: statically compute sort key

  @todo = sort_by {
    my ($srcpos, $src, $dstpos, $dst) = decode_edge($_);
    pack 'N*', !$m->is_terminal_vertex($dst), 
      $srcpos, $src, $dstpos, $dst;
  } @todo;

  my $first_non_terminal_ix = first_index {
    my ($pos1, $src1, $pos2, $dst1) = decode_edge($_);
    !$m->is_terminal_vertex($dst1);
  } @todo;

  return $first_non_terminal_ix, @todo;
}

sub process_block {
  my ($self, $m, $vertex_matches, $heads, $begin, $end, $in) = @_;
  my @edges;

  my @heads = @{ Storable::dclone $heads };

  for (my $offset = $begin; $offset < $end; ++$offset) {

#    warn "offset $offset with $#{heads} heads" if $offset % 1000 == 0;

    my @todo = _process_step($self, $vertex_matches, $m, $in->[$offset], @heads);

    my ($first_non_terminal_ix, @sorted) = 
      _sort_uniq_first_index($m, @todo);

    if ($first_non_terminal_ix >= 0) {
      push @edges, splice @sorted, $first_non_terminal_ix;
    }

    @heads = @sorted;
  }

  return \@edges, \@heads;
}

sub begin {
  my ($self, $m, $vertex_matches) = @_;

  my ($edges, $heads) = Grammar::Graph::Shamrock->process_block(
    $m,
    $vertex_matches,
    [ encode_edge( @{ $m->first_edge } ) ],
    0,
    1,
    [ $m->prelude_char ],
  );

  return $edges, $heads;
}

sub finalize {
  my ($self, $m, $vertex_matches, $heads) = @_;

  my ($edges, $heads2) = Grammar::Graph::Shamrock->process_block(
    $m,
    $vertex_matches,
    $heads,
    0,
    1,
    [ $m->postlude_char ],
  );
  
  return $edges, $heads2;
}

sub cleanup_block {
  # TODO: better variable names

  my ($class, $m, $block_start_pos, $block_final_pos, $ex, $h2) = @_;

  my %reachable = Grammar::Graph::Peachpuff::cleanup_edges($m,
    $block_start_pos, $block_final_pos, @$ex, @$h2);

  my @filtered = grep {
    # FIXME: proper decode function
    my ($srcv, $dstv) = @$_;
    ($reachable{$srcv} and $reachable{$dstv});
  } @$ex;

  return @filtered;  
}


1;

__END__

