package Grammar::Graph::Peachpuff;
use Modern::Perl;
use List::UtilsBy qw/sort_by/;

sub vertex_from_pos_id {
  return pack 'N2', @_;
}

sub encode_edge         { &Grammar::Graph::Shamrock::encode_edge; }
sub decode_edge         { &Grammar::Graph::Shamrock::decode_edge; }
sub decode_edge_as_pair { 
  die unless @_ == 1;
  my ($e) = @_;
  return @$e;
}

sub cleanup_edges {
  my ($m, $block_start_pos, $block_final_pos, @edges) = @_;

=pod
  return map  {
    my ($srcpos, $src, $dstpos, $dst) = decode_edge($_);
    pack('N2', $srcpos, $src), 1,
    pack('N2', $dstpos, $dst), 1,
  } @edges;
=cut

  my @ordered = sort_by {
    my ($srcpos, $src, $dstpos, $dst) = decode_edge($_);
    pack 'N*', $srcpos, $src, # $m->topological_id($src),
               $dstpos, $dst, # $m->topological_id($dst)
               ;
  } @edges;

  my %ok;
  my %ok2;

=pod
  my $first_edge = [ decode_edge($ordered[0]) ];
  my $last_edge = [ decode_edge($ordered[-1]) ];
  my $lowest_srcpos = $first_edge->[0];
  my $highest_dstpos = $last_edge->[2];

  for (my $ix = 0; $ix < @ordered; ++$ix) {
    my ($srcpos, $src, $dstpos, $dst) = decode_edge($ordered[$ix]);
    last if $srcpos > $first_edge->[0];
    my ($srcv, $dstv) = decode_edge_as_pair($ordered[$ix]);
    warn "ok2 $srcpos,$src";
    $ok2{ $srcv }++;
  }

  for (my $ix = $#ordered; $ix >= 0; --$ix) {
    my ($srcpos, $src, $dstpos, $dst) = decode_edge($ordered[$ix]);
#    warn join " ", $srcpos, $src, "topo", $m->topological_id($src), $dstpos, $dst, "topo", $m->topological_id($dst);
    last if $dstpos < $last_edge->[2];
    my ($srcv, $dstv) = decode_edge_as_pair($ordered[$ix]);
    warn "ok $dstpos,$dst";
    $ok{ $dstv }++;
  }
=cut

  # Edges that start before $block_start_pos or end
  # after $block_final_pos are assumed to be reachable

  # Vertices outside $block_start_pos $block_final_pos
  # are reachable

  for (my $ix = 0; $ix < @ordered; ++$ix) {
    my ($srcpos, $src, $dstpos, $dst) = decode_edge($ordered[$ix]);
    my $srcv = vertex_from_pos_id($srcpos, $src);
    my $dstv = vertex_from_pos_id($dstpos, $dst);
    if ($srcpos <= $block_start_pos) {
#      $ok{$srcv}++;
      $ok2{$srcv}++;
#      warn "NEW ok2 $srcpos,$src";
    }
    if ($dstpos >= $block_final_pos) {
      $ok{$dstv}++;
#      warn "NEW ok $dstpos,$dst";
#      $ok2{$dstv}++;
    }
  }

  for (my $ix = $#ordered; $ix >= 0; --$ix) {
    my ($srcpos, $src, $dstpos, $dst) = decode_edge($ordered[$ix]);
    for my $v ($src, $m->scc_vertices($src)) {
      my $srcv = vertex_from_pos_id($srcpos, $v);
      my $dstv = vertex_from_pos_id($dstpos, $dst);
      $ok{$srcv}++ if ($ok{$dstv});
    }
  }

  for (my $ix = 0; $ix < @ordered; ++$ix) {
    my ($srcpos, $src, $dstpos, $dst) = decode_edge($ordered[$ix]);
    for my $v ($dst, $m->scc_vertices($dst)) {
      my $srcv = vertex_from_pos_id($srcpos, $src);
      my $dstv = vertex_from_pos_id($dstpos, $v);
      $ok2{$dstv}++ if ($ok2{$srcv} and $ok{$dstv});
    }
  }

  for (my $ix = 0; $ix < @ordered; ++$ix) {
    my ($srcpos, $src, $dstpos, $dst) = decode_edge($ordered[$ix]);
#    warn join "\t", "cleanup_edges", $srcpos, $src, $dstpos, $dst;
  }

use YAML::XS;
#warn Dump \%ok;
#warn Dump \%ok2;
#die;

  return %ok2;
}

1;

__END__

