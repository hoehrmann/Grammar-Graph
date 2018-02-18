package Grammar::Graph::ReplaceBalancedIfs;

sub find_conditional_6tuple {
  my ($g, $if_id) = @_;
  return (
    $if_id,
    $g->vp_p1($if_id),
    $g->vp_p2($if_id),
    $g->vp_partner( $g->vp_p1($if_id) ),
    $g->vp_partner( $g->vp_p2($if_id) ),
    $g->vp_partner( $if_id ),
  );
}

sub replace_balanced_conditional_subgraph {
  my ($g, $if_id) = @_;

  my ($if, $if1, $if2, $fi1, $fi2, $fi) =
    find_conditional_6tuple($g, $if_id);

  # ... dfa ...

  my @dfa_5tuple;
  my %d;

  for my $t (@dfa_5tuple) {
    my ($dsrc, $vsrc, $via, $ddst, $vdst) = @$t;
    $d{$vsrc}{$dsrc}++;
    $d{$vdst}{$ddst}++;
  }

  my @dfa_7tuple;

  my $do_thing = sub {
    my ($state, $v) = @_;
    my @result;
    my $partner = $g->vp_partner($v);

    if (defined $partner) {
      for my $r (keys %{ $d{$v} }) {
        push @result, [ $state, $v, $r ]
      }

    } else {
      push @result, [ $state, $v, 0 ];
    }

    return @result;
  };

  for my $t (@dfa_5tuple) {
    my ($dsrc, $vsrc, $via, $ddst, $vdst) = @$t;
    for my $x ($do_thing->($dsrc, $vsrc)) {
      for my $y ($do_thing->($ddst, $vdst)) {
        push @dfa_7tuple, [ @$x, @$y ];
      }
    }
  }

  # ... add to graph ...

  # ... add labels ...

  my $if_r = $g->fa_add_state();
  my $fi_r = $g->fa_add_state();

  # %c = map old vertex to new cloned vertices

  # connect $if_r to all IfX clones' successors
  for my $ifx ($if1, $if2) {
    $g->g->add_edge($if_r, $_) for
      map { ...->successors($_) }
      @{ $c{ $ifx } } 
  }

  # connect all FiX clones' predecessors to $fi_r
  for my $fix ($fi1, $fi2) {
    $g->g->add_edge($_, $fi_r) for
      map { ...->predecessors($_) }
      @{ $c{ $fix } } 
  }

  # restore edges to/from exterior
  for my $e ($g->g->edges) {
    my ($src, $dst) = @$e;
    
    my ($src_in, $dst_in) = map {
      $interior_vertex_set{ $_ }
    } $src, $dst;

    next unless $src_in ne $dst_in;

    if ($src_in) {
      $g->g->add_edge($_, $dst) for @{ $c{$src} };
    }

    if ($dst_in) {
      $g->g->add_edge($src, $_) for @{ $c{$dst} };
    }
  }
 
  graph_delete_vertices_fast($g->g,
    keys %interior_vertex_set);

  # NOTE: graph needs cleanup after this
  return ($if_r, $fi_r);
}

1;

__END__


%interior_vertex_set

  needs to include, for each vertex, all related vertices 

$start_vertex

  must be included in interior_vertex_set

dfa_graph

for each (state, vertex) with related vertices:

  replace (state, vertex) with (state, vertex, ref_state)
    vertices for each ref_state that contains the related vertex

the related vertex is then always, swapped,

  (ref_state, related vertex, state)

for each exterior vertex exterior
  for each dfa_graph vertex interior
    if input_graph has_edge(exterior, interior.vertex_part)
      output_graph.add_edge(exterior, interior)
    if input_graph has_edge(interior.vertex_part, exterior)
      output_graph.add_edge(interior, exterior)


