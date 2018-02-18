package Grammar::Graph::Verdigris;
use Modern::Perl;
use Grammar::Graph::Shamrock;
use YAML::XS;
use Storable qw/dclone/;
use List::UtilsBy qw/sort_by/;

sub _replace_uncoupled_vertices {
  my ($m, $pg, $block_start_pos, $block_end_pos) = @_;
  # FIXME(bh): implement this
}

sub _conditional_vertices {
  my ($m, $pg, $ifX, $fiX) = @_;
  my ($pos1) = $pg->vertex_pos($ifX);
  my ($pos2) = $pg->vertex_pos($fiX);
  my ($fi) = $pg->successors($fiX);

  return unless defined $fi;

  my $fi_id = $pg->vertex_id($fi);
  my $if_id = $m->partner_id($fi_id);

  return (
    $pg->vertex_from_pos_id( $pos1, $if_id ),
    $pg->vertex_from_pos_id( $pos1, $m->p1_id($if_id) ),
    $pg->vertex_from_pos_id( $pos1, $m->p2_id($if_id) ),
    $fi,
    $pg->vertex_from_pos_id( $pos2, $m->p1_id($fi_id) ),
    $pg->vertex_from_pos_id( $pos2, $m->p2_id($fi_id) ),
  );
}

sub _handle_ifX_fiX {
  my ($m, $pg, $e) = @_;

  my %actions = (
    # FIXME: bad comments
    # FIXME: should be FAILED and SUCCEEDED and indeterminate
    # $if1 has successors:     0000000011111111
    # $if1 has edge to $fi1:   0000111100001111
    # $if2 has successors:     0011001100110011
    # $if2 has edge to $fi2:   0101010101010101
    '#conjunction'         => '___0_______w0_w3',
    '#ordered_conjunction' => '___0_______w0_w1',
    '#ordered_choice'      => '___2_______w1_11',
    '#exclusion'           => '___0_______01_w0',
  );
  
  my ($if, $if1, $if2, $fi, $fi1, $fi2) =
    _conditional_vertices($m, $pg, @$e);

  return unless defined $fi;

  # TODO(bh): not sure about this
  return unless $pg->has_edge($if, $e->[0]);

  my $maybe = sub {
    my ($ifX, $fiX) = @_;
    return $pg->successors($ifX) && $pg->predecessors($fiX);
  };

  my $aix = (($maybe->($if1, $fi1))        << 3)
          | (($pg->has_edge($if1, $fi1))   << 2)
          | (($maybe->($if2, $fi2))        << 1)
          | (($pg->has_edge($if2, $fi2))   << 0);

  my $name = $m->name( $pg->vertex_id($if) );
  my $action = substr $actions{ $name }, $aix, 1;

  if ($action eq 'w') {
    # We cannot make a decision yet
    return $e;
  }
  
  my $label1 = $pg->get_edge_label($if1, $fi1);
  my $label2 = $pg->get_edge_label($if2, $fi2);

  $pg->delete_edge($if2, $fi2);
  $pg->delete_edge($if1, $fi1);

  if ($action eq '0') {
    # Take neither
    return;

  } elsif ($action eq '1') {
    # Take first
    return _contract_path($m, $pg, $if, $if1, $label1, $fi1, $fi);
    
  } elsif ($action eq '2') {
    # Take second
    return _contract_path($m, $pg, $if, $if2, $label2, $fi2, $fi);

  } elsif ($action eq '3') {
    # Take both
    return
      _contract_path($m, $pg, $if, $if2, $label2, $fi2, $fi),
      _contract_path($m, $pg, $if, $if1, $label1, $fi1, $fi);

  } else {
    ...
  }

  return;
}

sub _is_possible_edge {
  my ($m, $pg, $srcv, $dstv) = @_;
  my ($srcpos, $srcid) = $pg->vertex_pos_id($srcv);
  my ($dstpos, $dstid) = $pg->vertex_pos_id($dstv);
  return 0 if $m->is_push_vertex($srcid)
          and $m->is_pop_vertex($dstid)
          and $m->partner_id($srcid) ne $dstid;

  # FIXME: possibly incomplete

  return 1;
}

sub _contract_path {
  my ($m, $pg, $p, $src, $label, $dst, $s) = @_;

  return unless _is_possible_edge($m, $pg, $p, $s);

  $pg->merge_edge_label($p, $s, [
    $pg->get_edge_label($p, $src),
    $src,
    $label,
    $dst,
    $pg->get_edge_label($dst, $s),
  ]);

  return [$p, $s];
}

sub _can_handle_edge {
  my ($m, $pg, $e) = @_;

  my ($src, $dst) = @$e;
  my ($srcpos, $srcid, $dstpos, $dstid) = $pg->edge_to_4tuple(@$e);
  
  # Ignore edges like Final->Start
  return unless $m->is_push_vertex($srcid);

  # Ignore edges like Start->Start or If->If1
  return if $m->type( $m->partner_id($srcid) ) ne $m->type( $dstid );

  die unless $m->is_pop_vertex( $dstid );

  # skip edges that are not currently present
  return unless $pg->has_edge($src, $dst);

  # This should not happen, but in any case, there is no point.
  return if $srcid eq $m->anon_start_id
        and $dstid eq $m->anon_final_id;

  return 1;
}

sub _handle_edge {
  my ($m, $pg, $e) = @_;

  my ($src, $dst) = @$e;
  my ($srcpos, $srcid, $dstpos, $dstid) = $pg->edge_to_4tuple(@$e);

  # TODO: can be removed if already checked by caller
  die unless _can_handle_edge($m, $pg, $e);

  # TODO: skip start -> ... -> start ... -> final -> ... -> final loops
  if ($m->epsilon_loop($srcid) and $m->epsilon_loop($dstid)) {
    warn "FIXME(bh): implement this";
    return;
  }

  # Remove illegal edges like start<X> -> final<Y>
  if ($m->partner_id($srcid) ne $dstid) {
    $pg->delete_edge($src, $dst);
    return;
  }

  if ($m->type($srcid) eq 'If1' or $m->type($srcid) eq 'If2') {
    return _handle_ifX_fiX($m, $pg, $e);
  }

  my $label = $pg->get_edge_label($src, $dst);
  $pg->delete_edge($src, $dst);

  my @result;

  unless ($pg->predecessors($src) and $pg->successors($dst)) {
    warn; # would be okay, but
  }

  warn " AHA " if grep {
    my ($dstpos, $dst) = $pg->vertex_pos_id($_);
    $m->is_terminal_vertex( $dst );
  } $pg->successors($dst);

  for my $p ($pg->predecessors($src)) {
    for my $s ($pg->successors($dst)) {
      push @result,
        _contract_path($m, $pg, $p, $src, $label, $dst, $s);
    }
  }

  return @result;
}

sub verdigris {
  my ($cleanup, $m, $pg, $block_start_pos, $block_end_pos, $hx) = @_;

  _replace_uncoupled_vertices($m, $pg, $block_start_pos, $block_end_pos);

  my $ultimate = [
    $pg->vertex_from_pos_id( 0, $m->{grammar}{anon_start_id} ),
    # FIXME: use real length
    $pg->vertex_from_pos_id( $block_end_pos, $m->{grammar}{anon_final_id} ),
  ];

  my $round = 1;
  while (1) {
    
    warn "round " . $round++;

    do { warn; last } if $round > 80;

    # TODO(bh): use edge iterator provided by graph implementation
    my @edges = sort_by {
      my ($srcpos, $src, $dstpos, $dst) = $pg->edge_to_4tuple(@$_);
      pack 'N4', $srcpos, $src, $dstpos, $dst;
    } $pg->edges;

    my @more;
    for my $e (@edges) {

      my ($srcpos, $src, $dstpos, $dst) = $pg->edge_to_4tuple(@$e);
      my ($srcv, $dstv) = @$e;

      next unless _can_handle_edge($m, $pg, $e);

      # TODO: this can be done with a traversal beforehand
      # TODO: and is only needed when handling a small block
      my $t1 = grep {
        $pg->vertex_pos($_) < $srcpos;
      } $pg->_g->all_predecessors($srcv);

      my $t2 = grep {
        $pg->vertex_pos($_) > $dstpos;
      } $pg->_g->all_successors($dstv);

      warn join "\t", "skipping", $srcpos, $src, $dstpos, $dst, "between", $block_start_pos, "and", $block_end_pos 
        unless $t1 and $t2;

      next unless $t1 and $t2;

      warn join "\t", "verdigris", $srcpos, $src, $dstpos, $dst, $block_start_pos, $block_end_pos;

      push @more, _handle_edge($m, $pg, $e);
    }

    my %ok = $cleanup->($m, $block_start_pos, $block_end_pos, $pg->edges, @$hx);

    my @delete = grep {
      my ($srcv, $dstv) = @$_;
      not $ok{ $srcv } or not $ok{ $dstv } 
    } $pg->edges;

    $pg->delete_edge(@$_) for @delete;

    last unless @more;

    last if $pg->has_edge(@$ultimate);
  }

  # FIXME: this return value doesn't make sense for block processing
  return $pg->get_edge_label(@$ultimate)  
}

sub _transform_nested_array {
  my ($m, $pg, @x) = @_;

  # FIXME: arguments ought to be $p $d $s
  # TODO: hide conditionals

  my $root = [];
  my @todo = @x;
  my @stack = ($root);
  my @flat;

  while (@todo) {
    my $current = shift @todo;

    if (ref $current) {
      unshift @todo, @$current;
      next;
    }

    my ($pos, $v) = $pg->vertex_pos_id($current);

    if ($m->is_push_vertex($v)) {
      my $name = join ':',
        map { $_ // "" } $m->type($v), $m->name($v);
      my $new = [ $name, [], $pos, undef ];
      push @{ $stack[-1][1] }, $new;
      push @stack, $new;
      next;
    }

    if ($m->is_pop_vertex($v)) {
      $stack[-1][3] = $pos;
      pop @stack;
      next;
    }

    ...
  }

  return $root->[1][0];
}

1;

__END__

map {
    my ($srcpos, $src, $dstpos, $dst) = Grammar::Graph::Shamrock::decode_edge($_);
    my $sv = $pg->vertex_from_pos_id($srcpos, $src);
    my $dv = $pg->vertex_from_pos_id($dstpos, $dst);
    die unless $_->[0] eq $sv and $_->[1] eq $dv;
    [$sv, $dv]
  } 

[ $s, @$d, $f ]

[ p, p->src, src, src->dst, dst, dst->s, s  ]

  $pg->merge_edge_label($p, $s, [
    $pg->get_edge_label($p, $src),
    $src,
    $label,
    $dst,
    $pg->get_edge_label($dst, $s),
  ]);

pvertex(...)->pos/id
pedge(...)

UINT32_MAX









