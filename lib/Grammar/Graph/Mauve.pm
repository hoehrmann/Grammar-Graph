#####################################################################
# Grammar::Graph::Mauve
#####################################################################
package Grammar::Graph::Mauve;
use 5.012000;
use Modern::Perl;
use Grammar::Formal;
use List::UtilsBy qw/partition_by sort_by nsort_by/;
use List::MoreUtils qw/uniq/;
use List::Util qw/shuffle sum max/;
use Storable qw/freeze thaw/;
use Graph::SomeUtils qw/:all/;
use Graph::Directed;
use Memoize qw/memoize/;
use Grammar::Graph::Mauve::Data;
use Grammar::Graph::Mauve::InputDFA;

local $Storable::canonical = 1;

sub _get_epsilon_loop_data {
  my ($g, $vertices) = @_;

  my $p = $g->_graph_copy_graph_without_terminal_out_edges();
  my %result;
  for my $v ($p->vertices) {
    $result{$v} = grep { $_ eq $v } $p->all_successors($v);
  }

  return %result;
}

sub _get_scc_data {
  my ($g, $vertices) = @_;
  my %v2scc = $g->_create_vertex_to_scc();

  my %result;

  for my $v (keys %v2scc) {
    $result{$v} = [ sort split/\+/, $v2scc{$v} ];
  }

  return %result;
}

sub _get_topological_data {
  my ($g, $vertices) = @_;
  my %v2t = $g->_create_vertex_to_topological();
  return %v2t;
}

sub _graph_all_successors_cond {
  my ($g, $source, $cond) = @_;
  $cond //= sub { 1 };
  my %seen;
  my @todo = ($source);
  my %ok;
  while (defined(my $v = pop @todo)) {
    $ok{$_}++ for $g->successors($v);
    push @todo, grep {
      $cond->($_) and not $seen{$_}++
    } $g->successors($v);
  }
  keys %ok;
}

sub _get_other_loop_data {
  my ($ig) = @_;

  my $g = $ig->g->copy_graph;

  for my $v ($g->vertices) {
    next if $ig->is_push_vertex($v)
         or $ig->is_pop_vertex($v);
    for my $p ($g->predecessors($v)) {
      for my $s ($g->successors($v)) {
        $g->add_edge($p, $s);
      }
    }

    graph_delete_vertex_fast($g, $v);
  }

  my %result;
  for my $v ($g->vertices) {
    $result{$v} =
      grep { $_ eq $v } _graph_all_successors_cond($g, $v, sub {
        my $label = $ig->get_vertex_label($v);
        my $partner_id = UNIVERSAL::can($label, 'partner') ?
          $label->partner : undef;
        $_ ne $partner_id
      })
  }

  return %result;
}

sub _get_shrunk_graph_successor_data {
  my ($ig, $m) = @_;

  # NOTE: needs information from other functions through $m

  my $vertices = $m->{vertices};
  my $g = $ig->g->copy_graph;

  my %name_is_wanted;
  for my $v ($g->vertices) {
    # FIXME(bh): this should not take name from If->name() and such
    # Or alternatively, If->name must not clash with other namespaces
    my $name = $vertices->[$v]{name} // '';
    $name_is_wanted{ $name } //=
          $vertices->[$v]{self_loop}
       || $vertices->[$v]{other_loop}
       || $name_is_wanted{ $name };
  }

  for my $v ($g->vertices) {
    next if 0
         or $v eq $m->{grammar}{anon_start_id}
         or $v eq $m->{grammar}{anon_final_id}
         or $vertices->[$v]{self_loop}
         or $vertices->[$v]{other_loop}
         or $vertices->[$v]{is_terminal_vertex}
         or ($vertices->[$v]{type} // '') =~ /^(if\d*|fi\d*)$/i
         or ($vertices->[$v]{type} // '') =~ /^(Prelude|Postlude)$/i
         or $name_is_wanted{ $vertices->[$v]{name} // '' }
         ;

    for my $p ($g->predecessors($v)) {
      for my $s ($g->successors($v)) {
        $g->add_edge($p, $s);
      }
    }
    graph_delete_vertex_fast($g, $v);
  }

  return map { $_ => [ $g->successors($_) ] } $g->vertices;
}

sub _mauve {
  my ($g) = @_;

  # TODO(bh): sort successors by topological_id

  my %epsilon_loop = _get_epsilon_loop_data($g);
  my %scc = _get_scc_data($g);
  my %topological = _get_topological_data($g);
  my %other_loop = _get_other_loop_data($g);

  my @vertices;

  my $max_vertices = max( $g->g->vertices );

  return unless defined $max_vertices;

  for my $v (0 .. $max_vertices) {
    my $vl = $g->get_vertex_label($v);
    next unless $g->g->has_vertex( $v );
    $vertices[$v] = {
      vertex_id          => $v,
      type               => (ref($vl) =~ s/.*:://r),
      name               => (UNIVERSAL::can($vl, 'name') ? $vl->name : undef ),
      partner_id         => (UNIVERSAL::can($vl, 'partner') ? $vl->partner : undef ),
      p1_id              => (UNIVERSAL::can($vl, 'p1') ? $vl->p1 : undef ),
      p2_id              => (UNIVERSAL::can($vl, 'p2') ? $vl->p2 : undef ),
      epsilon_loop       => $epsilon_loop{$v},
      topological_id     => $topological{$v},
      other_loop         => $other_loop{$v},
      scc_vertices       => $scc{$v},
      scc_id             => ($scc{$v}[0] // $v),
      is_terminal_vertex => scalar($g->is_terminal_vertex($v)),
      is_push_vertex     => scalar($g->is_push_vertex($v)),
      is_pop_vertex      => scalar($g->is_pop_vertex($v)),
      spans              => (!UNIVERSAL::can($vl, 'spans') ? undef :
                              [ $vl->spans->spans ]),
      successors         => [ $g->g->successors($v) ],
    };
  }

  my ($start) = $g->g->predecessorless_vertices();
  my @heads = $g->g->edges_from($start);
  die unless @heads == 1;
  my $prelude = $heads[0]->[1];

  my ($final) = $g->g->successorless_vertices();
  my @rheads = [ map { @$_ } $g->g->edges_to($final) ];
  my $postlude = $rheads[0]->[0];

  my %grammar = (
    anon_start_id => $start,
    prelude_id    => $prelude,
    postlude_id   => $postlude,
    anon_final_id => $final,
    prelude_char  => -1, # FIXME: make dynamic
    postlude_char => -1, # FIXME: make dynamic
  );

  my %m = (
    vertices => \@vertices,
    grammar => \%grammar,
  );

  my %shrunk_successors = _get_shrunk_graph_successor_data($g, \%m);

  for my $v (keys %shrunk_successors) {
    $vertices[$v]->{shrunk_successors} = $shrunk_successors{$v};
  }

  return %m;
}

# TODO: rename convert_singles?
sub _convert_vertices {
  my ($accumulator, @vertices) = @_;
  my $index = @$accumulator;
  push @$accumulator, @vertices;
  push @$accumulator, 0;
  return $index;
}

sub _convert_spans {
  my ($accumulator, @spans) = @_;
  my $index = @$accumulator;
  push @$accumulator, map { $_->[0], $_->[1] + 1 } @spans;
  push @$accumulator, 0, 0;
  return $index;
}

sub _renumber_vertices {
  my ($m) = @_;

  my $vertex_map = Data::AutoBimap->new(start => 0);
  $vertex_map->s2n(0);

  $vertex_map->s2n($_) for nsort_by {
    $m->{vertices}[$_]{topological_id}
  } grep {
    defined $m->{vertices}[$_]
  } 0 .. @{ $m->{vertices} } - 1;

  my %is_vertex = (
    grammar => {
      anon_start_id => 1,
      prelude_id    => 1,
      postlude_id   => 1,
      anon_final_id => 1,
      prelude_char  => 0,
      postlude_char => 0,
    },
    vertex => {
      vertex_id          => 1,
      type               => 0,
      name               => 0,
      partner_id         => 1,
      p1_id              => 1,
      p2_id              => 1,
      epsilon_loop       => 0,
      topological_id     => 0,
      other_loop         => 0,
      scc_vertices       => 0,
      scc_id             => 1,
      is_terminal_vertex => 0,
      is_push_vertex     => 0,
      is_pop_vertex      => 0,
      spans              => 0,
      input_dfa_class_id => 0,
      successors         => 0,
      shrunk_successors  => 0,
    },
  );

  my %new = (
    spans => [ @{ $m->{spans} } ],
  );

  $new{vertex_lists} = [
    map { $vertex_map->s2n($_) } @{ $m->{vertex_lists} }
  ];

  $new{input_dfa_table} = $m->{input_dfa_table};
  $new{input_dfa} = $m->{input_dfa};

  while (my ($k, $v) = each %{ $m->{grammar} }) {
    warn "Unknown key $k" unless defined $is_vertex{grammar}{$k};
    $new{grammar}{$k} = $is_vertex{grammar}{$k} ?
      $vertex_map->s2n($v) : $v;
  }

  for (my $v = 0; $v < @{ $m->{vertices} }; ++$v) {
    next unless defined $m->{vertices}[$v];
    while (my ($k, $val) = each %{ $m->{vertices}[$v] }) {
      warn "Unknown key $k" unless defined $is_vertex{vertex}{$k};
      $new{vertices}[$vertex_map->s2n($v)]{$k} =
        $is_vertex{vertex}{$k} ? $vertex_map->s2n($val // 0) : $val;
    }
  }

  # TODO: nsort in vertex_lists

  return %new;
}

sub _mauve_linear {
  my ($g) = @_;
  my %m = _mauve($g);
  $m{vertex_lists} = [];
  $m{spans} = [];

  my $convert_list = memoize(sub {
    return _convert_vertices($m{vertex_lists}, @_);
  }, NORMALIZER => sub {
    return freeze \@_
  });

  my $convert_spans = memoize(sub {
    return _convert_spans($m{spans}, @_);
  }, NORMALIZER => sub {
    return freeze \@_
  });

  # empty list goes first
  $convert_list->();
  $convert_spans->();

  for my $vd (@{ $m{vertices} }) {
    next unless $vd and %$vd;
    for my $name (qw/successors shrunk_successors scc_vertices/) {
      $vd->{$name} = $convert_list->(sort @{ $vd->{$name} // [] });
    }
    $vd->{spans} = $convert_spans->(@{ $vd->{spans} // [] });
  }

#  Grammar::Graph::Mauve::InputDFA::add_input_dfa_to_data(\%m);

  %m = _renumber_vertices(\%m);

  return bless \%m, 'Grammar::Graph::Mauve::Data';
}

1;

__END__

