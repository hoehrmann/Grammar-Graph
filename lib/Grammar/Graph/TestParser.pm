package Grammar::Graph::TestParser::Context::Forward;
use Modern::Perl;
use Moose;

extends 'Grammar::Graph::TestParser::Context::Base';

sub current_ord {
  my ($self) = @_;
  $self->input->[$self->current_index + 1];
}

sub first_index {
  my ($self) = @_;
  return -1;
}

sub last_index {
  my ($self) = @_;
  return -1 + scalar @{ $self->input };
}

sub previous_index {
  my ($self, $index) = @_;
  return $index - 1;
}

sub next_index {
  my ($self, $index) = @_;
  return $index + 1;
}

sub is_push_vertex {
  my ($self, $v) = @_;
  return $self->g->is_push_vertex($v);
}

sub is_pop_vertex {
  my ($self, $v) = @_;
  return $self->g->is_pop_vertex($v);
}

package Grammar::Graph::TestParser::Context::Backward;
use Modern::Perl;
use Moose;

extends 'Grammar::Graph::TestParser::Context::Base';

sub current_ord {
  my ($self) = @_;
  $self->input->[$self->current_index + 0];
}

sub first_index {
  Grammar::Graph::TestParser::Context::Forward::last_index(@_);
}

sub last_index {
  Grammar::Graph::TestParser::Context::Forward::first_index(@_);
}

sub previous_index {
  Grammar::Graph::TestParser::Context::Forward::next_index(@_);
}

sub next_index {
  Grammar::Graph::TestParser::Context::Forward::previous_index(@_);
}

sub is_push_vertex {
  Grammar::Graph::TestParser::Context::Forward::is_pop_vertex(@_);
}

sub is_pop_vertex {
  Grammar::Graph::TestParser::Context::Forward::is_push_vertex(@_);
}

package Grammar::Graph::TestParser::Context::Base;
use Modern::Perl;
use Moose;
use MooseX::Aliases;

has 'grammar_graph' => (
  is       => 'ro',
  required => 1,
  isa      => 'Grammar::Graph',
  alias    => 'g',
);

has 'planar_graph' => (
  is       => 'ro',
  required => 0,
  isa      => 'Graph::Directed',
  default  => sub { Graph::Directed->new },
  writer   => '_set_planar_graph',
  alias    => 'pg'
);

has 'stack_graph' => (
  is       => 'ro',
  required => 0,
  isa      => 'Graph::Directed',
  default  => sub { Graph::Directed->new },
  writer   => '_set_stack_graph',
  alias    => 'o'
);

has 'vertex_to_scc' => (
  is       => 'ro',
  required => 0,
  isa      => 'HashRef',
  writer   => '_set_vertex_to_scc',
  default  => sub { {} },
);

has 'vertex_to_topological' => (
  is       => 'ro',
  required => 0,
  isa      => 'HashRef',
  writer   => '_set_vertex_to_topological',
  default  => sub { {} },
);

has 'input' => (
  is       => 'ro',
  required => 1,
  isa      => 'ArrayRef',
);

has 'current_index' => (
  is       => 'rw',
  required => 0,
  isa      => 'Int',
  default  => sub { 0 },
);

sub BUILD {
  my ($self, $args) = @_;

  my %vertex_to_scc = $self->g->_create_vertex_to_scc();
  $self->_set_vertex_to_scc(\%vertex_to_scc);

  my %vertex_to_topological =
    $self->g->_create_vertex_to_topological();

  $self->_set_vertex_to_topological(\%vertex_to_topological);
}

sub is_matching_couple {
  my ($self, $vid, $pid) = @_;
  return $self->g->is_matching_couple($vid, $pid);
}

sub start_encoded {
  my ($self) = @_;
  return Grammar::Graph::TestParser::_encode(
    $self->first_index,
    $self->g->start_vertex);
}

sub final_encoded {
  my ($self) = @_;
  Grammar::Graph::TestParser::_encode(
    $self->last_index,
    $self->g->final_vertex);
}

#####################################################################
#
#####################################################################

=pod
  my ($srcix, $srcid, $srcd) = Grammar::Graph::TestParser::_decode($src);
  my ($dstix, $dstid, $dstd) = Grammar::Graph::TestParser::_decode($dst);
  return if $self->is_push_vertex($srcid)
    and $self->is_pop_vertex($dstid)
    and not $self->is_matching_couple($srcid, $dstid);
=cut

#####################################################################
#
#####################################################################

sub stack_add_edge {
  my ($self, $src, $dst) = @_;
  return if $self->o->has_edge($src, $dst);
  $self->o->add_edge($src, $dst);
  return 1;
}

sub stack_has_edge {
  my ($self, $src, $dst) = @_;
  $self->o->has_edge($src, $dst);
}

sub stack_delete_edge {
  my ($self, $src, $dst) = @_;
  $self->o->delete_edge($src, $dst);
}

sub stack_successors {
  my ($self, $v) = @_;
  $self->o->successors($v);
}

sub stack_predecessors {
  my ($self, $v) = @_;
  $self->o->predecessors($v);
}

#####################################################################
#
#####################################################################
sub planar_add_edge {
  my ($self, $src, $dst) = @_;
  $self->pg->add_edge($src, $dst);
}

sub planar_has_edge {
  my ($self, $src, $dst) = @_;
  $self->pg->has_edge($src, $dst);
}

sub planar_has_vertex {
  my ($self, $v) = @_;
  $self->pg->has_vertex($v);
}

#####################################################################
#
#####################################################################
sub grammar_successors {
  my ($self, $v) = @_;
  $self->g->g->successors($v);
}


#####################################################################
#
#####################################################################

package Grammar::Graph::TestParser;
use Algorithm::ConstructDFA::XS 0.24;
use Parse::ABNF 0.20;
use Grammar::Formal 0.20;
use Grammar::Graph 0.20;
use Grammar::Graph::Simplify;
use Data::AutoBimap;
use Graph::Directed;
use Graph::SomeUtils ':all';
use List::Util qw/min max/;
use List::MoreUtils qw/uniq/;
use List::UtilsBy qw/partition_by sort_by/;
use List::OrderBy;
use Modern::Perl;
use Set::IntSpan;
use Storable qw/freeze thaw retrieve/;
use YAML::XS;
use JSON;
use Encode;
use Graph::Traversal::BFS;
use autodie;

local $Storable::canonical = 1;

sub from_abnf_file {
  my ($class, $path, $shortname) = @_;

  my $formal = Parse::ABNF->new->parse_to_grammar_formal(do {
    local $/;
    die "There is no file $path" unless -f $path;
    open my $f, '<', $path;
    <$f> =~ s/\r\n/\n/gr;
  }, core => 1);

  my $g = Grammar::Graph->from_grammar_formal($formal, $shortname);

  $g->fa_drop_rules_not_needed_for($shortname);
  $g->fa_merge_character_classes();
  $g->fa_separate_character_classes();

  $g->fa_expand_references();
  $g->fa_remove_useless_epsilons($g->g->vertices);
  $g->fa_truncate();

  return $g;
}

sub _encode {
  my ($offset, $vertex, $data) = @_;
  return pack 'l2', $offset, $vertex unless $data;
  return pack 'l3', $offset, $vertex, $data;
}

sub _decode {
  my ($packed) = @_;
  return unpack 'l2', $packed if length($packed) == 8;
  return unpack 'l3', $packed;
}

#####################################################################
# 
#####################################################################

sub file_to_ords {
  my ($input_path) = @_;

  open my $f, '<:utf8', $input_path;
  my $chars = do { local $/; binmode $f; <$f> };
  my @input = map { ord } split//, $chars;

  return -1, @input, -1;
}

#####################################################################
#
#####################################################################

sub parse_parse {
  my ($g, $data_path, $class) = @_;

  my @input = file_to_ords($data_path);


  if ($class eq 'Grammar::Graph::TestParser::Context::Backward') {
    my $ctx = simple_parse($g->reversed_copy, \@input, $class);

    my $tmp = Graph::Directed->new;
    $tmp->add_edge(reverse @$_) for $ctx->planar_graph->edges;

    my $tmp2 = Graph::Directed->new;
    $tmp2->add_edge(reverse @$_) for $ctx->stack_graph->edges;

    return $g,
      $tmp, 
      $tmp2,

  } else {
    my $ctx = simple_parse($g, \@input, $class);
    return $g, $ctx->planar_graph, $ctx->stack_graph;
  }
}

sub parse_parse_parse {
  my ($abnf_path, $shortname, $data_path) = @_;

  my $g = Grammar::Graph::TestParser->from_abnf_file($abnf_path, $shortname);

  return parse_parse($g, $data_path, 'Grammar::Graph::TestParser::Context::Forward');
}

#####################################################################
# 
#####################################################################

sub delete_non_stack_vertices {
  my ($ctx) = @_;

  # TODO: delete except is_push_vertex/is_pop_vertex (?)
  graph_delete_vertices_fast($ctx->o, grep { 
    my ($vix, $vid, $vd) = _decode($_);
    $ctx->g->is_terminal_vertex($vid);
  } $ctx->o->vertices);
}

sub delete_stack_vertices_not_in_planar_graph {
  my ($ctx) = @_;
  graph_delete_vertices_fast($ctx->o, grep {
    my ($vix, $vid, $vdata) = _decode($_);
    not $ctx->planar_has_vertex(_encode($vix, $vid, 0))
  } $ctx->o->vertices);
}

sub does_vertex_have_partner_successor {
  my ($ctx, $v) = @_;

  my ($vix, $vid, $vdata) = _decode($v);

  return grep {
    my ($six, $sid, $sdata) = _decode($_);
    $ctx->is_pop_vertex($sid)
      and $ctx->is_matching_couple($vid, $sid);
  } $ctx->stack_successors($v)
}

sub delete_stack_vertices_without_final {
  my ($ctx) = @_;

  graph_delete_vertices_fast($ctx->o, grep {
    my ($vix, $vid, $vdata) = _decode($_);

    $ctx->is_push_vertex($vid)
      and not does_vertex_have_partner_successor($ctx, $_)

  } $ctx->o->vertices);
};

sub graph_delete_self_loops {
  my ($g) = @_;
  $g->delete_edge($_, $_) for $g->vertices;
}

sub delete_false_stack_edges {
  my ($ctx) = @_;
  for my $e ($ctx->o->edges) {
    my ($pix, $pid, $pdata) = _decode($e->[0]);
    my ($six, $sid, $sdata) = _decode($e->[1]);
    $ctx->o->delete_edge(@$e) if 1
      and $ctx->is_push_vertex($pid)
      and $ctx->is_pop_vertex($sid)
      and !$ctx->is_matching_couple($pid, $sid);
  }
}

sub _have_matching_successors {
  my ($ctx, $p, $s) = @_;

  my ($pix, $pid, $pd) = _decode($p);
  my ($six, $sid, $sd) = _decode($s);

  die unless $ctx->is_push_vertex($pid);
  die unless $ctx->is_push_vertex($sid);

  for my $ps ($ctx->stack_successors($p)) {
    for my $ss ($ctx->stack_successors($s)) {
      my ($psix, $psid, $psd) = _decode($ps);
      my ($ssix, $ssid, $ssd) = _decode($ss);

      next unless 1
        and $ctx->is_pop_vertex($psid)
        and $ctx->is_pop_vertex($ssid);

      return 1 if $ctx->stack_graph->has_edge($ss, $ps);
    }
  }

  return 0;
}

sub _have_matching_predecessors {
  my ($ctx, $p, $s) = @_;

  my ($pix, $pid, $pd) = _decode($p);
  my ($six, $sid, $sd) = _decode($s);

  die unless $ctx->is_pop_vertex($pid);
  die unless $ctx->is_pop_vertex($sid);

  for my $ps ($ctx->stack_predecessors($p)) {
    for my $ss ($ctx->stack_predecessors($s)) {
      my ($psix, $psid, $psd) = _decode($ps);
      my ($ssix, $ssid, $ssd) = _decode($ss);

      next unless 1
        and $ctx->is_push_vertex($psid)
        and $ctx->is_push_vertex($ssid);

      return 1 if $ctx->stack_graph->has_edge($ss, $ps);
    }
  }

  return 0;
}

sub delete_failed_speculative_stack_edges {
  my ($ctx) = @_;

  for my $e ($ctx->stack_graph->edges) {
    my ($p, $s) = @$e;
    my ($pix, $pid, $pd) = _decode($p);
    my ($six, $sid, $sd) = _decode($s);

    next unless
      $ctx->is_push_vertex($pid) == $ctx->is_push_vertex($sid);

    if ($ctx->is_push_vertex($pid)) {

      next if _have_matching_successors($ctx, $p, $s);
      $ctx->stack_graph->delete_edge($p, $s);
      # warn "removing speculative edge";

    } else {

      next if _have_matching_predecessors($ctx, $p, $s);
      $ctx->stack_graph->delete_edge($p, $s);
      # warn "removing speculative reverse edge";
    }

  }

}

sub delete_planar_exclusive_stack_vertices {
  my ($ctx) = @_;

  $ctx->pg->delete_vertices(grep {
    my ($pix, $pid, $pd) = _decode($_);

    ($ctx->is_pop_vertex($pid) or $ctx->o->has_vertex($pid))
      and not $ctx->o->has_vertex($_);

  } $ctx->pg->vertices);
}

sub cleanup_graphs {
  my ($ctx) = @_;

  delete_non_stack_vertices($ctx);

  delete_false_stack_edges($ctx);

  for (1 .. 1) {

  graph_truncate_to_vertices_between($ctx->pg,
    $ctx->start_encoded, $ctx->final_encoded);

#warn "...";
#return;

#  delete_stack_vertices_not_in_planar_graph($ctx);

  graph_truncate_to_vertices_between($ctx->o,
    $ctx->start_encoded, $ctx->final_encoded);

  # FIXME: works for 2, needs to work for N
  delete_failed_speculative_stack_edges($ctx);

  graph_truncate_to_vertices_between($ctx->o,
    $ctx->start_encoded, $ctx->final_encoded);

  }

  delete_planar_exclusive_stack_vertices($ctx);
  graph_truncate_to_vertices_between($ctx->pg,
    $ctx->start_encoded, $ctx->final_encoded);

}

#####################################################################
# ...
#####################################################################
sub does_terminal_vertex_match_char {
  my ($g, $vid, $ord) = @_;

  my $label = $g->get_vertex_label($vid);

#  warn sprintf "testing char '%c' against " . $label->spans . " from $vid", $ord;

  return $label->spans->member($ord);
}

#####################################################################
#
#####################################################################

sub handle_fi {
  my ($g, $o, $both, $vertex_to_scc, $todo, $ix, $v, $parent) = @_;
  my ($vix, $vid, $vdata) = _decode($v);
  my ($pix, $pid, $pdata) = _decode($parent);
 
  # possibly 

  # $v is a fi vertex
  # We've already processed all predecessors of $v

  # General structure is
  #
  #     +--> op1s --> ... --> op1f --> +
  #    /                                \
  # if                                    fi
  #    \                                /
  #     +--> op2s --> ... --> op2f --> +
  #

  # right now $o->has_edge($parent, $v)

  # $parent and $v are a matching couple

  # So are $op1f and $op1s, $op2f and $op2s

  # my $op1f = _encode($vix, $fi_label->op1)
  # my $op2f = _encode($vix, $fi_label->op2)

  # sub matching_predecessors(...)

  # $t1 = $o->predecessors($op1f) not empty
  # $t2 = $o->predecessors($op2f) not empty

  # choice
  #   return $t1 or $t2
  # ordered_choice
  #   $o->delete_vertex($op2f) if $t1
  #   $o->delete_edge($op2s, $op2f) if $t1
  #   return $t1 or $t2

  # conjunction
  #   return $t1 and $t2
  # ordered_conjunction
  #   $o->delete_vertex($op2f) if $t1 and $t2
  #   $o->delete_edge($op2s, $op2f) if $t1 and $t2
  #   return $t1 and $t2

  # subtraction
  #   $o->delete_vertex($op2f)
  #   $o->delete_edge($if, $fi) if $t2
  #   return $t1 and !$t2

}

sub handle_final {
  my ($ctx, $both, $todo, $v) = @_;

  my $vertex_to_scc = $ctx->vertex_to_scc;
  my $ix = $ctx->current_index;

  my ($vix, $vid, $vdata) = _decode($v);

  ###############################################################
  # `final` vertices correspond to `pop` operations when using a
  # stack. They have to be matched against all the `predecessors`
  # aka the most recently pushed vertices on the stack graph, and
  # when they match, a `pop` is simulated by making the previous
  # values, the second-most-recently-pushed vertices, available
  # to the successors of the current vertex. Since the current
  # vertex can be its own (direct or indirect) successor, due to
  # right recursion, the successor may have to be processed more
  # than one time to clear the emulated stack of matching values.
  ###############################################################
  for my $parent ($ctx->stack_predecessors($v)) {

    my ($pix, $pid, $pdata) = _decode($parent);
    
    next unless $ctx->is_matching_couple($pid, $vid);

    # TODO(bh): Evaluate conditionals here

    for my $pp ($ctx->stack_predecessors($parent)) {

     my ($ppix, $ppid, $ppdata) = _decode($pp);

     for my $s ($both->successors($v)) {
        my ($six, $sid, $sdata) = _decode($s);

        $ctx->stack_add_edge($v, $s);

        push @$todo, $s if $ctx->stack_add_edge($pp, $s);
      }
    }
  }
  
}

sub handle_terminal {
  my ($ctx, $both, $heads, $in, $v) = @_;

  my ($vix, $vid, $vdata) = _decode($v);

#warn "testing at ix " . $ctx->current_index;

  ###############################################################
  # ...
  ###############################################################
  return unless does_terminal_vertex_match_char($ctx->g, $vid, $in);

  for my $sid ($ctx->grammar_successors($vid)) {
    my $s = _encode($ctx->next_index($vix), $sid);

    $both->add_edge($v, $s);

    $heads->{$s}++;

    for my $parent ($ctx->stack_predecessors($v)) {
      $ctx->stack_add_edge($parent, $s);
    }
  }
}

sub simple_parse_step {
  my ($ctx, $heads, $in) = @_;

  my %seen;
  my @todo = keys %$heads;

  delete $heads->{$_} for keys %$heads;

  my $both = Graph::Directed->new;

  while (@todo) {
    my $v = shift @todo;
    my ($vix, $vid, $vdata) = _decode($v);

#    warn "doing vid $vid " . ref $ctx->g->get_vertex_label($vid);
    
     #################################################################
     # Successors have to be processed after their predecessors. 
     #################################################################
     if (not $seen{$v}++) {

       push @todo, $v;

       next if $ctx->g->is_terminal_vertex($vid);
 
       $both->add_edge($v, _encode($vix, $_))
         for $ctx->grammar_successors($vid);
 
       push @todo, map {
         _encode($vix, $_)
       } $ctx->grammar_successors($vid);

       next;
    }

    if ($ctx->g->is_terminal_vertex($vid)) {

      handle_terminal($ctx, $both, $heads, $in, $v);

    } elsif ($ctx->is_push_vertex($vid)) {
      ###############################################################
      # `start` vertices correspond to `push` operations when using a
      # stack. In the graph representation, the most recently pushed
      # vertex is, accordingly, a predecessor of the current vertex.
      ###############################################################
      for my $s ($both->successors($v)) {
        # TODO: does this have to push?
        $ctx->stack_add_edge($v, $s);
      }

    } elsif ($ctx->is_pop_vertex($vid)) {

      handle_final($ctx, $both, \@todo, $v);

    } else {

      ###############################################################
      # Other vertices do not affect the stack and so successors have
      # the all the possible stack configurations available to them.
      ###############################################################
      for my $s ($both->successors($v)) {

        for my $parent ($ctx->stack_predecessors($v)) {
          # TODO: does this have to push?
          $ctx->stack_add_edge($parent, $s);
        }
      }
    }    
  }

  $ctx->planar_add_edge(@$_) for $both->edges;
}

sub ctx_from_graph_and_input {
  my ($g, $input, $class) = @_;

  my $ctx = $class->new(
    grammar_graph => $g,
    input => $input,
  );

  return $ctx;
}

sub simple_parse {
  my ($g, $input, $class) = @_;

  #####################################################################
  # The algorithm transfers a view of the stack from vertices to their
  # immediate successors. The `@heads` are the vertices that still need
  # to be processed for a given edge, because their successors are the
  # newly added vertices in the following edge.
  #####################################################################

  my $ctx = ctx_from_graph_and_input($g, $input, $class);

  my $heads = { $ctx->start_encoded() => 1 };

  $ctx->current_index($ctx->first_index);

#  warn "current_index " . $ctx->current_index;
#  warn "last_index " . $ctx->last_index;

#  warn "final: " . join("/", _decode($ctx->final_encoded));

  while ($ctx->current_index != $ctx->last_index) {
    my $in = $ctx->current_ord();
#    warn join " ", "current index", $ctx->current_index, "in", $in;
    simple_parse_step($ctx, $heads, $in);
    $ctx->current_index($ctx->next_index($ctx->current_index));
  }

  cleanup_graphs($ctx);

  return $ctx;
}

#####################################################################
# ...
#####################################################################
sub graph_eliminate_vertex_by_connecting_neighbours {
  my ($g, $v) = @_;

  for my $p ($g->predecessors($v)) {
    for my $s ($g->successors($v)) {
      $g->add_edge($p, $s);
    }
  }

  graph_delete_vertex_fast($g, $v);
}

sub result_graph_from_test_representation {
  my ($path) = @_;

  open my $f, '<', $path;
  my $content = do { local $/; <$f> };
  close $f;
  
  my $ref = Graph::Directed->new;

  while ($content =~ /(\S+) -> (\S+)\s*/mg) {
    $ref->add_edge($1, $2);
  }

  return ($content, $ref);
}

sub result_graph_to_test_representation_json {

}

sub result_graph_to_test_representation {
  my ($g, $r) = @_;

  # TODO: returns graph but should return string ???

  # "offset,type,name,data"
  #   ->
  # "offset,type,name,data"
  my $fmt = sub {
    my ($v, $vid_map, $vdata_map) = @_;
    my ($vix, $vid, $vdata) = _decode($v);
    my $label = $g->get_vertex_label($vid);
    return join(",",
      $vix,
      (ref($label) =~ s/^Grammar::Graph:://r),
      (UNIVERSAL::can($label, 'name') ? $label->name : ''),
      $vid,
      (defined $vdata ? $vdata : ())
    );
  };

  my $c = $r->copy_graph;

=pod
  # remove unlabeled
  graph_eliminate_vertex_by_connecting_neighbours($c, $_)
    for grep {
      my ($vix, $vid, $vdata) = _decode($_);
      my $label = $g->get_vertex_label($vid);
      !(ref($label) && ($g->is_push_vertex($vid) || $g->is_pop_vertex($vid)))
    } $c->vertices;
=cut

  my $t = Graph::Directed->new;
  $t->add_edge(map { $fmt->($_) } @$_)
    for sort_by { 1 } $c->edges;

  return $t;
}

#####################################################################
# ...
#####################################################################
sub compare_fwd_and_bwd_stack_graph {
=pod
  my ($fwd, $bwd) = @_;

  my %h;
  my $e ($fwd->edges) {
    my ($vix, $vtype, $vname, $vid, $vdata) = split/,/, $e->[0];
    my ($six, $stype, $sname, $sid, $sdata) = split/,/, $e->[1];
    $h{$vtype}{$stype}
  }
=cut
  ...
}


sub test_representations_are_isomorphic {
  my ($r1, $r2) = @_;

  my @list;
  push @list, map { ["r1", $r1, $_] } $r1->vertices;
  push @list, map { ["r2", $r2, $_] } $r2->vertices;

#use Data::Dumper;
#warn Dumper [ $r1->edges ];
#warn Dumper [ $r2->edges ];

  my %graph_vertex_to_index;
  for (my $ix = 0; $ix < @list; ++$ix) {
    my ($id, $r, $v) = @{ $list[$ix] };
    $graph_vertex_to_index{$id}{$v} = $ix;
  }

  my $p = Acme::Partitioner->using(0 .. $#list);

  my $partitioner =
    $p->once_by(sub {
      my ($id, $r, $v) = @{ $list[$_] };

      my ($vix, $type, $name, $vid, $vdata) = split/,/, $v;
      return join ",", $vix, $type, $name, $vdata // 0;
    })
    ->then_by(sub {
      my ($id, $r, $v) = @{ $list[$_] };

      my %parts = map {
        my $mapped = $graph_vertex_to_index{$id}{$_};
        $p->partition_of($mapped), 1
      } $r->successors($v);

      return join '', sort keys %parts;
    });

  while ($partitioner->refine) {
    1;
  }

#warn Dumper [ $p->all_partitions ];

  ###################################################################
  # This is a bit of a kludge. The partition refinement does 
  # not express that within one graph, different vertex ids imply
  # different vertices (that cannot easily be expressed there);
  # That means the algorithm puts different vertices within one
  # graph into the same bucket (and accordingly does the same for
  # an isomorphic graph). So instead of checking that partitions
  # hold exactly one vertex from each graph and nothing else, we
  # check for an equal number of vertices from each input graph.
  ###################################################################
  for my $partition ($p->all_partitions) {
    my %h = partition_by {
      my ($id, $r, $v) = @{ $list[$_] };
      $id;
    } @$partition;

    return unless @{ $h{"r1"} // [] }
      == @{ $h{"r2"} // [] };
  }

  return 1;
}

sub result_graphs_are_isomorphic {
  my ($g1, $r1, $g2, $r2) = @_;

  # TODO: this could create copies of the graphs and eliminate any
  # vertex that is not essential for parse graphs, to allow future
  # annotations. 

  my @list;
  push @list, map { [$g1, $r1, $_] } $r1->vertices;
  push @list, map { [$g2, $r2, $_] } $r2->vertices;

  my %graph_vertex_to_index;
  for (my $ix = 0; $ix < @list; ++$ix) {
    my ($g, $r, $v) = @{ $list[$ix] };
    $graph_vertex_to_index{$g}{$v} = $ix;
  }

  my $p = Acme::Partitioner->using(0 .. $#list);

  my $partitioner =
    $p->once_by(sub {
      my ($g, $r, $v) = @{ $list[$_] };

      my ($vix, $vid, $vdata) =
        Grammar::Graph::TestParser::_decode($v);

      my $label = $g->get_vertex_label($vid);

      return join " ", $vix, ($vdata // ''), ref($label),
        (UNIVERSAL::can($label, 'name') ? $label->name : '');
    })
    ->then_by(sub {
      my ($g, $r, $v) = @{ $list[$_] };

      my %parts = map {
        my $mapped = $graph_vertex_to_index{$g}{$_};
        $p->partition_of($mapped), 1
      } $r->successors($v);

      return join '', sort keys %parts;
    });

  while ($partitioner->refine) {
    1;
  }

  ###################################################################
  # This is a bit of a kludge. The partition refinement does 
  # not express that within one graph, different vertex ids imply
  # different vertices (that cannot easily be expressed there);
  # That means the algorithm puts different vertices within one
  # graph into the same bucket (and accordingly does the same for
  # an isomorphic graph). So instead of checking that partitions
  # hold exactly one vertex from each graph and nothing else, we
  # check for an equal number of vertices from each input graph.
  ###################################################################
  for my $partition ($p->all_partitions) {
    my %h = partition_by {
      my ($g, $r, $v) = @{ $list[$_] };
      "$g"
    } @$partition;

    return unless @{ $h{$g1} } == @{ $h{$g2} };
  }

  return 1;
}

sub graph_swap_vertices {
  my ($g, $v1, $v2) = @_;

  my @p1 = $g->predecessors($v1);
  my @p2 = $g->predecessors($v2);
  my @s1 = $g->successors($v1);
  my @s2 = $g->successors($v2);

  graph_isolate_vertex($g, $v1);
  graph_isolate_vertex($g, $v2);

  $g->add_edge($_, $v1) for @p2;
  $g->add_edge($_, $v2) for @p1;
  $g->add_edge($v1, $_) for @s2;
  $g->add_edge($v2, $_) for @s1;
}

1;

__END__

