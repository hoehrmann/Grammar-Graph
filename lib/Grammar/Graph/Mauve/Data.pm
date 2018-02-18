package Grammar::Graph::Mauve::Data;
use Modern::Perl;

sub _vertices {
  my ($self, $index) = @_;
  my @result;

  return unless defined $index;

  for (my $ix = $index; ; ++$ix) {
    last unless $self->{vertex_lists}[$ix];
    push @result, $self->{vertex_lists}[$ix];
  }
  return @result;
}

sub scc_vertices {
  my ($self, $v) = @_;
  return _vertices($self, $self->{vertices}[$v]{scc_vertices});
}

sub shrunk_successors {
  my ($self, $v) = @_;
  return _vertices($self, $self->{vertices}[$v]{shrunk_successors});
}

sub successors {
  my ($self, $v) = @_;
  return _vertices($self, $self->{vertices}[$v]{successors});
}

sub _grammar_property {
  my ($self) = @_;
  my $name = [caller 1]->[3] =~ s/^.*:://r;
  return $self->{grammar}{$name};
}

sub anon_start_id { &_grammar_property }
sub prelude_id { &_grammar_property }
sub postlude_id { &_grammar_property }
sub anon_final_id { &_grammar_property }
sub prelude_char { &_grammar_property }
sub postlude_char { &_grammar_property }

sub _vertex_property {
  my ($self, $v) = @_;
  my $name = [caller 1]->[3] =~ s/^.*:://r;
  return $self->{vertices}[$v]{$name};
}

sub type { &_vertex_property }
sub name { &_vertex_property }
sub partner_id { &_vertex_property }
sub p1_id { &_vertex_property }
sub p2_id { &_vertex_property }
sub scc_id { &_vertex_property }
sub epsilon_loop { &_vertex_property }
sub topological_id { &_vertex_property }
sub other_loop { &_vertex_property }
sub is_terminal_vertex { &_vertex_property }
sub is_push_vertex { &_vertex_property }
sub is_pop_vertex { &_vertex_property }

sub first_edge {
  my ($self) = @_;
  return [ 0, $self->anon_start_id, 0, $self->prelude_id ];
}

sub stack_type {
  my ($self, $v) = @_;
  return "push" if $self->is_push_vertex($v);
  return "pop" if $self->is_pop_vertex($v);
  return "none";
}

sub spans {
  my ($self, $v) = @_;

  my @result;
  my $six = $self->{vertices}->[$v]->{spans};

  for (my $ix = $six; 1; $ix += 2) {
    my $lo = $self->{spans}->[$ix];
    my $hi = $self->{spans}->[$ix+1];
    last if $lo eq $hi;
    push @result, [ $lo, $hi - 1 ];
  }

  return @result;
}

sub all_int_spans {
  my ($self) = @_;

  my @spans = ([]);

  my %spans_offset_to_list_index;

  for (my $ix = 0; $ix < @{ $self->{spans} }; $ix += 2) {
    my $min_inclusive = $self->{spans}[$ix];
    my $max_exclusive = $self->{spans}[$ix+1];

#    next if $min_inclusive  < 0;

    if ($min_inclusive == $max_exclusive) {
      push @spans, [];
      $spans_offset_to_list_index{ $ix + 2 } = $#spans;
      next;
    }

    push @{ $spans[-1] }, [ $min_inclusive, $max_exclusive - 1 ];
  }

  pop @spans;

  my @int_spans = map {
    Set::IntSpan->new(@$_);
  } @spans;

  return @int_spans;
}

1;

__END__

