package Grammar::Graph::Traversal;

sub vertex_hash {
  my ($class, $g, %o) = @_;

  $o{from} //= [];
  $o{then} //= "successors";
  $o{self} //= "if_reachable";
  $o{take_if} //= sub { 1 };
  $o{over_if} //= sub { 1 };

  die unless grep { $o{then} eq $_ }
    qw/successors predecessors/;

  my $next = $o{then} eq 'successors'
    ? sub { $g->successors(@_) }
    : sub { $g->predecessors(@_) };

  die unless grep { $o{self} eq $_ }
    qw/always if_reachable/;

  warn unless @{ $o{from} };

  my %result;

  my @todo = @{ $o{from} };

  $result{$_} = 1 for grep {
    $o{self} eq 'always'
  } @todo;

  my %seen;

  while (defined($_ = pop @todo)) {
    $result{$_} = 1 if $o{take_if}->($_);

    # TODO: might might not take, but still go over a vertex;
    # is that intentional? Maybe the parameter should be sth
    # else

    next if $seen{$_}++;

    next unless $o{over_if}->($_);

    push @todo, $_ for $next->($_);
  }

  return %result;
}

1;

__END__

