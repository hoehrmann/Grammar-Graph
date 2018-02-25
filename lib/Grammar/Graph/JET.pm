package Grammar::Graph::JET;
use 5.024;
use strict;
use warnings;
use JSON;
use Storable qw/dclone/;

our %arity = (
  'grammar'                => [ undef, undef ],

  'repetition'             => [ 1, 'group' ],

  'optional'               => [ 1, 'group' ],
  'greedyOptional'         => [ 1, 'group' ],
  'lazyOptional'           => [ 1, 'group' ],

  'zeroOrMore'             => [ 1, 'group' ],
  'greedyZeroOrMore'       => [ 1, 'group' ],
  'lazyZeroOrMore'         => [ 1, 'group' ],

  'oneOrMore'              => [ 1, 'group' ],
  'greedyOneOrMore'        => [ 1, 'group' ],
  'lazyOneOrMore'          => [ 1, 'group' ],

  'group'                  => [ 2, 'group' ],

  'rule'                   => [ 1, 'group' ],

  'exclusion'              => [ 2, 'group' ],
  'choice'                 => [ 2, 'choice' ],
  'conjunction'            => [ 2, 'conjunction' ],
  'orderedChoice'          => [ 2, 'orderedChoice' ],
  'orderedConjunction'     => [ 2, 'orderedConjunction' ],
  'ref'                    => [ 0, undef ],
  'range'                  => [ 0, undef ],
  'asciiInsensitiveString' => [ 0, undef ],
  'string'                 => [ 0, undef ],
  'empty'                  => [ 0, undef ],
);

sub from_json_string {
  my ($class, $json_string) = @_;

  my $self = bless {
    _ => JSON->new->decode($json_string),
  }, $class;

  return $self;
}

sub from_tree {
  my ($class, $root) = @_;

  my $self = bless {
    _ => dclone($root),
  }, $class;

  # TODO: validate

  return $self;
}

sub make_binary {
  my ($self) = @_;
  _make_jet_binary($self->{_});
  return $self;
}

sub to_tree {
  my ($self) = @_;
  return dclone $self->{_};
}

sub _make_jet_binary {
  my ($node) = @_;

  my @todo = ($node);

  while (my $current = pop @todo) {

    if (not defined $arity{ $current->[0] } ) {
      ...
    }

    my $max = $arity{ $current->[0] }->[0];

    while ( defined $max and $max < @{ $current->[2] } ) {

      my $rhs = pop @{ $current->[2] };
      my $lhs = pop @{ $current->[2] };
      my $new = [
        $arity{ $current->[0] }[1],
        {},
        [$lhs, $rhs]
      ];
      
      if (not defined $new->[0]) {
        ...
      }

      push @{ $current->[2] }, $new;
    }

    push @todo, @{ $current->[2] };
  }

  return $node;
}

sub to_json_string {
  my ($self) = @_;
  return _to_json_tree($self->{_});
}

sub _to_json_tree {
  my ($node) = @_;

  my $result = _to_json_tree_step($node, 0);

  $result =~ s/^(\s*\["rule")/\n$1/mg;
  $result =~ s/,\s*$//;

  return $result;
}

sub _to_json_tree_step {
  my ($node, $depth) = @_;

  my ($name, $args, $children) = @$node;

  return '' unless @$node;

  # TODO: JSON encode $name

  my $result = sprintf qq{\n%*s["%s", %s, [},
    $depth*2, '', ($name // ''),
    JSON->new->space_after(1)->canonical(1)->encode($args);

  $result .= _to_json_tree_step($_, $depth+1) for @$children;

  $result .= sprintf qq{]],};

  $result =~ s/,\]/]/sg;

  return $result;
}

1;

__END__

