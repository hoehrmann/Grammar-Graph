package Grammar::Graph::JET;
use 5.024;
use strict;
use warnings;
use JSON;
use Storable qw/dclone/;

our %arity = (
  'grammar'                => [ undef, undef ],
  'rule'                   => [ 1, 'group' ],
  'repetition'             => [ 1, 'group' ],
  'group'                  => [ 2, 'group' ],
  'exclusion'              => [ 2, 'group' ],
  'repetition'             => [ 2, 'group' ],
  'rule'                   => [ 2, 'group' ],

  'optional'               => [ 1, 'group' ],
  'greedyOptional'         => [ 1, 'group' ],
  'lazyOptional'           => [ 1, 'group' ],

  'zeroOrMore'             => [ 1, 'group' ],
  'greedyZeroOrMore'       => [ 1, 'group' ],
  'lazyZeroOrMore'         => [ 1, 'group' ],

  'oneOrMore'              => [ 1, 'group' ],
  'greedyOneOrMore'        => [ 1, 'group' ],
  'lazyOneOrMore'          => [ 1, 'group' ],

  'empty'                  => [ 0, undef ],

  'choice'                 => [ 2, 'choice' ],
  'conjunction'            => [ 2, 'conjunction' ],
  'orderedChoice'          => [ 2, 'orderedChoice' ],
  'orderedConjunction'     => [ 2, 'orderedConjunction' ],
  'ref'                    => [ 0, undef ],
  'range'                  => [ 0, undef ],
  'asciiInsensitiveString' => [ 0, undef ],
  'string'                 => [ 0, undef ],
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

1;

__END__

