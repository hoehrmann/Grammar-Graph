package Grammar::Graph::Simplify;
use 5.024;
use strict;
use warnings;
use JSON;
use Storable qw/dclone/;

# TODO: asciiInsensitiveString -> string with fold attribute
# string, aciString

sub simplify {

  my ($ctx, $item) = @_;

  my ($name, $attr, $children) = @$item;

  my %handler = (
    'range'                  => \&range,
    'ranges'                 => \&ranges,
    'asciiInsensitiveString' => \&asciiInsensitiveString,
    'string'                 => \&string,
    'repetition'             => \&repetition,
    'optional'               => \&optional,
    'zeroOrMore'             => \&zeroOrMore,
    'greedyOptional'         => \&greedyOptional,
    'greedyZeroOrMore'       => \&greedyZeroOrMore,
    'lazyOptional'           => \&lazyOptional,
    'lazyZeroOrMore'         => \&lazyZeroOrMore,
  );

  my $default = sub {
    my ($args, @kids) = @_;

    return [ $name, { %$args }, [@kids] ];
  };

  my @kids = map { simplify($ctx, $_) } @$children;

  return ($handler{$name} // $default)->(
    $attr, @kids
  );

}

sub repetition_cloning {

  my ($args, @kids) = @_;

  die unless @kids == 1;

  my $min = $args->{min};
  my $max = $args->{max};

#  return zeroOrMore({}, @kids) if $min == 0 and not defined $max;
#  return oneOrMore({}, @kids) if $min == 1 and not defined $max;

  my $group = empty({});

  for (my $ix = 0; $ix < $min; ++$ix) {
    my $clone = dclone $kids[0];
    $group = group({}, $group, $clone);
  }

  if (not defined $max) {
    return group({}, $group, zeroOrMore({}, @kids));
  }

  for (my $ix = $min; $ix < $max; ++$ix) {
    my $clone = dclone $kids[0];
    $group = group({}, $group, optional({}, $clone));
  }

  return $group;

}

sub repetition {

  my ($args, @kids) = @_;

  return repetition_cloning($args, @kids);

}

sub ranges {
  my ($args, @kids) = @_;

  die 'kids ought to be charClass at this point' if grep {
    $_->[0] ne 'charClass'
  } @kids;

  my $run_list = join ',', map {
    $_->[1]->{run_list}
  } @kids;

  return charClass({ run_list => $run_list });

}

sub range {

  my ($args, @kids) = @_;

  my $run_list = join(
    '-',
    $args->{first},
    $args->{last},
  );

  return charClass({ run_list => $run_list });
}

sub string {

  my ($args, @kids) = @_;

  my @spans = map {
    range({ first => ord(), last => ord()})
  } split//, $args->{text};

  my $group = empty({});

  while (@spans) {
    $group = group({}, pop(@spans), $group);
  }

  return $group;

}

sub asciiInsensitiveString {
  my ($args, @kids) = @_;

  my @chars = split//, $args->{text};

  use bytes;

  my @spans = map {
    charClass({ run_list => join(',', ord(uc), ord(lc)) })
  } @chars;

  my $group = empty({});

  while (@spans) {
    $group = group({}, pop(@spans), $group);
  }

  return $group;
}

sub empty {
  my ($args, @kids) = @_;
  return [ "empty", {}, [] ];
}

sub choice {
  my ($args, @kids) = @_;

  die unless @kids == 2;

  return [ "choice", {}, [@kids] ];
}

sub group {
  my ($args, @kids) = @_;

  die unless @kids == 2;

  return [ "group", {}, [@kids] ];
}

sub orderedChoice {
  my ($args, @kids) = @_;

  die unless @kids == 2;

  return [ "orderedChoice", {}, [@kids] ];
}

sub optional {
  my ($args, @kids) = @_;

  die unless @kids == 1;

  return choice({}, empty({}), @kids);
}

sub lazyOptional {
  my ($args, @kids) = @_;

  die unless @kids == 1;

  return orderedChoice({}, empty({}), @kids);
}

sub greedyOptional {
  my ($args, @kids) = @_;

  die unless @kids == 1;

  return orderedChoice({}, @kids, empty({}));
}

sub oneOrMore { 
  my ($args, @kids) = @_;

  die unless @kids == 1;

  return [ "oneOrMore", {}, [@kids] ];
}

sub lazyOneOrMore {
  my ($args, @kids) = @_;

  die unless @kids == 1;

  return [ "lazyOneOrMore", {}, [@kids] ];
}

sub greedyOneOrMore {
  my ($args, @kids) = @_;

  die unless @kids == 1;

  return [ "greedyOneOrMore", {}, [@kids] ];
}

sub zeroOrMore { 
  my ($args, @kids) = @_;

  die unless @kids == 1;

  return optional({}, oneOrMore({}, @kids));
}

sub lazyZeroOrMore {
  my ($args, @kids) = @_;

  die unless @kids == 1;

  return lazyOptional({}, lazyOneOrMore({}, @kids));
}

sub greedyZeroOrMore {
  my ($args, @kids) = @_;

  die unless @kids == 1;

  return greedyOptional({}, greedyOneOrMore({}, @kids));
}

sub charClass {
  my ($args, @kids) = @_;

  return [ "charClass", {%$args}, [] ];
}

1;

__END__
