package Grammar::Graph::Testsuite::Sample;
use Modern::Perl;
use Types::Standard qw/:all/;
use Graph::Directed;
use Graph::SomeUtils qw/:all/;
use List::UtilsBy qw/sort_by nsort_by partition_by/;
use List::Util qw/uniq/;
use Moo;
use Memoize;
use Log::Any qw//;
use File::Basename;


use Grammar::Graph::Gobbledygook;
use Grammar::Graph::Shamrock;

has 'base_path' => (
  is       => 'ro',
  required => 1,
  isa      => Str,
);

has 'startrule' => (
  is       => 'ro',
  required => 1,
  isa      => Str,
  builder  => sub {
    my ($self) = @_;
    open my $f, '<:utf8', $self->base_path . '/startrule';
    my $first_line = getline $f;
    close $f;
    chomp $first_line;
    return $first_line;
  },
);

sub grammar_path {
  my ($self) = @_;
  my @candidates = glob( $self->base_path . '/*.aabnf' );
  die unless @candidates == 1;
  return $candidates[0];
}

sub input_paths {
  my ($self) = @_;
  return glob( $self->base_path . '/*.input' );
}

sub generate {
  my ($self) = @_;

  my $d = {
    startrule => $self->startrule,
  };

  my $g = Grammar::Graph::TestParser->from_abnf_file(
    $self->grammar_path, $self->startrule);

  eval {
    $d->{mauve} = Grammar::Graph::Mauve::_mauve_linear($g);
  };

  if ($@) {
    warn;
    return;
  }

  for my $input_path ($self->input_paths) {

#    next unless $input_path eq 'Grammar-Graph/data/parsing//unamed0001/0002.input';

    my $filename = basename $input_path;

    my @in = Grammar::Graph::Gobbledygook::file_to_ords($input_path);

    $d->{files}{$filename}{reachable} =
      _generate_reachable($self, $d->{mauve}, $input_path);

    $d->{files}{$filename}{breviated} =
      _generate_breviated($self, $d->{mauve}, $input_path);

    for (1) {
      warn "input_path $input_path\n";
      push @{ $d->{files}{$filename}{trees} },
        _generate_a_tree($self,
                         $d->{mauve}, 
                         $d->{files}{$filename}{breviated}, 
                         scalar(@in));
    }
  }

  return $d;
}

sub _generate_reachable {
  my ($self, $m, $path) = @_;

  return;
}

sub _generate_breviated {
  my ($self, $m, $path) = @_;

  my @in = Grammar::Graph::Gobbledygook::file_to_ords($path);

  my @filtered = Grammar::Graph::Gobbledygook::shamrock_parse_to_reachable($m,
    \&Grammar::Graph::Gobbledygook::vertex_matches, \@in);

  return [ map {
    [ Grammar::Graph::Shamrock::decode_edge($_) ]
  } @filtered ];
}

sub _generate_a_tree {
  my ($self, $m, $all_edges, $input_length) = @_;

  my $pg = Grammar::Graph::Stormcloud->from_edge_list(map {
    Grammar::Graph::Shamrock::encode_edge(@$_)
  } @$all_edges);

  my $xxx = Grammar::Graph::Verdigris::verdigris(
    \&Grammar::Graph::Peachpuff::cleanup_edges, $m, $pg, 0, $input_length + 2);

  my $s = $pg->vertex_from_pos_id( 0, $m->{grammar}{anon_start_id} );
  my $f = $pg->vertex_from_pos_id( $input_length + 2, $m->{grammar}{anon_final_id} );

  return Grammar::Graph::Verdigris::_transform_nested_array($m, $pg, $s, $xxx, $f);
}

1;

__END__






