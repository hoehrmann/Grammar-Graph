package Grammar::Graph::Gobbledygook;

use Parse::ABNF 0.20;
use Grammar::Formal 0.20;
use Grammar::Graph 0.20;
use Grammar::Graph::Simplify;
use Data::AutoBimap;
use Graph::Directed;
use Graph::SomeUtils ':all';
use List::Util qw/min max shuffle/;
use List::MoreUtils qw/uniq first_index/;
use List::UtilsBy qw/partition_by sort_by nsort_by uniq_by/;
use List::OrderBy;
use Modern::Perl;
use Set::IntSpan;
use Storable qw/freeze thaw retrieve dclone/;
use YAML::XS;
use JSON;
use Encode;
use Grammar::Graph::TestParser;
use Grammar::Graph::Debug;
use Acme::Partitioner;
use Time::Out qw/timeout/;
use Data::Dumper;
use Grammar::Graph::Mauve;
use Grammar::Graph::Shamrock;
use Grammar::Graph::Stormcloud;
use Grammar::Graph::Verdigris;
use Grammar::Graph::Peachpuff;
use Memoize;

local $Storable::canonical = 1;

sub shamrock_parse_to_reachable {
  my ($m, $vertex_matches, $in) = @_;

  my @cx = ($m, $vertex_matches);

  my ($begin_edges, $begin_heads) = Grammar::Graph::Shamrock->begin(@cx);

  my $interior_edges = [];
  my $previous_heads = $begin_heads;

  for (my $six = 0; $six < @$in; ) {
    my $fix = $six + int(rand( @$in - $six + 1 ));

    next if $fix == $six;
    die if $fix > @$in;

    my ($block_edges, $block_heads) = Grammar::Graph::Shamrock->process_block(
      @cx, $previous_heads, $six, $fix, $in,
    );

    # must we really pass $block_heads?
    my @filtered = Grammar::Graph::Shamrock->cleanup_block(
      $m, $six + 1, $fix + 1, $block_edges, $block_heads);

    # TODO: we also ought to filter $block_heads

    $six = $fix;

    $previous_heads = $block_heads;

    push @$interior_edges, @$block_edges;
  }

  my ($final_edges, $final_heads) = Grammar::Graph::Shamrock->finalize(@cx, $previous_heads);

  my @all_edges = (@$begin_edges, @$interior_edges, @$final_edges);

  my @filtered = Grammar::Graph::Shamrock->cleanup_block(
    $m, 0, scalar(@$in) + 2, \@all_edges, []);
  
  return @filtered;
}

sub file_to_ords {
  my ($input_path) = @_;

  open my $f, '<:utf8', $input_path;
  my $chars = do { local $/; binmode $f; <$f> };
  my @input = map { ord } split//, $chars;

  return @input;
}

sub vertex_matches {
  my ($m, $v, $in) = @_;

  my $g_spans = $m->{spans};

  for (my $ix = $m->{vertices}->[$v]->{spans}; $g_spans->[$ix]; $ix += 2) {
    return 1 if ($g_spans->[$ix] <= $in and $g_spans->[$ix+1] > $in);
  }

  return 0;
}



1;

__END__

