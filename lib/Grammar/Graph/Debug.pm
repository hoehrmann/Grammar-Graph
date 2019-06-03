package Grammar::Graph::Debug;
# use Algorithm::ConstructDFA::XS 0.24;
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
use Modern::Perl;
use Set::IntSpan;
use Storable qw/freeze thaw retrieve/;
use YAML::XS;
use JSON;
use Encode;

use Grammar::Graph::TestParser;

local $Storable::canonical = 1;

sub _encode {
  Grammar::Graph::TestParser::_encode(@_);
}

sub _decode {
  Grammar::Graph::TestParser::_decode(@_);
}

sub parsegraph_to_graphviz {
  my ($g, $pg, $path) = @_;

  open my $pgf, '>', $path;

  say $pgf "digraph G {";

  for my $v (sort $pg->vertices) {
    my ($vix, $vid, $vd) = _decode($v);
    my $label = $g->g->get_vertex_attribute($vid, 'label');
    my $name = UNIVERSAL::can($label, 'name') ? $label->name : '';
    my $type = ref($label) =~ s/.*:://r;
    my $spans = (UNIVERSAL::can($label, 'spans') ? $label->spans : '');
    $spans =~ s/.{10,}$/.../;
    printf $pgf qq("%s"[label="%s %s %s %s",color="%s"];\n),
      join(',', $vix, $vid, $vd ? $vd : ()),
      join(',', $vix, $vid, $vd ? $vd : ()),
      $type,
      $name,
      $spans,
#      $keep{$v} ? 'black' : 'red'
      'black'
  }

  printf $pgf qq("%s" -> "%s";\n),
    join(',', _decode($_->[0])),
    join(',', _decode($_->[1])),
      for $pg->edges;

  say $pgf "}";
  close $pgf;
}

# FIXME: misnamed
sub subgraph_to_graphviz {
  my ($g) = @_;

  # FIXME
  open my $dot, '>', 'd.dot';

  say $dot "digraph G {";

  for (sort $g->g->vertices) {
    my $label = $g->get_vertex_label($_);
    my $type = ref($label) =~ s/.*:://r;
    my $name = UNIVERSAL::can($label, 'name') ? $label->name : '';
    $name ||= UNIVERSAL::can($label, 'ref') ? $label->ref : '';
    my $spans = (UNIVERSAL::can($label, 'spans') ? $label->spans : '');
    $spans =~ s/(.{10,})$/.../;
    printf $dot "%u[label=\"%u: %s %s %s\"];\n",
      $_, $_, $type//'', $name//'',
        $spans;
  }

  for ($g->g->edges) {
      my ($v1, $v2) = @$_;
      print $dot join "->", $v1, $v2;
      print $dot ";\n";
  }

  say $dot '}';

  close $dot;

}



1;

__END__

