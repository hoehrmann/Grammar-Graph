# has input_files

package Grammar::Graph::Testsuite;
use Modern::Perl;
use Types::Standard qw/:all/;
use Graph::Directed;
use Graph::SomeUtils qw/:all/;
use List::UtilsBy qw/sort_by nsort_by partition_by/;
use List::Util qw/uniq/;
use Moo;
use Memoize;
use Log::Any qw//;
use Grammar::Graph::Testsuite::Sample;
use File::Basename;

has 'base_path' => (
  is       => 'ro',
  required => 1,
  isa      => Str,
);

sub samples {
  my ($self) = @_;

  return
    map {
      Grammar::Graph::Testsuite::Sample->new(
        base_path => $_,
      )
    }
    grep { -d }
    glob $self->base_path . '/*';
}

1;

__END__
