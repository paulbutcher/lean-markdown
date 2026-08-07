#!/usr/bin/env perl
# Extracts the example suite embedded in a CommonMark spec.txt into JSON,
# reproducing the schema produced by commonmark-spec's test/spec_tests.py
# --dump-tests. Re-run after vendoring a new spec.txt to refresh spec.json.
use strict;
use warnings;
use utf8;
binmode(STDIN, ':encoding(UTF-8)');
binmode(STDOUT, ':encoding(UTF-8)');

my ($specfile) = @ARGV;
die "usage: extract_spec.pl <spec.txt>\n" unless defined $specfile;

open(my $fh, '<:encoding(UTF-8)', $specfile) or die "cannot open $specfile: $!";

my $line_number = 0;
my $start_line = 0;
my $example_number = 0;
my @markdown_lines;
my @html_lines;
my $state = 0; # 0 regular text, 1 markdown example, 2 html output
my $headertext = '';
my $extensions = '';
my @tests;

sub json_string {
    my ($s) = @_;
    $s =~ s/\\/\\\\/g;
    $s =~ s/"/\\"/g;
    $s =~ s/\t/\\t/g;
    $s =~ s/\r/\\r/g;
    $s =~ s/\n/\\n/g;
    $s =~ s/([\x00-\x1f])/sprintf('\u%04x', ord($1))/ge;
    return $s;
}

while (my $line = <$fh>) {
    $line_number++;
    (my $l = $line) =~ s/^\s+|\s+$//g;
    if ($l =~ /^(?:`{32}) example(?:\s+(.*))?$/) {
        $state = 1;
        $extensions = defined $1 ? $1 : '';
    } elsif ($state == 2 && $l eq ('`' x 32)) {
        $state = 0;
        $example_number++;
        my $end_line = $line_number;
        my $markdown = join('', @markdown_lines);
        my $html = join('', @html_lines);
        $markdown =~ s/\x{2192}/\t/g;
        $html =~ s/\x{2192}/\t/g;
        push @tests, {
            markdown    => $markdown,
            html        => $html,
            example     => $example_number,
            start_line  => $start_line,
            end_line    => $end_line,
            section     => $headertext,
            extensions  => $extensions,
        };
        $start_line = 0;
        @markdown_lines = ();
        @html_lines = ();
        $extensions = '';
    } elsif ($l eq '.') {
        $state = 2;
    } elsif ($state == 1) {
        $start_line = $line_number - 1 if $start_line == 0;
        push @markdown_lines, $line;
    } elsif ($state == 2) {
        push @html_lines, $line;
    } elsif ($state == 0 && $line =~ /^#+ /) {
        ($headertext = $line) =~ s/^#+ //;
        $headertext =~ s/^\s+|\s+$//g;
    }
}
close($fh);

print "[\n";
for my $i (0 .. $#tests) {
    my $t = $tests[$i];
    print "  {\n";
    print '    "markdown": "' . json_string($t->{markdown}) . "\",\n";
    print '    "html": "' . json_string($t->{html}) . "\",\n";
    print '    "example": ' . $t->{example} . ",\n";
    print '    "start_line": ' . $t->{start_line} . ",\n";
    print '    "end_line": ' . $t->{end_line} . ",\n";
    print '    "section": "' . json_string($t->{section}) . "\",\n";
    print '    "extensions": "' . json_string($t->{extensions}) . "\"\n";
    print "  }" . ($i < $#tests ? ",\n" : "\n");
}
print "]\n";
