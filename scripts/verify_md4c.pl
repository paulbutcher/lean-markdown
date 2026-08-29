#!/usr/bin/env perl
# Copyright (c) 2026 Paul Butcher. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Re-checks the recorded expected output in test/vendor/md4c/*.json against what md4c's own
# md2html actually produces, at the tag scripts/build_md4c.sh pins.
#
# This closes the loop without needing to run any Lean: `lake test` proves this library agrees
# with the recorded expectations (MathGuards/MathInteractionGuards are generated from them), and
# this proves the recorded expectations agree with md4c. The deliberate divergences aren't
# recorded in these files at all -- they live in test/MathDivergenceGuards.lean -- so there is
# no exclusion list to keep in step here.
use strict;
use warnings;
use JSON::PP qw(decode_json);
use Encode qw(encode_utf8);
use File::Temp qw(tempfile);

my $root = $0; $root =~ s{/scripts/[^/]+$}{};
$root = '.' if $root eq $0;
my $md2html = "$root/build/md2html";
die "no $md2html: run scripts/build_md4c.sh first\n" unless -x $md2html;

my $failures = 0;
my $checked = 0;

for my $file (@ARGV) {
    open(my $fh, '<:raw', $file) or die "cannot open $file: $!";
    local $/;
    my $tests = decode_json(<$fh>);
    close($fh);

    for my $t (@$tests) {
        my ($tmp, $tmpname) = tempfile();
        binmode($tmp, ':raw');
        print $tmp encode_utf8($t->{markdown});
        close($tmp);
        my $got = `$md2html --flatex-math < $tmpname`;
        unlink $tmpname;
        $checked++;
        my $want = encode_utf8($t->{html});
        next if $got eq $want;
        $failures++;
        print "MISMATCH $file example $t->{example} ($t->{section})\n";
        print "  input:    " . encode_utf8($t->{markdown});
        print "  recorded: $want";
        print "  md2html:  $got";
    }
}

print "checked $checked examples against md2html, $failures mismatched\n";
exit($failures == 0 ? 0 : 1);
