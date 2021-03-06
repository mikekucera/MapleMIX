#!/usr/bin/perl

use Getopt::Long;
use File::Basename;
use File::Copy;
use File::Path;
use Config;

$Getopt::Long::ignorecase = 0;
$| = 1;

$ErrEOF = "Unexpected end of file";
$ThereWasAFailure = 0;

$vistimelimit = 50;

###
# Tester
###

@dirs =();
@exclude = ();
@libs =();

%CmdOpts = ( directory => \@dirs,      # directory(s) to start search of the tests
             exclude => \@exclude,     # directory(s) to exclude
             failures => ".",          # directory to put failures in
             help => 0,                # print help message
             all => 0,                 # run all sandbox tests
             f => 0,                   # run tests returned by sft -t -fm arg
             library => 0,             # run sandbox library tests
             regression => 0,          # run sandbox regression tests
             pvcs => 0,                # run sandbox pvcs tests
             internal => 0,            # run sandbox internal tests
             kernelext => 0,           # run sandbox kernelext tests
             toolbox => 0,             # run sandbox toolbox tests
	     #maple => "cmaple -s -A 2 -u",  # version of maple to use
	     maple => "maple10 -s -A 2 -u",  # version of maple to use
             #maple => "/usr/share/maple10/bin/maple -s -A 2 -u",  # version of maple to use
             #maple => "smaple -s -A 2 -u",  # version of maple to use
             compile => 1,             # compile test from tst to xtst file
             record => 1,              # recreate the failures
             remove => 0,              # remove old .xtst and .vis from dirs
             run => 1,                 # run the test
             Log => 0,                 # create a log of events
             mr => "",                 # specify MAPLE_ROOT
             testroot => "",           # specify the root location for tests
             S => 0,                   # ignore MAPLELIB
             b => \@libs,              # use the specified directory
             debug => 0,               # use debug kernel
             large => 0,               # run tests in "large" directories
             lonly => 0,               # run only "large" tests
             unfixed => 0,             # run tests in "unfixed"directories
             T => "0",                 # override time option for all tests
             L => "",                  # name of the file for logm
             cleanup => 1,             # remove compiled test from $failures
             inplace => 0,             # compile into the original directory
             retest => "",             # retest directory
             logtime => "",            # directory to log time to
             local => 1,               # look at the users directories
             preprocess => "",         # script name for preprocessing
             postprocess => "",        # script name for postprocessing
             count => 0,               # count number of tests & show progress
             sample => 0,              # make a sample file
             port => "",               # specify a port for the server
             giveup => 0,              # give up after first failure
             list => "",               # get the arguments from the file
             repeat => 1,              # repeat testing (times) until failure
             dump => "",               # dump test names into file
             multiplier => 1,          # adjustment of a multiplier
             errorbreak => 2,          # set errorbreak level
             stest => "",              # run stest tests
             longest => 0,             # only run tests with limits < than this
             start => "" );          # start with this test

GetOptions( \%CmdOpts, "directory=s@", "exclude=s@", "failures=s",
            "help", "all", "f=s", "Log", "toolbox",
            "library", "regression", "pvcs", "internal", "kernelext",
            "maple=s", "compile!", "remove!", "record!",
            "run!", "mr=s", "testroot=s", "S", "b=s@","debug",
            "large", "lonly", "T=s", "L=s", "cleanup!", "inplace", "retest=s",
            "logtime=s", "local!", "preprocess=s", "postprocess=s", "count",
            "sample", "port=s", "stest=s", "list=s", "repeat=i", "giveup",
            "dump=s", "multiplier=f", "errorbreak=i", "unfixed", "longest=i",
            "start=s" )
            || die "Can not process options";

print $CmdOpts{list};

foreach $i (@exclude)
   {
   $exclude{$i} = 1
   }

if( $CmdOpts{help} )
   {
   print <<EOF;
Usage: tester [-all] [-b=libs] [-cleanup] [-compile] [-count] [-debug]
     [-dump=<filename>] [-errorbreak=<integer>] [-exclude=dirs] [-f=<function>]
     [-failures=dir] [-giveup] [-help] [-inplace] [-internal] [-kernelext]
     [-large] [-library] [-list=<filename>] [-local] [-logtime] [-Log]
     [-longest=<limit>] [-lonly] [-L] [-maple=cmd] [-mr] [-multiplier=<float>]
     [-port=portid] [-postprocess=<script>] [-preprocess=<script>] [-pvcs]
     [-regression] [-remove] [-repeat=<number>] [-retest] [-run] [-sample]
     [-stest] [-S] [-testroot=path] [-T] [-unfixed]
EOF
   exit;
   }

$host=`hostname`;
($host)=split /\./,$host;
chomp($host);

if ( (! defined($ENV{MAPLE_ROOT})) or ($ENV{MAPLE_ROOT} eq "/u/maple/repository/main") )
   {

   open ENV, "</u/maple/repository/main/bin/env/$host.env";
   @env = <ENV>;
   @base = grep s/^\s*BASE=//, @env;

   if (@base != ())
      {
      ( $MAPLE_ROOT = $base[0] ) =~ s/\s.//g;
      chomp $MAPLE_ROOT;
      }
   else
      {
      $MAPLE_ROOT = "/u/maple/repository/main";
      }
   close ENV;
   }
else
   {
   $MAPLE_ROOT = $ENV{MAPLE_ROOT}
   }

if (defined($ENV{CYG_SYSTEM}))
   {
   $DIFFCMD = "diff --strip-trailing-cr";
   }
else
   {
   $DIFFCMD = "diff";
   }

$failures=$CmdOpts{failures};
$smaple="$CmdOpts{maple}";

$smaple .= " -q";

foreach $i (@libs)
   {
   $smaple .= " -b $i";
   }

if ( $CmdOpts{debug} )
   {
   $smaple .= " -v d"
   }

if ( $CmdOpts{S} )
   {
   $smaple .= " -S"
   }

if ( $CmdOpts{L} )
   {
   $smaple .= " -L $CmdOpts{L}"
   }

if ( $CmdOpts{port} )
   {
   $smaple .= " -p $CmdOpts{port}"
   }

if ($CmdOpts{mr} ne "")
   {
   $root = $CmdOpts{mr}
   }
else
   {
   $root = $MAPLE_ROOT;
   }

$root =~ s#/$##;

open ENV, "<$root/bin/env/$host.env";
@env = <ENV>;
@mult = grep { s/^\s*MULT=// } @env;

if (@mult != ())
   {
   ( $mult = $mult[0] ) =~ s/\s.//g;
   chomp $mult;
   }
else
   {
   $mult = 1;
   }

if ($CmdOpts{multiplier} ne "")
   {
   $mult *= $CmdOpts{multiplier};
   }

if ($CmdOpts{testroot} ne "")
   {
   $testroot = $CmdOpts{testroot}
   }
else
   {
   $testroot = $root;
   }

$failures =~ s#/$##;

$exclude{"$testroot/lib/LinearAlgebraTestbot"} = 1;

if ($CmdOpts{dump})
   {
   open DUMP, ">$CmdOpts{dump}" || die "can't open dump file";
   }

if ($CmdOpts{count} or $CmdOpts{dump})
   {
   $total = 0;
   if ($CmdOpts{all})
      {
      $total += count("$testroot/lib");
      $total += count("$testroot/test/regression");
      $total += count("$testroot/test/pvcs");
      $total += count("$testroot/internal/tst");
      $total += count("$testroot/internal/kernelext");
      $total += count("$testroot/toolbox_source");
      }
   else
      {
      if ($CmdOpts{library})
         {
         $total += count("$testroot/lib");
         }
      if ($CmdOpts{regression})
         {
         $total += count("$testroot/test/regression");
         }
      if ($CmdOpts{pvcs})
         {
         $total += count("$testroot/test/pvcs");
         }
      if ($CmdOpts{internal})
         {
         $total += count("$testroot/internal/tst");
         }
      if ($CmdOpts{kernelext})
         {
         $total += count("$testroot/internal/kernelext");
         }
      if ($CmdOpts{toolbox})
         {
         $total += count("$testroot/toolbox_source");
         }
      }
   foreach $dir (@dirs)
      {
      $total += count($dir);
      }

   $total += @ARGV;
   if ($CmdOpts{dump} && $#ARGV >= 0)
      {
      $, = "\n";
      print DUMP @ARGV;
      $, = "";
      print DUMP "\n";
      close DUMP;
      }
   }

$testnum = 0;
$passed = 0;
$skipped = 0;

# If both compiling and running, make temporary names unique to the process
# This allows several concurrent runs in the same directory.

if ( $CmdOpts{compile} && $CmdOpts{run} )
   {
   $timetmp = "time.tmp.$$";
   $outtmp  = "out.tmp.$$";
   }
else
   {
   $timetmp = "time.tmp";
   $outtmp  = "out.tmp";
   }

$timinglog = "tester.Timing.log";
$failureslog = "tester.Failures.log";
$checksumlog = "tester.Checksum.log";

if ( $CmdOpts{logtime} )
   {
   unlink("$CmdOpts{logtime}/$timinglog");
   unlink("$CmdOpts{logtime}/$failureslog");
   unlink("$CmdOpts{logtime}/$checksumlog");
   open CHSUM, ">$CmdOpts{logtime}/$checksumlog";
   }

@failedtests = ();
$totalused = 0;
$totalalloc = 0;
$totaltime = 0;

# Report the version used.

   print "\nTester uses sandbox : $root\n";
   print "Tester uses the command : $smaple (-e $CmdOpts{errorbreak})\n";

if ( (! $CmdOpts{port}) && $CmdOpts{run} )
   {
   #print "Libraries used: ";
   #print `echo libname | $smaple -t`;
   }

if ($CmdOpts{T})
   {
   print "Timing option used is : -T $CmdOpts{T}\n\n";
   }
else
   {
   print "Timing option is determined by each individual test\n\n";
   }

if( !(-d "$failures/") )
{
   my $old_mask = umask 000;
   mkdir $failures, 0777;
   umask $old_mask
}

$tempdir = "$failures/tester.tmp.$$";

sub RemoveTempDir
   {
   if( -d $tempdir )
      {
      rmtree $tempdir;
      }
   }

sub MakeTempDir
   {
   RemoveTempDir();

   my $old_mask = umask 000;
   mkdir $tempdir, 0777;
   umask $old_mask;
   }

if ($CmdOpts{retest})
   {
   @list = build_retest_list($CmdOpts{retest});
   if ($CmdOpts{count})
      {
      $total = @list + 0;
      }
   run_list(@list);

   $, = "\n";
   if ($ThereWasAFailure)
      {
      print "\nMaple failed these tests:\n", @failedtests;
      }

   print "\n\nTotal bytes used      : $totalused\n";
   print "Total bytes allocated : $totalallocated\n";
   print "Total time used       : $totaltime\n";

   exit $ThereWasAFailure;
   }

if ($CmdOpts{regression} or $CmdOpts{all})
   {
   if ($CmdOpts{run})
      {
      `date > $failures/regression_begin.$host`;
      }
   search_dir("$testroot/test/regression","$testroot/test/");
   if ($CmdOpts{run})
      {
      `date > $failures/regression_end.$host`;
      }
   }

if ($CmdOpts{pvcs} or $CmdOpts{all})
   {
   if ($CmdOpts{run})
      {
      `date > $failures/pvcs_begin.$host`;
      }
   search_dir("$testroot/test/pvcs","$testroot/test/");
   if ($CmdOpts{run})
      {
      `date > $failures/pvcs_end.$host`;
      }
   }

if ($CmdOpts{internal} or $CmdOpts{all})
   {
   if ($CmdOpts{run})
      {
      `date > $failures/internal_begin.$host`;
      }
   search_dir("$testroot/internal/tst","$testroot/internal/tst/");
   if ($CmdOpts{run})
      {
      `date > $failures/internal_end.$host`;
      }
   }

if ($CmdOpts{kernelext} or $CmdOpts{all})
   {
   if ($CmdOpts{run})
      {
      `date > $failures/kernelext_begin.$host`;
      }
   search_dir("$testroot/internal/kernelext","$testroot/internal/");
   if ($CmdOpts{run})
      {
      `date > $failures/kernelext_end.$host`;
      }
   }

if ($CmdOpts{toolbox} or $CmdOpts{all})
   {
   if ($CmdOpts{run})
      {
      `date > $failures/toolbox_begin.$host`;
      }
   search_dir("$testroot/toolbox_source","$testroot/");
   if ($CmdOpts{run})
      {
      `date > $failures/toolbox_end.$host`;
      }
   }
if ($CmdOpts{library} or $CmdOpts{all})
   {
   if ($CmdOpts{run})
      {
      `date > $failures/lib_begin.$host`;
      }
   search_dir("$testroot/lib","$testroot/");
   if ($CmdOpts{run})
      {
      `date > $failures/lib_end.$host`;
      }
   }

foreach $dir (@dirs)
   {
   search_dir($dir,"");
   }

@tests_to_run=@ARGV;

if ($CmdOpts{list})
   {
   open LIST, $CmdOpts{list};
   @more_tests=<LIST>;
   map s/\r?\n//, @more_tests;
   @tests_to_run = (@tests_to_run, @more_tests);
   close LIST;
   }

if ($CmdOpts{f})
   {
   @more_tests = split /\s+/, `sft -tester -fm $CmdOpts{f}`;
   push @tests_to_run, @more_tests
   }

$total = @tests_to_run;

run_list(@tests_to_run);

$, = "\n";
if ($ThereWasAFailure)
   {
   print "\nMaple failed these tests:\n", @failedtests;
   }

print "\n\nTotal bytes used      : $totalused\n";
print "Total bytes allocated : $totalallocated\n";
print "Total time used       : $totaltime\n";

if ($CmdOpts{logtime})
   {
   close CHSUM;
   }

if ($CmdOpts{cleanup})
   {
   RemoveTempDir()
   }

exit $ThereWasAFailure;

###################
# The Subroutines #
###################

sub run_list
   {
   my @list = @_;
   my ($test, $torun, $tocomp, $testname, $i);

   foreach $testname (@list)
      {
      $testersource = "";
      $test = translate_name($testname);
      $test =~ s/\.$/\.tst/;
      $test =~ s/\.fail$/\.tst/;
      $torun = $test;
      $failname = make_failname($test, "");

      if ($CmdOpts{compile})
         {
         $tocomp = $test;
         if (substr($test,-4,4) ne ".tst")
            {
            $tocomp .= ".tst";
            }
         if (-e $tocomp and $CmdOpts{local} )
            {
            $testersource = dirname $tocomp;
            next if !compile($tocomp, $failname);
            }
         elsif (-e "$testroot/$tocomp")
            {
            $testersource = dirname "$testroot/$tocomp";
            next if !compile("$testroot/$tocomp", $failname);
            }
         else
            {
            print "Error: No test $tocomp to compile. \n";
            }
         $torun = "$failures/".basename($tocomp);
         $prefix = "$failures/";
         }

      if ($CmdOpts{run})
         {
         $testnum++;
         unlink "$failname.fail";
         $RepeatFailure = 0;
         if (substr($torun, -5, 5) eq ".xtst")
            {
            if (! $testersource)
               {
               $testersource = dirname $torun;
               }
            for ( $i=0; $i<$CmdOpts{repeat}; $i++)
               {
               $run_number = $i+1;
               run_test($torun, $failname);
               if ($RepeatFailure)
                  {
                  last;
                  }
               }
            next;
            }
         elsif (substr($torun, -4, 4) eq ".vis")
            {
            if (! ("$torun" =~ /\.[0-9]*\.vis$/ ))
               {
               if (! $testersource)
                  {
                  $testersource = dirname $torun;
                  }
               for ( $i=0; $i<$CmdOpts{repeat}; $i++)
                  {
                  $run_number = $i+1;
                  run_visual("$torun", $failname);
                  if ($RepeatFailure)
                     {
                     last;
                     }
                  }
               }
            next;
            }
         elsif (substr($torun, -4, 4) eq ".tst")
            {
            substr($torun, -4, 4) = "";
            }

         if ( ( -e $torun.".xtst") || ( -e $torun.".vis" ) )
            {
            if ( -e $torun.".xtst" )
               {
               if (! $testersource)
                  {
                  $testersource = dirname $torun;
                  }
               for ( $i=0; $i<$CmdOpts{repeat}; $i++)
                  {
                  $run_number = $i+1;
                  run_test($torun.".xtst", $failname);
                  if ($RepeatFailure)
                     {
                     last;
                     }
                  }
               }
            if ( -e $torun.".vis" )
               {
               if (! $testersource)
                  {
                  $testersource = dirname $torun;
                  }
               for ( $i=0; $i<$CmdOpts{repeat}; $i++)
                  {
                  $run_number = $i+1;
                  run_visual($torun.".vis", $failname);
                  if ($RepeatFailure)
                     {
                     last;
                     }
                  }
               }
            }
         elsif ( ( -e "$testroot/$torun".".xtst") || ( -e "$testroot/$torun".".vis" ) )
            {
            if ( -e "$testroot/$torun".".xtst" )
               {
               if (! $testersource)
                  {
                  $testersource = dirname "$testroot/$torun";
                  }
               for ( $i=0; $i<$CmdOpts{repeat}; $i++)
                  {
                  $run_number = $i+1;
                  run_test("$testroot/$torun".".xtst", $failname);
                  if ($RepeatFailure)
                     {
                     last;
                     }
                  }
               }
            if ( -e "$testroot/$torun".".vis" )
               {
               if (! $testersource)
                  {
                  $testersource = dirname "$testroot/$torun";
                  }
               for ( $i=0; $i<$CmdOpts{repeat}; $i++)
                  {
                  $run_number = $i+1;
                  run_visual("$testroot/$torun".".vis", $failname);
                  if ($RepeatFailure)
                     {
                     last;
                     }
                  }
               }
            }
         else
            {
            print "Error: No test $torun to run. \n";
            $testnum--;
            }
         }
      if ($CmdOpts{compile} && $CmdOpts{cleanup} && dirname($torun) eq "$failures")
         {
         unlink "$torun.xtst";
         unlink glob("$torun*.vis");
         }
      }
   }

sub search_dir
   {
   my ($dir, $prefix) = @_;
   my ($i, @files);

   if ($exclude{$dir})
      {
      return
      }

   if ((not $CmdOpts{large}) and (not $CmdOpts{lonly}) and basename($dir) eq "large")
      {
      return
      }

   if ((not $CmdOpts{unfixed}) and basename($dir) eq "unfixed")
      {
      return
      }

   if ( basename($dir) eq "large" or (not $CmdOpts{lonly}))
      {
      opendir DIR, $dir;
      @files = sort grep { -f } map { "$dir/$_" } grep { /\.tst$/} readdir DIR;
      closedir DIR;

      if ( $CmdOpts{compile} and $CmdOpts{remove} )
         {
         opendir DIR, $dir;
         @remvis = sort grep { -f } map { "$dir/$_" } grep { /\.vis$/} readdir DIR;
         closedir DIR;
         opendir DIR, $dir;
         @remxtst = sort grep { -f } map { "$dir/$_" } grep { /\.xtst$/} readdir DIR;
         closedir DIR;
         unlink(@remvis);
         unlink(@remxtst);
         }

      foreach $i (@files)
         {

         $testersource = "";
         $failname = make_failname( $i, $prefix);

         if ($CmdOpts{compile})         # compile first
            {
            $testersource = dirname $i;
            next if !compile($i, $failname);
            }

         if ($CmdOpts{inplace} or ! $CmdOpts{compile})
            {
            $name = $i;
            }
         else
            {
            $name = "$failures/".basename($i);
            }
         substr($name, -4 , 4) = "";

         if ($CmdOpts{run})
            {
            unlink "$failname.fail";
            $testnum++;
            if (! ( -e $name.".xtst" or -e $name.".vis"))
               {
               print "Error: no compiled test for $i\n";
               }
            else
               {
               if (-e $name.".xtst")
                  {
                  if (! $testersource)
                     {
                     $testersource = dirname $name;
                     }
                  run_test($name.".xtst", $failname);
                  }
               if (-e $name.".vis")
                  {
                  if (! $testersource)
                     {
                     $testersource = dirname $name;
                     }
                  run_visual($name.".vis", $failname);
                  }
               }
            }

         if ($CmdOpts{compile} and $CmdOpts{cleanup})
            {
            unlink $name.".xtst";
            unlink <$name*.vis>;
            }
         }
      }
   # Now search recursively.

   opendir DIR, $dir;
   @files = sort grep -d, map "$dir/$_", readdir DIR;
   closedir DIR;

   foreach $i (@files)
      {
      if ($i ne "$dir/." and $i ne "$dir/..")
         {
         search_dir($i,$prefix);
         }
      }
   }

sub compile
   {
   my ($test, $failname) = @_;
   my $base, $result, $fails, $snip, $crash, $res, $vis;

   if( $CmdOpts{start} )
      {
      if( $test =~ /$CmdOpts{start}(\.tst)?$/ )
         {
         $CmdOpts{start} = "";
         }
      else
         {
         --$total;
         return 0;
         }
      }

   print "Compiling $test\n";

   $base = basename($test,".tst");

   if ($CmdOpts{inplace})
      {
      $res = substr($test, 0, -3)."xtst";
      }
   else
      {
      $res = "$failures/$base.xtst";
      }

   $fails = "$base.fail";
   $snip = "$base.snip";
   $crash = "$base.crash";

   if ($CmdOpts{inplace})
      {
      $vis = substr($test, 0, -4);
      }
   else
      {
      $vis = "$failures/$base"
      }

   open TEST, $test;

   while(<TEST>)
      {
      if ($_ =~ "^test" or $_ =~ "^#test")
         {
         $result = parse_test(substr($_,5), $failname, $test);
         if ($result)
            {
            last;
            }
         }
      elsif ($_ =~ "^visual" or $_=~ "^#visual")
         {
         $result = parse_visual(substr($_,7));
         if ($result)
            {
            last;
            }
         }
      }
   close TEST;
   if ($result)
      {
      open RES, ">$res";
      print RES "test\n";
      print RES "TRY(1, \"error \\\"test did not compile properly\\\";\");\n";
      print RES "end test";
      close RES;
      }

   return 1
   }

sub parse_test
   {
   my ($timelimit, $failname, $testname) = @_;
   my ($ind0, $ind1, $ind2, $ind3, $sam);

   chomp($timelimit);
   $timelimit =~ s/^\s*//;

   if ($CmdOpts{sample})
      {
      $sam = substr($res,0,-4)."smpl";
      open SAM, ">$sam" or die "Can't open $sam for writing";
      print SAM "TRY := proc(n, expr::uneval)\n";
      print SAM "          local i, ans;\n";
      print SAM "          if type(expr,'string') then\n";
      print SAM "             ans := parse(expr,'statement');\n";
      print SAM "          else\n";
      print SAM "             ans := eval(expr);\n";
      print SAM "          end if;\n";
      print SAM "          for i in indets({args[3..nargs]},\n";
      print SAM "                          'identical'('assign')='name') do\n";
      print SAM "             assign(op(2,i),ans);\n";
      print SAM "          end do;\n";
      print SAM "          ans;\n";
      print SAM "       end proc:\n";
      $rest = <TEST>;
      if (! $rest) { close SAM; return $ErrEOF; }
      while(not ($rest  =~ "^end test" or $rest =~ "^#end test"))
         {
         print SAM $rest;
         $rest = <TEST>;
         if (! $rest) { close SAM; return $ErrEOF; }
         }
      close SAM;
      close TEST;
      open TEST, $testname;
      while(<TEST>)
         {
         if ($_ =~ "^test" or $_ =~ "^#test") { last; }
         }
      }

   unlink($res);
   open RES, ">$res" or die "Can't open $res for writing";
   print RES "# timelimit $timelimit\n#\n";
   print RES "macro(TRY = TestTools:-Try):\n";

   if ($CmdOpts{record} == 0) {
      print RES "TestTools:-SetRecord(false):\n";
   }

   print RES "#","-"x59,"\n";
   print RES "# Low I/O TRY procedure - cannot detect test-specific crashes\n";
   print RES "#","-"x59,"\n";
   print RES "TRYnocrash := proc(n, expr::uneval)\n";
   print RES "local i,code;\n";
   print RES "   try\n";
   print RES "      if type(procname,'indexed') then\n";
   print RES "         code := TestTools:-Trynocrash[op(procname)](n,expr,args[3..nargs]);\n";
   print RES "      else\n";
   print RES "         code := TestTools:-Trynocrash(n,expr,args[3..nargs]);\n";
   print RES "      end if\n";
   print RES "   catch:\n";
   print RES "      code := [\n";
   print RES "         \"######### Error during call to TRY.\\n\",\n";
   print RES "         op(map(x->cat(convert(x,'string'),\"   \"), [lastexception])),\"\\n\",\n";
   print RES "         \"######### Can not reproduce the code.\\n\"\n";
   print RES "      ];\n";
   print RES "   end try:\n";
   print RES "   if not assigned(code) then\n";
   print RES "      code := [\n";
   print RES "         \"######### An untrappable error happened during call to TRY.\\n\",\n";
   print RES "         op(map(x->cat(convert(x,'string'),\"   \"), [lastexception])),\"\\n\",\n";
   print RES "         \"######### Can not reproduce the code.\\n\"\n";
   print RES "       ];\n";
   print RES "   end if;\n";
   print RES "   if [code] <> [] then\n";
   print RES "      interface(echo=0);\n";
   print RES "      if kernelopts(platform) = \"mac\" then\n";
   print RES "         appendto(\"$fails\");\n";
   print RES "      else\n";
   print RES "         appendto(\"$failures/$fails\");\n";
   print RES "      end if;\n";
   print RES "      printf(\"\\n#------------------------------------\\n\\n\\n\");\n";
   print RES "      for i in code do\n";
   print RES "         printf(\"%s\", i);\n";
   print RES "      end do;\n";
   print RES "      writeto(terminal);\n";
   print RES "   end if;\n";
   print RES "end proc:\n";
   print RES "\n";
   print RES "#","-"x59, "\n";
   print RES "# Handling for test-global crash detection\n";
   print RES "#","-"x59, "\n";
   print RES "if kernelopts(platform) = \"mac\" then\n";
   print RES "   writeto(\"$crash\");\n";
   print RES "else\n";
   print RES "   writeto(\"$failures/$crash\");\n";
   print RES "end if;\n";
   print RES "printf(\"# This test has crashed.\\n\");\n";
   print RES "writeto(terminal);\n";
   print RES "\n";
   print RES "#"x30," Test begins ","#"x30,"\n";
   $rest = <TEST>;
   if (! $rest) { close RES; return $ErrEOF; }

   while(not ($rest  =~ "^end test" or $rest =~ "^#end test"))
      {
      $ind1 = indexword ($rest, "TRY");
      $ind2 = indexword ($rest, "TestTools:-Try");
      $ind3 = indexword ($rest, "Try");

      @indsort = sort numerically $ind1, $ind2, $ind3;

      if ( $indsort[2] < 0)   # Nothing was found
         {
         print RES $rest;
         }
      else
         {
         if ($indsort[0] >= 0 )
            {
            $ind = $indsort[0];
            }
         elsif ($indsort[1] >= 0 )
            {
            $ind = $indsort[1];
            }
         else
            {
            $ind = $indsort[2];
            }

         $ind0 = index( $rest, "#");
         if ( $ind0 >= 0 and $ind0 < $ind )   # The Try was in comment anyway
            {
            print RES $rest;
            }
         else
            {
            print RES substr($rest, 0, $ind),"\n";
            $rest = substr($rest, $ind);
            print RES "#"x60,"\n";
            print RES "   code := 'code':\n";
            print RES "   failure := false:\n";
            print RES "   if kernelopts(platform) = \"mac\" then\n";
            print RES "      writeto(\"$snip\");\n";
            print RES "   else\n";
            print RES "      writeto(\"$failures/$snip\");\n";
            print RES "   end if;\n";
            print RES "   printf(\"# This code has crashed.\\n\");\n";
            print RES "   try\n";
            print RES "      code := ";
            $rest = skip_till ($rest,"[","(");
            if ($rest eq $ErrEOF)
               {
               close RES;
               return $ErrEOF;
               }

            # Now $rest starts with either [ or (.

            $sym = substr($rest,0,1);
            substr($rest,0,1) = "";
            print RES $sym;

            if ($sym eq "[")
               {
               $rest = skip_between("[","]",$rest);
               if ($rest eq $ErrEOF)
                  {
                  close RES;
                  return $ErrEOF;
                  }
               $rest = skip_till($rest,"(");
               if ($rest eq $ErrEOF)
                  {
                  close RES;
                  return $ErrEOF;
                  }
               print RES "(";
               substr($rest,0,1)="";
               }
            $rest = skip_between("(",")",$rest);
            if ($rest eq $ErrEOF)
               {
               close RES;
               return $ErrEOF;
               }
            $rest = skip_till($rest, ":", ";");
            if ($rest eq $ErrEOF)
               {
               close RES;
               return $ErrEOF;
               }
            print RES ":";
            substr($rest,0,1)="";
            print RES "\n   catch:\n";
            print RES "      code := [\n";
            print RES "         \"######### Error during call to TRY.\\n\",\n";
            print RES "         op(map(x->cat(convert(x,'string'),\"   \"), [lastexception])),\"\\n\",\n";
            print RES "         \"######### Can not reproduce the code.\\n\"\n";
            print RES "             ];\n";
            print RES "      failure := true;\n";
            print RES "   end try:\n";
            print RES "   if not assigned(code) then\n";
            print RES "      code := [\n";
            print RES "         \"######### An untrappable error happened during call to TRY.\\n\",\n";
            print RES "         op(map(x->cat(convert(x,'string'),\"   \"), [lastexception])),\"\\n\",\n";
            print RES "         \"######### Can not reproduce the code.\\n\"\n";
            print RES "             ];\n";
            print RES "      failure := true;\n";
            print RES "   end if;\n";
            print RES "   interface(echo=0);\n";
            print RES "   if kernelopts(platform) = \"mac\" then\n";
            print RES "      writeto(\"$snip\");\n";
            print RES "   else\n";
            print RES "      writeto(\"$failures/$snip\");\n";
            print RES "   end if;\n";
            print RES "   writeto(terminal);\n";
            print RES "   if [code] <> [] then\n";
            print RES "      failure := true;\n";
            print RES "      if kernelopts(platform) = \"mac\" then\n";
            print RES "         appendto(\"$fails\");\n";
            print RES "      else\n";
            print RES "         appendto(\"$failures/$fails\");\n";
            print RES "      end if;\n";
            print RES "      printf(\"\\n#------------------------------------\\n\\n\\n\");\n";
            print RES "   end if;\n";
            print RES "   for TestTools:-i in code do\n";
            print RES "      printf(\"%s\", TestTools:-i);\n";
            print RES "   end do;\n";
            if ($CmdOpts{giveup})
               {
               print RES "   if failure then\n";
               print RES "writeto(\"$timetmp\");\n";
               print RES "if assigned(printf) then\n";
               print RES "   printf(\"$failname        %d     %d %10.2f\\n\", kernelopts(bytesused), kernelopts(bytesalloc), time());\n";
               print RES "else\n";
               print RES "   iolib(9, default, \"$failname        %d     %d %10.2f\\n\", kernelopts(bytesused), kernelopts(bytesalloc), time());\n";
               print RES "   iolib(23,default);\n";
               print RES "end if:\n";
               print RES "#","-"x59, "\n";
               print RES "# Cleanup for test-global crash detection\n";
               print RES "#","-"x59, "\n";
               print RES "if kernelopts(platform) = \"mac\" then\n";
               print RES "   writeto(\"$crash\");\n";
               print RES "else\n";
               print RES "   writeto(\"$failures/$crash\");\n";
               print RES "end if;\n";
               print RES "      stop;\n";
               print RES "   end if;\n";
               }
            print RES "   writeto(terminal);\n";
            print RES "#","-"x59, "\n";
            redo;
            }
         }
      $rest = <TEST>;
      if (! $rest) { close RES; return $ErrEOF };
      }
   print RES "writeto(\"$timetmp\");\n";
   print RES "if assigned(printf) then\n";
   print RES "   printf(\"$failname        %d     %d %10.2f\\n\", kernelopts(bytesused), kernelopts(bytesalloc), time());\n";
   print RES "else\n";
   print RES "   iolib(9, default, \"$failname        %d     %d %10.2f\\n\", kernelopts(bytesused), kernelopts(bytesalloc), time());\n";
   print RES "   iolib(23,default);\n";
   print RES "end if:\n";
   print RES "#","-"x59, "\n";
   print RES "# Cleanup for test-global crash detection\n";
   print RES "#","-"x59, "\n";
   print RES "if kernelopts(platform) = \"mac\" then\n";
   print RES "   writeto(\"$crash\");\n";
   print RES "else\n";
   print RES "   writeto(\"$failures/$crash\");\n";
   print RES "end if;\n";
   print RES "writeto(terminal);\n";
   close RES;
   return 0;
   }

sub skip_between
   {
   my ($lb, $rb, $rest) = @_;
   my ($level, @chars, $inside_string);
   my (%delim, $backslashed_next);

   $inside_string = "";
   $backslashed_next = 0;
#   $delim{"\'"} = 1;
   $delim{"\""} = 1;
   $delim{"\`"} = 1;
   $level = 1;
   while (1)
      {
      @chars = split //,$rest;
      for ($i=0; $i < @chars; $i++)
         {
         print RES $chars[$i];
         if ( $backslashed_next )
            {
            $backslashed_next = 0;
            next;
            }
         if ( $delim{$chars[$i]} )
            {
            if ($inside_string eq $chars[$i] )
               {
               $inside_string = "";
               }
            elsif ($inside_string)
               {
               next;
               }
            else
               {
               $inside_string = $chars[$i];
               }
            }
         elsif ($inside_string)
            {
            if ( $chars[$i] eq "\\" )
               {
               $backslashed_next = 1;
               }
            next;
            }
         elsif ($chars[$i] eq $lb)
            {
            $level++;
            }
         elsif ($chars[$i] eq $rb)
            {
            $level--;
            if ($level == 0)
               {
               return substr($rest,$i+1);
               }
            }
         }
      $rest = <TEST> || return $ErrEOF;
      if (index($rest, "#") >=0  && $inside_string!="" )
         {
         print $rest;
         substr($rest, index($rest, "#")) = "";
         }
      }
   }

sub skip_till
   {
   my ($str, @substrs) = @_;
   my %inds;

   $inside_string = "";
   while(1)
      {
      %inds = ();
      foreach $substr (@substrs)
         {
         if (($ind = index($str, $substr)) >= 0)
            {
            $inds{$substr} = $ind;
            }
         }
      if (keys(%inds) == 0)
         {
         print RES $str;
         $str = <TEST> || return $ErrEOF;
         if (index($str, "#") >=0)
            {
            substr($str, index($str, "#")) = "";
            }
         redo;
         }
      else
         {
         $min = 10**10;
         $sym = "";
         foreach $key (keys(%inds))
            {
            if ( $inds{$key} < $min )
               {
               $min = $inds{$key};
               $sym = $key;
               }
            }
         }
      print RES substr($str, 0, $min);
      return substr($str, $min);
      }
   }

sub parse_visual
   {
   my $timelimit=$_[0];

   my ($i, $line, $writing_to_vis, $cs);

   chomp($timelimit);
   $timelimit =~ s/^\s*//;

   $cs = ($timelimit =~ /COMMAND/);
   $writing_to_vis = 1;
   $i = "";
   $line = <TEST> || return $ErrEOF;
   unlink <$vis.[0-9]*.vis>;
   open VIS, ">$vis.vis" or die "Can't open $vis.vis for writing";
   print VIS "# timelimit $timelimit\n#\n";

   while(not ($line =~ "^end visual" or $line =~ "^#end visual"))
      {
      if ($line =~ "^output" or $line =~ "^#output")
         {
         if ($writing_to_vis && ! $cs)
            {
            print VIS "writeto(\"$timetmp\");\n";
            print VIS "if assigned(printf) then\n";
            print VIS "   printf(\"$failname        %d     %d %10.2f\\n\", kernelopts(bytesused), kernelopts(bytesalloc), time());\n";
            print VIS "else\n";
            print VIS "   iolib(9, default, \"$failname        %d     %d %10.2f\\n\", kernelopts(bytesused), kernelopts(bytesalloc), time());\n";
            print VIS "   iolib(23,default);\n";
            print VIS "end if:\n";
            $writing_to_vis = 0;
            }
         close VIS;
         $i++;
         open VIS, ">$vis.$i.vis" or die "Can't open $vis.$i.vis for writing";
         }
      else
         {
         print VIS $line;
         }
      $line = <TEST>;
      if (! $line)
         {
         close VIS;
         return $ErrEOF;
         }
      }
   close VIS;
   return 0;
   }

sub run_test
   {
   my ($test, $failname) = @_;
   my ($timelimit, $base, $fail, $snip, $crash, $status, $chsum);
   my ($name, $bytesused, $bytesallocated, $time);

   # settimelimit also sets global $commandset;
   $timelimit = settimelimit($test);

   if( $CmdOpts{longest} && $timelimit > $CmdOpts{longest} )
      {
      print "Skipping $test Timelimit is $timelimit\n\n";
      ++$skipped;
      return;
      }

   MakeTempDir();

   print "Running $test";
   if ($CmdOpts{count})
      {
      print "($testnum out of $total";
      if ($CmdOpts{repeat}>1)
         {
         print ", run $run_number out of $CmdOpts{repeat}";
         }
      print ", passed $passed";
      print ", skipped $skipped" if $skipped;
      print ")";
      }

   print " Timelimit is $timelimit\n";
   if ($commandset)
      {
      print "Command is $commandset\n";
      }
   $base = basename($test,".xtst");
   $fail = "$failures/$base.fail";
   $snip = "$base.snip";
   $crash = "$base.crash";
   $output = "$failures/$base.output";
   unlink($fail);

   (my $testname = "$testersource/$base.tst") =~ s/.*$MAPLE_ROOT\///;

   if ( $CmdOpts{preprocess} )
      {
      `$CmdOpts{preprocess} $failname`;
      }

   #if ($commandset)
      #{	 
      #`MAPLE_ROOT=$root;TESTROOT=$testroot;TESTERTMP=$tempdir/;TESTER_SOURCEDIR=$testersource;MULT=$mult;CURRENT_TEST=$testname;export MAPLE_ROOT TESTROOT TESTERTMP TESTER_SOURCEDIR MULT CURRENT_TEST;$commandset $test > $output`;
      #}
   #else
      #{	
      #`MAPLE_ROOT=$root TESTROOT=$testroot TESTERTMP=$tempdir/ TESTER_SOURCEDIR=$testersource MULT=$mult CURRENT_TEST=$testname $smaple -I ${testroot}/lib -I ${testroot}/toolbox_source -T $timelimit -e $CmdOpts{errorbreak} $test > $output`;
      `$smaple -I ${testroot}/lib -I ${testroot}/toolbox_source -T $timelimit -e $CmdOpts{errorbreak} $test > $output`;
      #}
   $status = $?;

   if ( $CmdOpts{logtime} )
      {
      $chsum = `sum < $test`;
      chomp($chsum);
      print CHSUM $chsum, " $failname\n";
      }

   if (-e $fail)
      {
      print "$test Failed\n";
      $ThereWasAFailure = 1;
      $RepeatFailure =1;
      @failedtests = (@failedtests, $failname);

      if ( $CmdOpts{logtime} )
         {
         `echo "$failname" >> $CmdOpts{logtime}/$failureslog`;
         }

      if ($fail ne ("$failures/$failname".".fail"))
         {
         rename($fail, "$failures/$failname".".fail");
         }

      }

# I am reverting to determining crash by existence of non-zero
# size $snip also, since for syntax errors maple happily returns
# 0 exit status.
# Actually adding another hack - check for $timetmp

   if (-s "$failures/$snip" || $status || (! -e $timetmp))
      {
      print "$test Crashed\n";
      $ThereWasAFailure = 1;
      $RepeatFailure = 1;
      @failedtests = (@failedtests, $failname);

      `touch $failures/$snip`;
      if ( $CmdOpts{logtime} )
         {
         `echo "$failname" >> $CmdOpts{logtime}/$failureslog`;
         }
      rename("$failures/$snip", "$failures/$failname".".fail");
      }
   elsif (-s "$failures/$crash" || $status || (! -e $timetmp))
      {
      print "$test Crashed\n";
      $ThereWasAFailure = 1;
      $RepeatFailure = 1;
      @failedtests = (@failedtests, $failname);

      `touch $failures/$crash`;
      if ( $CmdOpts{logtime} )
         {
         `echo "$failname" >> $CmdOpts{logtime}/$failureslog`;
         }
      rename("$failures/$crash", "$failures/$failname".".fail");
      }
   else
      {
      open TTMP, $timetmp;
      ($name, $bytesused, $bytesallocated, $time) = split /\s+/, <TTMP>;
      $totalused += $bytesused;
      $totalallocated += $bytesallocated;
      $totaltime += $time;
      print "bytes used=$bytesused\talloc=$bytesallocated\ttime=$time\n\n";
      close TTMP;

      if ( $CmdOpts{logtime} )
         {
         `cat $timetmp >> $CmdOpts{logtime}/$timinglog`;
         }
      unlink($timetmp);
      unlink("$failures/$snip");
      }

   if (-f "$failures/$crash")
      {
      unlink("$failures/$crash");
      }

# Check Maple's return value to see if we can add a more descriptive
# error.

   if ( -e "$failures/$failname".".fail" && $status > 0 )
      {
      my ($retval, $signal, $msg);

      $retval = $status >> 8;
      $signal = $retval - 128;

      # Return values
      if( $retval == 1 )
         {
         $msg = "Maple initialization error";
         }
      elsif( $retval == 2 )
         {
         $msg = "Unexpected end of Maple input";
         }
      elsif( $retval == 3 )
         {
         $msg = "Maple could not reopen terminal";
         }
      elsif( $retval == 4 )
         {
         $msg = "Uncaught Maple exception (with errorbreak=2)";
         }
      elsif( $retval == 5 )
         {
         $msg = "Fatal error, lost connection to kernel";
         }
      # Signals (note that we're checking $signal now, not $retval)
      elsif( $signal == 6 )
         {
         $msg = "Abort Process";
         }
      elsif( $signal == 8 )
         {
         $msg = "Floating Point Exception";
         }
      elsif( $signal == 9 )
         {
         $msg = "CPU time limit exceeded";
         }
      elsif( $signal == 10 )
         {
         $msg = "Bus Error";
         }
      elsif( $signal == 11 )
         {
         $msg = "Segmentation fault";
         }
      elsif( $signal == 24 )
         {
         $msg = "Data limit exceeded";
         }
      elsif( $signal == 30 )
         {
         $msg = "Stack limit exceeded";
         }
      elsif( $signal < 0 )
         {
         $msg = "Return code $retval ($status)";
         }
      else
         {
         if( defined($Config{sig_name}) )
            {
            my @sigNames = split(' ',$Config{sig_name});
            my $sigName = $sigNames[$signal];
            if( $sigName )
               {
               $signal = "$sigName [$signal]" ;
               }
            }
         $msg = "Signal $signal ($status)";
         }

      open FAILHANDLE, ">>$failures/$failname.fail";
      print FAILHANDLE "# Execution stopped: $msg\n";

      if( open(OFP,"<$output") )
         {
         print FAILHANDLE "\n", "#" x 33, " Maple Output ", "#" x 32, "\n\n";
         while( <OFP> )
            {
            print FAILHANDLE "# $_";
            }
         close(OFP);
         }

      close FAILHANDLE;
      }

   if (-f "$output")
      {
      unlink("$output");
      }

   if ( $CmdOpts{postprocess} )
      {
      `$CmdOpts{postprocess} $failname`;
      }

   if (! $RepeatFailure)
      {
      $passed++;
      }

   if( $CmdOpts{cleanup} )
      {
      RemoveTempDir();
      }
   }

sub run_visual
   {
   my ($test, $failname) = @_;
   my ($name, $bytesused, $bytesallocated, $time);
   my $timelimit;

   # settimelimit also sets global $commandset;
   $timelimit = settimelimit($test);

   if( $CmdOpts{longest} && $timelimit > $CmdOpts{longest} )
      {
      print "Skipping $test Timelimit is $timelimit\n\n";
      ++$skipped;
      return;
      }

   MakeTempDir();

   # uniquify outtmp by appending the testname to it. Otherwise, we can run into
   # problems on Windows
   my $newouttmp;
   ($newouttmp = $test) =~ s#^.*/##g;
   $newouttmp =~ s#\.vis##;
   $newouttmp = $outtmp . "." . $newouttmp;

   print "Running $test";
   if ($CmdOpts{count})
      {
      print "($testnum out of $total";
      if ($CmdOpts{repeat}>1)
         {
         print ", run $run_number out of $CmdOpts{repeat}";
         }
      print ", passed $passed";
      print ", skipped $skipped" if $skipped;
      print ")";
      }
   print " Timelimit is $timelimit\n";
   if ($commandset)
      {
      print "Command is $commandset\n";
      }

   $wildc = substr($test,0,-3)."[0-9]*\.vis";

   if ( $CmdOpts{preprocess} )
      {
      `$CmdOpts{preprocess} $failname`;
      }

   if ($commandset)
      {
      `MAPLE_ROOT=$root;TESTROOT=$testroot;TESTERTMP=$tempdir/;TESTER_SOURCEDIR=$testersource;MULT=$mult;export MAPLE_ROOT TESTROOT TESTERTMP TESTER_SOURCEDIR MULT;$commandset < $test > $failures/$newouttmp`;
      }
   else
      {
      `MAPLE_ROOT=$root TESTROOT=$testroot TESTERTMP=$tempdir/ TESTER_SOURCEDIR=$testersource MULT=$mult $smaple -I ${testroot}/lib -I ${testroot}/toolbox_source -T $timelimit < $test > $failures/$newouttmp`;
      }
   $status = $?;
   $prod = 1;

   foreach $file (glob($wildc))
      {
      `echo "--------------- $file ------------------------" >> $failures/$newouttmp.diff`;
      `$DIFFCMD $file $failures/$newouttmp >> $failures/$newouttmp.diff`;
      $prod *= ($? >> 8) & 127;
      }

   if ($prod)
      {
      print "$test Failed\n";
      $ThereWasAFailure = 1;
      $RepeatFailure = 1;
      @failedtests = (@failedtests, $failname);

      if ( $CmdOpts{logtime} )
         {
         `echo "$failname" >> $CmdOpts{logtime}/$failureslog`;
         }

      open VISFAIL, ">>$failures/$failname.fail" || die "Can't open $failures/$failname.fail";
      print VISFAIL "# Visual failed.\n";
      print VISFAIL "# Maple code:\n";
      print VISFAIL "# ---------------------------------------------\n";
      open CODE, $test;
      while (<CODE>)
         {
         print VISFAIL "  $_";
         }
      close CODE;
      print VISFAIL "# ---------------------------------------------\n";
      print VISFAIL "# Actual output:\n";
      print VISFAIL "#----------------------------------------------\n";
      open ACTUAL, "$failures/$newouttmp";
      while (<ACTUAL>)
         {
         print VISFAIL "#-->$_";
         }
      close ACTUAL;
      print VISFAIL "#----------------------------------------------\n";
      print VISFAIL "# Expected output(s):\n";
      print VISFAIL "#----------------------------------------------\n";
      foreach $file (glob($wildc))
         {
         open EXPECT, $file;
         while(<EXPECT>)
            {
            print VISFAIL "#-->$_";
            }
         close EXPECT;
         print VISFAIL "#----------------------------------------------\n";
         }
      open DIFFS, "$failures/$newouttmp.diff";
      print VISFAIL "# Differences:\n";
      print VISFAIL "#----------------------------------------------\n";
      while (<DIFFS>)
         {
         print VISFAIL "#-->$_";
         }
      close DIFFS;
      print VISFAIL "#----------------------------------------------\n";
      close VISFAIL;
      }
   else
      {
      unlink("$failures/$snip");
      }

   if ( -s $timetmp )
      {
      open TTMP, $timetmp;
      ($name, $bytesused, $bytesallocated, $time) = split /\s+/, <TTMP>;
      $totalused += $bytesused;
      $totalallocated += $bytesallocated;
      $totaltime += $time;
      print "bytes used=$bytesused\talloc=$bytesallocated\ttime=$time\n\n";
      close TTMP;

      if ( $CmdOpts{logtime} )
         {
         `cat $timetmp >> $CmdOpts{logtime}/$timinglog`;
         }
      unlink($timetmp);
      }

   if ( $CmdOpts{postprocess} )
      {
      `$CmdOpts{postprocess} $failname`;
      }
   if ( $CmdOpts{cleanup} )
      {
      RemoveTempDir();
      # On windows, files are not always deleted by the OS immediately. Thus
      # check if the file has been deleted, and sleep if it still exists.
      # Do this a max of, say, 60 times, so as to not hang the entire test
      # process.
      my $countreps = 0;
      my $maxcountreps = 60;
      unlink("$failures/$newouttmp");
      while ( -f "$failures/$newouttmp" && $countreps < $maxcountreps )
        {
        print "Waiting for $failures/$newouttmp to finish deleting\n";
        sleep 1;
        $countreps++;
        }
      $countreps = 0;
      unlink("$failures/$newouttmp.diff");
      while ( -f "$failures/$newouttmp.diff" && $countreps < $maxcountreps )
        {
        print "Waiting for $failures/$newouttmp.diff to finish deleting\n";
        sleep 1;
        $countreps++;
        }
      }
   if (! $RepeatFailure)
      {
      $passed++;
      }
   }

sub settimelimit
   {

   my $test=$_[0];
   my $line;
   my @dummy;

   if ($CmdOpts{T})
      {
      $mult=1;
      return $CmdOpts{T}    # override time limit if given
      }                     # in command line.

   open TEST, $test;
   $line = <TEST>;
   close TEST;
   if ( $line =~ /(.*\S)\s+COMMAND\s+(.*\S)\s*/ )
      {
      $commandset = $2;
      @dummy = split /[ ,]/, $1;
      }
   else
      {
      $commandset = "";
      $line =~ s/\s*$//;
      @dummy = split /[ ,]/, $line;
      }

#   print( $line );
#   print( join( "|", @dummy ) );

   if( $dummy[2] != 0)
      {
      $dummy[2] = int($mult*$dummy[2]+0.5);
      }
   else
      {
      $dummy[2] = int($mult * 50);
      }
   if ( $dummy[2] < 4 )
      {
      $dummy[2] = 4;
      }

   return join ',', @dummy[2..@dummy-1];
   }

sub make_failname
   {
   my ($test, $prefix) = @_;

   $test =~ s/\.tst$//;
   $test =~ s/$prefix//;
   $test =~ s#/#^#g;

   # Now three special cases - maybe get rid of them later when processing
   # of the input filename is more sophisticated, e.g. can simply enter
   # test kernelext/nag/stringent/tst/sw_...

   $test =~ s/^test\^regression/regression/;
   $test =~ s/^test\^pvcs/pvcs/;
   $test =~ s/^internal\^tst\^kernel/kernel/;
   $test =~ s/^internal\^tst\^mint/mint/;
   $test =~ s/^internal\^tst\^cmaple/cmaple/;
   $test =~ s/^internal\^kernelext/kernelext/;
   $test =~ s/^toolbox_source/toolbox/;

   return $test;
   }

sub build_retest_list
   {
   my $dir = $_[0];
   my (@list, $file, @faillist);

   opendir DIR, $dir;
   @faillist = grep { /.*\.fail$/ } readdir DIR;

   foreach $file (@faillist)
      {
      $file = basename $file, ".fail";
      push @list, translate_name($file);
      }
   closedir DIR;

   return @list;
   }

sub translate_name
   {
   my $file = $_[0];

   if ($file =~ /\^/)
      {
      if ($file =~ /^regression/)
         {
         $file = "test/$file";
         }
      elsif ($file =~ /^pvcs/)
         {
         $file = "test/$file";
         }
      elsif ($file =~ /^kernelext/)
         {
         $file = "internal/$file";
         }
      elsif ($file =~ /^toolbox/)
         {
         $file =~ s/^toolbox/toolbox_source/;
         }
      elsif ($file =~ /^kernel/ || $file =~ /^mint/ || $file =~ /^cmaple/ )
         {
         $file = "internal/tst/$file";
         }
      $file =~ s#\^#/#g;
      }
   return $file;
   }


sub indexword
   {
   my ($string, $pattern) = @_;
   my $ind;

   $ind = index($string, $pattern);

   if ( $ind < 0 )
      {
      return $ind;
      }
   elsif ( substr($string, $ind + length($pattern), 1) =~ /\w/ )  # inside longer word
      {
      return -1;
      }
   else
      {
      return $ind;
      }
   }

sub numerically { $a <=> $b; }

sub count
   {
   my $dir = $_[0];
   my (@files, $total, $i);

   if ($exclude{$dir})
      {
      return 0;
      }

   if ((not $CmdOpts{large}) and (not $CmdOpts{lonly}) and basename($dir) eq "large")
      {
      return 0;
      }

   if ((not $CmdOpts{unfixed}) and basename($dir) eq "unfixed")
      {
      return 0;
      }

   if ( basename($dir) eq large or (not $CmdOpts{lonly}))
      {
      opendir DIR, $dir;
      @files = grep -f, map "$dir/$_", grep { /\.tst$/ }readdir DIR;
      closedir DIR;

      if ($CmdOpts{dump} && $#files >= 0)
         {
         $, = "\n";
         print DUMP @files;
         $, = "";
         print DUMP "\n";
         }

      $total = @files + 0;
      }

   opendir DIR, $dir;
   @files = grep -d, map "$dir/$_", readdir DIR;
   closedir DIR;

   foreach $i (@files)
      {
      if ($i ne "$dir/." and $i ne "$dir/..")
         {
         $total += count($i);
         }
      }
   return $total;
   }
