#!/bin/sh

scriptname=`basename $0`

. `dirname $0`/colors.sh || exit 1

############################################################################

usage() {
cat <<EOF
usage: $scriptname [ <option> ]

where '<option>' is one of the following:

-h         print this command line option summary
-j[ ]<n>   number '<n>' of parallel threads (passed to 'makefile')
-s[ ]<n>   number '<n>' of starting configuration
-m | -m32  include 32 bit tests
EOF
exit 0
}

die () {
  echo "$scriptname: ${BAD}${BOLD}error${NORMAL}: $*" 1>&2
  exit 1
}

fatal () {
  echo "$scriptname: ${BAD}${BOLD}fatal internal error${NORMAL}: $*" 1>&2
  exit 1
}

############################################################################

if [ -f configure ]
then
  configure="./configure"
  makeoptions=""
elif [ -f ../configure ]
then
  configure="../configure"
  makeoptions=" -C .."
else
  die "Can not find 'configure'."
fi

if [ "$CXX" = "" ]
then
  environment=""
else
  environment="CXX=$CXX "
fi

if [ ! "$CXXFLAGS" = "" ]
then
  [ "$environment" = "" ] || environment="$environment "
  environment="${environment}CXXFLAGS=\"$CXXFLAGS\" "
fi

############################################################################

ok=0
skipped=0
running="unknown"

skip() {
  test $m32 = yes && return 1
  while [ $# -gt 0 ]
  do
    case "$1" in
      -m32) return 0;;
    esac
    shift
  done
  return 1
}

run () {
  if [ "$*" = "" ]
  then
    configureoptions=""
  else
    configureoptions=" $*"
  fi
  if skip $*
  then
    echo "[$running] $environment$configure$configureoptions # skipped"
    skipped=`expr $skipped + 1`
  else
    echo "[$running] $environment$configure$configureoptions && make$makeoptions$makeflags && make$makeoptions$makeflags test && make$makeoptions$makeflags clean"
    $configure$configureoptions $* >/dev/null 2>&1
    test $? = 0 || die "configuration $running failed (run '$configure$configureoptions $*' to investigate)"
    make$makeoptions$makeflags >/dev/null 2>&1
    test $? = 0 || die "building configuration $running failed (run 'make' to investigate)"
    make$makeoptions$makeflags test >/dev/null 2>&1
    test $? = 0 || die "testing configuration $running failed (run 'make test' to investigate)"
    make$makeoptions$makeflags clean >/dev/null 2>&1
    test $? = 0 || die "cleaning configuration $running failed (run 'make clean' to investigate)"
    ok=`expr $ok + 1`
  fi
}

############################################################################

begin=0
end=32

m32=no

while [ $# -gt 0 ]
do
  case "$1" in
    -h) usage;;
    -j[1-9]|-j[1-9][0-9]*)
       makeflags=" -j`echo @$1 |sed -e 's,@-j,,'`"
       ;;
    -j) 
        shift
	test $# = 0 && die "argument to '-j' missing'"
	case "$1" in
	  [0-9]|[1-9][0-9]) makeflags="$1" ;;
	  *) die "invalid argument in '-j $1'" ;;
	esac
	;;
    -m|-m32) m32=yes;;
    -s[0-9]|-s[1-9][0-9])
       begin=`echo "@$1" |sed -e 's,@-s,,'`
       test $begin -gt $end && \
         die "invalid start configuration '$1' (above end '$end')"
       ;;
    -s) 
        shift
	test $# = 0 && die "argument to '-s' missing'"
	case "$1" in
	  [0-9]|[1-9][0-9]*) begin="$1" ;;
	  *) die "invalid argument in '-s $1'" ;;
	esac
	 test $begin -gt $end && \
	   die "invalid start configuration '-s $1' (above end '$end')"
	;;
    *)
      die "invalid option '$1' (try '-h')"
      ;;
  esac
  shift
done

############################################################################

map_and_run () {

  running="$1" # such that 'run' knows the configuration number

  case $1 in	# default configuration (depends on 'MAKEFLAGS'!)
    0) run -p;;	# then check default pedantic first

    1) run -q;;	# library users might want to disable messages
    2) run -q -p;;	# also check '--quiet' pedantically

    # now start with the five single options

    3) run -a;;	# actually enables all the four next options below
    4) run -c;;
    5) run -g;;
    6) run -l;;

    # all five single options pedantically

    7) run -a -p;;
    8) run -c -p;;
    9) run -g -p;;
    10) run -l -p;;

    # all legal pairs of single options
    # ('-a' can not be combined with any of the other options)
    # ('-g' can not be combined '-c')

    11) run -c -l;;
    12) run -c -q;;
    13) run -g -l;;
    14) run -g -q;;

    # the same pairs but now with pedantic compilation

    15) run -c -l -p;;
    16) run -c -q -p;;
    17) run -g -l -p;;
    18) run -g -q -p;;

    # finally check that these also work to some extend

    19) run --no-unlocked -q;;
    20) run --no-unlocked -a -p;;

    21) run --no-contracts -q;;
    22) run --no-contracts -a -p;;

    23) run --no-tracing -q;;
    24) run --no-tracing -a -p;;

    25) run -m32 -q;;
    26) run -m32 -a -p;;

    # Shared library builds

    27) run -shared;;
    28) run -shared -p;;
    29) run -shared -p -m32;;

    # Sanitizer configurations

    30) run -a -fsanitize=address -fsanitize=undefined;;
    31) run -a -p -fsanitize=address -fsanitize=undefined;;
    32) run -a -Wswitch-enum -p -Wextra -Wall -Wextra -Wformat=2 -Wswitch-enum -Wpointer-arith -Winline -Wundef -Wcast-qual -Wwrite-strings -Wunreachable-code -Wstrict-aliasing=3 -fno-common -fstrict-aliasing -Wno-format-nonliteral

      executed_last_configuration=yes # Keep this as part of last configuration!

      ;; 

    *) fatal "iterating over invalid configuration '$1'";;
  esac
}

############################################################################


built_and_tested=0;
configurations=`expr $end + 1`
executed_last_configuration=no

echo "building and testing ${BOLD}$configurations${NORMAL} configurations 0..$end"

if [ $begin = 0 ]
then
  echo "starting with default configuration $begin"
else
  echo "starting with non-default configuration $begin (and then wrapping around)"
fi

i=$begin
while [ $built_and_tested -lt $configurations ]
do
  map_and_run $i
  built_and_tested=`expr $built_and_tested + 1`
  i=`expr $i + 1`
  [ $i -gt $end ] && i=0
done

############################################################################

test $executed_last = no && fatal "last configuration not executed"

if [ $skipped = 0 ]
then
  echo "successfully built and tested ${GOOD}${ok}${NORMAL} configurations (none skipped)"
else
  echo "successfully built and tested ${GOOD}${ok}${NORMAL} configurations ($skipped skipped)"
fi
