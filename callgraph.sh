#!/bin/sh

# Copyright (c) 2004-2007 Juan M. Bello Rivas <jmbr@superadditive.com>
#
# Permission is hereby granted, free of charge, to any person
# obtaining a copy of this software and associated documentation files
# (the "Software"), to deal in the Software without restriction,
# including without limitation the rights to use, copy, modify, merge,
# publish, distribute, sublicense, and/or sell copies of the Software,
# and to permit persons to whom the Software is furnished to do so,
# subject to the following conditions:
#
# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
# BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
# ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
# CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

prog_name="callgraph"

if [ $# -lt 1 ]; then
    echo "Usage: $prog_name EXECUTABLE [ARGS...]"
    echo
    echo "Example: $prog_name ~/bin/test-program foo 23"
    exit 1
fi

# Sanity checks.
FILE=$1

if [ ! -x $FILE ]; then
    echo "$prog_name: Unable to find executable '$FILE'"
    exit 1
fi

LANG="" gdb --eval-command=quit $FILE 2>&1 \
    | grep -E '(no\ debugging\ symbols\ found|not\ in\ executable\ format)' 2>&1 > /dev/null
if false; then # [ $? -eq 0 ]; then
    echo -n "$prog_name: Can't print call graph for '$FILE' because it's not a "
    echo "binary executable compiled with debugging symbols."
    exit 1;
fi

shift

# Set up temporary files.
TRACE="`mktemp -t $prog_name.XXXXXXXXXX`" || exit
GETFUNCS="`mktemp -t $prog_name.XXXXXXXXXX`" || exit
trap 'rm -f -- "$GETFUNCS"' EXIT
trap 'trap - EXIT; rm -f -- "$TRACE" "$GETFUNCS"; exit 1' HUP INT QUIT TERM

# Take control of GDB and print call graph.
cat > $GETFUNCS <<EOF
set height 0
info functions
EOF

gdb --batch --command=$GETFUNCS $FILE 2>/dev/null | awk '
function get_func_name(str)
{
  len = split(str, part, "  ");

  return part[len];
}

BEGIN {
  total = 0;
  print "set width 0";
  print "set height 0";
  print "set verbose off";
}

/^0x[0-9a-f]*  (.*)$/ {
  fn = get_func_name($0);
  printf("break %s\n", fn);
  ++total;
}

END {
  for (i = 1; i <= total; i++) {
    print "commands", i;
    /* print "info args"; */
    print "backtrace 2";
    print "continue";
    print "end";
  }

  print "run"
}
' > $TRACE

gdb --batch --command=$TRACE --tty=/dev/null --args $FILE $@ 2>/dev/null | awk '
function get_callee(s)
{
  split(s, info, ",");
  split(info[2], fn, " ");
  callee = fn[1];

  return callee;
}

function get_params(s, n)
{
  split(s, par, n);
  split(par[2], par, " at ");
  sub(/ \(/, "(", par[1]);

  return par[1];
}

BEGIN {
  isrecord = 0;
  callee = "";
  caller = "*INITIAL*";
  params = "";
}

/^Breakpoint [0-9]+,/ {
  isrecord = 1;

  callee = get_callee($0);
  params = get_params($0, callee);
}

/^#1[ \t]+/ {
  if (isrecord)
    caller = $4;
}

/^$/ {
  if (isrecord && (caller != "*INITIAL*")) {
    printf("%s %s %s\n", caller, callee, params);
    callee = caller = params = "";
  }
}
'
