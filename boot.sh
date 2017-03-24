#!/bin/bash

set -e

dir="$1"

if [ -z "$dir" -o -d "$dir" ]
then
  echo "Usage: $0 directory/"
  echo "(directory must not exist)"
  exit 1
fi

# veggies=
# if [ -x "./veggies" ]; then veggies="$PWD/veggies"
# else if whereis veggies >/dev/null; then veggies="veggies";
# else echo "Coult not find ./veggies or veggies in the PATH."; exit 1; fi; fi

if ! [ -d boot-data ]; then echo "Could not find ./boot-data/."; exit 1; fi

mkdir $dir
dir="$(readlink -f $dir)"
mkdir $dir/bin
mkdir $dir/dist
mkdir $dir/libexec
mkdir $dir/lib
mkdir $dir/package.conf.d

ghc-pkg --package-db $dir/package.conf.d recache

cp -v boot-data/settings boot-data/platformConstants $dir

ghc -O -package ghc \
    -ivellvm-ast-pp/ \
    Main.hs \
    -o $dir/libexec/veggies

cat > $dir/bin/veggies <<__END__
#!/bin/sh
topdir="$dir"
executablename="$dir/libexec/veggies"
exec "\$executablename" -B"\$topdir" \${1+"\$@"}
__END__
chmod +x  $dir/bin/veggies

cd fake-rts
clang-4.0 -c rts.ll
ar rcs libHSrts.a rts.o
mkdir $dir/lib/rts
cp -v libHSrts.a $dir/lib/rts
cd ..
cp -v boot-data/rts.conf $dir/package.conf.d/

cp -vr boot-data/include $dir/include

sed -i -e "s,^library-dirs: .*,library-dirs: $dir/lib/rts," $dir/package.conf.d/rts.conf
sed -i -e "s,^include-dirs: .*,include-dirs: $dir/include," $dir/package.conf.d/rts.conf
ghc-pkg --package-db $dir/package.conf.d recache


echo "Building ghc-prim"
cd ghc-prim/
ghc --make Setup.hs
./Setup configure --builddir $dir/dist/prim --package-db=$dir/package.conf.d -w $dir/bin/veggies --prefix $dir
./Setup build --builddir $dir/dist/prim
./Setup install --builddir $dir/dist/prim
cd ..
sed -i -e 's,^exposed-modules:,exposed-modules: GHC.Prim,' $dir/package.conf.d/ghc-prim-*.conf
ghc-pkg --package-db $dir/package.conf.d recache


echo "Building integer-gmp"
cd integer-gmp
ghc --make Setup.hs
./Setup configure --builddir $dir/dist/integer-gmp --package-db=$dir/package.conf.d -w $dir/bin/veggies --prefix $dir
./Setup build     --builddir $dir/dist/integer-gmp
./Setup install   --builddir $dir/dist/integer-gmp
cd ..

echo "Building base"
ghc --make base/Setup.hs
cd base
./Setup configure --builddir $dir/dist/base --package-db=$dir/package.conf.d -w $dir/bin/veggies --prefix $dir -finteger-gmp
./Setup build     --builddir $dir/dist/base
./Setup install   --builddir $dir/dist/base
cd ..

echo "Veggies succesfully bootstraped."
echo "You can use $dir/bin/veggies now."
