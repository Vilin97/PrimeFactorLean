#!/usr/bin/env bash
# Build the native baselines used for the head-to-head comparison, from pinned
# sources and pinned distribution packages, into baselines/ (gitignored).
# Heavy steps hold the shared benchmark lock so that they never overlap timed
# runs of other projects on this machine.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BASE="$ROOT/baselines"
SRC="$BASE/src"
PREFIX="$BASE/prefix"
LOCK=/tmp/vas-timed-benchmarks.lock
JOBS="${JOBS:-16}"
mkdir -p "$SRC" "$PREFIX" "$BASE/debs"

# Pinned versions.
DEBS="libgmp-dev=2:6.3.0+dfsg-5ubuntu2 libgmpxx4ldbl=2:6.3.0+dfsg-5ubuntu2
      libecm1=7.0.6+ds-2 libecm1-dev=7.0.6+ds-2 libecm1-dev-common=7.0.6+ds-2
      libhwloc-dev=2.13.0-2 libhwloc15=2.13.0-2
      python3-flask=3.1.3-1ubuntu1 python3-werkzeug=3.1.5-1 python3-itsdangerous=2.2.0-2build1"
CMAKE_VERSION=3.31.12
YAFU_COMMIT=8110dfbd8c6f
CADO_COMMIT=692ecb7e62f0

locked() { flock "$LOCK" "$@"; }

checkout() { # url dir commit
  if [ ! -d "$SRC/$2/.git" ]; then git clone --quiet "$1" "$SRC/$2"; fi
  git -C "$SRC/$2" fetch --quiet origin || true
  git -C "$SRC/$2" checkout --quiet "$3"
}

# GMP 6.3.0, GMP-ECM 7.0.6, hwloc and Flask (CADO-NFS' work-unit server) from
# the distribution archive (no root needed: packages are downloaded and
# unpacked into $PREFIX). The runtime libgmp.so.10 is the system's.
LIB="$PREFIX/usr/lib/x86_64-linux-gnu"
if [ ! -f "$PREFIX/usr/include/ecm.h" ]; then
  (cd "$BASE/debs" && apt-get download $DEBS)
  for d in "$BASE"/debs/*.deb; do dpkg -x "$d" "$PREFIX"; done
  ln -sf /usr/lib/x86_64-linux-gnu/libgmp.so.10.5.0 "$LIB/libgmp.so.10.5.0"
  ln -sf /usr/lib/x86_64-linux-gnu/libgmp.so.10 "$LIB/libgmp.so.10"
fi

# CMake (prebuilt release binary; CADO-NFS build dependency).
if [ ! -x "$BASE/cmake/bin/cmake" ]; then
  curl -sSL -o "$SRC/cmake.tar.gz" \
    https://github.com/Kitware/CMake/releases/download/v$CMAKE_VERSION/cmake-$CMAKE_VERSION-linux-x86_64.tar.gz
  rm -rf "$BASE/cmake" && mkdir -p "$BASE/cmake"
  tar xf "$SRC/cmake.tar.gz" -C "$BASE/cmake" --strip-components=1
fi

checkout https://github.com/bbuhrow/yafu.git yafu "$YAFU_COMMIT"
checkout https://gitlab.inria.fr/cado-nfs/cado-nfs.git cado-nfs "$CADO_COMMIT"

# YAFU 3 (its tree vendors ytools/ysieve): AVX-512 + IFMA SIQS, OpenMP, GMP-ECM.
if [ ! -x "$SRC/yafu/yafu" ]; then
  (cd "$SRC/yafu" && locked make -j"$JOBS" yafu CC=gcc OMP=1 ECM=1 USE_AVX512=1 \
      USE_AVX512IFMA=1 USE_BMI2=1 NO_ZLIB=1 \
      GMP_INCDIR="$PREFIX/usr/include/x86_64-linux-gnu" GMP_LIBDIR="$LIB" \
      ECM_INCDIR="$PREFIX/usr/include" ECM_LIBDIR="$LIB")
fi

# CADO-NFS: optimized native build (-O3 -march=native -DNDEBUG).
P="$PREFIX/usr"
cat > "$SRC/cado-nfs/local.sh" <<LOCAL
build_tree=$BASE/build/cado-nfs
CC=gcc
CXX=g++
CFLAGS="-O3 -march=native -DNDEBUG -I$P/include -I$P/include/x86_64-linux-gnu"
CXXFLAGS="-O3 -march=native -DNDEBUG -I$P/include -I$P/include/x86_64-linux-gnu"
GMP_INCDIR=$P/include/x86_64-linux-gnu
GMP_LIBDIR=$LIB
HWLOC_INCDIR=$P/include
HWLOC_LIBDIR=$LIB
GMPECM_INCDIR=$P/include
GMPECM_LIBDIR=$LIB
CMAKE=$BASE/cmake/bin/cmake
export PATH=$BASE/cmake/bin:\$PATH
export PYTHONPATH=$P/lib/python3/dist-packages
LOCAL
if [ ! -x "$BASE/build/cado-nfs/sieve/las" ]; then
  (cd "$SRC/cado-nfs" && export PATH="$BASE/cmake/bin:$PATH" && locked make cmake && locked make -j"$JOBS")
fi
echo "baselines ready: $SRC/yafu/yafu, $BASE/build/cado-nfs/cado-nfs.py"
echo "run with LD_LIBRARY_PATH=$LIB PYTHONPATH=$P/lib/python3/dist-packages"
