{ stdenv, fetchFromGitHub, softfloat-riscv }:

# Berkeley TestFloat 3, linked against softfloat-riscv.
#
# `testfloat` is not built: it assumes long double is x87 80-bit, which fails on
# aarch64, and this project only uses the generated vectors.
stdenv.mkDerivation {
  pname = "berkeley-testfloat-3-riscv";
  version = "3e-unstable-2025-03-07";

  src = fetchFromGitHub {
    owner = "ucb-bar";
    repo = "berkeley-testfloat-3";
    rev = "a9c849f1b0eb0264b626d9686ffae167d996e3be";
    hash = "sha256-/rCTt+EAjQ/coi+pDpdZjCafS2cHNi9o7swIEeBNtDk=";
  };

  makeFlags = [
    "-C"
    "build/Linux-x86_64-GCC"
    "SOFTFLOAT_INCLUDE_DIR=${softfloat-riscv}/include"
    "SOFTFLOAT_LIB=${softfloat-riscv}/lib/softfloat.a"
  ];

  buildFlags = [
    "testfloat_gen"
    "testfloat_ver"
    "testsoftfloat"
    "timesoftfloat"
  ];

  enableParallelBuilding = true;

  installPhase = ''
    runHook preInstall
    install -Dm755 -t $out/bin \
      build/Linux-x86_64-GCC/testfloat_gen \
      build/Linux-x86_64-GCC/testfloat_ver \
      build/Linux-x86_64-GCC/testsoftfloat \
      build/Linux-x86_64-GCC/timesoftfloat
    runHook postInstall
  '';

  # testfloat_gen output was byte-identical on both (2026-10-09).
  meta.platforms = [ "x86_64-linux" "aarch64-linux" ];
}
