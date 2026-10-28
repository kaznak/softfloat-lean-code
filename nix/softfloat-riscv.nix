{ stdenv, fetchFromGitHub }:

# Berkeley SoftFloat 3, RISC-V specialization.
#
# Upstream has no aarch64 build directory. The x86_64 one only needs a little-endian
# 64-bit GCC with __builtin_clz and __int128, so aarch64 uses it too.
stdenv.mkDerivation {
  pname = "berkeley-softfloat-3-riscv";
  version = "3e-unstable-2025-03-07";

  src = fetchFromGitHub {
    owner = "ucb-bar";
    repo = "berkeley-softfloat-3";
    rev = "a0c6494cdc11865811dec815d5c0049fba9d82a8";
    hash = "sha256-TO1DhvUMd2iP5gvY9Hqy9Oas0Da7lD0oRVPBlfAzc90=";
  };

  makeFlags = [
    "-C"
    "build/Linux-x86_64-GCC"
    "SPECIALIZE_TYPE=RISCV"
  ];

  enableParallelBuilding = true;

  installPhase = ''
    runHook preInstall
    install -Dm644 build/Linux-x86_64-GCC/softfloat.a $out/lib/softfloat.a
    install -Dm644 -t $out/include source/include/softfloat.h source/include/softfloat_types.h
    runHook postInstall
  '';

  # The hosts where this build has been tried.
  meta.platforms = [ "x86_64-linux" "aarch64-linux" ];
}
