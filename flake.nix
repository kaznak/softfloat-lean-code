{
  description = "Development environment for softfloat-lean";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";

  outputs = { self, nixpkgs }:
    let
      supportedSystems = [ "x86_64-linux" "aarch64-linux" ];
      forAllSystems = nixpkgs.lib.genAttrs supportedSystems;
    in
    {
      packages = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
          softfloat-riscv = pkgs.callPackage ./nix/softfloat-riscv.nix { };
        in
        {
          inherit softfloat-riscv;
          testfloat-riscv = pkgs.callPackage ./nix/testfloat-riscv.nix { inherit softfloat-riscv; };
        });

      devShells = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
        in
        {
          default = pkgs.mkShell {
            packages = with pkgs; [
              bashInteractive
              coreutils
              less
              findutils
              gnumake
              # flock, which the Makefile takes so that two builds in one tree do not overlap.
              util-linux
              shellcheck

              cacert
              curl
              elan
              git
              jq
              yq-go

              self.packages.${system}.testfloat-riscv
            ];
          };
        });
    };
}
