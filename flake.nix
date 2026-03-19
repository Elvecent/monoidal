{
  description = "Agda + Cubical dev shell";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
  };

  outputs = inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];

      perSystem = { pkgs, ... }:
        let
          agdaWithCubical = pkgs.agda.withPackages (p: [ p.cubical ]);
        in
        {
          devShells.default = pkgs.mkShell {
            buildInputs = [ agdaWithCubical ];
            shellHook = ''
              echo "Agda $(agda --version) with cubical library ready."
            '';
          };
        };
    };
}
