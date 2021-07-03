{
  description = "TLA+ Radix Tree Specifications";

  inputs.nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };

        repo = pkgs.callPackage ./repo.nix {
          inherit pkgs;
        };
      in {
        devShell = repo.shell;
      }
    );
}
