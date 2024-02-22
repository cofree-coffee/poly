{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-23.05";

    flake-utils.url = "github:numtide/flake-utils";

  };
  outputs = inputs@{ self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        agda = pkgs.agda.withPackages (p: [
          (p.standard-library.overrideAttrs (oldAttrs: {
            version = "1.7.2";
            src = pkgs.fetchFromGitHub {
              repo = "agda-stdlib";
              owner = "agda";
              rev = "177dc9e983606b653a3c6af2ae2162bbc87882ad";
              sha256 = "sha256-ovnhL5otoaACpqHZnk/ucivwtEfBQtGRu4/xw4+Ws+c=";
            };
          }))
        ]);
      in
      {
        formatter = pkgs.nixpkgs-fmt;
        devShells.default =
          pkgs.mkShell {
            buildInputs = [
              agda
            ];
          };
      });
}
