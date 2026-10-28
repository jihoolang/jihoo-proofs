{
  description = "Compile-time proof checking experiments for jihoo";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    # The compiler under test. Move it with `nix flake update jihoo`.
    jihoo.url = "github:jihoolang/jihoo";
    jihoo.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { self, nixpkgs, jihoo }:
    let
      lib = nixpkgs.lib;
      systems = [ "x86_64-linux" "aarch64-linux" ];
      forAllSystems = f: lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in
    {
      devShells = forAllSystems (pkgs:
        let llvm = pkgs.llvmPackages_21; in
        {
          default = pkgs.mkShell {
            nativeBuildInputs = [
              jihoo.packages.${pkgs.stdenv.hostPlatform.system}.jihoo
              llvm.llvm # opt, for checking that verification is erased at O2
              pkgs.python3
            ];
          };

          # Rust is only an oracle for the optional Horn differential suites.
          differential = pkgs.mkShell {
            inputsFrom = [ self.devShells.${pkgs.stdenv.hostPlatform.system}.default ];
            packages = [ pkgs.rustc pkgs.cargo ];
          };
        });
    };
}
