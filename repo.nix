{ pkgs }: {
  shell = pkgs.mkShell rec {
    name = "tlaplus-dev-shell";

    buildInputs = with pkgs; [
      tlaplus
    ];
  };
}
