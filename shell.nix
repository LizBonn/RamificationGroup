{ pkgs, ... }:
let
   pythonPackages = pkgs.python39Packages;
   tex = (pkgs.texlive.combine {
     inherit (pkgs.texlive)
       scheme-small dvisvgm
       amsmath hyperref comment;
   });
in pkgs.mkShell {
  name = "python-venv";
  venvDir = "./.venv";

  packages = with pkgs; [ tex graphviz pdf2svg elan gnumake ];

  buildInputs = [
    # A Python interpreter including the 'venv' module is required to bootstrap
    # the environment.
    pythonPackages.python

    # This executes some shell code to initialize a venv in $venvDir before
    # dropping into the shell
    pythonPackages.venvShellHook

  ];

  # Run this command, only after creating the virtual environment
  postVenvCreation = ''
    unset SOURCE_DATE_EPOCH
    pip install -r requirements.txt
  '';

  # Now we can execute any commands within the virtual environment.
  # This is optional and can be left out to run pip manually.
  postShellHook = ''
    # allow pip to install wheels
    unset SOURCE_DATE_EPOCH
  '';
}
