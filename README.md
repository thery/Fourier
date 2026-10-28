<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Fourier

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/thery/Fourier/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/thery/Fourier/actions/workflows/docker-action.yml




Fourier tactic for rat

## Meta

- Author(s):
  - Laurent Théry
- License: [MIT License](LICENSE)
- Additional dependencies:
  - [MathComp ssreflect 2.6 or later](https://math-comp.github.io)
  - [MathComp algebra 2.6 or later](https://math-comp.github.io)
- Rocq/Coq namespace: `Fourier`
- Related publication(s): none

## Building and installation instructions

To build and install manually, you need to make sure that all the
libraries this development depends on are installed.  The easiest way to do that
is still to rely on opam:

``` shell
git clone https://github.com/thery/Fourier.git
cd Fourier
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



