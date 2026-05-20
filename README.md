# SatQMCert

The package `SatQMCert` implements the algorithm in (Castellanos-Joo and
Kapur 2026) to compute
certificates of elements in saturated quadratic module. The algorithm
is
fully symbolic in the sense that it does not depend on numerical
algorithm to obtain certificates.

## Dependencies

- [BasicLemma](https://github.com/typesAreSpaces/BasicLemma):
  This maple package implements an algorithm of Lemma 2.1 in (Kuhlmann
  et al. 2005).
- [StrictlyPositiveCert](https://github.com/typesAreSpaces/StrictlyPositiveCert):
  This maple package implements the algorithm `Algorithm 4` proposed in
  (Shang et al. 2025) which is used to compute certificates of strictly
  positive polynomial on Archimedean quadratic modules.
- (Optional)[RealCertify](https://gricad-gitlab.univ-grenoble-alpes.fr/magronv/RealCertify):
  `RealCertify` is a maple package that also computes certificates of
  strictly positive polynomial over Archimedean quadratic modules. It
  can be used instead of `StrictlyPositiveCert` and it is used in some
  comparision benchmarks.

## Installation

Use the `make` command at the root of the project to produce the maple
library file `SatQMCert.mla`. Then, load the `SatQMCert` package by
adding the following two lines at the beginning of your maple file:

    libname := libname, "<PATH-TO-SATQMCERT>/SatQMCert.mla":
    with(SatQMCert):

## Usage and examples

The command `certInQM` has the following inputs:

- `f`: Denotes the input polynomial
- `nat`: Denotes the set of natural generators associated to the
  original generators
- `a_0`: Denotes the minimum point in the semialgebraic set associated
  to the original generators
- `b_k`: Denotes the maximum point in the semialgebraic set associated
  to the original generators
- `x`: Denotes the free variable of the ring of univariate polynomial

For examples, check the directory `tests`.

## References

Kuhlmann, S., M. Marshall, and N. Schwartz. 2005. *Positivity, Sums of
Squares and the Multi-Dimensional Moment Problem II*. 5 (4): 583--606.
<https://doi.org/10.1515/advg.2005.5.4.583>.

Shang, Weifeng, Chenqi Mou, Jose Abel Castellanos Joo, and Deepak Kapur.
2025. *Computing Certificates of Strictly Positive Polynomials in
Archimedean Quadratic Modules*. <https://arxiv.org/abs/2503.11119>.



Castellanos-Joo, Jose Abel, and Deepak Kapur. 2026. *Computing
Certificates in Archimedean Univariate Saturated Quadratic Modules*.
<https://arxiv.org/abs/2605.18980>.


