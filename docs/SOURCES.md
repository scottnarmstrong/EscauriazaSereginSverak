# Mathematical sources

The references below are the bibliography of [the manuscript](../paper/ess.tex),
with citation keys from [refs.bib](../paper/refs.bib), together with two further
works consulted (Seregin's lecture notes and Tao's paper). Inclusion here does not
mean that every result in a reference is a formalized dependency. The
adopted mathematical scope and the departures from these sources are recorded
in [DEVIATIONS.md](DEVIATIONS.md) and [the design notes](DESIGN_NOTES.md).

The manuscript follows Escauriaza, Seregin and Šverák for the regularity,
backward-uniqueness and unique-continuation theorems. The existence theorem,
which follows the review of Ożański and Pooley with the suitability arguments
of Tsai and of Robinson, Rodrigo and Sadowski, is proved in the CKN library
and its paper (the Leray sources below are those of that part; see the
[CKN repository](https://github.com/scottnarmstrong/CaffarelliKohnNirenberg)). Where it replaces a step of
these sources by a different argument, a “Departure from” remark in the
manuscript says so; its appendix `app:errata` records corrections to the
sources.

## Primary sources

- **Escauriaza, Luis; Seregin, Gregory A.; Šverák, Vladimír.**
  “$L_{3,\infty}$-solutions of Navier–Stokes equations and backward
  uniqueness.” *Russian Mathematical Surveys* **58**(2), 211–250 (2003).
  [DOI: 10.1070/RM2003v058n02ABEH000609](https://doi.org/10.1070/RM2003v058n02ABEH000609).
  Theorems 1.3 and 1.4, the unique-continuation Theorem 4.1, the
  backward-uniqueness Theorem 5.1 and the Carleman Propositions 6.1–6.2 are
  the results formalized in the regularity part; Theorem 1.3 is formalized in
  full, its smoothness clause through Theorem 1.2, the
  Ladyzhenskaya–Prodi–Serrin theorem, which is formalized in Part VI of the
  manuscript. Key: `ESS2003`.

- **Ożański, Wojciech S.; Pooley, Benjamin C.** “Leray's fundamental work on
  the Navier–Stokes equations: a modern review of ‘Sur le mouvement d'un
  liquide visqueux emplissant l'espace’.” In *Partial Differential Equations
  in Fluid Mechanics*, London Mathematical Society Lecture Note Series
  **452**, Cambridge University Press, 2018, 113–203.
  [arXiv:1708.09787](https://arxiv.org/abs/1708.09787). Exposition of the
  existence construction, formalized in the CKN library. Key: `OzanskiPooley2018`.

- **Leray, Jean.** “Sur le mouvement d'un liquide visqueux emplissant
  l'espace.” *Acta Mathematica* **63**, 193–248 (1934).
  [DOI: 10.1007/BF02547354](https://doi.org/10.1007/BF02547354). The original global
  existence theorem, proved in the CKN library. Key: `Leray1934`.

- **Caffarelli, Luis; Kohn, Robert; Nirenberg, Louis.** “Partial regularity
  of suitable weak solutions of the Navier–Stokes equations.” *Communications
  on Pure and Applied Mathematics* **35**(6), 771–831 (1982).
  [DOI: 10.1002/cpa.3160350604](https://doi.org/10.1002/cpa.3160350604).
  The partial-regularity theorem, used here through its formalization.
  Key: `CKN1982`.

- **Armstrong, Scott; Vicol, Vlad.** *The Caffarelli–Kohn–Nirenberg theorem,
  formalized in Lean 4* (2026).
  [github.com/scottnarmstrong/CaffarelliKohnNirenberg](https://github.com/scottnarmstrong/CaffarelliKohnNirenberg).
  The Lake dependency supplying suitable weak solutions, regular and singular
  points, Theorems A–C, and the Leray background used here (the Leray–Hopf
  definitions, Leray's existence theorem, the associated pressure and the
  forced versions). Key: `CKNLean`.

## The Ladyzhenskaya–Prodi–Serrin theorem (Part VI)

- **Prodi, Giovanni.** “Un teorema di unicità per le equazioni di
  Navier–Stokes.” *Annali di Matematica Pura ed Applicata* (4) **48**,
  173–182 (1959). [DOI: 10.1007/BF02410664](https://doi.org/10.1007/BF02410664). Original uniqueness
  theorem. Key: `Prodi1959`.

- **Serrin, James.** “The initial value problem for the Navier–Stokes
  equations.” In *Nonlinear Problems* (R. E. Langer, ed.), University of
  Wisconsin Press, Madison, 1963, 69–98. Key: `Serrin1963`. Also “On the
  interior regularity of weak solutions of the Navier–Stokes equations.”
  *Archive for Rational Mechanics and Analysis* **9**, 187–195 (1962).
  [DOI: 10.1007/BF00253344](https://doi.org/10.1007/BF00253344). Key: `Serrin1962`.

- **Ladyzhenskaya, O. A.** “On uniqueness and smoothness of generalized
  solutions to the Navier–Stokes equations.” *Zap. Nauchn. Sem. Leningrad.
  Otdel. Mat. Inst. Steklov. (LOMI)* **5**, 169–185 (1967); English
  translation: *Sem. Math. V. A. Steklov Math. Inst. Leningrad* **5** (1969),
  60–66. Key: `Ladyzhenskaya1967`.

- **Robinson, Rodrigo and Sadowski** (see below), Theorems 8.17 and 8.19, the
  textbook route followed for the theorem in the full range
  \(3<s\le\infty\); together with the Escauriaza–Seregin–Šverák theorem
  (the case \(s=3\)) it covers the whole regularity criterion
  \(3\le s\le\infty\). The departures from that route are recorded in
  [DEVIATIONS.md](DEVIATIONS.md).

## Supporting treatments

- **Tsai, Tai-Peng.** *Lectures on Navier–Stokes Equations*. Graduate
  Studies in Mathematics **192**. American Mathematical Society, Providence,
  RI, 2018. [DOI: 10.1090/gsm/192](https://doi.org/10.1090/gsm/192).
  Key: `Tsai2018`.

- **Robinson, James C.; Rodrigo, José L.; Sadowski, Witold.** *The
  Three-Dimensional Navier–Stokes Equations: Classical Theory*. Cambridge
  Studies in Advanced Mathematics **157**. Cambridge University Press, 2016.
  [DOI: 10.1017/CBO9781139095143](https://doi.org/10.1017/CBO9781139095143).
  Suitability of the constructed solutions (in the CKN library), the
  weak–strong comparison used for uniqueness, and Theorems 8.17 and 8.19 (the Ladyzhenskaya–Prodi–Serrin
  theorem) for Part VI. Key: `RobinsonRodrigoSadowski2016`.

- **Lemarié-Rieusset, Pierre Gilles.** *The Navier–Stokes Problem in the 21st
  Century*. First edition. CRC Press, Boca Raton, 2016.
  [DOI: 10.1201/b19556](https://doi.org/10.1201/b19556).
  Key: `LemarieRieusset2016`.

- **Seregin, Gregory.** *Lecture Notes on Regularity Theory for the
  Navier–Stokes Equations*. OxPDE Technical Report OxPDE-14/01, 2014.
  Key: `SereginNotes`.

- **Tao, Terence.** “Quantitative bounds for critically bounded solutions to
  the Navier–Stokes equations.”
  [arXiv:1908.04958](https://arxiv.org/abs/1908.04958) (2019).
  Key: `Tao2019`.
