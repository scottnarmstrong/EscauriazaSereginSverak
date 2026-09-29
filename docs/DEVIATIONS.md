# Departures from the sources

This document records where the manuscript, [paper/ess.tex](../paper/ess.tex),
and the Lean development differ from the published sources listed in
[SOURCES.md](SOURCES.md). References such as `thm:ess-local` are the
manuscript's LaTeX labels. The solution classes and main results are stated
in `sec:leray-hopf`; Parts I, IV and V of the manuscript follow them, and
Part VI proves the Ladyzhenskaya–Prodi–Serrin theorem. Parts II and III
(Leray existence and the associated pressure) are now proved in the
[CKN library](https://github.com/scottnarmstrong/CaffarelliKohnNirenberg)
and its paper, and the departures in those parts are recorded there. The manuscript
marks each departure by a “Departure from” remark next to the result
concerned, and its appendix `app:errata` records corrections to the sources.
The Lean statements follow the manuscript; the representation choices behind
them are explained in [the design notes](DESIGN_NOTES.md).

The departures in the proof of the local theorem are summarized in Part IV
below. The manuscript closes the step from a singular point to a
quantitative lower bound with `lem:thmA-top`, `def:good-point`,
`lem:good-open-glue` and `eq:bad-point-lower-bound` (see `app:errata`).

## Conventions and scope

- rem:global-LH reads global Leray–Hopf conditions on every finite time
  interval. This avoids requiring finite total space-time \(L^2\) mass from
  the energy inequality.
- def:sws, def:leray-hopf, thm:leray, thm:assoc-pressure (the last two
  proved in the CKN library), thm:ess-local, thm:ess-global, thm:ess-l5-unique, thm:lps,
  cor:ess-smooth and cor:serrin-criterion state the main results. The manuscript fixes spatial dimension three, carries the weak
  gradient separately, and uses the CKN library's suitability notion.
- thm:ess-l5-unique proves the \(L^5\) and uniqueness conclusions of ESS
  Theorem 1.3 by the manuscript's own route (Part V below). Smoothness on
  \(\mathbb{R}^3\times(0,T]\), the remaining conclusion of ESS Theorem 1.3,
  is proved in cor:ess-smooth from thm:lps (Part VI below).
- In thm:lps and cor:ess-smooth, equality of two Leray–Hopf solutions is
  equality almost everywhere on \(\mathbb{R}^3\times(0,T)\), because the
  prescribed time-slice representatives need not agree at every point. The
  smooth representative is smooth in the space-time sense on
  \(\mathbb{R}^3\times(0,T]\), with derivatives at \(T\) taken within that
  set. The hypothesis is the single Serrin condition: the mixed norm
  \(L^{\ell}_tL^s_x\) with \(\ell=2s/(s-3)\) for \(3<s<\infty\), or
  \(L^2_tL^\infty_x\) for \(s=\infty\).
- The backward-uniqueness statements specify their trace and weak-gradient
  conventions. In particular, the source's spatial dimension \(n\) is
  specialized to \(n=3\).
- Forcing appears in the existence results only (proved in the CKN library);
  the regularity theorems are unforced, as in ESS.

## Part I: Carleman inequalities and unique continuation

1. prop:carleman-gauss gives an explicit constant for the Gaussian
   estimate. prop:carleman-halfspace displays the Cauchy–Schwarz absorption
   omitted at the end of ESS Proposition 6.2 and gives explicit choices
   \(a_0(\alpha)=2\) and
   \(c_*(\alpha)=5+7/(2(2\alpha-1))\). This is the remark following the
   half-space estimate.
2. lem:carleman-sobolev extends the smooth compact-support estimates of
   ESS Propositions 6.1–6.2 to compactly supported \(W^{2,1}_2\) fields by
   zero extension, mollification, and weighted \(L^2\) convergence.
3. lem:caccioppoli and lem:ftc-small-time give the local gradient and
   small-time trace estimates used for weak-class cutoffs. The latter
   replaces the source's initial-slice zero extension and pointwise
   parabolic gradient bounds by a spacetime \(L^2\) estimate under the
   stated continuous-representative convention.
4. thm:uc replaces the pointwise Gaussian estimate in ESS Lemma 4.3 by
   parabolic-box \(L^2\) bounds. Its proof controls cutoff collars using the
   source's local \(L^2\) norms, justifies the initial-time cutoff limit by
   a dyadic shell sum, and reaches the target ball by an explicit radius
   iteration.
5. lem:bu-gaussian uses Caccioppoli and average estimates rather than the
   source's pointwise gradient bounds and zero extension. It states an
   explicit smallness choice \(A_0=10^{-12}\), \(\beta=10^{-6}\), which
   keeps the Gaussian exponent positive even when the input growth value is
   zero.
6. lem:bu-small-time inserts spatial cutoffs before applying the
   half-space Carleman estimate to the noncompact field; the shell errors
   vanish by the Gaussian-average estimate and Caccioppoli. A cutoff above
   the initial time avoids zero extension. The propagation through the
   curved zero region is proved with a center and radius chosen for each
   target point, and the transition interval keeps cutoff derivatives in
   the required Carleman region.
7. lem:bu-iterate proves the trace at each step from continuity on the
   already-vanishing interval and displays the rescaling factors and
   recurrence that are compressed in ESS Lemma 5.4.
8. thm:bu handles the large-growth iteration by translating and
   parabolically rescaling each time slab. The rescaling keeps the growth
   exponent and differential-inequality constant within the small-growth
   lemma's range, and the final partial slab is included. Its statement
   fixes the trace and weak-gradient conventions and the project dimension.

## Parts II and III: existence, associated pressure and forced versions

These are proved in the CKN library (`CKN.leray_existence`,
`CKN.leray_existence_singularSet`, `CKN.associatedPressure`,
`CKN.lerayExistenceForced`, `CKN.lerayExistenceForcedSingularSet`,
`CKN.associatedPressureForced`) and the last part of the CKN paper; their
departures from Ożański–Pooley, Tsai and Robinson–Rodrigo–Sadowski (the Fourier
\(L^2\) construction of the regularized solutions, the double-Riesz pressure,
the forced pressure split, and the stability and compactness arguments) are
documented in the deviations of the
[CKN repository](https://github.com/scottnarmstrong/CaffarelliKohnNirenberg).
The associated-pressure statement `thm:assoc-pressure` includes the
conditional clause that \(p\in L^\infty_tL^{3/2}_x\) when
\(\esssup_t\|u(\cdot,t)\|_{L^3}<\infty\); the manuscript's `lem:assoc-pressure-L3`
records the slice-wise double-Riesz estimate behind it, which Part IV uses.

## Part IV: \(L^\infty_tL^3_x\) regularity route

The changes to the source's proof of thm:ess-local are the following; the
route lemmas and the proof are assembled in sec:thm-local.

- **Local energy equality.** lem:lei-L4 mollifies the equation and
  passes to the limit using \(u\in L^4_{\mathrm{loc}}\). The pressure flux
  retains the full \(L^{3/2}\) pressure, including its harmonic part. This
  supplies the local energy-equality consequence needed from ESS (3.2),
  not the source's derivative estimates.
- **Time representative.** lem:weak-cont-L3 derives weak time
  continuity and every-time \(L^3\) slice bounds from the momentum-pairing
  modulus and lower semicontinuity, rather than the stronger maximal-
  regularity estimate (3.10).
- **Compactness.** lem:compactness (now in the CKN paper) uses spatial mollification and
  Arzelà–Ascoli for strong local space-time \(L^2\), weak gradients, and
  weak convergence of every velocity slice. It does not assert strong
  \(C_tL^2_{\mathrm{loc}}\) convergence.
- **Pressure split and bad-point lower bound.** lem:pressure-split,
  with rem:pb1-departure, fixes the whole-space Riesz
  pressure of the zero-extended tensor and its harmonic difference, then
  proves the interior bound and rescaled vanishing for that split. It does
  not transfer ESS's (3.19) to a newly chosen remainder. The direct
  implication from CKN Theorem A to ESS's full-neighborhood singular-point
  lower bound fails at the top face because the CKN conclusion there is
  one-sided. The manuscript instead closes the needed bridge through
  lem:thmA-top, def:good-point, lem:good-open-glue, and
  eq:bad-point-lower-bound; the blow-up proof uses this bad-point lower
  bound, not ESS's full-neighborhood singular-point formulation.
- **Time projection and backward uniqueness.**
  lem:time-projection supplies regular time slices from the CKN singular
  set estimate. thm:vorticity-regularity proves the finite weak-to-regular
  bootstrap and retains the local gradient-energy dependence. It does not
  supply the all-orders and infinite-order vanishing hypotheses in ESS
  Theorem 4.1; those are not consequences of this finite-order result.
  thm:uc and thm:bu provide the integrated unique-continuation and
  backward-uniqueness statements with their explicit trace and iteration
  steps.
- **Shifted center.** lem:regular-point-shift applies the local
  theorem at a later center whose half-cylinder contains the original
  point in its interior, and verifies the radius and time-domain conditions.
- **Good-point criterion.** def:good-point and lem:good-open-glue define
  and propagate a CKN smallness condition and give a lower bound at points
  that fail it. At the top face they produce a one-sided Hölder extension,
  not CKN's open-neighborhood IsRegularPoint property. This criterion is
  not identified with ESS's source notion of a regular point.
- **Top-face regularity.** lem:thmA-top makes the one-sided Hölder
  conclusion from CKN Theorem A explicit after shifted-center gluing. It
  gives the closure regularity used in thm:ess-local without declaring a
  top-face point regular in the open-neighborhood CKN sense.
- **Blow-up limit.** prop:blowup-limit uses strong local space-time \(L^2\),
  strong \(L^3\), and weak convergence of every velocity slice, not strong
  \(C_tL^2_{\mathrm{loc}}\) convergence. Pairing continuity, weak slice
  convergence at \(t=0\), and lower semicontinuity give the endpoint
  conclusion; time-strip estimates handle the strong-\(L^3\) passage.
  Its pressure estimate uses the fixed split from lem:pressure-split.
- **Global theorem.** lem:assoc-pressure-L3 obtains the critical pressure
  bound directly from the canonical slice-wise double-Riesz estimate.
  The written proof of thm:ess-global uses this bound and applies
  thm:ess-local at a later center; it uses the coherent
  \(B_1\times(-1,0)\) cylinder, correcting the sign mismatch in the printed
  statement of ESS Theorem 1.4.

## Part V: \(L^5\) and uniqueness

- thm:ess-l5-unique follows the positive-time reduction (3.5)–(3.7) and
  the short-time construction of Theorems 7.3–7.4 of ESS
  (rem:pv-departure). The initial \(L^3\) trace is derived from good times
  and the strong \(L^2\) trace, the special heat estimate is proved
  instead of using the general mixed-norm assertion (7.4) of ESS Lemma 7.1,
  and the fixed-point limit is written in the spaces used here.
- lem:pv-stokes isolates the zero-data Stokes estimate as a linear response,
  fixes the pressure through def:riesz-pressure, and records the difference
  estimates needed for completion (rem:pv-stokes-departure).
- Weak–strong uniqueness is proved at exponents \((5,5)\) by the zero-start
  energy comparison of Robinson, Rodrigo and Sadowski, with the
  cross-testing identity derived by spatial mollification instead of their
  Serrin regularity theorem and testing lemma. No general mixed-norm
  estimate from ESS Lemma 7.1 and no result attributed to Giga is used.

## Part VI: the Ladyzhenskaya–Prodi–Serrin theorem

thm:lps and cor:ess-smooth follow the route of Robinson, Rodrigo and
Sadowski, Theorems 8.17 and 8.19, with the following departures; the
manuscript notes each next to the result concerned.

- **No strong energy inequality is assumed.** Their Leray–Hopf class includes
  a strong energy inequality from good positive times. Here the class of
  def:leray-hopf is used as it stands, and the restart at positive times is
  supplied by lem:lps-energy-equality: under the Serrin condition the energy
  equality holds, and is proved only for almost every time, since the
  definition may prescribe nonmeasurable slices on exceptional times. The
  proof is the mollified cross-testing identity of Part V applied with the
  solution in both slots, with the interpolation of lem:lps-mixed-interpolation.
- **Local strong solution.** The strong solution from \(H^1\) data, and
  its \(H^1\) estimate and continuation, are obtained through the Fourier
  \(L^2\) machinery of the CKN library, not by the construction of the textbook.
- **Comparison at restart times by concatenation.** The comparison between a
  Leray–Hopf solution and the strong solution is made at almost every
  restart time, by concatenating the strong solution with the given one, not
  by a strong energy inequality at good times.
- **Smoothing by a regularity ladder.** Smoothness on
  \(\mathbb{R}^3\times(0,T]\) is obtained by a direct ladder of \(H^m\)
  estimates on the strong solution (including the a posteriori energy
  inequality of rem:lps-Hm-energy) proved in the manuscript.
- **Endpoints.** The endpoint \(s=\infty\) (the class \(L^2_tL^\infty_x\))
  and smoothness up to the final time \(T\), one-sided at \(T\), are proved
  explicitly, as the statements require.
- **Relation to ESS.** ESS derive smoothness in Theorem 1.3 from the
  \(L^5\) bound by citing Theorem 1.2. Here thm:ess-l5-unique supplies the
  \(L^5\) bound and cor:ess-smooth applies thm:lps at \((s,\ell)=(5,5)\).

## Carleman constants and comparator restatements

- **Carleman constants.** The manuscript's proofs of prop:carleman-gauss and
  prop:carleman-halfspace compute explicit constants:
  \(c_0=e^{4/3}(9+2\sqrt6)\) for the Gaussian estimate, and \(a_0=2\),
  \(c_*=5+\tfrac{7}{2(2\alpha-1)}\) for the half-space estimate. The
  Lean statements `carlemanGaussian` and `carlemanHalfSpace` assert only the
  existence of such constants, as the statements of ESS do; the explicit
  values are used in the proofs but are not part of the statements.
- **Growth rate in backward uniqueness.** The library statement
  `ESS.backwardUniqueness` assumes \(M>0\) in the Gaussian growth bound
  \(|w(x,t)|\le e^{M|x|^2}\), while thm:bu allows every real \(M\). Nothing is
  lost: the bound for \(M\) implies the bound for \(\max(M,1)\). The comparator
  challenge states the theorem for every real \(M\), and its Solution applies
  the library statement with \(\max(M,1)\).
- **Mathlib-native comparator statements.** The comparator challenges in
  `comparators/{Linear,Regularity}` restate the theorems in Mathlib-native
  form: Euclidean space `EuclideanSpace ℝ (Fin 3)` in place of `Vec3`, the
  ordinary product space-time in place of `ParabolicPoint`, Mathlib's `fderiv`,
  Lebesgue measures, and Hölder regularity in the ordinary metric. The
  Regularity Challenge asserts that the singular set is empty; CKN's comparator
  separately states parabolic Hausdorff nullity.
  The Solutions prove these notions equivalent to the library's parabolic and
  componentwise notions by transport lemmas, and derive the challenge
  statements from the library theorems. The two pairs restate all ten
  theorems of this library; the comparator pair for the Leray theorems
  (five of the six) is in the CKN repository.
