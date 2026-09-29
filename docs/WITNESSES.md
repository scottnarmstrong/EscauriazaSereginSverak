# Examples and satisfiability witnesses

The formalization includes explicit examples alongside its general theorems.
They show that the solution classes and other definitions used in the main
statements admit the data they are intended to describe. The main collection
is [ESS/Witnesses](../ESS/Witnesses); a few further witnesses sit next to
the definitions they instantiate. Witnesses for the definitions that moved to
the CKN library (the Leray–Hopf solution classes, the force classes, the local
Sobolev predicates and the regularized mild solution) are in the
[CKN repository](https://github.com/scottnarmstrong/CaffarelliKohnNirenberg).

A satisfiability theorem has a precise, limited purpose. A result of the form
`∃ data, P data`, or `P d` for an explicit `d`, shows that the predicate `P`
is inhabited. It does not prove a general estimate for every datum
satisfying `P`, nor does it show that every additional hypothesis of a later
theorem can be satisfied simultaneously. The statement of each witness,
rather than its name, determines what it establishes.

## Leray–Hopf solutions

The examples for `CKN.IsInJ`, `CKN.IsLerayHopfSolution`,
`CKN.IsGlobalLerayHopfSolution` and the forced classes (zero solution, zero
force) are in `CKN/Witnesses/LerayHopfZero.lean` and
`CKN/Witnesses/ForcedZero.lean` of the CKN repository. For nonzero data,
`CKN.leray_existence` supplies, for every `a` with `IsInJ a`, a global
Leray–Hopf solution with datum `a` that is also a suitable weak solution.

## Space-time weak derivatives

The unique-continuation and backward-uniqueness theorems carry explicit
space-time weak-derivative data through `CKN.HasSpaceTimeWeakDerivs`.

- [`ESS.hasSpaceTimeWeakDerivs_zero`](../ESS/Witnesses/SpaceTimeWeakDerivsZero.lean)
  instantiates it with the zero field on any domain.
- [`ESS.hasSpaceTimeWeakDerivs_of_contDiff`](../ESS/Witnesses/SpaceTimeWeakDerivsSmooth.lean)
  proves that every smooth field on an open product domain has its classical
  first, second and time derivatives as space-time weak derivatives.
- `ESS.hasSpaceTimeWeakDerivs_nonzero_witness`, in the same file, applies
  this to the constant field with all components equal to one, which is
  nonzero.

## Other interfaces

- [WeakDerivOneDim.lean](../ESS/Witnesses/WeakDerivOneDim.lean):
  `ESS.IsIntervalTest_satisfiable` exhibits a nonzero smooth bump that is a
  test function on `(0, 1)`, and `ESS.HasWeakDerivOn_satisfiable` shows that
  a nonzero constant has weak derivative zero there; zero-function versions
  are also included.
- [GoodPoint.lean](../ESS/Witnesses/GoodPoint.lean): `ESS.isGoodPoint_zero`
  instantiates the smallness criterion `ESS.IsGoodPoint` used in the proof of
  the local regularity theorem, with the zero velocity and pressure.
- `CKN.memSobolevOn_zero` (in the CKN library) instantiates the local
  Sobolev predicate used in the vorticity bootstrap.

## Local strong solutions (Part VI)

[StrongSolutionZero.lean](../ESS/LPS/StrongSolutionZero.lean) proves
`ESS.isLpsStrongSolution_zero`: the zero velocity, gradient and pressure
form an `ESS.IsLpsStrongSolution` on every interval `[t₀, T]` with `t₀ < T`;
this is the class of local strong solutions used in the proof of the Ladyzhenskaya–Prodi–Serrin theorem. It
shows only that this predicate is inhabited; the existence of such solutions
for general data is a theorem of Part VI, not this witness.

## Checking the inventory

`scripts/prop_interfaces.py` lists every project definition whose type is
`Prop` and reports whether the repository contains a declaration that
instantiates it. The reviewed pairs are recorded in
`scripts/prop_interface_allowlist.txt`, and `scripts/check_rules.py`, which
runs before every guarded build, rejects a new or changed interface that has
no instantiating declaration and is not on that list.

All witness modules are imported by `ESS.lean`. The exact statement of each
declaration explains what the example proves; compilation and the axiom
checks verify its proof.
