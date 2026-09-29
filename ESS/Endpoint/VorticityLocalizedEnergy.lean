-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import ESS.Endpoint.VorticityTestOperators
public import ESS.Endpoint.VorticityWeakEquation
public import ESS.Endpoint.VorticityWeakEquationPairings
public import CKN.Core.Step3.LocalizedEquationBasics
public import CKN.Pressure.LeibnizLaplacian
public import CKN.Setting.Energy.Calculus
public import CKN.ClassEquivalence.TestSupport

/-!
# Smooth localization of the weak vorticity equation

Multiplying a compact test by a smooth scalar preserves admissibility. The
time and spatial derivative identities below are the calculus terms needed
when localizing `lem:localized-vorticity-energy`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open CKN.Foundation.Parabolic

namespace ESS

noncomputable section

end

end ESS
