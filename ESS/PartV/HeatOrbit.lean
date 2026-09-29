-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import ESS.PartV.HeatConvolution

@[expose] public section

open CKN.Foundation.Heat CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The componentwise Gaussian convolution of a vector field at a fixed time. -/
def heatConvVec3 (t : ℝ) (b : Vec3 → Vec3) (x : Vec3) : Vec3 :=
  fun i => heatConv t (fun y => b y i) x

/-- The heat orbit in `sec:pv-trace`, represented by CKN's Gaussian kernel. -/
def heatOrbit (b : Vec3 → Vec3) (z : ParabolicPoint) : Vec3 :=
  heatConvVec3 z.2 b z.1

end ESS

end
