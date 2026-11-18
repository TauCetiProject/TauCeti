/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Comparison

/-!
# The hypotheses of compactness for the weak Cauchy–Riemann equation

The planar compactness theorem for the weak equation `TauCeti.IsWeakCauchyRiemannOn` with the
standard structure `J = i` and `η = 0` (McDuff–Salamon, Theorem B.4.2 and Theorem 4.1.1) asks for
a uniform bound on `du_m` and for the images of compact sets to stay in a fixed compact set; at a
boundary with values in a totally real `L`, it asks for `L` to be closed. Without boundary, this
theorem is `TauCeti.exists_subseq_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn_I_smul_id`,
which needs only the image bound, since for `J = i` Cauchy's estimates give the gradient bound.

The sequences witnessing these hypotheses are holomorphic, and their properties, stated with the
real Fréchet derivatives `fderiv ℝ` and the image bound that theorem uses, are in
`TauCeti.Analysis.Complex.HolomorphicFunctions.CompactnessExamples`. This file supplies the
remaining fact, that each sequence solves the weak equation.

* Closedness of `L`. The constant maps `1 / (m + 2)` solve the weak equation on every set, in
  particular on the half-disc, by `TauCeti.isWeakCauchyRiemannOn_const`; their boundary values
  lie in `L = (0, 1) ⊆ ℝ ⊆ ℂ`, but those of their limit `0` do not
  (`TauCeti.HolomorphicCompactness.not_mapsTo_zero_ofReal_image_Ioo`), while for the closed
  `L = ℝ` they do (`TauCeti.HolomorphicCompactness.mapsTo_zero_range_ofReal`).
* The gradient bound. The maps `z ↦ m z` solve the weak equation on every open set
  (`TauCeti.HolomorphicCompactness.isWeakCauchyRiemannOn_const_mul`) and violate the gradient
  and image bounds (`TauCeti.HolomorphicCompactness.not_exists_norm_fderiv_natCast_mul_le`,
  `TauCeti.HolomorphicCompactness.not_exists_isCompact_forall_mapsTo_natCast_mul`). The maps
  `z ↦ z / m` solve it as well (`TauCeti.HolomorphicCompactness.isWeakCauchyRiemannOn_div_natCast`)
  and converge to the solution `0` with every real iterated derivative
  (`TauCeti.HolomorphicCompactness.tendstoLocallyUniformly_iteratedFDeriv_div_natCast`).
* The image bound. The constant maps `m` solve the weak equation on every set by
  `TauCeti.isWeakCauchyRiemannOn_const`, have derivative zero, and violate the image bound
  (`TauCeti.HolomorphicCompactness.not_exists_isCompact_forall_mapsTo_natCast`).

## Main results

* `TauCeti.HolomorphicCompactness.isWeakCauchyRiemannOn_const_mul`: the maps `c z` are weak
  solutions.
* `TauCeti.HolomorphicCompactness.isWeakCauchyRiemannOn_div_natCast`: the maps `z / m` are weak
  solutions.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 4.1.1 and Theorem B.4.2.
-/

public section

noncomputable section

open Complex TopologicalSpace

namespace TauCeti

variable {p : ENNReal} {Ω : Opens ℂ}

namespace HolomorphicCompactness

local notation "Jᵢ" => fun (_ : ℂ) (_ : ℂ) => I • ContinuousLinearMap.id ℝ ℂ

/-- The maps `z ↦ c z` solve the homogeneous weak equation for `J = i` on every open set. -/
theorem isWeakCauchyRiemannOn_const_mul (c : ℂ) :
    IsWeakCauchyRiemannOn p Ω Jᵢ (fun _ _ => 0) (fun z => c * z) :=
  (differentiable_id.const_mul c).differentiableOn.isWeakCauchyRiemannOn

/-- The maps `z ↦ z / m` solve the homogeneous weak equation for `J = i` on every open set. -/
theorem isWeakCauchyRiemannOn_div_natCast (m : ℕ) :
    IsWeakCauchyRiemannOn p Ω Jᵢ (fun _ _ => 0) (fun z => z / m) :=
  (differentiable_id.div_const _).differentiableOn.isWeakCauchyRiemannOn

end HolomorphicCompactness

end TauCeti
