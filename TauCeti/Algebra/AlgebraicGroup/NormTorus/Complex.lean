/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.NormTorus.Basic
public import TauCeti.RingTheory.Norm.Complex
public import Mathlib.Analysis.Complex.Norm

/-!
# The norm torus of `ℂ/ℝ` on real points

The real points of `Res_{ℂ/ℝ} 𝔾ₘ` are the units of `ℂ ⊗[ℝ] ℝ ≃ ℂ`. On them, the norm
`TauCeti.NormTorus.norm ℝ ℂ ℝ` is the squared modulus `x + iy ↦ x² + y²`, so the real points of the
norm-one torus of `ℂ/ℝ` are the unit circle. The norm `ℂˣ → ℝˣ` is not surjective on real points:
its image is the group of positive reals.

## Main results

* `TauCeti.NormTorus.coe_norm_complex`: on real points, the norm is `Complex.normSq`.
* `TauCeti.NormTorus.mem_normOne_complex_iff`: a real point has norm one exactly when it lies on the
  unit circle.
* `TauCeti.NormTorus.range_norm_complex`: the image of the norm on real points is the subgroup of
  positive reals.
-/

public section

open scoped TensorProduct

namespace TauCeti.NormTorus

/-- On real points of `Res_{ℂ/ℝ} 𝔾ₘ`, read in `ℂ` through `ℂ ⊗[ℝ] ℝ ≃ ℂ`, the norm is the squared
modulus. -/
theorem coe_norm_complex (u : (ℂ ⊗[ℝ] ℝ)ˣ) :
    (norm ℝ ℂ ℝ u : ℝ) = Complex.normSq (Algebra.TensorProduct.rid ℝ ℝ ℂ u) := by
  rw [norm_eq_normUnits, Algebra.coe_normUnits, Units.coe_map, MonoidHom.coe_ofClass,
    Algebra.norm_complex_apply]

/-- The real points of the norm-one torus of `ℂ/ℝ` are the points of the unit circle. -/
theorem mem_normOne_complex_iff {u : (ℂ ⊗[ℝ] ℝ)ˣ} :
    u ∈ normOne ℝ ℂ ℝ ↔ ‖Algebra.TensorProduct.rid ℝ ℝ ℂ u‖ = 1 := by
  rw [mem_normOne, Units.ext_iff, coe_norm_complex, Units.val_one, Complex.normSq_eq_norm_sq,
    pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero]

/-- The image of the norm on real points of `Res_{ℂ/ℝ} 𝔾ₘ` is the group of positive reals; in
particular `-1` is not a norm. -/
theorem range_norm_complex : (norm ℝ ℂ ℝ).range = Units.posSubgroup ℝ := by
  -- `ℂ ⊗[ℝ] ℝ ≃ ℂ` identifies the norm with the field norm, whose image is the norm group
  rw [← normGroup_real_complex]
  ext x
  rw [MonoidHom.mem_range, mem_normGroup_iff_exists_normUnits]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨_, (norm_eq_normUnits u).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨Units.map ((Algebra.TensorProduct.rid ℝ ℝ ℂ).symm : ℂ →* ℂ ⊗[ℝ] ℝ) z, ?_⟩
    rw [norm_eq_normUnits]
    congr 1
    ext
    simp

end TauCeti.NormTorus
