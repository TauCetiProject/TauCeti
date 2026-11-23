/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The south pole of the unit sphere of `ℝ³` and its equatorial plane

`TauCeti.sphereSouthPole` is the point `(0, 0, -1)` of the unit sphere `S² ⊂ ℝ³`, and
`TauCeti.complexIsometryOrthogonalSphereSouthPole` is the explicit isometry `z ↦ (Re z, Im z, 0)`
of `ℂ` onto the plane orthogonal to it. Unlike the general
`TauCeti.complexIsometryOrthogonalSpanSingleton`, which is built from a chosen orthonormal basis,
its coordinates are explicit, so orientation signs of frames built from it can be computed.

## Main definitions

* `TauCeti.sphereSouthPole`: the south pole `(0, 0, -1)` of `S²`.
* `TauCeti.complexIsometryOrthogonalSphereSouthPole`: the isometry `z ↦ (Re z, Im z, 0)` of `ℂ`
  onto the equatorial plane.
-/

public section

noncomputable section

open Metric

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "S²" => sphere (0 : ℝ³) 1

namespace TauCeti

/-- The south pole `(0, 0, -1)` of the unit sphere of `ℝ³`. -/
def sphereSouthPole : S² :=
  ⟨WithLp.toLp 2 ![0, 0, -1], by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    simp [Fin.sum_univ_three]⟩

/-- The south pole of `S²` is the vector `(0, 0, -1)` of `ℝ³`. -/
@[simp]
theorem coe_sphereSouthPole : (sphereSouthPole : ℝ³) = WithLp.toLp 2 ![0, 0, -1] :=
  (rfl)

/-- The linear isometry `z ↦ (Re z, Im z, 0)` of `ℂ` into the plane orthogonal to the south
pole. -/
private def complexIsometryOrthogonalSphereSouthPoleAux :
    ℂ →ₗᵢ[ℝ] (ℝ ∙ (sphereSouthPole : ℝ³))ᗮ where
  toFun z := ⟨WithLp.toLp 2 ![z.re, z.im, 0], by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right,
      EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct, Fin.sum_univ_three]⟩
  map_add' z w := by ext i; fin_cases i <;> simp
  map_smul' c z := by ext i; fin_cases i <;> simp
  norm_map' z := by
    change ‖(WithLp.toLp 2 ![z.re, z.im, 0] : ℝ³)‖ = ‖z‖
    rw [EuclideanSpace.norm_eq, Complex.norm_def, Complex.normSq_apply]
    simp [Fin.sum_univ_three, sq]

/-- The isometry `z ↦ (Re z, Im z, 0)` of `ℂ` onto the equatorial plane of `S²`, the plane
orthogonal to the south pole. -/
def complexIsometryOrthogonalSphereSouthPole : ℂ ≃ₗᵢ[ℝ] (ℝ ∙ (sphereSouthPole : ℝ³))ᗮ :=
  complexIsometryOrthogonalSphereSouthPoleAux.toLinearIsometryEquiv <| by
    have : Fact (Module.finrank ℝ ℝ³ = 2 + 1) := ⟨by simp⟩
    rw [Complex.finrank_real_complex, Submodule.finrank_orthogonal_span_singleton (n := 2)
      (ne_zero_of_mem_unit_sphere sphereSouthPole)]

/-- The isometry onto the equatorial plane is `z ↦ (Re z, Im z, 0)`. -/
@[simp]
theorem coe_complexIsometryOrthogonalSphereSouthPole_apply (z : ℂ) :
    (complexIsometryOrthogonalSphereSouthPole z : ℝ³) = WithLp.toLp 2 ![z.re, z.im, 0] :=
  (rfl)

end TauCeti
