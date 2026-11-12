/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import TauCeti.Geometry.Symplectic.AlmostComplex
import TauCeti.Analysis.InnerProductSpace.Orientation
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace

/-!
# Orthogonal complex structures on a Euclidean plane

Let `J` be an almost complex structure on a two-dimensional real inner product space `V` which
preserves the inner product. For every nonzero `w`, the frame `(w, J w)` is an orthogonal basis
with sides of equal length. This file draws two consequences.

* Any symmetric bilinear form `B` preserved by `J` is a multiple of the inner product:
  `‖w‖² B = B(w, w) ⟪·, ·⟫` for every `w`. In particular any two inner products preserved by `J`
  are conformal.
* If `V` is oriented so that every frame `(w, J w)` is positive, `J` is the rotation by a right
  angle `Orientation.rightAngleRotation`, so the volume form of `V` is the area form
  `ω(u, v) = ⟪J u, v⟫`.

## Main results

* `TauCeti.AlmostComplexStructure.norm_sq_smul_bilinForm_eq_smul_innerₗ`: a symmetric
  `J`-invariant bilinear form is proportional to the inner product.
* `TauCeti.AlmostComplexStructure.apply_eq_rightAngleRotation`: `J` is the rotation by a right
  angle of the orientation making `(w, J w)` positive.
* `TauCeti.AlmostComplexStructure.volumeForm_apply_eq_inner`: the volume form of that orientation
  is `ω(u, v) = ⟪J u, v⟫`.
-/

public section

namespace TauCeti.AlmostComplexStructure

open Module
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 2)]
  {J : AlmostComplexStructure V}

/-- The frame `(w, J w)` of a nonzero vector `w` of a plane, as a basis. -/
private noncomputable def basisPair (J : AlmostComplexStructure V) {w : V} (hw : w ≠ 0) :
    Basis (Fin 2) ℝ V :=
  basisOfLinearIndependentOfCardEqFinrank (J.linearIndependent_pair hw)
    (by simp [(Fact.out : finrank ℝ V = 2)])

private theorem coe_basisPair {w : V} (hw : w ≠ 0) : ⇑(basisPair J hw) = ![w, J w] :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

/-- **Invariant forms on a plane are conformal.** On a Euclidean plane with an orthogonal complex
structure `J`, a symmetric bilinear form `B` preserved by `J` is the multiple
`B(w, w) / ‖w‖²` of the inner product, for any nonzero `w`. -/
theorem norm_sq_smul_bilinForm_eq_smul_innerₗ (hJ : ∀ u v, ⟪J u, J v⟫ = ⟪u, v⟫)
    {B : LinearMap.BilinForm ℝ V} (hB : B.IsSymm) (hBJ : ∀ u v, B (J u) (J v) = B u v) (w : V) :
    ‖w‖ ^ 2 • B = B w w • innerₗ V := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have h₀ := J.bilinForm_apply_apply_self_eq_zero hB hBJ w
  have h₁ : ⟪w, J w⟫ = 0 := by rw [real_inner_comm, inner_apply_self hJ]
  refine LinearMap.ext_basis (basisPair J hw) (basisPair J hw) fun i k ↦ ?_
  fin_cases i <;> fin_cases k <;>
    simp [coe_basisPair, h₀, h₁, hB.eq (J w) w, real_inner_comm w, hBJ, hJ, mul_comm]

/-- On a plane oriented so that every frame `(v, J v)` is positive, an orthogonal complex
structure `J` is the rotation by a right angle. -/
theorem apply_eq_rightAngleRotation (o : Orientation ℝ V (Fin 2))
    (hJ : ∀ u v, ⟪J u, J v⟫ = ⟪u, v⟫)
    (ho : ∀ b : Basis (Fin 2) ℝ V, b 1 = J (b 0) → b.orientation = o) (v : V) :
    J v = o.rightAngleRotation v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  -- The frame `(v, J v)` is positive, orthogonal and has sides of length `|v|`.
  have hpos : 0 < o.areaForm v (J v) := by
    rw [Orientation.areaForm_to_volumeForm, ← coe_basisPair hv]
    exact Orientation.volumeForm_apply_pos_iff.2 (ho _ (by simp [coe_basisPair]))
  have hnorm : ‖J v‖ = ‖v‖ := norm_apply hJ v
  have harea : o.areaForm v (J v) = ‖v‖ ^ 2 := by
    rw [← abs_of_pos hpos,
      o.abs_areaForm_of_orthogonal (by rw [real_inner_comm, inner_apply_self hJ]), hnorm, sq]
  -- Equality in Cauchy–Schwarz for `⟪R v, J v⟫ = ω(v, J v) = |R v| |J v|`, where `R` is the
  -- rotation by a right angle.
  have hR : ‖o.rightAngleRotation v‖ = ‖v‖ := by simp
  have heq : ⟪o.rightAngleRotation v, J v⟫ = ‖o.rightAngleRotation v‖ * ‖J v‖ := by
    rw [Orientation.inner_rightAngleRotation_left, harea, hR, hnorm, sq]
  rw [inner_eq_norm_mul_iff_real, hR, hnorm] at heq
  exact (smul_right_injective _ (norm_ne_zero_iff.2 hv) heq).symm

/-- **The area form of a plane.** On a plane oriented so that every frame `(v, J v)` is positive,
the volume form of an orthogonal complex structure `J` is `ω(u, v) = ⟪J u, v⟫`. -/
theorem volumeForm_apply_eq_inner (o : Orientation ℝ V (Fin 2))
    (hJ : ∀ u v, ⟪J u, J v⟫ = ⟪u, v⟫)
    (ho : ∀ b : Basis (Fin 2) ℝ V, b 1 = J (b 0) → b.orientation = o) (u v : V) :
    o.volumeForm ![u, v] = ⟪J u, v⟫ := by
  rw [← Orientation.areaForm_to_volumeForm, apply_eq_rightAngleRotation o hJ ho,
    Orientation.inner_rightAngleRotation_left]

end TauCeti.AlmostComplexStructure
