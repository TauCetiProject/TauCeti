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

Let `J` be an almost complex structure on a two-dimensional real vector space `V`. For every
nonzero `w`, the frame `(w, J w)` is a basis (`TauCeti.AlmostComplexStructure.basisPair`). When
`V` is an inner product space and `J` preserves the inner product, this basis is orthogonal with
sides of equal length. This file draws two consequences.

* Any two symmetric bilinear forms `A` and `B` preserved by `J` are proportional:
  `A(w, w) B = B(w, w) A` for every `w`. In particular a symmetric bilinear form preserved by an
  orthogonal `J` is a multiple of the inner product, `‖w‖² B = B(w, w) ⟪·, ·⟫`, and any two inner
  products preserved by `J` are conformal.
* If `V` is oriented so that every frame `(w, J w)` is positive, `J` is the rotation by a right
  angle `Orientation.rightAngleRotation`, so the volume form of `V` is the area form
  `ω(u, v) = ⟪J u, v⟫`.

## Main results

* `TauCeti.AlmostComplexStructure.bilinForm_apply_self_smul_eq_smul`: two symmetric `J`-invariant
  bilinear forms on a plane are proportional.
* `TauCeti.AlmostComplexStructure.norm_sq_smul_bilinForm_eq_smul_innerₗ`: a symmetric
  `J`-invariant bilinear form is proportional to the inner product.
* `TauCeti.AlmostComplexStructure.volumeForm_apply_self_apply_pos`: for the orientation making
  every frame `(v, J v)` positive, the volume form is positive on these frames, whether or not `J`
  preserves the inner product.
* `TauCeti.AlmostComplexStructure.apply_eq_rightAngleRotation`: `J` is the rotation by a right
  angle of the orientation making `(w, J w)` positive.
* `TauCeti.AlmostComplexStructure.volumeForm_apply_eq_inner`: the volume form of that orientation
  is `ω(u, v) = ⟪J u, v⟫`.
-/

public section

namespace TauCeti.AlmostComplexStructure

open Module
open scoped RealInnerProductSpace

section Module

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [Fact (finrank ℝ V = 2)]
  {J : AlmostComplexStructure V}

/-- The frame `(w, J w)` of a nonzero vector `w` of a plane, as a basis. -/
noncomputable def basisPair (J : AlmostComplexStructure V) {w : V} (hw : w ≠ 0) :
    Basis (Fin 2) ℝ V :=
  basisOfLinearIndependentOfCardEqFinrank (J.linearIndependent_pair hw)
    (by simp [(Fact.out : finrank ℝ V = 2)])

@[simp]
theorem coe_basisPair {w : V} (hw : w ≠ 0) : ⇑(basisPair J hw) = ![w, J w] :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

/-- **Invariant forms on a plane are proportional.** On a plane with a complex structure `J`, two
symmetric bilinear forms `A` and `B` preserved by `J` satisfy `A(w, w) B = B(w, w) A` for every
`w`. -/
theorem bilinForm_apply_self_smul_eq_smul {A B : LinearMap.BilinForm ℝ V} (hA : A.IsSymm)
    (hAJ : ∀ u v, A (J u) (J v) = A u v) (hB : B.IsSymm) (hBJ : ∀ u v, B (J u) (J v) = B u v)
    (w : V) : A w w • B = B w w • A := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have hA₀ := J.bilinForm_apply_apply_self_eq_zero hA hAJ w
  have hB₀ := J.bilinForm_apply_apply_self_eq_zero hB hBJ w
  refine LinearMap.ext_basis (basisPair J hw) (basisPair J hw) fun i k ↦ ?_
  fin_cases i <;> fin_cases k <;>
    simp [hA₀, hB₀, hA.eq (J w) w, hB.eq (J w) w, hAJ, hBJ, mul_comm]

end Module

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 2)]
  {J : AlmostComplexStructure V}

/-- **Invariant forms on a plane are conformal.** On a Euclidean plane with an orthogonal complex
structure `J`, a symmetric bilinear form `B` preserved by `J` is the multiple
`B(w, w) / ‖w‖²` of the inner product, for any nonzero `w`. -/
theorem norm_sq_smul_bilinForm_eq_smul_innerₗ (hJ : ∀ u v, ⟪J u, J v⟫ = ⟪u, v⟫)
    {B : LinearMap.BilinForm ℝ V} (hB : B.IsSymm) (hBJ : ∀ u v, B (J u) (J v) = B u v) (w : V) :
    ‖w‖ ^ 2 • B = B w w • innerₗ V := by
  simpa [real_inner_self_eq_norm_sq] using bilinForm_apply_self_smul_eq_smul
    (A := innerₗ V) ⟨fun u v ↦ real_inner_comm v u⟩ hJ hB hBJ w

/-- On a plane oriented so that every frame `(v, J v)` is positive, the volume form is positive on
the frame `(v, J v)` of a nonzero vector. -/
theorem volumeForm_apply_self_apply_pos (o : Orientation ℝ V (Fin 2))
    (ho : ∀ b : Basis (Fin 2) ℝ V, b 1 = J (b 0) → b.orientation = o) {v : V} (hv : v ≠ 0) :
    0 < o.volumeForm ![v, J v] := by
  rw [← coe_basisPair hv]
  exact Orientation.volumeForm_apply_pos_iff.2 (ho _ (by simp))

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
    rw [Orientation.areaForm_to_volumeForm]
    exact volumeForm_apply_self_apply_pos o ho hv
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
