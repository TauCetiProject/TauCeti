/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.Hereditary.Ideal

/-!
# Matrix counterexamples for hereditary C⋆-subalgebras and strict positivity

Two `2 × 2` matrix examples in `CStarMatrix (Fin 2) (Fin 2) ℂ` separate the notions developed in
`TauCeti.Analysis.CStarAlgebra.Hereditary.Basic` and
`TauCeti.Analysis.CStarAlgebra.Hereditary.Ideal`:

* `TauCeti.CStarAlgebra.exists_isClosed_not_isHereditary_matrix`: `CStarMatrix (Fin 2) (Fin 2) ℂ`
  contains a norm-closed `⋆`-subalgebra that is not hereditary.
* `TauCeti.CStarAlgebra.exists_isFull_and_not_isStrictlyPositive_matrix`:
  `CStarMatrix (Fin 2) (Fin 2) ℂ` contains a positive full element that is not strictly positive.
-/

public section

open scoped CStarAlgebra ComplexOrder

namespace TauCeti.CStarAlgebra

/-- `CStarMatrix (Fin 2) (Fin 2) ℂ` contains a norm-closed `⋆`-subalgebra that is not hereditary. -/
theorem exists_isClosed_not_isHereditary_matrix :
    ∃ B : NonUnitalStarSubalgebra ℂ (CStarMatrix (Fin 2) (Fin 2) ℂ),
      IsClosed (B : Set (CStarMatrix (Fin 2) (Fin 2) ℂ)) ∧ ¬IsHereditary B := by
  let B : NonUnitalStarSubalgebra ℂ (CStarMatrix (Fin 2) (Fin 2) ℂ) :=
    { carrier := {M | M 0 1 = 0 ∧ M 1 0 = 0}
      mul_mem' := fun {M N} hM hN => by
        refine ⟨?_, ?_⟩ <;>
          simp [CStarMatrix.mul_apply, Fin.sum_univ_two, hM.1, hM.2, hN.1, hN.2]
      add_mem' := fun {M N} hM hN => ⟨by simp [hM.1, hN.1], by simp [hM.2, hN.2]⟩
      zero_mem' := ⟨rfl, rfl⟩
      smul_mem' := fun c {M} hM => ⟨by simp [hM.1], by simp [hM.2]⟩
      star_mem' := fun {M} hM =>
        ⟨by simp [CStarMatrix.star_apply, hM.2], by simp [CStarMatrix.star_apply, hM.1]⟩ }
  have hB_closed : IsClosed (B : Set (CStarMatrix (Fin 2) (Fin 2) ℂ)) :=
    (isClosed_eq ((continuous_apply (1 : Fin 2)).comp (continuous_apply (0 : Fin 2)))
      continuous_const).inter
      (isClosed_eq ((continuous_apply (0 : Fin 2)).comp (continuous_apply (1 : Fin 2)))
        continuous_const)
  refine ⟨B, hB_closed, fun hB => ?_⟩
  let b₁ : CStarMatrix (Fin 2) (Fin 2) ℂ := CStarMatrix.ofMatrix (Matrix.single 0 0 1)
  let b₂ : CStarMatrix (Fin 2) (Fin 2) ℂ := CStarMatrix.ofMatrix (Matrix.single 1 1 1)
  let a : CStarMatrix (Fin 2) (Fin 2) ℂ := CStarMatrix.ofMatrix (Matrix.single 0 1 1)
  have hb₁ : b₁ ∈ B := ⟨by simp [b₁], by simp [b₁]⟩
  have hb₂ : b₂ ∈ B := ⟨by simp [b₂], by simp [b₂]⟩
  have hmem : b₁ * a * b₂ ∈ B := hB.mul_mem hb₁ a hb₂
  have h01 : (b₁ * a * b₂) 0 1 = 1 := by
    simp [b₁, b₂, a, CStarMatrix.mul_apply, Fin.sum_univ_two]
  exact one_ne_zero (h01 ▸ hmem.1)

/-- `CStarMatrix (Fin 2) (Fin 2) ℂ` contains a positive full element that is not strictly
positive. -/
theorem exists_isFull_and_not_isStrictlyPositive_matrix :
    ∃ e : CStarMatrix (Fin 2) (Fin 2) ℂ, 0 ≤ e ∧ IsFull e ∧ ¬IsStrictlyPositive e := by
  let e : CStarMatrix (Fin 2) (Fin 2) ℂ := CStarMatrix.ofMatrix (Matrix.single 0 0 1)
  have he_sq : star e * e = e := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [e, CStarMatrix.star_apply, CStarMatrix.mul_apply, Fin.sum_univ_two]
  have he_nonneg : 0 ≤ e := he_sq ▸ star_mul_self_nonneg e
  have he_full : IsFull e := by
    rw [isFull_def, ← TwoSidedIdeal.one_mem_iff]
    refine TwoSidedIdeal.le_topologicalClosure _ ?_
    let I := TwoSidedIdeal.span ({e} : Set (CStarMatrix (Fin 2) (Fin 2) ℂ))
    have heI : e ∈ I := TwoSidedIdeal.subset_span (Set.mem_singleton e)
    let u : CStarMatrix (Fin 2) (Fin 2) ℂ := CStarMatrix.ofMatrix (Matrix.single 1 0 1)
    let v : CStarMatrix (Fin 2) (Fin 2) ℂ := CStarMatrix.ofMatrix (Matrix.single 0 1 1)
    have he11 : u * e * v ∈ I := I.mul_mem_right (u * e) v (I.mul_mem_left u e heI)
    have hsum : e + u * e * v = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [e, u, v, CStarMatrix.mul_apply, Fin.sum_univ_two]
    exact hsum ▸ I.add_mem heI he11
  have he_not_sp : ¬IsStrictlyPositive e := by
    rw [isStrictlyPositive_iff_of_unital]
    intro h
    obtain ⟨u, hu⟩ := h.isUnit
    let u_inv : CStarMatrix (Fin 2) (Fin 2) ℂ := ↑u⁻¹
    have hmul : e * u_inv = 1 := hu ▸ u.mul_inv
    have h11 : (e * u_inv) 1 1 = 0 := by
      simp [e, CStarMatrix.mul_apply]
    have hone : (1 : CStarMatrix (Fin 2) (Fin 2) ℂ) 1 1 = 1 := CStarMatrix.one_apply_eq 1
    exact one_ne_zero (hone ▸ hmul ▸ h11)
  exact ⟨e, he_nonneg, he_full, he_not_sp⟩

end TauCeti.CStarAlgebra
