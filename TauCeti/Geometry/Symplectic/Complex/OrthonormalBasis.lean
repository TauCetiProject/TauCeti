/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# Adapted orthonormal bases of an orthogonal complex structure

Let `V` be a real inner product space of dimension four and `J` an orthogonal almost complex
structure on `V`, that is, `‖J v‖ = ‖v‖` for every `v`. Then `V` has an orthonormal basis of the
form `(u₁, J u₁, u₂, J u₂)`: pick a unit vector `u₁`, note that `J u₁` is a unit vector orthogonal
to it, and pick a unit vector `u₂` orthogonal to both. The orientation of such a basis is the
orientation induced by `J`.

## Main results

* `TauCeti.AlmostComplexStructure.exists_adapted_orthonormalBasis`: an orthogonal complex
  structure on a four-dimensional inner product space has an adapted orthonormal basis
  `(u₁, J u₁, u₂, J u₂)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
-/

public section

namespace TauCeti.AlmostComplexStructure

open Module
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  (J : AlmostComplexStructure V)

/-- **An orthogonal complex structure on a four-dimensional inner product space has an adapted
orthonormal basis** `(u₁, J u₁, u₂, J u₂)`. The orientation of such a basis is the orientation
induced by `J`. -/
theorem exists_adapted_orthonormalBasis (hJ : ∀ v, ‖J v‖ = ‖v‖) :
    ∃ b : OrthonormalBasis (Fin 4) ℝ V, b 1 = J (b 0) ∧ b 3 = J (b 2) := by
  have hinner (v w : V) : ⟪J v, J w⟫ = ⟪v, w⟫ :=
    ({ J.toLinearMap with norm_map' := hJ } : V →ₗᵢ[ℝ] V).inner_map_map v w
  have hswap (v w : V) : ⟪v, J w⟫ = -⟪J v, w⟫ := by
    have h := hinner v (J w)
    rw [apply_apply, inner_neg_right] at h
    linarith
  have hperp (v : V) : ⟪v, J v⟫ = 0 := by
    linarith [hswap v v, real_inner_comm v (J v)]
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ V = 4)
  obtain ⟨u₁, hu₁⟩ := exists_norm_eq V zero_le_one
  set K := Submodule.span ℝ (Set.range ![u₁, J u₁])
  have : Nontrivial Kᗮ := by
    apply (Module.finrank_pos_iff (R := ℝ) (M := Kᗮ)).mp
    have h₁ := K.finrank_add_finrank_orthogonal
    have h₂ : finrank ℝ K ≤ 2 := (finrank_range_le_card _).trans (by simp)
    rw [Fact.out (p := finrank ℝ V = 4)] at h₁
    omega
  obtain ⟨⟨u₂, hu₂K⟩, hu₂⟩ := exists_norm_eq Kᗮ zero_le_one
  replace hu₂ : ‖u₂‖ = 1 := hu₂
  have h₁₂ : ⟪u₁, u₂⟫ = 0 := hu₂K u₁ (Submodule.subset_span ⟨0, rfl⟩)
  have hJ₁₂ : ⟪J u₁, u₂⟫ = 0 := hu₂K _ (Submodule.subset_span ⟨1, rfl⟩)
  have hperp' (v : V) : ⟪J v, v⟫ = 0 := by rw [real_inner_comm, hperp]
  have h₂₁ : ⟪u₂, u₁⟫ = 0 := by rw [real_inner_comm, h₁₂]
  have h₂J₁ : ⟪u₂, J u₁⟫ = 0 := by rw [real_inner_comm, hJ₁₂]
  have h₁J₂ : ⟪u₁, J u₂⟫ = 0 := by rw [hswap, hJ₁₂, neg_zero]
  have hJ₂₁ : ⟪J u₂, u₁⟫ = 0 := by rw [real_inner_comm, h₁J₂]
  have hf : Orthonormal ℝ ![u₁, J u₁, u₂, J u₂] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hJ, hinner, hperp, hperp', hu₁, hu₂, h₁₂, hJ₁₂, h₂₁, h₂J₁, h₁J₂, hJ₂₁]
  have hsp := hf.linearIndependent.span_eq_top_of_card_eq_finrank
    (by rw [Fintype.card_fin, Fact.out (p := finrank ℝ V = 4)])
  refine ⟨OrthonormalBasis.mk hf hsp.ge, ?_, ?_⟩ <;> simp

end TauCeti.AlmostComplexStructure
