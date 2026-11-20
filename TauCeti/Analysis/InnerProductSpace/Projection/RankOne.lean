/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Rank-one projections and orthonormal bases

Complete orthogonal families of unit rank-one projections correspond exactly to
orthonormal bases.

A. M. Gleason, *Measures on the Closed Subspaces of a Hilbert Space*, 1957, §1.
-/

public section

namespace TauCeti

/-- A complete orthogonal family of unit rank-one projections comes from an orthonormal basis. -/
theorem exists_orthonormalBasis_iff_complete_orthogonal_rankOne
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} [Fintype ι] {p : ι → E →L[ℂ] E} :
    (∃ b : OrthonormalBasis ι ℂ E,
        ∀ i, p i = InnerProductSpace.rankOne ℂ (b i) (b i)) ↔
      (∀ i, ∃ v : E, ‖v‖ = 1 ∧ p i = InnerProductSpace.rankOne ℂ v v) ∧
        (∀ i j, i ≠ j → p i * p j = 0) ∧ (∑ i, p i = 1) := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact ⟨b i, b.norm_eq_one i, hb i⟩
    · intro i j hij
      rw [hb i, hb j, ContinuousLinearMap.mul_def,
        InnerProductSpace.rankOne_comp_rankOne]
      simp [b.inner_eq_zero hij]
    · calc
        ∑ i, p i = ∑ i, InnerProductSpace.rankOne ℂ (b i) (b i) :=
          Finset.sum_congr rfl fun i _ => hb i
        _ = 1 := b.sum_rankOne_eq_id
  · rintro ⟨hunit, horth, hsum⟩
    classical
    choose v hvnorm hp using hunit
    have hv_ne : ∀ i, v i ≠ 0 := fun i => by
      intro h
      have h' : (0 : ℝ) = 1 := by simpa [h] using hvnorm i
      exact zero_ne_one h'
    -- Orthogonality of the projections forces orthogonality of their unit vectors.
    have hv_orth : Orthonormal ℂ v := by
      constructor
      · exact hvnorm
      · intro i j hij
        have hzero : InnerProductSpace.rankOne ℂ (v i) (v i) *
            InnerProductSpace.rankOne ℂ (v j) (v j) = 0 := by
          simpa only [hp i, hp j] using horth i j hij
        rw [ContinuousLinearMap.mul_def,
          InnerProductSpace.rankOne_comp_rankOne] at hzero
        exact (smul_eq_zero.mp hzero).resolve_right
          (InnerProductSpace.rankOne_ne_zero (hv_ne i) (hv_ne j))
    have hsum' : ∑ i, InnerProductSpace.rankOne ℂ (v i) (v i) = 1 := by
      rw [← hsum]
      exact Finset.sum_congr rfl fun i _ => (hp i).symm
    -- Completeness of the projection family makes the vectors span the whole space.
    have hsp : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
      intro x _
      have hx : (∑ i, InnerProductSpace.rankOne ℂ (v i) (v i)) x = x := by
        rw [hsum']
        simp
      rw [← hx]
      simp only [sum_apply, InnerProductSpace.rankOne_apply]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    let b : OrthonormalBasis ι ℂ E := OrthonormalBasis.mk hv_orth hsp
    refine ⟨b, fun i => ?_⟩
    simpa [b] using hp i

end TauCeti
