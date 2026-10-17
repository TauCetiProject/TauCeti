/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.NormalOperator
import Mathlib.Analysis.CStarAlgebra.Fuglede
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# A common orthonormal eigenbasis for commuting normal operators

A commuting family of normal operators on a finite-dimensional complex inner product space
has a common orthonormal eigenbasis. The family need not be finite. This allows an entire
commutative group of unitary operators to be diagonalized by one change of basis.

The construction uses Mathlib's joint-eigenspace decomposition for symmetric operators,
applied to all real and imaginary parts. Fuglede's theorem ensures these parts commute.

## References

* S. Axler, *Linear Algebra Done Right*, 3rd ed., Springer (2015), Chapter 7.
-/

public section

namespace TauCeti

open Module Module.End ComplexStarModule LinearMap

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- A commuting family of normal operators has a common orthonormal eigenbasis, indexed by
any finite type of cardinality equal to the dimension. No finiteness of the family is needed. -/
theorem exists_orthonormalBasis_apply_eq_smul_of_pairwise_commute
    (T : ι → E →ₗ[ℂ] E) (hT : ∀ i, IsStarNormal (T i))
    (hC : Pairwise (fun i j => Commute (T i) (T j)))
    {κ : Type*} [Fintype κ] (hκ : Fintype.card κ = finrank ℂ E) :
    ∃ (b : OrthonormalBasis κ ℂ E) (μ : ι → κ → ℂ),
      ∀ i j, T i (b j) = μ i j • b j := by
  classical
  have := FiniteDimensional.complete ℂ E
  have hcomm (i j : ι) : Commute (T i) (T j) :=
    if h : i = j then h ▸ Commute.refl _ else hC h
  -- Fuglede's theorem is stated for continuous operators; in finite dimensions all maps qualify.
  have hstar (i j : ι) : Commute (T i) (star (T j)) := by
    let A := (T j).toContinuousLinearMap
    let B := (T i).toContinuousLinearMap
    have : IsStarNormal A := ⟨by
      ext x
      simpa [A, LinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
        ← LinearMap.adjoint_toContinuousLinearMap] using
        congrArg (fun f : E →ₗ[ℂ] E => f x) (hT j).star_comm_self.eq⟩
    have h : Commute B A := by
      ext x
      exact congrArg (fun f : E →ₗ[ℂ] E => f x) (hcomm i j).eq
    have hs := IsStarNormal.commute_star_right (a := A) inferInstance h
    ext x
    simpa [A, B, LinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
      ← LinearMap.adjoint_toContinuousLinearMap] using
      congrArg (fun f : E →L[ℂ] E => f x) hs.eq
  -- All real and imaginary parts are symmetric and commute with one another.
  let S : ι × Bool → E →ₗ[ℂ] E := fun p => if p.2 then ℑ (T p.1) else ℜ (T p.1)
  have hS (p : ι × Bool) : (S p).IsSymmetric := by
    dsimp [S]
    split
    · exact (isSymmetric_iff_isSelfAdjoint _).mpr (ℑ _).2
    · exact (isSymmetric_iff_isSelfAdjoint _).mpr (ℜ _).2
  have hSC : Pairwise (fun p q => Commute (S p) (S q)) := by
    intro p q _
    have h₁ := hcomm p.1 q.1
    have h₂ := hstar p.1 q.1
    have h₃ := (hstar q.1 p.1).symm
    have h₄ := (hcomm p.1 q.1).star_star
    rcases p with ⟨i, a⟩
    rcases q with ⟨j, b⟩
    cases a <;> cases b <;>
      simp only [S, Bool.false_eq_true, ↓reduceIte, realPart_apply_coe,
        imaginaryPart_apply_coe]
    · exact (((h₁.add_right h₂).add_left (h₃.add_right h₄)).smul_left _).smul_right _
    · exact ((((h₁.sub_right h₂).add_left (h₃.sub_right h₄)).smul_left _).smul_right
        (2⁻¹ : ℝ)).smul_right _
    · exact ((((h₁.add_right h₂).sub_left (h₃.add_right h₄)).smul_left
        (2⁻¹ : ℝ)).smul_left _).smul_right _
    · exact (((((h₁.sub_right h₂).sub_left (h₃.sub_right h₄)).smul_left
        (2⁻¹ : ℝ)).smul_left _).smul_right (2⁻¹ : ℝ)).smul_right _
  -- Only finitely many joint eigenspaces are nonzero. Choose a basis subordinate to them.
  let V : ((ι × Bool) → ℂ) → Submodule ℂ E := fun χ =>
    ⨅ p, eigenspace (S p) (χ p)
  have hV : DirectSum.IsInternal V :=
    IsSymmetric.directSum_isInternal_of_pairwise_commute hS hSC
  have hO := IsSymmetric.orthogonalFamily_iInf_eigenspaces hS
  let J := {χ : (ι × Bool) → ℂ // V χ ≠ ⊥}
  let _ : Fintype J := hV.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  have hVJ : DirectSum.IsInternal fun χ : J => V χ := DirectSum.isInternal_ne_bot_iff.mpr hV
  have hOJ := hO.comp (Subtype.val_injective (p := fun χ => V χ ≠ ⊥))
  let b := hVJ.subordinateOrthonormalBasis rfl hOJ
  let χ : Fin (finrank ℂ E) → J := fun j =>
    hVJ.subordinateOrthonormalBasisIndex rfl j hOJ
  let e : κ ≃ Fin (finrank ℂ E) := Fintype.equivFinOfCardEq hκ
  refine ⟨b.reindex e.symm, fun i j => (χ (e j)).1 (i, false) +
    Complex.I * (χ (e j)).1 (i, true), fun i j => ?_⟩
  have hmem := hVJ.subordinateOrthonormalBasis_subordinate rfl (e j) hOJ
  rw [OrthonormalBasis.reindex_apply, Equiv.symm_symm]
  exact apply_eq_smul_of_mem_eigenspace_realPart_imaginaryPart (T i)
    (by simpa [S] using ((Submodule.mem_iInf _).mp hmem (i, false)))
    (by simpa [S] using ((Submodule.mem_iInf _).mp hmem (i, true)))

end TauCeti
