/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Analysis.CStarAlgebra.Fuglede
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Tactic.Module

/-!
# Spectral theorems for commuting normal operators

A linear operator `T` on a finite-dimensional complex inner product space is **normal** when it
commutes with its adjoint, `IsStarNormal T`. The spectral theorem says that `T` is then
diagonalized by an orthonormal basis: there is an orthonormal basis of eigenvectors of `T`.
Mathlib proves this for symmetric (self-adjoint) operators,
`LinearMap.IsSymmetric.eigenvectorBasis`; this file extends it to normal ones.

The family theorem `TauCeti.exists_orthonormalBasis_apply_eq_smul_of_pairwise_commute`
constructs a common orthonormal eigenbasis for any commuting family of normal operators,
including infinite families. It applies Mathlib's joint-eigenspace decomposition to all real
and imaginary parts; Fuglede's theorem ensures that these parts commute. The single-operator
spectral theorem follows by taking a singleton family.

Unlike the self-adjoint case, the eigenvalues are complex, and the statement is specific to
complex scalars: a rotation of the real plane is normal but has no real eigenvector.

## Main results

* `TauCeti.exists_orthonormalBasis_apply_eq_smul_of_pairwise_commute`: a common orthonormal
  eigenbasis for any commuting family of normal operators.

* `LinearMap.exists_orthonormalBasis_apply_eq_smul_of_isStarNormal`: **the spectral theorem for
  normal operators**, a normal operator on a finite-dimensional complex inner product space has
  an orthonormal basis of eigenvectors, indexed by any finite type of the right cardinality.

## References

* S. Axler, *Linear Algebra Done Right*, 3rd ed., Springer (2015), Theorem 7.24 (the complex
  spectral theorem).
-/

public section

namespace TauCeti

open Module Module.End ComplexStarModule LinearMap

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- On a joint eigenspace of the real and imaginary parts of `T`, where `ℜ T` acts by `a` and
`ℑ T` by `b`, the operator `T` acts by `a + i b`. Normality is not needed here; finite
dimensionality only enters because the adjoint, hence `ℜ T` and `ℑ T`, is defined on
finite-dimensional spaces. -/
theorem apply_eq_smul_of_mem_eigenspace_realPart_imaginaryPart (T : E →ₗ[ℂ] E)
    {a b : ℂ} {v : E} (ha : v ∈ eigenspace (ℜ T : E →ₗ[ℂ] E) a)
    (hb : v ∈ eigenspace (ℑ T : E →ₗ[ℂ] E) b) :
    T v = (a + Complex.I * b) • v := by
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart T]
  rw [LinearMap.add_apply, LinearMap.smul_apply, mem_eigenspace_iff.mp ha,
    mem_eigenspace_iff.mp hb, add_smul,
    mul_smul]

/-- Finite-dimensional Fuglede: an operator commuting with a normal operator also commutes
with its adjoint. -/
theorem commute_star_right_of_isStarNormal {T S : E →ₗ[ℂ] E} [IsStarNormal S]
    (h : Commute T S) : Commute T (star S) := by
  have := FiniteDimensional.complete ℂ E
  have hc : Commute T.toContinuousLinearMap S.toContinuousLinearMap := by
    ext x
    exact congrArg (fun f : E →ₗ[ℂ] E => f x) h.eq
  have hs := IsStarNormal.commute_star_right (a := S.toContinuousLinearMap) inferInstance hc
  rw [← toContinuousLinearMap_star] at hs
  ext x
  exact congrArg (fun f : E →L[ℂ] E => f x) hs.eq

/-- The real and imaginary parts of two commuting normal operators commute in all four
combinations. -/
theorem commute_realPart_imaginaryPart_of_commute {T S : E →ₗ[ℂ] E}
    [IsStarNormal T] [IsStarNormal S] (h : Commute T S) :
    Commute (ℜ T : E →ₗ[ℂ] E) (ℜ S : E →ₗ[ℂ] E) ∧
      Commute (ℜ T : E →ₗ[ℂ] E) (ℑ S : E →ₗ[ℂ] E) ∧
      Commute (ℑ T : E →ₗ[ℂ] E) (ℜ S : E →ₗ[ℂ] E) ∧
      Commute (ℑ T : E →ₗ[ℂ] E) (ℑ S : E →ₗ[ℂ] E) := by
  have h₂ := commute_star_right_of_isStarNormal h
  have h₃ := (commute_star_right_of_isStarNormal h.symm).symm
  have h₄ := h.star_star
  -- Expand multiplication, use the four commutation relations, then normalize scalars.
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp only [realPart_apply_coe, imaginaryPart_apply_coe, commute_iff_eq,
      smul_mul_assoc, mul_smul_comm, mul_add, add_mul, mul_sub, sub_mul,
      h.eq, h₂.eq, h₃.eq, h₄.eq]
    module

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
  -- All real and imaginary parts are symmetric and commute with one another.
  let S : ι × Bool → E →ₗ[ℂ] E := fun p => if p.2 then ℑ (T p.1) else ℜ (T p.1)
  have hS (p : ι × Bool) : (S p).IsSymmetric := by
    dsimp [S]
    split
    · exact (isSymmetric_iff_isSelfAdjoint _).mpr (ℑ _).2
    · exact (isSymmetric_iff_isSelfAdjoint _).mpr (ℜ _).2
  have hSC : Pairwise (fun p q => Commute (S p) (S q)) := by
    intro p q _
    have := hT p.1
    have := hT q.1
    have h := commute_realPart_imaginaryPart_of_commute (hcomm p.1 q.1)
    rcases p with ⟨i, a⟩
    rcases q with ⟨j, b⟩
    cases a <;> cases b
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2
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

open Module

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- **The spectral theorem for normal operators.** A normal operator on a finite-dimensional
complex inner product space has an orthonormal basis of eigenvectors. The basis may be indexed by
any finite type whose cardinality is the dimension of the space. -/
theorem exists_orthonormalBasis_apply_eq_smul_of_isStarNormal (T : E →ₗ[ℂ] E) [IsStarNormal T]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = finrank ℂ E) :
    ∃ (b : OrthonormalBasis ι ℂ E) (μ : ι → ℂ), ∀ i, T (b i) = μ i • b i := by
  obtain ⟨b, μ, hb⟩ := TauCeti.exists_orthonormalBasis_apply_eq_smul_of_pairwise_commute
    (fun _ : Unit => T) (fun _ => inferInstance) (fun _ _ _ => Commute.refl _) hι
  exact ⟨b, μ (), hb ()⟩

end LinearMap
