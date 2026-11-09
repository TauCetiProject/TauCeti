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

*Eigenspaces of bounded normal operators.* For a normal bounded operator `T` on a Hilbert space,
`‖(T - μ) x‖ = ‖(T - μ)† x‖`, so `T x = μ x` exactly when `T† x = conj μ x`
(`IsStarNormal.adjoint_apply_eq_smul_iff`). Consequently the eigenspaces of `T` are mutually
orthogonal (`IsStarNormal.orthogonalFamily_eigenspaces`), and the orthogonal complement of all of
them is invariant under `T`. Over `ℂ`, the eigenspace of `T` at `μ` is the joint eigenspace of its
real part `ℜ T` at `re μ` and its imaginary part `ℑ T` at `im μ`. These facts need no finite
dimensionality.

## Main results

* `TauCeti.exists_orthonormalBasis_apply_eq_smul_of_pairwise_commute`: a common orthonormal
  eigenbasis for any commuting family of normal operators.

* `LinearMap.exists_orthonormalBasis_apply_eq_smul_of_isStarNormal`: **the spectral theorem for
  normal operators**, a normal operator on a finite-dimensional complex inner product space has
  an orthonormal basis of eigenvectors, indexed by any finite type of the right cardinality.

* `IsStarNormal.adjoint_apply_eq_smul_iff`: for a normal bounded operator `T`,
  `T† x = conj μ • x ↔ T x = μ • x`.

* `IsStarNormal.orthogonalFamily_eigenspaces`: the eigenspaces of a normal bounded operator are
  mutually orthogonal.

## References

* S. Axler, *Linear Algebra Done Right*, 3rd ed., Springer (2015), Theorem 7.24 (the complex
  spectral theorem).
-/

public section

namespace IsStarNormal

open Module.End ContinuousLinearMap ComplexStarModule
open scoped InnerProductSpace ComplexConjugate

/-! ### Eigenspaces of bounded normal operators -/

section Normal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] {T : E →L[𝕜] E}

/-- A vector is an eigenvector of the adjoint of a normal operator `T` with eigenvalue `conj μ`
exactly when it is an eigenvector of `T` with eigenvalue `μ`. -/
theorem adjoint_apply_eq_smul_iff (hT : IsStarNormal T) (μ : 𝕜) (x : E) :
    adjoint T x = conj μ • x ↔ T x = μ • x := by
  have hN : IsStarNormal (T - μ • 1) :=
    Commute.isStarNormal_sub (by simpa using (Commute.one_right T).smul_right (conj μ))
  simpa [sub_eq_zero, ← star_eq_adjoint] using
    ContinuousLinearMap.IsStarNormal.adjoint_apply_eq_zero_iff hN x

/-- The eigenspace of the adjoint of a normal operator at `conj μ` is the eigenspace of the
operator at `μ`. -/
theorem eigenspace_adjoint (hT : IsStarNormal T) (μ : 𝕜) :
    eigenspace (adjoint T : Module.End 𝕜 E) (conj μ) = eigenspace (T : Module.End 𝕜 E) μ := by
  ext x
  simpa only [mem_eigenspace_iff, coe_coe] using hT.adjoint_apply_eq_smul_iff μ x

/-- The eigenspaces of a normal operator are mutually orthogonal. -/
theorem orthogonalFamily_eigenspaces (hT : IsStarNormal T) :
    OrthogonalFamily 𝕜 (fun μ ↦ eigenspace (T : Module.End 𝕜 E) μ)
      fun μ ↦ (eigenspace (T : Module.End 𝕜 E) μ).subtypeₗᵢ := by
  rintro μ ν hμν ⟨v, hv⟩ ⟨w, hw⟩
  rw [mem_eigenspace_iff, coe_coe] at hv hw
  have h := adjoint_inner_left T w v
  rw [(hT.adjoint_apply_eq_smul_iff μ v).2 hv, hw, inner_smul_left, inner_smul_right,
    RCLike.conj_conj] at h
  exact (mul_eq_mul_right_iff.mp h).resolve_left hμν

/-- The orthogonal complement of the eigenspaces of a normal operator is invariant under the
operator. -/
theorem orthogonalComplement_iSup_eigenspaces_invariant (hT : IsStarNormal T) ⦃v : E⦄
    (hv : v ∈ (⨆ μ, eigenspace (T : Module.End 𝕜 E) μ)ᗮ) :
    T v ∈ (⨆ μ, eigenspace (T : Module.End 𝕜 E) μ)ᗮ := by
  rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf] at hv ⊢
  intro μ
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [← adjoint_inner_left, (hT.adjoint_apply_eq_smul_iff μ u).2 (mem_eigenspace_iff.mp hu),
    inner_smul_left, Submodule.inner_right_of_mem_orthogonal hu (hv μ), mul_zero]

end Normal

section Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {T : E →L[ℂ] E}

/-- The eigenspace of a normal operator at `μ` is the joint eigenspace of its real part at
`re μ` and its imaginary part at `im μ`. -/
theorem eigenspace_eq_eigenspace_realPart_inf_eigenspace_imaginaryPart (hT : IsStarNormal T)
    (μ : ℂ) :
    eigenspace (T : Module.End ℂ E) μ =
      eigenspace ((ℜ T : E →L[ℂ] E) : Module.End ℂ E) μ.re ⊓
        eigenspace ((ℑ T : E →L[ℂ] E) : Module.End ℂ E) μ.im := by
  ext x
  simp only [Submodule.mem_inf, mem_eigenspace_iff, coe_coe]
  constructor
  · intro hx
    have hx' := (hT.adjoint_apply_eq_smul_iff μ x).2 hx
    simp only [realPart_apply_coe, imaginaryPart_apply_coe, star_eq_adjoint, add_apply, sub_apply,
      smul_apply, hx, hx', ← add_smul, ← sub_smul, Complex.add_conj, Complex.sub_conj, smul_smul,
      ← Complex.coe_smul]
    constructor
    · congr 1
      push_cast
      ring
    · congr 1
      push_cast
      linear_combination (-(μ.im : ℂ)) * Complex.I_sq
  · rintro ⟨hre, him⟩
    rw [← realPart_add_I_smul_imaginaryPart T, add_apply, smul_apply, hre, him, smul_smul,
      ← add_smul, mul_comm, Complex.re_add_im]

end Complex

end IsStarNormal

open Function Module Module.End ComplexStarModule LinearMap

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

namespace LinearMap

/-- On a joint eigenspace of the real and imaginary parts of `T`, where `ℜ T` acts by `a` and
`ℑ T` by `b`, the operator `T` acts by `a + i b`. Normality is not needed here; finite
dimensionality only enters because the adjoint, hence `ℜ T` and `ℑ T`, is defined on
finite-dimensional spaces. -/
theorem apply_eq_smul_of_mem_eigenspace_realPart_imaginaryPart (T : E →ₗ[ℂ] E)
    {a b : ℂ} {v : E} (ha : v ∈ eigenspace (ℜ T : E →ₗ[ℂ] E) a)
    (hb : v ∈ eigenspace (ℑ T : E →ₗ[ℂ] E) b) :
    T v = (a + Complex.I * b) • v := by
  rw [← realPart_add_I_smul_imaginaryPart T, LinearMap.add_apply, LinearMap.smul_apply,
    mem_eigenspace_iff.mp ha, mem_eigenspace_iff.mp hb, add_smul, mul_smul]

end LinearMap

namespace Commute

/-- Finite-dimensional Fuglede: an operator commuting with a normal operator also commutes
with its adjoint. -/
theorem star_right_of_isStarNormal {T S : E →ₗ[ℂ] E} [IsStarNormal S]
    (h : Commute T S) : Commute T (star S) := by
  have := FiniteDimensional.complete ℂ E
  -- Transfer commutation along the endomorphism algebra equivalence in both directions.
  have hc := h.map (Module.End.toContinuousLinearMap (𝕜 := ℂ) E)
  have hs := IsStarNormal.commute_star_right (a := S.toContinuousLinearMap) inferInstance hc
  rw [← toContinuousLinearMap_star] at hs
  exact hs.of_map (Module.End.toContinuousLinearMap (𝕜 := ℂ) E).injective

/-- The real and imaginary parts of two commuting normal operators commute in all four
combinations. -/
theorem realPart_imaginaryPart_of_isStarNormal {T S : E →ₗ[ℂ] E}
    [IsStarNormal T] [IsStarNormal S] (h : Commute T S) :
    Commute (ℜ T : E →ₗ[ℂ] E) (ℜ S : E →ₗ[ℂ] E) ∧
      Commute (ℜ T : E →ₗ[ℂ] E) (ℑ S : E →ₗ[ℂ] E) ∧
      Commute (ℑ T : E →ₗ[ℂ] E) (ℜ S : E →ₗ[ℂ] E) ∧
      Commute (ℑ T : E →ₗ[ℂ] E) (ℑ S : E →ₗ[ℂ] E) := by
  have h₂ := h.star_right_of_isStarNormal
  have h₃ := h.symm.star_right_of_isStarNormal.symm
  have h₄ := h.star_star
  -- Expand multiplication, use the four commutation relations, then normalize scalars.
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp only [realPart_apply_coe, imaginaryPart_apply_coe, commute_iff_eq,
      smul_mul_assoc, mul_smul_comm, mul_add, add_mul, mul_sub, sub_mul,
      h.eq, h₂.eq, h₃.eq, h₄.eq]
    module

end Commute

namespace TauCeti

/-- A commuting family of normal operators has a common orthonormal eigenbasis, indexed by
any finite type of cardinality equal to the dimension. No finiteness of the family is needed. -/
theorem exists_orthonormalBasis_apply_eq_smul_of_pairwise_commute
    (T : ι → E →ₗ[ℂ] E) (hT : ∀ i, IsStarNormal (T i))
    (hC : Pairwise (Commute on T))
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
    rw [isSymmetric_iff_isSelfAdjoint]
    rcases p with ⟨i, _ | _⟩
    exacts [(ℜ (T i)).2, (ℑ (T i)).2]
  have hSC : Pairwise (Commute on S) := by
    rintro ⟨i, a⟩ ⟨j, b⟩ -
    have := hT i
    have := hT j
    have h := (hcomm i j).realPart_imaginaryPart_of_isStarNormal
    cases a <;> cases b
    exacts [h.1, h.2.1, h.2.2.1, h.2.2.2]
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
  exact (T i).apply_eq_smul_of_mem_eigenspace_realPart_imaginaryPart
    (by simpa [S] using ((Submodule.mem_iInf _).mp hmem (i, false)))
    (by simpa [S] using ((Submodule.mem_iInf _).mp hmem (i, true)))

end TauCeti

namespace LinearMap

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
