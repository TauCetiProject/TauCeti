/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.CompactResolvent
public import TauCeti.LinearAlgebra.LinearPMap.Restrict

/-!
# Orthonormal eigenbases of self-adjoint operators with compact resolvent

A self-adjoint operator `D` with compact resolvent on a complex Hilbert space `H` has a complete
orthonormal basis of eigenvectors, each in the domain of `D` and with a real eigenvalue. This is
the basis in which the functional calculus of such operators, and in particular of the Dirac
operator of a spectral triple, is written.

The proof diagonalizes `D` on finite-dimensional pieces. The compact positive injective operator
`K = (1 + D²)⁻¹` (`LinearPMap.invOneAddSq`) has mutually orthogonal eigenspaces with dense span.
Those for nonzero eigenvalues are finite-dimensional, contained in the domain of `D` and invariant
under `D`, and the eigenspace for `0` is trivial. On each of them `D` restricts to a symmetric
operator on a finite-dimensional inner product space, so it has an orthonormal eigenbasis with
real eigenvalues (`LinearMap.IsSymmetric.eigenvectorBasis`). Collecting these bases gives an
orthonormal family with dense span, hence a Hilbert basis. An eigenspace of `K` for an eigenvalue
`(1 + λ²)⁻¹` can contain eigenvectors of `D` for both `λ` and `-λ`, so the diagonalization of `D`
inside it is needed: an eigenbasis of `K` alone need not consist of eigenvectors of `D`.

The first step only uses that the pieces are finite-dimensional, mutually orthogonal, invariant
and densely spanning, and is stated for any symmetric partial linear map over `ℝ` or `ℂ`. The
assembly of the Hilbert basis from orthonormal bases of the pieces follows the bounded compact
symmetric case, `ContinuousLinearMap.exists_hilbertBasis_forall_hasEigenvector_of_dense_eigenspaces`
in `TauCeti.Analysis.InnerProductSpace.Spectrum`.

## Main results

* `LinearPMap.IsFormalAdjoint.exists_hilbertBasis_forall_apply_eq_smul_of_orthogonalFamily`: a
  symmetric partial linear map which preserves each member of a densely spanning orthogonal family
  of finite-dimensional subspaces of its domain has a Hilbert basis of eigenvectors with real
  eigenvalues.
* `IsSelfAdjoint.exists_hilbertBasis_forall_apply_eq_smul_of_hasCompactResolvent`: a self-adjoint
  operator with compact resolvent has a Hilbert basis of eigenvectors with real eigenvalues.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics IV: Analysis of Operators*,
  §XIII.14.
* A. Connes, *Noncommutative Geometry*, Chapter IV, §2.
-/

public section

open Module End Submodule

universe u

namespace LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **Diagonalization on invariant finite-dimensional pieces.** Let `A` be a symmetric partial
linear map and `V` a family of mutually orthogonal finite-dimensional subspaces of the domain of
`A` whose span is dense. If `A` maps each `V i` into itself, then the Hilbert space has a Hilbert
basis consisting of eigenvectors of `A` with real eigenvalues. -/
theorem IsFormalAdjoint.exists_hilbertBasis_forall_apply_eq_smul_of_orthogonalFamily
    {A : E →ₗ.[𝕜] E} (hA : A.IsFormalAdjoint A) {ι : Type u} (V : ι → Submodule 𝕜 E)
    [∀ i, FiniteDimensional 𝕜 (V i)]
    (hV : OrthogonalFamily 𝕜 (fun i ↦ V i) fun i ↦ (V i).subtypeₗᵢ)
    (hdom : ∀ i, V i ≤ A.domain) (hinv : ∀ i, A.IsInvariant (V i))
    (hspan : (⨆ i, V i)ᗮ = ⊥) :
    ∃ (κ : Type u) (b : HilbertBasis κ 𝕜 E) (lam : κ → ℝ),
      ∀ k, ∃ hk : b k ∈ A.domain, A ⟨b k, hk⟩ = (lam k : 𝕜) • b k := by
  -- As `V i` lies in the domain of `A`, the restriction of `A` to `V i` is an endomorphism of
  -- `V i`, and it is symmetric.
  let T (i : ι) : V i →ₗ[𝕜] V i :=
    (A.toFun ∘ₗ inclusion (hdom i)).codRestrict (V i) fun x ↦ (hinv i).apply_mem _ x.2
  have hT_apply (i : ι) (x : V i) : (T i x : E) = A ⟨x, hdom i x.2⟩ := rfl
  have hT (i : ι) : (T i).IsSymmetric := fun x y ↦ by
    rw [coe_inner, coe_inner, hT_apply, hT_apply]
    exact hA ⟨x, hdom i x.2⟩ ⟨y, hdom i y.2⟩
  -- Collect orthonormal eigenbases of the restrictions into one orthonormal family in `E`.
  let b (i : ι) : OrthonormalBasis (Fin (finrank 𝕜 (V i))) 𝕜 (V i) :=
    (hT i).eigenvectorBasis rfl
  let v : (Σ i, Fin (finrank 𝕜 (V i))) → E := fun p ↦ (V p.1).subtypeₗᵢ (b p.1 p.2)
  have hv : Orthonormal 𝕜 v := hV.orthonormal_sigma_orthonormal fun i ↦ (b i).orthonormal
  -- Each `V i` lies in the span of the family, so the span is dense.
  have hsp : (span 𝕜 (Set.range v))ᗮ = ⊥ := by
    refine eq_bot_iff.2 ((orthogonal_le (iSup_le fun i y hy ↦ ?_)).trans hspan.le)
    have hy' : ∑ j, (b i).repr ⟨y, hy⟩ j • v ⟨i, j⟩ = y := by
      simpa [v] using congrArg Subtype.val ((b i).sum_repr ⟨y, hy⟩)
    rw [← hy']
    exact sum_mem fun j _ ↦ smul_mem _ _ (subset_span ⟨⟨i, j⟩, rfl⟩)
  -- The family consists of eigenvectors of `A`.
  have hev (p : Σ i, Fin (finrank 𝕜 (V i))) : ∃ hk : v p ∈ A.domain,
      A ⟨v p, hk⟩ = ((hT p.1).eigenvalues rfl p.2 : 𝕜) • v p := by
    refine ⟨hdom p.1 (b p.1 p.2).2, ?_⟩
    have h := congrArg Subtype.val ((hT p.1).apply_eigenvectorBasis rfl p.2)
    rw [hT_apply] at h
    simpa [v, b] using h
  refine ⟨_, HilbertBasis.mkOfOrthogonalEqBot hv hsp, fun p ↦ (hT p.1).eigenvalues rfl p.2, ?_⟩
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  exact hev

end LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open LinearPMap in
/-- **Orthonormal eigenbasis of a self-adjoint operator with compact resolvent.** A self-adjoint
operator `A` with compact resolvent on a complex Hilbert space has a Hilbert basis consisting of
vectors in its domain which are eigenvectors of `A` with real eigenvalues. -/
theorem IsSelfAdjoint.exists_hilbertBasis_forall_apply_eq_smul_of_hasCompactResolvent
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) :
    ∃ (κ : Type) (b : HilbertBasis κ ℂ H) (lam : κ → ℝ),
      ∀ k, ∃ hk : b k ∈ A.domain, A ⟨b k, hk⟩ = (lam k : ℂ) • b k := by
  have hp := hA.I_mem_resolventSet
  have hm := hA.neg_I_mem_resolventSet
  have hK := hA.isPositive_invOneAddSq.isSymmetric
  have h0 := eigenspace_invOneAddSq_zero_eq_bot hp hm
  have : ∀ μ, FiniteDimensional ℂ (eigenspace (A.invOneAddSq : End ℂ H) μ) := fun μ ↦ by
    rcases eq_or_ne μ 0 with rfl | hμ
    · rw [h0]
      infer_instance
    · exact h.finiteDimensional_eigenspace_invOneAddSq hp hμ
  refine hA.isFormalAdjoint.exists_hilbertBasis_forall_apply_eq_smul_of_orthogonalFamily _
    hK.orthogonalFamily_eigenspaces (fun μ ↦ ?_)
    (fun _ ↦ isInvariant_iff.2 fun x hx ↦ apply_mem_eigenspace_invOneAddSq hp hm x hx)
    (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
      (h.isCompactOperator_invOneAddSq hp) hK)
  rcases eq_or_ne μ 0 with rfl | hμ
  · exact h0.le.trans bot_le
  · simpa using eigenspace_invOneAddSq_le_domainPow hp hm hμ 1
