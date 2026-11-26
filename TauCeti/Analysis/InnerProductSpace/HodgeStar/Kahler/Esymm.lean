/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Power
public import TauCeti.Analysis.InnerProductSpace.RelativeEigenvalues.HermitianForm
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
public import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Pow.Esymm
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Complex
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# Powers of a (1,1)-form wedged with powers of the Kähler form

Let `E` be a complex inner product space of dimension `n`, with `ω` the Kähler form of
multiplication by `i` and the real inner product `Re ⟪·, ·⟫_ℂ`, and let `α` be a real two-form of
type (1,1), with eigenvalues `λ[α]` of its Hermitian form `H_α` relative to the inner product. Then
for `k + l = n`

`α ^ k ∧ ω ^ l = (k! l! / n!) σ_k(λ[α]) ω ^ n`

(`TauCeti.AlmostComplexStructure.wedge_wedgePow_wedgePow_ofComplexModule`), where `σ_k` is the
`k`-th elementary symmetric polynomial. This is the form identity
`α ^ k ∧ ω ^ (n - k) = (k! (n - k)! / n!) σ_k(λ[α]) ω ^ n` of complex Hessian equations. For
`k = n` it is `α ^ n = (∏ⱼ λⱼ[α]) ω ^ n`
(`TauCeti.AlmostComplexStructure.wedgePow_ofComplexModule`), and for `k = 1` it is the trace
identity `n α ∧ ω ^ (n - 1) = (∑ⱼ λⱼ[α]) ω ^ n`
(`TauCeti.AlmostComplexStructure.nsmul_wedge_wedgePow_ofComplexModule`). For `n = 2` and
`λ[α] = (λ₁, λ₂)` it reads `α ∧ ω = ((λ₁ + λ₂) / 2) ω ^ 2`.

Both sides are forms of top degree, so they are compared on the real frame
`(u₁, i u₁, …, uₙ, i uₙ)` of an orthonormal eigenbasis `u` of `H_α`
(`LinearMap.IsSymm.relEigenvectorBasis`), on which `ω ^ n` takes the value `n!`. On that frame
both `α` and `ω` are diagonal: `α(uⱼ, uₖ) = ω(uⱼ, uₖ) = 0`, `α(uⱼ, i uₖ) = λⱼ δⱼₖ` and
`ω(uⱼ, i uₖ) = δⱼₖ`. So `α ^ k ∧ ω ^ l` takes the value `k! l! σ_k(λ[α])` there
(`ContinuousAlternatingMap.pairedWedge_wedgePow_wedgePow_apply_finProdFinEquiv`).

The two sides have degrees `2 k + 2 l` and `2 n`, so the identity is stated on every tuple of
vectors, with the tuple reindexed along `2 n = 2 k + 2 l`.

## Main results

* `TauCeti.AlmostComplexStructure.wedge_wedgePow_wedgePow_apply_complexRealFrame`: the value
  `k! l! σ_k(λ[α])` of `α ^ k ∧ ω ^ l` on the real frame of the eigenbasis.
* `TauCeti.AlmostComplexStructure.wedge_wedgePow_wedgePow_ofComplexModule`: the form identity
  `α ^ k ∧ ω ^ l = (k! l! / n!) σ_k(λ[α]) ω ^ n`.

## References

* S. Dinew and S. Kołodziej, *A priori estimates for complex Hessian equations*, Anal. PDE 7
  (2014), read as arXiv:1112.3063v1 (the form identity, lines 33–35).
-/

public section

noncomputable section

open Module ContinuousAlternatingMap Complex

namespace TauCeti.AlmostComplexStructure

attribute [local instance] InnerProductSpace.complexToReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {α : E [⋀^Fin 2]→L[ℝ] ℝ} (hα : ∀ u v : E, α ![I • u, I • v] = α ![u, v])
include hα

/-- On the real frame `(u₁, i u₁, …, uₙ, i uₙ)` of the eigenbasis `u` of `H_α`, the form
`α ^ k ∧ ω ^ l`, for `k + l = n`, takes the value `k! l! σ_k(λ[α])`. -/
theorem wedge_wedgePow_wedgePow_apply_complexRealFrame {n k l : ℕ} (hn : finrank ℂ E = n)
    (hkl : k + l = n) :
    wedge (α.wedgePow k) ((alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow l)
        ((ofComplexModule E).complexRealFrame
          ((isSymm_hermitianSesqForm hα).relEigenvectorBasis hn) ∘ Fin.cast (by omega)) =
      k.factorial * l.factorial * MvPolynomial.eval
        ((isSymm_hermitianSesqForm hα).relEigenvalues hn) (MvPolynomial.esymm (Fin n) ℝ k) := by
  set u := (isSymm_hermitianSesqForm hα).relEigenvectorBasis hn
  rw [wedge_def, complexRealFrame_def]
  simp only [Function.comp_def, Fin.cast_cast]
  -- The goal is now the lemma's tuple, up to beta-reducing the pair family `b` below and
  -- unfolding the coercion of `ofComplexModule E`.
  exact pairedWedge_wedgePow_wedgePow_apply_finProdFinEquiv α _ hkl
    (fun p : Fin n × Fin 2 ↦ ![u p.1, ofComplexModule E (u p.1)] p.2)
    ((isSymm_hermitianSesqForm hα).relEigenvalues hn) (apply_relEigenvectorBasis_eq_zero hα hn)
    (apply_relEigenvectorBasis_ofComplexModule hα hn)
    (alternatingFormEquiv_kahlerForm_vecCons_eq_zero real_inner_ofComplexModule_ofComplexModule
      u.orthonormal.real_inner_ofComplexModule_eq_zero)
    (alternatingFormEquiv_kahlerForm_vecCons_apply real_inner_ofComplexModule_ofComplexModule
      u.orthonormal.real)

/-- **The form identity** `α ^ k ∧ ω ^ l = (k! l! / n!) σ_k(λ[α]) ω ^ n`: on a complex inner
product space of dimension `n = k + l`, with `ω` the Kähler form of multiplication by `i`, a real
two-form `α` of type (1,1) satisfies it on every tuple of `2 n` vectors, where `λ[α]` are the
eigenvalues of the Hermitian form `H_α` relative to the inner product and `σ_k` is the `k`-th
elementary symmetric polynomial. -/
theorem wedge_wedgePow_wedgePow_ofComplexModule {n k l : ℕ} (hn : finrank ℂ E = n)
    (hkl : k + l = n) (v : Fin (2 * n) → E) :
    wedge (α.wedgePow k) ((alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow l)
        (v ∘ Fin.cast (by omega)) =
      (k.factorial * l.factorial / n.factorial * MvPolynomial.eval
        ((isSymm_hermitianSesqForm hα).relEigenvalues hn) (MvPolynomial.esymm (Fin n) ℝ k)) *
        (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow n v := by
  set u := (isSymm_hermitianSesqForm hα).relEigenvectorBasis hn
  have huR : Orthonormal ℝ (u : Fin n → E) := u.orthonormal.real
  have hJu := u.orthonormal.real_inner_ofComplexModule_eq_zero
  have hJ := real_inner_ofComplexModule_ofComplexModule (E := E)
  -- The real frame of the eigenbasis is a basis of `E`, indexed by `Fin (2 n)`.
  let B : Basis (Fin (2 * n)) ℝ E := basisOfLinearIndependentOfCardEqFinrank' _
    ((orthonormal_complexRealFrame_iff hJ).2 ⟨huR, hJu⟩).linearIndependent
    (by simp [finrank_real_of_complex, hn])
  have hB : (B : Fin (2 * n) → E) = (ofComplexModule E).complexRealFrame u :=
    coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  have hcast : 2 * k + 2 * l = 2 * n := by omega
  rw [apply_eq_det_mul _ (B.reindex (finCongr hcast.symm)),
    apply_eq_det_mul _ B v, Basis.det_reindex, Basis.coe_reindex, hB,
    wedgePow_kahlerForm_apply_complexRealFrame hJ huR hJu]
  have hval := wedge_wedgePow_wedgePow_apply_complexRealFrame hα hn hkl
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hv : v ∘ Fin.cast (by omega) ∘ finCongr hcast.symm = v := by
    funext r
    simp only [Function.comp_apply, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
  have hfr : (ofComplexModule E).complexRealFrame u ∘ (finCongr hcast.symm).symm =
      (ofComplexModule E).complexRealFrame u ∘ Fin.cast (by omega) := by
    funext r
    simp only [Function.comp_apply, finCongr_symm, finCongr_apply]
  rw [Function.comp_assoc, hv, hfr, hval]
  field_simp

end TauCeti.AlmostComplexStructure
