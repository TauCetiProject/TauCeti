/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Power
public import TauCeti.Analysis.InnerProductSpace.RelativeEigenvalues.HermitianForm
public import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Complex

/-!
# The top power of a (1,1)-form

Let `E` be a complex inner product space of dimension `n`, with `ω` the Kähler form of
multiplication by `i` and the real inner product `Re ⟪·, ·⟫_ℂ`, and let `α` be a real two-form of
type (1,1), with eigenvalues `λ[α]` of its Hermitian form `H_α` relative to the inner product. Then

`α ^ n = (∏ⱼ λⱼ[α]) ω ^ n`

(`TauCeti.AlmostComplexStructure.wedgePow_ofComplexModule`). This is the case `k = n` of the form
identity `α ^ k ∧ ω ^ (n - k) = (k! (n - k)! / n!) σ_k(λ[α]) ω ^ n`, and the pointwise form of the
complex Monge–Ampère operator: the top power of a (1,1)-form is its determinant relative to `ω`,
times `ω ^ n`.

Both sides are forms of top degree, so `α ^ n` is its value on the real frame
`(u₁, i u₁, …, uₙ, i uₙ)` of an orthonormal basis `u` times `ω ^ n / n!`
(`TauCeti.AlmostComplexStructure.eq_smul_kahlerPowerForm`). On the frame of an orthonormal
eigenbasis `u` of `H_α` (`LinearMap.IsSymm.relEigenvectorBasis`), the form `α` is diagonal:
`α(uⱼ, uₖ) = Im H_α(uⱼ, uₖ) = 0` and `α(uⱼ, i uₖ) = Re H_α(uⱼ, uₖ) = λⱼ δⱼₖ`. So `α ^ n` takes
the value `n! ∏ⱼ λⱼ` there
(`ContinuousAlternatingMap.wedgePow_apply_finProdFinEquiv_eq_mul_prod`).

## Main results

* `TauCeti.AlmostComplexStructure.wedgePow_apply_complexRealFrame_relEigenvectorBasis`: the value
  `n! ∏ⱼ λⱼ[α]` of `α ^ n` on the real frame of the eigenbasis.
* `TauCeti.AlmostComplexStructure.wedgePow_ofComplexModule`: `α ^ n = (∏ⱼ λⱼ[α]) ω ^ n`.

## References

* G. Székelyhidi, *Fully non-linear elliptic equations on compact Hermitian manifolds*,
  J. Differential Geom. 109 (2018), Section 2.
-/

public section

noncomputable section

open Module ContinuousAlternatingMap Complex

namespace TauCeti.AlmostComplexStructure

attribute [local instance] InnerProductSpace.complexToReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {α : E [⋀^Fin 2]→L[ℝ] ℝ} (hα : ∀ u v : E, α ![I • u, I • v] = α ![u, v])
include hα

/-- On the real frame `(u₁, i u₁, …, uₙ, i uₙ)` of the eigenbasis `u` of `H_α`, the `n`-th wedge
power of a (1,1)-form `α` takes the value `n! ∏ⱼ λⱼ[α]`. -/
theorem wedgePow_apply_complexRealFrame_relEigenvectorBasis {n : ℕ} (hn : finrank ℂ E = n) :
    α.wedgePow n ((ofComplexModule E).complexRealFrame
        ((isSymm_hermitianSesqForm hα).relEigenvectorBasis hn)) =
      n.factorial * ∏ j, (isSymm_hermitianSesqForm hα).relEigenvalues hn j := by
  set u := (isSymm_hermitianSesqForm hα).relEigenvectorBasis hn
  have hH (i j : Fin n) : α.hermitianForm (u i) (u j) =
      if i = j then ((isSymm_hermitianSesqForm hα).relEigenvalues hn i : ℂ) else 0 := by
    rw [← hermitianSesqForm_apply hα]
    exact (isSymm_hermitianSesqForm hα).apply_relEigenvectorBasis hn i j
  rw [complexRealFrame_def]
  refine wedgePow_apply_finProdFinEquiv_eq_mul_prod α
    (fun p : Fin n × Fin 2 ↦ ![u p.1, ofComplexModule E (u p.1)] p.2)
    ((isSymm_hermitianSesqForm hα).relEigenvalues hn) (fun i j ↦ ?_) (fun i j ↦ ?_)
  · simpa [← im_hermitianForm, apply_ite] using congrArg Complex.im (hH i j)
  · simpa [ofComplexModule_apply, ← re_hermitianForm, apply_ite] using congrArg Complex.re (hH i j)

/-- **The top power of a (1,1)-form**: on a complex inner product space of dimension `n`, with
`ω` the Kähler form of multiplication by `i`, a real two-form `α` of type (1,1) satisfies
`α ^ n = (∏ⱼ λⱼ[α]) ω ^ n`, where `λ[α]` are the eigenvalues of the Hermitian form `H_α`
relative to the inner product. -/
theorem wedgePow_ofComplexModule {n : ℕ} (hn : finrank ℂ E = n) :
    α.wedgePow n = (∏ j, (isSymm_hermitianSesqForm hα).relEigenvalues hn j) •
      (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow n := by
  set u := (isSymm_hermitianSesqForm hα).relEigenvectorBasis hn
  have huR : Orthonormal ℝ (u : Fin n → E) := u.orthonormal.real
  have hJu (i j : Fin n) : inner ℝ ((ofComplexModule E) (u i)) (u j) = 0 := by
    rw [ofComplexModule_apply]
    exact (huR.complex_iff_forall_real_inner_I_smul_eq_zero).1 u.orthonormal i j
  rw [eq_smul_kahlerPowerForm real_inner_ofComplexModule_ofComplexModule
      (by rw [finrank_real_of_complex, hn]) huR hJu (α.wedgePow n),
    wedgePow_apply_complexRealFrame_relEigenvectorBasis hα hn,
    kahlerPowerForm_def, smul_smul]
  congr 1
  field_simp

end TauCeti.AlmostComplexStructure
