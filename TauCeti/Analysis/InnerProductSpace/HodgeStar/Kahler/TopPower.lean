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

For `α = ω` the Hermitian form is the inner product
(`TauCeti.AlmostComplexStructure.hermitianSesqForm_alternatingFormEquiv_kahlerForm`), so every
eigenvalue of `ω` is `1`.

## Main results

* `TauCeti.AlmostComplexStructure.relEigenvalues_alternatingFormEquiv_kahlerForm`: `λ[ω] = 1`.
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

/-- The Kähler form `ω(u, v) = Re ⟪i u, v⟫` is of type (1,1). -/
theorem alternatingFormEquiv_kahlerForm_apply_I_smul (u v : E) :
    alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm ![I • u, I • v] =
      alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm ![u, v] := by
  simp only [alternatingFormEquiv_kahlerForm_apply real_inner_ofComplexModule_ofComplexModule,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show I • v = ofComplexModule E v by simp [ofComplexModule_apply],
    show I • u = ofComplexModule E u by simp [ofComplexModule_apply],
    real_inner_ofComplexModule_ofComplexModule]

/-- The Hermitian form of the Kähler form is the inner product. -/
@[simp]
theorem hermitianSesqForm_alternatingFormEquiv_kahlerForm :
    (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).hermitianSesqForm
      alternatingFormEquiv_kahlerForm_apply_I_smul = innerₛₗ ℂ := by
  ext u v
  simp only [hermitianSesqForm_apply, hermitianForm_def,
    alternatingFormEquiv_kahlerForm_apply real_inner_ofComplexModule_ofComplexModule,
    Matrix.cons_val_zero, Matrix.cons_val_one, ofComplexModule_apply, innerₛₗ_apply_apply,
    real_inner_eq_re_inner]
  apply Complex.ext <;> simp [inner_smul_left, inner_smul_right]

/-- The eigenvalues of the Kähler form relative to the inner product are all `1`. -/
@[simp]
theorem relEigenvalues_alternatingFormEquiv_kahlerForm {n : ℕ} (hn : finrank ℂ E = n) :
    (isSymm_hermitianSesqForm alternatingFormEquiv_kahlerForm_apply_I_smul).relEigenvalues hn =
      1 := by
  have key : ∀ (a : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) (h : a.IsSymm), a = innerₛₗ ℂ →
      h.relEigenvalues hn = 1 := by
    rintro a h rfl
    exact LinearMap.IsSymm.relEigenvalues_innerₛₗ h hn
  exact key _ _ hermitianSesqForm_alternatingFormEquiv_kahlerForm

section

variable {α : E [⋀^Fin 2]→L[ℝ] ℝ} (hα : ∀ u v : E, α ![I • u, I • v] = α ![u, v])
include hα

/-- On the real frame `(u₁, i u₁, …, uₙ, i uₙ)` of the eigenbasis `u` of `H_α`, the `n`-th wedge
power of a (1,1)-form `α` takes the value `n! ∏ⱼ λⱼ[α]`. -/
theorem wedgePow_apply_complexRealFrame_relEigenvectorBasis {n : ℕ} (hn : finrank ℂ E = n) :
    α.wedgePow n ((ofComplexModule E).complexRealFrame
        ((isSymm_hermitianSesqForm hα).relEigenvectorBasis hn)) =
      n.factorial * ∏ j, (isSymm_hermitianSesqForm hα).relEigenvalues hn j := by
  set u := (isSymm_hermitianSesqForm hα).relEigenvectorBasis hn
  rw [complexRealFrame_def]
  exact wedgePow_apply_finProdFinEquiv_eq_mul_prod α
    (fun p : Fin n × Fin 2 ↦ ![u p.1, ofComplexModule E (u p.1)] p.2)
    ((isSymm_hermitianSesqForm hα).relEigenvalues hn) (apply_relEigenvectorBasis_eq_zero hα hn)
    (apply_relEigenvectorBasis_ofComplexModule hα hn)

/-- **The top power of a (1,1)-form**: on a complex inner product space of dimension `n`, with
`ω` the Kähler form of multiplication by `i`, a real two-form `α` of type (1,1) satisfies
`α ^ n = (∏ⱼ λⱼ[α]) ω ^ n`, where `λ[α]` are the eigenvalues of the Hermitian form `H_α`
relative to the inner product. -/
theorem wedgePow_ofComplexModule {n : ℕ} (hn : finrank ℂ E = n) :
    α.wedgePow n = (∏ j, (isSymm_hermitianSesqForm hα).relEigenvalues hn j) •
      (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow n := by
  set u := (isSymm_hermitianSesqForm hα).relEigenvectorBasis hn
  rw [eq_smul_kahlerPowerForm real_inner_ofComplexModule_ofComplexModule
      (by rw [finrank_real_of_complex, hn]) u.orthonormal.real
      u.orthonormal.real_inner_ofComplexModule_eq_zero (α.wedgePow n),
    wedgePow_apply_complexRealFrame_relEigenvectorBasis hα hn,
    kahlerPowerForm_def, smul_smul]
  congr 1
  field_simp

end

end TauCeti.AlmostComplexStructure
