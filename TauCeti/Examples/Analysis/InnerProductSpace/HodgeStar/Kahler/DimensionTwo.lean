/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.TopPower
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Trace
import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Mass

/-!
# Checks: the form identities in complex dimension two

On a complex inner product space `E` of dimension `2`, with `ω` the Kähler form of
multiplication by `i`, a real two-form `α` of type (1,1) with eigenvalues `λ[α] = (λ₁, λ₂)`
relative to the inner product satisfies

* `α ∧ ω = ((λ₁ + λ₂) / 2) ω²` (`wedge_wedgePow_one_eq`), the trace identity at `n = 2`;
* `α² = λ₁ λ₂ ω²` (`wedgePow_two_eq`), the top-power identity at `n = 2`.

For `α = ω` the Hermitian form is the inner product (`hermitianSesqForm_kahlerForm`), so
`λ[ω] = (1, 1)` (`relEigenvalues_kahlerForm`) and `σ₁ = 2` gives `ω ∧ ω = ω²`
(`wedge_wedgePow_one_kahlerForm`).
-/

public section

open Module ContinuousAlternatingMap Complex TauCeti.AlmostComplexStructure

namespace TauCeti.Examples.KahlerDimensionTwo

attribute [local instance] InnerProductSpace.complexToReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

section

variable {α : E [⋀^Fin 2]→L[ℝ] ℝ} (hα : ∀ u v : E, α ![I • u, I • v] = α ![u, v])
include hα

/-- In complex dimension two, `α ∧ ω = ((λ₁ + λ₂) / 2) ω²` for a (1,1)-form `α`. -/
theorem wedge_wedgePow_one_eq (hE : finrank ℂ E = 2) :
    wedge ((alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow 1) α =
      (((isSymm_hermitianSesqForm hα).relEigenvalues hE 0 +
          (isSymm_hermitianSesqForm hα).relEigenvalues hE 1) / 2) •
        (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow 2 := by
  have h := nsmul_wedge_wedgePow_ofComplexModule hα (m := 1) hE
  rw [Fin.sum_univ_two, ← Nat.cast_smul_eq_nsmul ℝ] at h
  rw [div_eq_inv_mul, mul_smul, ← h, smul_smul]
  norm_num

/-- In complex dimension two, `α² = λ₁ λ₂ ω²` for a (1,1)-form `α`. -/
theorem wedgePow_two_eq (hE : finrank ℂ E = 2) :
    α.wedgePow 2 =
      ((isSymm_hermitianSesqForm hα).relEigenvalues hE 0 *
          (isSymm_hermitianSesqForm hα).relEigenvalues hE 1) •
        (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow 2 := by
  rw [wedgePow_ofComplexModule hα hE, Fin.prod_univ_two]

end

/-- The Kähler form `ω(u, v) = Re ⟪i u, v⟫` is of type (1,1). -/
theorem kahlerForm_I_smul (u v : E) :
    alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm ![I • u, I • v] =
      alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm ![u, v] := by
  simp only [alternatingFormEquiv_kahlerForm_apply real_inner_ofComplexModule_ofComplexModule,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show I • v = ofComplexModule E v by simp [ofComplexModule_apply],
    show I • u = ofComplexModule E u by simp [ofComplexModule_apply],
    real_inner_ofComplexModule_ofComplexModule]

/-- The Hermitian form of the Kähler form is the inner product. -/
theorem hermitianSesqForm_kahlerForm :
    (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).hermitianSesqForm
      kahlerForm_I_smul = innerₛₗ ℂ := by
  ext u v
  simp only [hermitianSesqForm_apply, hermitianForm_def,
    alternatingFormEquiv_kahlerForm_apply real_inner_ofComplexModule_ofComplexModule,
    Matrix.cons_val_zero, Matrix.cons_val_one, ofComplexModule_apply, innerₛₗ_apply_apply,
    real_inner_eq_re_inner]
  apply Complex.ext <;> simp [inner_smul_left, inner_smul_right]

/-- The eigenvalues of the Kähler form relative to the inner product are all `1`. -/
theorem relEigenvalues_kahlerForm {n : ℕ} (hE : finrank ℂ E = n) :
    (isSymm_hermitianSesqForm kahlerForm_I_smul).relEigenvalues hE = 1 := by
  have key : ∀ (a : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) (h : a.IsSymm), a = innerₛₗ ℂ →
      h.relEigenvalues hE = 1 := by
    rintro a h rfl
    exact LinearMap.IsSymm.relEigenvalues_innerₛₗ h hE
  exact key _ _ hermitianSesqForm_kahlerForm

/-- In complex dimension two, `σ₁(λ[ω]) = 2` gives `ω ∧ ω = ω²`. -/
theorem wedge_wedgePow_one_kahlerForm (hE : finrank ℂ E = 2) :
    wedge ((alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow 1)
        (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm) =
      (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow 2 := by
  rw [wedge_wedgePow_one_eq kahlerForm_I_smul hE, relEigenvalues_kahlerForm]
  norm_num

end TauCeti.Examples.KahlerDimensionTwo
