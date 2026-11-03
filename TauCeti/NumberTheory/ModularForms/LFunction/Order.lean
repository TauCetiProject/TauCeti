/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LFunction.FunctionalEquation

/-!
# Vanishing orders of completed L-functions

On the positive real half-plane the gamma factor is holomorphic and nonzero, so the
entire L-function of a cusp form and both its completions have the same vanishing order.
In particular their orders agree at the central point of a positive-weight form. This
allows functional equations of the completed L-function to control the analytic rank
of the ordinary L-function.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §5.10.
-/

public section

open Filter Topology Matrix

namespace CuspForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}

/-- Removing the gamma factor does not change the order on `Re s > 0`. The order refers
to the entire continuation `ModularForm.L`, not to the coefficient Dirichlet series. -/
theorem analyticOrderAt_L_eq_Λ (f : CuspForm Γ k) (hk : 0 < k) {s : ℂ}
    (hs : 0 < s.re) :
    analyticOrderAt (ModularForm.L hk f) s = analyticOrderAt (ModularForm.Λ hk f) s := by
  have hgamma : Complex.Gammaℂ s ≠ 0 := by
    rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one]
    exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hs)
      (Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using add_pos hs zero_lt_one))
  have heq : ModularForm.L hk f =ᶠ[𝓝 s]
      (ModularForm.Λ hk f * fun z ↦ 2 * (Complex.Gammaℂ z)⁻¹) := by
    filter_upwards [eventually_ne_nhds (Complex.ne_zero_of_re_pos hs)] with z hz
    simpa only [Pi.mul_apply, div_eq_mul_inv] using ModularForm.L_apply_of_ne_zero hk f hz
  have hfactor : AnalyticAt ℂ (fun z ↦ 2 * (Complex.Gammaℂ z)⁻¹) s :=
    (Complex.differentiable_Gammaℂ_inv.const_mul 2).analyticAt s
  rw [analyticOrderAt_congr heq,
    analyticOrderAt_mul ((differentiable_Λ hk f).analyticAt s) hfactor,
    hfactor.analyticOrderAt_eq_zero.mpr (mul_ne_zero two_ne_zero (inv_ne_zero hgamma)), add_zero]

/-- The level factor `N^(s/2)` and gamma factor do not change the order on `Re s > 0`. -/
theorem analyticOrderAt_frickeCompletedL_eq_L (f : CuspForm Γ k) (N : ℕ+)
    (hk : 0 < k) {s : ℂ} (hs : 0 < s.re) :
    analyticOrderAt (frickeCompletedL f N) s = analyticOrderAt (ModularForm.L hk f) s := by
  have hN : ((N : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr N.ne_zero
  have hfactor : Differentiable ℂ (fun z : ℂ ↦ ((N : ℕ) : ℂ) ^ (z / 2)) :=
    (differentiable_id.div_const 2).const_cpow (Or.inl hN)
  have hfactor0 : ((N : ℕ) : ℂ) ^ (s / 2) ≠ 0 :=
    fun h ↦ hN ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have heq : frickeCompletedL f N =
      (fun z : ℂ ↦ ((N : ℕ) : ℂ) ^ (z / 2)) * ModularForm.Λ hk f :=
    funext (frickeCompletedL_eq_cpow_mul_Λ f N hk)
  rw [heq, analyticOrderAt_mul (hfactor.analyticAt s) ((differentiable_Λ hk f).analyticAt s),
    (hfactor.analyticAt s).analyticOrderAt_eq_zero.mpr hfactor0, zero_add,
    analyticOrderAt_L_eq_Λ f hk hs]

end CuspForm
