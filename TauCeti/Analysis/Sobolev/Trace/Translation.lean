/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Continuous
public import TauCeti.Analysis.Sobolev.W1p.Translation
public import TauCeti.MeasureTheory.Function.Lp.Translation

/-!
# Flat traces commute with tangential translations

Translating a whole-space Sobolev function `w ∈ W^{1,p}(ℝ × E)` parallel to the hyperplane
`{a} × E`, by a vector `(0, b)`, translates its trace on that hyperplane by `b`:

`Tr (x ↦ w (x + (0, b))) = (y ↦ Tr w (y + b))`

(`TauCeti.W1p.hyperplaneTrace_translate`). Both sides are bounded linear in `w`, and on test
functions both are the classical restriction `y ↦ φ (a, y + b)`, so they agree by density.

Tangential translation is how a boundary condition imposed on part of the hyperplane is moved off
the edge of that part: a function whose trace vanishes on `{y | ℓ y < c}` is translated to one
whose trace vanishes on the larger region `{y | ℓ y < c + τ}`.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The flat trace commutes with tangential translation.** For `1 ≤ p < ∞`, the trace on
`{a} × E` of the translate `x ↦ w (x + (0, b))` of `w ∈ W^{1,p}(ℝ × E)` is the translate
`y ↦ Tr w (y + b)` of the trace of `w`. -/
theorem W1p.hyperplaneTrace_translate (hp : p ≠ ∞) (a : ℝ) (b : E)
    (w : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p) :
    W1p.hyperplaneTrace hp a
        (W1p.translate (Omega := ⊤) (V := ⊤) (h := WithLp.toLp 2 (0, b)) (fun _ _ => by simp)
          w) =
      Measure.translateLp volume p b (W1p.hyperplaneTrace hp a w) := by
  have hVO : MapsTo (· + WithLp.toLp 2 ((0 : ℝ), b)) (⊤ : Opens (WithLp 2 (ℝ × E))) ⊤ :=
    fun _ _ => by simp
  -- Both sides are continuous linear in `w`; they agree on the dense test functions.
  have key : ((W1p.hyperplaneTrace hp a).comp (W1p.translateL hVO) :
        W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p → Lp ℝ p (volume : Measure E)) =
      ((Measure.translateLp volume p b :
          Lp ℝ p (volume : Measure E) ≃ₗᵢ[ℝ] _).toContinuousLinearEquiv :
        Lp ℝ p (volume : Measure E) →L[ℝ] _).comp (W1p.hyperplaneTrace hp a) := by
    refine (W1p.denseRange_ofTestFunctionₗ_top hp).equalizer (ContinuousLinearMap.continuous _)
      (ContinuousLinearMap.continuous _) (funext fun φ => Lp.ext ?_)
    have hmp := (measurePreserving_add_right (volume : Measure E) b).quasiMeasurePreserving
    have hval : W1p.value (W1p.translate hVO (W1p.ofTestFunctionₗ volume ⊤ p φ)) =ᵐ[volume]
        fun x => φ (x + WithLp.toLp 2 (0, b)) := by
      have h := W1p.value_translate_ae hVO (W1p.ofTestFunctionₗ volume ⊤ p φ)
      simp only [Opens.coe_top, Measure.restrict_univ] at h
      exact h.trans ((measurePreserving_add_right volume _).quasiMeasurePreserving.ae_eq_comp
        (W1p.value_ofTestFunctionₗ_top_ae φ))
    filter_upwards [W1p.hyperplaneTrace_apply_ae_of_continuous hp a
        (by fun_prop : Continuous fun x => φ (x + WithLp.toLp 2 (0, b))) hval,
      Measure.coeFn_translateLp (mu := (volume : Measure E)) (p := p) b
        (W1p.hyperplaneTrace hp a (W1p.ofTestFunctionₗ volume ⊤ p φ)),
      hmp.ae (W1p.hyperplaneTrace_ofTestFunction_apply_ae hp a φ)] with y h₁ h₂ h₃
    simp only [Function.comp_apply, ContinuousLinearMap.coe_comp, W1p.translateL_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv] at h₁ ⊢
    rw [h₁, h₂, Function.comp_apply, h₃, ← WithLp.toLp_add, Prod.mk_add_mk, add_zero]
  simpa only [Function.comp_apply, ContinuousLinearMap.coe_comp, W1p.translateL_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
    congrFun key w

end TauCeti
