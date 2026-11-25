/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.Action.Koopman
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Checks: the Koopman group

Checks for the Koopman group `U_t f = f ∘ (t +ᵥ ·)` (`TauCeti.koopmanGroup`) of §12.3 of the
MathematicalBilliards roadmap.

* **The identity action.** If every `t` acts as the identity, then `U_t = 1` for every `t`
  (`koopmanGroup_eq_one_of_forall_vadd_eq`).
* **Translation on `AddCircle 1`.** Let `ℝ` act on `AddCircle 1` by `t +ᵥ x = t + x`, preserving
  the normalised Haar measure. For the mode `e_n(x) = exp(2πinx)` (`fourierLp 2 n`),
  `U_t e_n = exp(2πint) e_n` (`koopmanGroup_fourierLp`), continuous in `t`.
-/

public section

noncomputable section

open MeasureTheory Complex
open scoped Real ENNReal

namespace TauCeti.Examples.KoopmanChecks

section Identity

variable {X : Type*} [MeasurableSpace X] [AddAction ℝ X] [MeasurableVAdd₂ ℝ X]
  {μ : Measure X} [SFinite μ] [VAddInvariantMeasure ℝ X μ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The identity action** gives the identity Koopman group: if every `t` acts as the identity,
then `U_t = 1`. -/
theorem koopmanGroup_eq_one_of_forall_vadd_eq (hp : p ≠ ∞) (h : ∀ (t : ℝ) (x : X), t +ᵥ x = x)
    (t : ℝ) : koopmanGroup μ E p hp t = 1 := by
  ext f : 1
  rw [koopmanGroup_apply]
  change _ = f
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_vadd t μ)] with x hx
  rw [hx, Function.comp_apply, h]

end Identity

section Circle

/-- The translation action of `ℝ` on `AddCircle 1`, `t +ᵥ x = t + x`. -/
instance instAddActionRealAddCircleOne : AddAction ℝ (AddCircle (1 : ℝ)) :=
  AddAction.compHom _ (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))

theorem vadd_def (t : ℝ) (x : AddCircle (1 : ℝ)) : t +ᵥ x = (t : AddCircle (1 : ℝ)) + x :=
  (rfl)

/-- The translation action of `ℝ` on `AddCircle 1` is jointly measurable. -/
instance instMeasurableVAdd₂RealAddCircleOne : MeasurableVAdd₂ ℝ (AddCircle (1 : ℝ)) :=
  ⟨by
    change Measurable fun p : ℝ × AddCircle (1 : ℝ) => (p.1 : AddCircle (1 : ℝ)) + p.2
    exact (((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_fst).add
      continuous_snd).measurable⟩

/-- The translation action of `ℝ` on `AddCircle 1` preserves the normalised Haar measure. -/
instance instVAddInvariantMeasureRealHaarAddCircle :
    VAddInvariantMeasure ℝ (AddCircle (1 : ℝ)) (AddCircle.haarAddCircle (T := 1)) :=
  ⟨fun t s _ => by simp only [vadd_def]; exact measure_preimage_add _ _ _⟩

/-- **The modes are eigenvectors.** For the translation flow on `AddCircle 1`,
`U_t e_n = exp(2πint) e_n`, where `e_n(x) = exp(2πinx)`. -/
theorem koopmanGroup_fourierLp (n : ℤ) (t : ℝ) :
    koopmanGroup (AddCircle.haarAddCircle (T := 1)) ℂ 2 ENNReal.ofNat_ne_top t (fourierLp 2 n) =
      exp (2 * π * I * n * t) • fourierLp 2 n := by
  rw [koopmanGroup_apply]
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_compMeasurePreserving (fourierLp 2 n)
      (measurePreserving_vadd t (AddCircle.haarAddCircle (T := 1))),
    (measurePreserving_vadd t (AddCircle.haarAddCircle (T := 1))).quasiMeasurePreserving.ae_eq_comp
      (coeFn_fourierLp 2 n),
    Lp.coeFn_smul (exp (2 * π * I * n * t)) (fourierLp 2 n), coeFn_fourierLp 2 n]
    with x h1 h2 h3 h4
  rw [h1, h2, h3, Pi.smul_apply, h4, Function.comp_apply, vadd_def, smul_eq_mul]
  rw [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul, ← fourier_apply,
    fourier_coe_apply, ofReal_one, div_one, ← fourier_apply]

/-- The orbit `t ↦ U_t e_n` is continuous. -/
example (n : ℤ) : Continuous fun t : ℝ =>
    koopmanGroup (AddCircle.haarAddCircle (T := 1)) ℂ 2 ENNReal.ofNat_ne_top t (fourierLp 2 n) := by
  simp_rw [koopmanGroup_fourierLp]
  fun_prop

end Circle

end TauCeti.Examples.KoopmanChecks
