/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Holder.Gain
public import TauCeti.Analysis.Complex.Wirtinger.Holder

/-!
# Hölder bounds for the complex derivative of the Cauchy transform

The complex-linear derivative `∂T` of the actual normalized Cauchy integral has a fixed-disc
Hölder and supremum bound depending only on the source Hölder norm. This is the derivative
form of the Beurling estimate; identifying it with the principal-value kernel is a separate
singular-integral statement.
-/

public noncomputable section

open Complex Metric MeasureTheory
open scoped NNReal ContDiff

namespace TauCeti

/-- The complex-linear derivative of the actual Cauchy transform is bounded in `C^{0,α}` on
each fixed output disc, while its conjugate Wirtinger derivative is the original source. -/
theorem exists_holderOnWith_wirtingerDeriv_pi_inv_smul_integral_sub_inv_smul
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) (c : ℂ) {r R : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R) :
    ∃ C : ℝ≥0, ∀ {f : ℂ → ℂ} {H M : ℝ≥0},
      Function.support f ⊆ closedBall c r → HolderWith H α f → (∀ x, ‖f x‖ ≤ M) →
      let T : ℂ → ℂ := fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z
      HolderOnWith (C * (H + M)) α (fun x ↦ wirtingerDeriv T x 1) (closedBall c R) ∧
        (∀ x ∈ closedBall c R, ‖wirtingerDeriv T x 1‖ ≤ C * (H + M)) ∧
        ∀ x ∈ ball c (R + 1), conjWirtingerDeriv T x 1 = f x := by
  obtain ⟨C, hC⟩ :=
    exists_contDiffOn_holderOnWith_fderiv_pi_inv_smul_integral_sub_inv_smul hα hα1 c hr hR
  refine ⟨C, fun {f H M} hs hf hM ↦ ?_⟩
  obtain ⟨-, hH, hN, hI⟩ := hC hs hf hM
  refine ⟨by simpa only [nnnorm_one, mul_one] using hH.wirtingerDeriv_apply 1, ?_, hI⟩
  intro x hx
  have h := norm_wirtingerDeriv_apply_le
    (fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z) x 1
  simp only [norm_one, mul_one] at h
  exact h.trans (hN x hx)

end TauCeti
