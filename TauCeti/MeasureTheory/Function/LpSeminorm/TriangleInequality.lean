/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# `Lᵖ` bounds from a pointwise bound by two functions

If `‖f‖ ≤ A ‖g‖ + B ‖h‖` almost everywhere, then for `1 ≤ p` the Minkowski inequality gives
`‖f‖_{Lᵖ} ≤ A ‖g‖_{Lᵖ} + B ‖h‖_{Lᵖ}` (`TauCeti.eLpNorm_le_mul_add_mul_of_ae_norm_le`). This is the
`Lᵖ` step of a product rule estimate such as `‖ψ Du + Dψ ⊗ u‖_{Lᵖ}`, where only the pointwise
bound depends on the product. For `0 ≤ c`, scaling the norm of `f` by `c` scales its `Lᵖ` norm:
`‖c |f|‖_{Lᵖ} = c ‖f‖_{Lᵖ}` (`TauCeti.eLpNorm_const_mul_norm`), so for `0 ≤ R, c` the Minkowski
inequality gives `‖R |f| + c |g|‖_{Lᵖ} ≤ R ‖f‖_{Lᵖ} + c ‖g‖_{Lᵖ}`
(`TauCeti.eLpNorm_mul_norm_add_mul_norm_le`).

If `f` differs from `g` by at most `M` on a measurable set `s` and `‖g‖_{Lᵖ(s)} ≤ B`, the same
inequality gives `‖f‖_{Lᵖ(s)} ≤ μ(s)^(1/p) M + B` (`TauCeti.eLpNorm_restrict_le_of_norm_sub_le`).
This bounds a function in `Lᵖ` when it equals an `Lᵖ`-bounded function up to bounded
zeroth-order terms.
-/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace TauCeti

variable {α E F G : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedAddCommGroup G] {p : ℝ≥0∞}

/-- If `‖f‖ ≤ A ‖g‖ + B ‖h‖` almost everywhere, then for `1 ≤ p`,
`‖f‖_{Lᵖ} ≤ A ‖g‖_{Lᵖ} + B ‖h‖_{Lᵖ}`. -/
theorem eLpNorm_le_mul_add_mul_of_ae_norm_le (hp : 1 ≤ p) {f : α → E} {g : α → F} {h : α → G}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hh : AEStronglyMeasurable h μ) {A B : ℝ≥0}
    (hfgh : ∀ᵐ x ∂μ, ‖f x‖ ≤ A * ‖g x‖ + B * ‖h x‖) :
    eLpNorm f p μ ≤ A * eLpNorm g p μ + B * eLpNorm h p μ := by
  calc eLpNorm f p μ ≤ eLpNorm ((A : ℝ) • (fun x ↦ ‖g x‖) + (B : ℝ) • fun x ↦ ‖h x‖) p μ :=
        eLpNorm_mono_ae_real hf hfgh
    _ ≤ eLpNorm ((A : ℝ) • fun x ↦ ‖g x‖) p μ + eLpNorm ((B : ℝ) • fun x ↦ ‖h x‖) p μ :=
        eLpNorm_add_le hp
    _ = A * eLpNorm g p μ + B * eLpNorm h p μ := by
        rw [eLpNorm_const_smul, eLpNorm_const_smul, eLpNorm_norm _ hg, eLpNorm_norm _ hh]
        simp

/-- **Scaling the norm of a function.** For `0 ≤ c`, the `Lᵖ` norm of `x ↦ c ‖f x‖` is
`c ‖f‖_{Lᵖ}`. -/
theorem eLpNorm_const_mul_norm {c : ℝ} (hc : 0 ≤ c) {f : α → E}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x ↦ c * ‖f x‖) p μ = ENNReal.ofReal c * eLpNorm f p μ := by
  have hcf : (fun x ↦ c * ‖f x‖) = c • fun x ↦ ‖f x‖ := funext fun _ ↦ (smul_eq_mul _ _).symm
  rw [hcf, eLpNorm_const_smul, eLpNorm_norm f hf, Real.eNorm_of_nonneg hc]

/-- For `1 ≤ p` and `0 ≤ R, c`, the `Lᵖ` norm of `x ↦ R ‖f x‖ + c ‖g x‖` is at most
`R ‖f‖_{Lᵖ} + c ‖g‖_{Lᵖ}`. -/
theorem eLpNorm_mul_norm_add_mul_norm_le (hp : 1 ≤ p) {R c : ℝ} (hR : 0 ≤ R) (hc : 0 ≤ c)
    {f : α → E} {g : α → F} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun x ↦ R * ‖f x‖ + c * ‖g x‖) p μ ≤
      ENNReal.ofReal R * eLpNorm f p μ + ENNReal.ofReal c * eLpNorm g p μ := by
  refine (eLpNorm_add_le hp).trans_eq ?_
  rw [eLpNorm_const_mul_norm hR hf, eLpNorm_const_mul_norm hc hg]

/-- **`Lᵖ` bounds up to a bounded error.** Let `1 ≤ p` and let `s` be measurable. If
`‖f - g‖ ≤ M` on `s` and `‖g‖_{Lᵖ(s)} ≤ B`, then `‖f‖_{Lᵖ(s)} ≤ μ(s)^(1/p) M + B`. -/
theorem eLpNorm_restrict_le_of_norm_sub_le (hp : 1 ≤ p) {s : Set α} (hs : MeasurableSet s)
    {f g : α → E} (hf : AEStronglyMeasurable f (μ.restrict s)) {M : ℝ} {B : ℝ≥0}
    (hM : ∀ x ∈ s, ‖f x - g x‖ ≤ M) (hB : eLpNorm g p (μ.restrict s) ≤ B) :
    eLpNorm f p (μ.restrict s) ≤ μ s ^ p.toReal⁻¹ * ENNReal.ofReal M + B := by
  have hg : AEStronglyMeasurable g (μ.restrict s) :=
    aestronglyMeasurable_of_eLpNorm_ne_top (hB.trans_lt ENNReal.coe_lt_top).ne
  -- Split `f` as the bounded `f - g` plus `g`.
  calc eLpNorm f p (μ.restrict s) = eLpNorm ((f - g) + g) p (μ.restrict s) := by
        rw [sub_add_cancel]
    _ ≤ eLpNorm (f - g) p (μ.restrict s) + eLpNorm g p (μ.restrict s) := eLpNorm_add_le hp
    _ ≤ μ s ^ p.toReal⁻¹ * ENNReal.ofReal M + B := by
      refine add_le_add ((eLpNorm_le_of_ae_bound (hf.sub hg) ((ae_restrict_iff' hs).2
        (Eventually.of_forall hM))).trans_eq ?_) hB
      rw [Measure.restrict_apply_univ]

end TauCeti
