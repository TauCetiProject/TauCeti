/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.SpaceTime.Holder
public import TauCeti.Analysis.Holder.Algebra
import TauCeti.Analysis.Normed.Operator.Holder

/-!
# Market coefficient fields on parabolic Hölder slabs

This module constructs the parabolic Hölder coefficient fields on `slab (E := ℝ) t₀ t₁` from
market volatility `σ(s, t)` and a time-only `(α / 2)`-Hölder short rate `r(t)`:

* `TauCeti.Finance.logSpotHalfVarianceHolder` constructs the log-spot half-variance field
  `a(y, t) = σ(e^y, t)² / 2` in `HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ`, with quantitative norm
  bound `TauCeti.Finance.norm_logSpotHalfVarianceHolder_le`.
* `TauCeti.Finance.shortRateHolder` promotes `r(t)` via `HolderSpace.compSlabTimeL` to a
  space-independent parabolic `α`-Hölder field on `slab (E := ℝ) t₀ t₁`, with quantitative norm
  bound `TauCeti.Finance.norm_shortRateHolder_le`.

This module depends only on parabolic space-time Hölder spaces and normed Hölder algebras, without
importing parabolic PDE solvers or existence theory.
-/

public section
noncomputable section

namespace TauCeti.Finance

open Set Real ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

variable {α : ℝ≥0} {t₀ t₁ : ℝ}

/-- The log-spot half-variance field `a(y, t) = σ(e^y, t)² / 2` as an element of
`HolderSpace α (slab t₀ t₁) ℝ`, built from a bounded parabolically `α`-Hölder volatility
(`0 < α`). -/
def logSpotHalfVarianceHolder (hα₀ : 0 < α) (σ : ℝ → ℝ → ℝ) {M : ℝ}
    (hbdd : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    (hσ : MemHolder α (fun p : slab (E := ℝ) t₀ t₁ ↦
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p))) :
    HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ :=
  let f : slab (E := ℝ) t₀ t₁ → ℝ := fun p ↦
    σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p)
  let σB : slab (E := ℝ) t₀ t₁ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup f
    (hσ.holderWith.continuous hα₀) M fun p ↦ by
      simpa only [f, Real.norm_eq_abs] using hbdd _ _ (slabTime p).property
  have hcoe : (σB : slab (E := ℝ) t₀ t₁ → ℝ) = f :=
    BoundedContinuousFunction.coe_ofNormedAddCommGroup _ _ _ _
  (2⁻¹ : ℝ) • (HolderSpace.ofBoundedContinuousFunction σB (hcoe.symm ▸ hσ)) ^ 2

/-- Evaluation of `logSpotHalfVarianceHolder` at a slab point gives `σ(e^y, t)² / 2`. -/
@[simp]
theorem logSpotHalfVarianceHolder_apply (hα₀ : 0 < α) (σ : ℝ → ℝ → ℝ) {M : ℝ}
    (hbdd : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    (hσ : MemHolder α (fun p : slab (E := ℝ) t₀ t₁ ↦
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p)))
    (p : slab (E := ℝ) t₀ t₁) :
    logSpotHalfVarianceHolder hα₀ σ hbdd hσ p =
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p) ^ 2 / 2 := by
  rw [logSpotHalfVarianceHolder, HolderSpace.smul_apply, HolderSpace.pow_apply,
    HolderSpace.ofBoundedContinuousFunction_apply]
  have hcoe : ∀ q : slab (E := ℝ) t₀ t₁,
      BoundedContinuousFunction.ofNormedAddCommGroup
        (fun p : slab (E := ℝ) t₀ t₁ ↦ σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p))
        (hσ.holderWith.continuous hα₀) M
        (fun p ↦ by simpa only [Real.norm_eq_abs] using hbdd _ _ (slabTime p).property) q =
      σ (exp (q : ParabolicSpaceTime ℝ).space) (slabTime q) :=
    congrFun (BoundedContinuousFunction.coe_ofNormedAddCommGroup _ _ _ _)
  rw [hcoe, smul_eq_mul]
  ring

/-- Norm bound for `logSpotHalfVarianceHolder`: if `|σ(e^y, t)| ≤ M` (`0 ≤ M`) and
`(y, t) ↦ σ(e^y, t)` is parabolically `α`-Hölder with constant `H`, then the log-spot half-variance
field `a = σ² / 2` has Hölder-space norm at most `M ^ 2 / 2 + M * H`. -/
theorem norm_logSpotHalfVarianceHolder_le (hα₀ : 0 < α) (σ : ℝ → ℝ → ℝ) {M : ℝ}
    (hM0 : 0 ≤ M) (hbdd : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    {H : ℝ≥0} (hσH : HolderWith H α (fun p : slab (E := ℝ) t₀ t₁ ↦
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p))) :
    ‖logSpotHalfVarianceHolder hα₀ σ hbdd hσH.memHolder‖ ≤ M ^ 2 / 2 + M * H := by
  let f : slab (E := ℝ) t₀ t₁ → ℝ := fun p ↦
    σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p)
  have hpoint : ∀ p : slab (E := ℝ) t₀ t₁,
      ‖logSpotHalfVarianceHolder hα₀ σ hbdd hσH.memHolder p‖ ≤ M ^ 2 / 2 := fun p ↦ by
    rw [logSpotHalfVarianceHolder_apply, Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_pos (two_pos : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg _) (hbdd _ _ (slabTime p).property) 2) zero_le_two
  have hmul : HolderWith (‖ContinuousLinearMap.mul ℝ ℝ‖₊ * (M.toNNReal * H + M.toNNReal * H)) α
      (fun p ↦ f p * f p) :=
    (ContinuousLinearMap.mul ℝ ℝ).holderWith_comp₂ hσH hσH
      (fun p ↦ by
        simpa only [f, Real.norm_eq_abs, Real.coe_toNNReal _ hM0] using
          hbdd _ _ (slabTime p).property)
      (fun p ↦ by
        simpa only [f, Real.norm_eq_abs, Real.coe_toNNReal _ hM0] using
          hbdd _ _ (slabTime p).property)
  have hsmul : HolderWith (M.toNNReal * H) α (fun p ↦ (2⁻¹ : ℝ) • (f p * f p)) := by
    refine (hmul.smul (2⁻¹ : ℝ)).mono ?_
    have hB : ‖ContinuousLinearMap.mul ℝ ℝ‖₊ ≤ 1 := by
      exact_mod_cast ContinuousLinearMap.opNorm_mul_le ℝ ℝ
    have hhalf : ‖(2⁻¹ : ℝ)‖₊ = 2⁻¹ := by
      rw [← NNReal.coe_inj, coe_nnNorm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      norm_num
    rw [hhalf]
    calc ‖ContinuousLinearMap.mul ℝ ℝ‖₊ * (M.toNNReal * H + M.toNNReal * H) * 2⁻¹
        ≤ 1 * (M.toNNReal * H + M.toNNReal * H) * 2⁻¹ := by gcongr
      _ = M.toNNReal * H := by ring
  have hhold : HolderWith (M.toNNReal * H) α
      (logSpotHalfVarianceHolder hα₀ σ hbdd hσH.memHolder) := by
    have hfun : (⇑(logSpotHalfVarianceHolder hα₀ σ hbdd hσH.memHolder)) =
        fun p ↦ (2⁻¹ : ℝ) • (f p * f p) :=
      funext fun p ↦ by rw [logSpotHalfVarianceHolder_apply, smul_eq_mul]; ring
    simpa only [hfun] using hsmul
  simpa only [NNReal.coe_mul, Real.coe_toNNReal _ hM0] using
    HolderSpace.norm_le_of_norm_le_of_holderWith (by positivity) hpoint hhold

/-- A time-only short rate `r : ℝ → ℝ` that is `(α / 2)`-Hölder on `[t₀, t₁]` (`0 < α`), promoted
via `HolderSpace.compSlabTimeL` to a space-independent parabolic `α`-Hölder field on
`slab (E := ℝ) t₀ t₁`. -/
def shortRateHolder (hα₀ : 0 < α) (r : ℝ → ℝ) {H : ℝ≥0}
    (hr : HolderOnWith H (α / 2) r (Icc t₀ t₁)) :
    HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ :=
  HolderSpace.compSlabTimeL
    (HolderSpace.ofHolderWithOfCompact (div_pos hα₀ two_pos) (fun t : Icc t₀ t₁ ↦ r t)
      fun t s ↦ by simpa only [Subtype.edist_eq] using hr t t.property s s.property)

/-- Evaluation of `shortRateHolder` at a slab point gives `r` at its time coordinate. -/
@[simp]
theorem shortRateHolder_apply (hα₀ : 0 < α) (r : ℝ → ℝ) {H : ℝ≥0}
    (hr : HolderOnWith H (α / 2) r (Icc t₀ t₁)) (p : slab (E := ℝ) t₀ t₁) :
    shortRateHolder hα₀ r hr p = r (slabTime p) := by
  rw [shortRateHolder, HolderSpace.compSlabTimeL_apply]
  exact HolderSpace.ofHolderWithOfCompact_apply (div_pos hα₀ two_pos) (fun t : Icc t₀ t₁ ↦ r t) _
    (slabTime p)

/-- Norm bound for `shortRateHolder`: if `|r(t)| ≤ M` (`0 ≤ M`) and `r` is `H`-Hölder of exponent
`α / 2` on `[t₀, t₁]`, then `shortRateHolder` has Hölder-space norm at most `M + H`. -/
theorem norm_shortRateHolder_le (hα₀ : 0 < α) (r : ℝ → ℝ) {M : ℝ} (hM0 : 0 ≤ M)
    (hbdd : ∀ t ∈ Icc t₀ t₁, |r t| ≤ M) {H : ℝ≥0} (hr : HolderOnWith H (α / 2) r (Icc t₀ t₁)) :
    ‖shortRateHolder hα₀ r hr‖ ≤ M + H := by
  let g : HolderSpace (α / 2) (Icc t₀ t₁) ℝ :=
    HolderSpace.ofHolderWithOfCompact (div_pos hα₀ two_pos) (fun t : Icc t₀ t₁ ↦ r t)
      fun t s ↦ by simpa only [Subtype.edist_eq] using hr t t.property s s.property
  have hg : ∀ t : Icc t₀ t₁, g t = r t := fun t ↦
    HolderSpace.ofHolderWithOfCompact_apply (div_pos hα₀ two_pos) (fun t : Icc t₀ t₁ ↦ r t) _ t
  refine (HolderSpace.norm_compSlabTimeL_apply_le g).trans
    (HolderSpace.norm_le_of_norm_le_of_holderWith hM0 (fun t ↦ ?_) (fun t s ↦ ?_))
  · change ‖g t‖ ≤ M
    rw [hg, Real.norm_eq_abs]
    exact hbdd t.val t.property
  · change edist (g t) (g s) ≤ _
    rw [hg, hg]
    simpa only [Subtype.edist_eq] using hr t t.property s s.property

end TauCeti.Finance
