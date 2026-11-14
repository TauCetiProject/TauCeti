/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Pointwise bounds for the real-valued `Lᵖ` norm

A pointwise bound `‖f x‖ ≤ c ‖g x‖` almost everywhere bounds the real-valued `Lᵖ` norm:
`lpNorm f p μ ≤ c * lpNorm g p μ` (`MeasureTheory.lpNorm_le_mul_lpNorm_of_ae_le_mul`). This is
the `lpNorm` form of Mathlib's `MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul`. Since
`lpNorm` is `0` off `Lᵖ`, the hypothesis `g ∈ Lᵖ(μ)` is needed. It is the estimate for
multiplication by a bounded measurable coefficient, as for the lower-order terms of a
differential operator.

In particular, scalar multiplication by a function bounded by `c` multiplies the `Lᵖ` norm by at
most `c` (`MeasureTheory.lpNorm_smul_le_mul_lpNorm_of_ae_le`). For `1 ≤ p`, the lower-order terms
`⟪b, G⟫ + c V` of a second-order operator over `ℝ` or `ℂ`, with `‖b‖ ≤ β` and `‖c‖ ≤ γ`, lie in
`Lᵖ` with norm at most `β ‖G‖ + γ ‖V‖` (`MeasureTheory.memLp_inner_add_mul_and_lpNorm_le`), so
they can be moved to the right-hand side of an equation
(`MeasureTheory.Lp.exists_ae_eq_norm_le_of_add_inner_add_mul_ae_eq`).
-/

public section

open scoped ENNReal InnerProductSpace

namespace MeasureTheory

variable {α F G : Type*} {m : MeasurableSpace α} [NormedAddCommGroup F] [NormedAddCommGroup G]
  {p : ℝ≥0∞} {μ : Measure α}

/-- **A pointwise bound bounds `lpNorm`.** If `g ∈ Lᵖ(μ)` and `‖f x‖ ≤ c ‖g x‖` for almost every
`x`, then `lpNorm f p μ ≤ c * lpNorm g p μ`. -/
theorem lpNorm_le_mul_lpNorm_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : MemLp g p μ) (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) :
    lpNorm f p μ ≤ c * lpNorm g p μ := by
  rcases lt_or_ge c 0 with hc | hc
  · -- For `c < 0` the bound forces `f = 0` and `g = 0` almost everywhere.
    obtain ⟨hf0, hg0⟩ := eLpNorm_eq_zero_and_zero_of_ae_le_mul_neg h hc p
    rw [← toReal_eLpNorm, ← toReal_eLpNorm, hf0, hg0, ENNReal.toReal_zero, mul_zero]
  rw [← toReal_eLpNorm, ← toReal_eLpNorm, ← ENNReal.toReal_ofReal hc, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.eLpNorm_ne_top)
    (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hf h p)

/-- **Multiplying by a bounded function.** If `f ∈ Lᵖ(μ)` and `‖ψ x‖ ≤ c` for almost every `x`,
then `lpNorm (ψ • f) p μ ≤ c * lpNorm f p μ`. -/
theorem lpNorm_smul_le_mul_lpNorm_of_ae_le {𝕜 : Type*} [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 F]
    [IsBoundedSMul 𝕜 F] {ψ : α → 𝕜} {f : α → F} {c : ℝ} (hf : MemLp f p μ)
    (h : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ c) : lpNorm (fun x => ψ x • f x) p μ ≤ c * lpNorm f p μ := by
  rcases lt_or_ge c 0 with hc | hc
  · -- For `c < 0` the bound `‖ψ x‖ ≤ c` forces `μ = 0`.
    obtain rfl : μ = 0 := ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1
      (h.mono fun x hx => (norm_nonneg (ψ x)).not_gt (hx.trans_lt hc)))
    simp
  by_cases hm : AEStronglyMeasurable (fun x => ψ x • f x) μ
  · exact lpNorm_le_mul_lpNorm_of_ae_le_mul hm hf (h.mono fun _ hx =>
      (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _)))
  rw [lpNorm_of_not_aestronglyMeasurable hm]
  exact mul_nonneg hc lpNorm_nonneg

/-- **The lower-order terms lie in `Lᵖ`.** For `1 ≤ p`, let `G ∈ Lᵖ(μ)` take values in an inner
product space over `𝕜 = ℝ` or `ℂ` and `V ∈ Lᵖ(μ)` be `𝕜`-valued, and let `b` and `c` be
measurable with `‖b‖ ≤ β` and `‖c‖ ≤ γ` almost everywhere. Then `⟪b, G⟫ + c V` lies in `Lᵖ(μ)`,
with `Lᵖ` norm at most `β ‖G‖ + γ ‖V‖`. -/
theorem memLp_inner_add_mul_and_lpNorm_le {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (hp : 1 ≤ p) {b G : α → E} {c V : α → 𝕜} {β γ : ℝ}
    (hb : AEStronglyMeasurable b μ) (hbβ : ∀ᵐ x ∂μ, ‖b x‖ ≤ β) (hc : AEStronglyMeasurable c μ)
    (hcγ : ∀ᵐ x ∂μ, ‖c x‖ ≤ γ) (hG : MemLp G p μ) (hV : MemLp V p μ) :
    MemLp (fun x => ⟪b x, G x⟫_𝕜 + c x * V x) p μ ∧
      lpNorm (fun x => ⟪b x, G x⟫_𝕜 + c x * V x) p μ ≤ β * lpNorm G p μ + γ * lpNorm V p μ := by
  have hdm : AEStronglyMeasurable (fun x => ⟪b x, G x⟫_𝕜) μ := hb.inner hG.aestronglyMeasurable
  have hdle : ∀ᵐ x ∂μ, ‖⟪b x, G x⟫_𝕜‖ ≤ β * ‖G x‖ := hbβ.mono fun x hx =>
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  have hzle : ∀ᵐ x ∂μ, ‖c x * V x‖ ≤ γ * ‖V x‖ := hcγ.mono fun x hx =>
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  have hd : MemLp (fun x => ⟪b x, G x⟫_𝕜) p μ := hG.of_le_mul hdm hdle
  refine ⟨hd.add (hV.of_le_mul (hc.mul hV.aestronglyMeasurable) hzle),
    (lpNorm_add_le hd hp).trans ?_⟩
  exact add_le_add (lpNorm_le_mul_lpNorm_of_ae_le_mul hdm hG hdle)
    (lpNorm_smul_le_mul_lpNorm_of_ae_le hV hcγ)

/-- **Moving the lower-order terms to the right-hand side.** For `1 ≤ p` and `𝕜 = ℝ` or `ℂ`, if
`P + ⟪b, G⟫ + c V = f` almost everywhere, where `f`, `G` and `V` lie in `Lᵖ(μ)` and `‖b‖ ≤ β`,
`‖c‖ ≤ γ` almost everywhere, then `P` agrees almost everywhere with some `g ∈ Lᵖ(μ)` with
`‖g‖ ≤ ‖f‖ + β ‖G‖ + γ ‖V‖`. -/
theorem Lp.exists_ae_eq_norm_le_of_add_inner_add_mul_ae_eq {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fact (1 ≤ p)] {P : α → 𝕜} {b : α → E}
    {c : α → 𝕜} {β γ : ℝ} (hb : AEStronglyMeasurable b μ) (hbβ : ∀ᵐ x ∂μ, ‖b x‖ ≤ β)
    (hc : AEStronglyMeasurable c μ) (hcγ : ∀ᵐ x ∂μ, ‖c x‖ ≤ γ) (G : Lp E p μ) (V : Lp 𝕜 p μ)
    (f : Lp 𝕜 p μ) (heq : ∀ᵐ x ∂μ, P x + ⟪b x, G x⟫_𝕜 + c x * V x = f x) :
    ∃ g : Lp 𝕜 p μ, P =ᵐ[μ] g ∧ ‖g‖ ≤ ‖f‖ + β * ‖G‖ + γ * ‖V‖ := by
  obtain ⟨hL, hLle⟩ :=
    memLp_inner_add_mul_and_lpNorm_le Fact.out hb hbβ hc hcγ (Lp.memLp G) (Lp.memLp V)
  rw [← Lp.norm_eq_lpNorm_of_ae_eq hL.coeFn_toLp, ← Lp.norm_eq_lpNorm_of_ae_eq (f := G) .rfl,
    ← Lp.norm_eq_lpNorm_of_ae_eq (f := V) .rfl] at hLle
  refine ⟨f - hL.toLp _, ?_, by linarith [norm_sub_le f (hL.toLp _)]⟩
  filter_upwards [heq, Lp.coeFn_sub f (hL.toLp _), hL.coeFn_toLp] with x hx h1 h2
  rw [h1, Pi.sub_apply, h2, ← hx]
  ring

end MeasureTheory
