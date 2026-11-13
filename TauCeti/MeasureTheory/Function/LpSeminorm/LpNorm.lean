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

Multiplying by a function bounded by one does not increase the `Lᵖ` norm
(`MeasureTheory.lpNorm_mul_le_of_ae_norm_le_one`). For `1 ≤ p`, the lower-order terms
`⟪b, G⟫ + c V` of a second-order operator, with `‖b‖ ≤ β` and `|c| ≤ γ`, lie in `Lᵖ` with norm at
most `β ‖G‖ + γ ‖V‖` (`MeasureTheory.memLp_inner_add_mul_and_lpNorm_le`), so they can be moved to
the right-hand side of an equation
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

/-- **Multiplying by a function bounded by one.** If `f ∈ Lᵖ(μ)` and `‖ψ x‖ ≤ 1` for almost every
`x`, then `lpNorm (ψ * f) p μ ≤ lpNorm f p μ`. -/
theorem lpNorm_mul_le_of_ae_norm_le_one {R : Type*} [NormedRing R] {ψ f : α → R}
    (hψ : AEStronglyMeasurable ψ μ) (hf : MemLp f p μ) (h : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ 1) :
    lpNorm (fun x => ψ x * f x) p μ ≤ lpNorm f p μ := by
  simpa only [one_mul] using lpNorm_le_mul_lpNorm_of_ae_le_mul (f := fun x => ψ x * f x) (c := 1)
    (hψ.mul hf.aestronglyMeasurable) hf (h.mono fun x hx =>
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _)))

/-- **The lower-order terms lie in `Lᵖ`.** For `1 ≤ p`, let `G ∈ Lᵖ(μ)` take values in a real
inner product space and `V ∈ Lᵖ(μ)` be real, and let `b` and `c` be measurable with `‖b‖ ≤ β` and
`|c| ≤ γ` almost everywhere. Then `⟪b, G⟫ + c V` lies in `Lᵖ(μ)`, with `Lᵖ` norm at most
`β ‖G‖ + γ ‖V‖`. -/
theorem memLp_inner_add_mul_and_lpNorm_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (hp : 1 ≤ p) {b G : α → E} {c V : α → ℝ} {β γ : ℝ}
    (hb : AEStronglyMeasurable b μ) (hbβ : ∀ᵐ x ∂μ, ‖b x‖ ≤ β) (hc : AEStronglyMeasurable c μ)
    (hcγ : ∀ᵐ x ∂μ, |c x| ≤ γ) (hG : MemLp G p μ) (hV : MemLp V p μ) :
    MemLp (fun x => ⟪b x, G x⟫_ℝ + c x * V x) p μ ∧
      lpNorm (fun x => ⟪b x, G x⟫_ℝ + c x * V x) p μ ≤ β * lpNorm G p μ + γ * lpNorm V p μ := by
  have hdm : AEStronglyMeasurable (fun x => ⟪b x, G x⟫_ℝ) μ := hb.inner hG.aestronglyMeasurable
  have hzm : AEStronglyMeasurable (fun x => c x * V x) μ := hc.mul hV.aestronglyMeasurable
  have hdle : ∀ᵐ x ∂μ, ‖⟪b x, G x⟫_ℝ‖ ≤ β * ‖G x‖ := hbβ.mono fun x hx => by
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  have hzle : ∀ᵐ x ∂μ, ‖c x * V x‖ ≤ γ * ‖V x‖ := hcγ.mono fun x hx => by
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  have hd : MemLp (fun x => ⟪b x, G x⟫_ℝ) p μ := hG.of_le_mul hdm hdle
  refine ⟨hd.add (hV.of_le_mul hzm hzle), (lpNorm_add_le hd hp).trans ?_⟩
  exact add_le_add (lpNorm_le_mul_lpNorm_of_ae_le_mul hdm hG hdle)
    (lpNorm_le_mul_lpNorm_of_ae_le_mul hzm hV hzle)

/-- **Moving the lower-order terms to the right-hand side.** For `1 ≤ p`, if `P + ⟪b, G⟫ + c V = f`
almost everywhere, where `f`, `G` and `V` lie in `Lᵖ(μ)` and `‖b‖ ≤ β`, `|c| ≤ γ` almost everywhere,
then `P` agrees almost everywhere with some `g ∈ Lᵖ(μ)` with `‖g‖ ≤ ‖f‖ + β ‖G‖ + γ ‖V‖`. -/
theorem Lp.exists_ae_eq_norm_le_of_add_inner_add_mul_ae_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fact (1 ≤ p)] {P : α → ℝ} {b : α → E} {c : α → ℝ} {β γ : ℝ}
    (hb : AEStronglyMeasurable b μ) (hbβ : ∀ᵐ x ∂μ, ‖b x‖ ≤ β) (hc : AEStronglyMeasurable c μ)
    (hcγ : ∀ᵐ x ∂μ, |c x| ≤ γ) (G : Lp E p μ) (V : Lp ℝ p μ) (f : Lp ℝ p μ)
    (heq : ∀ᵐ x ∂μ, P x + ⟪b x, G x⟫_ℝ + c x * V x = f x) :
    ∃ g : Lp ℝ p μ, P =ᵐ[μ] g ∧ ‖g‖ ≤ ‖f‖ + β * ‖G‖ + γ * ‖V‖ := by
  obtain ⟨hL, hLle⟩ :=
    memLp_inner_add_mul_and_lpNorm_le Fact.out hb hbβ hc hcγ (Lp.memLp G) (Lp.memLp V)
  rw [← Lp.norm_eq_lpNorm_of_ae_eq hL.coeFn_toLp, ← Lp.norm_eq_lpNorm_of_ae_eq (f := G) .rfl,
    ← Lp.norm_eq_lpNorm_of_ae_eq (f := V) .rfl] at hLle
  refine ⟨f - hL.toLp _, ?_, by linarith [norm_sub_le f (hL.toLp _)]⟩
  filter_upwards [heq, Lp.coeFn_sub f (hL.toLp _), hL.coeFn_toLp] with x hx h1 h2
  rw [h1, Pi.sub_apply, h2, ← hx]
  ring

end MeasureTheory
