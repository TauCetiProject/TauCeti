/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz

/-!
# The Cover–Hart inequalities

For a function `η` with values in `[0, 1]` and a measure `μ` of total mass at most `1`, write
`L* = ∫ min(η, 1 - η) dμ` and `L(1) = ∫ 2η(1 - η) dμ`. The Cover–Hart inequalities are
`L* ≤ L(1) ≤ 2L*(1 - L*) ≤ 2L*`.

In binary classification, when `μ` is the law of the features and `η` a measurable regression
function `x ↦ P(Y = 1 | X = x)`, `L*` is the Bayes risk. Under the assumptions of a separate
nearest-neighbour limit theorem (Cover and Hart's, for example), `L(1)` is the asymptotic risk of
the 1-nearest-neighbour rule. The inequalities themselves concern only the two integrals.

## Main results

* `TauCeti.bayesRisk_le_nnRisk_le`: the Cover–Hart inequalities
  `L* ≤ L(1) ≤ 2L*(1 - L*) ≤ 2L*`, for any `η` with values in `[0, 1]` almost everywhere, under
  any measure of total mass at most `1`. No measurability of `η` is needed: if
  `min(η, 1 - η)` is not almost everywhere strongly measurable, neither is `2η(1 - η)`, and both
  integrals are `0`.

## References

* T. M. Cover and P. E. Hart, *Nearest neighbor pattern classification*, IEEE Trans. Inform.
  Theory 13 (1967), 21–27.
* L. Devroye, L. Györfi and G. Lugosi, *A Probabilistic Theory of Pattern Recognition*,
  Springer (1996), (3.1), p. 22.

## Attribution

Adapted from lean-CKSD, `CKSD/Learning/LocalAveraging.lean` (`bayesRisk_le_nnRisk_le`), with AI
assistance (Claude). Here the bound `2L*(1 - L*) ≤ 2L*` is added, `η` need not be measurable
and takes values in `[0, 1]` only almost everywhere, and the measure need only have mass at most
`1`.
-/

public section

open MeasureTheory Set

namespace TauCeti

/-- **Cover–Hart inequalities.** For a measure `μ` of total mass at most `1` (in particular a
probability law) and a function `η` with values in `[0, 1]` `μ`-almost everywhere, the integrals
`L* = ∫ min(η, 1 - η) dμ` and `L(1) = ∫ 2η(1 - η) dμ` satisfy `L* ≤ L(1) ≤ 2L*(1 - L*) ≤ 2L*`.
They are the Bayes risk and the asymptotic 1-nearest-neighbour risk when `η` is a measurable
regression function and a nearest-neighbour limit theorem identifies `L(1)`. -/
theorem bayesRisk_le_nnRisk_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (hμ : μ univ ≤ 1) (η : X → ℝ) (h01 : ∀ᵐ x ∂μ, η x ∈ Icc (0 : ℝ) 1) :
    (∫ x, min (η x) (1 - η x) ∂μ) ≤ ∫ x, 2 * η x * (1 - η x) ∂μ ∧
      (∫ x, 2 * η x * (1 - η x) ∂μ) ≤
        2 * (∫ x, min (η x) (1 - η x) ∂μ) * (1 - ∫ x, min (η x) (1 - η x) ∂μ) ∧
      2 * (∫ x, min (η x) (1 - η x) ∂μ) * (1 - ∫ x, min (η x) (1 - η x) ∂μ) ≤
        2 * ∫ x, min (η x) (1 - η x) ∂μ := by
  set m : X → ℝ := fun x ↦ min (η x) (1 - η x)
  set g : ℝ → ℝ := fun t ↦ 2 * t * (1 - t)
  -- The nearest-neighbour integrand is `g ∘ m`, since `g` is symmetric about `1/2`.
  have hgm : (fun x ↦ 2 * η x * (1 - η x)) = g ∘ m := by
    funext x
    simp only [Function.comp_apply, m, g, min_def]
    split_ifs <;> ring
  have hm_le : ∀ x, m x ≤ 2⁻¹ := fun x ↦ min_le_iff.2 (by by_contra! h; linarith [h.1, h.2])
  have hm : ∀ᵐ x ∂μ, 0 ≤ m x := h01.mono fun x hx ↦ le_min hx.1 (by linarith [hx.2])
  rw [hgm]
  have : IsFiniteMeasure μ := ⟨hμ.trans_lt ENNReal.one_lt_top⟩
  by_cases hmeas : AEStronglyMeasurable m μ
  · have hbd : ∀ᵐ x ∂μ, ‖m x‖ ≤ 1 := hm.mono fun x hx ↦ by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hm_le x]
    have hmi : Integrable m μ := Integrable.of_bound hmeas 1 hbd
    have hgi : Integrable (g ∘ m) μ :=
      Integrable.of_bound ((by fun_prop : Continuous g).comp_aestronglyMeasurable hmeas) 1
        (hm.mono fun x hx ↦ by
          rw [Function.comp_apply, Real.norm_eq_abs, abs_le]
          constructor <;> simp only [g] <;> nlinarith [hm_le x])
    set a := ∫ x, m x ∂μ
    have hm2 : Integrable (fun x ↦ m x ^ 2) μ := (MemLp.of_bound hmeas 1 hbd).integrable_sq
    -- The middle bound: `∫ g ∘ m = 2a - 2 ∫ m²`, and Cauchy–Schwarz against `1` gives
    -- `a² ≤ ∫ m²` because `μ univ ≤ 1`.
    have hCS : a ^ 2 ≤ ∫ x, m x ^ 2 ∂μ := by
      calc a ^ 2 = |a| ^ 2 := (sq_abs a).symm
        _ ≤ √(∫ x, m x ^ 2 ∂μ) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg a) (hm2.abs_integral_le_sqrt_integral_sq hμ) 2
        _ = ∫ x, m x ^ 2 ∂μ := Real.sq_sqrt (integral_nonneg fun x ↦ sq_nonneg _)
    have hgint : ∫ x, (g ∘ m) x ∂μ = 2 * a - 2 * ∫ x, m x ^ 2 ∂μ := by
      rw [integral_congr_ae (g := fun x ↦ 2 * m x - 2 * m x ^ 2)
          (ae_of_all _ fun x ↦ by simp only [Function.comp_apply, g]; ring),
        integral_sub (hmi.const_mul _) (hm2.const_mul _), integral_const_mul, integral_const_mul]
    refine ⟨integral_mono_ae hmi hgi (hm.mono fun x hx ↦ ?_), ?_, by nlinarith [sq_nonneg a]⟩
    · simp only [Function.comp_apply, g]
      nlinarith [hm_le x]
    · rw [hgint]
      nlinarith [hCS]
  · -- `m = h ∘ g ∘ m` for a continuous `h`, neither integrand is integrable: both are `0`.
    have hinv : m = (fun s ↦ (1 - √(1 - 2 * s)) / 2) ∘ g ∘ m := by
      funext x
      have : 1 - 2 * g (m x) = (1 - 2 * m x) ^ 2 := by simp only [g]; ring
      simp only [Function.comp_apply, this, Real.sqrt_sq (by linarith [hm_le x] : 0 ≤ 1 - 2 * m x)]
      ring
    have hgm_meas : ¬AEStronglyMeasurable (g ∘ m) μ := fun h ↦ hmeas <| by
      rw [hinv]
      exact (by fun_prop : Continuous fun s : ℝ ↦ (1 - √(1 - 2 * s)) / 2)
        |>.comp_aestronglyMeasurable h
    rw [integral_undef fun h ↦ hmeas h.1, integral_undef fun h ↦ hgm_meas h.1]
    norm_num

end TauCeti
