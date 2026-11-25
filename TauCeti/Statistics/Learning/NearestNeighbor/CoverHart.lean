/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The Cover–Hart inequalities

For a regression function `η` with values in `[0, 1]` under a law `μ` of the features, the Bayes
risk of binary classification is `L* = E min(η, 1 - η)`, and the asymptotic risk of the
1-nearest-neighbour rule is `L(1) = E 2η(1 - η)`. Cover and Hart compared the two:
`L* ≤ L(1) ≤ 2L*(1 - L*) ≤ 2L*`.

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
and takes values in `[0, 1]` only almost everywhere, the measure need only have mass at most `1`,
and the middle bound is proved by integrating `2m(1 - m) + 2(m - L*)²`, which is affine in
`m = min(η, 1 - η)`, instead of through the variance.
-/

public section

open MeasureTheory Set

namespace TauCeti

/-- **Cover–Hart inequalities.** For a measure `μ` of total mass at most `1` (in particular a
probability law) and a function `η` with values in `[0, 1]` `μ`-almost everywhere, the Bayes
risk `L* = E min(η, 1 - η)` and the asymptotic nearest-neighbour risk `L(1) = E 2η(1 - η)`
satisfy `L* ≤ L(1) ≤ 2L*(1 - L*) ≤ 2L*`. -/
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
    -- `g ∘ m + 2 (m - a)²` is affine in `m`; its integral is at most `2a(1 - a)` as `μ univ ≤ 1`.
    have hsq : Integrable (fun x ↦ 2 * (m x - a) ^ 2) μ :=
      (MemLp.integrable_sq ((MemLp.of_bound hmeas 1 hbd).sub (memLp_const a))).const_mul 2
    have hsum : ∫ x, (g ∘ m) x + 2 * (m x - a) ^ 2 ∂μ =
        2 * (1 - 2 * a) * a + μ.real univ * (2 * a ^ 2) := by
      rw [integral_congr_ae (g := fun x ↦ 2 * (1 - 2 * a) * m x + 2 * a ^ 2)
          (ae_of_all _ fun x ↦ by simp only [Function.comp_apply, g]; ring),
        integral_add (hmi.const_mul _) (integrable_const _), integral_const_mul, integral_const,
        smul_eq_mul]
    refine ⟨integral_mono_ae hmi hgi (hm.mono fun x hx ↦ ?_), ?_, by nlinarith [sq_nonneg a]⟩
    · simp only [Function.comp_apply, g]
      nlinarith [hm_le x]
    · rw [integral_add hgi hsq] at hsum
      nlinarith [(integral_nonneg (fun x ↦ by positivity) : 0 ≤ ∫ x, 2 * (m x - a) ^ 2 ∂μ),
        (by simpa [measureReal_def] using ENNReal.toReal_mono ENNReal.one_ne_top hμ :
          μ.real univ ≤ 1)]
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
