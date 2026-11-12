/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Uniform
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalitiesPow
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Uniform convexity of powers of the norm

Let `E` be a uniformly convex real normed space and `1 < q`. The power mean inequality bounds
`‖a + b‖ ^ q` by `2 ^ (q - 1) * (‖a‖ ^ q + ‖b‖ ^ q)` for all vectors `a`, `b`. This file shows
that the bound improves by a uniform factor once `a` and `b` are far apart relative to their size:
for every `η > 0` there is `δ > 0` such that

`‖a + b‖ ^ q ≤ (1 - δ) * 2 ^ (q - 1) * (‖a‖ ^ q + ‖b‖ ^ q)`
whenever `η * (‖a‖ ^ q + ‖b‖ ^ q) ≤ ‖a - b‖ ^ q`.

When `‖b‖` is much smaller than `‖a‖`, the improvement comes from strict convexity of
`t ↦ t ^ q`; when the two norms are comparable, it comes from uniform convexity of `E`.

Combining the two cases gives an inequality valid for all `a` and `b`, with no side condition:

`‖a + b‖ ^ q + δ * ‖a - b‖ ^ q ≤ (2 ^ (q - 1) + δ * η) * (‖a‖ ^ q + ‖b‖ ^ q)`.

For `2 ≤ q` in an inner product space, Clarkson's inequality
`TauCeti.norm_add_rpow_add_norm_sub_rpow_le` is the sharper form with `δ = 1` and `η = 0`.
Like Clarkson's inequality, the combined form is linear in `q`-th powers of norms, so it
integrates to the same inequality in `Lᵖ`. This is how uniform convexity passes from `E` to the
Lebesgue–Bochner spaces `Lp E p μ` for `1 < p < ∞`.

## Main statements

* `TauCeti.exists_forall_norm_add_rpow_le`: the improved power mean inequality for vectors
  that are far apart.
* `TauCeti.exists_forall_norm_add_rpow_add_mul_norm_sub_rpow_le`: the combined inequality, valid
  for all pairs of vectors.

## References

* M. M. Day, *Some more uniformly convex spaces*, Bull. Amer. Math. Soc. 47 (1941), 504–507.
-/

public section

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [UniformConvexSpace E]
  {q η : ℝ}

/-- **Uniform convexity of the `q`-th power of the norm.** In a uniformly convex real normed
space, for `1 < q` and `η > 0` there is `δ > 0` such that
`‖a + b‖ ^ q ≤ (1 - δ) * 2 ^ (q - 1) * (‖a‖ ^ q + ‖b‖ ^ q)` whenever
`η * (‖a‖ ^ q + ‖b‖ ^ q) ≤ ‖a - b‖ ^ q`. Without the separation hypothesis this holds with
`δ = 0`, by the power mean inequality. -/
theorem exists_forall_norm_add_rpow_le (hq : 1 < q) (hη : 0 < η) :
    ∃ δ, 0 < δ ∧ ∀ a b : E, η * (‖a‖ ^ q + ‖b‖ ^ q) ≤ ‖a - b‖ ^ q →
      ‖a + b‖ ^ q ≤ (1 - δ) * 2 ^ (q - 1) * (‖a‖ ^ q + ‖b‖ ^ q) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨δ₁, hδ₁, hUC⟩ :=
    exists_forall_closed_ball_dist_add_le_two_sub E (Real.rpow_pos_of_pos hη q⁻¹)
  obtain ⟨κ, hκ, hreal⟩ :=
    Real.exists_rpow_le_of_le_add_of_le_two_sub_mul hq hδ₁
  -- The case `‖b‖ ≤ ‖a‖`: rescale `a` to the unit sphere and apply uniform convexity.
  have key (a b : E) (hba : ‖b‖ ≤ ‖a‖) (hab : η * (‖a‖ ^ q + ‖b‖ ^ q) ≤ ‖a - b‖ ^ q) :
      ‖a + b‖ ^ q ≤ (1 - κ) * 2 ^ (q - 1) * (‖a‖ ^ q + ‖b‖ ^ q) := by
    refine hreal _ _ _ (norm_nonneg b) hba (norm_nonneg _) (norm_add_le a b) ?_
    rcases (norm_nonneg a).eq_or_lt with ha | ha
    · have hb : ‖b‖ = 0 := le_antisymm (ha ▸ hba) (norm_nonneg b)
      have := norm_add_le a b
      rw [← ha, hb] at this
      rw [← ha, mul_zero]
      linarith
    have hnorm (c : ℝ) (x : E) (hc : 0 ≤ c) : ‖c • x‖ = c * ‖x‖ := by
      rw [norm_smul, Real.norm_of_nonneg hc]
    have hinv : 0 ≤ ‖a‖⁻¹ := inv_nonneg.2 ha.le
    have hx : ‖‖a‖⁻¹ • a‖ ≤ 1 := by rw [hnorm _ _ hinv, inv_mul_cancel₀ ha.ne']
    have hy : ‖‖a‖⁻¹ • b‖ ≤ 1 := by
      rw [hnorm _ _ hinv, inv_mul_le_iff₀ ha, mul_one]
      exact hba
    have hsep : η ^ q⁻¹ ≤ ‖‖a‖⁻¹ • a - ‖a‖⁻¹ • b‖ := by
      rw [← smul_sub, hnorm _ _ hinv, le_inv_mul_iff₀ ha]
      have hbq : 0 ≤ ‖b‖ ^ q := Real.rpow_nonneg (norm_nonneg b) q
      calc ‖a‖ * η ^ q⁻¹ = (η * ‖a‖ ^ q) ^ q⁻¹ := by
            rw [mul_comm, Real.mul_rpow hη.le (Real.rpow_nonneg (norm_nonneg a) q),
              Real.rpow_rpow_inv (norm_nonneg a) hq0.ne']
        _ ≤ (‖a - b‖ ^ q) ^ q⁻¹ := by
            gcongr
            nlinarith
        _ = ‖a - b‖ := Real.rpow_rpow_inv (norm_nonneg _) hq0.ne'
    have h := hUC hx hy hsep
    rw [← smul_add, hnorm _ _ hinv, inv_mul_le_iff₀ ha] at h
    nlinarith
  refine ⟨κ, hκ, fun a b hab ↦ ?_⟩
  rcases le_total ‖b‖ ‖a‖ with h | h
  · exact key a b h hab
  · have := key b a h (by rwa [norm_sub_rev, add_comm (‖b‖ ^ q)])
    rwa [add_comm b, add_comm (‖b‖ ^ q)] at this

/-- **A Clarkson-type inequality in uniformly convex spaces.** In a uniformly convex real
normed space, for `1 < q` and `η > 0` there is `δ > 0` such that for all vectors `a` and `b`,
`‖a + b‖ ^ q + δ * ‖a - b‖ ^ q ≤ (2 ^ (q - 1) + δ * η) * (‖a‖ ^ q + ‖b‖ ^ q)`.

Being linear in `q`-th powers of norms, this inequality integrates to the same inequality in
`Lᵖ` and so shows that `Lᵖ` is uniformly convex. -/
theorem exists_forall_norm_add_rpow_add_mul_norm_sub_rpow_le (hq : 1 < q) (hη : 0 < η) :
    ∃ δ, 0 < δ ∧ ∀ a b : E,
      ‖a + b‖ ^ q + δ * ‖a - b‖ ^ q ≤ (2 ^ (q - 1) + δ * η) * (‖a‖ ^ q + ‖b‖ ^ q) := by
  obtain ⟨δ, hδ, h⟩ := exists_forall_norm_add_rpow_le (E := E) hq hη
  refine ⟨δ, hδ, fun a b ↦ ?_⟩
  have hq0 : 0 ≤ q := by linarith
  -- The power mean inequality, lifted from `ℝ≥0`.
  have hmean (x y : E) : ‖x + y‖ ^ q ≤ 2 ^ (q - 1) * (‖x‖ ^ q + ‖y‖ ^ q) := by
    refine (Real.rpow_le_rpow (norm_nonneg _) (norm_add_le x y) hq0).trans ?_
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow ‖x‖₊ ‖y‖₊ hq.le
  have hS : 0 ≤ ‖a‖ ^ q + ‖b‖ ^ q := by positivity
  have hδη : 0 ≤ δ * η := mul_nonneg hδ.le hη.le
  by_cases hab : η * (‖a‖ ^ q + ‖b‖ ^ q) ≤ ‖a - b‖ ^ q
  · -- Far apart: the improved power mean inequality absorbs `δ * ‖a - b‖ ^ q`.
    have hsub : ‖a - b‖ ^ q ≤ 2 ^ (q - 1) * (‖a‖ ^ q + ‖b‖ ^ q) := by
      simpa [sub_eq_add_neg] using hmean a (-b)
    nlinarith [h a b hab]
  · -- Close together: `δ * ‖a - b‖ ^ q` is at most `δ * η * (‖a‖ ^ q + ‖b‖ ^ q)`.
    push Not at hab
    nlinarith [hmean a b]

end TauCeti
