/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Uniform
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact

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

/-- For `1 < q`, `0 < δ` and `0 ≤ r ≤ 1`, `min (1 + r) (2 - δ) ^ q < 2 ^ (q - 1) * (1 + r ^ q)`:
for `r < 1` by strict convexity of `t ↦ t ^ q`, and for `r = 1` because `2 - δ < 2`. -/
private theorem min_rpow_lt_two_rpow_sub_one_mul {q δ r : ℝ} (hq : 1 < q) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    min (1 + r) (2 - δ) ^ q < 2 ^ (q - 1) * (1 + r ^ q) := by
  have hq0 : 0 < q := by linarith
  have h2sub : (2 : ℝ) ^ (q - 1) = 2 ^ q / 2 := Real.rpow_sub_one two_ne_zero q
  have hmin0 : 0 ≤ min (1 + r) (2 - δ) := le_min (by linarith) (by linarith)
  rcases hr1.lt_or_eq with hr1 | rfl
  · have hstrict := (strictConvexOn_rpow hq).2 (Set.mem_Ici.2 zero_le_one) (Set.mem_Ici.2 hr0)
      hr1.ne' (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    simp only [smul_eq_mul, Real.one_rpow] at hstrict
    have hle : min (1 + r) (2 - δ) ^ q ≤ (1 + r) ^ q :=
      Real.rpow_le_rpow hmin0 (min_le_left _ _) hq0.le
    have hhalf : (1 + r) ^ q = 2 ^ q * (1 / 2 * 1 + 1 / 2 * r) ^ q := by
      rw [← Real.mul_rpow zero_le_two (by positivity)]
      ring_nf
    have := mul_lt_mul_of_pos_left hstrict (by positivity : (0 : ℝ) < 2 ^ q)
    rw [h2sub]
    nlinarith
  · have hlt : min (1 + 1) (2 - δ) ^ q < 2 ^ q :=
      Real.rpow_lt_rpow hmin0 ((min_le_right _ _).trans_lt (by linarith)) hq0
    have h2 : (2 : ℝ) ^ q / 2 * (1 + 1) = 2 ^ q := by ring
    rwa [Real.one_rpow, h2sub, h2]

/-- The scalar part of `TauCeti.exists_forall_norm_add_rpow_le`. For `1 < q` and `0 < δ ≤ 1`
there is `κ > 0` such that `u ^ q ≤ (1 - κ) * 2 ^ (q - 1) * (s ^ q + t ^ q)` whenever
`0 ≤ t ≤ s` and `0 ≤ u ≤ min (s + t) ((2 - δ) * s)`. After rescaling to `s = 1`, the gap
between the two sides is a continuous positive function of `t ∈ [0, 1]`, so it has a positive
minimum. -/
private theorem exists_rpow_le_of_le_add_of_le_two_sub_mul {q δ : ℝ} (hq : 1 < q) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    ∃ κ, 0 < κ ∧ ∀ s t u : ℝ, 0 ≤ t → t ≤ s → 0 ≤ u → u ≤ s + t → u ≤ (2 - δ) * s →
      u ^ q ≤ (1 - κ) * 2 ^ (q - 1) * (s ^ q + t ^ q) := by
  have hq0 : 0 < q := by linarith
  have h2sub : (2 : ℝ) ^ (q - 1) = 2 ^ q / 2 := Real.rpow_sub_one two_ne_zero q
  -- The gap between the two sides after rescaling to `s = 1`.
  set φ : ℝ → ℝ := fun r ↦ 2 ^ (q - 1) * (1 + r ^ q) - min (1 + r) (2 - δ) ^ q with hφ
  have hφc : Continuous φ := by
    have := Real.continuous_rpow_const hq0.le
    fun_prop
  obtain ⟨r₀, hr₀, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 zero_le_one) hφc.continuousOn
  have hm : 0 < φ r₀ := sub_pos.2 (min_rpow_lt_two_rpow_sub_one_mul hq hδ hδ1 hr₀.1 hr₀.2)
  refine ⟨φ r₀ / 2 ^ q, by positivity, fun s t u ht hts hu hus hu2 ↦ ?_⟩
  rcases (ht.trans hts).eq_or_lt with rfl | hs
  · obtain rfl : t = 0 := le_antisymm hts ht
    obtain rfl : u = 0 := le_antisymm (by simpa using hus) hu
    simp [Real.zero_rpow hq0.ne']
  set r := t / s with hr_def
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := ⟨div_nonneg ht hs.le, div_le_one_of_le₀ hts hs.le⟩
  have hv : u / s ≤ min (1 + r) (2 - δ) := by
    refine le_min ?_ ?_ <;> rw [div_le_iff₀ hs]
    · rw [hr_def, add_mul, div_mul_cancel₀ _ hs.ne', one_mul]
      exact hus
    · linarith
  have hrq : r ^ q ≤ 1 := Real.rpow_le_one hr.1 hr.2 hq0.le
  have hgap : φ r₀ ≤ φ r := hmin hr
  have hvq : (u / s) ^ q ≤ min (1 + r) (2 - δ) ^ q :=
    Real.rpow_le_rpow (div_nonneg hu hs.le) hv hq0.le
  have key : (u / s) ^ q ≤ (1 - φ r₀ / 2 ^ q) * 2 ^ (q - 1) * (1 + r ^ q) := by
    simp only [hφ] at hgap
    have hrq0 : 0 ≤ r ^ q := Real.rpow_nonneg hr.1 q
    have : (1 - φ r₀ / 2 ^ q) * 2 ^ (q - 1) * (1 + r ^ q) =
        2 ^ (q - 1) * (1 + r ^ q) - φ r₀ * ((1 + r ^ q) / 2) := by
      rw [h2sub]
      field_simp
    rw [this]
    nlinarith
  have hsq : 0 < s ^ q := Real.rpow_pos_of_pos hs q
  calc u ^ q = s ^ q * (u / s) ^ q := by
        rw [Real.div_rpow hu hs.le, mul_div_cancel₀ _ hsq.ne']
    _ ≤ s ^ q * ((1 - φ r₀ / 2 ^ q) * 2 ^ (q - 1) * (1 + r ^ q)) := by gcongr
    _ = (1 - φ r₀ / 2 ^ q) * 2 ^ (q - 1) * (s ^ q + t ^ q) := by
        rw [hr_def, Real.div_rpow ht hs.le]
        field_simp

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
  obtain ⟨κ, hκ, hreal⟩ := exists_rpow_le_of_le_add_of_le_two_sub_mul hq (lt_min hδ₁ one_pos)
    (min_le_right δ₁ 1)
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
    nlinarith [min_le_left δ₁ 1]
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
