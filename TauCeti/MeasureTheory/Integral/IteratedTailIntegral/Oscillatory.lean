/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Asymptotics.Oscillatory
public import TauCeti.MeasureTheory.Integral.IteratedTailIntegral.Basic

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import TauCeti.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.MeasureTheory.Integral.IteratedTailIntegral.Asymptotics

/-!
# Repeated improper tail integrals of oscillatory functions

Integration by parts for power-damped oscillations `t ^ (-α) * cos (c * t ^ p + φ)` with `c ≠ 0`,
`1 ≤ p`, and `0 < α + p - 1` improves polynomial decay by `p - 1` at each step while preserving
the oscillatory form `TauCeti.HasOscillatoryDecay c p α₀ f` (defined in
`TauCeti.Analysis.Asymptotics.Oscillatory`). This file proves that `TauCeti.iteratedTailIntegral`
preserves `HasOscillatoryDecay` to all orders:

* Every `iteratedTailIntegral f n` satisfies `HasOscillatoryDecay c p (α₀ + n * (p - 1))`
  (`TauCeti.HasOscillatoryDecay.iteratedTailIntegral`), hence
  `iteratedTailIntegral f n =O[atTop] fun t ↦ t ^ (-(α₀ + n * (p - 1)))` via
  `TauCeti.HasOscillatoryDecay.isBigO_rpow_neg`.
* For every `n : ℕ` and `x : ℝ`, `R ↦ ∫ t in x..R, iteratedTailIntegral f n t` converges to
  `iteratedTailIntegral f (n + 1) x` as `R → ∞`
  (`TauCeti.HasOscillatoryDecay.tendsto_intervalIntegral_iteratedTailIntegral`). When
  `LocallyIntegrableOn (iteratedTailIntegral f n) (Ici x)` holds, this represents a genuine
  convergent improper integral; where local integrability of `iteratedTailIntegral f n` on
  `[x, ∞)` fails, truncated integrals vanish for large `R` by Mathlib's
  `intervalIntegral.integral_undef` convention (and positive-order iterates collapse to `0` if `f`
  is locally integrable on no ray `[a, ∞)`).

## Main declarations

* `TauCeti.HasOscillatoryDecay.iteratedTailIntegral`: preservation of `HasOscillatoryDecay` under
  `TauCeti.iteratedTailIntegral` with exponent shift `n * (p - 1)`.
* `TauCeti.HasOscillatoryDecay.tendsto_intervalIntegral_iteratedTailIntegral`: convergence of all
  repeated improper tail integrals.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974.
* NIST Digital Library of Mathematical Functions, §9.10(v).
-/

public section

namespace TauCeti

open Asymptotics Filter MeasureTheory Set
open scoped Topology Interval

/-- Continuity of a phase-shifted oscillatory mode `t ↦ t ^ q * trig (c * t ^ p + φ)` on `[x, ∞)`
(`0 < x`). -/
private theorem continuousOn_rpow_mul_trig_add {c p q x φ : ℝ} (hx : 0 < x) {trig : ℝ → ℝ}
    (hcont : Continuous trig) :
    ContinuousOn (fun t : ℝ ↦ t ^ q * trig (c * t ^ p + φ)) (Ici x) :=
  (ContinuousOn.rpow_const continuousOn_id fun _ ht ↦ Or.inl (hx.trans_le ht).ne').mul
    (hcont.comp_continuousOn ((continuousOn_const.mul
      (ContinuousOn.rpow_const continuousOn_id fun _ ht ↦ Or.inl (hx.trans_le ht).ne')).add
      continuousOn_const))

/-- Continuity of an algebraic-oscillatory mode `t ↦ t ^ q * trig (c * t ^ p)` on `[x, ∞)`
(`0 < x`). -/
private theorem continuousOn_rpow_mul_trig {c p q x : ℝ} (hx : 0 < x) {trig : ℝ → ℝ}
    (hcont : Continuous trig) :
    ContinuousOn (fun t : ℝ ↦ t ^ q * trig (c * t ^ p)) (Ici x) := by
  simpa only [add_zero] using continuousOn_rpow_mul_trig_add (c := c) (p := p) (q := q) (φ := 0)
    hx hcont

/-- Finite-interval integration by parts for `t ^ (-α) * cos (c * t ^ p + φ)` on `[x, R]`
(`0 < x`). -/
private theorem intervalIntegral_rpow_mul_cos_add_eq {c p α φ x R : ℝ}
    (hc : c ≠ 0) (hp : 0 < p) (hx : 0 < x) (hR : x ≤ R) :
    ∫ t in x..R, t ^ (-α) * Real.cos (c * t ^ p + φ) =
      (c * p)⁻¹ * R ^ (-(α + p - 1)) * Real.sin (c * R ^ p + φ) -
        (c * p)⁻¹ * x ^ (-(α + p - 1)) * Real.sin (c * x ^ p + φ) +
        ((α + p - 1) / (c * p)) *
          ∫ t in x..R, t ^ (-(α + p)) * Real.cos (c * t ^ p + (φ - Real.pi / 2)) := by
  let u : ℝ → ℝ := fun t ↦ (c * p)⁻¹ * t ^ (-(α + p - 1))
  let u' : ℝ → ℝ := fun t ↦ -((α + p - 1) / (c * p)) * t ^ (-(α + p))
  let v : ℝ → ℝ := fun t ↦ Real.sin (c * t ^ p + φ)
  let v' : ℝ → ℝ := fun t ↦ Real.cos (c * t ^ p + φ) * (c * (p * t ^ (p - 1)))
  have hpos : ∀ t ∈ [[x, R]], 0 < t := fun _ ht ↦ hx.trans_le ((uIcc_of_le hR ▸ ht).1)
  have hrp (q : ℝ) : ContinuousOn (fun t : ℝ ↦ t ^ q) [[x, R]] :=
    ContinuousOn.rpow_const continuousOn_id fun t ht ↦ Or.inl (hpos t ht).ne'
  have hu : ∀ t ∈ [[x, R]], HasDerivAt u (u' t) t := fun t ht ↦ by
    have hexp : -(α + p - 1) - 1 = -(α + p) := by ring
    refine ((Real.hasDerivAt_rpow_const (p := -(α + p - 1))
      (Or.inl (hpos t ht).ne')).const_mul (c * p)⁻¹).congr_deriv ?_
    dsimp [u']; rw [hexp]; ring
  have hv : ∀ t ∈ [[x, R]], HasDerivAt v (v' t) t := fun t ht ↦
    ((((Real.hasDerivAt_rpow_const (p := p)
      (Or.inl (hpos t ht).ne')).const_mul c).add_const φ).sin).congr_deriv rfl
  have hu'_cont : ContinuousOn u' [[x, R]] := continuousOn_const.mul (hrp _)
  have hv'_cont : ContinuousOn v' [[x, R]] :=
    (Real.continuous_cos.comp_continuousOn ((continuousOn_const.mul (hrp p)).add
      continuousOn_const)).mul (continuousOn_const.mul (continuousOn_const.mul (hrp _)))
  have hcongr : ∫ t in x..R, t ^ (-α) * Real.cos (c * t ^ p + φ) = ∫ t in x..R, u t * v' t := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    dsimp [u, v']
    have hexp : -(α + p - 1) + (p - 1) = -α := by ring
    calc
      t ^ (-α) * Real.cos (c * t ^ p + φ)
          = ((c * p)⁻¹ * (c * p)) * (t ^ (-(α + p - 1)) * t ^ (p - 1)) *
              Real.cos (c * t ^ p + φ) := by
            rw [inv_mul_cancel₀ (mul_ne_zero hc hp.ne'), one_mul, ← Real.rpow_add (hpos t ht),
              hexp]
      _ = (c * p)⁻¹ * t ^ (-(α + p - 1)) *
            (Real.cos (c * t ^ p + φ) * (c * (p * t ^ (p - 1)))) := by
          ring
  have huv : (fun t ↦ u' t * v t) = fun t ↦ -((α + p - 1) / (c * p)) *
      (t ^ (-(α + p)) * Real.cos (c * t ^ p + (φ - Real.pi / 2))) := by
    ext t; dsimp [u', v]; rw [← add_sub_assoc, Real.cos_sub_pi_div_two]; ring
  rw [hcongr, intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    hu'_cont.intervalIntegrable hv'_cont.intervalIntegrable, huv,
    intervalIntegral.integral_const_mul]
  dsimp [u, v]; ring

/-- Improper oscillatory integration by parts on `(x, ∞)` (`0 < x`, `0 < α + p - 1`) for a
phase-shifted cosine mode `t ^ (-α) * cos (c * t ^ p + φ)`. -/
private theorem tendsto_and_tail_rpow_mul_cos_add {c p α φ x : ℝ}
    (hc : c ≠ 0) (hp : 0 < p) (hα : 0 < α + p - 1) (hx : 0 < x) :
    (∃ L, Tendsto (fun R : ℝ ↦ ∫ t in x..R, t ^ (-α) * Real.cos (c * t ^ p + φ)) atTop (𝓝 L)) ∧
      iteratedTailIntegral (fun t ↦ t ^ (-α) * Real.cos (c * t ^ p + φ)) 1 x =
        -(c * p)⁻¹ * (x ^ (-(α + p - 1)) * Real.cos (c * x ^ p + (φ - Real.pi / 2))) +
          ((α + p - 1) / (c * p)) *
            iteratedTailIntegral
              (fun t ↦ t ^ (-(α + p)) * Real.cos (c * t ^ p + (φ - Real.pi / 2))) 1 x := by
  have hbnd : Tendsto (fun R : ℝ ↦ (c * p)⁻¹ * R ^ (-(α + p - 1)) * Real.sin (c * R ^ p + φ))
      atTop (𝓝 0) := by
    have hbig : (fun R : ℝ ↦ (c * p)⁻¹ * R ^ (-(α + p - 1)) * Real.sin (c * R ^ p + φ)) =O[atTop]
        fun R : ℝ ↦ R ^ (-(α + p - 1)) := by
      simpa only [mul_assoc] using ((HasOscillatoryDecay.rpow_mul_sin_add (c := c) (p := p)
        le_rfl φ).const_mul (c * p)⁻¹).isBigO_rpow_neg
    exact hbig.trans_tendsto (tendsto_rpow_neg_atTop hα)
  have hrem_int : IntegrableOn
      (fun t : ℝ ↦ t ^ (-(α + p)) * Real.cos (c * t ^ p + (φ - Real.pi / 2))) (Ioi x) := by
    refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (by linarith : -(α + p) < -1) hx)
      (((continuousOn_rpow_mul_trig_add hx Real.continuous_cos).mono
        Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (hx.trans ht).le _), Real.norm_eq_abs]
    exact mul_le_of_le_one_right (Real.rpow_nonneg (hx.trans ht).le _) (Real.abs_cos_le_one _)
  have ht : Tendsto (fun R : ℝ ↦ ∫ t in x..R, t ^ (-α) * Real.cos (c * t ^ p + φ)) atTop
      (𝓝 (-(c * p)⁻¹ * (x ^ (-(α + p - 1)) * Real.cos (c * x ^ p + (φ - Real.pi / 2))) +
        ((α + p - 1) / (c * p)) *
          ∫ t in Ioi x, t ^ (-(α + p)) * Real.cos (c * t ^ p + (φ - Real.pi / 2)))) := by
    have hlim := (hbnd.sub_const ((c * p)⁻¹ * x ^ (-(α + p - 1)) * Real.sin (c * x ^ p + φ))).add
      ((intervalIntegral_tendsto_integral_Ioi x hrem_int tendsto_id).const_mul
        ((α + p - 1) / (c * p)))
    convert hlim.congr' ?_ using 2
    · rw [← add_sub_assoc, Real.cos_sub_pi_div_two]; ring
    · filter_upwards [eventually_ge_atTop x] with R hR using
        (intervalIntegral_rpow_mul_cos_add_eq hc hp hx hR).symm
  refine ⟨⟨_, ht⟩, ?_⟩
  rw [iteratedTailIntegral_one_eq_of_tendsto ht, iteratedTailIntegral_one_eq_integral_Ioi hrem_int]

/-- Inductive step in `m` for `hasOscillatoryDecay_tail_rpow_mul_cos_add`. -/
private theorem hasOscillatoryDecayAt_tail_rpow_mul_cos_add_aux {c p : ℝ}
    (hc : c ≠ 0) (hp : 0 < p) (m : ℕ) {γ B : ℝ} (φ : ℝ)
    (hγ : 0 < γ + p - 1) (hB : B ≤ γ + p - 1 + m * p) :
    HasOscillatoryDecayAt c p (γ + p - 1) B
      (iteratedTailIntegral (fun t ↦ t ^ (-γ) * Real.cos (c * t ^ p + φ)) 1) := by
  have htail : HasOscillatoryDecayAt c p (γ + p - 1) B
      (iteratedTailIntegral
        (fun t ↦ t ^ (-(γ + p)) * Real.cos (c * t ^ p + (φ - Real.pi / 2))) 1) := by
    cases m with
    | zero =>
      have hbig : (fun t : ℝ ↦ t ^ (-(γ + p)) * Real.cos (c * t ^ p + (φ - Real.pi / 2))) =O[atTop]
          fun t : ℝ ↦ t ^ (-(γ + p)) :=
        (HasOscillatoryDecay.rpow_mul_cos_add (c := c) (p := p) le_rfl
          (φ - Real.pi / 2)).isBigO_rpow_neg
      exact HasOscillatoryDecayAt.of_isBigO (integrableOn_and_isBigO_tail_of_isBigO_rpow (B := B)
        ((continuousOn_rpow_mul_trig_add one_pos Real.continuous_cos).locallyIntegrableOn
          measurableSet_Ici) (by linarith) (by push_cast at hB; linarith) hbig).2
    | succ m =>
      exact (hasOscillatoryDecayAt_tail_rpow_mul_cos_add_aux hc hp m (γ := γ + p) (B := B)
        (φ - Real.pi / 2) (by linarith) (by push_cast at hB; linarith)).mono (by linarith)
  have hlead : HasOscillatoryDecayAt c p (γ + p - 1) B
      (fun x ↦ -(c * p)⁻¹ * (x ^ (-(γ + p - 1)) * Real.cos (c * x ^ p + (φ - Real.pi / 2)))) :=
    (hasOscillatoryDecay_iff.mp ((HasOscillatoryDecay.rpow_mul_cos_add (c := c) (p := p)
      (le_refl (γ + p - 1)) (φ - Real.pi / 2)).const_mul (-(c * p)⁻¹))) B
  refine (hlead.add (htail.const_mul ((γ + p - 1) / (c * p)))).congr_atTop ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simpa only [Pi.add_apply] using (tendsto_and_tail_rpow_mul_cos_add hc hp hγ hx).2.symm

/-- Iterated oscillatory integration by parts shows that the tail integral of a single
phase-shifted cosine mode `t ^ (-α) * cos (c * t ^ p + φ)` (`0 < α + p - 1`, `0 < p`, `c ≠ 0`) has
`HasOscillatoryDecay c p (α + p - 1)`. -/
private theorem hasOscillatoryDecay_tail_rpow_mul_cos_add {c p α : ℝ} (φ : ℝ)
    (hc : c ≠ 0) (hp : 0 < p) (hα : 0 < α + p - 1) :
    HasOscillatoryDecay c p (α + p - 1)
      (iteratedTailIntegral (fun t ↦ t ^ (-α) * Real.cos (c * t ^ p + φ)) 1) :=
  hasOscillatoryDecay_iff.mpr fun B ↦ hasOscillatoryDecayAt_tail_rpow_mul_cos_add_aux hc hp
    ⌈(B - (α + p - 1)) / p⌉₊ φ hα (by
      have := (div_le_iff₀ hp).mp (Nat.le_ceil ((B - (α + p - 1)) / p)); linarith)

/-- Continuity of a finite oscillatory sum on `[x, ∞)` (`0 < x`). -/
private theorem continuousOn_oscillatorySum {c p x : ℝ} {k : ℕ} {α u v : Fin k → ℝ}
    (hx : 0 < x) :
    ContinuousOn (fun t ↦ ∑ i, (u i * (t ^ (-α i) * Real.cos (c * t ^ p)) +
        v i * (t ^ (-α i) * Real.sin (c * t ^ p)))) (Ici x) :=
  continuousOn_finsetSum Finset.univ fun _ _ ↦
    (continuousOn_const.mul (continuousOn_rpow_mul_trig hx Real.continuous_cos)).add
      (continuousOn_const.mul (continuousOn_rpow_mul_trig hx Real.continuous_sin))

/-- Improper tail integral of a finite oscillatory sum on `[x, ∞)` (`0 < x`). -/
private theorem tendsto_oscillatorySum {c p x : ℝ} {k : ℕ} {α u v : Fin k → ℝ}
    (hc : c ≠ 0) (hp : 0 < p) (hα : ∀ i, 0 < α i + p - 1) (hx : 0 < x) :
    Tendsto (fun R : ℝ ↦ ∫ t in x..R,
        ∑ i, (u i * (t ^ (-α i) * Real.cos (c * t ^ p)) +
          v i * (t ^ (-α i) * Real.sin (c * t ^ p)))) atTop
      (𝓝 (∑ i, (u i * iteratedTailIntegral (fun t ↦ t ^ (-α i) * Real.cos (c * t ^ p)) 1 x +
        v i * iteratedTailIntegral (fun t ↦ t ^ (-α i) * Real.sin (c * t ^ p)) 1 x))) := by
  have hL (i : Fin k) (φ : ℝ) :
      Tendsto (fun R : ℝ ↦ ∫ t in x..R, t ^ (-α i) * Real.cos (c * t ^ p + φ))
        atTop (𝓝 (iteratedTailIntegral (fun t ↦ t ^ (-α i) * Real.cos (c * t ^ p + φ)) 1 x)) := by
    obtain ⟨_, h⟩ := (tendsto_and_tail_rpow_mul_cos_add (α := α i) (φ := φ) hc hp (hα i) hx).1
    rwa [iteratedTailIntegral_one_eq_of_tendsto h]
  refine (tendsto_finsetSum Finset.univ fun i _ ↦
    (Filter.Tendsto.const_mul (u i) (by simpa only [add_zero] using hL i 0)).add
      (Filter.Tendsto.const_mul (v i)
        (by simpa only [← sub_eq_add_neg, Real.cos_sub_pi_div_two] using
          hL i (-(Real.pi / 2))))).congr' ?_
  filter_upwards [eventually_ge_atTop x] with R hR
  have hsub : [[x, R]] ⊆ Ici x := by rw [uIcc_of_le hR]; exact fun _ ht ↦ ht.1
  have hint (i : Fin k) (a : ℝ) {trig : ℝ → ℝ} (htrig : Continuous trig) :
      IntervalIntegrable (fun t ↦ a * (t ^ (-α i) * trig (c * t ^ p))) volume x R :=
    (continuousOn_const.mul ((continuousOn_rpow_mul_trig hx htrig).mono hsub)).intervalIntegrable
  symm
  rw [intervalIntegral.integral_finsetSum fun i _ ↦
    (hint i (u i) Real.continuous_cos).add (hint i (v i) Real.continuous_sin)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [intervalIntegral.integral_add (hint i (u i) Real.continuous_cos)
      (hint i (v i) Real.continuous_sin),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- `HasOscillatoryDecayAt` bound for the tail of a finite oscillatory decomposition plus a fast
remainder. -/
private theorem hasOscillatoryDecayAt_sum_tail_add {c p α₀ B : ℝ} {k : ℕ} {α u v : Fin k → ℝ}
    {r : ℝ → ℝ} (hc : c ≠ 0) (hp : 0 < p) (hαi : ∀ i, α₀ ≤ α i) (hα_pos : ∀ i, 0 < α i + p - 1)
    (hr_tail : iteratedTailIntegral r 1 =O[atTop] fun x ↦ x ^ (-B)) :
    HasOscillatoryDecayAt c p (α₀ + p - 1) B
      (fun x ↦ (∑ i,
        (u i * iteratedTailIntegral (fun t ↦ t ^ (-α i) * Real.cos (c * t ^ p)) 1 x +
          v i * iteratedTailIntegral (fun t ↦ t ^ (-α i) * Real.sin (c * t ^ p)) 1 x)) +
        iteratedTailIntegral r 1 x) := by
  refine (HasOscillatoryDecayAt.sum fun i _ ↦ ?_).add (HasOscillatoryDecayAt.of_isBigO hr_tail)
  have hdc : HasOscillatoryDecay c p (α i + p - 1)
      (iteratedTailIntegral (fun t ↦ t ^ (-α i) * Real.cos (c * t ^ p)) 1) := by
    simpa only [add_zero] using
      hasOscillatoryDecay_tail_rpow_mul_cos_add (α := α i) 0 hc hp (hα_pos i)
  have hds : HasOscillatoryDecay c p (α i + p - 1)
      (iteratedTailIntegral (fun t ↦ t ^ (-α i) * Real.sin (c * t ^ p)) 1) := by
    simpa only [← sub_eq_add_neg, Real.cos_sub_pi_div_two] using
      hasOscillatoryDecay_tail_rpow_mul_cos_add (α := α i) (-(Real.pi / 2)) hc hp (hα_pos i)
  exact (((hasOscillatoryDecay_iff.mp hdc B).mono (by linarith [hαi i])).const_mul (u i)).add
    (((hasOscillatoryDecay_iff.mp hds B).mono (by linarith [hαi i])).const_mul (v i))

/-- Single-step convergence and `HasOscillatoryDecay` preservation for a locally integrable
function on `[a, ∞)`. -/
private theorem tendsto_and_hasOscillatoryDecay_step {c p α₀ a : ℝ} {f : ℝ → ℝ}
    (hc : c ≠ 0) (hp : 0 < p) (hα : 0 < α₀ + p - 1)
    (hf : HasOscillatoryDecay c p α₀ f) (hloc : LocallyIntegrableOn f (Ici a)) :
    (∃ L, Tendsto (fun R : ℝ ↦ ∫ t in a..R, f t) atTop (𝓝 L)) ∧
      HasOscillatoryDecay c p (α₀ + p - 1) (iteratedTailIntegral f 1) := by
  have hB (B : ℝ) : (∃ L, Tendsto (fun R : ℝ ↦ ∫ t in a..R, f t) atTop (𝓝 L)) ∧
      HasOscillatoryDecayAt c p (α₀ + p - 1) B (iteratedTailIntegral f 1) := by
    obtain ⟨k, α, u, v, r, hαi, hr, heq⟩ := hasOscillatoryDecay_def.mp hf (max B 1 + 2)
    obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp heq
    let x₀ : ℝ := max (max a 1) R₀
    have hx₀_pos : 0 < x₀ :=
      lt_of_lt_of_le zero_lt_one ((le_max_right a 1).trans (le_max_left _ _))
    have ha_x₀ : a ≤ x₀ := (le_max_left a 1).trans (le_max_left _ _)
    have hα_pos : ∀ i, 0 < α i + p - 1 := fun i ↦ by linarith [hαi i]
    have hr_loc : LocallyIntegrableOn r (Ici x₀) := by
      refine ((hloc.mono_set (Ici_subset_Ici.mpr ha_x₀)).sub (ContinuousOn.locallyIntegrableOn
        (continuousOn_oscillatorySum hx₀_pos (c := c) (p := p) (α := α) (u := u) (v := v))
        measurableSet_Ici)).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t (ht : x₀ ≤ t)
      simp [hR₀ t ((le_max_right _ _).trans ht)]
    obtain ⟨hr_int, hr_tail⟩ := integrableOn_and_isBigO_tail_of_isBigO_rpow (B := B) hr_loc
      (by linarith [le_max_right B 1]) (by linarith [le_max_left B 1]) hr
    have hfx_of_ge {x : ℝ} (hx : x₀ ≤ x) :
        Tendsto (fun R : ℝ ↦ ∫ t in x..R, f t) atTop
          (𝓝 ((∑ i, (u i * iteratedTailIntegral (fun t ↦ t ^ (-α i) * Real.cos (c * t ^ p)) 1 x +
            v i * iteratedTailIntegral (fun t ↦ t ^ (-α i) * Real.sin (c * t ^ p)) 1 x)) +
            ∫ t in Ioi x, r t)) := by
      refine ((tendsto_oscillatorySum hc hp hα_pos (hx₀_pos.trans_le hx) (u := u) (v := v)).add
        (intervalIntegral_tendsto_integral_Ioi x (hr_int.mono_set (Ioi_subset_Ioi hx))
          tendsto_id)).congr' ?_
      filter_upwards [eventually_ge_atTop x] with R hR
      have hsub : [[x, R]] ⊆ Ici x := by rw [uIcc_of_le hR]; exact fun _ ht ↦ ht.1
      rw [id, ← intervalIntegral.integral_add
        (((continuousOn_oscillatorySum (hx₀_pos.trans_le hx) (c := c) (p := p) (α := α) (u := u)
          (v := v)).mono hsub).intervalIntegrable)
        (hr_loc.intervalIntegrable (hsub.trans (Ici_subset_Ici.mpr hx)))]
      exact intervalIntegral.integral_congr fun t ht ↦
        (hR₀ t ((le_max_right _ _).trans (hx.trans (hsub ht)))).symm
    refine ⟨⟨_, hloc.tendsto_intervalIntegral_sub ha_x₀ le_rfl (hfx_of_ge le_rfl)⟩,
      (hasOscillatoryDecayAt_sum_tail_add (u := u) (v := v) hc hp hαi hα_pos hr_tail).congr_atTop
        ?_⟩
    filter_upwards [eventually_ge_atTop x₀] with x hx
    simp only [iteratedTailIntegral_one_eq_integral_Ioi (hr_int.mono_set (Ioi_subset_Ioi hx)),
      iteratedTailIntegral_one_eq_of_tendsto (hfx_of_ge hx)]
  exact ⟨(hB 0).1, hasOscillatoryDecay_iff.mpr fun B ↦ (hB B).2⟩

/-- Single-step convergence (for every basepoint `x : ℝ`, genuinely when `LocallyIntegrableOn f
(Ici x)` holds and vacuously to `0` by `intervalIntegral.integral_undef` otherwise) and
`HasOscillatoryDecay` preservation (`0 < p`, `0 < α₀ + p - 1`). -/
private theorem tendsto_and_hasOscillatoryDecay_one {c p α₀ : ℝ} {f : ℝ → ℝ}
    (hc : c ≠ 0) (hp : 0 < p) (hα : 0 < α₀ + p - 1) (hf : HasOscillatoryDecay c p α₀ f) :
    (∀ x : ℝ, Tendsto (fun R : ℝ ↦ ∫ t in x..R, f t) atTop
      (𝓝 (iteratedTailIntegral f 1 x))) ∧
      HasOscillatoryDecay c p (α₀ + p - 1) (iteratedTailIntegral f 1) := by
  have hx_tend (x : ℝ) :
      Tendsto (fun R : ℝ ↦ ∫ t in x..R, f t) atTop (𝓝 (iteratedTailIntegral f 1 x)) := by
    by_cases hx : LocallyIntegrableOn f (Ici x)
    · obtain ⟨_, hL⟩ := (tendsto_and_hasOscillatoryDecay_step hc hp hα hf hx).1
      rwa [iteratedTailIntegral_one_eq_of_tendsto hL]
    · have h0 := tendsto_intervalIntegral_zero_of_not_locallyIntegrableOn_Ici hx
      rwa [iteratedTailIntegral_one_eq_of_tendsto h0]
  refine ⟨hx_tend, ?_⟩
  by_cases hex : ∃ a : ℝ, LocallyIntegrableOn f (Ici a)
  · exact (tendsto_and_hasOscillatoryDecay_step hc hp hα hf hex.choose_spec).2
  · push Not at hex
    have hzero : iteratedTailIntegral f 1 = 0 := by
      ext x
      exact iteratedTailIntegral_one_eq_of_tendsto
        (tendsto_intervalIntegral_zero_of_not_locallyIntegrableOn_Ici (hex x))
    rw [hzero]
    exact HasOscillatoryDecay.zero c p (α₀ + p - 1)

namespace HasOscillatoryDecay

/-- **Oscillatory decay preservation under `iteratedTailIntegral`.** If `f` satisfies
`HasOscillatoryDecay c p α₀ f` with `c ≠ 0`, `1 ≤ p`, and `0 < α₀ + p - 1`, then for every
`n : ℕ`, `iteratedTailIntegral f n` satisfies `HasOscillatoryDecay c p (α₀ + n * (p - 1))` (and
hence `iteratedTailIntegral f n =O[atTop] fun t ↦ t ^ (-(α₀ + n * (p - 1)))` via
`HasOscillatoryDecay.isBigO_rpow_neg`). If `f` fails `LocallyIntegrableOn` on every ray `[a, ∞)`,
positive-order iterates collapse to `0` by `intervalIntegral.integral_undef`. -/
theorem iteratedTailIntegral {c p α₀ : ℝ} {f : ℝ → ℝ}
    (hc : c ≠ 0) (hp : 1 ≤ p) (hα : 0 < α₀ + p - 1)
    (hf : HasOscillatoryDecay c p α₀ f) (n : ℕ) :
    HasOscillatoryDecay c p (α₀ + n * (p - 1)) (TauCeti.iteratedTailIntegral f n) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  induction n with
  | zero => simpa only [Nat.cast_zero, zero_mul, add_zero, iteratedTailIntegral_zero] using hf
  | succ n ih =>
    have hpos : 0 < (α₀ + n * (p - 1)) + p - 1 := by
      have : 0 ≤ (n : ℝ) * (p - 1) := mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hp)
      linarith
    have hstep := (tendsto_and_hasOscillatoryDecay_one hc hp0 hpos ih).2
    have hshift : (α₀ + n * (p - 1)) + p - 1 = α₀ + ↑(n + 1) * (p - 1) := by push_cast; ring
    rwa [← iteratedTailIntegral_succ, hshift] at hstep

/-- **Convergence of repeated improper tail integrals** of a function satisfying
`HasOscillatoryDecay c p α₀ f` (`c ≠ 0`, `1 ≤ p`, `0 < α₀ + p - 1`). For every `n : ℕ` and
`x : ℝ`, `R ↦ ∫ t in x..R, iteratedTailIntegral f n t` tends to `iteratedTailIntegral f (n + 1) x`
as `R → ∞`. This represents a genuine convergent improper integral whenever
`LocallyIntegrableOn (iteratedTailIntegral f n) (Ici x)` holds; where local integrability of
`iteratedTailIntegral f n` on `[x, ∞)` fails, truncated integrals vanish for large `R` by Mathlib's
`intervalIntegral.integral_undef` convention and the limit holds vacuously with value `0`. -/
theorem tendsto_intervalIntegral_iteratedTailIntegral {c p α₀ : ℝ} {f : ℝ → ℝ}
    (hc : c ≠ 0) (hp : 1 ≤ p) (hα : 0 < α₀ + p - 1)
    (hf : HasOscillatoryDecay c p α₀ f) (n : ℕ) (x : ℝ) :
    Tendsto (fun R : ℝ ↦ ∫ t in x..R, TauCeti.iteratedTailIntegral f n t) atTop
      (𝓝 (TauCeti.iteratedTailIntegral f (n + 1) x)) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpos : 0 < (α₀ + n * (p - 1)) + p - 1 := by
    have : 0 ≤ (n : ℝ) * (p - 1) := mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hp)
    linarith
  simpa only [← iteratedTailIntegral_succ] using
    (tendsto_and_hasOscillatoryDecay_one hc hp0 hpos (hf.iteratedTailIntegral hc hp hα n)).1 x

end HasOscillatoryDecay

end TauCeti
