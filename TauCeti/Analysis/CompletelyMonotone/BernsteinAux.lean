/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import TauCeti.Analysis.CompletelyMonotone.Basic

/-!
# Analytic lemmas for Bernstein's representation theorem

Auxiliary analytic facts about `TauCeti.IsCompletelyMonotone` used by the Chafaï-style
construction of the representing measure (`CompletelyMonotone/BernsteinMeasures.lean` and the
Bernstein representation theorem). These extend the object API in
`CompletelyMonotone/Basic.lean` with the integral/Taylor layer: the limit at infinity, the
fundamental-theorem identity `f(x) - f(T) = ∫ₓᵀ (-f')`, and the sign of the Taylor integral
remainder.

Ported from the sorry-free `mrdouglasny/hille-yosida` development (`HilleYosida.BernsteinBasic`),
whose `IsCompletelyMonotone` is the same predicate; the basic sign/monotonicity lemmas it ports
already live in `Basic.lean`, so only the analytic extras appear here.

## Main declarations

* `TauCeti.IsCompletelyMonotone.bounded`: `f t ≤ f 0` on `[0, ∞)`.
* `TauCeti.IsCompletelyMonotone.tendsto_atTop`: `f` has a limit `L ≥ 0` at infinity.
* `TauCeti.IsCompletelyMonotone.iteratedDerivWithin_Icc_eq_Ici`: iterated derivatives within
  `Icc x T` and within `Ici 0` agree at interior points.
* `TauCeti.IsCompletelyMonotone.taylor_nonneg_remainder`: the Taylor integral remainder has
  sign `(-1)ⁿ`.
* `TauCeti.IsCompletelyMonotone.integral_neg_deriv`, `TauCeti.IsCompletelyMonotone.integral_mass`:
  `f(x) - f(T) = ∫ₓᵀ (-f')`, and the total-mass identity on `[0, T]`.

## References

* D. V. Widder, *The Laplace Transform* (Princeton, 1941), Ch. IV.
* D. Chafaï, *Aspects of the Bernstein theorem* (2013).
-/

public section

open MeasureTheory Set intervalIntegral Filter
open scoped ContDiff Topology

namespace TauCeti

variable {f : ℝ → ℝ}

namespace IsCompletelyMonotone

/-- A completely monotone function is bounded by its value at `0` on `[0, ∞)`. -/
lemma bounded (hf : IsCompletelyMonotone f) {t : ℝ} (ht : 0 ≤ t) : f t ≤ f 0 :=
  hf.antitoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht

/-- A completely monotone function has a limit `L ≥ 0` at infinity: it is antitone on `[0, ∞)`
and bounded below by `0`. -/
lemma tendsto_atTop (hf : IsCompletelyMonotone f) :
    ∃ L, Tendsto f atTop (nhds L) ∧ 0 ≤ L := by
  have hanti := hf.antitoneOn
  set g := fun t : ℝ => f (max t 0) with hg
  have hg_anti : Antitone g := fun a b hab =>
    hanti (mem_Ici.mpr (le_max_right _ _)) (mem_Ici.mpr (le_max_right _ _))
      (max_le_max_right 0 hab)
  have hg_bdd : BddBelow (Set.range g) :=
    ⟨0, fun _ ⟨t, ht⟩ => ht ▸ hf.nonneg (le_max_right _ _)⟩
  refine ⟨⨅ i, g i, ?_, le_ciInf (fun _ => hf.nonneg (le_max_right _ _))⟩
  exact (tendsto_atTop_ciInf hg_anti hg_bdd).congr'
    (eventually_atTop.mpr ⟨0, fun t ht => by simp [hg, max_eq_left ht]⟩)

/-- `iteratedDerivWithin` on `Icc x T` agrees with `iteratedDerivWithin` on `Ici 0` at interior
points, since both equal `iteratedDeriv n f t` when `0 < t`. -/
lemma iteratedDerivWithin_Icc_eq_Ici {n : ℕ} (hf : IsCompletelyMonotone f)
    {x T t : ℝ} (hx : 0 ≤ x) (hxT : x < T) (ht : t ∈ Ioo x T) :
    iteratedDerivWithin n f (Icc x T) t = iteratedDerivWithin n f (Ici 0) t := by
  have ht_pos : 0 < t := lt_of_le_of_lt hx ht.1
  have hcda : ContDiffAt ℝ (n : WithTop ℕ∞) f t :=
    (hf.contDiffOn.contDiffAt (Ici_mem_nhds ht_pos)).of_le (by exact_mod_cast le_top)
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hxT) hcda
        (Ioo_subset_Icc_self ht),
      ← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcda
        (mem_Ici.mpr ht_pos.le)]

/-- **CM sign of the Taylor remainder.** For a completely monotone function the Taylor integral
remainder `∫ₓᵀ (T-t)ⁿ⁻¹/(n-1)! · f⁽ⁿ⁾(t) dt` has sign `(-1)ⁿ`. Uses
`iteratedDerivWithin_Icc_eq_Ici` (set transfer at interior points) and `Ioo_ae_eq_Icc`
(the boundary is Lebesgue-null). -/
lemma taylor_nonneg_remainder (hf : IsCompletelyMonotone f) {x T : ℝ} {n : ℕ}
    (hx : 0 ≤ x) (hxT : x < T) :
    0 ≤ (-1 : ℝ) ^ n * ∫ t in x..T,
      (↑(n - 1).factorial)⁻¹ * (T - t) ^ (n - 1) *
      iteratedDerivWithin n f (Icc x T) t := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_nonneg_of_ae_restrict hxT.le
  have hIoo : ∀ t ∈ Ioo x T, (0 : ℝ) ≤ ((-1 : ℝ) ^ n *
      ((↑(n - 1).factorial)⁻¹ * (T - t) ^ (n - 1) *
        iteratedDerivWithin n f (Icc x T) t)) := fun t ht =>
    calc (0 : ℝ) ≤ (↑(n - 1).factorial)⁻¹ * (T - t) ^ (n - 1) *
          ((-1 : ℝ) ^ n * iteratedDerivWithin n f (Icc x T) t) :=
          mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
            (pow_nonneg (sub_nonneg.mpr ht.2.le) _))
            (by rw [hf.iteratedDerivWithin_Icc_eq_Ici hx hxT ht]
                exact hf.neg_one_pow_mul_iteratedDerivWithin_nonneg n
                  (lt_of_le_of_lt hx ht.1).le)
      _ = _ := by ring
  have h_mem : ∀ᵐ t ∂volume.restrict (Icc x T), t ∈ Ioo x T := by
    rw [ae_restrict_iff' measurableSet_Icc]
    exact (Ioo_ae_eq_Icc (a := x) (b := T)).mono (fun t h ht => h.mpr ht)
  exact h_mem.mono fun t ht => by simp only [Pi.zero_apply]; exact hIoo t ht

/-- For a completely monotone `f` the `n = 1` fundamental-theorem identity gives
`f(x) - f(T) = ∫ₓᵀ (-f'(t)) dt`, with the integrand nonnegative by the sign condition. -/
lemma integral_neg_deriv (hf : IsCompletelyMonotone f)
    (x T : ℝ) (hx : 0 ≤ x) (hxT : x < T) :
    f x - f T = ∫ t in x..T, -iteratedDerivWithin 1 f (Icc x T) t := by
  have hsubset : Icc x T ⊆ Ici 0 := Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hx)
  have hcm_Icc : ContDiffOn ℝ 1 f (Icc x T) :=
    (hf.contDiffOn.mono hsubset).of_le (by exact_mod_cast le_top)
  have hud : UniqueDiffOn ℝ (Icc x T) := uniqueDiffOn_Icc hxT
  have hf_cont : ContinuousOn f (Icc x T) := hcm_Icc.continuousOn
  have hf_diff : DifferentiableOn ℝ f (Icc x T) := hcm_Icc.differentiableOn (by norm_num)
  have hdw_cont : ContinuousOn (iteratedDerivWithin 1 f (Icc x T)) (Icc x T) :=
    hcm_Icc.continuousOn_iteratedDerivWithin (by norm_num) hud
  have hderiv_right : ∀ t ∈ Ioo x T,
      HasDerivWithinAt f (iteratedDerivWithin 1 f (Icc x T) t) (Ioi t) t := by
    intro t ht
    rw [iteratedDerivWithin_one]
    exact ((hf_diff t (Ioo_subset_Icc_self ht)).hasDerivWithinAt.hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)).hasDerivWithinAt
  have hint : IntervalIntegrable (iteratedDerivWithin 1 f (Icc x T)) volume x T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxT.le enorm_ne_top]
    exact hdw_cont.integrableOn_compact isCompact_Icc
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hxT.le hf_cont
    hderiv_right hint
  rw [intervalIntegral.integral_neg]
  linarith [hFTC]

/-- The total mass identity `∫₀ᵀ (-f') = f(0) - f(T)` for a completely monotone function. -/
lemma integral_mass (hf : IsCompletelyMonotone f) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Icc 0 T) t = f 0 - f T := by
  linarith [hf.integral_neg_deriv 0 T le_rfl hT]

end IsCompletelyMonotone

end TauCeti
