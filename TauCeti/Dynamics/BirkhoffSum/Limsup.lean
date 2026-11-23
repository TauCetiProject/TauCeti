/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.Data.EReal.Operations
public import Mathlib.Order.LiminfLimsup
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Orbit invariance of extended-real `limsup` and `liminf` of Birkhoff averages

For any self-map `T : Ω → Ω` and any real-valued function `g : Ω → ℝ` (requiring no measure theory
or boundedness), shifting the starting point along an orbit from `x` to `T x` leaves both the
extended-real `limsup` and `liminf` of `birkhoffAverage ℝ T g n` unchanged.

## Main results

* `TauCeti.limsup_birkhoffAverage_comp` — orbit invariance of the extended-real `limsup` of
  Birkhoff averages.
* `TauCeti.liminf_birkhoffAverage_comp` — orbit invariance of the extended-real `liminf` of
  Birkhoff averages.
-/

public section

open Filter
open scoped Topology

namespace TauCeti

/-- Multiplying an `EReal`-valued sequence by factors in `[0, 1]` converging to `1` preserves
its `limsup`. -/
private lemma limsup_mul_eq_of_tendsto_one {u b : ℕ → EReal}
    (hb0 : 0 ≤ᶠ[atTop] b) (hb1 : b ≤ᶠ[atTop] 1) (hb : Tendsto b atTop (𝓝 1)) :
    limsup (u * b) atTop = limsup u atTop := by
  by_cases hu : ∃ᶠ n in atTop, 0 ≤ u n
  · exact le_antisymm
      ((EReal.limsup_mul_le hu hb0 (.inr (by rw [hb.limsup_eq]; exact EReal.coe_ne_top 1))
        (.inr (by simp [hb.limsup_eq]))).trans_eq (by rw [hb.limsup_eq, mul_one]))
      (by simpa [hb.liminf_eq] using EReal.le_limsup_mul hu hb0)
  · push Not at hu
    refine le_antisymm ?_ (limsup_le_limsup ?_)
    · have h1 := EReal.le_liminf_mul (u := -u) (hu.mono fun _ hn ↦ by simpa using hn.le) hb0
      have hneg : (-u) * b = -(u * b) := by ext n; simp [neg_mul]
      rwa [hb.liminf_eq, mul_one, hneg, EReal.liminf_neg, EReal.liminf_neg,
        EReal.neg_le_neg_iff] at h1
    · filter_upwards [hu, hb0, hb1] with n hnu hn0 hn1
      have hn0' : (0 : EReal) ≤ b n := hn0
      have hn1' : b n ≤ (1 : EReal) := hn1
      simp only [Pi.mul_apply]
      cases hx : u n with
      | bot => exact bot_le
      | top => simp [hx] at hnu
      | coe r =>
        have hr : r < 0 := EReal.coe_lt_coe_iff.mp (hx ▸ hnu)
        cases hy : b n with
        | bot => simp [hy] at hn0'
        | top => exact absurd (hy ▸ hn1') (not_le_of_gt (EReal.coe_lt_top 1))
        | coe s =>
          have hs1 : s ≤ 1 := by
            rw [hy, ← EReal.coe_one, EReal.coe_le_coe_iff] at hn1'
            exact hn1'
          rw [← EReal.coe_mul, EReal.coe_le_coe_iff]
          nlinarith

/-- The extended-real `limsup` of the Birkhoff averages of a real-valued function along a forward
orbit is invariant under shifting the starting point from `x` to `T x`. -/
theorem limsup_birkhoffAverage_comp {Ω : Type*} (T : Ω → Ω) (g : Ω → ℝ) (x : Ω) :
    limsup (fun n ↦ ((birkhoffAverage ℝ T g n (T x) : ℝ) : EReal)) atTop =
      limsup (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop := by
  -- Re-index `A_n(x)` to `A_{n+1}(x)` and decompose for `n ≠ 0`:
  --   `A_{n+1}(x) = A_n(T x) * (n / (n + 1)) + g x / (n + 1) = u n * b n + a n`,
  -- where `a n → 0` and `b n → 1` with `0 ≤ b n ≤ 1`.
  rw [← limsup_nat_add (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) 1]
  let u : ℕ → EReal := fun n ↦ ((birkhoffAverage ℝ T g n (T x) : ℝ) : EReal)
  let a : ℕ → EReal := fun n ↦ ((((n + 1 : ℕ) : ℝ)⁻¹ * g x : ℝ) : EReal)
  let b : ℕ → EReal := fun n ↦ (((n : ℝ) / ((n + 1 : ℕ) : ℝ) : ℝ) : EReal)
  have hinv : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ha : Tendsto a atTop (𝓝 0) :=
    EReal.tendsto_coe.mpr (by simpa using hinv.mul_const (g x))
  have hb : Tendsto b atTop (𝓝 1) := EReal.tendsto_coe.mpr <| by
    simpa only [Nat.cast_add, Nat.cast_one] using tendsto_natCast_div_add_atTop (1 : ℝ)
  have hb0 : 0 ≤ᶠ[atTop] b := Eventually.of_forall fun n ↦ EReal.coe_nonneg.mpr (by positivity)
  have hb1 : b ≤ᶠ[atTop] 1 := Eventually.of_forall fun n ↦ by
    change b n ≤ ((1 : ℝ) : EReal)
    rw [EReal.coe_le_coe_iff, div_le_one (by positivity)]
    push_cast; linarith
  have heq : (fun n ↦ ((birkhoffAverage ℝ T g (n + 1) x : ℝ) : EReal)) =ᶠ[atTop] u * b + a := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp only [Pi.add_apply, Pi.mul_apply, u, b, a, ← EReal.coe_mul, ← EReal.coe_add,
      EReal.coe_eq_coe_iff, birkhoffAverage, smul_eq_mul, birkhoffSum_succ_apply']
    field_simp [hn']; ring
  rw [limsup_congr heq]
  -- Drop the vanishing additive perturbation `a → 0`.
  have hadd : limsup (u * b + a) atTop = limsup (u * b) atTop := le_antisymm
    ((EReal.limsup_add_le (.inr (by simp [ha.limsup_eq]))
      (.inr (by simp [ha.limsup_eq]))).trans (by simp [ha.limsup_eq]))
    (by simpa [ha.liminf_eq] using EReal.le_limsup_add (u := u * b) (v := a) (f := atTop))
  rw [hadd, limsup_mul_eq_of_tendsto_one hb0 hb1 hb]

/-- The extended-real `liminf` of the Birkhoff averages of a real-valued function along a forward
orbit is invariant under shifting the starting point from `x` to `T x`. -/
theorem liminf_birkhoffAverage_comp {Ω : Type*} (T : Ω → Ω) (g : Ω → ℝ) (x : Ω) :
    liminf (fun n ↦ ((birkhoffAverage ℝ T g n (T x) : ℝ) : EReal)) atTop =
      liminf (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop := by
  have h (y : Ω) : (fun n ↦ ((birkhoffAverage ℝ T g n y : ℝ) : EReal)) =
      -(fun n ↦ ((birkhoffAverage ℝ T (-g) n y : ℝ) : EReal)) := by
    ext n; simp [birkhoffAverage_neg_apply]
  rw [h (T x), h x, EReal.liminf_neg, EReal.liminf_neg, limsup_birkhoffAverage_comp]

end TauCeti
