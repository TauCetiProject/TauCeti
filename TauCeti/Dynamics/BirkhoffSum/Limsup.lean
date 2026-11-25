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
import TauCeti.Topology.Instances.EReal

/-!
# Orbit invariance of extended-real `limsup` and `liminf` of Birkhoff averages

For any self-map `T : Ω → Ω` and any real-valued function `g : Ω → ℝ` (requiring no measure theory
or boundedness), shifting the starting point along an orbit from `x` to `T x` leaves both the
extended-real `limsup` and `liminf` of `birkhoffAverage ℝ T g n` unchanged.

## Main results

* `TauCeti.coe_birkhoffAverage_eq_neg_neg` — coercing the Birkhoff averages of `g` to `EReal`
  negates the coerced Birkhoff averages of `-g`.
* `TauCeti.limsup_birkhoffAverage_apply_eq_limsup_birkhoffAverage` — orbit invariance of the
  extended-real `limsup` of Birkhoff averages.
* `TauCeti.liminf_birkhoffAverage_apply_eq_liminf_birkhoffAverage` — orbit invariance of the
  extended-real `liminf` of Birkhoff averages.
-/

public section

open Filter
open scoped Topology

namespace TauCeti

/-- Coercing the Birkhoff averages of `g` to `EReal` negates the coerced Birkhoff averages of
`-g`. -/
theorem coe_birkhoffAverage_eq_neg_neg {Ω : Type*} (T : Ω → Ω) (g : Ω → ℝ) (x : Ω) :
    (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) =
      -(fun n ↦ ((birkhoffAverage ℝ T (-g) n x : ℝ) : EReal)) := by
  ext n
  simp [birkhoffAverage_neg_apply]

/-- The extended-real `limsup` of the Birkhoff averages of a real-valued function along a forward
orbit is invariant under shifting the starting point from `x` to `T x`. -/
theorem limsup_birkhoffAverage_apply_eq_limsup_birkhoffAverage {Ω : Type*} (T : Ω → Ω)
    (g : Ω → ℝ) (x : Ω) :
    limsup (fun n ↦ ((birkhoffAverage ℝ T g n (T x) : ℝ) : EReal)) atTop =
      limsup (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop := by
  -- Re-index `A_n(x)` to `A_{n+1}(x)` and decompose for `n ≠ 0`:
  --   `A_{n+1}(x) = A_n(T x) * (n / (n + 1)) + g x / (n + 1) = u n * b n + a n`,
  -- where `a n → 0` and `b n → 1`.
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
  rw [hadd, EReal.limsup_mul_eq_of_tendsto_one hb]

/-- The extended-real `liminf` of the Birkhoff averages of a real-valued function along a forward
orbit is invariant under shifting the starting point from `x` to `T x`. -/
theorem liminf_birkhoffAverage_apply_eq_liminf_birkhoffAverage {Ω : Type*} (T : Ω → Ω)
    (g : Ω → ℝ) (x : Ω) :
    liminf (fun n ↦ ((birkhoffAverage ℝ T g n (T x) : ℝ) : EReal)) atTop =
      liminf (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop := by
  rw [coe_birkhoffAverage_eq_neg_neg T g (T x), coe_birkhoffAverage_eq_neg_neg T g x,
    EReal.liminf_neg, EReal.liminf_neg, limsup_birkhoffAverage_apply_eq_limsup_birkhoffAverage]

end TauCeti
