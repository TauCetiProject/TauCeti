/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.Data.EReal.Operations
public import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Orbit invariance of extended-real `limsup` and `liminf` of Birkhoff averages

For any self-map `T : Ω → Ω` and any real-valued function `g : Ω → ℝ` (requiring no measure theory
or boundedness), shifting the starting point along an orbit from `x` to `T x` leaves both the
extended-real `limsup` and `liminf` of `birkhoffAverage ℝ T g n` unchanged.

## Main results

* `TauCeti.liminf_birkhoffAverage_eq_neg_limsup_neg` — the `liminf` of the Birkhoff averages of `g`
  equals the negation of the `limsup` of the Birkhoff averages of `-g`.
* `TauCeti.limsup_birkhoffAverage_comp` — orbit invariance of the extended-real `limsup` of
  Birkhoff averages.
* `TauCeti.liminf_birkhoffAverage_comp` — orbit invariance of the extended-real `liminf` of
  Birkhoff averages.
-/

public section

open Filter
open scoped Topology

namespace TauCeti

/-- The extended-real `liminf` of the Birkhoff averages of `g` equals the negation of the `limsup`
of the Birkhoff averages of `-g`. -/
theorem liminf_birkhoffAverage_eq_neg_limsup_neg {Ω : Type*} (T : Ω → Ω) (g : Ω → ℝ) (x : Ω) :
    liminf (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop =
      -limsup (fun n ↦ ((birkhoffAverage ℝ T (-g) n x : ℝ) : EReal)) atTop := by
  rw [← EReal.liminf_neg]
  refine congrArg (liminf · atTop) (funext fun n ↦ ?_)
  simp [birkhoffAverage_neg_apply]

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
  have hinv : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp (tendsto_add_atTop_nat 1)
  have ha : Tendsto a atTop (𝓝 0) :=
    EReal.tendsto_coe.mpr (by simpa using hinv.mul_const (g x))
  have hb : Tendsto b atTop (𝓝 1) := EReal.tendsto_coe.mpr <|
    (by simpa using tendsto_const_nhds.sub hinv :
      Tendsto (fun n : ℕ ↦ (1 : ℝ) - ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 1)).congr fun n ↦ by
      have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
      push_cast; field_simp [hn]; ring
  have hb0 : 0 ≤ᶠ[atTop] b := Eventually.of_forall fun n ↦ EReal.coe_nonneg.mpr (by positivity)
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
  rw [hadd]
  -- Drop the multiplicative factor `b → 1` (`0 ≤ b ≤ 1`) by splitting on the sign of `u n`:
  -- * if `0 ≤ u n` frequently, `EReal.limsup_mul_le` and `EReal.le_limsup_mul` apply directly;
  -- * if `u n < 0` eventually, `b n ≤ 1` yields `u n ≤ u n * b n` pointwise, while applying
  --   `EReal.le_liminf_mul` to `-u ≥ 0` and negating yields `limsup (u * b) ≤ limsup u`.
  by_cases hu : ∃ᶠ n in atTop, 0 ≤ u n
  · exact (le_antisymm
      ((EReal.limsup_mul_le hu hb0 (.inr (by rw [hb.limsup_eq]; exact EReal.coe_ne_top 1))
        (.inr (by simp [hb.limsup_eq]))).trans_eq (by rw [hb.limsup_eq, mul_one]))
      (by simpa [hb.liminf_eq] using EReal.le_limsup_mul hu hb0)).symm
  · push Not at hu
    refine le_antisymm (limsup_le_limsup <| hu.mono fun n hn ↦ ?_) ?_
    · have hn' : birkhoffAverage ℝ T g n (T x) < 0 := EReal.coe_lt_coe_iff.mp hn
      have hb1 : (n : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]; push_cast; linarith
      exact EReal.coe_le_coe_iff.mpr (by nlinarith)
    · have h1 := EReal.le_liminf_mul (u := -u) (hu.mono fun _ hn ↦ by simpa using hn.le) hb0
      have hneg : (-u) * b = -(u * b) := by ext n; simp [neg_mul]
      rwa [hb.liminf_eq, mul_one, hneg, EReal.liminf_neg, EReal.liminf_neg,
        EReal.neg_le_neg_iff] at h1

/-- The extended-real `liminf` of the Birkhoff averages of a real-valued function along a forward
orbit is invariant under shifting the starting point from `x` to `T x`. -/
theorem liminf_birkhoffAverage_comp {Ω : Type*} (T : Ω → Ω) (g : Ω → ℝ) (x : Ω) :
    liminf (fun n ↦ ((birkhoffAverage ℝ T g n (T x) : ℝ) : EReal)) atTop =
      liminf (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop := by
  rw [liminf_birkhoffAverage_eq_neg_limsup_neg, liminf_birkhoffAverage_eq_neg_limsup_neg,
    limsup_birkhoffAverage_comp]

end TauCeti
