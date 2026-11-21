/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Hyperbolic.Basic
import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import Mathlib.Tactic.FieldSimp

/-!
# The positive-real hyperbolic projection parameter family

In `TauCeti.Algebra.TypeAHeckeAlgebra.Hyperbolic.Basic`, at the Hecke parameter `q = exp (-θ)` and
rescaled braid generators `γ i = I * exp (-α) • T i`, the positive and negative stabilization
constants of a Markov trace with native projection parameter `η` agree (when `cosh α * cosh θ ≠ 0`)
if and only if `η = (1 - tanh α * tanh θ) / 2` (`TauCeti.hyperbolicProjParam`), while the
complementary projection convention assigns `1 - η = (1 + tanh α * tanh θ) / 2`
(`TauCeti.hyperbolicWenzlProjParam`).

This file develops the real parameter family `α, θ ∈ ℝ` (`Q = exp (-2 * θ) > 0`), without any
Wenzl-parameter or root-of-unity dependencies:

* For `0 < θ`, `α ↦ (1 - Real.tanh α * Real.tanh θ) / 2` is a strictly decreasing bijection from
  `ℝ` onto the open interval `(Q / (1 + Q), 1 / (1 + Q))`, with `α → ±∞` endpoint limits
  `Q / (1 + Q)` and `1 / (1 + Q)`.
* For every real `θ`, the closure of the range is `[min (1 / (1 + Q)) (Q / (1 + Q)),
  max (1 / (1 + Q)) (Q / (1 + Q))]` (reducing to `{1 / 2}` at `θ = 0`, `Q = 1`), and its endpoints
  `sInf` and `sSup` tend to `0` and `1` as `θ → ±∞`.

## Main definitions

* `TauCeti.realHyperbolicProjParam`: the real native hyperbolic projection parameter
  `(1 - Real.tanh α * Real.tanh θ) / 2`.
* `TauCeti.realHyperbolicWenzlProjParam`: the real complementary hyperbolic projection parameter
  `(1 + Real.tanh α * Real.tanh θ) / 2`.

## Main results

* `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_hyperbolicGen_ofReal_eq_iff`: for real
  `α, θ`, the stabilization constants agree if and only if `η = realHyperbolicProjParam α θ`.
* `TauCeti.tendsto_realHyperbolicProjParam_atTop` and
  `TauCeti.tendsto_realHyperbolicProjParam_atBot`: the `α → ±∞` endpoint limits.
* `TauCeti.bijOn_realHyperbolicProjParam`, `TauCeti.range_realHyperbolicProjParam_of_ne_zero`, and
  `TauCeti.closure_range_realHyperbolicProjParam`: the monotone bijection onto the open interval
  for `0 < θ` and its range and closure for every real `θ`.
* `TauCeti.sInf_range_realHyperbolicProjParam`, `TauCeti.sSup_range_realHyperbolicProjParam`, and
  `TauCeti.tendsto_sInf_range_realHyperbolicProjParam_atTop`: the interval endpoints and their
  scalar limits `{0, 1}` as `θ → ±∞`.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Section 6.
* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §§2–3.
-/

public section

open Complex
open scoped Real Topology

namespace TauCeti

/-- The real native hyperbolic projection parameter `(1 - Real.tanh α * Real.tanh θ) / 2`. -/
noncomputable def realHyperbolicProjParam (α θ : ℝ) : ℝ :=
  (1 - Real.tanh α * Real.tanh θ) / 2

/-- The real Wenzl hyperbolic projection parameter `(1 + Real.tanh α * Real.tanh θ) / 2`. -/
noncomputable def realHyperbolicWenzlProjParam (α θ : ℝ) : ℝ :=
  (1 + Real.tanh α * Real.tanh θ) / 2

/-- Defining formula for `realHyperbolicProjParam`. -/
theorem realHyperbolicProjParam_def (α θ : ℝ) :
    realHyperbolicProjParam α θ = (1 - Real.tanh α * Real.tanh θ) / 2 := (rfl)

/-- Defining formula for `realHyperbolicWenzlProjParam`. -/
theorem realHyperbolicWenzlProjParam_def (α θ : ℝ) :
    realHyperbolicWenzlProjParam α θ = (1 + Real.tanh α * Real.tanh θ) / 2 := (rfl)

/-- Coercion of `realHyperbolicProjParam` to `ℂ` agrees with `hyperbolicProjParam`. -/
@[simp]
theorem ofReal_realHyperbolicProjParam (α θ : ℝ) :
    (realHyperbolicProjParam α θ : ℂ) = hyperbolicProjParam α θ := by
  simp [realHyperbolicProjParam_def, hyperbolicProjParam_def]

/-- Coercion of `realHyperbolicWenzlProjParam` to `ℂ` agrees with `hyperbolicWenzlProjParam`. -/
@[simp]
theorem ofReal_realHyperbolicWenzlProjParam (α θ : ℝ) :
    (realHyperbolicWenzlProjParam α θ : ℂ) = hyperbolicWenzlProjParam α θ := by
  simp [realHyperbolicWenzlProjParam_def, hyperbolicWenzlProjParam_def]

/-- `realHyperbolicWenzlProjParam` is `1` minus `realHyperbolicProjParam`. -/
theorem realHyperbolicWenzlProjParam_eq_one_sub (α θ : ℝ) :
    realHyperbolicWenzlProjParam α θ = 1 - realHyperbolicProjParam α θ := by
  rw [realHyperbolicWenzlProjParam_def, realHyperbolicProjParam_def]
  ring

/-- The real native and Wenzl hyperbolic projection parameters sum to `1`. -/
theorem realHyperbolicProjParam_add_realHyperbolicWenzlProjParam (α θ : ℝ) :
    realHyperbolicProjParam α θ + realHyperbolicWenzlProjParam α θ = 1 := by
  rw [realHyperbolicWenzlProjParam_eq_one_sub]
  ring

/-- Negating `α` exchanges the real native and Wenzl hyperbolic projection parameters. -/
@[simp]
theorem realHyperbolicProjParam_neg_left (α θ : ℝ) :
    realHyperbolicProjParam (-α) θ = realHyperbolicWenzlProjParam α θ := by
  simp [realHyperbolicProjParam_def, realHyperbolicWenzlProjParam_def, Real.tanh_neg,
    sub_eq_add_neg]

/-- Negating `θ` exchanges the real native and Wenzl hyperbolic projection parameters. -/
@[simp]
theorem realHyperbolicProjParam_neg_right (α θ : ℝ) :
    realHyperbolicProjParam α (-θ) = realHyperbolicWenzlProjParam α θ := by
  simp [realHyperbolicProjParam_def, realHyperbolicWenzlProjParam_def, Real.tanh_neg,
    sub_eq_add_neg]

/-- Negating `α` turns the real Wenzl hyperbolic projection parameter into the native one. -/
@[simp]
theorem realHyperbolicWenzlProjParam_neg_left (α θ : ℝ) :
    realHyperbolicWenzlProjParam (-α) θ = realHyperbolicProjParam α θ := by
  simp [realHyperbolicProjParam_def, realHyperbolicWenzlProjParam_def, Real.tanh_neg,
    sub_eq_add_neg]

/-- Negating `θ` turns the real Wenzl hyperbolic projection parameter into the native one. -/
@[simp]
theorem realHyperbolicWenzlProjParam_neg_right (α θ : ℝ) :
    realHyperbolicWenzlProjParam α (-θ) = realHyperbolicProjParam α θ := by
  simp [realHyperbolicProjParam_def, realHyperbolicWenzlProjParam_def, Real.tanh_neg,
    sub_eq_add_neg]

/-- Negating both `α` and `θ` leaves `realHyperbolicProjParam` unchanged. -/
theorem realHyperbolicProjParam_neg_neg (α θ : ℝ) :
    realHyperbolicProjParam (-α) (-θ) = realHyperbolicProjParam α θ := by
  simp

/-- At `α = 0`, `realHyperbolicProjParam 0 θ = 1 / 2` for every real `θ`. -/
@[simp]
theorem realHyperbolicProjParam_zero_left (θ : ℝ) : realHyperbolicProjParam 0 θ = 1 / 2 := by
  simp [realHyperbolicProjParam_def]

/-- At `θ = 0` (`Q = 1`), `realHyperbolicProjParam α 0 = 1 / 2` for every real `α`. -/
@[simp]
theorem realHyperbolicProjParam_zero_right (α : ℝ) : realHyperbolicProjParam α 0 = 1 / 2 := by
  simp [realHyperbolicProjParam_def]

/-- At `α = 0`, `realHyperbolicWenzlProjParam 0 θ = 1 / 2` for every real `θ`. -/
@[simp]
theorem realHyperbolicWenzlProjParam_zero_left (θ : ℝ) :
    realHyperbolicWenzlProjParam 0 θ = 1 / 2 := by
  simp [realHyperbolicWenzlProjParam_def]

/-- At `θ = 0` (`Q = 1`), `realHyperbolicWenzlProjParam α 0 = 1 / 2` for every real `α`. -/
@[simp]
theorem realHyperbolicWenzlProjParam_zero_right (α : ℝ) :
    realHyperbolicWenzlProjParam α 0 = 1 / 2 := by
  simp [realHyperbolicWenzlProjParam_def]

/-- On the real hyperbolic family (`α, θ ∈ ℝ`), no nonvanishing side-conditions are needed: the
stabilization constants of a Markov trace with native parameter `η` agree if and only if
`η = realHyperbolicProjParam α θ`. -/
theorem InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_hyperbolicGen_ofReal_eq_iff {α θ : ℝ}
    {z η : ℂ} {τ : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam θ) →ₗ[ℂ] ℂ}
    (hτ : InfiniteTypeAHeckeAlgebra.IsMarkovTrace z τ)
    (hz : z = exp (-(θ : ℂ)) * η - exp (θ : ℂ) * (1 - η)) (n : ℕ) :
    τ (InfiniteTypeAHeckeAlgebra.hyperbolicGen α θ n) =
        τ ↑(InfiniteTypeAHeckeAlgebra.hyperbolicGen α θ n)⁻¹ ↔
      η = realHyperbolicProjParam α θ := by
  rw [hτ.map_hyperbolicGen_eq_map_inv_iff hz (cosh_ofReal_ne_zero α) (cosh_ofReal_ne_zero θ) n,
    ofReal_realHyperbolicProjParam]

/-- Negating `θ` leaves the range of `α ↦ realHyperbolicProjParam α θ` unchanged. -/
theorem range_realHyperbolicProjParam_neg (θ : ℝ) :
    (Set.range fun α ↦ realHyperbolicProjParam α (-θ)) =
      Set.range fun α ↦ realHyperbolicProjParam α θ := by
  ext y
  refine ⟨fun ⟨α, hα⟩ ↦ ⟨-α, ?_⟩, fun ⟨α, hα⟩ ↦ ⟨-α, ?_⟩⟩
  · dsimp only at hα ⊢
    rw [← realHyperbolicProjParam_neg_neg (-α) θ, neg_neg, hα]
  · dsimp only at hα ⊢
    rw [realHyperbolicProjParam_neg_neg α θ, hα]

/-- **Upper-`α` endpoint limit.** For every real `θ`, as `α → +∞`, `realHyperbolicProjParam α θ`
tends to `exp (-2 * θ) / (1 + exp (-2 * θ))`. -/
theorem tendsto_realHyperbolicProjParam_atTop (θ : ℝ) :
    Filter.Tendsto (fun α ↦ realHyperbolicProjParam α θ) Filter.atTop
      (𝓝 (Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ)))) := by
  simp_rw [realHyperbolicProjParam_def]
  have hend : (1 - 1 * Real.tanh θ) / 2 = Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ)) := by
    rw [one_mul, Real.one_sub_tanh_div_two]
  rw [← hend]
  exact (tendsto_const_nhds.sub (Real.tendsto_tanh_atTop.mul_const _)).div_const 2

/-- **Lower-`α` endpoint limit.** For every real `θ`, as `α → -∞`, `realHyperbolicProjParam α θ`
tends to `1 / (1 + exp (-2 * θ))`. -/
theorem tendsto_realHyperbolicProjParam_atBot (θ : ℝ) :
    Filter.Tendsto (fun α ↦ realHyperbolicProjParam α θ) Filter.atBot
      (𝓝 (1 / (1 + Real.exp (-2 * θ)))) := by
  simp_rw [realHyperbolicProjParam_def]
  have hend : (1 - (-1) * Real.tanh θ) / 2 = 1 / (1 + Real.exp (-2 * θ)) := by
    rw [neg_one_mul, sub_neg_eq_add, Real.one_add_tanh_div_two]
  rw [← hend]
  exact (tendsto_const_nhds.sub (Real.tendsto_tanh_atBot.mul_const _)).div_const 2

/-- For every real `θ`, as `α → +∞`, `realHyperbolicWenzlProjParam α θ` tends to
`1 / (1 + exp (-2 * θ))`. -/
theorem tendsto_realHyperbolicWenzlProjParam_atTop (θ : ℝ) :
    Filter.Tendsto (fun α ↦ realHyperbolicWenzlProjParam α θ) Filter.atTop
      (𝓝 (1 / (1 + Real.exp (-2 * θ)))) := by
  simpa [Function.comp_def] using
    (tendsto_realHyperbolicProjParam_atBot θ).comp Filter.tendsto_neg_atTop_atBot

/-- For every real `θ`, as `α → -∞`, `realHyperbolicWenzlProjParam α θ` tends to
`exp (-2 * θ) / (1 + exp (-2 * θ))`. -/
theorem tendsto_realHyperbolicWenzlProjParam_atBot (θ : ℝ) :
    Filter.Tendsto (fun α ↦ realHyperbolicWenzlProjParam α θ) Filter.atBot
      (𝓝 (Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ)))) := by
  simpa [Function.comp_def] using
    (tendsto_realHyperbolicProjParam_atTop θ).comp Filter.tendsto_neg_atBot_atTop

/-- For `0 < θ`, `α ↦ realHyperbolicProjParam α θ` is strictly decreasing. -/
theorem strictAnti_realHyperbolicProjParam {θ : ℝ} (hθ : 0 < θ) :
    StrictAnti fun α ↦ realHyperbolicProjParam α θ := by
  have ht : 0 < Real.tanh θ := by simpa using Real.tanh_strictMono hθ
  intro a b hab
  have h := mul_lt_mul_of_pos_right (Real.tanh_strictMono hab) ht
  dsimp only
  rw [realHyperbolicProjParam_def, realHyperbolicProjParam_def]
  linarith

/-- For `0 < θ`, `α ↦ realHyperbolicWenzlProjParam α θ` is strictly increasing. -/
theorem strictMono_realHyperbolicWenzlProjParam {θ : ℝ} (hθ : 0 < θ) :
    StrictMono fun α ↦ realHyperbolicWenzlProjParam α θ := by
  intro a b hab
  simpa only [realHyperbolicWenzlProjParam_eq_one_sub, sub_lt_sub_iff_left] using
    strictAnti_realHyperbolicProjParam hθ hab

/-- **Positive-real interval bijection (`0 < θ`).** For `0 < θ` (so `Q = exp (-2 * θ) ∈ (0, 1)`),
`α ↦ realHyperbolicProjParam α θ` is a bijection from `ℝ` onto the open interval
`(Q / (1 + Q), 1 / (1 + Q))`. -/
theorem bijOn_realHyperbolicProjParam {θ : ℝ} (hθ : 0 < θ) :
    Set.BijOn (fun α ↦ realHyperbolicProjParam α θ) Set.univ
      (Set.Ioo (Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ))) (1 / (1 + Real.exp (-2 * θ)))) := by
  have ht : 0 < Real.tanh θ := by simpa using Real.tanh_strictMono hθ
  refine ⟨fun α _ ↦ ?_, (strictAnti_realHyperbolicProjParam hθ).injective.injOn, fun η hη ↦ ?_⟩
  · dsimp only
    rw [Set.mem_Ioo, ← Real.one_sub_tanh_div_two, ← Real.one_add_tanh_div_two,
      realHyperbolicProjParam_def]
    exact ⟨by nlinarith [Real.tanh_lt_one α], by nlinarith [Real.neg_one_lt_tanh α]⟩
  · rw [Set.mem_Ioo, ← Real.one_sub_tanh_div_two, ← Real.one_add_tanh_div_two] at hη
    let t := (1 - 2 * η) / Real.tanh θ
    have ht_mem : t ∈ Set.Ioo (-1 : ℝ) 1 := by
      rw [Set.mem_Ioo, lt_div_iff₀ ht, div_lt_iff₀ ht]
      exact ⟨by linarith [hη.2], by linarith [hη.1]⟩
    refine ⟨Real.artanh t, Set.mem_univ _, ?_⟩
    dsimp only
    rw [realHyperbolicProjParam_def, Real.tanh_artanh ht_mem]
    dsimp only [t]
    field_simp [ht.ne']
    ring

/-- For `0 < θ`, Wenzl's parameter `α ↦ realHyperbolicWenzlProjParam α θ` is also a bijection from
`ℝ` onto `(exp (-2 * θ) / (1 + exp (-2 * θ)), 1 / (1 + exp (-2 * θ)))`. -/
theorem bijOn_realHyperbolicWenzlProjParam {θ : ℝ} (hθ : 0 < θ) :
    Set.BijOn (fun α ↦ realHyperbolicWenzlProjParam α θ) Set.univ
      (Set.Ioo (Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ))) (1 / (1 + Real.exp (-2 * θ)))) := by
  have hneg : Set.BijOn Neg.neg (Set.univ : Set ℝ) Set.univ :=
    ⟨fun _ _ ↦ trivial, neg_injective.injOn, fun x _ ↦ ⟨-x, trivial, neg_neg x⟩⟩
  simpa [Function.comp_def] using (bijOn_realHyperbolicProjParam hθ).comp hneg

/-- For `0 < θ`, the range of `α ↦ realHyperbolicProjParam α θ` is
`(exp (-2 * θ) / (1 + exp (-2 * θ)), 1 / (1 + exp (-2 * θ)))`. -/
theorem range_realHyperbolicProjParam_of_pos {θ : ℝ} (hθ : 0 < θ) :
    Set.range (fun α ↦ realHyperbolicProjParam α θ) =
      Set.Ioo (Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ))) (1 / (1 + Real.exp (-2 * θ))) := by
  rw [← Set.image_univ]
  exact (bijOn_realHyperbolicProjParam hθ).image_eq

/-- For every nonzero real `θ`, the range of `α ↦ realHyperbolicProjParam α θ` is the open interval
between `1 / (1 + exp (-2 * θ))` and `exp (-2 * θ) / (1 + exp (-2 * θ))`. -/
theorem range_realHyperbolicProjParam_of_ne_zero {θ : ℝ} (hθ : θ ≠ 0) :
    Set.range (fun α ↦ realHyperbolicProjParam α θ) =
      Set.Ioo (min (1 / (1 + Real.exp (-2 * θ))) (Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ))))
        (max (1 / (1 + Real.exp (-2 * θ))) (Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ)))) := by
  rcases lt_or_gt_of_ne hθ with hlt | hgt
  · have hpos : 0 < -θ := neg_pos.2 hlt
    have hQ₁ : Real.exp (-2 * (-θ)) / (1 + Real.exp (-2 * (-θ))) =
        1 / (1 + Real.exp (-2 * θ)) := by
      rw [← Real.one_sub_tanh_div_two, Real.tanh_neg, sub_neg_eq_add, Real.one_add_tanh_div_two]
    have hQ₂ : 1 / (1 + Real.exp (-2 * (-θ))) =
        Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ)) := by
      rw [← Real.one_add_tanh_div_two, Real.tanh_neg, ← sub_eq_add_neg, Real.one_sub_tanh_div_two]
    have hle : 1 / (1 + Real.exp (-2 * θ)) ≤ Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ)) :=
      div_le_div_of_nonneg_right (Real.one_le_exp (by linarith)) (by positivity)
    rw [← range_realHyperbolicProjParam_neg, range_realHyperbolicProjParam_of_pos hpos, hQ₁, hQ₂,
      min_eq_left hle, max_eq_right hle]
  · have hle : Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ)) ≤ 1 / (1 + Real.exp (-2 * θ)) :=
      div_le_div_of_nonneg_right (Real.exp_le_one_iff.2 (by linarith)) (by positivity)
    rw [range_realHyperbolicProjParam_of_pos hgt, min_eq_right hle, max_eq_left hle]

/-- **Closure of the real hyperbolic family.** For every real `θ` (including `θ = 0`, where both
sides equal `{1 / 2}`), the closure of the range of `α ↦ realHyperbolicProjParam α θ` is the closed
interval `[min (1 / (1 + Q)) (Q / (1 + Q)), max (1 / (1 + Q)) (Q / (1 + Q))]` at
`Q = exp (-2 * θ)`. -/
theorem closure_range_realHyperbolicProjParam (θ : ℝ) :
    closure (Set.range fun α ↦ realHyperbolicProjParam α θ) =
      Set.Icc (min (1 / (1 + Real.exp (-2 * θ))) (Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ))))
        (max (1 / (1 + Real.exp (-2 * θ))) (Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ)))) := by
  rcases eq_or_ne θ 0 with rfl | hθ
  · simp [Set.range_const, one_add_one_eq_two]
  · have hlt := Set.nonempty_Ioo.1 (range_realHyperbolicProjParam_of_ne_zero hθ ▸
      Set.range_nonempty _)
    rw [range_realHyperbolicProjParam_of_ne_zero hθ]
    exact closure_Ioo hlt.ne

/-- The greatest lower bound of `α ↦ realHyperbolicProjParam α θ` is
`min (1 / (1 + exp (-2 * θ))) (exp (-2 * θ) / (1 + exp (-2 * θ)))`. -/
theorem sInf_range_realHyperbolicProjParam (θ : ℝ) :
    sInf (Set.range fun α ↦ realHyperbolicProjParam α θ) =
      min (1 / (1 + Real.exp (-2 * θ))) (Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ))) := by
  rcases eq_or_ne θ 0 with rfl | hθ
  · simp [Set.range_const, one_add_one_eq_two]
  · have hlt := Set.nonempty_Ioo.1 (range_realHyperbolicProjParam_of_ne_zero hθ ▸
      Set.range_nonempty _)
    rw [range_realHyperbolicProjParam_of_ne_zero hθ]
    exact csInf_Ioo hlt

/-- The least upper bound of `α ↦ realHyperbolicProjParam α θ` is
`max (1 / (1 + exp (-2 * θ))) (exp (-2 * θ) / (1 + exp (-2 * θ)))`. -/
theorem sSup_range_realHyperbolicProjParam (θ : ℝ) :
    sSup (Set.range fun α ↦ realHyperbolicProjParam α θ) =
      max (1 / (1 + Real.exp (-2 * θ))) (Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ))) := by
  rcases eq_or_ne θ 0 with rfl | hθ
  · simp [Set.range_const, one_add_one_eq_two]
  · have hlt := Set.nonempty_Ioo.1 (range_realHyperbolicProjParam_of_ne_zero hθ ▸
      Set.range_nonempty _)
    rw [range_realHyperbolicProjParam_of_ne_zero hθ]
    exact csSup_Ioo hlt

/-- **Scalar limit of the lower interval endpoint as `θ → +∞`.** As `θ → +∞` (`Q → 0⁺`), the lower
endpoint of the real hyperbolic interval tends to `0 = a_(-1)(Q)`. -/
theorem tendsto_sInf_range_realHyperbolicProjParam_atTop :
    Filter.Tendsto (fun θ ↦ sInf (Set.range fun α ↦ realHyperbolicProjParam α θ)) Filter.atTop
      (𝓝 0) := by
  simp_rw [sInf_range_realHyperbolicProjParam, ← Real.one_add_tanh_div_two,
    ← Real.one_sub_tanh_div_two]
  simpa using
    (((tendsto_const_nhds (x := (1 : ℝ))).add Real.tendsto_tanh_atTop).div_const 2).min
      (((tendsto_const_nhds (x := (1 : ℝ))).sub Real.tendsto_tanh_atTop).div_const 2)

/-- **Scalar limit of the upper interval endpoint as `θ → +∞`.** As `θ → +∞` (`Q → 0⁺`), the upper
endpoint of the real hyperbolic interval tends to `1 = a_1(Q)`. -/
theorem tendsto_sSup_range_realHyperbolicProjParam_atTop :
    Filter.Tendsto (fun θ ↦ sSup (Set.range fun α ↦ realHyperbolicProjParam α θ)) Filter.atTop
      (𝓝 1) := by
  simp_rw [sSup_range_realHyperbolicProjParam, ← Real.one_add_tanh_div_two,
    ← Real.one_sub_tanh_div_two]
  simpa [one_add_one_eq_two] using
    (((tendsto_const_nhds (x := (1 : ℝ))).add Real.tendsto_tanh_atTop).div_const 2).max
      (((tendsto_const_nhds (x := (1 : ℝ))).sub Real.tendsto_tanh_atTop).div_const 2)

/-- **Scalar limit of the lower interval endpoint as `θ → -∞`.** As `θ → -∞` (`Q → +∞`), the lower
endpoint of the real hyperbolic interval tends to `0`. -/
theorem tendsto_sInf_range_realHyperbolicProjParam_atBot :
    Filter.Tendsto (fun θ ↦ sInf (Set.range fun α ↦ realHyperbolicProjParam α θ)) Filter.atBot
      (𝓝 0) := by
  have h : (fun θ : ℝ ↦ sInf (Set.range fun α ↦ realHyperbolicProjParam α θ)) =
      (fun θ : ℝ ↦ sInf (Set.range fun α ↦ realHyperbolicProjParam α (-θ))) := by
    ext θ; rw [range_realHyperbolicProjParam_neg]
  rw [h]
  exact tendsto_sInf_range_realHyperbolicProjParam_atTop.comp Filter.tendsto_neg_atBot_atTop

/-- **Scalar limit of the upper interval endpoint as `θ → -∞`.** As `θ → -∞` (`Q → +∞`), the upper
endpoint of the real hyperbolic interval tends to `1`. -/
theorem tendsto_sSup_range_realHyperbolicProjParam_atBot :
    Filter.Tendsto (fun θ ↦ sSup (Set.range fun α ↦ realHyperbolicProjParam α θ)) Filter.atBot
      (𝓝 1) := by
  have h : (fun θ : ℝ ↦ sSup (Set.range fun α ↦ realHyperbolicProjParam α θ)) =
      (fun θ : ℝ ↦ sSup (Set.range fun α ↦ realHyperbolicProjParam α (-θ))) := by
    ext θ; rw [range_realHyperbolicProjParam_neg]
  rw [h]
  exact tendsto_sSup_range_realHyperbolicProjParam_atTop.comp Filter.tendsto_neg_atBot_atTop

end TauCeti
