/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Analysis.Complex.Schwarz

import Mathlib.Analysis.Complex.ExponentialBounds
import TauCeti.Algebra.CharZero.RatCast

/-!
# The analytic bound for Schneider's auxiliary function

Let `β ∈ ℂ` be irrational, `λ ∈ ℂ`, and let

`F(z) = ∑_{i < D₁, j < D₂} a_{ij} z ^ i exp (j λ z)`

be an exponential polynomial with complex coefficients that vanishes at the `L²` distinct points
`u + v β` of the grid `1 ≤ u, v ≤ L`. This is Schneider's auxiliary function from the proof of
the Gelfond–Schneider theorem, whose coefficients are produced by Siegel's lemma in
`RingHom.exists_schneider_auxiliary`. This file shows that `F` is very small on the larger grid
`0 ≤ u, v ≤ c L`: the extrapolation estimate of Evertse's Lemma 4.27.

The proof applies Schwarz's lemma with prescribed zeros (`TauCeti.norm_le_mul_three_mul_div_pow`)
on discs of radii `R` and `T = 3 e R`, where `R` bounds the moduli of all the grid points. On the
circle of radius `T` the function `F` is trivially bounded by `D₁ D₂ A T ^ D₁ exp (D₂ |λ| T)`,
where `A` bounds the coefficients, and the `L²` zeros contribute the factor `exp (-L²)`.

In the proof of the Gelfond–Schneider theorem the values `F(u + v β)` are the images of algebraic
numbers whose houses and denominators are bounded by `exp (O(L^{3/2} log L))`. The factor
`exp (-L²)` here then forces those algebraic numbers to vanish, by Liouville's inequality.

## Main results

* `TauCeti.norm_schneider_auxiliary_le`: the bound
  `‖F z‖ ≤ D₁ D₂ A T ^ D₁ exp (D₂ ‖λ‖ T) (3 R / T) ^ (L ^ 2)` for `‖z‖ ≤ R`.
* `TauCeti.exists_norm_schneider_auxiliary_le_exp`: if `|a_{ij}| ≤ exp (c₁ (D₁ log L + D₂ L))`,
  then `|F(u + v β)| ≤ exp (C (D₁ log L + D₂ L) - L ^ 2)` for `0 ≤ u, v ≤ c L`.
* `TauCeti.exists_norm_schneider_auxiliary_le_exp_rpow`: for Schneider's parameters
  `L = 2 d M²`, `D₁ = (2 d)² M³`, `D₂ = 2 d M`, the bound
  `|F(u + v β)| ≤ exp (c₄ L ^ (3 / 2) log L - L ^ 2)` of Lemma 4.27.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 4, §4.4, Lemmas 4.26
  and 4.27.
-/

public section

open Finset Metric

namespace TauCeti

/-- The trivial bound for Schneider's auxiliary function on a disc: if `‖a_{ij}‖ ≤ A`, `1 ≤ T`
and `‖w‖ ≤ T`, then `‖F w‖ ≤ D₁ D₂ A T ^ D₁ exp (D₂ ‖λ‖ T)`. -/
private theorem norm_schneider_auxiliary_le_of_norm_le (l : ℂ) {D₁ D₂ : ℕ}
    {a : Fin D₁ → Fin D₂ → ℂ} {A T : ℝ} (ha : ∀ i j, ‖a i j‖ ≤ A) (hT : 1 ≤ T) {w : ℂ}
    (hw : ‖w‖ ≤ T) :
    ‖∑ i, ∑ j, a i j * w ^ (i : ℕ) * Complex.exp (j * l * w)‖ ≤
      D₁ * D₂ * A * T ^ D₁ * Real.exp (D₂ * ‖l‖ * T) := by
  have hterm (i : Fin D₁) (j : Fin D₂) :
      ‖a i j * w ^ (i : ℕ) * Complex.exp (j * l * w)‖ ≤
        A * T ^ D₁ * Real.exp (D₂ * ‖l‖ * T) := by
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_exp]
    have hexp : Real.exp (j * l * w).re ≤ Real.exp (D₂ * ‖l‖ * T) := by
      refine Real.exp_le_exp.2 ((Complex.re_le_norm _).trans ?_)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      have : (j : ℝ) ≤ D₂ := by exact_mod_cast j.is_lt.le
      gcongr
    have hA : 0 ≤ A := (norm_nonneg _).trans (ha i j)
    calc ‖a i j‖ * ‖w‖ ^ (i : ℕ) * Real.exp (j * l * w).re
        ≤ A * T ^ (i : ℕ) * Real.exp (D₂ * ‖l‖ * T) := by gcongr; exact ha i j
      _ ≤ A * T ^ D₁ * Real.exp (D₂ * ‖l‖ * T) := by
        gcongr
        exact i.is_lt.le
  calc ‖∑ i, ∑ j, a i j * w ^ (i : ℕ) * Complex.exp (j * l * w)‖
      ≤ ∑ i, ∑ j, ‖a i j * w ^ (i : ℕ) * Complex.exp (j * l * w)‖ :=
        (norm_sum_le _ _).trans (sum_le_sum fun i _ ↦ norm_sum_le _ _)
    _ ≤ ∑ _i : Fin D₁, ∑ _j : Fin D₂, A * T ^ D₁ * Real.exp (D₂ * ‖l‖ * T) :=
        sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ hterm i j
    _ = D₁ * D₂ * A * T ^ D₁ * Real.exp (D₂ * ‖l‖ * T) := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Schwarz's lemma for Schneider's auxiliary function.** Let `β ∈ ℂ` be irrational and let
`F(z) = ∑_{i < D₁, j < D₂} a_{ij} z ^ i exp (j λ z)` vanish at `u + v β` for `1 ≤ u, v ≤ L`. If
`‖a_{ij}‖ ≤ A`, `L (1 + ‖β‖) ≤ R`, `3 R ≤ T` and `1 ≤ T`, then on the disc `‖z‖ ≤ R`
`‖F z‖ ≤ D₁ D₂ A T ^ D₁ exp (D₂ ‖λ‖ T) (3 R / T) ^ (L ^ 2)`. -/
theorem norm_schneider_auxiliary_le {β : ℂ} (hβ : ∀ q : ℚ, (q : ℂ) ≠ β) {l : ℂ} {L D₁ D₂ : ℕ}
    {a : Fin D₁ → Fin D₂ → ℂ} {A R T : ℝ} (ha : ∀ i j, ‖a i j‖ ≤ A)
    (hzero : ∀ u v : ℕ, 1 ≤ u → u ≤ L → 1 ≤ v → v ≤ L →
      ∑ i, ∑ j, a i j * ((u : ℂ) + v * β) ^ (i : ℕ) * Complex.exp (j * l * (u + v * β)) = 0)
    (hR : L * (1 + ‖β‖) ≤ R) (hRT : 3 * R ≤ T) (hT : 1 ≤ T) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖∑ i, ∑ j, a i j * z ^ (i : ℕ) * Complex.exp (j * l * z)‖ ≤
      D₁ * D₂ * A * T ^ D₁ * Real.exp (D₂ * ‖l‖ * T) * (3 * R / T) ^ (L ^ 2) := by
  set f : ℂ → ℂ := fun z ↦ ∑ i, ∑ j, a i j * z ^ (i : ℕ) * Complex.exp (j * l * z)
  have hf : Differentiable ℂ f := by fun_prop
  -- The `L²` zeros of `F` on the grid.
  set s : Finset ℂ := (Icc 1 L ×ˢ Icc 1 L).image fun p : ℕ × ℕ ↦ (p.1 : ℂ) + p.2 * β
  have hs : #s = L ^ 2 := by
    have hinj : Set.InjOn (fun p : ℕ × ℕ ↦ (p.1 : ℂ) + p.2 * β) ↑(Icc 1 L ×ˢ Icc 1 L) := by
      rintro ⟨u, v⟩ - ⟨u', v'⟩ - h
      simpa using ratCast_add_ratCast_mul_injective hβ (a₁ := (u, v)) (a₂ := (u', v'))
        (by simpa using h)
    rw [card_image_of_injOn hinj, card_product, Nat.card_Icc, Nat.add_sub_cancel, sq]
  have hk : ∀ x ∈ s, ((1 : ℕ) : ℕ∞) ≤ analyticOrderAt f x := by
    simp only [s, mem_image, mem_product, mem_Icc, Prod.exists]
    rintro _ ⟨u, v, ⟨⟨hu₁, hu⟩, hv₁, hv⟩, rfl⟩
    rw [Nat.cast_one, Order.one_le_iff_ne_zero, analyticOrderAt_ne_zero]
    exact ⟨hf.analyticAt _, hzero u v hu₁ hu hv₁ hv⟩
  have hsR : (s : Set ℂ) ⊆ closedBall 0 R := by
    simp only [s, coe_image, Set.image_subset_iff]
    rintro ⟨u, v⟩ huv
    simp only [coe_product, coe_Icc, Set.mem_prod, Set.mem_Icc] at huv
    obtain ⟨⟨-, hu⟩, -, hv⟩ := huv
    have hu' : (u : ℝ) ≤ L := by exact_mod_cast hu
    have hv' : (v : ℝ) ≤ L := by exact_mod_cast hv
    rw [Set.mem_preimage, mem_closedBall_zero_iff]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    nlinarith [norm_nonneg β]
  have hM (w : ℂ) (hw : w ∈ sphere (0 : ℂ) T) :=
    norm_schneider_auxiliary_le_of_norm_le l ha hT (mem_sphere_zero_iff_norm.1 hw).le
  have := norm_le_mul_three_mul_div_pow (f := f) (s := s) (k := fun _ ↦ 1)
    (fun x _ ↦ hf.analyticAt x) hk hsR hRT hM (mem_closedBall_zero_iff.2 hz)
  simpa only [sum_const, smul_eq_mul, mul_one, hs] using this

/-- The size estimate behind `exists_norm_schneider_auxiliary_le_exp`: for `L ≥ 2`, `κ ≥ 1` and
`μ ≥ 0`, with `E = D₁ log L + D₂ L`,
`D₁ D₂ exp (c₁ E) (κ L) ^ D₁ exp (D₂ μ κ L) ≤ exp ((3 + |c₁| + 2 log κ + μ κ) E)`. -/
private theorem schneider_circle_bound_le_exp {c₁ κ μ : ℝ} {L D₁ D₂ : ℕ} (hL : 2 ≤ L)
    (hκ : 1 ≤ κ) (hμ : 0 ≤ μ) :
    (D₁ : ℝ) * D₂ * Real.exp (c₁ * (D₁ * Real.log L + D₂ * L)) * (κ * L) ^ D₁ *
        Real.exp (D₂ * μ * (κ * L)) ≤
      Real.exp ((3 + |c₁| + 2 * Real.log κ + μ * κ) * (D₁ * Real.log L + D₂ * L)) := by
  set E : ℝ := D₁ * Real.log L + D₂ * L
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hlogL : 1 / 2 ≤ Real.log L := by
    linarith [Real.log_two_gt_d9, Real.log_le_log (by norm_num) hL']
  have hlogκ := Real.log_nonneg hκ
  have hD₁ : (0 : ℝ) ≤ D₁ := D₁.cast_nonneg
  have hD₂ : (0 : ℝ) ≤ D₂ := D₂.cast_nonneg
  have h₁ : (D₁ : ℝ) ≤ Real.exp (2 * (D₁ * Real.log L)) :=
    (le_add_of_nonneg_right zero_le_one).trans
      ((Real.add_one_le_exp _).trans (Real.exp_le_exp.2 (by nlinarith)))
  have h₂ : (D₂ : ℝ) ≤ Real.exp (D₂ * L) :=
    (le_add_of_nonneg_right zero_le_one).trans
      ((Real.add_one_le_exp _).trans (Real.exp_le_exp.2 (by nlinarith)))
  have h₃ : Real.exp (c₁ * E) ≤ Real.exp (|c₁| * E) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_abs_self c₁) (by positivity))
  have h₄ : (κ * L) ^ D₁ = Real.exp (D₁ * Real.log κ + D₁ * Real.log L) := by
    rw [← mul_add, ← Real.log_mul (by positivity) (by positivity), ← Real.log_pow,
      Real.exp_log (by positivity)]
  calc (D₁ : ℝ) * D₂ * Real.exp (c₁ * E) * (κ * L) ^ D₁ * Real.exp (D₂ * μ * (κ * L))
      ≤ Real.exp (2 * (D₁ * Real.log L)) * Real.exp (D₂ * L) * Real.exp (|c₁| * E) *
          Real.exp (D₁ * Real.log κ + D₁ * Real.log L) * Real.exp (D₂ * μ * (κ * L)) := by
        rw [h₄]
        gcongr
    _ ≤ Real.exp ((3 + |c₁| + 2 * Real.log κ + μ * κ) * E) := by
        simp only [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        -- `D₁ log κ ≤ 2 log κ · D₁ log L`, as `1 ≤ 2 log L`.
        have h₅ : D₁ * Real.log κ ≤ 2 * Real.log κ * (D₁ * Real.log L) := by
          linear_combination mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 * Real.log L by linarith)
            (mul_nonneg hD₁ hlogκ)
        have h₆ : 0 ≤ D₁ * Real.log L := by positivity
        have h₇ : 0 ≤ D₂ * (L : ℝ) := by positivity
        have h₈ : 0 ≤ |c₁| * E := by positivity
        simp only [E] at h₈ ⊢
        nlinarith [abs_nonneg c₁, mul_nonneg hμ (by linarith : (0 : ℝ) ≤ κ)]

/-- **Extrapolation of Schneider's auxiliary function**, the estimate of Evertse's Lemma 4.27 for
arbitrary parameters. Let `β ∈ ℂ` be irrational, `λ ∈ ℂ`, `c₁ ∈ ℝ` and `c ∈ ℕ`. There is
`C ≥ 0` such that the following holds for all `L ≥ 2` and `D₁, D₂`. If
`F(z) = ∑_{i < D₁, j < D₂} a_{ij} z ^ i exp (j λ z)` has coefficients
`‖a_{ij}‖ ≤ exp (c₁ (D₁ log L + D₂ L))` and vanishes at `u + v β` for `1 ≤ u, v ≤ L`, then
`‖F(u + v β)‖ ≤ exp (C (D₁ log L + D₂ L) - L ^ 2)` for all `0 ≤ u, v ≤ c L`. -/
theorem exists_norm_schneider_auxiliary_le_exp {β : ℂ} (hβ : ∀ q : ℚ, (q : ℂ) ≠ β) (l : ℂ)
    (c₁ : ℝ) (c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L D₁ D₂ : ℕ, 2 ≤ L → ∀ a : Fin D₁ → Fin D₂ → ℂ,
      (∀ i j, ‖a i j‖ ≤ Real.exp (c₁ * (D₁ * Real.log L + D₂ * L))) →
      (∀ u v : ℕ, 1 ≤ u → u ≤ L → 1 ≤ v → v ≤ L →
        ∑ i, ∑ j, a i j * ((u : ℂ) + v * β) ^ (i : ℕ) * Complex.exp (j * l * (u + v * β)) = 0) →
      ∀ u v : ℕ, u ≤ c * L → v ≤ c * L →
        ‖∑ i, ∑ j, a i j * ((u : ℂ) + v * β) ^ (i : ℕ) * Complex.exp (j * l * (u + v * β))‖ ≤
          Real.exp (C * (D₁ * Real.log L + D₂ * L) - L ^ 2) := by
  -- The discs have radii `R = (c + 1) (1 + ‖β‖) L` and `T = κ L` with `κ = 3 e (c + 1) (1 + ‖β‖)`.
  set b : ℝ := (c + 1) * (1 + ‖β‖)
  set κ : ℝ := 3 * Real.exp 1 * b
  have hb : 1 ≤ b := one_le_mul_of_one_le_of_one_le (by linarith [c.cast_nonneg' (α := ℝ)])
    (by linarith [norm_nonneg β])
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hκ : 1 ≤ κ := by
    simp only [κ]
    nlinarith
  refine ⟨3 + |c₁| + 2 * Real.log κ + ‖l‖ * κ, by
    linarith [abs_nonneg c₁, Real.log_nonneg hκ,
      mul_nonneg (norm_nonneg l) (by linarith : 0 ≤ κ)],
    fun L D₁ D₂ hL a ha hzero u v hu hv ↦ ?_⟩
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hu' : (u : ℝ) ≤ c * L := by exact_mod_cast hu
  have hv' : (v : ℝ) ≤ c * L := by exact_mod_cast hv
  have hR : (L : ℝ) * (1 + ‖β‖) ≤ b * L := by
    simp only [b]
    nlinarith [norm_nonneg β, c.cast_nonneg' (α := ℝ)]
  have hRT : 3 * (b * L) ≤ κ * L := by
    have hbL : 0 ≤ 3 * (b * L) := by positivity
    simp only [κ]
    linear_combination mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ Real.exp 1 by linarith) hbL
  have hz : ‖(u : ℂ) + v * β‖ ≤ b * L := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    simp only [b]
    nlinarith [norm_nonneg β]
  have h := norm_schneider_auxiliary_le hβ ha hzero hR hRT (by nlinarith) hz
  -- The `L²` zeros contribute `(3 b L / (κ L)) ^ (L ^ 2) = exp (-L²)`.
  have hq : 3 * (b * L) / (κ * L) = Real.exp (-1) := by
    rw [Real.exp_neg, ← one_div, div_eq_div_iff (by positivity) (Real.exp_pos 1).ne']
    simp only [κ]
    ring
  rw [hq, ← Real.exp_nat_mul, mul_neg_one] at h
  refine h.trans ?_
  rw [sub_eq_add_neg, Real.exp_add]
  push_cast
  gcongr
  exact schneider_circle_bound_le_exp hL hκ (norm_nonneg l)

/-- Schneider's parameters `L = 2 d M²`, `D₁ = (2 d)² M³`, `D₂ = 2 d M` satisfy
`D₁ = √(2 d) L ^ (3 / 2)` and `D₂ L = √(2 d) L ^ (3 / 2)`. -/
private theorem schneider_params {d M L D₁ D₂ : ℕ} (hL : L = 2 * d * M ^ 2)
    (hD₁ : D₁ = (2 * d) ^ 2 * M ^ 3) (hD₂ : D₂ = 2 * d * M) :
    (D₁ : ℝ) = √(2 * d) * (L : ℝ) ^ (3 / 2 : ℝ) ∧
      (D₂ : ℝ) * L = √(2 * d) * (L : ℝ) ^ (3 / 2 : ℝ) := by
  have hpow : (L : ℝ) ^ (3 / 2 : ℝ) = L * √L := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' L.cast_nonneg (by norm_num),
      Real.rpow_one, Real.sqrt_eq_rpow]
  have hsqrt : √(L : ℝ) = √(2 * d) * M := by
    rw [hL]
    push_cast
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq M.cast_nonneg]
  have hs : √(2 * d : ℝ) * √(2 * d) = 2 * d := Real.mul_self_sqrt (by positivity)
  rw [hpow, hsqrt, hD₁, hD₂, hL]
  push_cast
  constructor <;> linear_combination (-(2 * (d : ℝ) * M ^ 3)) * hs

/-- **Extrapolation of Schneider's auxiliary function, Lemma 4.27 form** (Evertse, Lemma 4.27).
Let `β ∈ ℂ` be irrational, `λ ∈ ℂ`, `c₁ ∈ ℝ` and `d, c ∈ ℕ`. There is `c₄` such that, for
Schneider's parameters `L = 2 d M²`, `D₁ = (2 d)² M³`, `D₂ = 2 d M` with `M ≥ 1`, every
`F(z) = ∑_{i < D₁, j < D₂} a_{ij} z ^ i exp (j λ z)` with coefficients
`‖a_{ij}‖ ≤ exp (c₁ (D₁ log L + D₂ L))` vanishing at `u + v β` for `1 ≤ u, v ≤ L` satisfies
`‖F(u + v β)‖ ≤ exp (c₄ L ^ (3 / 2) log L - L ^ 2)` for all `0 ≤ u, v ≤ c L`. -/
theorem exists_norm_schneider_auxiliary_le_exp_rpow {β : ℂ} (hβ : ∀ q : ℚ, (q : ℂ) ≠ β) (l : ℂ)
    (d : ℕ) (c₁ : ℝ) (c : ℕ) :
    ∃ c₄ : ℝ, ∀ M L D₁ D₂ : ℕ, 1 ≤ M → L = 2 * d * M ^ 2 → D₁ = (2 * d) ^ 2 * M ^ 3 →
      D₂ = 2 * d * M → ∀ a : Fin D₁ → Fin D₂ → ℂ,
      (∀ i j, ‖a i j‖ ≤ Real.exp (c₁ * (D₁ * Real.log L + D₂ * L))) →
      (∀ u v : ℕ, 1 ≤ u → u ≤ L → 1 ≤ v → v ≤ L →
        ∑ i, ∑ j, a i j * ((u : ℂ) + v * β) ^ (i : ℕ) * Complex.exp (j * l * (u + v * β)) = 0) →
      ∀ u v : ℕ, u ≤ c * L → v ≤ c * L →
        ‖∑ i, ∑ j, a i j * ((u : ℂ) + v * β) ^ (i : ℕ) * Complex.exp (j * l * (u + v * β))‖ ≤
          Real.exp (c₄ * (L : ℝ) ^ (3 / 2 : ℝ) * Real.log L - L ^ 2) := by
  obtain ⟨C, hC, h⟩ := exists_norm_schneider_auxiliary_le_exp hβ l c₁ c
  refine ⟨3 * √(2 * d) * C, fun M L D₁ D₂ hM hL hD₁ hD₂ a ha hzero u v hu hv ↦ ?_⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- For `d = 0` there are no terms.
    obtain rfl : D₁ = 0 := by simpa using hD₁
    simpa using (Real.exp_pos _).le
  have hL₂ : 2 ≤ L := by
    rw [hL]
    nlinarith [Nat.one_le_pow 2 M hM]
  refine (h L D₁ D₂ hL₂ a ha hzero u v hu hv).trans (Real.exp_le_exp.2 (sub_le_sub_right ?_ _))
  obtain ⟨h₁, h₂⟩ := schneider_params hL hD₁ hD₂
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL₂
  have hlogL : 1 / 2 ≤ Real.log L := by
    linarith [Real.log_two_gt_d9, Real.log_le_log (by norm_num) hL']
  -- `D₁ log L + D₂ L = √(2 d) L ^ (3 / 2) (log L + 1) ≤ 3 √(2 d) L ^ (3 / 2) log L`.
  have hP : 0 ≤ √(2 * d : ℝ) * (L : ℝ) ^ (3 / 2 : ℝ) := by positivity
  rw [h₁, h₂]
  nlinarith [mul_nonneg hC hP]

end TauCeti
