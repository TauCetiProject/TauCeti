/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebyshev.Mertens
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Log.Bounds

/-!
# Total served colength in a theta chain

The local gain inequality compares the full prime-power ask, less the net gain,
with the ask at the unserved tops and the local rounding and sandwich losses.
Since the unserved ask is part of the full ask, the served colength is bounded
by the gross gain plus those losses. Mertens' bound controls the gross gain;
at the theta-chain scale the total fits below the square of the row unit.

The local gain comparison is the one used in Levent Alpöge's
`Formalism.MainNotions.LinkG_at` and `Formalism.RankGapBounds.WeightedMeanData.Data.LoP`
in his [formalization of the Riemann hypothesis](https://github.com/leanprover-community/riemann-hypothesis).
-/

public section

open BigOperators Filter Real

namespace TauCeti.ThetaLift

/-- The logarithmically weighted served colength is bounded by the gross gain budget
and the weighted local losses. The net gain at `p` is `gain p - colength p`;
`unserved p ≤ full p` compares the ask at unserved tops with the full ask.
The factor of two is the inert-prime normalization in the gain comparison. -/
theorem sum_two_log_mul_served_colength_le {X G : ℝ} {s : Finset ℕ}
    (hX : 1 ≤ X) (hG : 0 ≤ G) (hs : s ⊆ Nat.primesLE ⌊X⌋₊)
    {colength gain full unserved loss : ℕ → ℝ}
    (hlocal : ∀ p ∈ s, full p - (gain p - colength p) ≤ unserved p + loss p)
    (hask : ∀ p ∈ s, unserved p ≤ full p) (hgain : ∀ p ∈ s, gain p ≤ G / p) :
    ∑ p ∈ s, 2 * log p * colength p ≤
      2 * G * (log X + (log 4 + 4)) + 2 * ∑ p ∈ s, log p * loss p := by
  have hlog (p : ℕ) (hp : p ∈ Nat.primesLE ⌊X⌋₊) : 0 ≤ log (p : ℝ) :=
    log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le)
  have hsum : ∑ p ∈ s, log (p : ℝ) / p ≤ log X + (log 4 + 4) := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hs fun p hp _ ↦ ?_).trans
      (Chebyshev.sum_primesLE_log_div_le hX)
    exact div_nonneg (hlog p hp) (Nat.cast_nonneg p)
  calc
    _ ≤ ∑ p ∈ s, (2 * G * (log (p : ℝ) / p) + 2 * (log p * loss p)) := by
      refine Finset.sum_le_sum fun p hp ↦ ?_
      have h : colength p ≤ G / p + loss p := by
        linarith only [hlocal p hp, hask p hp, hgain p hp]
      calc
        _ ≤ 2 * log p * (G / p + loss p) :=
          mul_le_mul_of_nonneg_left h (by positivity)
        _ = _ := by ring
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      gcongr

private theorem log_two_mul_scale_le {ε x : ℝ} (hε : 0 ≤ ε) (hx : 1 ≤ x) :
    log (2 * (x * exp (x ^ ε))) ≤ 3 * x ^ (1 + ε) := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hy := one_le_rpow hx hε
  rw [log_mul two_ne_zero (by positivity), log_mul hx₀.ne' (exp_pos _).ne', log_exp,
    rpow_add hx₀, rpow_one]
  linarith only [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2),
    log_le_sub_one_of_pos hx₀,
    le_mul_of_one_le_right (zero_le_one.trans hx) hy,
    le_mul_of_one_le_left (zero_le_one.trans hy) hx,
    one_le_mul_of_one_le_of_one_le hx hy]

private theorem servedColengthBudget_le {ε x X C : ℝ} (hε : 0 ≤ ε) (hx : 1 ≤ x)
    (hX : 1 ≤ X) (hC : 0 ≤ C) {D P m f N : ℕ} (hP : (P : ℝ) ≤ x ^ D)
    (hm : (m : ℝ) ≤ x ^ D) (hf : (f : ℝ) ≤ x ^ D) (hN : (N : ℝ) ≤ x ^ D)
    (hcut : X ≤ x * exp (x ^ ε)) :
    let b := exp (x ^ ε)
    let a := x * b
    8 * P * m * a * (log X + (log 4 + 4)) +
        2 * C * m * (P * b + f * X * ((N : ℝ) ^ 2 * log (2 * a) + log (2 * a) ^ 2)) ≤
      (72 + 26 * C) * x ^ (4 * D + 3 + 2 * ε : ℝ) * b := by
  intro b a
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  let R := x ^ D
  let Z := x ^ (1 + ε)
  have hR : 1 ≤ R := one_le_pow₀ hx
  have hZ : 1 ≤ Z := one_le_rpow hx (by linarith)
  have hb : 0 < b := exp_pos _
  have hL : log (2 * a) ≤ 3 * Z := log_two_mul_scale_le hε hx
  have hL₀ : 0 ≤ log (2 * a) := log_nonneg <|
    (show (1 : ℝ) ≤ 2 * X by linarith).trans (mul_le_mul_of_nonneg_left hcut (by norm_num))
  have hlogX : log X + (log 4 + 4) ≤ 9 * Z := by
    have h := log_le_log (zero_lt_one.trans_le hX)
      (hcut.trans (le_mul_of_one_le_left (show 0 ≤ a by positivity) (by norm_num : (1 : ℝ) ≤ 2)))
    linarith only [h, log_four_le_two, hZ, hL]
  have hZ2 : Z ≤ Z ^ 2 := le_self_pow₀ hZ (by decide)
  have hNcost : (N : ℝ) ^ 2 * log (2 * a) + log (2 * a) ^ 2 ≤ 12 * (R ^ 2 * Z ^ 2) := by
    calc
      _ ≤ R ^ 2 * (3 * Z) + (3 * Z) ^ 2 := by gcongr
      _ ≤ _ := by
        have h₁ := mul_le_mul_of_nonneg_left hZ2 (show 0 ≤ 3 * R ^ 2 by positivity)
        have h₂ := le_mul_of_one_le_left (sq_nonneg Z) (one_le_pow₀ hR (n := 2))
        linarith only [h₁, h₂]
  have hdom : 1 ≤ x * Z ^ 2 := one_le_mul_of_one_le_of_one_le hx (one_le_pow₀ hZ)
  have hbudget : x ^ (4 * D + 3 + 2 * ε : ℝ) = R ^ 4 * x * Z ^ 2 := by
    rw [show (4 * D + 3 + 2 * ε : ℝ) = (D : ℝ) * ((4 : ℕ) : ℝ) + 1 +
        (1 + ε) * ((2 : ℕ) : ℝ) by push_cast; ring,
      rpow_add hx₀, rpow_add hx₀, rpow_one, rpow_mul_natCast hx₀.le,
      rpow_mul_natCast hx₀.le, rpow_natCast]
  have hlogX₀ : 0 ≤ log X + (log 4 + 4) :=
    add_nonneg (log_nonneg hX) (by positivity)
  rw [hbudget]
  calc
    _ ≤ 8 * R * R * a * (9 * Z) + 2 * C * R * (R * b + R * a * (12 * (R ^ 2 * Z ^ 2))) := by
      gcongr
    _ = 72 * (R ^ 2 * x * Z * b) + 2 * C * (R ^ 2 * b) +
        24 * C * (R ^ 4 * x * Z ^ 2 * b) := by dsimp only [a]; ring
    _ ≤ _ := by
      have hR4 : R ^ 2 ≤ R ^ 4 := pow_le_pow_right₀ hR (by decide)
      have h₁ : R ^ 2 * x * Z * b ≤ R ^ 4 * x * Z ^ 2 * b := by gcongr
      have h₂ : R ^ 2 * b ≤ R ^ 4 * x * Z ^ 2 * b := by
        rw [mul_assoc (R ^ 4) x]
        exact mul_le_mul_of_nonneg_right (hR4.trans (le_mul_of_one_le_right (by positivity) hdom))
          hb.le
      linarith only [mul_le_mul_of_nonneg_left h₁ (by norm_num : (0 : ℝ) ≤ 72),
        mul_le_mul_of_nonneg_left h₂ (show 0 ≤ 2 * C by positivity)]

/-- At the scale `a = x * b`, `b = exp (x ^ ε)`, the served colength fits in `b²`.
The gross gain per prime is at most `4 * P * m * a / p`, for `P` tops and `m` lifts.
The loss budget includes both `P * b` per lift and the sandwich contribution with
host degree `f`, prime cutoff `X`, and rank bound `N`. The scale threshold depends
only on `ε`, the loss constant `C`, and the common polynomial exponent `D`. -/
theorem eventually_sum_log_mul_served_colength_le_sq {ε : ℝ} (hε : 0 < ε) (C : ℝ)
    (D : ℕ) : ∀ᶠ x : ℝ in atTop,
    let b := exp (x ^ ε)
    let a := x * b
    ∀ (X : ℝ) (P m f N : ℕ) (s : Finset ℕ) (colength gain full unserved loss : ℕ → ℝ),
      X ≤ a → s ⊆ Nat.primesLE ⌊X⌋₊ →
      (P : ℝ) ≤ x ^ D → (m : ℝ) ≤ x ^ D → (f : ℝ) ≤ x ^ D → (N : ℝ) ≤ x ^ D →
      (∀ p ∈ s, full p - (gain p - colength p) ≤ unserved p + loss p) →
      (∀ p ∈ s, unserved p ≤ full p) →
      (∀ p ∈ s, gain p ≤ 4 * P * m * a / p) →
      (∑ p ∈ s, log p * loss p) ≤
        C * m * (P * b + f * X * ((N : ℝ) ^ 2 * log (2 * a) + log (2 * a) ^ 2)) →
      ∑ p ∈ s, 2 * log p * colength p ≤ b ^ 2 := by
  let E : ℝ := 4 * D + 3 + 2 * ε
  let C₀ := max C 0
  have hC₀ : 0 ≤ C₀ := le_max_right ..
  have hsmall : (fun x : ℝ ↦ (72 + 26 * C₀) * x ^ E) =o[atTop] fun x ↦ exp (x ^ ε) := by
    refine (((isLittleO_rpow_exp_atTop (E / ε)).comp_tendsto
      (tendsto_rpow_atTop hε)).const_mul_left (72 + 26 * C₀)).congr' ?_ .rfl
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [Function.comp_apply, ← rpow_mul hx, mul_div_cancel₀ _ hε.ne']
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall.eventuallyLE] with x hx hscale
  intro b a X P m f N s colength gain full unserved loss hcut hs hP hm hf hN
    hlocal hask hgain hloss
  rcases s.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · simpa only [Finset.sum_empty] using sq_nonneg b
  have hX : 1 ≤ X := by
    have hp' := Nat.prime_of_mem_primesLE (hs hp)
    have hpX := (Nat.le_floor_iff' hp'.ne_zero).mp (Nat.le_of_mem_primesLE (hs hp))
    exact (show (1 : ℝ) ≤ p by exact_mod_cast hp'.one_lt.le).trans hpX
  have hL : 0 ≤ log (2 * a) := log_nonneg <|
    (show (1 : ℝ) ≤ 2 * X by linarith).trans (mul_le_mul_of_nonneg_left hcut (by norm_num))
  have hloss' : (∑ p ∈ s, log p * loss p) ≤
      C₀ * m * (P * b + f * X * ((N : ℝ) ^ 2 * log (2 * a) + log (2 * a) ^ 2)) := by
    refine hloss.trans ?_
    gcongr
    exact le_max_left ..
  calc
    _ ≤ 2 * (4 * P * m * a) * (log X + (log 4 + 4)) + 2 * ∑ p ∈ s, log p * loss p :=
      sum_two_log_mul_served_colength_le hX (by positivity) hs hlocal hask hgain
    _ ≤ 8 * P * m * a * (log X + (log 4 + 4)) +
        2 * C₀ * m * (P * b + f * X * ((N : ℝ) ^ 2 * log (2 * a) + log (2 * a) ^ 2)) := by
      linarith only [hloss']
    _ ≤ (72 + 26 * C₀) * x ^ E * b := servedColengthBudget_le hε.le hx hX hC₀ hP hm hf hN hcut
    _ ≤ b ^ 2 := by
      have h : (72 + 26 * C₀) * x ^ E ≤ b := by
        simpa only [Real.norm_of_nonneg (show 0 ≤ (72 + 26 * C₀) * x ^ E by positivity),
          Real.norm_of_nonneg (exp_nonneg _)] using hscale
      rw [sq]
      exact mul_le_mul_of_nonneg_right h (exp_nonneg _)

end TauCeti.ThetaLift
