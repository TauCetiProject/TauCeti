/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.RingTheory.Radical.NatInt
public import TauCeti.NumberTheory.DirichletCharacter.IntervalSum

import Mathlib.Analysis.Real.Sqrt
import TauCeti.Analysis.SpecialFunctions.Trigonometric.CosecantSum
import TauCeti.Data.ZMod.FinEquiv
import TauCeti.NumberTheory.CircleMethod.AdditiveCharacter
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.InducedSum
import TauCeti.NumberTheory.DirichletCharacter.PolyaVinogradov.Basic

/-!
# The classical explicit Pólya–Vinogradov inequality

This file proves the classical explicit Pólya–Vinogradov inequality for primitive, nonprincipal,
and prime-level complex Dirichlet characters.

For a primitive character `χ : DirichletCharacter ℂ q` (`q ≥ 2`) and integers `M : ℤ`, `N : ℕ`,
discrete Fourier inversion `DirichletCharacter.norm_sum_range_add_le_fourier` together with
`DirichletCharacter.intervalSum_eq_sum_range` gives

  `‖S_χ(M, N)‖ ≤ (√q)⁻¹ * ∑_{1 ≤ b < q} ‖∑_{M < n ≤ M + N} e(b * n / q)‖`,

where each inner geometric sum has modulus
`|sin (π * b * N / q)| / sin (π * b / q) ≤ min N (sin (π * b / q))⁻¹`
(`TauCeti.norm_sum_Ioc_expTwoPiI_mul_div_le`). Bounding each inner sum by `(sin (π * b / q))⁻¹`
and applying Pomerance's cosecant-sum inequality `TauCeti.sum_Ico_inv_sin_pi_mul_div_lt` yields

  `‖S_χ(M, N)‖ < (2 / π) * √q * (log q + log (4 / π) + π ^ 2 / (12 * q ^ 2))`,

both pointwise (`DirichletCharacter.polya_vinogradov_classical`) and for the maximal
interval sum `χ.maxIntervalSum` (`DirichletCharacter.maxIntervalSum_lt_of_isPrimitive`). Combining
this with the primitive reduction
`DirichletCharacter.maxIntervalSum_le_pow_mul_maxIntervalSum_primitiveCharacter` extends the bound
to every nonprincipal character modulo `q ≥ 1`. When `q ≥ 3` and `χ` is primitive (in particular
for any nonprincipal character modulo a prime `p`), `TauCeti.two_div_pi_mul_log_add_le_log` gives
`‖S_χ(M, N)‖ < √q * log q`.

## Main statements

* `DirichletCharacter.norm_intervalSum_le_inv_sqrt_mul_sum_min`:
  `‖S_χ(M, N)‖ ≤ (√q)⁻¹ * ∑_{1 ≤ b < q} min N (sin (π * b / q))⁻¹`.
* `DirichletCharacter.polya_vinogradov_classical`,
  `DirichletCharacter.maxIntervalSum_lt_of_isPrimitive`: classical explicit Pólya–Vinogradov
  inequality for primitive `χ` modulo `q ≥ 2`.
* `DirichletCharacter.maxIntervalSum_lt_of_ne_one`,
  `DirichletCharacter.norm_intervalSum_lt_of_ne_one`: extension to arbitrary nonprincipal `χ`
  via the conductor `χ.conductor` and `2 ^ ω (radical q / gcd (radical q) χ.conductor)`.
* `DirichletCharacter.norm_intervalSum_lt_sqrt_mul_log_of_isPrimitive`,
  `DirichletCharacter.maxIntervalSum_lt_sqrt_mul_log_of_isPrimitive`,
  `DirichletCharacter.norm_intervalSum_lt_sqrt_mul_log`,
  `DirichletCharacter.maxIntervalSum_lt_sqrt_mul_log`: bound `√q * log q` for primitive
  characters of level `q ≥ 3` and nonprincipal characters of prime level `p`.

## References

* C. Pomerance, *Remarks on the Pólya–Vinogradov inequality*, Integers 11 (2011), Lemma 4 and
  displays (4)–(10).
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I: Classical Theory*,
  Cambridge Studies in Advanced Mathematics 97, 2007, §9.4.
-/

public section

open Finset UniqueFactorizationMonoid
open scoped ArithmeticFunction.omega Real

namespace DirichletCharacter

/-! ### Pointwise bound from discrete Fourier inversion -/

/-- Bounding every character interval sum of a primitive character modulo `q ≥ 2` by the
normalized sum of `min N (sin (π * b / q))⁻¹`. -/
theorem norm_intervalSum_le_inv_sqrt_mul_sum_min {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (M : ℤ) (N : ℕ) :
    ‖χ.intervalSum M N‖ ≤
      (Real.sqrt q)⁻¹ * ∑ b ∈ Ico 1 q, min (N : ℝ) (Real.sin (π * b / q))⁻¹ := by
  have : NeZero q := ⟨by omega⟩
  have hχ₀ : χ ≠ 1 := fun h ↦ by
    have := hχ.eq_one_iff.mp h
    omega
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq_fac : Real.sqrt q / q = (Real.sqrt q)⁻¹ := by
    rw [div_eq_iff hqpos.ne', inv_mul_eq_div, eq_div_iff (Real.sqrt_ne_zero'.mpr hqpos),
      Real.mul_self_sqrt hqpos.le]
  let f : ℕ → ℝ := fun b ↦
    ‖∑ j ∈ range N, ZMod.stdAddChar ((b : ZMod q) * ((M : ZMod q) + 1 + (j : ZMod q)))‖
  have hsum_eq : ∑ k ∈ univ.erase (0 : ZMod q),
      ‖∑ j ∈ range N, ZMod.stdAddChar (k * ((M : ZMod q) + 1 + (j : ZMod q)))‖ =
      ∑ b ∈ Ico 1 q, f b := by
    have h1 : ∑ k ∈ univ.erase (0 : ZMod q),
        ‖∑ j ∈ range N, ZMod.stdAddChar (k * ((M : ZMod q) + 1 + (j : ZMod q)))‖ =
        ∑ k ∈ univ.erase (0 : ZMod q), f k.val :=
      sum_congr rfl fun k _ ↦ by simp only [f, ZMod.natCast_zmod_val]
    have h2 : f 0 + ∑ k ∈ univ.erase (0 : ZMod q), f k.val = f 0 + ∑ b ∈ Ico 1 q, f b := by
      rw [← ZMod.val_zero (n := q),
        add_sum_erase univ (fun k : ZMod q ↦ f k.val) (mem_univ 0),
        ZMod.sum_val_eq_sum_range, ← Nat.Ico_zero_eq_range,
        sum_eq_sum_Ico_succ_bot (NeZero.pos q), ZMod.val_zero]
    exact h1.trans (add_left_cancel h2)
  have hterm (b : ℕ) (hb : b ∈ Ico 1 q) :
      f b ≤ min (N : ℝ) (Real.sin (π * b / q))⁻¹ := by
    have hgeom : ∑ j ∈ range N, ZMod.stdAddChar ((b : ZMod q) * ((M : ZMod q) + 1 + (j : ZMod q))) =
        ∑ n ∈ Ioc M (M + N), TauCeti.expTwoPiI ((b : ℝ) * n / q) := by
      rw [Int.Ioc_eq_finset_map, add_sub_cancel_left, Int.toNat_natCast, sum_map]
      refine sum_congr rfl fun j _ ↦ ?_
      simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]
      rw [show (b : ZMod q) * ((M : ZMod q) + 1 + (j : ZMod q)) =
          (((b : ℤ) * (M + 1 + j) : ℤ) : ZMod q) by push_cast; ring,
        TauCeti.stdAddChar_intCast_eq_expTwoPiI]
      congr 1
      push_cast
      ring
    rw [mem_Ico] at hb
    dsimp only [f]
    rw [hgeom]
    exact TauCeti.norm_sum_Ioc_expTwoPiI_mul_div_le hb.1 hb.2 M N
  calc
    ‖χ.intervalSum M N‖
      = ‖∑ j ∈ range N, χ ((M : ZMod q) + 1 + (j : ZMod q))‖ := by
        rw [intervalSum_eq_sum_range]
    _ ≤ (Real.sqrt q / q) * ∑ k ∈ univ.erase (0 : ZMod q),
          ‖∑ j ∈ range N, ZMod.stdAddChar (k * ((M : ZMod q) + 1 + (j : ZMod q)))‖ :=
        norm_sum_range_add_le_fourier χ hχ hχ₀ ((M : ZMod q) + 1) N
    _ = (Real.sqrt q)⁻¹ * ∑ b ∈ Ico 1 q, f b := by rw [hq_fac, hsum_eq]
    _ ≤ (Real.sqrt q)⁻¹ * ∑ b ∈ Ico 1 q, min (N : ℝ) (Real.sin (π * b / q))⁻¹ :=
        mul_le_mul_of_nonneg_left (sum_le_sum hterm) (by positivity)

/-! ### The classical explicit Pólya–Vinogradov inequality -/

/-- **Classical explicit Pólya–Vinogradov inequality.** For a primitive complex Dirichlet
character `χ` modulo `q ≥ 2` and all `M : ℤ`, `N : ℕ`,
`‖S_χ(M, N)‖ < (2 / π) * √q * (log q + log (4 / π) + π ^ 2 / (12 * q ^ 2))`. -/
theorem polya_vinogradov_classical {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (M : ℤ) (N : ℕ) :
    ‖χ.intervalSum M N‖ <
      2 / π * Real.sqrt q * (Real.log q + Real.log (4 / π) + π ^ 2 / (12 * (q : ℝ) ^ 2)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hsqrt_pos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hqpos
  have hmin : ∑ b ∈ Ico 1 q, min (N : ℝ) (Real.sin (π * b / q))⁻¹ ≤
      ∑ b ∈ Ico 1 q, (Real.sin (π * b / q))⁻¹ :=
    sum_le_sum fun _ _ ↦ min_le_right _ _
  have hcsc := TauCeti.sum_Ico_inv_sin_pi_mul_div_lt (Nat.le_of_succ_le hq)
  have hq_div : (Real.sqrt q)⁻¹ * (2 * (q : ℝ) / π) = 2 / π * Real.sqrt q := by
    calc
      (Real.sqrt q)⁻¹ * (2 * (q : ℝ) / π)
        = (Real.sqrt q)⁻¹ * (2 * (Real.sqrt q * Real.sqrt q) / π) := by
          rw [Real.mul_self_sqrt hqpos.le]
      _ = 2 / π * Real.sqrt q := by
          field_simp [hsqrt_pos.ne']
  calc
    ‖χ.intervalSum M N‖
      ≤ (Real.sqrt q)⁻¹ * ∑ b ∈ Ico 1 q, min (N : ℝ) (Real.sin (π * b / q))⁻¹ :=
        norm_intervalSum_le_inv_sqrt_mul_sum_min hχ hq M N
    _ ≤ (Real.sqrt q)⁻¹ * ∑ b ∈ Ico 1 q, (Real.sin (π * b / q))⁻¹ :=
        mul_le_mul_of_nonneg_left hmin (by positivity)
    _ < (Real.sqrt q)⁻¹ *
          (2 * q / π * (Real.log q + Real.log (4 / π) + π ^ 2 / (12 * (q : ℝ) ^ 2))) :=
        mul_lt_mul_of_pos_left hcsc (inv_pos.mpr hsqrt_pos)
    _ = 2 / π * Real.sqrt q * (Real.log q + Real.log (4 / π) + π ^ 2 / (12 * (q : ℝ) ^ 2)) := by
        rw [← mul_assoc, hq_div]

/-- **Classical explicit Pólya–Vinogradov inequality** for the maximal interval sum `M_χ` of a
primitive character modulo `q ≥ 2`. -/
theorem maxIntervalSum_lt_of_isPrimitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) :
    χ.maxIntervalSum <
      2 / π * Real.sqrt q * (Real.log q + Real.log (4 / π) + π ^ 2 / (12 * (q : ℝ) ^ 2)) := by
  obtain ⟨M, -, N, -, hMN⟩ := χ.exists_norm_intervalSum_eq_maxIntervalSum
  rw [← hMN]
  exact χ.polya_vinogradov_classical hχ hq M N

/-- **Classical explicit Pólya–Vinogradov inequality for arbitrary nonprincipal characters:** for
`χ ≠ 1` modulo `q ≥ 1` with conductor `q*` and `r = radical q / gcd (radical q) q*`,
`M_χ < 2 ^ ω r * (2 / π * √q* * (log q* + log (4 / π) + π ^ 2 / (12 * q* ^ 2)))`. -/
theorem maxIntervalSum_lt_of_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) :
    χ.maxIntervalSum <
      2 ^ ω (radical q / (radical q).gcd χ.conductor) *
        (2 / π * Real.sqrt χ.conductor *
          (Real.log χ.conductor + Real.log (4 / π) + π ^ 2 / (12 * (χ.conductor : ℝ) ^ 2))) := by
  have hc₂ := Nat.le_of_succ_le (three_le_conductor_of_ne_one hχ)
  have hωpos : (0 : ℝ) < 2 ^ ω (radical q / (radical q).gcd χ.conductor) := by positivity
  calc
    χ.maxIntervalSum
      ≤ 2 ^ ω (radical q / (radical q).gcd χ.conductor) *
          χ.primitiveCharacter.maxIntervalSum :=
        χ.maxIntervalSum_le_pow_mul_maxIntervalSum_primitiveCharacter hχ
    _ < 2 ^ ω (radical q / (radical q).gcd χ.conductor) *
          (2 / π * Real.sqrt χ.conductor *
            (Real.log χ.conductor + Real.log (4 / π) + π ^ 2 / (12 * (χ.conductor : ℝ) ^ 2))) :=
        mul_lt_mul_of_pos_left
          (χ.primitiveCharacter.maxIntervalSum_lt_of_isPrimitive
            χ.primitiveCharacter_isPrimitive hc₂)
          hωpos

/-- Pointwise classical explicit Pólya–Vinogradov inequality for an arbitrary nonprincipal complex
Dirichlet character modulo `q ≥ 1`. -/
theorem norm_intervalSum_lt_of_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (M : ℤ) (N : ℕ) :
    ‖χ.intervalSum M N‖ <
      2 ^ ω (radical q / (radical q).gcd χ.conductor) *
        (2 / π * Real.sqrt χ.conductor *
          (Real.log χ.conductor + Real.log (4 / π) + π ^ 2 / (12 * (χ.conductor : ℝ) ^ 2))) :=
  (norm_intervalSum_le_maxIntervalSum hχ M N).trans_lt (χ.maxIntervalSum_lt_of_ne_one hχ)

/-- Every interval sum of a primitive character modulo `q ≥ 2` has norm strictly less than
`√q * log q` (note that no primitive character exists modulo `2`, so `q ≥ 3`). -/
theorem norm_intervalSum_lt_sqrt_mul_log_of_isPrimitive {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (M : ℤ) (N : ℕ) :
    ‖χ.intervalSum M N‖ < Real.sqrt q * Real.log q := by
  have : NeZero q := ⟨by omega⟩
  have hq3 : 3 ≤ q := χ.three_le_level_of_ne_one fun h ↦ by
    have h1 : q = 1 := hχ.eq_one_iff.mp h
    omega
  calc
    ‖χ.intervalSum M N‖
      < 2 / π * Real.sqrt q * (Real.log q + Real.log (4 / π) + π ^ 2 / (12 * (q : ℝ) ^ 2)) :=
        χ.polya_vinogradov_classical hχ hq M N
    _ = Real.sqrt q * (2 / π * (Real.log q + Real.log (4 / π) + π ^ 2 / (12 * (q : ℝ) ^ 2))) := by
        ring
    _ ≤ Real.sqrt q * Real.log q :=
        mul_le_mul_of_nonneg_left
          (TauCeti.two_div_pi_mul_log_add_le_log (by exact_mod_cast hq3))
          (Real.sqrt_nonneg _)

/-- The maximal interval sum of a primitive character modulo `q ≥ 2` is strictly less than
`√q * log q`. -/
theorem maxIntervalSum_lt_sqrt_mul_log_of_isPrimitive {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : 2 ≤ q) :
    χ.maxIntervalSum < Real.sqrt q * Real.log q := by
  obtain ⟨M, -, N, -, hMN⟩ := χ.exists_norm_intervalSum_eq_maxIntervalSum
  rw [← hMN]
  exact χ.norm_intervalSum_lt_sqrt_mul_log_of_isPrimitive hχ hq M N

/-- Every interval sum of a nonprincipal character modulo a prime `p` has norm strictly less than
`√p * log p`. -/
theorem norm_intervalSum_lt_sqrt_mul_log {p : ℕ} (hp : p.Prime) (χ : DirichletCharacter ℂ p)
    (hχ : χ ≠ 1) (M : ℤ) (N : ℕ) :
    ‖χ.intervalSum M N‖ < Real.sqrt p * Real.log p :=
  χ.norm_intervalSum_lt_sqrt_mul_log_of_isPrimitive
    (isPrimitive_of_ne_one_of_prime hp hχ) hp.two_le M N

/-- The maximal interval sum of a nonprincipal character modulo a prime `p` is strictly less than
`√p * log p`. -/
theorem maxIntervalSum_lt_sqrt_mul_log {p : ℕ} [NeZero p] (hp : p.Prime)
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    χ.maxIntervalSum < Real.sqrt p * Real.log p :=
  χ.maxIntervalSum_lt_sqrt_mul_log_of_isPrimitive
    (isPrimitive_of_ne_one_of_prime hp hχ) hp.two_le

/-! ### Checks -/

example : ‖∑ n ∈ Ioc (0 : ℤ) 1, TauCeti.expTwoPiI ((1 : ℝ) * n / (3 : ℕ))‖ = 1 := by
  have h := TauCeti.norm_sum_Ioc_expTwoPiI_mul_div_eq (b := 1) (q := 3) (by omega) (by omega) 0 1
  simp only [Nat.cast_one, Nat.cast_ofNat, one_mul, mul_one, zero_add,
    Real.sin_pi_div_three] at h
  simp only [Nat.cast_ofNat, one_mul]
  rw [h, abs_of_pos (by positivity), div_self (by positivity)]

example (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1) (M : ℤ) (N : ℕ) :
    ‖χ.intervalSum M N‖ < Real.sqrt 5 * Real.log 5 :=
  χ.norm_intervalSum_lt_sqrt_mul_log (by decide) hχ M N

end DirichletCharacter
