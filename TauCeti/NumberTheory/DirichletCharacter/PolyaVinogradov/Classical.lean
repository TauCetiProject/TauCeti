/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
public import TauCeti.NumberTheory.CircleMethod.AdditiveCharacter
public import TauCeti.NumberTheory.DirichletCharacter.IntervalSum

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import TauCeti.Analysis.SpecialFunctions.Trigonometric.CosecantSum
import TauCeti.NumberTheory.DirichletCharacter.Conductor
import TauCeti.NumberTheory.DirichletCharacter.GaussSum

/-!
# The classical explicit Pólya–Vinogradov inequality

This file proves the Gauss-sum expansion of character interval sums and the classical explicit
Pólya–Vinogradov inequality for primitive, nonprincipal, and prime-level complex Dirichlet
characters.

For a primitive character `χ : DirichletCharacter ℂ q` (`q ≥ 2`) and integers `M : ℤ`, `N : ℕ`,
applying the Gauss-sum shift identity to `χ⁻¹` and the standard additive character
`ZMod.stdAddChar` gives

  `S_χ(M, N) = τ(χ⁻¹)⁻¹ * ∑_{1 ≤ b < q} χ⁻¹ b * ∑_{M < n ≤ M + N} e(b * n / q)`,

where `|τ(χ⁻¹)| = √q` and the inner geometric sum has modulus
`|sin (π * b * N / q)| / sin (π * b / q) ≤ min N (sin (π * b / q))⁻¹`. For even `χ` only the
cosine parts survive and for odd `χ` only the sine parts survive. Bounding each inner sum by
`(sin (π * b / q))⁻¹` and applying Pomerance's cosecant-sum inequality
`TauCeti.sum_Ico_inv_sin_pi_mul_div_lt` yields

  `‖S_χ(M, N)‖ < (2 / π) * √q * (log q + log (4 / π) + π ^ 2 / (12 * q ^ 2))`,

both pointwise and for the maximal interval sum `χ.maxIntervalSum`. Combining this with the
primitive reduction `DirichletCharacter.maxIntervalSum_le_two_pow_omega_mul_primitiveCharacter`
extends the bound to every nonprincipal character modulo `q ≥ 1`, and for a nonprincipal character
modulo a prime `p` gives `‖S_χ(M, N)‖ < √p * log p`.

## Main statements

* `TauCeti.norm_sum_Ioc_expTwoPiI_mul_div_eq`: exact modulus
  `|sin (π * b * N / q)| / sin (π * b / q)` of `∑_{M < n ≤ M + N} e(b * n / q)` for `1 ≤ b < q`.
* `DirichletCharacter.mul_gaussSum_inv_stdAddChar_eq_sum`: Gauss-sum expansion of `χ n`.
* `DirichletCharacter.intervalSum_eq_inv_gaussSum_mul_sum`,
  `DirichletCharacter.Even.intervalSum_eq_inv_gaussSum_mul_sum_cos`,
  `DirichletCharacter.Odd.intervalSum_eq_inv_gaussSum_mul_sum_sin`: Gauss-sum expansions of
  `S_χ(M, N)` and their parity forms.
* `DirichletCharacter.norm_intervalSum_le_inv_sqrt_mul_sum_min`:
  `‖S_χ(M, N)‖ ≤ (√q)⁻¹ * ∑_{1 ≤ b < q} min N (sin (π * b / q))⁻¹`.
* `DirichletCharacter.polya_vinogradov_classical`,
  `DirichletCharacter.maxIntervalSum_lt_of_isPrimitive`: classical explicit Pólya–Vinogradov
  inequality for primitive `χ` modulo `q ≥ 2`.
* `DirichletCharacter.maxIntervalSum_lt_of_ne_one`,
  `DirichletCharacter.norm_intervalSum_lt_of_ne_one`: extension to arbitrary nonprincipal `χ`
  via the conductor `χ.conductor` and `2 ^ ω r`.
* `DirichletCharacter.norm_intervalSum_lt_sqrt_mul_log`,
  `DirichletCharacter.maxIntervalSum_lt_sqrt_mul_log`: prime-level bound `√p * log p`.

## References

* C. Pomerance, *Remarks on the Pólya–Vinogradov inequality*, Integers 11 (2011), Lemma 4 and
  displays (4)–(10).
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I: Classical Theory*,
  Cambridge Studies in Advanced Mathematics 97, 2007, §9.4.
-/

public section

open Finset
open scoped ArithmeticFunction.omega Real

namespace TauCeti

/-! ### Geometric sums of `e(b * n / q)` -/

/-- Exact modulus of a character-expansion geometric sum: for `1 ≤ b < q`, `M : ℤ`, and `N : ℕ`,
`‖∑ n ∈ Ioc M (M + N), e(b * n / q)‖ = |sin (π * b * N / q)| / sin (π * b / q)`. -/
theorem norm_sum_Ioc_expTwoPiI_mul_div_eq {b q : ℕ} (hb₀ : 1 ≤ b) (hbq : b < q)
    (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Ioc M (M + N), expTwoPiI ((b : ℝ) * n / q)‖ =
      |Real.sin (π * b * N / q)| / Real.sin (π * b / q) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  set α : ℝ := (b : ℝ) / q
  have hα₀ : 0 < α := div_pos hbpos hqpos
  have hα₁ : α < 1 := (div_lt_one hqpos).mpr (by exact_mod_cast hbq)
  have hdist : distInt α ≠ 0 := by
    intro h
    obtain ⟨m, hm⟩ := distInt_eq_zero_iff.mp h
    have hm₀ : (0 : ℝ) < m := hm ▸ hα₀
    have hm₁ : (m : ℝ) < 1 := hm ▸ hα₁
    have hmZ₀ : (0 : ℤ) < m := Int.cast_pos.mp hm₀
    have hmZ₁ : m < 1 := Int.cast_lt.mp (by exact_mod_cast hm₁)
    omega
  have hsin_pos : 0 < Real.sin (π * α) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hα₀)
      (by nlinarith [Real.pi_pos])
  -- Shift `n ∈ Ioc M (M + N)` to `k ∈ Icc 1 N`.
  have hshift : ∑ n ∈ Ioc M (M + N), expTwoPiI ((b : ℝ) * n / q) =
      expTwoPiI (b * M / q) * ∑ k ∈ Icc 1 N, expTwoPiI (k * α) := by
    rw [Int.Ioc_eq_finset_map, add_sub_cancel_left, Int.toNat_natCast, sum_map, mul_sum,
      ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    refine sum_congr rfl fun k _ ↦ ?_
    simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply,
      Int.cast_add, Int.cast_natCast]
    rw [← expTwoPiI_add]
    congr 1
    dsimp only [α]
    push_cast
    ring
  rw [hshift, norm_mul, norm_expTwoPiI, one_mul, sum_expTwoPiI_eq N hdist,
    norm_div, norm_mul, norm_expTwoPiI, one_mul, norm_expTwoPiI_sub_one,
    norm_expTwoPiI_sub_one, abs_of_pos hsin_pos]
  rw [mul_div_mul_left _ _ two_ne_zero,
    show π * ((N : ℝ) * α) = π * b * N / q by dsimp only [α]; ring,
    show π * α = π * b / q by dsimp only [α]; ring]

/-- Upper bound for the geometric sum in the Gauss-sum expansion: for `1 ≤ b < q`, `M : ℤ`, and
`N : ℕ`, `‖∑ n ∈ Ioc M (M + N), e(b * n / q)‖ ≤ min N (sin (π * b / q))⁻¹`. -/
theorem norm_sum_Ioc_expTwoPiI_mul_div_le {b q : ℕ} (hb₀ : 1 ≤ b) (hbq : b < q)
    (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Ioc M (M + N), expTwoPiI ((b : ℝ) * n / q)‖ ≤
      min (N : ℝ) (Real.sin (π * b / q))⁻¹ := by
  refine le_min ?_ ?_
  · calc
      ‖∑ n ∈ Ioc M (M + N), expTwoPiI ((b : ℝ) * n / q)‖
        ≤ ∑ _n ∈ Ioc M (M + N), ‖expTwoPiI ((b : ℝ) * _n / q)‖ := norm_sum_le _ _
      _ = N := by
          simp [norm_expTwoPiI, Int.card_Ioc]
  · rw [norm_sum_Ioc_expTwoPiI_mul_div_eq hb₀ hbq, inv_eq_one_div]
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    have hsin_pos : 0 < Real.sin (π * b / q) :=
      Real.sin_pos_of_pos_of_lt_pi (div_pos (mul_pos Real.pi_pos hbpos) hqpos)
        (by rw [div_lt_iff₀ hqpos]; nlinarith [Real.pi_pos, show (b : ℝ) < q by exact_mod_cast hbq])
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hsin_pos.le

end TauCeti

namespace DirichletCharacter

/-! ### Gauss-sum expansion of character interval sums -/

private lemma stdAddChar_intCast_eq_expTwoPiI {q : ℕ} [NeZero q] (k : ℤ) :
    ZMod.stdAddChar (k : ZMod q) = TauCeti.expTwoPiI ((k : ℝ) / q) := by
  rw [ZMod.stdAddChar_coe, TauCeti.expTwoPiI_def]
  congr 1
  push_cast
  ring

private lemma stdAddChar_natCast_mul_intCast {q : ℕ} [NeZero q] (b : ℕ) (n : ℤ) :
    ZMod.stdAddChar ((b : ZMod q) * (n : ZMod q)) = TauCeti.expTwoPiI ((b : ℝ) * n / q) := by
  rw [← Int.cast_natCast b, ← Int.cast_mul, stdAddChar_intCast_eq_expTwoPiI]
  congr 1
  push_cast
  ring

/-- **Gauss-sum expansion of a primitive character:** for `χ` primitive modulo `q ≥ 1` and
every integer `n`, `χ n * τ(χ⁻¹) = ∑_{b mod q} χ⁻¹ b * e(b.val * n / q)`. -/
theorem mul_gaussSum_inv_stdAddChar_eq_sum {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (n : ℤ) :
    χ n * gaussSum χ⁻¹ ZMod.stdAddChar =
      ∑ b : ZMod q, χ⁻¹ b * TauCeti.expTwoPiI ((b.val : ℝ) * n / q) := by
  have h := gaussSum_mulShift_of_isPrimitive (ZMod.stdAddChar (N := q)) hχ.inv (n : ZMod q)
  rw [inv_inv] at h
  rw [← h, gaussSum]
  refine sum_congr rfl fun b _ ↦ ?_
  rw [AddChar.mulShift_apply]
  congr 1
  calc
    ZMod.stdAddChar ((n : ZMod q) * b)
      = ZMod.stdAddChar ((b.val : ZMod q) * (n : ZMod q)) := by
        rw [mul_comm, ZMod.natCast_zmod_val]
    _ = TauCeti.expTwoPiI ((b.val : ℝ) * n / q) := stdAddChar_natCast_mul_intCast b.val n

/-- **Gauss-sum expansion of a character interval sum:** for `χ` primitive modulo `q ≥ 2`, `M : ℤ`,
and `N : ℕ`, `S_χ(M, N) = τ(χ⁻¹)⁻¹ * ∑_{1 ≤ b < q} χ⁻¹ b * ∑_{M < n ≤ M + N} e(b * n / q)`. -/
theorem intervalSum_eq_inv_gaussSum_mul_sum {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (M : ℤ) (N : ℕ) :
    χ.intervalSum M N = (gaussSum χ⁻¹ ZMod.stdAddChar)⁻¹ *
      ∑ b ∈ Ico 1 q, χ⁻¹ b * ∑ n ∈ Ioc M (M + N), TauCeti.expTwoPiI ((b : ℝ) * n / q) := by
  have htau : gaussSum χ⁻¹ ZMod.stdAddChar ≠ 0 :=
    gaussSum_inv_ne_zero_of_isPrimitive hχ (ZMod.isPrimitive_stdAddChar q)
  have hterm (n : ℤ) : χ n = (gaussSum χ⁻¹ ZMod.stdAddChar)⁻¹ *
      ∑ b ∈ Ico 1 q, χ⁻¹ b * TauCeti.expTwoPiI ((b : ℝ) * n / q) := by
    have hexp := mul_gaussSum_inv_stdAddChar_eq_sum hχ n
    have hZMod : (∑ b : ZMod q, χ⁻¹ b * TauCeti.expTwoPiI ((b.val : ℝ) * n / q)) =
        ∑ b ∈ Ico 1 q, χ⁻¹ b * TauCeti.expTwoPiI ((b : ℝ) * n / q) := by
      have hbij : ∑ b : ZMod q, χ⁻¹ b * TauCeti.expTwoPiI ((b.val : ℝ) * n / q) =
          ∑ b ∈ Ico 0 q, χ⁻¹ (b : ZMod q) * TauCeti.expTwoPiI ((b : ℝ) * n / q) := by
        symm
        refine sum_bij (fun (b : ℕ) _ ↦ (b : ZMod q)) (fun _ _ ↦ mem_univ _) ?_ ?_ ?_
        · intro a ha b hb hab
          rw [mem_Ico] at ha hb
          have hval := congrArg ZMod.val hab
          simpa only [ZMod.val_natCast_of_lt ha.2, ZMod.val_natCast_of_lt hb.2] using hval
        · intro x _
          exact ⟨x.val, mem_Ico.mpr ⟨Nat.zero_le _, ZMod.val_lt x⟩, ZMod.natCast_zmod_val x⟩
        · intro b hb
          rw [mem_Ico] at hb
          rw [ZMod.val_natCast_of_lt hb.2]
      have hI : Ico 0 q = insert 0 (Ico 1 q) := by
        ext b
        simp only [mem_Ico, mem_insert]
        omega
      have hzero : χ⁻¹ (0 : ZMod q) = 0 := χ⁻¹.map_zero' (by omega)
      rw [hbij, hI, sum_insert (by simp)]
      simp [hzero]
    rw [hZMod] at hexp
    rw [eq_inv_mul_iff_mul_eq₀ htau, mul_comm]
    exact hexp
  rw [intervalSum_def]
  calc
    ∑ n ∈ Ioc M (M + N), χ n
      = ∑ n ∈ Ioc M (M + N), (gaussSum χ⁻¹ ZMod.stdAddChar)⁻¹ *
          ∑ b ∈ Ico 1 q, χ⁻¹ b * TauCeti.expTwoPiI ((b : ℝ) * n / q) :=
        sum_congr rfl fun n _ ↦ hterm n
    _ = (gaussSum χ⁻¹ ZMod.stdAddChar)⁻¹ *
          ∑ n ∈ Ioc M (M + N), ∑ b ∈ Ico 1 q, χ⁻¹ b * TauCeti.expTwoPiI ((b : ℝ) * n / q) := by
        rw [mul_sum]
    _ = (gaussSum χ⁻¹ ZMod.stdAddChar)⁻¹ *
          ∑ b ∈ Ico 1 q, χ⁻¹ b * ∑ n ∈ Ioc M (M + N), TauCeti.expTwoPiI ((b : ℝ) * n / q) := by
        congr 1
        rw [sum_comm]
        refine sum_congr rfl fun b _ ↦ ?_
        rw [← mul_sum]

private lemma expTwoPiI_add_neg_eq_cos (θ : ℝ) :
    TauCeti.expTwoPiI θ + TauCeti.expTwoPiI (-θ) = 2 * (Real.cos (2 * π * θ) : ℂ) := by
  have h (t : ℝ) : TauCeti.expTwoPiI t = (Real.cos (2 * π * t) : ℂ) +
      (Real.sin (2 * π * t) : ℂ) * Complex.I := by
    rw [TauCeti.expTwoPiI_def,
      show 2 * (π : ℂ) * Complex.I * t = ((2 * π * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I]
    norm_cast
  rw [h θ, h (-θ)]
  simp only [mul_neg, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, neg_mul]
  ring

private lemma expTwoPiI_sub_neg_eq_sin (θ : ℝ) :
    TauCeti.expTwoPiI θ - TauCeti.expTwoPiI (-θ) =
      2 * Complex.I * (Real.sin (2 * π * θ) : ℂ) := by
  have h (t : ℝ) : TauCeti.expTwoPiI t = (Real.cos (2 * π * t) : ℂ) +
      (Real.sin (2 * π * t) : ℂ) * Complex.I := by
    rw [TauCeti.expTwoPiI_def,
      show 2 * (π : ℂ) * Complex.I * t = ((2 * π * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I]
    norm_cast
  rw [h θ, h (-θ)]
  simp only [mul_neg, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, neg_mul]
  ring

private lemma sum_Ico_reflect_sub {M : Type*} [AddCommMonoid M] (q : ℕ) (f : ℕ → M) :
    ∑ b ∈ Ico 1 q, f (q - b) = ∑ b ∈ Ico 1 q, f b := by
  refine sum_bij (fun b _ ↦ q - b) ?_ ?_ ?_ fun _ _ ↦ rfl
  · intro b hb
    rw [mem_Ico] at hb ⊢
    omega
  · intro a ha b hb hab
    rw [mem_Ico] at ha hb
    omega
  · intro b hb
    rw [mem_Ico] at hb
    exact ⟨q - b, mem_Ico.mpr (by omega), by omega⟩

private lemma expTwoPiI_natCast_sub_mul_div {b q : ℕ} (hbq : b ≤ q) (hq : 0 < q) (n : ℤ) :
    TauCeti.expTwoPiI (((q - b : ℕ) : ℝ) * n / q) =
      TauCeti.expTwoPiI (-((b : ℝ) * n / q)) := by
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  rw [Nat.cast_sub hbq,
    show (((q : ℝ) - b) * n / q) = -((b : ℝ) * n / q) + (n : ℤ) by field_simp; ring,
    TauCeti.expTwoPiI_add_intCast]

/-- For an even primitive character `χ` modulo `q ≥ 2`, only the cosine terms survive in the
Gauss-sum expansion of `S_χ(M, N)`. -/
theorem Even.intervalSum_eq_inv_gaussSum_mul_sum_cos {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχe : χ.Even) (hχ : χ.IsPrimitive) (hq : 2 ≤ q)
    (M : ℤ) (N : ℕ) :
    χ.intervalSum M N = (gaussSum χ⁻¹ ZMod.stdAddChar)⁻¹ *
      ∑ b ∈ Ico 1 q, χ⁻¹ b * ∑ n ∈ Ioc M (M + N), (Real.cos (2 * π * b * n / q) : ℂ) := by
  rw [intervalSum_eq_inv_gaussSum_mul_sum hχ hq M N]
  congr 1
  let f : ℕ → ℂ := fun b ↦
    χ⁻¹ b * ∑ n ∈ Ioc M (M + N), TauCeti.expTwoPiI ((b : ℝ) * n / q)
  have hpair (b : ℕ) (hb : b ∈ Ico 1 q) : f b + f (q - b) =
      2 * (χ⁻¹ b * ∑ n ∈ Ioc M (M + N), (Real.cos (2 * π * b * n / q) : ℂ)) := by
    have hbq : b ≤ q := (mem_Ico.mp hb).2.le
    have hχneg : χ⁻¹ ((q - b : ℕ) : ZMod q) = χ⁻¹ (b : ZMod q) := by
      have hcast : ((q - b : ℕ) : ZMod q) = -(b : ZMod q) := by
        rw [Nat.cast_sub hbq, ZMod.natCast_self, zero_sub]
      rw [hcast, show -(b : ZMod q) = (-1 : ZMod q) * (b : ZMod q) by ring, map_mul,
        MulChar.inv_apply_eq_inv', hχe, inv_one, one_mul]
    dsimp only [f]
    rw [hχneg, ← mul_add, ← sum_add_distrib]
    have hsum : (∑ n ∈ Ioc M (M + N),
          (TauCeti.expTwoPiI ((b : ℝ) * n / q) + TauCeti.expTwoPiI (((q - b : ℕ) : ℝ) * n / q))) =
        2 * ∑ n ∈ Ioc M (M + N), (Real.cos (2 * π * b * n / q) : ℂ) := by
      rw [mul_sum]
      refine sum_congr rfl fun n _ ↦ ?_
      rw [expTwoPiI_natCast_sub_mul_div hbq (by omega) n, expTwoPiI_add_neg_eq_cos,
        show 2 * π * ((b : ℝ) * n / q) = 2 * π * b * n / q by ring]
    rw [hsum]
    ring
  have h2 : (2 : ℂ) * ∑ b ∈ Ico 1 q, f b =
      2 * ∑ b ∈ Ico 1 q, χ⁻¹ b * ∑ n ∈ Ioc M (M + N), (Real.cos (2 * π * b * n / q) : ℂ) := by
    calc
      (2 : ℂ) * ∑ b ∈ Ico 1 q, f b = ∑ b ∈ Ico 1 q, f b + ∑ b ∈ Ico 1 q, f b := by ring
      _ = ∑ b ∈ Ico 1 q, f b + ∑ b ∈ Ico 1 q, f (q - b) := by rw [sum_Ico_reflect_sub]
      _ = ∑ b ∈ Ico 1 q, (f b + f (q - b)) := (sum_add_distrib).symm
      _ = ∑ b ∈ Ico 1 q,
          2 * (χ⁻¹ b * ∑ n ∈ Ioc M (M + N), (Real.cos (2 * π * b * n / q) : ℂ)) :=
        sum_congr rfl hpair
      _ = 2 * ∑ b ∈ Ico 1 q, χ⁻¹ b * ∑ n ∈ Ioc M (M + N), (Real.cos (2 * π * b * n / q) : ℂ) :=
        (mul_sum _ _ _).symm
  exact mul_left_cancel₀ two_ne_zero h2

/-- For an odd primitive character `χ` modulo `q ≥ 2`, only the sine terms survive in the
Gauss-sum expansion of `S_χ(M, N)`. -/
theorem Odd.intervalSum_eq_inv_gaussSum_mul_sum_sin {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχo : χ.Odd) (hχ : χ.IsPrimitive) (hq : 2 ≤ q)
    (M : ℤ) (N : ℕ) :
    χ.intervalSum M N = (gaussSum χ⁻¹ ZMod.stdAddChar)⁻¹ * Complex.I *
      ∑ b ∈ Ico 1 q, χ⁻¹ b * ∑ n ∈ Ioc M (M + N), (Real.sin (2 * π * b * n / q) : ℂ) := by
  rw [intervalSum_eq_inv_gaussSum_mul_sum hχ hq M N, mul_assoc]
  congr 1
  let f : ℕ → ℂ := fun b ↦
    χ⁻¹ b * ∑ n ∈ Ioc M (M + N), TauCeti.expTwoPiI ((b : ℝ) * n / q)
  have hpair (b : ℕ) (hb : b ∈ Ico 1 q) : f b + f (q - b) =
      2 * (Complex.I * (χ⁻¹ b * ∑ n ∈ Ioc M (M + N), (Real.sin (2 * π * b * n / q) : ℂ))) := by
    have hbq : b ≤ q := (mem_Ico.mp hb).2.le
    have hχneg : χ⁻¹ ((q - b : ℕ) : ZMod q) = -χ⁻¹ (b : ZMod q) := by
      have hcast : ((q - b : ℕ) : ZMod q) = -(b : ZMod q) := by
        rw [Nat.cast_sub hbq, ZMod.natCast_self, zero_sub]
      rw [hcast, show -(b : ZMod q) = (-1 : ZMod q) * (b : ZMod q) by ring, map_mul,
        MulChar.inv_apply_eq_inv', hχo, inv_neg, inv_one, neg_one_mul]
    dsimp only [f]
    rw [hχneg, neg_mul, ← sub_eq_add_neg, ← mul_sub, ← sum_sub_distrib]
    have hsum : (∑ n ∈ Ioc M (M + N),
          (TauCeti.expTwoPiI ((b : ℝ) * n / q) - TauCeti.expTwoPiI (-((b : ℝ) * n / q)))) =
        2 * Complex.I * ∑ n ∈ Ioc M (M + N), (Real.sin (2 * π * b * n / q) : ℂ) := by
      rw [mul_sum]
      refine sum_congr rfl fun n _ ↦ ?_
      rw [expTwoPiI_sub_neg_eq_sin, show 2 * π * ((b : ℝ) * n / q) = 2 * π * b * n / q by ring]
    calc
      χ⁻¹ b * ∑ n ∈ Ioc M (M + N), (TauCeti.expTwoPiI ((b : ℝ) * n / q) -
          TauCeti.expTwoPiI (((q - b : ℕ) : ℝ) * n / q))
        = χ⁻¹ b * ∑ n ∈ Ioc M (M + N), (TauCeti.expTwoPiI ((b : ℝ) * n / q) -
            TauCeti.expTwoPiI (-((b : ℝ) * n / q))) := by
          congr 1
          refine sum_congr rfl fun n _ ↦ ?_
          rw [expTwoPiI_natCast_sub_mul_div hbq (by omega) n]
      _ = χ⁻¹ b * (2 * Complex.I *
            ∑ n ∈ Ioc M (M + N), (Real.sin (2 * π * b * n / q) : ℂ)) := by rw [hsum]
      _ = 2 * (Complex.I * (χ⁻¹ b *
            ∑ n ∈ Ioc M (M + N), (Real.sin (2 * π * b * n / q) : ℂ))) := by ring
  have h2 : (2 : ℂ) * ∑ b ∈ Ico 1 q, f b = 2 * (Complex.I *
      ∑ b ∈ Ico 1 q, χ⁻¹ b * ∑ n ∈ Ioc M (M + N), (Real.sin (2 * π * b * n / q) : ℂ)) := by
    calc
      (2 : ℂ) * ∑ b ∈ Ico 1 q, f b = ∑ b ∈ Ico 1 q, f b + ∑ b ∈ Ico 1 q, f b := by ring
      _ = ∑ b ∈ Ico 1 q, f b + ∑ b ∈ Ico 1 q, f (q - b) := by rw [sum_Ico_reflect_sub]
      _ = ∑ b ∈ Ico 1 q, (f b + f (q - b)) := (sum_add_distrib).symm
      _ = ∑ b ∈ Ico 1 q, 2 * (Complex.I *
          (χ⁻¹ b * ∑ n ∈ Ioc M (M + N), (Real.sin (2 * π * b * n / q) : ℂ))) :=
        sum_congr rfl hpair
      _ = 2 * (Complex.I * ∑ b ∈ Ico 1 q,
          χ⁻¹ b * ∑ n ∈ Ioc M (M + N), (Real.sin (2 * π * b * n / q) : ℂ)) := by
        rw [← mul_sum, ← mul_sum]
  exact mul_left_cancel₀ two_ne_zero h2

/-- Bounding every character interval sum of a primitive character modulo `q ≥ 2` by the
normalized sum of `min N (sin (π * b / q))⁻¹`. -/
theorem norm_intervalSum_le_inv_sqrt_mul_sum_min {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (M : ℤ) (N : ℕ) :
    ‖χ.intervalSum M N‖ ≤
      (Real.sqrt q)⁻¹ * ∑ b ∈ Ico 1 q, min (N : ℝ) (Real.sin (π * b / q))⁻¹ := by
  have : NeZero q := ⟨by omega⟩
  rw [intervalSum_eq_inv_gaussSum_mul_sum hχ hq M N, norm_mul, norm_inv,
    hχ.inv.norm_gaussSum (ZMod.isPrimitive_stdAddChar q)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans (sum_le_sum fun b hb ↦ ?_)
  rw [norm_mul]
  calc
    ‖χ⁻¹ (b : ZMod q)‖ * ‖∑ n ∈ Ioc M (M + N), TauCeti.expTwoPiI ((b : ℝ) * n / q)‖
      ≤ 1 * min (N : ℝ) (Real.sin (π * b / q))⁻¹ := by
        gcongr
        · exact χ⁻¹.norm_le_one _
        · rw [mem_Ico] at hb
          exact TauCeti.norm_sum_Ioc_expTwoPiI_mul_div_le hb.1 hb.2 M N
    _ = min (N : ℝ) (Real.sin (π * b / q))⁻¹ := one_mul _

/-! ### The classical explicit Pólya–Vinogradov inequality -/

/-- **Classical explicit Pólya–Vinogradov inequality.** For a primitive complex Dirichlet
character `χ` modulo `q ≥ 2` and all `M : ℤ`, `N : ℕ`,
`‖S_χ(M, N)‖ < (2 / π) * √q * (log q + log (4 / π) + π ^ 2 / (12 * q ^ 2))`. -/
theorem polya_vinogradov_classical {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : 2 ≤ q) (M : ℤ) (N : ℕ) :
    ‖χ.intervalSum M N‖ <
      2 / π * Real.sqrt q * (Real.log q + Real.log (4 / π) + π ^ 2 / (12 * (q : ℝ) ^ 2)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hsqrt_pos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hqpos
  have hmin : ∑ b ∈ Ico 1 q, min (N : ℝ) (Real.sin (π * b / q))⁻¹ ≤
      ∑ b ∈ Ico 1 q, (Real.sin (π * b / q))⁻¹ :=
    sum_le_sum fun _ _ ↦ min_le_right _ _
  have hcsc := TauCeti.sum_Ico_inv_sin_pi_mul_div_lt hq
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
`χ ≠ 1` modulo `q ≥ 1` with conductor `q*` and `r` the product of primes dividing `q` but not `q*`,
`M_χ < 2 ^ ω r * (2 / π * √q* * (log q* + log (4 / π) + π ^ 2 / (12 * q* ^ 2)))`. -/
theorem maxIntervalSum_lt_of_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) :
    χ.maxIntervalSum <
      2 ^ ω (∏ p ∈ q.primeFactors with ¬ p ∣ χ.conductor, p) *
        (2 / π * Real.sqrt χ.conductor *
          (Real.log χ.conductor + Real.log (4 / π) + π ^ 2 / (12 * (χ.conductor : ℝ) ^ 2))) := by
  have hc₀ : χ.conductor ≠ 0 := χ.conductor_ne_zero
  have hc₁ : χ.conductor ≠ 1 := mt χ.eq_one_iff_conductor_eq_one.mpr hχ
  have hc₂ : 2 ≤ χ.conductor := by omega
  have hωpos : (0 : ℝ) < 2 ^ ω (∏ p ∈ q.primeFactors with ¬ p ∣ χ.conductor, p) := by positivity
  calc
    χ.maxIntervalSum
      ≤ 2 ^ ω (∏ p ∈ q.primeFactors with ¬ p ∣ χ.conductor, p) *
          χ.primitiveCharacter.maxIntervalSum :=
        maxIntervalSum_le_two_pow_omega_mul_primitiveCharacter hχ
    _ < 2 ^ ω (∏ p ∈ q.primeFactors with ¬ p ∣ χ.conductor, p) *
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
      2 ^ ω (∏ p ∈ q.primeFactors with ¬ p ∣ χ.conductor, p) *
        (2 / π * Real.sqrt χ.conductor *
          (Real.log χ.conductor + Real.log (4 / π) + π ^ 2 / (12 * (χ.conductor : ℝ) ^ 2))) :=
  (norm_intervalSum_le_maxIntervalSum hχ M N).trans_lt (χ.maxIntervalSum_lt_of_ne_one hχ)

private lemma three_le_of_prime_of_ne_one {p : ℕ} (hp : p.Prime) {χ : DirichletCharacter ℂ p}
    (hχ : χ ≠ 1) : 3 ≤ p := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    apply hχ
    ext u
    have hu : u = 1 := by
      fin_cases u
      rfl
    simp [hu]
  have := hp.two_le
  omega

/-- Every interval sum of a nonprincipal character modulo a prime `p` has norm strictly less than
`√p * log p`. -/
theorem norm_intervalSum_lt_sqrt_mul_log {p : ℕ} (hp : p.Prime) (χ : DirichletCharacter ℂ p)
    (hχ : χ ≠ 1) (M : ℤ) (N : ℕ) :
    ‖χ.intervalSum M N‖ < Real.sqrt p * Real.log p := by
  have hp3 : 3 ≤ p := three_le_of_prime_of_ne_one hp hχ
  have hprim := isPrimitive_of_ne_one_of_prime hp hχ
  calc
    ‖χ.intervalSum M N‖
      < 2 / π * Real.sqrt p *
          (Real.log p + Real.log (4 / π) + π ^ 2 / (12 * (p : ℝ) ^ 2)) :=
        χ.polya_vinogradov_classical hprim (by omega) M N
    _ = Real.sqrt p *
          (2 / π * (Real.log p + Real.log (4 / π) + π ^ 2 / (12 * (p : ℝ) ^ 2))) := by ring
    _ ≤ Real.sqrt p * Real.log p :=
        mul_le_mul_of_nonneg_left
          (TauCeti.two_div_pi_mul_log_add_le_log (by exact_mod_cast hp3))
          (Real.sqrt_nonneg _)

/-- The maximal interval sum of a nonprincipal character modulo a prime `p` is strictly less than
`√p * log p`. -/
theorem maxIntervalSum_lt_sqrt_mul_log {p : ℕ} [NeZero p] (hp : p.Prime)
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    χ.maxIntervalSum < Real.sqrt p * Real.log p := by
  obtain ⟨M, -, N, -, hMN⟩ := χ.exists_norm_intervalSum_eq_maxIntervalSum
  rw [← hMN]
  exact χ.norm_intervalSum_lt_sqrt_mul_log hp hχ M N

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
