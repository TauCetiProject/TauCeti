/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.NumberTheory.DirichletCharacter.GroupDeterminant
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.NumberTheory.DirichletCharacter.Even
import TauCeti.NumberTheory.DirichletCharacter.LFunction.TrivialZeros
import TauCeti.NumberTheory.MulChar.Basic
import TauCeti.NumberTheory.ZetaValues

/-!
# Size bounds for generalized Bernoulli numbers and the Bernoulli group determinant

From the uniform bound `|Bₖ(x)| ≤ 4 k! / (2π)ᵏ` on `[0, 1]`
(`TauCeti.abs_bernoulliFun_le_four_mul_factorial_div`) and `Pₖ₊₁ ≤ 4ᵏ⁺¹` for the primorial
`Pₖ₊₁ = primorial (k + 1)`, this file bounds the generalized Bernoulli numbers `Bₖ,χ` of complex
Dirichlet characters modulo `N` and the nonzero integer `TauCeti.bernoulliGroupDet M k`, the
Bernoulli group determinant of `(ZMod M)ˣ`.

## Main results

* `DirichletCharacter.norm_generalizedBernoulli_le`: `‖Bₖ,χ‖ ≤ Nᵏ · 4 k! / (2π)ᵏ`.
* `DirichletCharacter.norm_primorial_mul_natCast_mul_generalizedBernoulli_le`:
  `‖Pₖ₊₁ N Bₖ,χ‖ ≤ 16 Nᵏ⁺¹ k!`. For `k = e + 1` this is the bound
  `|N P_{e+2} B_{e+1,ψ}| ≤ 16 N^{e+2} (e + 1)!` behind the estimate of
  BernoulliBoundsForClassGroupEigenspaces §10.1 (b).
* `TauCeti.abs_primorialBernoulli_le`: the integers `Pₖ₊₁ Mᵏ Bₖ(⟨t⟩ / M)` have absolute value
  at most `16 Mᵏ k!`.
* `TauCeti.abs_bernoulliGroupDet_le`: for `k ≥ 2`,
  `|bernoulliGroupDet M k| ≤ (32 Mᵏ⁺¹ k!) ^ φ(M)`.
* `TauCeti.sq_bernoulliGroupDet_le`: for `k ≥ 2` and `M > 2`,
  `bernoulliGroupDet M k ^ 2 ≤ (64 Mᵏ⁺¹ k!) ^ φ(M)`, so that
  `log |bernoulliGroupDet M k| ≤ φ(M) / 2 · log (64 Mᵏ⁺¹ k!)`.

The determinant bounds go through the eigenvalue factorization
`TauCeti.bernoulliGroupDet_eq_prod` over `ℂ`: the `φ(M)` eigenvalues are `2 Pₖ₊₁ M Bₖ,χ` for the
characters with `χ(-1) = (-1)ᵏ` and `±2` for the others, and above level two exactly half of the
characters have each parity (`DirichletCharacter.two_mul_card_apply_neg_one_eq`). This is the size
bound of the determinant `Δ` in step (3) of the route of UniformWildKernelBounds §6.5, for the full
group `(ZMod M)ˣ`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Chapter 4 (generalized
  Bernoulli numbers) and Lemma 5.26 (the group determinant).

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
PBC), file `src/Lib/Cyclotomic/Voronoi.lean`, the size bound in the proof of
`New.OddPart.exists_isStickelbergerBound` (with `New.OddPart.mul_sub_one_mul_le_two_pow_of_le`).
There the determinant is bounded entrywise by Hadamard's inequality, giving
`|det| ≤ φ(N)! (64 (e + 2)! Nᵉ⁺¹ (e + 1)!) ^ φ(N)`; here it is bounded through its eigenvalues, the
Bernoulli values are normalised by the primorial instead of factorials, and the Bernoulli
polynomial bound is Tau Ceti's `TauCeti.abs_bernoulliFun_le_four_mul_factorial_div`.
-/

public section

open Finset Real
open scoped Nat

/-- `Pₖ₊₁ · 4 k! / (2π)ᵏ ≤ 16 k!`, from `Pₖ₊₁ ≤ 4ᵏ⁺¹` and `4 ≤ 2π`. -/
private theorem primorial_mul_four_mul_factorial_div_le (k : ℕ) :
    (primorial (k + 1) : ℝ) * (4 * k ! / (2 * π) ^ k) ≤ 16 * k ! := by
  have hP : (primorial (k + 1) : ℝ) ≤ 4 ^ (k + 1) := mod_cast primorial_le_four_pow (k + 1)
  have h4 : (4 : ℝ) ^ k ≤ (2 * π) ^ k := by
    gcongr
    linarith [pi_gt_three]
  have hpos : (0 : ℝ) < (2 * π) ^ k := by positivity
  calc (primorial (k + 1) : ℝ) * (4 * k ! / (2 * π) ^ k)
      ≤ 4 ^ (k + 1) * (4 * k ! / (2 * π) ^ k) := by gcongr
    _ = 16 * k ! * (4 ^ k / (2 * π) ^ k) := by ring
    _ ≤ 16 * k ! * 1 := by gcongr; exact (div_le_one hpos).2 h4
    _ = 16 * k ! := mul_one _

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- **The size of a generalized Bernoulli number.** For a complex Dirichlet character `χ`
modulo `N`, `‖Bₖ,χ‖ ≤ Nᵏ · 4 k! / (2π)ᵏ`, where `Bₖ,χ` is the generalized Bernoulli number at the
modulus `N`. -/
theorem norm_generalizedBernoulli_le (χ : DirichletCharacter ℂ N) (k : ℕ) :
    ‖χ.generalizedBernoulli k‖ ≤ N ^ k * (4 * k ! / (2 * π) ^ k) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  -- each term `χ(a) Bₖ(ã / N)`, with `ã ∈ [1, N]`, has norm at most `4 k! / (2π)ᵏ`
  have hterm (a : ZMod N) : ‖χ a * algebraMap ℚ ℂ ((Polynomial.bernoulli k).eval
      (((if a = 0 then N else a.val : ℕ) : ℚ) / N))‖ ≤ 4 * k ! / (2 * π) ^ k := by
    set n : ℕ := if a = 0 then N else a.val
    have hn : n ≤ N := by
      simp only [n]
      split_ifs
      exacts [le_rfl, (ZMod.val_lt a).le]
    have hx : ((n : ℝ) / N) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hN).2 (mod_cast hn)⟩
    have h := TauCeti.abs_bernoulliFun_le_four_mul_factorial_div k hx
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one a)).trans ?_
    have hb := TauCeti.bernoulliFun_ratCast k ((n : ℚ) / N)
    rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast] at hb
    rwa [eq_ratCast, Complex.norm_ratCast, ← hb]
  rw [generalizedBernoulli_def, norm_mul, eq_ratCast, Complex.norm_ratCast]
  calc |(((N : ℚ) ^ ((k : ℤ) - 1) : ℚ) : ℝ)| * ‖∑ a : ZMod N, _‖
      ≤ (N : ℝ) ^ ((k : ℤ) - 1) * ∑ _a : ZMod N, 4 * k ! / (2 * π) ^ k := by
        rw [Rat.cast_zpow, Rat.cast_natCast, abs_of_pos (zpow_pos hN _)]
        gcongr
        exact (norm_sum_le _ _).trans (sum_le_sum fun a _ ↦ hterm a)
    _ = N ^ k * (4 * k ! / (2 * π) ^ k) := by
        rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul, ← mul_assoc, zpow_sub₀ hN.ne',
          zpow_one, zpow_natCast, div_mul_cancel₀ _ hN.ne']

/-- **The size of `Pₖ₊₁ N Bₖ,χ`.** For a complex Dirichlet character `χ` modulo `N`,
`‖Pₖ₊₁ N Bₖ,χ‖ ≤ 16 Nᵏ⁺¹ k!`, where `Pₖ₊₁ = primorial (k + 1)`. For `k = e + 1` this is the
bound `|N P_{e+2} B_{e+1,ψ}| ≤ 16 N^{e+2} (e + 1)!` behind BernoulliBoundsForClassGroupEigenspaces
§10.1 (b). -/
theorem norm_primorial_mul_natCast_mul_generalizedBernoulli_le (χ : DirichletCharacter ℂ N)
    (k : ℕ) :
    ‖(primorial (k + 1) : ℂ) * N * χ.generalizedBernoulli k‖ ≤ 16 * N ^ (k + 1) * k ! := by
  rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  calc (primorial (k + 1) : ℝ) * N * ‖χ.generalizedBernoulli k‖
      ≤ primorial (k + 1) * N * (N ^ k * (4 * k ! / (2 * π) ^ k)) := by
        gcongr
        exact χ.norm_generalizedBernoulli_le k
    _ = N ^ (k + 1) * (primorial (k + 1) * (4 * k ! / (2 * π) ^ k)) := by ring
    _ ≤ N ^ (k + 1) * (16 * k !) :=
        mul_le_mul_of_nonneg_left (primorial_mul_four_mul_factorial_div_le k) (by positivity)
    _ = 16 * N ^ (k + 1) * k ! := by ring

end DirichletCharacter

namespace TauCeti

open _root_.DirichletCharacter

/-- **The size of the Bernoulli entries.** `|Pₖ₊₁ Mᵏ Bₖ(⟨t⟩ / M)| ≤ 16 Mᵏ k!`. -/
theorem abs_primorialBernoulli_le (M k : ℕ) (t : ZMod M) :
    |primorialBernoulli M k t| ≤ 16 * M ^ k * k ! := by
  have hx : ((t.val : ℝ) / M) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rcases eq_or_ne M 0 with rfl | hM
    · simp
    · have : NeZero M := ⟨hM⟩
      exact div_le_one_of_le₀ (mod_cast (ZMod.val_lt t).le) (Nat.cast_nonneg M)
  have h := abs_bernoulliFun_le_four_mul_factorial_div k hx
  have hcast : (primorialBernoulli M k t : ℝ) =
      primorial (k + 1) * M ^ k * bernoulliFun k ((t.val : ℝ) / M) := by
    have := congrArg (Rat.cast : ℚ → ℝ) (intCast_primorialBernoulli M k t)
    have hb := bernoulliFun_ratCast k ((t.val : ℚ) / M)
    rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast] at hb
    rw [hb]
    exact_mod_cast this
  have hR : (|primorialBernoulli M k t| : ℝ) ≤ 16 * M ^ k * k ! := by
    rw [hcast, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ _),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (M : ℝ) ^ k)]
    calc (primorial (k + 1) : ℝ) * M ^ k * |bernoulliFun k ((t.val : ℝ) / M)|
        ≤ M ^ k * (primorial (k + 1) * (4 * k ! / (2 * π) ^ k)) := by
          rw [mul_comm (primorial (k + 1) : ℝ), mul_assoc]
          gcongr
      _ ≤ M ^ k * (16 * k !) :=
          mul_le_mul_of_nonneg_left (primorial_mul_four_mul_factorial_div_le k) (by positivity)
      _ = 16 * M ^ k * k ! := by ring
  exact_mod_cast hR

variable {M : ℕ} [NeZero M] {k : ℕ}

/-- The norm of an eigenvalue `2 Pₖ₊₁ M Bₖ,χ - (-1)ᵏ + χ(-1)` of the Bernoulli group matrix is at
most `32 Mᵏ⁺¹ k!` when `χ(-1) = (-1)ᵏ`, and is `2` otherwise. -/
private theorem norm_bernoulliGroupEigenvalue_le (hk : 2 ≤ k) (χ : DirichletCharacter ℂ M) :
    ‖2 * ((primorial (k + 1) : ℂ) * M * χ.generalizedBernoulli k) - (-1) ^ k + χ (-1)‖ ≤
      if χ (-1) = (-1) ^ k then 32 * (M : ℝ) ^ (k + 1) * (k ! : ℝ) else 2 := by
  split_ifs with hχ
  · rw [hχ, sub_add_cancel, norm_mul, Complex.norm_ofNat]
    linarith [χ.norm_primorial_mul_natCast_mul_generalizedBernoulli_le k]
  · rcases χ.apply_neg_one_eq_neg_one_pow_or k with h | h
    · exact absurd h hχ
    · rw [(generalizedBernoulli_eq_zero_iff hk).2 h, h]
      simp [← two_mul]

/-- **The size of the Bernoulli group determinant.** For `k ≥ 2`,
`|bernoulliGroupDet M k| ≤ (32 Mᵏ⁺¹ k!) ^ φ(M)`. -/
theorem abs_bernoulliGroupDet_le (hk : 2 ≤ k) :
    |bernoulliGroupDet M k| ≤ (32 * M ^ (k + 1) * k !) ^ M.totient := by
  have hM : (1 : ℝ) ≤ M := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne M))
  have h1 : (2 : ℝ) ≤ 32 * M ^ (k + 1) * k ! := by
    have : (1 : ℝ) ≤ M ^ (k + 1) * k ! :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM) (mod_cast Nat.one_le_iff_ne_zero.2
        (Nat.factorial_ne_zero k))
    linarith
  have hR : (|bernoulliGroupDet M k| : ℝ) ≤ (32 * M ^ (k + 1) * k !) ^ M.totient := by
    rw [← Complex.norm_intCast, bernoulliGroupDet_eq_prod hk ℂ, norm_prod,
      ← card_eq_totient_of_hasEnoughRootsOfUnity ℂ M, Nat.card_eq_fintype_card,
      ← card_univ, ← prod_const]
    refine prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun χ _ ↦
      (norm_bernoulliGroupEigenvalue_le hk χ).trans ?_
    split_ifs
    exacts [le_rfl, h1]
  exact_mod_cast hR

/-- **The size of the Bernoulli group determinant, above level two.** For `k ≥ 2` and `M > 2`,
`bernoulliGroupDet M k ^ 2 ≤ (64 Mᵏ⁺¹ k!) ^ φ(M)`: half of the `φ(M)` eigenvalues are `±2`, and
the other half have absolute value at most `32 Mᵏ⁺¹ k!`. -/
theorem sq_bernoulliGroupDet_le (hk : 2 ≤ k) (hM : 2 < M) :
    bernoulliGroupDet M k ^ 2 ≤ (64 * M ^ (k + 1) * k !) ^ M.totient := by
  classical
  set B : ℝ := 32 * (M : ℝ) ^ (k + 1) * (k ! : ℝ)
  -- the characters of parity `(-1)ᵏ` are half of all characters
  set c := #{χ : DirichletCharacter ℂ M | χ (-1) = (-1) ^ k}
  have hc : 2 * c = M.totient := by
    rw [← two_mul_card_apply_neg_one_eq hM (neg_one_pow_eq_or ℂ k), Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  have hc' : #{χ : DirichletCharacter ℂ M | ¬χ (-1) = (-1) ^ k} = c := by
    rw [filter_not, card_sdiff_of_subset (filter_subset _ _), card_univ,
      ← Nat.card_eq_fintype_card, card_eq_totient_of_hasEnoughRootsOfUnity]
    omega
  have hR : (|bernoulliGroupDet M k| : ℝ) ≤ B ^ c * 2 ^ c := by
    rw [← Complex.norm_intCast, bernoulliGroupDet_eq_prod hk ℂ, norm_prod]
    refine (prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun χ _ ↦
      norm_bernoulliGroupEigenvalue_le hk χ).trans_eq ?_
    rw [prod_ite, prod_const, prod_const, hc']
  have hR2 : ((bernoulliGroupDet M k ^ 2 : ℤ) : ℝ) ≤ (64 * M ^ (k + 1) * k !) ^ M.totient := by
    rw [Int.cast_pow, ← sq_abs, ← hc]
    calc |(bernoulliGroupDet M k : ℝ)| ^ 2 ≤ (B ^ c * 2 ^ c) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hR 2
      _ = (64 * M ^ (k + 1) * k ! : ℝ) ^ (2 * c) := by
          rw [← mul_pow, ← pow_mul, mul_comm c 2]
          congr 1
          simp only [B]
          ring
  exact_mod_cast hR2

end TauCeti
