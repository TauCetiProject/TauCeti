/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
public import TauCeti.NumberTheory.CircleMethod.AdditiveCharacter
public import TauCeti.NumberTheory.DirichletCharacter.IntervalSum
import TauCeti.Data.ZMod.FinEquiv
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.GaussSum
import TauCeti.NumberTheory.GaussSum.Trigonometric

/-!
# Trigonometric expansions of Dirichlet character sums

Combining `gaussSum_mulShift_of_isPrimitive` with `MulChar.gaussSum_eq_sum_mul_re_of_even`
and `MulChar.gaussSum_eq_I_mul_sum_mul_im_of_odd` gives
`DirichletCharacter.Even.intervalSum_mul_gaussSum_eq_sum_re` and
`DirichletCharacter.Odd.intervalSum_mul_gaussSum_eq_I_mul_sum_im` for primitive characters.
Specializing to the standard additive character `ZMod.stdAddChar` and isolating the `1 ≤ b < q`
frequencies gives:

* `DirichletCharacter.mul_gaussSum_inv_stdAddChar_eq_sum`: the primitive-character Gauss-sum
  expansion at `ZMod.stdAddChar`;
* `DirichletCharacter.intervalSum_eq_inv_gaussSum_mul_sum`: the full exponential expansion;
* `DirichletCharacter.Even.intervalSum_eq_inv_gaussSum_mul_sum_cos`: the cosine expansion for even
  primitive characters;
* `DirichletCharacter.Odd.intervalSum_eq_inv_gaussSum_mul_sum_sin`: the sine expansion for odd
  primitive characters.

See C. Pomerance, *Remarks on the Pólya–Vinogradov inequality*, equations (8)–(10).
-/

public section

open Finset
open scoped Real

namespace DirichletCharacter

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- The cosine expansion of the interval sum of an even primitive character, multiplied by
the Gauss sum of its inverse. -/
theorem Even.intervalSum_mul_gaussSum_eq_sum_re (hχ : χ.Even) (hprim : χ.IsPrimitive)
    (e : AddChar (ZMod q) ℂ) (M : ℤ) (N : ℕ) :
    χ.intervalSum M N * gaussSum χ⁻¹ e =
      ∑ b : ZMod q, χ⁻¹ b * ∑ n ∈ Ioc M (M + N), (e ((n : ZMod q) * b)).re := by
  have hneg : χ (-1) = 1 := hχ
  have hinv : χ⁻¹.Even := by
    simp only [Even, MulChar.inv_apply_eq_inv', hneg, inv_one]
  have hshift (a : ZMod q) : gaussSum χ⁻¹ (e.mulShift a) = χ a * gaussSum χ⁻¹ e := by
    simpa only [inv_inv] using gaussSum_mulShift_of_isPrimitive e hprim.inv a
  rw [intervalSum_def, sum_mul]
  simp_rw [← hshift, MulChar.gaussSum_eq_sum_mul_re_of_even χ⁻¹ _ hinv.to_fun,
    AddChar.mulShift_apply]
  rw [sum_comm]
  simp only [Complex.ofReal_sum, mul_sum]

/-- The sine expansion of the interval sum of an odd primitive character, multiplied by
the Gauss sum of its inverse. -/
theorem Odd.intervalSum_mul_gaussSum_eq_I_mul_sum_im (hχ : χ.Odd) (hprim : χ.IsPrimitive)
    (e : AddChar (ZMod q) ℂ) (M : ℤ) (N : ℕ) :
    χ.intervalSum M N * gaussSum χ⁻¹ e =
      Complex.I * ∑ b : ZMod q, χ⁻¹ b * ∑ n ∈ Ioc M (M + N), (e ((n : ZMod q) * b)).im := by
  have hneg : χ (-1) = -1 := hχ
  have hinv : χ⁻¹.Odd := by
    simp only [Odd, MulChar.inv_apply_eq_inv', hneg, inv_neg, inv_one]
  have hshift (a : ZMod q) : gaussSum χ⁻¹ (e.mulShift a) = χ a * gaussSum χ⁻¹ e := by
    simpa only [inv_inv] using gaussSum_mulShift_of_isPrimitive e hprim.inv a
  rw [intervalSum_def, sum_mul]
  simp_rw [← hshift, MulChar.gaussSum_eq_I_mul_sum_mul_im_of_odd χ⁻¹ _ hinv.to_fun,
    AddChar.mulShift_apply]
  rw [← mul_sum, sum_comm]
  simp only [Complex.ofReal_sum, mul_sum]

/-- **Gauss-sum expansion of a primitive character:** for `χ` primitive modulo `q ≥ 1` and
every integer `n`, `χ n * τ(χ⁻¹) = ∑_{b mod q} χ⁻¹ b * e(b.val * n / q)`. -/
theorem mul_gaussSum_inv_stdAddChar_eq_sum (hχ : χ.IsPrimitive) (n : ℤ) :
    χ n * gaussSum χ⁻¹ ZMod.stdAddChar =
      ∑ b : ZMod q, χ⁻¹ b * TauCeti.expTwoPiI ((b.val : ℝ) * n / q) := by
  have h := gaussSum_mulShift_of_isPrimitive (ZMod.stdAddChar (N := q)) hχ.inv (n : ZMod q)
  rw [inv_inv] at h
  rw [← h, gaussSum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  have hb :
      ZMod.stdAddChar ((n : ZMod q) * b) = ZMod.stdAddChar ((n : ZMod q) * (b.val : ZMod q)) :=
    congrArg (fun x : ZMod q ↦ ZMod.stdAddChar ((n : ZMod q) * x)) b.natCast_zmod_val.symm
  rw [AddChar.mulShift_apply, hb, TauCeti.stdAddChar_intCast_mul_natCast]

/-- **Gauss-sum expansion of a character interval sum:** for `χ` primitive modulo `q ≥ 2`, `M : ℤ`,
and `N : ℕ`, `S_χ(M, N) = τ(χ⁻¹)⁻¹ * ∑_{1 ≤ b < q} χ⁻¹ b * ∑_{M < n ≤ M + N} e(b * n / q)`. -/
theorem intervalSum_eq_inv_gaussSum_mul_sum (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (M : ℤ) (N : ℕ) :
    χ.intervalSum M N = (gaussSum χ⁻¹ ZMod.stdAddChar)⁻¹ *
      ∑ b ∈ Ico 1 q, χ⁻¹ b * ∑ n ∈ Ioc M (M + N), TauCeti.expTwoPiI ((b : ℝ) * n / q) := by
  have htau : gaussSum χ⁻¹ ZMod.stdAddChar ≠ 0 :=
    gaussSum_inv_ne_zero_of_isPrimitive hχ (ZMod.isPrimitive_stdAddChar q)
  have hterm (n : ℤ) : χ n = (gaussSum χ⁻¹ ZMod.stdAddChar)⁻¹ *
      ∑ b ∈ Ico 1 q, χ⁻¹ b * TauCeti.expTwoPiI ((b : ℝ) * n / q) := by
    have hsum : (∑ b : ZMod q, χ⁻¹ b * TauCeti.expTwoPiI ((b.val : ℝ) * n / q)) =
        ∑ b ∈ Ico 1 q, χ⁻¹ b * TauCeti.expTwoPiI ((b : ℝ) * n / q) := by
      simpa only [ZMod.natCast_zmod_val] using
        ZMod.sum_val_eq_sum_Ico_one (n := q)
          (fun b ↦ χ⁻¹ (b : ZMod q) * TauCeti.expTwoPiI ((b : ℝ) * n / q))
          (by simp [χ⁻¹.map_zero' (by omega)])
    rw [eq_inv_mul_iff_mul_eq₀ htau, mul_comm, ← hsum]
    exact mul_gaussSum_inv_stdAddChar_eq_sum hχ n
  rw [intervalSum_def, sum_congr rfl fun n _ ↦ hterm n, ← mul_sum, sum_comm]
  congr 1
  exact sum_congr rfl fun b _ ↦ (mul_sum _ _ _).symm

/-- For an even primitive character `χ` modulo `q ≥ 2`, only the cosine terms survive in the
Gauss-sum expansion of `S_χ(M, N)`. -/
theorem Even.intervalSum_eq_inv_gaussSum_mul_sum_cos (hχe : χ.Even) (hχ : χ.IsPrimitive)
    (hq : 2 ≤ q) (M : ℤ) (N : ℕ) :
    χ.intervalSum M N = (gaussSum χ⁻¹ ZMod.stdAddChar)⁻¹ *
      ∑ b ∈ Ico 1 q, χ⁻¹ b * ∑ n ∈ Ioc M (M + N), (Real.cos (2 * π * b * n / q) : ℂ) := by
  have htau : gaussSum χ⁻¹ ZMod.stdAddChar ≠ 0 :=
    gaussSum_inv_ne_zero_of_isPrimitive hχ (ZMod.isPrimitive_stdAddChar q)
  have hre := hχe.intervalSum_mul_gaussSum_eq_sum_re hχ ZMod.stdAddChar M N
  simp only [Complex.ofReal_sum] at hre
  have hterm (b : ℕ) (n : ℤ) :
      (ZMod.stdAddChar ((n : ZMod q) * (b : ZMod q))).re = Real.cos (2 * π * b * n / q) := by
    rw [TauCeti.stdAddChar_intCast_mul_natCast, TauCeti.re_expTwoPiI]
    congr 1
    ring
  have hsum : (∑ b : ZMod q, χ⁻¹ b *
        ∑ n ∈ Ioc M (M + N), ((ZMod.stdAddChar ((n : ZMod q) * b)).re : ℂ)) =
      ∑ b ∈ Ico 1 q, χ⁻¹ b * ∑ n ∈ Ioc M (M + N), (Real.cos (2 * π * b * n / q) : ℂ) := by
    simpa only [ZMod.natCast_zmod_val, hterm] using
      ZMod.sum_val_eq_sum_Ico_one (n := q)
        (fun b ↦ χ⁻¹ (b : ZMod q) *
          ∑ n ∈ Ioc M (M + N), ((ZMod.stdAddChar ((n : ZMod q) * (b : ZMod q))).re : ℂ))
        (by simp [χ⁻¹.map_zero' (by omega)])
  rw [eq_inv_mul_iff_mul_eq₀ htau, mul_comm, hre, hsum]

/-- For an odd primitive character `χ` modulo `q`, only the sine terms survive in the Gauss-sum
expansion of `S_χ(M, N)`. -/
theorem Odd.intervalSum_eq_inv_gaussSum_mul_sum_sin (hχo : χ.Odd) (hχ : χ.IsPrimitive)
    (M : ℤ) (N : ℕ) :
    χ.intervalSum M N = (gaussSum χ⁻¹ ZMod.stdAddChar)⁻¹ * Complex.I *
      ∑ b ∈ Ico 1 q, χ⁻¹ b * ∑ n ∈ Ioc M (M + N), (Real.sin (2 * π * b * n / q) : ℂ) := by
  have hχ1 : χ ≠ 1 := fun h ↦ Odd.not_even 1 (h ▸ hχo) even_one
  have hq : 2 ≤ q := by
    have := χ.three_le_level_of_ne_one hχ1
    omega
  have htau : gaussSum χ⁻¹ ZMod.stdAddChar ≠ 0 :=
    gaussSum_inv_ne_zero_of_isPrimitive hχ (ZMod.isPrimitive_stdAddChar q)
  have him := hχo.intervalSum_mul_gaussSum_eq_I_mul_sum_im hχ ZMod.stdAddChar M N
  simp only [Complex.ofReal_sum] at him
  have hterm (b : ℕ) (n : ℤ) :
      (ZMod.stdAddChar ((n : ZMod q) * (b : ZMod q))).im = Real.sin (2 * π * b * n / q) := by
    rw [TauCeti.stdAddChar_intCast_mul_natCast, TauCeti.im_expTwoPiI]
    congr 1
    ring
  have hsum : (∑ b : ZMod q, χ⁻¹ b *
        ∑ n ∈ Ioc M (M + N), ((ZMod.stdAddChar ((n : ZMod q) * b)).im : ℂ)) =
      ∑ b ∈ Ico 1 q, χ⁻¹ b * ∑ n ∈ Ioc M (M + N), (Real.sin (2 * π * b * n / q) : ℂ) := by
    simpa only [ZMod.natCast_zmod_val, hterm] using
      ZMod.sum_val_eq_sum_Ico_one (n := q)
        (fun b ↦ χ⁻¹ (b : ZMod q) *
          ∑ n ∈ Ioc M (M + N), ((ZMod.stdAddChar ((n : ZMod q) * (b : ZMod q))).im : ℂ))
        (by simp [χ⁻¹.map_zero' (by omega)])
  rw [mul_assoc, eq_inv_mul_iff_mul_eq₀ htau, mul_comm, him, hsum]

end DirichletCharacter
