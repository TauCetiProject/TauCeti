/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import TauCeti.NumberTheory.DirichletCharacter.PolyaVinogradov
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.ClassOfOne

/-!
# Mean squares of Jacobi-symbol series averaged over numerators

When averaging `|∑ n, a n * J(-v | n°)|²` over the numerator `-v`, with `n°` the odd part
of `n`, the pair `m, n` contributes a character sum of modulus `(m * n)°`. The pairs for
which this modulus is square are bounded trivially; the others admit Pólya–Vinogradov
cancellation. This separation allows the same mean-square estimate to be used for finite sums
and for absolutely summable weights such as Gaussian weights in theta series.

The application to quadratic twists follows the moment calculation in
`grh/src/Lib/Analytic/QuadraticTwist.lean` of
[grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207),
notably `New.dirichletCharacter_jacobiSym_ne_one`, `New.norm_sum_jacobiSym_le`, and
`New.sum_sq_thetaSeries_jacobiSym_le`.
-/

public section

open Finset Nat
open scoped ComplexConjugate

namespace TauCeti

/-- The sum of `J(-v | b)` for `1 ≤ v ≤ X` is bounded in norm by `X`, and for odd nonsquare
`b` also by the Pólya–Vinogradov bound. The minimum gives one bound usable for all odd `b`. -/
theorem norm_sum_jacobiSym_neg_Icc_le {b : ℕ} (hb : Odd b) (X : ℕ) :
    ‖∑ v ∈ Icc 1 X, (jacobiSym (-(v : ℤ)) b : ℂ)‖ ≤
      if IsSquare b then (X : ℝ) else min X (2 * Real.sqrt b * (1 + Real.log b)) := by
  let : NeZero b := ⟨hb.pos.ne'⟩
  let χ := jacobiChar ℂ b
  have hcard : ‖∑ v ∈ Icc 1 X, (jacobiSym (-(v : ℤ)) b : ℂ)‖ ≤ X := by
    refine (norm_sum_le_of_le _ (n := fun _ ↦ (1 : ℝ)) fun v _ ↦ ?_).trans_eq (by simp)
    rw [← jacobiChar_intCast]
    exact χ.norm_le_one _
  split_ifs with hsq
  · exact hcard
  refine le_min hcard ?_
  have hχ : χ ≠ 1 := by
    obtain ⟨s, a, hs, ha, rfl, hsf⟩ := Nat.sq_mul_squarefree_of_pos hb.pos
    let : NeZero s := ⟨hs.ne'⟩
    let : NeZero a := ⟨ha.ne'⟩
    have hs₁ : 1 < s := by
      by_contra! h
      have heq : s = 1 := by omega
      exact hsq ⟨a, by simp [heq, sq]⟩
    have hlift : χ = (jacobiChar ℂ s).changeLevel (dvd_mul_left s (a ^ 2)) := by
      refine MulChar.ext fun u ↦ ?_
      have hcop := (ZMod.val_coe_unit_coprime u).coprime_dvd_right
        ((dvd_pow_self a two_ne_zero).trans (dvd_mul_right (a ^ 2) s))
      have hsqUnit : jacobiSym (u : ZMod (a ^ 2 * s)).val a ^ 2 = 1 :=
        jacobiSym.sq_one (by rwa [Int.gcd_natCast_natCast])
      dsimp only [χ]
      simp only [jacobiChar_apply, changeLevel_jacobiChar_apply_units, jacobiSym.mul_right,
        jacobiSym.pow_right, hsqUnit, one_mul]
    rw [ne_eq, hlift, DirichletCharacter.changeLevel_eq_one_iff]
    obtain ⟨v, _, hv, hval⟩ := exists_modEq_one_jacobiSym_eq_neg_one_of_squarefree
      (Nat.odd_mul.mp hb).2 hs₁ hsf (Nat.coprime_one_right s)
    have hv' := (ZMod.isUnit_iff_coprime v s).2 (by simpa using hv)
    intro h
    have heq : (-1 : ℂ) = 1 := by
      simpa [jacobiChar_natCast, hval, MulChar.one_apply hv'] using
        DFunLike.congr_fun h (v : ZMod s)
    exact (by norm_num : (-1 : ℂ) ≠ 1) heq
  have hval (v : ℕ) : (jacobiSym (-(v : ℤ)) b : ℂ) = χ (-1) * χ v := by
    simp only [χ, ← jacobiChar_intCast (R := ℂ), Int.cast_neg, Int.cast_natCast]
    rw [← map_mul, neg_one_mul]
  simp_rw [hval, ← mul_sum, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans
    (χ.norm_sum_Icc_le_of_ne_one hχ X)

/-- Pair correlation of Jacobi symbols with denominators the odd parts of `m` and `n`. The
square case is bounded by the length of the interval; the nonsquare case has a bound independent
of that length. -/
theorem norm_sum_mul_jacobiSym_ordCompl_le (X : ℕ) (m n : ℕ+) :
    ‖∑ v ∈ Icc 1 X, (jacobiSym (-(v : ℤ)) (ordCompl[2] (m : ℕ)) : ℂ) *
      (jacobiSym (-(v : ℤ)) (ordCompl[2] (n : ℕ)) : ℂ)‖ ≤
      if IsSquare (ordCompl[2] ((m : ℕ) * n)) then (X : ℝ)
      else min (X : ℝ) (2 * Real.sqrt (ordCompl[2] ((m : ℕ) * n) : ℕ) *
        (1 + Real.log (ordCompl[2] ((m : ℕ) * n) : ℕ))) := by
  have hmul (v : ℕ) : (jacobiSym (-(v : ℤ)) (ordCompl[2] (m : ℕ)) : ℂ) *
      (jacobiSym (-(v : ℤ)) (ordCompl[2] (n : ℕ)) : ℂ) =
      jacobiSym (-(v : ℤ)) (ordCompl[2] ((m : ℕ) * n)) := by
    rw [Nat.ordCompl_mul, jacobiSym.mul_right' _ (Nat.ordCompl_pos 2 m.ne_zero).ne'
      (Nat.ordCompl_pos 2 n.ne_zero).ne', Int.cast_mul]
  simp_rw [hmul]
  exact norm_sum_jacobiSym_neg_Icc_le (Nat.coprime_two_left.mp (Nat.coprime_ordCompl
    Nat.prime_two (mul_ne_zero m.ne_zero n.ne_zero))) X

/-- The mean square of a Jacobi-symbol series with absolutely summable complex coefficients.
Pairs with square odd part of `m * n` are kept separate from pairs with cancellation. The bound
by the interval length in both cases keeps the series on the right absolutely convergent. -/
theorem sum_norm_tsum_mul_jacobiSym_sq_le (X : ℕ) {a : ℕ+ → ℂ}
    (ha : Summable fun n ↦ ‖a n‖) :
    ∑ v ∈ Icc 1 X, ‖∑' n : ℕ+, a n * (jacobiSym (-(v : ℤ)) (ordCompl[2] (n : ℕ)) : ℂ)‖ ^ 2 ≤
      ∑' p : ℕ+ × ℕ+, ‖a p.1‖ * ‖a p.2‖ *
        (let b := ordCompl[2] ((p.1 : ℕ) * p.2)
         if IsSquare b then (X : ℝ) else min X (2 * Real.sqrt b * (1 + Real.log b))) := by
  let J (v : ℕ) (n : ℕ+) : ℂ := jacobiSym (-(v : ℤ)) (ordCompl[2] (n : ℕ))
  let A (v : ℕ) (n : ℕ+) := a n * J v n
  let W (p : ℕ+ × ℕ+) : ℝ :=
    let b := ordCompl[2] ((p.1 : ℕ) * p.2)
    if IsSquare b then X else min X (2 * Real.sqrt b * (1 + Real.log b))
  have hJ (v : ℕ) (n : ℕ+) : ‖J v n‖ ≤ 1 := by
    let : NeZero (ordCompl[2] (n : ℕ)) := ⟨(Nat.ordCompl_pos 2 n.ne_zero).ne'⟩
    simpa only [J, jacobiChar_intCast] using
      (jacobiChar ℂ (ordCompl[2] (n : ℕ))).norm_le_one (Int.cast (-(v : ℤ)))
  have hA (v : ℕ) : Summable fun n ↦ ‖A v n‖ := ha.of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) (fun n ↦ by
      dsimp only [A]
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hJ v n))
  have hW (p) : ‖∑ v ∈ Icc 1 X, J v p.1 * J v p.2‖ ≤ W p :=
    norm_sum_mul_jacobiSym_ordCompl_le X p.1 p.2
  have hMajor : Summable fun p ↦ ‖a p.1‖ * ‖a p.2‖ * W p :=
    ((ha.mul_of_nonneg ha (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)).mul_right
      (X : ℝ)).of_nonneg_of_le
      (fun p ↦ mul_nonneg (by positivity) ((norm_nonneg _).trans (hW p))) (fun p ↦ by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simp only [W]
        split_ifs <;> simp)
  have hExpand : HasSum
      (fun p : ℕ+ × ℕ+ ↦ ∑ v ∈ Icc 1 X, A v p.1 * conj (A v p.2))
      (∑ v ∈ Icc 1 X, ((‖∑' n, A v n‖ ^ 2 : ℝ) : ℂ)) := by
    apply hasSum_sum
    intro v _
    have h := (hA v).of_norm.hasSum
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    have hc : Summable (fun n ↦ ‖conj (A v n)‖) := by simpa only [Complex.norm_conj] using hA v
    exact h.mul ((RCLike.hasSum_conj' ℂ).mpr h) (summable_mul_of_summable_norm (hA v) hc)
  have hBound (p : ℕ+ × ℕ+) :
      ‖∑ v ∈ Icc 1 X, A v p.1 * conj (A v p.2)‖ ≤ ‖a p.1‖ * ‖a p.2‖ * W p := by
    have h (v : ℕ) : A v p.1 * conj (A v p.2) =
        (a p.1 * conj (a p.2)) * (J v p.1 * J v p.2) := by
      simp only [A, map_mul, J, map_intCast]
      ring
    simp_rw [h, ← mul_sum, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (hW p) (by positivity)
  have hnonneg : 0 ≤ ∑ v ∈ Icc 1 X, ‖∑' n, A v n‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have h := hExpand.norm_le_of_bounded hMajor.hasSum hBound
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg] at h
  exact h

end TauCeti
