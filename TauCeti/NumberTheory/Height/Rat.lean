/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.MvPolynomial
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Polynomial.Content

/-!
# Heights of integer tuples and integer polynomials over `ℚ`

Mathlib's `Rat.mulHeight_eq_max_abs_of_gcd_eq_one` computes the height over `ℚ` of a tuple of
coprime integers as the largest absolute value of its entries. Every finite place contributes
at most `1` to the height of an integer tuple, so for an arbitrary nonzero integer tuple the
largest absolute value is still an upper bound for the height:

`H(x) ≤ maxᵢ |xᵢ|`, with equality if `gcd(x) = 1`.

The same holds for finitely supported integer vectors, and hence for the coefficient heights of
integer polynomials viewed over `ℚ`: for every `P ∈ ℤ[X₁, …, Xₙ]`,
`h(P) ≤ log maxμ |Pμ|`, with equality if the coefficients of `P` are coprime.

This is how an integer auxiliary polynomial with coefficients bounded by `B`, such as the one of
`TauCeti.exists_roth_auxiliary_polynomial`, gets the height bound `h(P) ≤ log B` required by
height estimates such as Roth's lemma.

## Main results

* `Rat.mulHeight_le_max_abs`: `H(x) ≤ maxᵢ |xᵢ|` for a nonzero integer tuple `x`.
* `Rat.den_le_mulHeight₁`, `Rat.log_den_le_logHeight₁`: the denominator of a rational number is
  at most its height.
* `Rat.mulHeight₁_le_max_one_abs_mul_den`: conversely, `H(q) ≤ max(1, |q|) den(q)`.
* `Rat.mulHeight₁_intCast_div_le`: `H(x / y) ≤ max(|x|, |y|)` for integers `x` and `y ≠ 0`.
* `padicValNat.mul_log_le_log`, `Rat.abs_padicValRat_mul_log_le_logHeight₁`: the `p`-adic
  valuation is bounded by the height, `v_p(n) log p ≤ log n` and `|v_p(q)| log p ≤ h(q)`.
* `Rat.abs_padicValRat_le_logHeight₁_div_log_two`: `|v_p(q)| ≤ h(q) / log 2` for `2 ≤ p`.
* `Finsupp.mulHeight_mapRange_intCast_le`, `Finsupp.mulHeight_mapRange_intCast_eq`: the bound,
  and the equality for coprime entries, for finitely supported integer vectors.
* `Finsupp.mulHeight_mapRange_intCast_le_of_abs_le`: `H(x) ≤ B` if all entries of the nonzero
  integer vector `x` are bounded by `B` in absolute value.
* `MvPolynomial.logHeight_map_intCast_le`, `MvPolynomial.logHeight_map_intCast_eq`: for an
  integer polynomial, `h(P) ≤ log maxμ |Pμ|`, with equality for coprime coefficients.
* `MvPolynomial.logHeight_map_intCast_le_log`: `h(P) ≤ log B` if all coefficients of the nonzero
  integer polynomial `P` are bounded by `B` in absolute value.
* `Polynomial.logHeight_map_intCast_le`, `Polynomial.logHeight_map_intCast_eq`,
  `Polynomial.logHeight_map_intCast_le_log`: the same for univariate polynomials, where coprime
  coefficients means that `P` is primitive.

## References

* L. Pottmeyer, [*Diophantine Approximation*](https://esaga.uni-due.de/f/lukas.pottmeyer/DioApp.pdf)
  (2022), §3.5.2.
* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 5, Theorem 5.6.
-/

public section

open Height

namespace Rat

variable {ι : Type*} [Finite ι]

/-- The height of a nonzero tuple of integers, viewed as rational numbers, is at most the largest
absolute value of its entries. Equality holds for coprime entries, by
`Rat.mulHeight_eq_max_abs_of_gcd_eq_one`. -/
theorem mulHeight_le_max_abs {x : ι → ℤ} (hx : x ≠ 0) :
    mulHeight (((↑) : ℤ → ℚ) ∘ x) ≤ ⨆ i, |x i| := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  have : Nonempty ι := ⟨i₀⟩
  -- Write `x = g • y` with `g = gcd(x) ≠ 0` and `gcd(y) = 1`.
  obtain ⟨y, hxy, hy⟩ := Finset.univ.extract_gcd x Finset.univ_nonempty
  have hg : Finset.univ.gcd x ≠ 0 := fun h ↦
    hi₀ (Finset.gcd_eq_zero_iff.mp h i₀ (Finset.mem_univ _))
  have hcast : ((↑) : ℤ → ℚ) ∘ x = ((Finset.univ.gcd x : ℤ) : ℚ) • (((↑) : ℤ → ℚ) ∘ y) := by
    ext i
    simp [hxy i (Finset.mem_univ i)]
  rw [hcast, mulHeight_smul_eq_mulHeight _ (Int.cast_ne_zero.mpr hg),
    mulHeight_eq_max_abs_of_gcd_eq_one hy]
  -- `|x i| = |gcd(x)| |y i| ≥ |y i|`, since `gcd(x) ≠ 0`.
  refine Int.cast_le.mpr (ciSup_mono (Finite.bddAbove_range _) fun i ↦ ?_)
  rw [hxy i (Finset.mem_univ i), abs_mul]
  exact le_mul_of_one_le_left (abs_nonneg _) (Int.one_le_abs hg)

/-- The logarithmic height of a tuple of integers, viewed as rational numbers, is at most the
logarithm of the largest absolute value of its entries. -/
theorem logHeight_le_max_abs (x : ι → ℤ) :
    logHeight (((↑) : ℤ → ℚ) ∘ x) ≤ Real.log ↑(⨆ i, |x i|) := by
  rcases eq_or_ne x 0 with rfl | hx
  · cases isEmpty_or_nonempty ι <;> simp [iSup_of_empty', Int.csSup_empty]
  rw [logHeight_eq_log_mulHeight]
  exact Real.log_le_log (mulHeight_pos _) (mulHeight_le_max_abs hx)

/-- The denominator of a rational number is at most its multiplicative height. -/
theorem den_le_mulHeight₁ (q : ℚ) : (q.den : ℝ) ≤ mulHeight₁ q := by
  rw [mulHeight₁_eq_max]
  exact_mod_cast le_max_right _ _

/-- The multiplicative height of a rational number `q` is at most `max 1 |q|` times its
denominator. -/
theorem mulHeight₁_le_max_one_abs_mul_den (q : ℚ) :
    mulHeight₁ q ≤ max 1 |(q : ℝ)| * q.den := by
  have hnum : (q.num : ℝ) = q * q.den := by
    rw [Rat.cast_def]
    field_simp
  rw [mulHeight₁_eq_max]
  push_cast
  refine max_le ?_ (le_mul_of_one_le_left (by positivity) (le_max_left _ _))
  rw [Nat.cast_natAbs, Int.cast_abs, hnum, abs_mul, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- The multiplicative height of a quotient `x / y` of integers with `y ≠ 0` is at most
`max(|x|, |y|)`. -/
theorem mulHeight₁_intCast_div_le (x : ℤ) {y : ℤ} (hy : y ≠ 0) :
    mulHeight₁ ((x : ℚ) / y) ≤ max |(x : ℝ)| |(y : ℝ)| := by
  have hv : ![(x : ℚ), y] = ((↑) : ℤ → ℚ) ∘ ![x, y] := by
    ext i
    fin_cases i <;> simp
  rw [mulHeight₁_div_eq_mulHeight, hv]
  refine (mulHeight_le_max_abs (by simp [hy])).trans ?_
  rw [← Int.cast_abs, ← Int.cast_abs, ← Int.cast_max, Int.cast_le]
  exact ciSup_le fun i ↦ by fin_cases i <;> simp

/-- The logarithm of the denominator of a rational number is at most its logarithmic height. -/
theorem log_den_le_logHeight₁ (q : ℚ) : Real.log q.den ≤ logHeight₁ q := by
  rw [logHeight₁_eq_log_mulHeight₁]
  exact Real.log_le_log (by positivity) (den_le_mulHeight₁ q)

end Rat

namespace padicValNat

/-- The `p`-adic valuation of a natural number `n` satisfies `v_p(n) log p ≤ log n`. -/
theorem mul_log_le_log (p n : ℕ) :
    (padicValNat p n : ℝ) * Real.log p ≤ Real.log n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  -- `p ^ v_p(n)` divides `n ≠ 0`, so it is a positive integer at most `n`.
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  have hpos : 0 < p ^ padicValNat p n := Nat.pos_of_dvd_of_pos pow_padicValNat_dvd hn'
  rw [← Real.log_pow]
  exact Real.log_le_log (by exact_mod_cast hpos)
    (by exact_mod_cast Nat.le_of_dvd hn' pow_padicValNat_dvd)

end padicValNat

namespace Rat

/-- The `p`-adic valuation of a rational number `q` satisfies `|v_p(q)| log p ≤ h(q)`, where
`h` is the logarithmic height. -/
theorem abs_padicValRat_mul_log_le_logHeight₁ (p : ℕ) (q : ℚ) :
    |(padicValRat p q : ℝ)| * Real.log p ≤ logHeight₁ q := by
  have hp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hnum : (padicValNat p q.num.natAbs : ℝ) * Real.log p ≤ logHeight₁ q := by
    rcases eq_or_ne q.num.natAbs 0 with h | h
    · simpa [h] using zero_le_logHeight₁ q
    refine (padicValNat.mul_log_le_log p _).trans ?_
    rw [logHeight₁_eq_log_mulHeight₁, mulHeight₁_eq_max]
    exact Real.log_le_log (Nat.cast_pos.2 (Nat.pos_of_ne_zero h))
      (by exact_mod_cast le_max_left _ _)
  have hden := (padicValNat.mul_log_le_log p q.den).trans (log_den_le_logHeight₁ q)
  -- `v_p(q) = v_p(num q) - v_p(den q)` is a difference of two naturals.
  have habs : |(padicValRat p q : ℝ)| ≤
      max (padicValNat p q.num.natAbs : ℝ) (padicValNat p q.den) := by
    have h1 := le_max_left (padicValNat p q.num.natAbs : ℝ) (padicValNat p q.den)
    have h2 := le_max_right (padicValNat p q.num.natAbs : ℝ) (padicValNat p q.den)
    rw [padicValRat_def, padicValInt, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, abs_le]
    constructor <;> linarith [(padicValNat p q.num.natAbs).cast_nonneg (α := ℝ),
      (padicValNat p q.den).cast_nonneg (α := ℝ)]
  calc |(padicValRat p q : ℝ)| * Real.log p
      ≤ max (padicValNat p q.num.natAbs : ℝ) (padicValNat p q.den) * Real.log p :=
        mul_le_mul_of_nonneg_right habs hp
    _ = max ((padicValNat p q.num.natAbs : ℝ) * Real.log p)
          ((padicValNat p q.den : ℝ) * Real.log p) := max_mul_of_nonneg _ _ hp
    _ ≤ logHeight₁ q := max_le hnum hden

/-- For `2 ≤ p`, the `p`-adic valuation of a rational number `q` satisfies
`|v_p(q)| ≤ h(q) / log 2`, where `h` is the logarithmic height. -/
theorem abs_padicValRat_le_logHeight₁_div_log_two {p : ℕ} (hp : 2 ≤ p) (q : ℚ) :
    |(padicValRat p q : ℝ)| ≤ logHeight₁ q / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [le_div_iff₀ hlog2]
  refine le_trans ?_ (abs_padicValRat_mul_log_le_logHeight₁ p q)
  gcongr
  exact_mod_cast hp

end Rat

namespace Finsupp

variable {α : Type*}

/-- The height over `ℚ` of an integer vector is the height of its restriction to its support. -/
private theorem mulHeight_mapRange_intCast_eq_support (x : α →₀ ℤ) :
    (x.mapRange ((↑) : ℤ → ℚ) Int.cast_zero).mulHeight =
      Height.mulHeight (((↑) : ℤ → ℚ) ∘ fun a : x.support ↦ x a) := by
  rw [mulHeight_eq_of_support_subset _ x.support support_mapRange]
  exact congrArg Height.mulHeight (funext fun a ↦ mapRange_apply ..)

/-- The height over `ℚ` of a nonzero finitely supported integer vector is at most the largest
absolute value of its entries. -/
theorem mulHeight_mapRange_intCast_le {x : α →₀ ℤ} (hx : x ≠ 0) :
    (x.mapRange ((↑) : ℤ → ℚ) Int.cast_zero).mulHeight ≤ x.support.sup fun a ↦ (x a).natAbs := by
  obtain ⟨a₀, ha₀⟩ := support_nonempty_iff.mpr hx
  have : Nonempty x.support := ⟨⟨a₀, ha₀⟩⟩
  have hx' : (fun a : x.support ↦ x a) ≠ 0 := fun h ↦ mem_support_iff.mp ha₀ (congrFun h ⟨a₀, ha₀⟩)
  rw [mulHeight_mapRange_intCast_eq_support]
  refine (Rat.mulHeight_le_max_abs hx').trans ?_
  rw [← Int.cast_natCast, Int.cast_le]
  refine ciSup_le fun a ↦ ?_
  rw [← Int.natCast_natAbs, Int.ofNat_le]
  exact Finset.le_sup (f := fun a ↦ (x a).natAbs) a.prop

/-- If the entries of a nonzero finitely supported integer vector are bounded by `B` in absolute
value, then its height over `ℚ` is at most `B`. -/
theorem mulHeight_mapRange_intCast_le_of_abs_le {x : α →₀ ℤ} (hx : x ≠ 0) {B : ℝ}
    (hB : ∀ a, |(x a : ℝ)| ≤ B) : (x.mapRange ((↑) : ℤ → ℚ) Int.cast_zero).mulHeight ≤ B := by
  obtain ⟨a, -, hsup⟩ :=
    Finset.exists_mem_eq_sup _ (support_nonempty_iff.mpr hx) fun a ↦ (x a).natAbs
  refine (mulHeight_mapRange_intCast_le hx).trans ?_
  rw [hsup, Nat.cast_natAbs, Int.cast_abs]
  exact hB a

/-- The height over `ℚ` of a finitely supported integer vector with coprime entries is the largest
absolute value of its entries. -/
theorem mulHeight_mapRange_intCast_eq {x : α →₀ ℤ} (hx : x.support.gcd x = 1) :
    (x.mapRange ((↑) : ℤ → ℚ) Int.cast_zero).mulHeight = x.support.sup fun a ↦ (x a).natAbs := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨a, ha, hsup⟩ :=
    Finset.exists_mem_eq_sup _ (support_nonempty_iff.mpr hx0) fun a ↦ (x a).natAbs
  have : Nonempty x.support := ⟨⟨a, ha⟩⟩
  have hgcd : (Finset.univ : Finset x.support).gcd (fun a ↦ x a) = 1 := by
    classical
    rwa [Finset.univ_eq_attach, ← Function.comp_def x Subtype.val, ← Finset.gcd_image,
      Finset.attach_image_val]
  refine (mulHeight_mapRange_intCast_le hx0).antisymm ?_
  rw [mulHeight_mapRange_intCast_eq_support, Rat.mulHeight_eq_max_abs_of_gcd_eq_one hgcd, hsup,
    ← Int.cast_natCast, Int.cast_le, Int.natCast_natAbs]
  exact le_ciSup (f := fun b : x.support ↦ |x b|) (Finite.bddAbove_range _) ⟨a, ha⟩

end Finsupp

namespace MvPolynomial

variable {σ : Type*} {P : MvPolynomial σ ℤ}

private theorem mulHeight_map_intCast_eq_finsupp (P : MvPolynomial σ ℤ) :
    (P.map (Int.castRingHom ℚ)).mulHeight =
      ((AddMonoidAlgebra.coeff P).mapRange ((↑) : ℤ → ℚ) Int.cast_zero).mulHeight := by
  rw [mulHeight_eq_finsupp]
  refine congrArg Finsupp.mulHeight (Finsupp.ext fun m ↦ ?_)
  simp [coeff_map]

/-- The height over `ℚ` of a nonzero integer polynomial is at most the largest absolute value of
its coefficients. -/
theorem mulHeight_map_intCast_le (hP : P ≠ 0) :
    (P.map (Int.castRingHom ℚ)).mulHeight ≤ P.support.sup fun m ↦ (P.coeff m).natAbs := by
  rw [mulHeight_map_intCast_eq_finsupp]
  exact Finsupp.mulHeight_mapRange_intCast_le (by simpa using hP)

/-- The height over `ℚ` of an integer polynomial with coprime coefficients is the largest absolute
value of its coefficients. -/
theorem mulHeight_map_intCast_eq (hP : P.support.gcd P.coeff = 1) :
    (P.map (Int.castRingHom ℚ)).mulHeight = P.support.sup fun m ↦ (P.coeff m).natAbs := by
  rw [mulHeight_map_intCast_eq_finsupp]
  exact Finsupp.mulHeight_mapRange_intCast_eq hP

/-- **Pottmeyer, §3.5.2.** The logarithmic height over `ℚ` of an integer polynomial is at most
the logarithm of the largest absolute value of its coefficients. -/
theorem logHeight_map_intCast_le (P : MvPolynomial σ ℤ) :
    (P.map (Int.castRingHom ℚ)).logHeight ≤
      Real.log ((P.support.sup fun m ↦ (P.coeff m).natAbs : ℕ) : ℝ) := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  rw [logHeight_eq_log_mulHeight]
  exact Real.log_le_log (mulHeight_pos _) (mulHeight_map_intCast_le hP)

/-- The logarithmic height over `ℚ` of an integer polynomial with coprime coefficients is the
logarithm of the largest absolute value of its coefficients. -/
theorem logHeight_map_intCast_eq (hP : P.support.gcd P.coeff = 1) :
    (P.map (Int.castRingHom ℚ)).logHeight =
      Real.log ((P.support.sup fun m ↦ (P.coeff m).natAbs : ℕ) : ℝ) := by
  rw [logHeight_eq_log_mulHeight, mulHeight_map_intCast_eq hP]

/-- If the coefficients of a nonzero integer polynomial `P` are bounded by `B` in absolute value,
then the logarithmic height of `P` over `ℚ` is at most `log B`. -/
theorem logHeight_map_intCast_le_log (hP : P ≠ 0) {B : ℝ}
    (hB : ∀ m, |(P.coeff m : ℝ)| ≤ B) :
    (P.map (Int.castRingHom ℚ)).logHeight ≤ Real.log B := by
  rw [logHeight_eq_log_mulHeight]
  refine Real.log_le_log (mulHeight_pos _) ?_
  rw [mulHeight_map_intCast_eq_finsupp]
  exact Finsupp.mulHeight_mapRange_intCast_le_of_abs_le (by simpa using hP) hB

end MvPolynomial

namespace Polynomial

variable {P : ℤ[X]}

private theorem mulHeight_map_intCast_eq_finsupp (P : ℤ[X]) :
    (P.map (Int.castRingHom ℚ)).mulHeight =
      (P.toFinsupp.coeff.mapRange ((↑) : ℤ → ℚ) Int.cast_zero).mulHeight := by
  rw [mulHeight_eq_finsupp]
  refine congrArg Finsupp.mulHeight (Finsupp.ext fun n ↦ ?_)
  simp [toFinsupp_apply, coeff_map]

/-- The height over `ℚ` of a nonzero integer polynomial is at most the largest absolute value of
its coefficients. -/
theorem mulHeight_map_intCast_le (hP : P ≠ 0) :
    (P.map (Int.castRingHom ℚ)).mulHeight ≤ P.support.sup fun n ↦ (P.coeff n).natAbs := by
  rw [mulHeight_map_intCast_eq_finsupp]
  exact Finsupp.mulHeight_mapRange_intCast_le (by simpa using hP)

/-- The height over `ℚ` of a primitive integer polynomial is the largest absolute value of its
coefficients. -/
theorem mulHeight_map_intCast_eq (hP : P.IsPrimitive) :
    (P.map (Int.castRingHom ℚ)).mulHeight = P.support.sup fun n ↦ (P.coeff n).natAbs := by
  rw [mulHeight_map_intCast_eq_finsupp]
  exact Finsupp.mulHeight_mapRange_intCast_eq (isPrimitive_iff_content_eq_one.mp hP)

/-- The logarithmic height over `ℚ` of an integer polynomial is at most the logarithm of the
largest absolute value of its coefficients. -/
theorem logHeight_map_intCast_le (P : ℤ[X]) :
    (P.map (Int.castRingHom ℚ)).logHeight ≤
      Real.log ((P.support.sup fun n ↦ (P.coeff n).natAbs : ℕ) : ℝ) := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  rw [logHeight_eq_log_mulHeight]
  exact Real.log_le_log (mulHeight_pos _) (mulHeight_map_intCast_le hP)

/-- The logarithmic height over `ℚ` of a primitive integer polynomial is the logarithm of the
largest absolute value of its coefficients. -/
theorem logHeight_map_intCast_eq (hP : P.IsPrimitive) :
    (P.map (Int.castRingHom ℚ)).logHeight =
      Real.log ((P.support.sup fun n ↦ (P.coeff n).natAbs : ℕ) : ℝ) := by
  rw [logHeight_eq_log_mulHeight, mulHeight_map_intCast_eq hP]

/-- If the coefficients of a nonzero integer polynomial `P` are bounded by `B` in absolute value,
then the logarithmic height of `P` over `ℚ` is at most `log B`. -/
theorem logHeight_map_intCast_le_log (hP : P ≠ 0) {B : ℝ}
    (hB : ∀ n, |(P.coeff n : ℝ)| ≤ B) :
    (P.map (Int.castRingHom ℚ)).logHeight ≤ Real.log B := by
  rw [logHeight_eq_log_mulHeight]
  refine Real.log_le_log (mulHeight_pos _) ?_
  rw [mulHeight_map_intCast_eq_finsupp]
  exact Finsupp.mulHeight_mapRange_intCast_le_of_abs_le (by simpa using hP)
    fun n ↦ by simpa [toFinsupp_apply] using hB n

end Polynomial
