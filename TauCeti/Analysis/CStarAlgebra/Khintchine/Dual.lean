/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.Normed.Module.RademacherSum.Basic

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Column and row square functions and dual Rademacher factorization in C⋆-algebras

For a finite family `a : ι → A` in a non-unital C⋆-algebra `A` equipped with its canonical
`StarOrderedRing` order, the column and row square functions are
$$\mathrm{columnSquare}(a) = \Bigl(\sum_k a_k^* a_k\Bigr)^{1/2}, \qquad
  \mathrm{rowSquare}(a) = \Bigl(\sum_k a_k a_k^*\Bigr)^{1/2}.$$

This file develops the C⋆-algebraic calculus of `columnSquare` and `rowSquare` together with the
dual `L^∞` Rademacher factorization theorem underlying the `p = 1` noncommutative Khintchine
inequality with the sharp Haagerup–Pisier constant `√3`:

1. **Sign-cube Bessel inequalities**: for any `Φ : (ι → ℤˣ) → A`, the Rademacher Fourier
   coefficients `y_k = 𝔼_ε ε_k Φ(ε)` satisfy `∑_k y_k* y_k ≤ 𝔼_ε Φ(ε)* Φ(ε)` and
   `∑_k y_k y_k* ≤ 𝔼_ε Φ(ε) Φ(ε)*`, hence
   `max ‖columnSquare y‖ ‖rowSquare y‖ ≤ sup_ε ‖Φ(ε)‖`.
2. **Pisier–Haagerup fourth-moment inequality**: for self-adjoint `x : ι → A`, expanding
   `𝔼_ε (∑_i ε_i x_i)^4` into its three surviving index pairings and bounding the alternating
   pairing `∑_{i,j} x_i x_j x_i x_j` via the Hilbert C⋆-module Cauchy–Schwarz inequality yields
   `‖𝔼_ε (∑_i ε_i x_i)^4‖ ≤ 3 ‖∑_i x_i^2‖^2`.
3. **Iterative functional-calculus truncation and `2 × 2` Hermitian dilation**: truncating each
   signed sum `∑_i ε_i x_i` at threshold `√3 / 2` contracts `‖∑_i r_i^2‖` by `1 / 4` at each step,
   giving a geometric series in `(ι → ℤˣ) → A` for self-adjoint families, and passing to the
   off-diagonal `2 × 2` block matrices over `A` yields for arbitrary `x : ι → A` a bounded family
   `Φ : (ι → ℤˣ) → A` with `𝔼_ε ε_i • Φ(ε) = x_i` and
   `‖Φ(ε)‖ ≤ √3 * max ‖columnSquare x‖ ‖rowSquare x‖`.

## Main declarations

* `TauCeti.columnSquare`, `TauCeti.rowSquare`: column and row square functions in a non-unital
  C⋆-algebra.
* `TauCeti.sum_star_expect_units_smul_mul_le`, `TauCeti.sum_expect_units_smul_mul_star_le`:
  operator-valued Bessel inequalities for Rademacher Fourier coefficients.
* `TauCeti.norm_expect_sum_units_smul_pow_four_le`: the Pisier–Haagerup fourth-moment inequality
  `‖𝔼_ε (∑_i ε_i • x_i)^4‖ ≤ 3 * ‖∑_i x_i^2‖^2` for self-adjoint `x : ι → A`.
* `TauCeti.exists_isSelfAdjoint_expect_units_smul_eq_and_norm_le`: dual Rademacher factorization
  with constant `√3` for self-adjoint families.
* `TauCeti.exists_expect_units_smul_eq_and_norm_le`: dual Rademacher factorization with constant
  `√3` for arbitrary finite families in a non-unital C⋆-algebra.

## References

* F. Lust-Piquard and G. Pisier, *Non commutative Khintchine and Paley inequalities*,
  Ark. Mat. 29 (1991), 241–260.
* U. Haagerup and M. Musat, *On the best constants in noncommutative Khintchine-type
  inequalities*, J. Funct. Anal. 250 (2007), 588–624, Theorem 2.11.
* G. Pisier, *Grothendieck's theorem, past and present*, Bull. Amer. Math. Soc. 49 (2012),
  Theorem 9.1.
-/

@[expose] public section

noncomputable section

open Filter Topology
open scoped BigOperators ComplexStarModule CStarModule NNReal WithCStarModule

namespace TauCeti

section SquareFunctions

variable {ι A : Type*} [Fintype ι] [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The column square function `(∑ k, star (a k) * a k)^(1/2)` of a finite family in a non-unital
C⋆-algebra. -/
def columnSquare (a : ι → A) : A :=
  CFC.sqrt (∑ k, star (a k) * a k)

/-- Unfolding definition of `columnSquare`. -/
theorem columnSquare_def (a : ι → A) :
    columnSquare a = CFC.sqrt (∑ k, star (a k) * a k) :=
  (rfl)

/-- The row square function `(∑ k, a k * star (a k))^(1/2)` of a finite family in a non-unital
C⋆-algebra. -/
def rowSquare (a : ι → A) : A :=
  CFC.sqrt (∑ k, a k * star (a k))

/-- Unfolding definition of `rowSquare`. -/
theorem rowSquare_def (a : ι → A) :
    rowSquare a = CFC.sqrt (∑ k, a k * star (a k)) :=
  (rfl)

/-- `columnSquare a` is nonnegative in the C⋆-algebra order. -/
theorem columnSquare_nonneg (a : ι → A) : 0 ≤ columnSquare a :=
  CFC.sqrt_nonneg _

/-- `rowSquare a` is nonnegative in the C⋆-algebra order. -/
theorem rowSquare_nonneg (a : ι → A) : 0 ≤ rowSquare a :=
  CFC.sqrt_nonneg _

/-- `columnSquare a` is self-adjoint. -/
theorem isSelfAdjoint_columnSquare (a : ι → A) : IsSelfAdjoint (columnSquare a) :=
  (columnSquare_nonneg a).isSelfAdjoint

/-- `rowSquare a` is self-adjoint. -/
theorem isSelfAdjoint_rowSquare (a : ι → A) : IsSelfAdjoint (rowSquare a) :=
  (rowSquare_nonneg a).isSelfAdjoint

/-- Squaring `columnSquare a` recovers `∑ k, star (a k) * a k`. -/
@[simp]
theorem columnSquare_mul_self (a : ι → A) :
    columnSquare a * columnSquare a = ∑ k, star (a k) * a k :=
  CFC.sqrt_mul_sqrt_self (∑ k, star (a k) * a k)
    (Finset.sum_nonneg fun k _ => star_mul_self_nonneg (a k))

/-- Squaring `rowSquare a` recovers `∑ k, a k * star (a k)`. -/
@[simp]
theorem rowSquare_mul_self (a : ι → A) :
    rowSquare a * rowSquare a = ∑ k, a k * star (a k) :=
  CFC.sqrt_mul_sqrt_self (∑ k, a k * star (a k))
    (Finset.sum_nonneg fun k _ => mul_star_self_nonneg (a k))

/-- The row square function of `a` is the column square function of `fun k => star (a k)`. -/
theorem rowSquare_eq_columnSquare_star (a : ι → A) :
    rowSquare a = columnSquare (fun k => star (a k)) := by
  simp [rowSquare, columnSquare]

/-- The column square function of `a` is the row square function of `fun k => star (a k)`. -/
theorem columnSquare_eq_rowSquare_star (a : ι → A) :
    columnSquare a = rowSquare (fun k => star (a k)) := by
  simp [rowSquare, columnSquare]

/-- At `0`, `columnSquare` vanishes. -/
@[simp]
theorem columnSquare_zero : columnSquare (0 : ι → A) = 0 := by
  simp [columnSquare]

/-- At `0`, `rowSquare` vanishes. -/
@[simp]
theorem rowSquare_zero : rowSquare (0 : ι → A) = 0 := by
  simp [rowSquare]

/-- The norm of `columnSquare a` is `√‖∑ k, star (a k) * a k‖`. -/
@[simp]
theorem norm_columnSquare (a : ι → A) :
    ‖columnSquare a‖ = √‖∑ k, star (a k) * a k‖ :=
  CFC.norm_sqrt (∑ k, star (a k) * a k)
    (Finset.sum_nonneg fun k _ => star_mul_self_nonneg (a k))

/-- The norm of `rowSquare a` is `√‖∑ k, a k * star (a k)‖`. -/
@[simp]
theorem norm_rowSquare (a : ι → A) :
    ‖rowSquare a‖ = √‖∑ k, a k * star (a k)‖ :=
  CFC.norm_sqrt (∑ k, a k * star (a k))
    (Finset.sum_nonneg fun k _ => mul_star_self_nonneg (a k))

/-- Squaring `‖columnSquare a‖` gives `‖∑ k, star (a k) * a k‖`. -/
theorem norm_columnSquare_sq (a : ι → A) :
    ‖columnSquare a‖ ^ 2 = ‖∑ k, star (a k) * a k‖ := by
  rw [norm_columnSquare, Real.sq_sqrt (norm_nonneg _)]

/-- Squaring `‖rowSquare a‖` gives `‖∑ k, a k * star (a k)‖`. -/
theorem norm_rowSquare_sq (a : ι → A) :
    ‖rowSquare a‖ ^ 2 = ‖∑ k, a k * star (a k)‖ := by
  rw [norm_rowSquare, Real.sq_sqrt (norm_nonneg _)]

/-- Each entry of `a` is bounded in norm by `‖columnSquare a‖`. -/
theorem norm_apply_le_norm_columnSquare (a : ι → A) (i : ι) :
    ‖a i‖ ≤ ‖columnSquare a‖ := by
  rw [norm_columnSquare, ← Real.sqrt_sq (norm_nonneg (a i))]
  refine Real.sqrt_le_sqrt ?_
  rw [sq, ← CStarRing.norm_star_mul_self]
  refine CStarAlgebra.norm_le_norm_of_le_of_nonneg ?_ (star_mul_self_nonneg (a i))
  exact Finset.single_le_sum (fun k _ => star_mul_self_nonneg (a k)) (Finset.mem_univ i)

/-- Each entry of `a` is bounded in norm by `‖rowSquare a‖`. -/
theorem norm_apply_le_norm_rowSquare (a : ι → A) (i : ι) :
    ‖a i‖ ≤ ‖rowSquare a‖ := by
  simpa only [rowSquare_eq_columnSquare_star, norm_star] using
    norm_apply_le_norm_columnSquare (fun k => star (a k)) i

end SquareFunctions

/-! ### Expectation helpers on the finite sign cube -/

section SignExpect

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem expect_eq_inv_card_smul_sum {κ M : Type*} [Fintype κ] [Nonempty κ]
    [AddCommMonoid M] [Module ℚ≥0 M] [Module ℝ M] (f : κ → M) :
    𝔼 x : κ, f x = (Fintype.card κ : ℝ)⁻¹ • ∑ x : κ, f x := by
  have hcard : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc 𝔼 x, f x
      = (Fintype.card κ : ℝ)⁻¹ • ((Fintype.card κ : ℝ) • 𝔼 x, f x) :=
        (inv_smul_smul₀ hcard _).symm
    _ = (Fintype.card κ : ℝ)⁻¹ • ∑ x, f x := by
        rw [Nat.cast_smul_eq_nsmul, Fintype.card_smul_expect]

private theorem units_smul_eq_real_smul {M : Type*} [AddCommGroup M] [Module ℝ M]
    (u : ℤˣ) (m : M) : u • m = ((u : ℤ) : ℝ) • m := by
  rw [Units.smul_def, Int.cast_smul_eq_zsmul ℝ]

private theorem star_units_smul {A : Type*} [AddCommGroup A] [StarAddMonoid A]
    (u : ℤˣ) (a : A) : star (u • a) = u • star a := by
  rw [Units.smul_def, Units.smul_def, star_zsmul]

private theorem isSelfAdjoint_units_smul {A : Type*} [AddCommGroup A] [StarAddMonoid A]
    {a : A} (ha : IsSelfAdjoint a) (u : ℤˣ) : IsSelfAdjoint (u • a) := by
  rw [IsSelfAdjoint, star_units_smul, ha.star_eq]

private theorem star_expect_units {A : Type*} [NonUnitalCStarAlgebra A] [Module ℚ≥0 A]
    (f : (ι → ℤˣ) → A) :
    star (𝔼 ε : ι → ℤˣ, f ε) = 𝔼 ε : ι → ℤˣ, star (f ε) := by
  rw [expect_eq_inv_card_smul_sum, expect_eq_inv_card_smul_sum, star_smul, star_trivial, star_sum]

private theorem isSelfAdjoint_expect_units {A : Type*} [NonUnitalCStarAlgebra A] [Module ℚ≥0 A]
    {f : (ι → ℤˣ) → A} (hf : ∀ ε, IsSelfAdjoint (f ε)) :
    IsSelfAdjoint (𝔼 ε : ι → ℤˣ, f ε) := by
  rw [IsSelfAdjoint, star_expect_units]
  exact Finset.expect_congr rfl fun ε _ => (hf ε).star_eq

private theorem real_smul_expect_units {M : Type*} [AddCommGroup M] [Module ℚ≥0 M] [Module ℝ M]
    (r : ℝ) (f : (ι → ℤˣ) → M) :
    r • (𝔼 ε : ι → ℤˣ, f ε) = 𝔼 ε : ι → ℤˣ, r • f ε := by
  rw [expect_eq_inv_card_smul_sum, expect_eq_inv_card_smul_sum, smul_comm, Finset.smul_sum]

private theorem expect_units_smul_const {M : Type*} [AddCommGroup M] [Module ℚ≥0 M] [Module ℝ M]
    (g : (ι → ℤˣ) → ℝ) (m : M) :
    (𝔼 ε : ι → ℤˣ, g ε • m) = (𝔼 ε : ι → ℤˣ, g ε) • m := by
  rw [expect_eq_inv_card_smul_sum, expect_eq_inv_card_smul_sum, ← Finset.sum_smul, smul_smul]
  rfl

private theorem mul_expect_units {A : Type*} [NonUnitalCStarAlgebra A] [Module ℚ≥0 A]
    (a : A) (f : (ι → ℤˣ) → A) :
    a * (𝔼 ε : ι → ℤˣ, f ε) = 𝔼 ε : ι → ℤˣ, a * f ε := by
  rw [expect_eq_inv_card_smul_sum, expect_eq_inv_card_smul_sum, mul_smul_comm, Finset.mul_sum]

private theorem expect_units_mul {A : Type*} [NonUnitalCStarAlgebra A] [Module ℚ≥0 A]
    (f : (ι → ℤˣ) → A) (a : A) :
    (𝔼 ε : ι → ℤˣ, f ε) * a = 𝔼 ε : ι → ℤˣ, f ε * a := by
  rw [expect_eq_inv_card_smul_sum, expect_eq_inv_card_smul_sum, smul_mul_assoc, Finset.sum_mul]

private theorem expect_units_nonneg {A : Type*} [NonUnitalCStarAlgebra A] [Module ℚ≥0 A]
    [PartialOrder A] [StarOrderedRing A] {f : (ι → ℤˣ) → A} (hf : ∀ ε, 0 ≤ f ε) :
    0 ≤ 𝔼 ε : ι → ℤˣ, f ε := by
  rw [expect_eq_inv_card_smul_sum]
  exact smul_nonneg (by positivity) (Finset.sum_nonneg fun ε _ => hf ε)

private theorem expect_units_mono {A : Type*} [NonUnitalCStarAlgebra A] [Module ℚ≥0 A]
    [PartialOrder A] [StarOrderedRing A] {f g : (ι → ℤˣ) → A} (hfg : ∀ ε, f ε ≤ g ε) :
    𝔼 ε : ι → ℤˣ, f ε ≤ 𝔼 ε : ι → ℤˣ, g ε := by
  rw [expect_eq_inv_card_smul_sum, expect_eq_inv_card_smul_sum]
  exact smul_le_smul_of_nonneg_left (Finset.sum_le_sum fun ε _ => hfg ε) (by positivity)

/-- Extracting the `i`-th Rademacher coefficient of a Rademacher sum `∑ j, ε j • x j` recovers
`x i`. -/
theorem expect_units_smul_sum_units_smul {M : Type*} [AddCommGroup M] [Module ℚ≥0 M] [Module ℝ M]
    (x : ι → M) (i : ι) :
    𝔼 ε : ι → ℤˣ, ε i • ∑ j, ε j • x j = x i := by
  simp_rw [Finset.smul_sum]
  rw [Finset.expect_sum_comm]
  have hterm (j : ι) :
      (𝔼 ε : ι → ℤˣ, ε i • (ε j • x j)) = if i = j then x j else 0 := by
    have hsmul (ε : ι → ℤˣ) :
        ε i • (ε j • x j) = (((ε i : ℤ) : ℝ) * (ε j : ℤ)) • x j := by
      rw [units_smul_eq_real_smul, units_smul_eq_real_smul, mul_smul]
    simp_rw [hsmul]
    rw [expect_units_smul_const, expect_units_apply_mul_apply]
    split_ifs <;> simp
  simp_rw [hterm]
  simp

/-- Averaged over the sign cube, the product of four Rademacher signs splits into the three pair
matchings minus twice the quadruple diagonal. -/
theorem expect_units_mul_four (i j k l : ι) :
    𝔼 ε : ι → ℤˣ, ((ε i : ℤ) : ℝ) * (ε j : ℤ) * (ε k : ℤ) * (ε l : ℤ) =
      (if i = j ∧ k = l then 1 else 0) +
      (if i = k ∧ j = l then 1 else 0) +
      (if i = l ∧ j = k then 1 else 0) -
      2 * (if i = j ∧ j = k ∧ k = l then 1 else 0) := by
  have hunit_sq (u : ℤˣ) : ((u : ℤ) : ℝ) * (u : ℤ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    norm_num
  by_cases hij : i = j
  · subst hij
    have hsq (ε : ι → ℤˣ) :
        ((ε i : ℤ) : ℝ) * (ε i : ℤ) * (ε k : ℤ) * (ε l : ℤ) =
          ((ε k : ℤ) : ℝ) * (ε l : ℤ) := by
      rw [hunit_sq, one_mul]
    simp_rw [hsq, expect_units_apply_mul_apply]
    by_cases hkl : k = l <;> by_cases hik : i = k <;> subst_vars <;> simp_all; norm_num
  · by_cases hik : i = k
    · subst hik
      have hsq (ε : ι → ℤˣ) :
          ((ε i : ℤ) : ℝ) * (ε j : ℤ) * (ε i : ℤ) * (ε l : ℤ) =
            ((ε j : ℤ) : ℝ) * (ε l : ℤ) := by
        calc ((ε i : ℤ) : ℝ) * (ε j : ℤ) * (ε i : ℤ) * (ε l : ℤ)
            = (((ε i : ℤ) : ℝ) * (ε i : ℤ)) * (((ε j : ℤ) : ℝ) * (ε l : ℤ)) := by ring
          _ = ((ε j : ℤ) : ℝ) * (ε l : ℤ) := by rw [hunit_sq, one_mul]
      simp_rw [hsq, expect_units_apply_mul_apply]
      by_cases hjl : j = l <;> subst_vars <;> simp_all
    · by_cases hil : i = l
      · subst hil
        have hsq (ε : ι → ℤˣ) :
            ((ε i : ℤ) : ℝ) * (ε j : ℤ) * (ε k : ℤ) * (ε i : ℤ) =
              ((ε j : ℤ) : ℝ) * (ε k : ℤ) := by
          calc ((ε i : ℤ) : ℝ) * (ε j : ℤ) * (ε k : ℤ) * (ε i : ℤ)
              = (((ε i : ℤ) : ℝ) * (ε i : ℤ)) * (((ε j : ℤ) : ℝ) * (ε k : ℤ)) := by ring
            _ = ((ε j : ℤ) : ℝ) * (ε k : ℤ) := by rw [hunit_sq, one_mul]
        simp_rw [hsq, expect_units_apply_mul_apply]
        by_cases hjk : j = k <;> subst_vars <;> simp_all
      · simp only [hij, hik, hil, false_and, ite_false, mul_zero, add_zero, sub_zero]
        let σ := Equiv.mulLeft (Pi.mulSingle i (-1) : ι → ℤˣ)
        have h := Fintype.expect_equiv σ
          (fun ε : ι → ℤˣ => -(((ε i : ℤ) : ℝ) * (ε j : ℤ) * (ε k : ℤ) * (ε l : ℤ)))
          (fun ε : ι → ℤˣ => ((ε i : ℤ) : ℝ) * (ε j : ℤ) * (ε k : ℤ) * (ε l : ℤ))
          fun ε => by simp [σ, Ne.symm hij, Ne.symm hik, Ne.symm hil]
        rw [Finset.expect_neg_distrib] at h
        linarith

end SignExpect

/-! ### Operator-valued Bessel inequalities on the sign cube -/

section Bessel

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [NonUnitalCStarAlgebra A] [Module ℚ≥0 A]
  [PartialOrder A] [StarOrderedRing A]

/-- Operator-valued Bessel inequality (column form): the Rademacher Fourier coefficients
`y k = 𝔼 ε, ε k • Φ ε` satisfy `∑ k, star (y k) * y k ≤ 𝔼 ε, star (Φ ε) * Φ ε`. -/
theorem sum_star_expect_units_smul_mul_le (Φ : (ι → ℤˣ) → A) :
    ∑ k, star (𝔼 ε : ι → ℤˣ, ε k • Φ ε) * (𝔼 ε : ι → ℤˣ, ε k • Φ ε) ≤
      𝔼 ε : ι → ℤˣ, star (Φ ε) * Φ ε := by
  set y : ι → A := fun k => 𝔼 ε : ι → ℤˣ, ε k • Φ ε
  set S : (ι → ℤˣ) → A := fun ε => ∑ k, ε k • y k
  have hnonneg : 0 ≤ 𝔼 ε : ι → ℤˣ, star (Φ ε - S ε) * (Φ ε - S ε) :=
    expect_units_nonneg fun ε => star_mul_self_nonneg _
  have hcross1 : 𝔼 ε : ι → ℤˣ, star (S ε) * Φ ε = ∑ k, star (y k) * y k := by
    simp only [S, star_sum, star_units_smul, Finset.sum_mul]
    rw [Finset.expect_sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hterm (ε : ι → ℤˣ) : (ε k • star (y k)) * Φ ε = star (y k) * (ε k • Φ ε) := by
      rw [units_smul_eq_real_smul, units_smul_eq_real_smul, smul_mul_assoc, mul_smul_comm]
    simp_rw [hterm, ← mul_expect_units]
    rfl
  have hcross2 : 𝔼 ε : ι → ℤˣ, star (Φ ε) * S ε = ∑ k, star (y k) * y k := by
    have hst := congrArg star hcross1
    simpa only [star_expect_units, star_mul, star_star, star_sum] using hst
  have hsq : 𝔼 ε : ι → ℤˣ, star (S ε) * S ε = ∑ k, star (y k) * y k := by
    simp only [S, star_sum, star_units_smul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.expect_sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.expect_sum_comm]
    have hterm (j : ι) :
        (𝔼 ε : ι → ℤˣ, (ε j • star (y j)) * (ε i • y i)) =
          if j = i then star (y j) * y i else 0 := by
      have hsmul (ε : ι → ℤˣ) :
          (ε j • star (y j)) * (ε i • y i) =
            (((ε j : ℤ) : ℝ) * (ε i : ℤ)) • (star (y j) * y i) := by
        rw [units_smul_eq_real_smul, units_smul_eq_real_smul, smul_mul_assoc,
          mul_smul_comm, mul_smul]
      simp_rw [hsmul]
      rw [expect_units_smul_const, expect_units_apply_mul_apply]
      split_ifs <;> simp only [one_smul, zero_smul]
    exact (Finset.sum_congr rfl fun j _ => hterm j).trans
      (Fintype.sum_ite_eq' i fun j => star (y j) * y i)
  have hexpand :
      𝔼 ε : ι → ℤˣ, star (Φ ε - S ε) * (Φ ε - S ε) =
        (𝔼 ε : ι → ℤˣ, star (Φ ε) * Φ ε) - ∑ k, star (y k) * y k := by
    have hpt (ε : ι → ℤˣ) :
        star (Φ ε - S ε) * (Φ ε - S ε) =
          star (Φ ε) * Φ ε - star (Φ ε) * S ε - star (S ε) * Φ ε + star (S ε) * S ε := by
      rw [star_sub, mul_sub, sub_mul, sub_mul]
      abel
    simp_rw [hpt]
    rw [Finset.expect_add_distrib, Finset.expect_sub_distrib, Finset.expect_sub_distrib,
      hcross1, hcross2, hsq]
    abel
  rw [hexpand, sub_nonneg] at hnonneg
  exact hnonneg

/-- Operator-valued Bessel inequality (row form): the Rademacher Fourier coefficients
`y k = 𝔼 ε, ε k • Φ ε` satisfy `∑ k, y k * star (y k) ≤ 𝔼 ε, Φ ε * star (Φ ε)`. -/
theorem sum_expect_units_smul_mul_star_le (Φ : (ι → ℤˣ) → A) :
    ∑ k, (𝔼 ε : ι → ℤˣ, ε k • Φ ε) * star (𝔼 ε : ι → ℤˣ, ε k • Φ ε) ≤
      𝔼 ε : ι → ℤˣ, Φ ε * star (Φ ε) := by
  have h := sum_star_expect_units_smul_mul_le (fun ε : ι → ℤˣ => star (Φ ε))
  simpa only [← star_units_smul, ← star_expect_units, star_star] using h

/-- If `‖Φ ε‖ ≤ C` for all `ε`, then the Rademacher Fourier coefficients `y k = 𝔼 ε, ε k • Φ ε`
satisfy `‖columnSquare y‖ ≤ C`. -/
theorem norm_columnSquare_expect_units_smul_le {Φ : (ι → ℤˣ) → A} {C : ℝ} (hC : 0 ≤ C)
    (hΦ : ∀ ε, ‖Φ ε‖ ≤ C) :
    ‖columnSquare (fun k => 𝔼 ε : ι → ℤˣ, ε k • Φ ε)‖ ≤ C := by
  rw [norm_columnSquare, ← Real.sqrt_sq hC]
  refine Real.sqrt_le_sqrt ?_
  have hbessel := sum_star_expect_units_smul_mul_le Φ
  have hsum_nonneg :
      0 ≤ ∑ k, star (𝔼 ε : ι → ℤˣ, ε k • Φ ε) * (𝔼 ε : ι → ℤˣ, ε k • Φ ε) :=
    Finset.sum_nonneg fun k _ => star_mul_self_nonneg _
  calc ‖∑ k, star (𝔼 ε : ι → ℤˣ, ε k • Φ ε) * (𝔼 ε : ι → ℤˣ, ε k • Φ ε)‖
      ≤ ‖𝔼 ε : ι → ℤˣ, star (Φ ε) * Φ ε‖ :=
        CStarAlgebra.norm_le_norm_of_le_of_nonneg hbessel hsum_nonneg
    _ ≤ 𝔼 ε : ι → ℤˣ, ‖star (Φ ε) * Φ ε‖ := by
        rw [expect_eq_inv_card_smul_sum, expect_eq_inv_card_smul_sum, norm_smul,
          Real.norm_of_nonneg (by positivity), smul_eq_mul]
        gcongr
        exact norm_sum_le _ _
    _ ≤ 𝔼 _ε : ι → ℤˣ, C ^ 2 := by
        refine Finset.expect_le_expect fun ε _ => ?_
        rw [CStarRing.norm_star_mul_self, ← sq]
        exact pow_le_pow_left₀ (norm_nonneg _) (hΦ ε) 2
    _ = C ^ 2 := Finset.expect_const Finset.univ_nonempty (C ^ 2)

/-- If `‖Φ ε‖ ≤ C` for all `ε`, then the Rademacher Fourier coefficients `y k = 𝔼 ε, ε k • Φ ε`
satisfy `‖rowSquare y‖ ≤ C`. -/
theorem norm_rowSquare_expect_units_smul_le {Φ : (ι → ℤˣ) → A} {C : ℝ} (hC : 0 ≤ C)
    (hΦ : ∀ ε, ‖Φ ε‖ ≤ C) :
    ‖rowSquare (fun k => 𝔼 ε : ι → ℤˣ, ε k • Φ ε)‖ ≤ C := by
  have h := norm_columnSquare_expect_units_smul_le (Φ := fun ε => star (Φ ε)) hC
    (fun ε => by rw [norm_star]; exact hΦ ε)
  simpa only [rowSquare_eq_columnSquare_star, ← star_units_smul, ← star_expect_units] using h

end Bessel

/-! ### The Pisier–Haagerup fourth-moment inequality -/

section FourthMoment

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [NonUnitalCStarAlgebra A] [Module ℚ≥0 A]
  [PartialOrder A] [StarOrderedRing A]

omit [DecidableEq ι] [Module ℚ≥0 A] [PartialOrder A] [StarOrderedRing A] in
private theorem sum_units_smul_mul_four (x : ι → A) (ε : ι → ℤˣ) :
    (∑ i, ε i • x i) * (∑ i, ε i • x i) * (∑ i, ε i • x i) * (∑ i, ε i • x i) =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (((ε i : ℤ) : ℝ) * (ε j : ℤ) * (ε k : ℤ) * (ε l : ℤ)) •
          (x i * x j * x k * x l) := by
  have h2 : (∑ i, ε i • x i) * (∑ j, ε j • x j) =
      ∑ i, ∑ j, (((ε i : ℤ) : ℝ) * (ε j : ℤ)) • (x i * x j) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [units_smul_eq_real_smul, units_smul_eq_real_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_assoc ((∑ i, ε i • x i) * (∑ i, ε i • x i)), h2, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc (((ε i : ℤ) : ℝ) * (ε j : ℤ)),
    ← mul_assoc (x i * x j)]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Exact expansion of the fourth Rademacher moment
`𝔼 ε, (∑ i, ε i • x i) * (∑ i, ε i • x i) * (∑ i, ε i • x i) * (∑ i, ε i • x i)` into the three
pair matchings minus twice the diagonal fourth product. -/
theorem expect_sum_units_smul_mul_four (x : ι → A) :
    𝔼 ε : ι → ℤˣ,
        (∑ i, ε i • x i) * (∑ i, ε i • x i) * (∑ i, ε i • x i) * (∑ i, ε i • x i) =
      (∑ i, x i * x i) * (∑ i, x i * x i) +
      (∑ i, ∑ j, x i * x j * x i * x j) +
      (∑ i, x i * (∑ j, x j * x j) * x i) -
      (2 : ℝ) • ∑ i, x i * x i * x i * x i := by
  simp_rw [sum_units_smul_mul_four]
  rw [Finset.expect_sum_comm]
  simp_rw [Finset.expect_sum_comm, expect_units_smul_const, expect_units_mul_four]
  simp only [sub_smul, add_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h1 :
      (∑ i, ∑ j, ∑ k, ∑ l,
        (if i = j ∧ k = l then (1 : ℝ) else 0) • (x i * x j * x k * x l)) =
        (∑ i, x i * x i) * (∑ i, x i * x i) := by
    simp only [ite_smul, one_smul, zero_smul, ite_and, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Fintype.sum_ite_eq]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => mul_assoc _ _ _
  have h2 :
      (∑ i, ∑ j, ∑ k, ∑ l,
        (if i = k ∧ j = l then (1 : ℝ) else 0) • (x i * x j * x k * x l)) =
        ∑ i, ∑ j, x i * x j * x i * x j := by
    simp only [ite_smul, one_smul, zero_smul, ite_and, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Fintype.sum_ite_eq]
  have h3 :
      (∑ i, ∑ j, ∑ k, ∑ l,
        (if i = l ∧ j = k then (1 : ℝ) else 0) • (x i * x j * x k * x l)) =
        ∑ i, x i * (∑ j, x j * x j) * x i := by
    simp only [ite_smul, one_smul, zero_smul, ite_and, Fintype.sum_ite_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by simp only [mul_assoc]
  have h4 :
      (∑ i, ∑ j, ∑ k, ∑ l,
        (2 * if i = j ∧ j = k ∧ k = l then (1 : ℝ) else 0) • (x i * x j * x k * x l)) =
        (2 : ℝ) • ∑ i, x i * x i * x i * x i := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hterm (j k l : ι) :
        (2 * if i = j ∧ j = k ∧ k = l then (1 : ℝ) else 0) • (x i * x j * x k * x l) =
          if k = l then if j = k then if i = j then (2 : ℝ) • (x i * x j * x k * x l)
            else 0 else 0 else 0 := by
      by_cases hij : i = j <;> by_cases hjk : j = k <;> by_cases hkl : k = l <;>
        simp [hij, hjk, hkl]
    simp_rw [hterm]
    simp only [Fintype.sum_ite_eq]
  rw [h1, h2, h3, h4]

omit [DecidableEq ι] [Module ℚ≥0 A] in
private theorem norm_sum_conj_sum_sq_le {x : ι → A} (hx : ∀ i, IsSelfAdjoint (x i)) :
    ‖∑ i, x i * (∑ j, x j * x j) * x i‖ ≤ ‖∑ i, x i * x i‖ ^ 2 := by
  set M : A := ∑ j, x j * x j
  have hM_nonneg : 0 ≤ M := Finset.sum_nonneg fun j _ => by
    nth_rw 1 [← (hx j).star_eq]
    exact star_mul_self_nonneg (x j)
  have hM_sa : IsSelfAdjoint M := hM_nonneg.isSelfAdjoint
  have hterm_nonneg : 0 ≤ ∑ i, x i * M * x i := Finset.sum_nonneg fun i _ => by
    nth_rw 1 [← (hx i).star_eq]
    exact star_left_conjugate_nonneg hM_nonneg (x i)
  have hterm_le : ∑ i, x i * M * x i ≤ ‖M‖ • M := by
    rw [Finset.smul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    simpa only [(hx i).star_eq] using
      CStarAlgebra.star_left_conjugate_le_norm_smul (x i) M hM_sa
  calc ‖∑ i, x i * M * x i‖
      ≤ ‖‖M‖ • M‖ := CStarAlgebra.norm_le_norm_of_le_of_nonneg hterm_le hterm_nonneg
    _ = ‖M‖ ^ 2 := by rw [norm_smul, Real.norm_of_nonneg (norm_nonneg M), sq]

omit [DecidableEq ι] [Module ℚ≥0 A] in
private theorem norm_sum_alternating_four_le {x : ι → A} (hx : ∀ i, IsSelfAdjoint (x i)) :
    ‖∑ i, ∑ j, x i * x j * x i * x j‖ ≤ ‖∑ i, x i * x i‖ ^ 2 := by
  set M : A := ∑ i, x i * x i
  let u : C⋆ᵐᵒᵈ(A, (ι × ι) → A) :=
    (WithCStarModule.equiv A ((ι × ι) → A)).symm fun p => x p.2 * x p.1
  let v : C⋆ᵐᵒᵈ(A, (ι × ι) → A) :=
    (WithCStarModule.equiv A ((ι × ι) → A)).symm fun p => x p.1 * x p.2
  have hinner : inner A u v = ∑ i, ∑ j, x i * x j * x i * x j := by
    rw [WithCStarModule.pi_inner, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [u, v, WithCStarModule.equiv_symm_pi_apply, WithCStarModule.inner_def,
      star_mul, (hx i).star_eq, (hx j).star_eq, mul_assoc]
  have hu_norm : ‖u‖ ≤ ‖M‖ := by
    rw [WithCStarModule.pi_norm, ← Real.sqrt_sq (norm_nonneg M)]
    refine Real.sqrt_le_sqrt ?_
    have hsum : (∑ p : ι × ι, inner A (u p) (u p)) = ∑ j, x j * M * x j := by
      rw [Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [u, M, WithCStarModule.equiv_symm_pi_apply, WithCStarModule.inner_def,
        Finset.mul_sum, Finset.sum_mul, star_mul, (hx _).star_eq, mul_assoc]
    rw [hsum]
    exact norm_sum_conj_sum_sq_le hx
  have hv_norm : ‖v‖ ≤ ‖M‖ := by
    rw [WithCStarModule.pi_norm, ← Real.sqrt_sq (norm_nonneg M)]
    refine Real.sqrt_le_sqrt ?_
    have hsum : (∑ p : ι × ι, inner A (v p) (v p)) = ∑ i, x i * M * x i := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [v, M, WithCStarModule.equiv_symm_pi_apply, WithCStarModule.inner_def,
        Finset.mul_sum, Finset.sum_mul, star_mul, (hx _).star_eq, mul_assoc]
    rw [hsum]
    exact norm_sum_conj_sum_sq_le hx
  rw [← hinner]
  calc ‖inner A u v‖
      ≤ ‖u‖ * ‖v‖ := CStarModule.norm_inner_le _
    _ ≤ ‖M‖ * ‖M‖ := mul_le_mul hu_norm hv_norm (norm_nonneg _) (norm_nonneg _)
    _ = ‖M‖ ^ 2 := (sq ‖M‖).symm

/-- **Pisier–Haagerup fourth-moment inequality**: for any finite family `x : ι → A` of self-adjoint
elements in a non-unital C⋆-algebra, the fourth Rademacher moment satisfies
`‖𝔼 ε, (∑ i, ε i • x i)^4‖ ≤ 3 * ‖∑ i, x i * x i‖ ^ 2`. -/
theorem norm_expect_sum_units_smul_pow_four_le {x : ι → A} (hx : ∀ i, IsSelfAdjoint (x i)) :
    ‖𝔼 ε : ι → ℤˣ,
        (∑ i, ε i • x i) * (∑ i, ε i • x i) * (∑ i, ε i • x i) * (∑ i, ε i • x i)‖ ≤
      3 * ‖∑ i, x i * x i‖ ^ 2 := by
  have hpow4_nonneg {a : A} (ha : IsSelfAdjoint a) : 0 ≤ a * a * a * a := by
    have h4 : a * a * a * a = star (a * a) * (a * a) := by
      rw [star_mul, ha.star_eq, mul_assoc]
    rw [h4]
    exact star_mul_self_nonneg (a * a)
  have hsum_sa (ε : ι → ℤˣ) : IsSelfAdjoint (∑ i, ε i • x i) := by
    rw [IsSelfAdjoint, star_sum]
    exact Finset.sum_congr rfl fun i _ => (isSelfAdjoint_units_smul (hx i) (ε i)).star_eq
  have hexp_nonneg :
      0 ≤ 𝔼 ε : ι → ℤˣ,
        (∑ i, ε i • x i) * (∑ i, ε i • x i) * (∑ i, ε i • x i) * (∑ i, ε i • x i) :=
    expect_units_nonneg fun ε => hpow4_nonneg (hsum_sa ε)
  have hdiag_nonneg : 0 ≤ (2 : ℝ) • ∑ i, x i * x i * x i * x i :=
    smul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hpow4_nonneg (hx i))
  set B : A :=
    (∑ i, x i * x i) * (∑ i, x i * x i) +
    (∑ i, ∑ j, x i * x j * x i * x j) +
    (∑ i, x i * (∑ j, x j * x j) * x i)
  have hle :
      (𝔼 ε : ι → ℤˣ,
        (∑ i, ε i • x i) * (∑ i, ε i • x i) * (∑ i, ε i • x i) * (∑ i, ε i • x i)) ≤ B := by
    rw [expect_sum_units_smul_mul_four]
    exact sub_le_self B hdiag_nonneg
  have hnorm1 : ‖(∑ i, x i * x i) * (∑ i, x i * x i)‖ ≤ ‖∑ i, x i * x i‖ ^ 2 := by
    simpa only [sq] using norm_mul_le (∑ i, x i * x i) (∑ i, x i * x i)
  calc ‖𝔼 ε : ι → ℤˣ,
          (∑ i, ε i • x i) * (∑ i, ε i • x i) * (∑ i, ε i • x i) * (∑ i, ε i • x i)‖
      ≤ ‖B‖ := CStarAlgebra.norm_le_norm_of_le_of_nonneg hle hexp_nonneg
    _ ≤ ‖(∑ i, x i * x i) * (∑ i, x i * x i)‖ + ‖∑ i, ∑ j, x i * x j * x i * x j‖ +
          ‖∑ i, x i * (∑ j, x j * x j) * x i‖ := norm_add₃_le
    _ ≤ ‖∑ i, x i * x i‖ ^ 2 + ‖∑ i, x i * x i‖ ^ 2 + ‖∑ i, x i * x i‖ ^ 2 :=
        add_le_add (add_le_add hnorm1 (norm_sum_alternating_four_le hx))
          (norm_sum_conj_sum_sq_le hx)
    _ = 3 * ‖∑ i, x i * x i‖ ^ 2 := by ring

end FourthMoment

/-! ### Functional-calculus truncation and dual Rademacher factorization -/

section Factorization

private def pisierCutoff (t : ℝ) : ℝ :=
  max (-(Real.sqrt 3 / 2)) (min (Real.sqrt 3 / 2) t)

private theorem continuous_pisierCutoff : Continuous pisierCutoff :=
  continuous_const.max (continuous_const.min continuous_id)

private theorem pisierCutoff_zero : pisierCutoff 0 = 0 := by
  have hpos : (0 : ℝ) ≤ Real.sqrt 3 / 2 := by positivity
  simp [pisierCutoff, min_eq_right hpos, max_eq_right (neg_nonpos.mpr hpos)]

private theorem pisierCutoff_neg (t : ℝ) : pisierCutoff (-t) = -pisierCutoff t := by
  have hpos : (0 : ℝ) ≤ Real.sqrt 3 / 2 := by positivity
  unfold pisierCutoff
  simp only [min_def, max_def]
  split_ifs <;> linarith

private theorem abs_pisierCutoff_le (t : ℝ) : |pisierCutoff t| ≤ Real.sqrt 3 / 2 := by
  have hpos : (0 : ℝ) ≤ Real.sqrt 3 / 2 := by positivity
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

private theorem sub_pisierCutoff_sq_le (t : ℝ) :
    (t - pisierCutoff t) ^ 2 ≤ (1 / 12 : ℝ) * t ^ 4 := by
  set c₀ : ℝ := Real.sqrt 3 / 2
  have hc₀_pos : 0 ≤ c₀ := by positivity
  have hc₀_sq : c₀ ^ 2 = 3 / 4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hpos_case {s : ℝ} (hs : c₀ ≤ s) :
      (s - c₀) ^ 2 ≤ (1 / 12 : ℝ) * s ^ 4 := by
    have hdiff :
        (1 / 12 : ℝ) * s ^ 4 - (s - c₀) ^ 2 =
          (1 / 12 : ℝ) * (s - 2 * c₀) ^ 2 * (s ^ 2 + 4 * c₀ * s - 4 * c₀ ^ 2) := by
      calc (1 / 12 : ℝ) * s ^ 4 - (s - c₀) ^ 2
          = (1 / 12 : ℝ) * s ^ 4 - (4 / 3 * c₀ ^ 2) * (s - c₀) ^ 2 := by
              rw [hc₀_sq]; ring
        _ = (1 / 12 : ℝ) * (s - 2 * c₀) ^ 2 * (s ^ 2 + 4 * c₀ * s - 4 * c₀ ^ 2) := by ring
    have hfac : 0 ≤ s ^ 2 + 4 * c₀ * s - 4 * c₀ ^ 2 := by
      have hmul : 4 * c₀ ^ 2 ≤ 4 * c₀ * s := by
        rw [sq, ← mul_assoc]
        exact mul_le_mul_of_nonneg_left hs (by positivity)
      linarith [sq_nonneg s]
    have hnn : 0 ≤ (1 / 12 : ℝ) * s ^ 4 - (s - c₀) ^ 2 := by
      rw [hdiff]
      exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hfac
    linarith
  rcases lt_or_ge t (-c₀) with hlt | hge
  · have hns : c₀ ≤ -t := by linarith
    have hcut : pisierCutoff (-t) = c₀ := by
      simp [pisierCutoff, c₀, min_eq_left hns, max_eq_right (by linarith : -c₀ ≤ c₀)]
    have h := hpos_case hns
    rw [← hcut, pisierCutoff_neg] at h
    have h1 : (-t - -pisierCutoff t) ^ 2 = (t - pisierCutoff t) ^ 2 := by ring
    have h2 : (-t) ^ 4 = t ^ 4 := by ring
    rwa [h1, h2] at h
  · rcases le_or_gt t c₀ with hle | hgt
    · have hcut : pisierCutoff t = t := by
        simp [pisierCutoff, c₀, min_eq_right hle, max_eq_right hge]
      rw [hcut, sub_self, zero_pow two_ne_zero]
      positivity
    · have hcut : pisierCutoff t = c₀ := by
        simp [pisierCutoff, c₀, min_eq_left hgt.le, max_eq_right (by linarith : -c₀ ≤ c₀)]
      rw [hcut]
      exact hpos_case hgt.le

section TruncationStep

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [NonUnitalCStarAlgebra A] [Module ℚ≥0 A]
  [PartialOrder A] [StarOrderedRing A]

private def pisierTruncate (x : ι → A) (ε : ι → ℤˣ) : A :=
  cfcₙ pisierCutoff (∑ i, ε i • x i)

private def pisierRemainder (x : ι → A) (i : ι) : A :=
  x i - 𝔼 ε : ι → ℤˣ, ε i • pisierTruncate x ε

omit [DecidableEq ι] [Module ℚ≥0 A] [PartialOrder A] [StarOrderedRing A] in
private theorem isSelfAdjoint_pisierTruncate (x : ι → A) (ε : ι → ℤˣ) :
    IsSelfAdjoint (pisierTruncate x ε) :=
  cfcₙ_predicate pisierCutoff _

omit [DecidableEq ι] [Module ℚ≥0 A] [PartialOrder A] [StarOrderedRing A] in
private theorem norm_pisierTruncate_le (x : ι → A) (ε : ι → ℤˣ) :
    ‖pisierTruncate x ε‖ ≤ Real.sqrt 3 / 2 :=
  norm_cfcₙ_le fun t _ => by simpa only [Real.norm_eq_abs] using abs_pisierCutoff_le t

omit [PartialOrder A] [StarOrderedRing A] in
private theorem isSelfAdjoint_pisierRemainder {x : ι → A} (hx : ∀ i, IsSelfAdjoint (x i))
    (i : ι) : IsSelfAdjoint (pisierRemainder x i) :=
  (hx i).sub (isSelfAdjoint_expect_units fun ε =>
    isSelfAdjoint_units_smul (isSelfAdjoint_pisierTruncate x ε) (ε i))

omit [Fintype ι] [DecidableEq ι] [Module ℚ≥0 A] in
private theorem sub_cfcₙ_pisierCutoff_sq_le {s : A} (hsa : IsSelfAdjoint s) :
    (s - cfcₙ pisierCutoff s) * (s - cfcₙ pisierCutoff s) ≤
      (1 / 12 : ℝ) • (s * s * s * s) := by
  have hcut_cont : ContinuousOn pisierCutoff (quasispectrum ℝ s) :=
    continuous_pisierCutoff.continuousOn
  have hδ_cfc : s - cfcₙ pisierCutoff s = cfcₙ (fun t : ℝ => t - pisierCutoff t) s := by
    nth_rw 1 [← cfcₙ_id' ℝ s hsa]
    exact (cfcₙ_sub (fun t : ℝ => t) pisierCutoff s
      (hf := continuousOn_id) (hf0 := rfl) (hg := hcut_cont) (hg0 := pisierCutoff_zero)).symm
  have hδ2_cfc :
      (s - cfcₙ pisierCutoff s) * (s - cfcₙ pisierCutoff s) =
        cfcₙ (fun t : ℝ => (t - pisierCutoff t) ^ 2) s := by
    have hfun : (fun t : ℝ => (t - pisierCutoff t) ^ 2) =
        fun t : ℝ => (t - pisierCutoff t) * (t - pisierCutoff t) := by
      ext t; ring
    rw [hδ_cfc, hfun, ← cfcₙ_mul (fun t : ℝ => t - pisierCutoff t)
      (fun t : ℝ => t - pisierCutoff t) s
      (hf := continuousOn_id.sub hcut_cont) (hf0 := by simp [pisierCutoff_zero])
      (hg := continuousOn_id.sub hcut_cont) (hg0 := by simp [pisierCutoff_zero])]
  have hS4_cfc :
      (1 / 12 : ℝ) • (s * s * s * s) = cfcₙ (fun t : ℝ => (1 / 12 : ℝ) * t ^ 4) s := by
    have hS2 : s * s = cfcₙ (fun t : ℝ => t * t) s := by
      conv_lhs => rw [← cfcₙ_id' ℝ s hsa]
      exact (cfcₙ_mul (fun t : ℝ => t) (fun t : ℝ => t) s
        (hf := continuousOn_id) (hf0 := rfl) (hg := continuousOn_id) (hg0 := rfl)).symm
    have hpow4 : s * s * s * s = cfcₙ (fun t : ℝ => t ^ 4) s := by
      have hfun4 : (fun t : ℝ => t ^ 4) = fun t : ℝ => (t * t) * (t * t) := by
        ext t; ring
      rw [mul_assoc (s * s), hS2, hfun4, ← cfcₙ_mul (fun t : ℝ => t * t)
        (fun t : ℝ => t * t) s
        (hf := continuousOn_id.mul continuousOn_id) (hf0 := mul_zero 0)
        (hg := continuousOn_id.mul continuousOn_id) (hg0 := mul_zero 0)]
    rw [hpow4, ← cfcₙ_const_mul (1 / 12 : ℝ) (fun t : ℝ => t ^ 4) s
      (hf := (continuous_pow 4).continuousOn) (h0 := by simp)]
  rw [hδ2_cfc, hS4_cfc]
  exact cfcₙ_mono (fun t _ => sub_pisierCutoff_sq_le t)
    (hf := ((continuous_id.sub continuous_pisierCutoff).pow 2).continuousOn)
    (hg := (continuous_const.mul (continuous_pow 4)).continuousOn)
    (hf0 := by simp [pisierCutoff_zero]) (hg0 := by simp)

private theorem norm_sum_pisierRemainder_sq_le {x : ι → A} (hx : ∀ i, IsSelfAdjoint (x i))
    (hnorm : ‖∑ i, x i * x i‖ ≤ 1) :
    ‖∑ i, pisierRemainder x i * pisierRemainder x i‖ ≤ 1 / 4 := by
  set S : (ι → ℤˣ) → A := fun ε => ∑ i, ε i • x i
  set δ : (ι → ℤˣ) → A := fun ε => S ε - pisierTruncate x ε
  have hS_sa (ε : ι → ℤˣ) : IsSelfAdjoint (S ε) := by
    rw [IsSelfAdjoint, star_sum]
    exact Finset.sum_congr rfl fun i _ => (isSelfAdjoint_units_smul (hx i) (ε i)).star_eq
  have hδ_sa (ε : ι → ℤˣ) : IsSelfAdjoint (δ ε) :=
    (hS_sa ε).sub (isSelfAdjoint_pisierTruncate x ε)
  have hrem_eq (i : ι) : pisierRemainder x i = 𝔼 ε : ι → ℤˣ, ε i • δ ε := by
    simp only [pisierRemainder, δ, smul_sub, Finset.expect_sub_distrib]
    rw [expect_units_smul_sum_units_smul x i]
  have hbessel :
      ∑ i, pisierRemainder x i * pisierRemainder x i ≤ 𝔼 ε : ι → ℤˣ, δ ε * δ ε := by
    have h := sum_star_expect_units_smul_mul_le δ
    refine (Finset.sum_congr rfl fun i _ => ?_).symm.trans_le
      (h.trans_eq (Finset.expect_congr rfl fun ε _ => ?_))
    · rw [← hrem_eq i, (isSelfAdjoint_pisierRemainder hx i).star_eq]
    · rw [(hδ_sa ε).star_eq]
  have hrem_nonneg : 0 ≤ ∑ i, pisierRemainder x i * pisierRemainder x i :=
    Finset.sum_nonneg fun i _ => by
      nth_rw 1 [← (isSelfAdjoint_pisierRemainder hx i).star_eq]
      exact star_mul_self_nonneg _
  have hchain :
      ∑ i, pisierRemainder x i * pisierRemainder x i ≤
        (1 / 12 : ℝ) • 𝔼 ε : ι → ℤˣ, S ε * S ε * S ε * S ε :=
    hbessel.trans ((expect_units_mono fun ε => sub_cfcₙ_pisierCutoff_sq_le (hS_sa ε)).trans_eq
      (real_smul_expect_units _ _).symm)
  calc ‖∑ i, pisierRemainder x i * pisierRemainder x i‖
      ≤ ‖(1 / 12 : ℝ) • 𝔼 ε : ι → ℤˣ, S ε * S ε * S ε * S ε‖ :=
        CStarAlgebra.norm_le_norm_of_le_of_nonneg hchain hrem_nonneg
    _ = (1 / 12 : ℝ) * ‖𝔼 ε : ι → ℤˣ, S ε * S ε * S ε * S ε‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    _ ≤ (1 / 12 : ℝ) * (3 * ‖∑ i, x i * x i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (norm_expect_sum_units_smul_pow_four_le hx) (by norm_num)
    _ ≤ (1 / 12 : ℝ) * (3 * 1 ^ 2) := by gcongr
    _ = 1 / 4 := by norm_num

private def pisierIter (x : ι → A) : ℕ → ι → A
  | 0 => x
  | m + 1 => fun i => (2 : ℝ) • pisierRemainder (pisierIter x m) i

omit [PartialOrder A] [StarOrderedRing A] in
@[simp]
private theorem pisierIter_zero (x : ι → A) (i : ι) : pisierIter x 0 i = x i :=
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
private theorem pisierIter_succ (x : ι → A) (m : ℕ) (i : ι) :
    pisierIter x (m + 1) i = (2 : ℝ) • pisierRemainder (pisierIter x m) i :=
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
private theorem isSelfAdjoint_pisierIter {x : ι → A} (hx : ∀ i, IsSelfAdjoint (x i)) :
    ∀ m i, IsSelfAdjoint (pisierIter x m i)
  | 0, i => hx i
  | m + 1, i => by
    rw [pisierIter_succ, IsSelfAdjoint, star_smul, star_trivial,
      (isSelfAdjoint_pisierRemainder (isSelfAdjoint_pisierIter hx m) i).star_eq]

private theorem norm_sum_pisierIter_sq_le_one {x : ι → A} (hx : ∀ i, IsSelfAdjoint (x i))
    (hnorm : ‖∑ i, x i * x i‖ ≤ 1) :
    ∀ m, ‖∑ i, pisierIter x m i * pisierIter x m i‖ ≤ 1
  | 0 => hnorm
  | m + 1 => by
    have ih := norm_sum_pisierIter_sq_le_one hx hnorm m
    have hrem := norm_sum_pisierRemainder_sq_le (isSelfAdjoint_pisierIter hx m) ih
    have hsum : ∑ i, pisierIter x (m + 1) i * pisierIter x (m + 1) i =
        (4 : ℝ) • ∑ i, pisierRemainder (pisierIter x m) i * pisierRemainder (pisierIter x m) i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pisierIter_succ, smul_mul_assoc, mul_smul_comm, smul_smul]
      norm_num
    rw [hsum, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    linarith

private theorem norm_pisierIter_apply_le_one {x : ι → A} (hx : ∀ i, IsSelfAdjoint (x i))
    (hnorm : ‖∑ i, x i * x i‖ ≤ 1) (N : ℕ) (i : ι) :
    ‖pisierIter x N i‖ ≤ 1 := by
  refine (norm_apply_le_norm_columnSquare (pisierIter x N) i).trans ?_
  rw [norm_columnSquare]
  have hsq_eq : (∑ k, star (pisierIter x N k) * pisierIter x N k) =
      ∑ k, pisierIter x N k * pisierIter x N k :=
    Finset.sum_congr rfl fun k _ => by rw [(isSelfAdjoint_pisierIter hx N k).star_eq]
  rw [hsq_eq]
  exact Real.sqrt_le_one.mpr (norm_sum_pisierIter_sq_le_one hx hnorm N)

omit [PartialOrder A] [StarOrderedRing A] in
private theorem expect_units_smul_pisierTruncate_iter (x : ι → A) (m : ℕ) (i : ι) :
    (𝔼 ε : ι → ℤˣ, ε i • (((1 / 2 : ℝ) ^ m) • pisierTruncate (pisierIter x m) ε)) =
      ((1 / 2 : ℝ) ^ m) • pisierIter x m i -
        ((1 / 2 : ℝ) ^ (m + 1)) • pisierIter x (m + 1) i := by
  have hpt (ε : ι → ℤˣ) :
      ε i • (((1 / 2 : ℝ) ^ m) • pisierTruncate (pisierIter x m) ε) =
        ((1 / 2 : ℝ) ^ m) • (ε i • pisierTruncate (pisierIter x m) ε) := by
    rw [units_smul_eq_real_smul, smul_smul, mul_comm, ← smul_smul, ← units_smul_eq_real_smul]
  simp_rw [hpt, ← real_smul_expect_units]
  have hexp_trunc :
      (𝔼 ε : ι → ℤˣ, ε i • pisierTruncate (pisierIter x m) ε) =
        pisierIter x m i - pisierRemainder (pisierIter x m) i := by
    simp [pisierRemainder]
  rw [hexp_trunc, smul_sub, pisierIter_succ, smul_smul, pow_succ, mul_assoc]
  norm_num

private theorem exists_isSelfAdjoint_expect_units_smul_eq_of_norm_le_one
    {x : ι → A} (hx : ∀ i, IsSelfAdjoint (x i)) (hnorm : ‖∑ i, x i * x i‖ ≤ 1) :
    ∃ Φ : (ι → ℤˣ) → A,
      (∀ ε, IsSelfAdjoint (Φ ε)) ∧
      (∀ i, 𝔼 ε : ι → ℤˣ, ε i • Φ ε = x i) ∧
      ∀ ε, ‖Φ ε‖ ≤ Real.sqrt 3 := by
  let g : ℕ → (ι → ℤˣ) → A :=
    fun m ε => ((1 / 2 : ℝ) ^ m) • pisierTruncate (pisierIter x m) ε
  have hgeom : HasSum (fun m : ℕ => ((1 / 2 : ℝ) ^ m) * (Real.sqrt 3 / 2)) (Real.sqrt 3) := by
    simpa [mul_div_cancel₀ _ (two_ne_zero' ℝ)] using
      hasSum_geometric_two.mul_right (Real.sqrt 3 / 2)
  have hg_norm (m : ℕ) (ε : ι → ℤˣ) :
      ‖g m ε‖ ≤ ((1 / 2 : ℝ) ^ m) * (Real.sqrt 3 / 2) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_pisierTruncate_le _ ε) (by positivity)
  have hg_summ (ε : ι → ℤˣ) : Summable (fun m => g m ε) :=
    Summable.of_norm_bounded hgeom.summable fun m => hg_norm m ε
  refine ⟨fun ε => ∑' m, g m ε, ?_, ?_, ?_⟩
  · intro ε
    have hsa (m : ℕ) : g m ε = star (g m ε) := by
      dsimp only [g]
      rw [star_smul, star_trivial, (isSelfAdjoint_pisierTruncate _ ε).star_eq]
    exact ((hg_summ ε).hasSum.star.congr_fun hsa).unique (hg_summ ε).hasSum
  · intro i
    have hexp_hasSum :
        HasSum (fun m => 𝔼 ε : ι → ℤˣ, ε i • g m ε)
          (𝔼 ε : ι → ℤˣ, ε i • ∑' m, g m ε) := by
      have hsum : HasSum (fun m => ∑ ε : ι → ℤˣ, ε i • g m ε)
          (∑ ε : ι → ℤˣ, ε i • ∑' m, g m ε) := by
        simp_rw [units_smul_eq_real_smul]
        exact hasSum_sum fun ε _ => (hg_summ ε).hasSum.const_smul ((ε i : ℤ) : ℝ)
      simpa only [← expect_eq_inv_card_smul_sum] using
        hsum.const_smul (Fintype.card (ι → ℤˣ) : ℝ)⁻¹
    have htail : Tendsto (fun N : ℕ => ((1 / 2 : ℝ) ^ N) • pisierIter x N i) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun N => ?_)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num : (1 / 2 : ℝ) < 1))
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact mul_le_of_le_one_right (by positivity) (norm_pisierIter_apply_le_one hx hnorm N i)
    have hpart : Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N, 𝔼 ε : ι → ℤˣ, ε i • g m ε)
        atTop (𝓝 (x i)) := by
      have hsub (N : ℕ) :
          (∑ m ∈ Finset.range N, 𝔼 ε : ι → ℤˣ, ε i • g m ε) =
            x i - ((1 / 2 : ℝ) ^ N) • pisierIter x N i := by
        dsimp only [g]
        simp_rw [expect_units_smul_pisierTruncate_iter x _ i]
        simpa using Finset.sum_range_sub' (fun m => ((1 / 2 : ℝ) ^ m) • pisierIter x m i) N
      simp_rw [hsub]
      simpa using tendsto_const_nhds.sub htail
    exact tendsto_nhds_unique hexp_hasSum.tendsto_sum_nat hpart
  · intro ε
    exact tsum_of_norm_bounded hgeom fun m => hg_norm m ε

/-- **Dual Rademacher factorization for self-adjoint families**: for any finite family `x : ι → A`
of self-adjoint elements in a non-unital C⋆-algebra, there exists a self-adjoint family
`Φ : (ι → ℤˣ) → A` such that `𝔼 ε, ε i • Φ ε = x i` for all `i` and
`‖Φ ε‖ ≤ √3 * √‖∑ i, x i * x i‖` for all `ε`. -/
theorem exists_isSelfAdjoint_expect_units_smul_eq_and_norm_le
    {x : ι → A} (hx : ∀ i, IsSelfAdjoint (x i)) :
    ∃ Φ : (ι → ℤˣ) → A,
      (∀ ε, IsSelfAdjoint (Φ ε)) ∧
      (∀ i, 𝔼 ε : ι → ℤˣ, ε i • Φ ε = x i) ∧
      ∀ ε, ‖Φ ε‖ ≤ Real.sqrt 3 * √‖∑ i, x i * x i‖ := by
  set s : ℝ := √‖∑ i, x i * x i‖
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hcol_eq : (∑ i, star (x i) * x i) = ∑ i, x i * x i :=
    Finset.sum_congr rfl fun i _ => by rw [(hx i).star_eq]
  by_cases hs : s = 0
  · refine ⟨0, fun _ => IsSelfAdjoint.zero _, fun i => ?_, fun _ => by simp [hs]⟩
    have hx_zero : x i = 0 := by
      have hle : ‖x i‖ ≤ 0 := by
        calc ‖x i‖ ≤ ‖columnSquare x‖ := norm_apply_le_norm_columnSquare x i
          _ = s := by rw [norm_columnSquare, hcol_eq]
          _ = 0 := hs
      exact norm_le_zero_iff.mp hle
    simp [hx_zero]
  · let y : ι → A := fun i => s⁻¹ • x i
    have hy_sa (i : ι) : IsSelfAdjoint (y i) := by
      dsimp only [y]
      rw [IsSelfAdjoint, star_smul, star_trivial, (hx i).star_eq]
    have hy_norm : ‖∑ i, y i * y i‖ ≤ 1 := by
      have hsum : (∑ i, y i * y i) = (s⁻¹ ^ 2) • ∑ i, x i * x i := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        dsimp only [y]
        rw [sq, smul_mul_assoc, mul_smul_comm, smul_smul]
      rw [hsum, norm_smul, Real.norm_of_nonneg (by positivity),
        ← Real.sq_sqrt (norm_nonneg (∑ i, x i * x i)), inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hs)]
    obtain ⟨Ψ, hΨ_sa, hΨ_exp, hΨ_norm⟩ :=
      exists_isSelfAdjoint_expect_units_smul_eq_of_norm_le_one hy_sa hy_norm
    refine ⟨fun ε => s • Ψ ε,
      fun ε => by rw [IsSelfAdjoint, star_smul, star_trivial, (hΨ_sa ε).star_eq],
      fun i => ?_,
      fun ε => ?_⟩
    · have hpt (ε : ι → ℤˣ) : ε i • (s • Ψ ε) = s • (ε i • Ψ ε) := by
        rw [units_smul_eq_real_smul, smul_smul, mul_comm, ← smul_smul, ← units_smul_eq_real_smul]
      simp_rw [hpt, ← real_smul_expect_units, hΨ_exp i]
      exact smul_inv_smul₀ hs (x i)
    · rw [norm_smul, Real.norm_of_nonneg hs_nonneg, mul_comm]
      exact mul_le_mul_of_nonneg_right (hΨ_norm ε) hs_nonneg

omit [Fintype ι] [DecidableEq ι] [PartialOrder A] [StarOrderedRing A] [Module ℚ≥0 A] in
private theorem norm_pair_eq_max_swap (a b : A) : ‖![a, b]‖ = max ‖b‖ ‖a‖ := by
  refine le_antisymm ?_
    (max_le (norm_le_pi_norm ![a, b] 1) (norm_le_pi_norm ![a, b] 0))
  rw [pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))]
  intro k
  fin_cases k
  · exact le_max_right _ _
  · exact le_max_left _ _

/-- **Dual Rademacher factorization in a non-unital C⋆-algebra** (Haagerup–Pisier): for any finite
family `x : ι → A` in a non-unital C⋆-algebra, there exists `Φ : (ι → ℤˣ) → A` such that
`𝔼 ε, ε i • Φ ε = x i` for all `i` and
`‖Φ ε‖ ≤ √3 * max ‖columnSquare x‖ ‖rowSquare x‖` for all `ε`. -/
theorem exists_expect_units_smul_eq_and_norm_le (x : ι → A) :
    ∃ Φ : (ι → ℤˣ) → A,
      (∀ i, 𝔼 ε : ι → ℤˣ, ε i • Φ ε = x i) ∧
      ∀ ε, ‖Φ ε‖ ≤ Real.sqrt 3 * max ‖columnSquare x‖ ‖rowSquare x‖ := by
  let X : ι → CStarMatrix (Fin 2) (Fin 2) A :=
    fun i => CStarMatrix.ofMatrix !![0, x i; star (x i), 0]
  have hX_sa (i : ι) : IsSelfAdjoint (X i) := by
    refine CStarMatrix.ext fun p q => ?_
    fin_cases p <;> fin_cases q <;> simp [X, CStarMatrix.star_apply]
  have hX_sq (i : ι) :
      X i * X i = CStarMatrix.ofMatrix (Matrix.diagonal ![x i * star (x i), star (x i) * x i]) := by
    refine CStarMatrix.ext fun p q => ?_
    fin_cases p <;> fin_cases q <;>
      simp [X, CStarMatrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]
  have hX_sum_sq :
      (∑ i, X i * X i) =
        CStarMatrix.ofMatrix
          (Matrix.diagonal ![∑ i, x i * star (x i), ∑ i, star (x i) * x i]) := by
    have hsum_apply (f : ι → CStarMatrix (Fin 2) (Fin 2) A) (p q : Fin 2) :
        (∑ i, f i) p q = ∑ i, f i p q :=
      map_sum (AddMonoidHom.mk' (fun M : CStarMatrix (Fin 2) (Fin 2) A => M p q)
        fun _ _ => rfl) f Finset.univ
    refine CStarMatrix.ext fun p q => ?_
    rw [hsum_apply]
    simp_rw [hX_sq]
    fin_cases p <;> fin_cases q <;> simp [Matrix.diagonal]
  have hX_norm :
      √‖∑ i, X i * X i‖ = max ‖columnSquare x‖ ‖rowSquare x‖ := by
    rw [hX_sum_sq, CStarMatrix.norm_ofMatrix_diagonal, norm_pair_eq_max_swap,
      Real.sqrt_monotone.map_max, ← norm_columnSquare, ← norm_rowSquare]
  obtain ⟨Ψ, _, hΨ_exp, hΨ_norm⟩ := exists_isSelfAdjoint_expect_units_smul_eq_and_norm_le hX_sa
  refine ⟨fun ε => Ψ ε 0 1, fun i => ?_, fun ε => ?_⟩
  · have hentry :
        (𝔼 ε : ι → ℤˣ, ε i • Ψ ε) 0 1 = 𝔼 ε : ι → ℤˣ, ε i • Ψ ε 0 1 :=
      map_expect
        ({ toFun := fun M : CStarMatrix (Fin 2) (Fin 2) A => M 0 1
           map_add' := fun _ _ => rfl
           map_smul' := fun _ _ => rfl } : CStarMatrix (Fin 2) (Fin 2) A →ₗ[ℚ≥0] A)
        (fun ε : ι → ℤˣ => ε i • Ψ ε) Finset.univ
    rw [← hentry, hΨ_exp i]
    simp [X]
  · calc ‖Ψ ε 0 1‖
        ≤ ‖Ψ ε‖ := CStarMatrix.norm_entry_le_norm
      _ ≤ Real.sqrt 3 * √‖∑ i, X i * X i‖ := hΨ_norm ε
      _ = Real.sqrt 3 * max ‖columnSquare x‖ ‖rowSquare x‖ := by rw [hX_norm]

end TruncationStep

end Factorization

end TauCeti
