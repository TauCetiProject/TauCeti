/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Data.Finsupp.WellFounded

/-!
# Geometric coefficient bounds for multivariate power series

Over an ultrametric seminormed ring, fix nonnegative rates `s : σ → ℝ` and consider power series
whose coefficients decay geometrically at these rates,

```text
‖coeff t f‖ ≤ a * ∏ i, s i ^ t i      for every exponent t.
```

For positive rates this says that the Gauss norm of `f` at the polyradii `s⁻¹` is at most `a`; the
rates may also vanish, which no Gauss norm at a finite radius expresses. Such bounds are
submultiplicative: each coefficient of a product is a finite sum of products of coefficients, and
the ultrametric inequality bounds it by its largest term. The same recursion bounds the inverse of
a series whose constant coefficient is a unit `u`: if `‖u⁻¹‖ ‖coeff t φ‖ ≤ ∏ i, s i ^ t i` for
every `t ≠ 0`, then the coefficients of the inverse `invOfUnit φ u` are bounded by
`‖u⁻¹‖ ∏ i, s i ^ t i`.

These bounds control the matrix coefficients of substitution operators on Tate algebras, such as
the slash operators of Möbius transformations acting on the coefficient modules of `p`-adic
families of automorphic forms.

## Main results

* `MvPowerSeries.prod_pow_nonneg`: the rate `∏ i, s i ^ t i` is nonnegative.
* `MvPowerSeries.prod_pow_add`: the rate is multiplicative in the exponent.
* `MvPowerSeries.prod_pow_single`: the rate of the exponent `single i n` is `s i ^ n`.
* `MvPowerSeries.norm_coeff_monomial_le_prod_pow`: the bound of a monomial.
* `MvPowerSeries.norm_coeff_mul_le_mul_prod_pow`: the bounds multiply under multiplication.
* `MvPowerSeries.norm_coeff_pow_le_pow_mul_prod_pow` and
  `MvPowerSeries.norm_coeff_prod_le_prod_mul_prod_pow`: the bounds of powers and finite products.
* `MvPowerSeries.norm_coeff_invOfUnit_le_mul_prod_pow`: the bound of an inverse.
* `MvPowerSeries.norm_coeff_mul_le_prod_pow`, `MvPowerSeries.norm_coeff_pow_le_prod_pow`,
  `MvPowerSeries.norm_coeff_prod_le_prod_pow` and `MvPowerSeries.norm_coeff_invOfUnit_le_prod_pow`:
  the same bounds for the unit bound `a = 1`.
* `MvPowerSeries.norm_coeff_mul_le_mul`, `MvPowerSeries.norm_coeff_pow_le_one`: uniform
  coefficient bounds multiply.
* `MvPowerSeries.norm_coeff_X_le_one` and `MvPowerSeries.norm_coeff_pderiv_le`: the variables have
  coefficients in the closed unit ball, and a partial derivative keeps a uniform bound.
-/

public section

namespace MvPowerSeries

open Finset

variable {σ R : Type*}

/-- The geometric rate `∏ i, s i ^ t i` of nonnegative rates `s` is nonnegative. -/
theorem prod_pow_nonneg {s : σ → ℝ} (hs : ∀ i, 0 ≤ s i) (t : σ →₀ ℕ) :
    0 ≤ t.prod (s · ^ ·) := by
  rw [Finsupp.prod]
  exact Finset.prod_nonneg fun i _ ↦ pow_nonneg (hs i) _

/-- The weights of exponents are multiplicative. -/
theorem prod_pow_add {c : σ → ℝ} (s t : σ →₀ ℕ) :
    (s + t).prod (c · ^ ·) = s.prod (c · ^ ·) * t.prod (c · ^ ·) :=
  Finsupp.prod_add_index' (fun _ ↦ pow_zero _) fun _ _ _ ↦ pow_add _ _ _

/-- The rate of the exponent `single i n`, i.e. of the monomial `Xᵢ ^ n`, is `s i ^ n`. -/
theorem prod_pow_single {s : σ → ℝ} (i : σ) (n : ℕ) :
    (Finsupp.single i n).prod (s · ^ ·) = s i ^ n :=
  Finsupp.prod_single_index (pow_zero _)

section Ring

variable [SeminormedRing R] [IsUltrametricDist R] {s : σ → ℝ}

/-- **Geometric coefficient bounds are submultiplicative.** If the coefficients of `f` and `g`
are bounded by `a * ∏ i, s i ^ t i` and `b * ∏ i, s i ^ t i`, those of `f * g` are bounded by
`a * b * ∏ i, s i ^ t i`. -/
theorem norm_coeff_mul_le_mul_prod_pow {f g : MvPowerSeries σ R} {a b : ℝ}
    (hf : ∀ t, ‖coeff t f‖ ≤ a * t.prod (s · ^ ·)) (hg : ∀ t, ‖coeff t g‖ ≤ b * t.prod (s · ^ ·))
    (t : σ →₀ ℕ) : ‖coeff t (f * g)‖ ≤ a * b * t.prod (s · ^ ·) := by
  classical
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty ⟨(0, t), by simp⟩ fun x hx ↦ ?_
  rw [← mem_antidiagonal.mp hx, prod_pow_add, mul_mul_mul_comm]
  exact norm_mul_le_of_le (hf x.1) (hg x.2)

/-- The unit case of `MvPowerSeries.norm_coeff_mul_le_mul_prod_pow`: if the coefficients of `f`
and `g` are bounded by `∏ i, s i ^ t i`, so are those of `f * g`. -/
theorem norm_coeff_mul_le_prod_pow {f g : MvPowerSeries σ R}
    (hf : ∀ t, ‖coeff t f‖ ≤ t.prod (s · ^ ·)) (hg : ∀ t, ‖coeff t g‖ ≤ t.prod (s · ^ ·))
    (t : σ →₀ ℕ) : ‖coeff t (f * g)‖ ≤ t.prod (s · ^ ·) := by
  simpa only [one_mul] using norm_coeff_mul_le_mul_prod_pow (a := 1) (b := 1)
    (fun t ↦ (one_mul _).trans_ge (hf t)) (fun t ↦ (one_mul _).trans_ge (hg t)) t

/-- **Uniform coefficient bounds multiply.** If the coefficients of `f` and `g` have norm at most
`a` and `b`, those of `f * g` have norm at most `a * b`. -/
theorem norm_coeff_mul_le_mul {f g : MvPowerSeries σ R} {a b : ℝ} (hf : ∀ t, ‖coeff t f‖ ≤ a)
    (hg : ∀ t, ‖coeff t g‖ ≤ b) (t : σ →₀ ℕ) : ‖coeff t (f * g)‖ ≤ a * b := by
  simpa using norm_coeff_mul_le_mul_prod_pow (s := fun _ ↦ (1 : ℝ)) (fun t ↦ by simpa using hf t)
    (fun t ↦ by simpa using hg t) t

omit [IsUltrametricDist R] in
/-- A monomial `x Xᵉ` with `‖x‖ ≤ ∏ i, s i ^ e i` has the geometric coefficient bound
`∏ i, s i ^ t i`. -/
theorem norm_coeff_monomial_le_prod_pow (hs : ∀ i, 0 ≤ s i) {e : σ →₀ ℕ} {x : R}
    (hx : ‖x‖ ≤ e.prod (s · ^ ·)) (t : σ →₀ ℕ) :
    ‖coeff t (monomial e x)‖ ≤ t.prod (s · ^ ·) := by
  classical
  rw [coeff_monomial]
  split_ifs with ht
  · exact ht ▸ hx
  · rw [norm_zero]
    exact prod_pow_nonneg hs t

variable [NormOneClass R]

omit [IsUltrametricDist R] in
/-- The constant series `1` has the geometric coefficient bound `∏ i, s i ^ t i`. -/
theorem norm_coeff_one_le_prod_pow (hs : ∀ i, 0 ≤ s i) (t : σ →₀ ℕ) :
    ‖coeff t (1 : MvPowerSeries σ R)‖ ≤ t.prod (s · ^ ·) := by
  classical
  rw [coeff_one]
  split_ifs with ht
  · simp [ht]
  · rw [norm_zero]
    exact prod_pow_nonneg hs t

/-- Raising a series to the `n`-th power raises its geometric coefficient bound `a` to `a ^ n`. -/
theorem norm_coeff_pow_le_pow_mul_prod_pow (hs : ∀ i, 0 ≤ s i) {f : MvPowerSeries σ R} {a : ℝ}
    (hf : ∀ t, ‖coeff t f‖ ≤ a * t.prod (s · ^ ·)) (n : ℕ) (t : σ →₀ ℕ) :
    ‖coeff t (f ^ n)‖ ≤ a ^ n * t.prod (s · ^ ·) := by
  induction n generalizing t with
  | zero => simpa using norm_coeff_one_le_prod_pow hs t
  | succ n ih => simpa only [pow_succ] using norm_coeff_mul_le_mul_prod_pow ih hf t

/-- The unit case of `MvPowerSeries.norm_coeff_pow_le_pow_mul_prod_pow`: if the coefficients of
`f` are bounded by `∏ i, s i ^ t i`, so are those of `f ^ n`. -/
theorem norm_coeff_pow_le_prod_pow (hs : ∀ i, 0 ≤ s i) {f : MvPowerSeries σ R}
    (hf : ∀ t, ‖coeff t f‖ ≤ t.prod (s · ^ ·)) (n : ℕ) (t : σ →₀ ℕ) :
    ‖coeff t (f ^ n)‖ ≤ t.prod (s · ^ ·) := by
  simpa only [one_pow, one_mul] using norm_coeff_pow_le_pow_mul_prod_pow hs (a := 1)
    (fun t ↦ (one_mul _).trans_ge (hf t)) n t

/-- If the coefficients of `f` have norm at most `1`, so do those of `f ^ n`. -/
theorem norm_coeff_pow_le_one {f : MvPowerSeries σ R} (hf : ∀ t, ‖coeff t f‖ ≤ 1) (n : ℕ)
    (t : σ →₀ ℕ) : ‖coeff t (f ^ n)‖ ≤ 1 := by
  simpa using norm_coeff_pow_le_prod_pow (s := fun _ ↦ (1 : ℝ)) (fun _ ↦ zero_le_one)
    (fun t ↦ by simpa using hf t) n t

omit [IsUltrametricDist R] in
/-- The coefficients of a variable `X i` have norm at most `1`. -/
theorem norm_coeff_X_le_one (i : σ) (t : σ →₀ ℕ) : ‖coeff t (X i : MvPowerSeries σ R)‖ ≤ 1 := by
  classical
  rw [coeff_X]
  split_ifs <;> simp

end Ring

section CommRing

variable [SeminormedCommRing R] [IsUltrametricDist R] [NormOneClass R] {s : σ → ℝ}

/-- A finite product of series has the product of their geometric coefficient bounds as its
geometric coefficient bound. -/
theorem norm_coeff_prod_le_prod_mul_prod_pow {ι : Type*} (hs : ∀ i, 0 ≤ s i) (S : Finset ι)
    {f : ι → MvPowerSeries σ R} {a : ι → ℝ}
    (hf : ∀ j ∈ S, ∀ t, ‖coeff t (f j)‖ ≤ a j * t.prod (s · ^ ·)) (t : σ →₀ ℕ) :
    ‖coeff t (∏ j ∈ S, f j)‖ ≤ (∏ j ∈ S, a j) * t.prod (s · ^ ·) := by
  classical
  induction S using Finset.induction_on generalizing t with
  | empty => simpa using norm_coeff_one_le_prod_pow hs t
  | insert j S hj ih =>
    rw [prod_insert hj, prod_insert hj]
    exact norm_coeff_mul_le_mul_prod_pow (hf j (mem_insert_self j S))
      (ih fun j' hj' ↦ hf j' (mem_insert_of_mem hj')) t

/-- The unit case of `MvPowerSeries.norm_coeff_prod_le_prod_mul_prod_pow`: if the coefficients of
each `f j` are bounded by `∏ i, s i ^ t i`, so are those of `∏ j ∈ S, f j`. -/
theorem norm_coeff_prod_le_prod_pow {ι : Type*} (hs : ∀ i, 0 ≤ s i) (S : Finset ι)
    {f : ι → MvPowerSeries σ R} (hf : ∀ j ∈ S, ∀ t, ‖coeff t (f j)‖ ≤ t.prod (s · ^ ·))
    (t : σ →₀ ℕ) : ‖coeff t (∏ j ∈ S, f j)‖ ≤ t.prod (s · ^ ·) := by
  simpa only [prod_const_one, one_mul] using norm_coeff_prod_le_prod_mul_prod_pow hs S
    (a := fun _ ↦ 1) (fun j hj t ↦ (one_mul _).trans_ge (hf j hj t)) t

/-- **A partial derivative keeps a uniform coefficient bound**: its coefficients are coefficients
of `f` times natural numbers, which have norm at most `1` in an ultrametric ring. -/
theorem norm_coeff_pderiv_le {f : MvPowerSeries σ R} {a : ℝ} (hf : ∀ t, ‖coeff t f‖ ≤ a) (i : σ)
    (t : σ →₀ ℕ) : ‖coeff t (pderiv i f)‖ ≤ a := by
  rw [coeff_pderiv]
  refine (norm_mul_le_of_le (hf _) ?_).trans_eq (mul_one a)
  simpa using IsUltrametricDist.norm_natCast_le_one R (t i + 1)

end CommRing

section Inverse

variable [SeminormedRing R] [IsUltrametricDist R] {s : σ → ℝ}

/-- **Geometric coefficient bounds of an inverse.** Let `u` be a unit and let the nonconstant
coefficients of `φ` satisfy `‖u⁻¹‖ ‖coeff t φ‖ ≤ ∏ i, s i ^ t i`. Then every coefficient of
`invOfUnit φ u`, which is the inverse of `φ` when `u` is its constant coefficient
(`MvPowerSeries.mul_invOfUnit`), is bounded by `‖u⁻¹‖ ∏ i, s i ^ t i`. -/
theorem norm_coeff_invOfUnit_le_mul_prod_pow (hs : ∀ i, 0 ≤ s i) {φ : MvPowerSeries σ R}
    {u : Rˣ} (hφ : ∀ t ≠ 0, ‖(↑u⁻¹ : R)‖ * ‖coeff t φ‖ ≤ t.prod (s · ^ ·)) (t : σ →₀ ℕ) :
    ‖coeff t (invOfUnit φ u)‖ ≤ ‖(↑u⁻¹ : R)‖ * t.prod (s · ^ ·) := by
  classical
  induction t using WellFoundedLT.induction with | _ t ih => ?_
  rw [coeff_invOfUnit]
  split_ifs with ht
  · simp [ht]
  refine (norm_mul_le _ _).trans ?_
  rw [norm_neg]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (prod_pow_nonneg hs t) fun x hx ↦ ?_
  split_ifs with hlt
  · -- In the recursion `x.1 + x.2 = t` with `x.2 < t`, so `x.1 ≠ 0` and `ih` applies to `x.2`.
    have hx1 : x.1 ≠ 0 := by
      rintro h
      rw [← mem_antidiagonal.mp hx, h, zero_add] at hlt
      exact hlt.false
    rw [← mem_antidiagonal.mp hx, prod_pow_add]
    calc ‖coeff x.1 φ * coeff x.2 (invOfUnit φ u)‖
        ≤ ‖coeff x.1 φ‖ * (‖(↑u⁻¹ : R)‖ * x.2.prod (s · ^ ·)) :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (ih x.2 hlt) (norm_nonneg _))
      _ = ‖(↑u⁻¹ : R)‖ * ‖coeff x.1 φ‖ * x.2.prod (s · ^ ·) := by ring
      _ ≤ x.1.prod (s · ^ ·) * x.2.prod (s · ^ ·) :=
          mul_le_mul_of_nonneg_right (hφ x.1 hx1) (prod_pow_nonneg hs _)
  · rw [norm_zero]
    exact prod_pow_nonneg hs t

/-- The unit case of `MvPowerSeries.norm_coeff_invOfUnit_le_mul_prod_pow`: if `‖u⁻¹‖ ≤ 1` and the
nonconstant coefficients of `φ` are bounded by `∏ i, s i ^ t i`, so are all coefficients of
`invOfUnit φ u`. -/
theorem norm_coeff_invOfUnit_le_prod_pow (hs : ∀ i, 0 ≤ s i) {φ : MvPowerSeries σ R} {u : Rˣ}
    (hu : ‖(↑u⁻¹ : R)‖ ≤ 1) (hφ : ∀ t ≠ 0, ‖coeff t φ‖ ≤ t.prod (s · ^ ·)) (t : σ →₀ ℕ) :
    ‖coeff t (invOfUnit φ u)‖ ≤ t.prod (s · ^ ·) :=
  (norm_coeff_invOfUnit_le_mul_prod_pow hs
    (fun t ht ↦ (mul_le_of_le_one_left (norm_nonneg _) hu).trans (hφ t ht)) t).trans
    (mul_le_of_le_one_left (prod_pow_nonneg hs t) hu)

end Inverse

end MvPowerSeries
