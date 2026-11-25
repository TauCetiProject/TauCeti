/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
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

* `MvPowerSeries.norm_coeff_monomial_le_prod_pow`: the bound of a monomial.
* `MvPowerSeries.norm_coeff_mul_le_mul_prod_pow`: the bounds multiply under multiplication.
* `MvPowerSeries.norm_coeff_pow_le_pow_mul_prod_pow` and
  `MvPowerSeries.norm_coeff_prod_le_prod_mul_prod_pow`: the bounds of powers and finite products.
* `MvPowerSeries.norm_coeff_invOfUnit_le_mul_prod_pow`: the bound of an inverse.
-/

public section

namespace MvPowerSeries

open Finset

variable {σ R : Type*}

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
  rw [← mem_antidiagonal.mp hx, Finsupp.prod_add_index' (fun _ ↦ pow_zero _)
    fun _ _ _ ↦ pow_add _ _ _, mul_mul_mul_comm]
  exact norm_mul_le_of_le (hf x.1) (hg x.2)

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
    exact Finset.prod_nonneg fun i _ ↦ pow_nonneg (hs i) _

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
    exact Finset.prod_nonneg fun i _ ↦ pow_nonneg (hs i) _

/-- Raising a series to the `n`-th power raises its geometric coefficient bound `a` to `a ^ n`. -/
theorem norm_coeff_pow_le_pow_mul_prod_pow (hs : ∀ i, 0 ≤ s i) {f : MvPowerSeries σ R} {a : ℝ}
    (hf : ∀ t, ‖coeff t f‖ ≤ a * t.prod (s · ^ ·)) (n : ℕ) (t : σ →₀ ℕ) :
    ‖coeff t (f ^ n)‖ ≤ a ^ n * t.prod (s · ^ ·) := by
  induction n generalizing t with
  | zero => simpa using norm_coeff_one_le_prod_pow hs t
  | succ n ih => simpa only [pow_succ] using norm_coeff_mul_le_mul_prod_pow ih hf t

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
  have hprod (t : σ →₀ ℕ) : 0 ≤ t.prod (s · ^ ·) :=
    Finset.prod_nonneg fun i _ ↦ pow_nonneg (hs i) _
  induction t using WellFoundedLT.induction with | _ t ih => ?_
  rw [coeff_invOfUnit]
  split_ifs with ht
  · simp [ht]
  refine (norm_mul_le _ _).trans ?_
  rw [norm_neg]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hprod t) fun x hx ↦ ?_
  split_ifs with hlt
  · -- In the recursion `x.1 + x.2 = t` with `x.2 < t`, so `x.1 ≠ 0` and `ih` applies to `x.2`.
    have hx1 : x.1 ≠ 0 := by
      rintro h
      rw [← mem_antidiagonal.mp hx, h, zero_add] at hlt
      exact hlt.false
    rw [← mem_antidiagonal.mp hx, Finsupp.prod_add_index' (fun _ ↦ pow_zero _)
      fun _ _ _ ↦ pow_add _ _ _]
    calc ‖coeff x.1 φ * coeff x.2 (invOfUnit φ u)‖
        ≤ ‖coeff x.1 φ‖ * (‖(↑u⁻¹ : R)‖ * x.2.prod (s · ^ ·)) :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (ih x.2 hlt) (norm_nonneg _))
      _ = ‖(↑u⁻¹ : R)‖ * ‖coeff x.1 φ‖ * x.2.prod (s · ^ ·) := by ring
      _ ≤ x.1.prod (s · ^ ·) * x.2.prod (s · ^ ·) :=
          mul_le_mul_of_nonneg_right (hφ x.1 hx1) (hprod _)
  · rw [norm_zero]
    exact hprod t

end Inverse

end MvPowerSeries
