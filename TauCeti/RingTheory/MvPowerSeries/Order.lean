/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Lowest-degree homogeneous components of powers, products and substitutions

If a series has order at least `p`, the degree-`n * p` homogeneous component of its `n`-th power
is the `n`-th power of its degree-`p` component, and similarly for finite products. This reduces
lowest-degree coefficient computations for powers to homogeneous series, over arbitrary semirings.

The same holds for substitution: if `f` has order at least `p` and the series `a i` have zero
constant coefficient, the degree-`p` component of `f(a)` only depends on the degree-`p` component
of `f` and on the linear parts of the `a i`, into which it is substituted
(`MvPowerSeries.homogeneousComponent_subst_of_le_order`). This is how the lowest-degree term of an
expression such as `f(F(X, Y), Z)`, for a formal group law `F(X, Y) = X + Y + ⋯`, is read off as
the polynomial `f_p(X + Y, Z)`.

For two-variable series with linear coefficients one, the degree-one component is `X + Y`.
Over a ring, vanishing of the constant coefficient then puts the remainder after subtracting
`X + Y` in order at least two, and over a commutative ring the linear part of `f(x, y)` is the
sum of the linear parts of `x` and `y` (`MvPowerSeries.homogeneousComponent_one_subst_pair`).
-/

public section

namespace MvPowerSeries

section Powers

variable {σ R : Type*} [Semiring R] {f : MvPowerSeries σ R}

/-- A variable is its own degree-one homogeneous component. -/
@[simp]
theorem homogeneousComponent_one_X (i : σ) :
    homogeneousComponent 1 (X i : MvPowerSeries σ R) = X i := by
  classical
  ext d
  rw [coeff_homogeneousComponent, coeff_X]
  split_ifs with h₁ h₂ h₂ <;> simp_all

/-- A homogeneous component of positive degree has no constant coefficient. -/
@[simp]
theorem constantCoeff_homogeneousComponent {p : ℕ} (hp : p ≠ 0) (f : MvPowerSeries σ R) :
    constantCoeff (homogeneousComponent p f) = 0 := by
  simp [← coeff_zero_eq_constantCoeff_apply, coeff_homogeneousComponent, hp.symm]

/-- A series of order at least `n` without degree-`n` component has order at least `n + 1`. -/
theorem succ_le_order_of_homogeneousComponent_eq_zero {n : ℕ} (hn : n ≤ f.order)
    (h : homogeneousComponent n f = 0) : ((n + 1 : ℕ) : ℕ∞) ≤ f.order := by
  refine nat_le_order fun d hd ↦ ?_
  rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd | hd
  · exact coeff_of_lt_order ((Nat.cast_lt.mpr hd).trans_le hn)
  · simpa [coeff_homogeneousComponent, hd] using congrArg (coeff d) h

/-- The lowest possible homogeneous component of a power is the corresponding power of the
lowest possible homogeneous component. -/
theorem homogeneousComponent_pow_of_le_order {p : ℕ} (hf : p ≤ f.order) (n : ℕ) :
    homogeneousComponent (n * p) (f ^ n) = (homogeneousComponent p f) ^ n := by
  classical
  induction n with
  | zero =>
    ext d
    by_cases hd : d = 0 <;>
      simp [coeff_homogeneousComponent, coeff_one, Finsupp.degree_eq_zero_iff, hd]
  | succ n ih =>
    have hn : (n * p : ℕ) ≤ (f ^ n).order := by
      simpa only [nsmul_eq_mul, Nat.cast_mul] using
        (nsmul_le_nsmul_right hf n).trans (le_order_pow n)
    rw [pow_succ, Nat.succ_mul, homogeneousComponent_mul_of_le_order hn hf, ih, pow_succ]

/-- For a series without constant coefficient, the degree-`n` component of its `n`-th power is the
`n`-th power of its linear part. -/
theorem homogeneousComponent_pow_of_constantCoeff_eq_zero (hf : constantCoeff f = 0) (n : ℕ) :
    homogeneousComponent n (f ^ n) = homogeneousComponent 1 f ^ n := by
  simpa using homogeneousComponent_pow_of_le_order (p := 1)
    (by simpa using one_le_order_iff_constCoeff_eq_zero.mpr hf) n

end Powers

section Products

variable {σ R : Type*} [CommSemiring R]

/-- The lowest possible homogeneous component of a finite product is the product of the lowest
possible homogeneous components of the factors. -/
theorem homogeneousComponent_prod_of_le_order {ι : Type*} (s : Finset ι)
    {f : ι → MvPowerSeries σ R} {p : ι → ℕ} (hf : ∀ i ∈ s, p i ≤ (f i).order) :
    homogeneousComponent (∑ i ∈ s, p i) (∏ i ∈ s, f i) =
      ∏ i ∈ s, homogeneousComponent (p i) (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext d
    by_cases hd : d = 0 <;>
      simp [coeff_homogeneousComponent, coeff_one, Finsupp.degree_eq_zero_iff, hd]
  | insert a s ha ih =>
    have hs : ((∑ i ∈ s, p i : ℕ) : ℕ∞) ≤ (∏ i ∈ s, f i).order := by
      push_cast
      exact (Finset.sum_le_sum fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)).trans
        (le_order_prod f s)
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.prod_insert ha,
      homogeneousComponent_mul_of_le_order (hf a (Finset.mem_insert_self a s)) hs,
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

/-- The monomial `aᵈ = ∏ᵢ (a i) ^ (d i)` in series without constant coefficient has order at least
the degree of `d`. -/
theorem degree_le_order_prod_pow {ι : Type*} {a : ι → MvPowerSeries σ R}
    (ha₀ : ∀ i, constantCoeff (a i) = 0) (d : ι →₀ ℕ) :
    (d.degree : ℕ∞) ≤ (d.prod fun i k ↦ a i ^ k).order := by
  rw [Finsupp.prod, Finsupp.degree_apply]
  push_cast
  refine (Finset.sum_le_sum fun i _ ↦ ?_).trans (le_order_prod _ _)
  simpa using le_order_pow_of_constantCoeff_eq_zero (d i) (ha₀ i)

/-- The degree-`|d|` component of the monomial `aᵈ = ∏ᵢ (a i) ^ (d i)` in series without constant
coefficient is the same monomial in their linear parts. -/
theorem homogeneousComponent_degree_prod_pow {ι : Type*} {a : ι → MvPowerSeries σ R}
    (ha₀ : ∀ i, constantCoeff (a i) = 0) (d : ι →₀ ℕ) :
    homogeneousComponent d.degree (d.prod fun i k ↦ a i ^ k) =
      d.prod fun i k ↦ homogeneousComponent 1 (a i) ^ k := by
  rw [Finsupp.prod, Finsupp.prod, Finsupp.degree_apply,
    homogeneousComponent_prod_of_le_order _ fun i _ ↦ ?_]
  · exact Finset.prod_congr rfl fun i _ ↦
      homogeneousComponent_pow_of_constantCoeff_eq_zero (ha₀ i) _
  · simpa using le_order_pow_of_constantCoeff_eq_zero (d i) (ha₀ i)

end Products

section Subst

variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The linear parts of a substitutable family can be substituted. -/
theorem HasSubst.homogeneousComponent_one {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
    HasSubst fun i ↦ homogeneousComponent 1 (a i) where
  const_coeff s := by simp
  coeff_zero d := (ha.coeff_zero d).subset fun s hs ↦ by
    simp only [Set.mem_ofPred_eq, coeff_homogeneousComponent] at hs ⊢
    split_ifs at hs
    exacts [hs, (hs rfl).elim]

/-- **The lowest-degree component of a substitution.** If `f` has order at least `p` and the series
`a i` have zero constant coefficient, the degree-`p` component of `f(a)` is the degree-`p` component
of `f` evaluated at the linear parts of the `a i`. -/
theorem homogeneousComponent_subst_of_le_order {f : MvPowerSeries σ R} {p : ℕ}
    (hf : p ≤ f.order) {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (ha₀ : ∀ i, constantCoeff (a i) = 0) :
    homogeneousComponent p (f.subst a) =
      (homogeneousComponent p f).subst fun i ↦ homogeneousComponent 1 (a i) := by
  ext e
  rw [coeff_homogeneousComponent, coeff_subst ha, coeff_subst ha.homogeneousComponent_one]
  split_ifs with he
  · refine finsum_congr fun d ↦ ?_
    rw [coeff_homogeneousComponent]
    split_ifs with hd
    · rw [← homogeneousComponent_degree_prod_pow ha₀, coeff_homogeneousComponent,
        ite_eq_left (he.trans hd.symm)]
    · rcases lt_or_gt_of_ne hd with hlt | hgt
      · rw [coeff_of_lt_order ((Nat.cast_lt.mpr hlt).trans_le hf), zero_smul, zero_smul]
      · rw [coeff_of_lt_order ((Nat.cast_lt.mpr (he.trans_lt hgt)).trans_le
          (degree_le_order_prod_pow ha₀ d)), smul_zero, zero_smul]
  · refine (finsum_eq_zero_of_forall_eq_zero fun d ↦ ?_).symm
    rw [coeff_homogeneousComponent]
    split_ifs with hd
    · rw [← homogeneousComponent_degree_prod_pow ha₀, coeff_homogeneousComponent,
        ite_eq_right (hd ▸ he), smul_zero]
    · rw [zero_smul]

end Subst

open Finsupp

variable {R : Type*} {f : MvPowerSeries (Fin 2) R}

/-- A series whose two linear coefficients are one has degree-one homogeneous component
`X + Y`, independently of its constant coefficient. -/
theorem homogeneousComponent_one_eq_X_add_X [Semiring R]
    (hX : coeff (single 0 1) f = 1) (hY : coeff (single 1 1) f = 1) :
    homogeneousComponent 1 f = X 0 + X 1 := by
  ext d
  rw [coeff_homogeneousComponent]
  by_cases hdeg : d.degree = 1
  · obtain ⟨j, rfl⟩ := (Set.ext_iff.mp range_single_one d).mpr hdeg
    fin_cases j <;> simp [hX, hY, coeff_X, single_eq_single_iff]
  · have hX' : d ≠ single 0 1 := fun h ↦ hdeg (by simp [h])
    have hY' : d ≠ single 1 1 := fun h ↦ hdeg (by simp [h])
    simp [hdeg, coeff_X, hX', hY']

section Ring

variable [Ring R]

/-- A power series in two variables with zero constant coefficient and linear part `X + Y` differs
from `X + Y` by a series of order at least two. -/
theorem two_le_order_sub_X_add_X (h₀ : f.constantCoeff = 0)
    (hX : coeff (single 0 1) f = 1) (hY : coeff (single 1 1) f = 1) :
    2 ≤ (f - (X 0 + X 1)).order := by
  refine nat_le_order (n := 2) fun d hd => ?_
  have hdeg : d.degree = 0 ∨ d.degree = 1 := by omega
  rcases hdeg with hdeg | hdeg
  · simp [(degree_eq_zero_iff d).mp hdeg, h₀]
  · have hc := congrArg (coeff d) (homogeneousComponent_one_eq_X_add_X hX hY)
    simp only [coeff_homogeneousComponent, ite_eq_left hdeg] at hc
    simp [hc]

end Ring

section CommRing

variable {τ S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- If `f` has zero constant coefficient and linear part `X + Y`, the linear part of `f(x, y)` is
the sum of the linear parts of `x` and `y`, for `x` and `y` without constant coefficient. -/
theorem homogeneousComponent_one_subst_pair (h₀ : f.constantCoeff = 0)
    (hX : coeff (single 0 1) f = 1) (hY : coeff (single 1 1) f = 1) {x y : MvPowerSeries τ S}
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    homogeneousComponent 1 (f.subst ![x, y]) =
      homogeneousComponent 1 x + homogeneousComponent 1 y := by
  have hxy : HasSubst ![x, y] := hasSubst_of_constantCoeff_zero fun i ↦ by
    fin_cases i <;> simp [hx, hy]
  have hl := hxy.homogeneousComponent_one
  rw [homogeneousComponent_subst_of_le_order
      (by simpa using one_le_order_iff_constCoeff_eq_zero.mpr h₀) hxy
      (fun i ↦ by fin_cases i <;> simp [hx, hy]),
    homogeneousComponent_one_eq_X_add_X hX hY, subst_add hl, subst_X hl, subst_X hl]
  simp

end CommRing

end MvPowerSeries
