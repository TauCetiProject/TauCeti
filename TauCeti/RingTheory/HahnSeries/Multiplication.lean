/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication

/-!
# Powers of Hahn series and compatibility with coefficient scalars

Over a reduced semiring, taking a power raises the leading coefficient to that power. Over a
reduced semiring that is also nontrivial, taking a power multiplies `orderTop`. Here `orderTop`
takes the value `⊤` on the zero series, so the `orderTop` formula holds for the zero series too.
Nontriviality is needed for the zeroth power: over the trivial semiring `1 = 0`, so the series
`1` has `orderTop` equal to `⊤` rather than `0`. These formulas detect whether a leading pole term
can be cancelled by a power.

The `orderTop` formula allows semiring coefficients; Mathlib's `HahnSeries.addVal` requires
coefficients in a domain that is a ring, so its `AddValuation.map_pow` does not cover this
generality.

The formulas are `HahnSeries.leadingCoeff_pow` and `HahnSeries.orderTop_pow`, both
simplification lemmas, companions of Mathlib's `HahnSeries.order_pow`. Mathlib's
`HahnSeries.order_pow`, `HahnSeries.leadingCoeff_mul` and `HahnSeries.orderTop_mul` assume no zero
divisors; for powers it suffices that the coefficients are reduced, and, for `orderTop`, that
they form a nontrivial semiring. Over a commutative semiring without zero divisors, the leading
coefficient of a finite product is the product of the leading coefficients
(`HahnSeries.leadingCoeff_prod`).

This file also records that coefficientwise scalar multiplication associates and commutes with
multiplication of Hahn series (`TauCeti.hahnSeries_isScalarTower` and
`TauCeti.hahnSeries_smulCommClass`), for any scalars acting on the coefficients compatibly with
their multiplication, following Mathlib's `MonoidAlgebra.isScalarTower_self` and
`MonoidAlgebra.smulCommClass_self`. Mathlib provides this for the action of Hahn series on Hahn
modules, and for commutative scalars through the algebra structure; but the default algebra
structure on Laurent series `R⸨X⸩` comes from `R⟦X⟧` and is not definitionally the
coefficientwise one. For instance, the `R⸨X⸩`-module structure on `R`-derivations of `R⸨X⸩`
needs `TauCeti.hahnSeries_smulCommClass` for the coefficientwise action of `R`, while
`TauCeti.hahnSeries_isScalarTower` moves that action across products:
`r • (x * y) = (r • x) * y`.

Finally, `HahnModule.of_symm_smul'` reads the coefficientwise action of `R` on `HahnModule Γ R V`
through `HahnModule.of`, for the action instance underlying the `R`-module structure.
`HahnModule.ofLinearEquiv` bundles this coefficient-preserving comparison as an `R`-linear
equivalence. The lemmas `HahnModule.coeff_smul_single_zero` and
`HahnModule.single_smul_single_zero` describe the convolution action of a scalar series on a
constant module-valued series, coefficientwise and on monomials, and
`HahnModule.single_neg_smul_single_smul` records that the monomials `t ^ a` and `t ^ (-a)` act
inversely.

`HahnSeries.coeff_mul_add_of_forall_le` computes the coefficient of a product at the sum of lower
bounds for the supports of the factors: it is the product of the coefficients at those bounds.
The sum of the lower bounds bounds the support of the product
(`HahnSeries.add_le_of_mem_support_mul`), and for powers `HahnSeries.nsmul_le_of_mem_support_pow`
and `HahnSeries.coeff_pow_nsmul_of_forall_le` give the corresponding bound and coefficient.
`HahnSeries.zero_le_orderTop_single` and `HahnSeries.zero_le_orderTop_one` record that monomials
of nonnegative exponent, and in particular the constant `1`, have nonnegative order.
`HahnSeries.commute_C_iff` characterizes when a Hahn series commutes with a constant series `C c`:
each coefficient commutes with `c`.
-/

public section

namespace TauCeti

section Scalar

variable {Γ R S : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [NonUnitalNonAssocSemiring R] [DistribSMul S R]

/-- Coefficientwise scalar multiplication associates with multiplication of Hahn series. -/
instance hahnSeries_isScalarTower [IsScalarTower S R R] :
    IsScalarTower S (HahnSeries Γ R) (HahnSeries Γ R) where
  smul_assoc s x y := by
    ext a
    rw [smul_eq_mul, smul_eq_mul,
      HahnSeries.coeff_mul_left' x.isPWO_support (HahnSeries.support_smul_subset s x)]
    simp only [HahnSeries.coeff_smul, HahnSeries.coeff_mul, Finset.smul_sum, smul_mul_assoc]

/-- Coefficientwise scalar multiplication commutes with multiplication of Hahn series. -/
instance hahnSeries_smulCommClass [SMulCommClass S R R] :
    SMulCommClass S (HahnSeries Γ R) (HahnSeries Γ R) where
  smul_comm s x y := by
    ext a
    rw [smul_eq_mul, smul_eq_mul,
      HahnSeries.coeff_mul_right' y.isPWO_support (HahnSeries.support_smul_subset s y)]
    simp only [HahnSeries.coeff_smul, HahnSeries.coeff_mul, Finset.smul_sum, mul_smul_comm]

end Scalar

end TauCeti

namespace HahnSeries

variable {Γ R : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [Semiring R] [IsReduced R]

/-- Over a reduced semiring, the leading coefficient of a power is the power of the leading
coefficient. -/
@[simp]
theorem leadingCoeff_pow (x : HahnSeries Γ R) (n : ℕ) :
    (x ^ n).leadingCoeff = x.leadingCoeff ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hx : x = 0
    · simp [hx]
    have h : x.leadingCoeff ^ (n + 1) ≠ 0 := pow_ne_zero _ (leadingCoeff_ne_zero.mpr hx)
    rw [pow_succ, leadingCoeff_mul_of_ne_zero (by rwa [ih, ← pow_succ]), ih, pow_succ]

/-- Over a nontrivial reduced semiring, `orderTop` of a power is the corresponding multiple of
`orderTop`. This includes the zero series, whose `orderTop` is `⊤`. -/
@[simp]
theorem orderTop_pow [Nontrivial R] (x : HahnSeries Γ R) (n : ℕ) :
    (x ^ n).orderTop = n • x.orderTop := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hx : x = 0
    · simp [hx, succ_nsmul]
    have h : x.leadingCoeff ^ (n + 1) ≠ 0 := pow_ne_zero _ (leadingCoeff_ne_zero.mpr hx)
    rw [pow_succ, orderTop_mul_of_ne_zero (by rwa [leadingCoeff_pow, ← pow_succ]), ih,
      succ_nsmul]

/-- Over a commutative semiring without zero divisors, the leading coefficient of a finite
product is the product of the leading coefficients. -/
@[simp]
theorem leadingCoeff_prod {R ι : Type*} [CommSemiring R] [NoZeroDivisors R] (s : Finset ι)
    (f : ι → HahnSeries Γ R) :
    (∏ i ∈ s, f i).leadingCoeff = ∏ i ∈ s, (f i).leadingCoeff := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, leadingCoeff_mul, ih]

end HahnSeries

namespace HahnModule

/-- The coefficientwise scalar action underlying the `R`-module structure, read through `of`.
Mathlib's `HahnModule.of_symm_smul` is stated for a different, though propositionally equal,
scalar action instance, so it does not rewrite this one. -/
@[simp]
theorem of_symm_smul' {Γ R V : Type*} [PartialOrder Γ] [Monoid R] [AddMonoid V]
    [DistribMulAction R V] (r : R) (x : HahnModule Γ R V) :
    (of R).symm (r • x) = r • (of R).symm x :=
  rfl

/-- The coefficient-preserving comparison between Hahn series and Hahn modules, linear for the
coefficientwise action of `R`. -/
noncomputable def ofLinearEquiv (R : Type*) {Γ V : Type*} [PartialOrder Γ] [Semiring R]
    [AddCommMonoid V] [Module R V] : HahnSeries Γ V ≃ₗ[R] HahnModule Γ R V where
  __ := of R
  map_add' := of_add
  map_smul' r f := (of R).symm.injective <| by simp

@[simp]
theorem ofLinearEquiv_apply {Γ R V : Type*} [PartialOrder Γ] [Semiring R] [AddCommMonoid V]
    [Module R V] (f : HahnSeries Γ V) : ofLinearEquiv R f = of R f := (rfl)

@[simp]
theorem ofLinearEquiv_symm_apply {Γ R V : Type*} [PartialOrder Γ] [Semiring R] [AddCommMonoid V]
    [Module R V] (f : HahnModule Γ R V) : (ofLinearEquiv R).symm f = (of R).symm f := (rfl)

open HahnSeries

variable {Γ R V : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
  [IsOrderedCancelAddMonoid Γ]

/-- Multiplying a constant module-valued series by a scalar series multiplies each coefficient
by the constant vector. -/
@[simp]
theorem coeff_smul_single_zero [Zero R] [AddCommMonoid V] [SMulWithZero R V]
    (f : HahnSeries Γ R) (v : V) (g : Γ) :
    ((of R).symm (f • of R (single 0 v))).coeff g = f.coeff g • v := by
  classical
  rw [coeff_smul_right (Set.isPWO_singleton 0) (by simpa using support_single_subset),
    Finset.sum_eq_single (g, 0)]
  · simp
  · rintro ⟨i, j⟩ hij hne
    simp only [Finset.mem_vaddAntidiagonal, Set.mem_singleton_iff, vadd_eq_add] at hij
    obtain ⟨-, rfl, rfl⟩ := hij
    simp at hne
  · intro h
    have hg : f.coeff g = 0 := by simpa [Finset.mem_vaddAntidiagonal] using h
    simp [hg]

/-- Multiplying by the monomials `t ^ a` and then `t ^ (-a)` is the identity. -/
@[simp]
theorem single_neg_smul_single_smul {Γ : Type*} [AddCommGroup Γ] [PartialOrder Γ]
    [IsOrderedAddMonoid Γ] [Semiring R] [AddCommMonoid V] [Module R V] (a : Γ)
    (x : HahnModule Γ R V) : single (-a) (1 : R) • single a (1 : R) • x = x := by
  rw [← mul_smul, single_mul_single, neg_add_cancel, one_mul, single_zero_one, one_smul]

/-- A scalar monomial times a constant vector series is a vector-valued monomial. -/
@[simp]
theorem single_smul_single_zero [Zero R] [AddCommMonoid V] [SMulWithZero R V]
    (g : Γ) (r : R) (v : V) :
    single g r • of R (single 0 v) = of R (single g (r • v)) := by
  apply HahnModule.ext
  funext h
  by_cases hh : h = g <;> simp [hh]

end HahnModule

namespace HahnSeries

section OrderTop

variable {Γ R : Type*} [Zero Γ] [PartialOrder Γ] [Zero R]

/-- A monomial of nonnegative exponent has nonnegative order. -/
theorem zero_le_orderTop_single {a : Γ} (ha : 0 ≤ a) (r : R) : 0 ≤ (single a r).orderTop :=
  (WithTop.coe_le_coe.2 ha).trans orderTop_single_le

/-- The constant `1` has nonnegative order. -/
theorem zero_le_orderTop_one [One R] : 0 ≤ (1 : HahnSeries Γ R).orderTop :=
  zero_le_orderTop_single le_rfl 1

end OrderTop

variable {Γ R : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]

/-- If `x` is supported at exponents at least `a` and `y` at exponents at least `b`, then the
coefficient of `x * y` at `a + b` is the product of the coefficients at `a` and `b`. -/
theorem coeff_mul_add_of_forall_le [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R}
    {a b : Γ} (hx : ∀ i ∈ x.support, a ≤ i) (hy : ∀ j ∈ y.support, b ≤ j) :
    (x * y).coeff (a + b) = x.coeff a * y.coeff b := by
  rw [coeff_mul]
  refine Finset.sum_eq_single (a, b) (fun ij hij hne => (hne ?_).elim) fun hab => ?_
  · obtain ⟨hi, hj, hsum⟩ := Finset.mem_antidiagonal.mp hij
    obtain ⟨rfl, rfl⟩ := (add_eq_add_iff_eq_and_eq (hx _ hi) (hy _ hj)).1 hsum.symm
    rfl
  · by_contra h
    exact hab (Finset.mem_antidiagonal.mpr
      ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h, rfl⟩)

/-- If `x` is supported at exponents at least `a` and `y` at exponents at least `b`, then `x * y`
is supported at exponents at least `a + b`. -/
theorem add_le_of_mem_support_mul [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} {a b : Γ}
    (hx : ∀ i ∈ x.support, a ≤ i) (hy : ∀ j ∈ y.support, b ≤ j) :
    ∀ k ∈ (x * y).support, a + b ≤ k := fun _ hk => by
  obtain ⟨i, hi, j, hj, rfl⟩ := Set.mem_add.mp (support_mul_subset hk)
  exact add_le_add (hx i hi) (hy j hj)

/-- If `x` is supported at exponents at least `a`, then `x ^ n` is supported at exponents at
least `n • a`. -/
theorem nsmul_le_of_mem_support_pow [Semiring R] {x : HahnSeries Γ R} {a : Γ}
    (hx : ∀ i ∈ x.support, a ≤ i) (n : ℕ) : ∀ i ∈ (x ^ n).support, n • a ≤ i := by
  induction n with
  | zero =>
    intro i hi
    rw [pow_zero, ← single_zero_one] at hi
    rw [zero_nsmul, Set.mem_singleton_iff.mp (support_single_subset hi)]
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact add_le_of_mem_support_mul ih hx

/-- If `x` is supported at exponents at least `a`, then the coefficient of `x ^ n` at `n • a` is
the `n`-th power of the coefficient of `x` at `a`. -/
theorem coeff_pow_nsmul_of_forall_le [Semiring R] {x : HahnSeries Γ R} {a : Γ}
    (hx : ∀ i ∈ x.support, a ≤ i) (n : ℕ) : (x ^ n).coeff (n • a) = x.coeff a ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, succ_nsmul, coeff_mul_add_of_forall_le (nsmul_le_of_mem_support_pow hx n) hx,
      ih, pow_succ]

/-- A Hahn series commutes with the constant series `C c` exactly when each of its coefficients
commutes with `c`. -/
theorem commute_C_iff [NonAssocSemiring R] {x : HahnSeries Γ R} {c : R} :
    Commute x (C c) ↔ ∀ g, Commute (x.coeff g) c := by
  simp only [commute_iff_eq, HahnSeries.ext_iff, funext_iff, C_apply, coeff_mul_single_zero,
    coeff_single_zero_mul]

end HahnSeries
