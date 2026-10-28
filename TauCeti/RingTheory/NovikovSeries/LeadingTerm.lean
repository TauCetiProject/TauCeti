/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import TauCeti.RingTheory.NovikovSeries.Multiplication

/-!
# Leading terms of Novikov series, and Novikov rings without zero divisors

Let `H` be an additive monoid with a period homomorphism `N : H →+ ℝ`. A nonzero Novikov series
`a` attains a least period on its support; this is its *order* `a.order`
(`TauCeti.NovikovSeries.order`). Since `N` need not be injective, finitely many nonzero
coefficients may share this least period. The *leading term*
`a.leadingTerm` keeps all of them: it is the element of the group ring `R[H]` with the
coefficients of `a` at the exponents of period `a.order`, and `0` elsewhere. Its exponents all have
the same period, so when `H` is a group they lie in a single coset `h + ker N`, and the leading
term is a monomial `e^h` times an element of the group ring of the period kernel.

Periods add under convolution, so the product `a * b` has no nonzero coefficient below the
period `a.order + b.order`, and at that period its coefficients are those of the group-ring
product `a.leadingTerm * b.leadingTerm`. Hence, whenever this product of leading terms is nonzero,
it is the leading term of `a * b`, and orders add. If the group ring `R[H]` has no zero divisors,
then neither has the Novikov ring. By Mathlib's `AffineAddMonoid.to_twoUniqueSums`, this applies
when `R` is a domain and `H` is a finitely generated torsion-free abelian group, so the Novikov
ring is then a domain. Ties in the period are retained throughout: nothing here assumes that `N`
is injective.

## Main definitions

* `TauCeti.NovikovSeries.leadingTerm`: the coefficients of least period, as an element of the
  group ring.

## Main results

* `TauCeti.NovikovSeries.coeff_mul_eq_zero_of_lt_order_add` and
  `TauCeti.NovikovSeries.coeff_mul_of_period_eq_order_add`: below the period
  `a.order + b.order` the product `a * b` vanishes, and at that period its coefficients are those
  of the product of the leading terms.
* `TauCeti.NovikovSeries.leadingTerm_mul_of_ne_zero` and
  `TauCeti.NovikovSeries.order_mul_of_leadingTerm_mul_ne_zero`: a nonzero product of leading
  terms is the leading term of the product, and then orders add.
* `TauCeti.NovikovSeries.leadingTerm_mul` and `TauCeti.NovikovSeries.order_mul`: when `R[H]` has
  no zero divisors, the leading term is multiplicative without side condition, and the orders of
  two nonzero series add.
* The instances `NoZeroDivisors` and `IsDomain`: the Novikov ring inherits the absence of zero
  divisors from the group ring.
* `TauCeti.NovikovSeries.isDomain_of_fg`: over a domain, the Novikov ring of a finitely generated
  torsion-free abelian group, or more generally of a finitely generated cancellative torsion-free
  commutative monoid, is a domain.

## References

* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 3.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 2.
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace NovikovSeries

variable {R H : Type*}

section LeadingTerm

variable [AddZeroClass H] {N : H →+ ℝ} [Semiring R] {a : NovikovSeries R H N} {h : H}

open scoped Classical in
/-- The leading term of a Novikov series: the element of the group ring `R[H]` with the
coefficients of the series at the exponents whose period is the order, and `0` elsewhere. Since
the period map need not be injective, it may have several nonzero coefficients. -/
def leadingTerm (a : NovikovSeries R H N) : AddMonoidAlgebra R H :=
  .ofCoeff <| Finsupp.ofSupportFinite (fun h => if N h = a.order then a.coeff h else 0) <|
    (a.finite_le a.order).subset fun h hh => by
      by_cases hN : N h = a.order
      · exact ⟨by simpa [hN] using hh, hN.le⟩
      · exact absurd (ite_eq_right hN) hh

@[simp]
theorem coeff_leadingTerm (a : NovikovSeries R H N) (h : H) :
    a.leadingTerm.coeff h = if N h = a.order then a.coeff h else 0 := by
  classical
  simp [leadingTerm, Finsupp.ofSupportFinite_coe]

/-- The exponents of the leading term all have period equal to the order. -/
theorem period_eq_order_of_coeff_leadingTerm_ne_zero (hh : a.leadingTerm.coeff h ≠ 0) :
    N h = a.order := by
  by_contra hN
  exact hh (by rw [coeff_leadingTerm, ite_eq_right hN])

theorem coeff_ne_zero_of_coeff_leadingTerm_ne_zero (hh : a.leadingTerm.coeff h ≠ 0) :
    a.coeff h ≠ 0 := by
  rwa [coeff_leadingTerm, ite_eq_left (period_eq_order_of_coeff_leadingTerm_ne_zero hh)] at hh

@[simp]
theorem leadingTerm_eq_zero_iff : a.leadingTerm = 0 ↔ a = 0 := by
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · by_contra ha'
    obtain ⟨h, hh, hN⟩ := exists_coeff_ne_zero_and_period_eq_order ha'
    have := congrArg (fun x => x.coeff h) ha
    simp only [coeff_leadingTerm, ite_eq_left hN, AddMonoidAlgebra.coeff_zero,
      Finsupp.coe_zero, Pi.zero_apply] at this
    exact hh this
  · subst ha
    ext h
    simp

@[simp]
theorem leadingTerm_zero : (0 : NovikovSeries R H N).leadingTerm = 0 :=
  leadingTerm_eq_zero_iff.2 rfl

@[simp]
theorem leadingTerm_single (h : H) (r : R) :
    (single h r : NovikovSeries R H N).leadingTerm = AddMonoidAlgebra.single h r := by
  classical
  by_cases hr : r = 0
  · simp [hr]
  ext g
  rw [coeff_leadingTerm, order_single hr, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases hg : g = h
  · simp [hg]
  · rw [coeff_single_of_ne hg, ite_eq_right (Ne.symm hg), ite_self]

end LeadingTerm

@[simp]
theorem leadingTerm_neg [AddZeroClass H] {N : H →+ ℝ} [Ring R] (a : NovikovSeries R H N) :
    (-a).leadingTerm = -a.leadingTerm := by
  ext h
  rw [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, coeff_leadingTerm, coeff_leadingTerm,
    order_neg, coeff_neg]
  split_ifs <;> simp

section MulOrder

variable [AddZeroClass H] {N : H →+ ℝ} [NonUnitalNonAssocSemiring R] {a b : NovikovSeries R H N}
  {h : H}

/-- A product of Novikov series has no nonzero coefficient below the sum of the orders. -/
theorem coeff_mul_eq_zero_of_lt_order_add (hh : N h < a.order + b.order) :
    (a * b).coeff h = 0 := by
  by_contra hab
  obtain ⟨u, v, rfl, hu, hv⟩ := exists_add_eq_of_coeff_mul_ne_zero hab
  rw [map_add] at hh
  linarith [order_le_of_coeff_ne_zero hu, order_le_of_coeff_ne_zero hv]

end MulOrder

section Mul

variable [AddMonoid H] {N : H →+ ℝ} [Semiring R] {a b : NovikovSeries R H N} {h : H}

/-- Two exponents of the supports of `a` and `b` whose sum has period `a.order + b.order` have
periods `a.order` and `b.order`. -/
private theorem period_eq_order_of_add {u v : H} (hu : a.coeff u ≠ 0) (hv : b.coeff v ≠ 0)
    (huv : N (u + v) = a.order + b.order) : N u = a.order ∧ N v = b.order := by
  have hu' := order_le_of_coeff_ne_zero hu
  have hv' := order_le_of_coeff_ne_zero hv
  rw [map_add] at huv
  constructor <;> linarith

/-- At an exponent of period `a.order + b.order`, the coefficient of `a * b` is that of the
group-ring product of the leading terms. -/
theorem coeff_mul_of_period_eq_order_add (hh : N h = a.order + b.order) :
    (a * b).coeff h = (a.leadingTerm * b.leadingTerm).coeff h := by
  have hL : (a.leadingTerm * b.leadingTerm).coeff h =
      (ofAddMonoidAlgebra (N := N) (a.leadingTerm * b.leadingTerm)).coeff h := by
    rw [coeff_ofAddMonoidAlgebra]
  have hs : ∀ p ∈ (finite_setOf_add_eq a b h).toFinset, p.1 + p.2 = h :=
    fun p hp => ((Set.Finite.mem_toFinset _).1 hp).1
  rw [hL, map_mul, coeff_mul a b, coeff_mul_eq_sum (a := ofAddMonoidAlgebra a.leadingTerm)
    (b := ofAddMonoidAlgebra b.leadingTerm) hs fun u v huv hu hv => ?_]
  · refine sum_congr rfl fun p hp => ?_
    obtain ⟨hp, hu, hv⟩ := (Set.Finite.mem_toFinset _).1 hp
    obtain ⟨hNu, hNv⟩ := period_eq_order_of_add hu hv (by rw [hp, hh])
    simp [hNu, hNv]
  · rw [coeff_ofAddMonoidAlgebra] at hu hv
    exact (Set.Finite.mem_toFinset _).2 ⟨huv, coeff_ne_zero_of_coeff_leadingTerm_ne_zero hu,
      coeff_ne_zero_of_coeff_leadingTerm_ne_zero hv⟩

/-- The nonzero coefficients of a product of leading terms sit at period `a.order + b.order`. -/
private theorem period_eq_order_add_of_coeff_leadingTerm_mul_ne_zero
    (hh : (a.leadingTerm * b.leadingTerm).coeff h ≠ 0) : N h = a.order + b.order := by
  rw [← coeff_ofAddMonoidAlgebra (N := N), map_mul] at hh
  obtain ⟨u, v, rfl, hu, hv⟩ := exists_add_eq_of_coeff_mul_ne_zero hh
  rw [coeff_ofAddMonoidAlgebra] at hu hv
  rw [map_add, period_eq_order_of_coeff_leadingTerm_ne_zero hu,
    period_eq_order_of_coeff_leadingTerm_ne_zero hv]

/-- If the product of the leading terms of `a` and `b` is nonzero, the orders add. -/
theorem order_mul_of_leadingTerm_mul_ne_zero (hab : a.leadingTerm * b.leadingTerm ≠ 0) :
    (a * b).order = a.order + b.order := by
  obtain ⟨g, hg⟩ := Finsupp.support_nonempty_iff.2
    (mt AddMonoidAlgebra.coeff_eq_zero.1 hab)
  rw [Finsupp.mem_support_iff] at hg
  have hNg := period_eq_order_add_of_coeff_leadingTerm_mul_ne_zero hg
  refine order_eq_of_isLeast ⟨⟨g, ?_, hNg⟩, ?_⟩
  · rwa [mem_support, coeff_mul_of_period_eq_order_add hNg]
  · rintro _ ⟨h, hh, rfl⟩
    by_contra hlt
    exact mem_support.1 hh (coeff_mul_eq_zero_of_lt_order_add (not_le.1 hlt))

/-- If the product of the leading terms of `a` and `b` is nonzero, it is the leading term of
`a * b`. -/
theorem leadingTerm_mul_of_ne_zero (hab : a.leadingTerm * b.leadingTerm ≠ 0) :
    (a * b).leadingTerm = a.leadingTerm * b.leadingTerm := by
  ext g
  rw [coeff_leadingTerm, order_mul_of_leadingTerm_mul_ne_zero hab]
  split_ifs with hg
  · exact coeff_mul_of_period_eq_order_add hg
  · by_contra hne
    exact hg (period_eq_order_add_of_coeff_leadingTerm_mul_ne_zero (Ne.symm hne))

section NoZeroDivisors

variable [NoZeroDivisors (AddMonoidAlgebra R H)]

/-- If the group ring has no zero divisors, the leading term is multiplicative. -/
@[simp]
theorem leadingTerm_mul (a b : NovikovSeries R H N) :
    (a * b).leadingTerm = a.leadingTerm * b.leadingTerm := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  exact leadingTerm_mul_of_ne_zero
    (mul_ne_zero (mt leadingTerm_eq_zero_iff.1 ha) (mt leadingTerm_eq_zero_iff.1 hb))

/-- If the group ring has no zero divisors, the orders of nonzero Novikov series add under
multiplication. -/
theorem order_mul (ha : a ≠ 0) (hb : b ≠ 0) : (a * b).order = a.order + b.order :=
  order_mul_of_leadingTerm_mul_ne_zero
    (mul_ne_zero (mt leadingTerm_eq_zero_iff.1 ha) (mt leadingTerm_eq_zero_iff.1 hb))

/-- If the group ring `R[H]` has no zero divisors, then neither has the Novikov ring. -/
instance instNoZeroDivisors : NoZeroDivisors (NovikovSeries R H N) where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab := by
    have := congrArg leadingTerm hab
    rw [leadingTerm_mul, leadingTerm_zero] at this
    simpa using this

end NoZeroDivisors

end Mul

/-- If the group ring `R[H]` over a nontrivial ring has no zero divisors, the Novikov ring is a
domain. -/
instance instIsDomain [AddMonoid H] {N : H →+ ℝ} [Ring R] [Nontrivial R]
    [NoZeroDivisors (AddMonoidAlgebra R H)] : IsDomain (NovikovSeries R H N) :=
  NoZeroDivisors.to_isDomain _

/-- Over a domain, the Novikov ring of a finitely generated cancellative torsion-free commutative
monoid, for instance of a finitely generated torsion-free abelian group, is a domain for every
period homomorphism. -/
theorem isDomain_of_fg [Ring R] [IsDomain R] [AddCancelCommMonoid H] [AddMonoid.FG H]
    [HasUniqueDiv H] (N : H →+ ℝ) : IsDomain (NovikovSeries R H N) :=
  inferInstance

end NovikovSeries

end TauCeti
