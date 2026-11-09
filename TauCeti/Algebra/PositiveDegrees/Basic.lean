/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.MulAntidiagonal

/-!
# Positive degree data

A positive degree on a submonoid of an additive commutative monoid is an integer-valued
additive functional, strictly positive away from zero, with finite bounded-degree
sets. Such data make additive decompositions finite, so multiplication of completed
graded objects can be defined by finite coefficient sums.

This file proves sharpness and finiteness of the addition fibers, supplies Mathlib's
`Finset.HasAntidiagonal` interface on the positive monoid, and constructs the standard
example of the nonnegative orthant in a finite power of `ℤ`, graded by coordinate sum.
Only the sharpness lemmas require an additive commutative group.

Adapted from `Mei/Algebra/PositiveDegrees/Basic.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f`, released under Apache 2.0.
-/

public section

namespace TauCeti

/-- A submonoid with a strictly positive additive degree and finite degree cutoffs.
No finite generation or saturation of the submonoid is required. -/
structure PositiveDegrees (N : Type*) [AddCommMonoid N] where
  /-- The monoid of allowed degrees, including zero. -/
  monoid : AddSubmonoid N
  /-- The additive integer-valued degree. -/
  degree : N →+ ℤ
  /-- Nonzero allowed degrees have strictly positive degree. -/
  degree_pos : ∀ {n}, n ∈ monoid → n ≠ 0 → 0 < degree n
  /-- Only finitely many allowed degrees occur below any natural cutoff. -/
  finite_le : ∀ k : ℕ, Set.Finite {n | n ∈ monoid ∧ degree n ≤ k}

namespace PositiveDegrees

variable {N : Type*} [AddCommMonoid N] (d : PositiveDegrees N)

/-- Positive degree data are determined by their monoid and degree homomorphism. -/
@[ext]
theorem ext {d e : PositiveDegrees N} (hP : d.monoid = e.monoid)
    (hδ : d.degree = e.degree) : d = e := by
  cases d
  cases e
  cases hP
  cases hδ
  rfl

/-- The degree is nonnegative on the allowed monoid. -/
theorem degree_nonneg {n : N} (hn : n ∈ d.monoid) : 0 ≤ d.degree n := by
  by_cases h : n = 0
  · simp [h]
  · exact (d.degree_pos hn h).le

/-- Among allowed degrees, only zero has degree zero. -/
@[simp]
theorem degree_eq_zero_iff {n : N} (hn : n ∈ d.monoid) : d.degree n = 0 ↔ n = 0 := by
  constructor
  · intro h
    by_contra hne
    have := d.degree_pos hn hne
    omega
  · rintro rfl
    exact map_zero _

/-- Adding an allowed degree to a nonzero allowed degree gives a nonzero degree. -/
theorem add_ne_zero {n m : N} (hn : n ∈ d.monoid) (hm : m ∈ d.monoid) (hn0 : n ≠ 0) :
    n + m ≠ 0 := by
  intro h
  have := d.degree_pos hn hn0
  have := d.degree_nonneg hm
  have := congrArg d.degree h
  simp only [map_add, map_zero] at this
  omega

/-- A sum of allowed degrees is zero precisely when both summands are zero. -/
theorem add_eq_zero_iff {n m : N} (hn : n ∈ d.monoid) (hm : m ∈ d.monoid) :
    n + m = 0 ↔ n = 0 ∧ m = 0 := by
  constructor
  · intro h
    have hn0 : n = 0 := by
      by_contra hn0
      exact d.add_ne_zero hn hm hn0 h
    exact ⟨hn0, by simpa [hn0] using h⟩
  · rintro ⟨rfl, rfl⟩
    exact zero_add _

/-- The degree cutoff, retaining zero and all allowed degrees of order at most `k`. -/
def cutoff (k : ℕ) : Set N := {n | n ∈ d.monoid ∧ d.degree n ≤ k}

/-- Membership in a degree cutoff. -/
@[simp]
theorem mem_cutoff {k : ℕ} {n : N} :
    n ∈ d.cutoff k ↔ n ∈ d.monoid ∧ d.degree n ≤ k := Iff.rfl

/-- Every degree cutoff is finite. -/
theorem finite_cutoff (k : ℕ) : (d.cutoff k).Finite := d.finite_le k

/-- Degree cutoffs are finite types, so they can index finite families. -/
instance (k : ℕ) : Finite (d.cutoff k) := (d.finite_cutoff k).to_subtype

/-- Increasing the cutoff retains every previously allowed degree. -/
theorem cutoff_mono : Monotone d.cutoff := by
  intro k l h n hn
  exact ⟨hn.1, hn.2.trans (Int.ofNat_le.mpr h)⟩

/-- The order-zero cutoff contains precisely zero. -/
@[simp]
theorem cutoff_zero : d.cutoff 0 = {0} := by
  ext n
  simp only [mem_cutoff, Nat.cast_zero, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hn, h⟩
    exact (d.degree_eq_zero_iff hn).mp (le_antisymm h (d.degree_nonneg hn))
  · rintro rfl
    simp [d.monoid.zero_mem]

/-- The left summand has degree at most the total when the right summand is allowed. -/
theorem degree_le_of_add_eq {a b n : N} (hb : b ∈ d.monoid) (h : a + b = n) :
    d.degree a ≤ d.degree n := by
  have hδ : d.degree a + d.degree b = d.degree n := by
    simpa using congrArg d.degree h
  have := d.degree_nonneg hb
  omega

/-- The right summand has degree at most the total when the left summand is allowed. -/
theorem degree_le_of_add_eq_right {a b n : N} (ha : a ∈ d.monoid) (h : a + b = n) :
    d.degree b ≤ d.degree n :=
  d.degree_le_of_add_eq ha (by simpa only [add_comm] using h)

/-- Both summands of an allowed decomposition lie in any cutoff bounding the total degree. -/
theorem antidiagonal_subset_cutoff_prod {n : N} {k : ℕ} (hn : d.degree n ≤ k) :
    Set.antidiagonal (d.monoid : Set N) d.monoid n ⊆ d.cutoff k ×ˢ d.cutoff k := by
  intro ⟨a, b⟩ hp
  obtain ⟨ha, hb, hab⟩ := Set.mem_antidiagonal.mp hp
  exact ⟨⟨ha, (d.degree_le_of_add_eq hb hab).trans hn⟩,
    ⟨hb, (d.degree_le_of_add_eq_right ha hab).trans hn⟩⟩

/-- There are finitely many ordered decompositions of any ambient element into
two allowed degrees. This also applies when the element lies outside the monoid. -/
theorem finite_antidiagonal (n : N) :
    (Set.antidiagonal (d.monoid : Set N) d.monoid n).Finite :=
  ((d.finite_cutoff (d.degree n).toNat).prod
    (d.finite_cutoff (d.degree n).toNat)).subset
    (d.antidiagonal_subset_cutoff_prod (Int.self_le_toNat _))

/-- Filtering a product of degree cutoffs by addition gives all allowed
decompositions whenever the cutoff bounds the degree of the total. -/
theorem filter_cutoff_product_eq_antidiagonal [DecidableEq N] (n : N) (k : ℕ)
    (hn : d.degree n ≤ k) :
    (((d.finite_cutoff k).toFinset ×ˢ (d.finite_cutoff k).toFinset).filter
      (fun p : N × N => p.1 + p.2 = n)) = (d.finite_antidiagonal n).toFinset := by
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_product, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨ha, hb⟩, hab⟩
    exact Set.mem_antidiagonal.mpr ⟨ha.1, hb.1, hab⟩
  · intro hp
    exact ⟨d.antidiagonal_subset_cutoff_prod hn hp, (Set.mem_antidiagonal.mp hp).2.2⟩

/-- Finite addition fibers on the subtype of allowed degrees. -/
theorem finite_antidiagonal_subtype (n : d.monoid) :
    Set.Finite {p : d.monoid × d.monoid | p.1 + p.2 = n} := by
  apply (d.finite_antidiagonal n).of_injOn
    (f := fun p : d.monoid × d.monoid => ((p.1 : N), (p.2 : N)))
  · intro p hp
    exact Set.mem_antidiagonal.mpr
      ⟨p.1.property, p.2.property, congrArg Subtype.val hp⟩
  · intro p _ q _ h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
      (Subtype.ext (congrArg Prod.snd h))

/-- The finite addition fibers, packaged for Mathlib's antidiagonal summation API.
Use `letI := d.hasAntidiagonal` when working on the subtype `d.monoid`. -/
@[instance_reducible]
noncomputable def hasAntidiagonal : Finset.HasAntidiagonal d.monoid where
  antidiagonal n := (d.finite_antidiagonal_subtype n).toFinset
  mem_antidiagonal := by simp

section Group

variable {G : Type*} [AddCommGroup G] (d : PositiveDegrees G)

/-- The allowed monoid is sharp: an element and its negative can both belong only
when the element is zero. -/
theorem eq_zero_of_mem_of_neg_mem {n : G} (hn : n ∈ d.monoid)
    (hneg : -n ∈ d.monoid) : n = 0 :=
  ((d.add_eq_zero_iff hn hneg).mp (add_neg_cancel n)).1

/-- Membership of the negative of an allowed degree characterizes zero. -/
@[simp]
theorem neg_mem_iff_eq_zero {n : G} (hn : n ∈ d.monoid) : -n ∈ d.monoid ↔ n = 0 := by
  constructor
  · exact d.eq_zero_of_mem_of_neg_mem hn
  · rintro rfl
    simp

end Group

/-- The nonnegative integers with their identity degree. -/
def nonnegIntegers : PositiveDegrees ℤ where
  monoid := AddSubmonoid.nonneg ℤ
  degree := AddMonoidHom.id ℤ
  degree_pos := by
    intro n hn hne
    exact lt_of_le_of_ne (AddSubmonoid.mem_nonneg.mp hn) (Ne.symm hne)
  finite_le k := (Set.finite_Icc (a := (0 : ℤ)) (b := k)).subset
    fun _ h => ⟨AddSubmonoid.mem_nonneg.mp h.1, h.2⟩

/-- The allowed integer degrees are precisely the nonnegative integers. -/
@[simp]
theorem mem_nonnegIntegers_monoid {n : ℤ} : n ∈ nonnegIntegers.monoid ↔ 0 ≤ n :=
  Iff.rfl

/-- The degree of a nonnegative integer is the integer itself. -/
@[simp]
theorem nonnegIntegers_degree (n : ℤ) : nonnegIntegers.degree n = n := (rfl)

/-- The nonnegative orthant in a finite power of `ℤ`, with coordinate-sum degree.
The empty coordinate type is allowed. -/
def orthant (ι : Type*) [Fintype ι] : PositiveDegrees (ι → ℤ) where
  monoid := AddSubmonoid.nonneg (ι → ℤ)
  degree :=
    { toFun := fun n => ∑ i, n i
      map_zero' := by simp
      map_add' := by intros; simp [Finset.sum_add_distrib] }
  degree_pos := by
    intro n hn hne
    exact Fintype.sum_pos
      (lt_of_le_of_ne (AddSubmonoid.mem_nonneg.mp hn) (Ne.symm hne))
  finite_le := by
    intro k
    apply (Set.Finite.pi (fun _ : ι => Set.finite_Icc (a := (0 : ℤ)) (b := k))).subset
    intro n hn
    simp only [Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_Icc]
    intro i
    exact ⟨(AddSubmonoid.mem_nonneg.mp hn.1) i,
      (Finset.single_le_sum (fun j _ => (AddSubmonoid.mem_nonneg.mp hn.1) j)
      (Finset.mem_univ i)).trans hn.2⟩

/-- The standard orthant consists of the coordinatewise nonnegative vectors. -/
@[simp]
theorem mem_orthant_monoid {ι : Type*} [Fintype ι] {n : ι → ℤ} :
    n ∈ (orthant ι).monoid ↔ ∀ i, 0 ≤ n i := Iff.rfl

/-- The standard degree is the coordinate sum. -/
@[simp]
theorem orthant_degree {ι : Type*} [Fintype ι] (n : ι → ℤ) :
    (orthant ι).degree n = ∑ i, n i := (rfl)

end PositiveDegrees
end TauCeti
