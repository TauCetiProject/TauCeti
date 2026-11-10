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

/-!
# Positive degree data

A positive degree on an additive monoid in an abelian group is an integer-valued
additive functional, strictly positive away from zero, with finite bounded-degree
sets. Such data make additive decompositions finite, so multiplication of completed
graded objects can be defined by finite coefficient sums.

This file proves sharpness and finiteness of the addition fibers, supplies Mathlib's
`Finset.HasAntidiagonal` interface on the positive monoid, and constructs the standard
example of the nonnegative orthant in a finite power of `ℤ`, graded by coordinate sum.

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

/-- A choice of finite enumeration of a degree cutoff. -/
noncomputable instance cutoffFintype (k : ℕ) : Fintype (d.cutoff k) :=
  (d.finite_cutoff k).fintype

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

/-- Each summand of a decomposition in the monoid has degree at most the total. -/
theorem degree_le_of_add_eq {a b n : N} (hb : b ∈ d.monoid) (h : a + b = n) :
    d.degree a ≤ d.degree n := by
  have hδ : d.degree a + d.degree b = d.degree n := by
    simpa using congrArg d.degree h
  have := d.degree_nonneg hb
  omega

/-- There are finitely many ordered decompositions of any ambient element into
two allowed degrees. This also applies when the element lies outside the monoid. -/
theorem finite_decompositions (n : N) :
    Set.Finite {p : N × N | p.1 ∈ d.monoid ∧ p.2 ∈ d.monoid ∧ p.1 + p.2 = n} := by
  apply ((d.finite_cutoff (d.degree n).toNat).prod
    (d.finite_cutoff (d.degree n).toNat)).subset
  rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
  exact ⟨⟨ha, (d.degree_le_of_add_eq hb hab).trans (Int.self_le_toNat _)⟩,
    ⟨hb, (d.degree_le_of_add_eq ha (by simpa [add_comm] using hab)).trans
      (Int.self_le_toNat _)⟩⟩

/-- Filtering a product of degree cutoffs by addition gives all allowed
decompositions whenever the cutoff bounds the degree of the total. -/
theorem filter_cutoff_product_eq_decompositions [DecidableEq N] (n : N) (k : ℕ)
    (hn : d.degree n ≤ k) :
    (((d.finite_cutoff k).toFinset ×ˢ (d.finite_cutoff k).toFinset).filter
      (fun p : N × N => p.1 + p.2 = n)) = (d.finite_decompositions n).toFinset := by
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_product, Set.Finite.mem_toFinset,
    mem_cutoff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨ha, hb⟩, hab⟩
    exact ⟨ha.1, hb.1, hab⟩
  · rintro ⟨ha, hb, hab⟩
    exact ⟨⟨⟨ha, (d.degree_le_of_add_eq hb hab).trans hn⟩,
      ⟨hb, (d.degree_le_of_add_eq ha (by simpa [add_comm] using hab)).trans hn⟩⟩, hab⟩

/-- Finite addition fibers on the subtype of allowed degrees. -/
theorem finite_add_fiber (n : d.monoid) :
    Set.Finite {p : d.monoid × d.monoid | p.1 + p.2 = n} := by
  apply (d.finite_decompositions n).of_injOn
    (f := fun p : d.monoid × d.monoid => ((p.1 : N), (p.2 : N)))
  · intro p hp
    exact ⟨p.1.property, p.2.property, congrArg Subtype.val hp⟩
  · intro p _ q _ h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
      (Subtype.ext (congrArg Prod.snd h))

/-- The finite addition fibers, packaged for Mathlib's convolution and power-series APIs.
Use `letI := d.hasAntidiagonal` when working on the subtype `d.monoid`. -/
@[instance_reducible]
noncomputable def hasAntidiagonal : Finset.HasAntidiagonal d.monoid where
  antidiagonal n := (d.finite_add_fiber n).toFinset
  mem_antidiagonal := by simp

section Group

variable {G : Type*} [AddCommGroup G] (d : PositiveDegrees G)

/-- The allowed monoid is sharp: an element and its negative can both belong only
when the element is zero. -/
theorem eq_zero_of_mem_of_neg_mem {n : G} (hn : n ∈ d.monoid)
    (hneg : -n ∈ d.monoid) : n = 0 := by
  have hnδ := d.degree_nonneg hn
  have hnegδ := d.degree_nonneg hneg
  rw [map_neg] at hnegδ
  exact (d.degree_eq_zero_iff hn).mp (by omega)

/-- Membership of the negative of an allowed degree characterizes zero. -/
@[simp]
theorem neg_mem_iff {n : G} (hn : n ∈ d.monoid) : -n ∈ d.monoid ↔ n = 0 := by
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
    exact lt_of_le_of_ne hn (Ne.symm hne)
  finite_le k := (Set.finite_Icc (a := (0 : ℤ)) (b := k)).subset fun _ h => h

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
    exact Fintype.sum_pos (lt_of_le_of_ne hn (Ne.symm hne))
  finite_le := by
    intro k
    apply (Set.Finite.pi (fun _ : ι => Set.finite_Icc (a := (0 : ℤ)) (b := k))).subset
    intro n hn
    simp only [Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_Icc]
    intro i
    exact ⟨hn.1 i, (Finset.single_le_sum (fun j _ => hn.1 j)
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
