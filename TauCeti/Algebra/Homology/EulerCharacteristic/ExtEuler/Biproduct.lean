/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Basic
public import TauCeti.Algebra.Homology.Ext.Biproduct

/-!
# Finite sums and the Ext-Euler characteristic

A finite biproduct is Euler-admissible against an object exactly when each summand is. This holds
in either variable, including for the empty biproduct. The two finiteness conditions are treated
separately: `Ext`-finiteness of a finite biproduct is `Ext`-finiteness of every summand, and a
vanishing bound holds for the biproduct exactly when it holds, unchanged, for every summand. The
Ext-Euler characteristic of a finite biproduct is the sum of the Ext-Euler characteristics of its
summands.

These results let finite additive closures of object families serve as domains for Ext-Euler
pairings. The binary closure lemmas `TauCeti.IsEulerAdmissible.biprod` and
`TauCeti.IsEulerAdmissible.biprod'` only give one direction, through the split short exact
sequence; here the decomposition `Ext(⨁ Xᵢ, Y) ≃ ∏ Ext(Xᵢ, Y)` gives both directions for
any finite index type. The graded counterparts are in
`TauCeti/Algebra/Homology/EulerCharacteristic/ExtEuler/Graded/Biproduct.lean`.

## Main results

* `TauCeti.isEulerAdmissible_biproduct_left_iff` and
  `TauCeti.isEulerAdmissible_biproduct_right_iff`: a finite biproduct is Euler-admissible against
  an object, resp. an object against a finite biproduct, exactly when each summand is.
* `TauCeti.extEuler_biproduct_left` and `TauCeti.extEuler_biproduct_right`:
  `χ(⨁ Xᵢ, Y) = ∑ χ(Xᵢ, Y)` and `χ(X, ⨁ Yᵢ) = ∑ χ(X, Yᵢ)`.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 2.4--2.7, for the
  additivity of Ext in both variables.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w v u t

attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type t} [Field k] [Linear k C]
  [HasExt.{w} C] {J : Type*}

section Admissibility

variable [Finite J]

/-- `Ext`-finiteness out of a finite biproduct is equivalent to `Ext`-finiteness out of each
summand. -/
@[simp]
theorem isExtFinite_biproduct_left_iff (X : J → C) (Y : C) :
    IsExtFinite.{w} k (⨁ X) Y ↔ ∀ i, IsExtFinite.{w} k (X i) Y := by
  let := Fintype.ofFinite J
  have e (n : ℕ) := Ext.biproductLinearEquiv k (biproduct.isBilimit X) Y n
  constructor
  · intro h i
    exact ⟨fun n ↦ haveI := h.finiteDimensional n
      haveI := Module.Finite.equiv (e n)
      Module.Finite.of_pi (fun i ↦ Ext.{w} (X i) Y n) i⟩
  · intro h
    exact ⟨fun n ↦ haveI := fun i ↦ (h i).finiteDimensional n
      Module.Finite.equiv (e n).symm⟩

/-- `Ext`-finiteness into a finite biproduct is equivalent to `Ext`-finiteness into each
summand. -/
@[simp]
theorem isExtFinite_biproduct_right_iff (X : C) (Y : J → C) :
    IsExtFinite.{w} k X (⨁ Y) ↔ ∀ i, IsExtFinite.{w} k X (Y i) := by
  let := Fintype.ofFinite J
  have e (n : ℕ) := Ext.linearEquivBiproduct k X (biproduct.isBilimit Y) n
  constructor
  · intro h i
    exact ⟨fun n ↦ haveI := h.finiteDimensional n
      haveI := Module.Finite.equiv (e n)
      Module.Finite.of_pi (fun i ↦ Ext.{w} X (Y i) n) i⟩
  · intro h
    exact ⟨fun n ↦ haveI := fun i ↦ (h i).finiteDimensional n
      Module.Finite.equiv (e n).symm⟩

/-- A vanishing bound holds out of a finite biproduct exactly when it holds out of every summand,
with the same bound. -/
@[simp]
theorem isExtBoundedBy_biproduct_left_iff (X : J → C) (Y : C) (N : ℕ) :
    IsExtBoundedBy.{w} (⨁ X) Y N ↔ ∀ i, IsExtBoundedBy.{w} (X i) Y N := by
  classical
  let := Fintype.ofFinite J
  have e (n : ℕ) := Ext.biproductAddEquiv (biproduct.isBilimit X) Y n
  constructor
  · intro h i
    refine ⟨fun n hn ↦ ?_⟩
    have := h.subsingleton hn
    have := (e n).symm.toEquiv.subsingleton
    exact (Pi.single_injective (M := fun i ↦ Ext.{w} (X i) Y n) i).subsingleton
  · intro h
    refine ⟨fun n hn ↦ ?_⟩
    have := fun i ↦ (h i).subsingleton hn
    exact (e n).toEquiv.subsingleton

/-- A vanishing bound holds into a finite biproduct exactly when it holds into every summand,
with the same bound. -/
@[simp]
theorem isExtBoundedBy_biproduct_right_iff (X : C) (Y : J → C) (N : ℕ) :
    IsExtBoundedBy.{w} X (⨁ Y) N ↔ ∀ i, IsExtBoundedBy.{w} X (Y i) N := by
  classical
  let := Fintype.ofFinite J
  have e (n : ℕ) := Ext.addEquivBiproduct X (biproduct.isBilimit Y) n
  constructor
  · intro h i
    refine ⟨fun n hn ↦ ?_⟩
    have := h.subsingleton hn
    have := (e n).symm.toEquiv.subsingleton
    exact (Pi.single_injective (M := fun i ↦ Ext.{w} X (Y i) n) i).subsingleton
  · intro h
    refine ⟨fun n hn ↦ ?_⟩
    have := fun i ↦ (h i).subsingleton hn
    exact (e n).toEquiv.subsingleton

/-- Eventual `Ext`-vanishing out of a finite biproduct is equivalent to eventual vanishing out of
every summand. -/
@[simp]
theorem isExtBounded_biproduct_left_iff (X : J → C) (Y : C) :
    IsExtBounded.{w} (⨁ X) Y ↔ ∀ i, IsExtBounded.{w} (X i) Y := by
  constructor
  · rintro ⟨N, hN⟩ i
    exact ((isExtBoundedBy_biproduct_left_iff X Y N).1 hN i).isExtBounded
  · intro h
    obtain ⟨N, hN⟩ := exists_forall_isExtBoundedBy h
    exact ⟨N, (isExtBoundedBy_biproduct_left_iff X Y N).2 hN⟩

/-- Eventual `Ext`-vanishing into a finite biproduct is equivalent to eventual vanishing into
every summand. -/
@[simp]
theorem isExtBounded_biproduct_right_iff (X : C) (Y : J → C) :
    IsExtBounded.{w} X (⨁ Y) ↔ ∀ i, IsExtBounded.{w} X (Y i) := by
  constructor
  · rintro ⟨N, hN⟩ i
    exact ((isExtBoundedBy_biproduct_right_iff X Y N).1 hN i).isExtBounded
  · intro h
    obtain ⟨N, hN⟩ := exists_forall_isExtBoundedBy h
    exact ⟨N, (isExtBoundedBy_biproduct_right_iff X Y N).2 hN⟩

/-- A finite biproduct is Euler-admissible in the first variable exactly when each summand is. -/
@[simp]
theorem isEulerAdmissible_biproduct_left_iff (X : J → C) (Y : C) :
    IsEulerAdmissible.{w} k (⨁ X) Y ↔ ∀ i, IsEulerAdmissible.{w} k (X i) Y := by
  constructor
  · intro h i
    exact ⟨(isExtFinite_biproduct_left_iff X Y).1 h.isExtFinite i,
      (isExtBounded_biproduct_left_iff X Y).1 h.isExtBounded i⟩
  · intro h
    exact ⟨(isExtFinite_biproduct_left_iff X Y).2 fun i ↦ (h i).isExtFinite,
      (isExtBounded_biproduct_left_iff X Y).2 fun i ↦ (h i).isExtBounded⟩

/-- A finite biproduct is Euler-admissible in the second variable exactly when each summand is. -/
@[simp]
theorem isEulerAdmissible_biproduct_right_iff (X : C) (Y : J → C) :
    IsEulerAdmissible.{w} k X (⨁ Y) ↔ ∀ i, IsEulerAdmissible.{w} k X (Y i) := by
  constructor
  · intro h i
    exact ⟨(isExtFinite_biproduct_right_iff X Y).1 h.isExtFinite i,
      (isExtBounded_biproduct_right_iff X Y).1 h.isExtBounded i⟩
  · intro h
    exact ⟨(isExtFinite_biproduct_right_iff X Y).2 fun i ↦ (h i).isExtFinite,
      (isExtBounded_biproduct_right_iff X Y).2 fun i ↦ (h i).isExtBounded⟩

end Admissibility

variable [Fintype J]

/-- Truncated alternating sums out of a finite biproduct of `Ext`-finite summands add up. -/
private theorem truncatedExtEuler_biproduct_left {X : J → C} {Y : C}
    (h : ∀ i, IsExtFinite.{w} k (X i) Y) (N : ℕ) :
    truncatedExtEuler.{w} k (⨁ X) Y N = ∑ i, truncatedExtEuler.{w} k (X i) Y N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have := fun i ↦ (h i).finiteDimensional N
    rw [truncatedExtEuler_succ, ih,
      (Ext.biproductLinearEquiv k (biproduct.isBilimit X) Y N).finrank_eq,
      Module.finrank_pi_fintype, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    simp only [truncatedExtEuler_succ]

/-- Truncated alternating sums into a finite biproduct of `Ext`-finite summands add up. -/
private theorem truncatedExtEuler_biproduct_right {X : C} {Y : J → C}
    (h : ∀ i, IsExtFinite.{w} k X (Y i)) (N : ℕ) :
    truncatedExtEuler.{w} k X (⨁ Y) N = ∑ i, truncatedExtEuler.{w} k X (Y i) N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have := fun i ↦ (h i).finiteDimensional N
    rw [truncatedExtEuler_succ, ih,
      (Ext.linearEquivBiproduct k X (biproduct.isBilimit Y) N).finrank_eq,
      Module.finrank_pi_fintype, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    simp only [truncatedExtEuler_succ]

/-- The Ext-Euler characteristic is additive on finite sums in the first variable:
`χ(⨁ Xᵢ, Y) = ∑ χ(Xᵢ, Y)`. -/
@[simp]
theorem extEuler_biproduct_left {X : J → C} {Y : C}
    (hsum : IsEulerAdmissible.{w} k (⨁ X) Y) :
    extEuler k hsum =
      ∑ i, extEuler k ((isEulerAdmissible_biproduct_left_iff X Y).1 hsum i) := by
  have h := (isEulerAdmissible_biproduct_left_iff X Y).1 hsum
  obtain ⟨N, hN⟩ := exists_forall_isExtBoundedBy fun i ↦ (h i).isExtBounded
  rw [extEuler_eq k hsum ((isExtBoundedBy_biproduct_left_iff X Y N).2 hN),
    truncatedExtEuler_biproduct_left (fun i ↦ (h i).isExtFinite) N]
  exact Finset.sum_congr rfl fun i _ ↦ (extEuler_eq k (h i) (hN i)).symm

/-- The Ext-Euler characteristic is additive on finite sums in the second variable:
`χ(X, ⨁ Yᵢ) = ∑ χ(X, Yᵢ)`. -/
@[simp]
theorem extEuler_biproduct_right {X : C} {Y : J → C}
    (hsum : IsEulerAdmissible.{w} k X (⨁ Y)) :
    extEuler k hsum =
      ∑ i, extEuler k ((isEulerAdmissible_biproduct_right_iff X Y).1 hsum i) := by
  have h := (isEulerAdmissible_biproduct_right_iff X Y).1 hsum
  obtain ⟨N, hN⟩ := exists_forall_isExtBoundedBy fun i ↦ (h i).isExtBounded
  rw [extEuler_eq k hsum ((isExtBoundedBy_biproduct_right_iff X Y N).2 hN),
    truncatedExtEuler_biproduct_right (fun i ↦ (h i).isExtFinite) N]
  exact Finset.sum_congr rfl fun i _ ↦ (extEuler_eq k (h i) (hN i)).symm

end TauCeti
