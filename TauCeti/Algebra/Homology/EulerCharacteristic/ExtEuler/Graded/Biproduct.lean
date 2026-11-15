/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Basic
public import TauCeti.Algebra.Homology.Ext.Biproduct

/-!
# Finite sums and the graded Ext-Euler characteristic

A finite biproduct is graded Euler-admissible against an object exactly when each summand is.
This holds in either variable, including for the empty biproduct. Finite internal support and
uniform cohomological vanishing are treated separately: the internal supports are united, and
the cohomological bounds are replaced by a common bound. The q-Euler characteristic of a finite
biproduct is the sum of the q-Euler characteristics of its summands.

These results let finite additive closures of object families serve as domains for graded Euler
pairings. No uniform internal support across all cohomological degrees, or global dimension
bound on the category, is assumed.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 2.4--2.7, for the
  additivity of Ext in both variables.
* Zsuzsanna Dancso and Anthony Licata, *Koszul algebras and flow lattices*, Section 2.2, for
  the graded Euler form and its target-shift convention.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits LaurentPolynomial

universe w v u t

attribute [local instance] Abelian.hasFiniteBiproducts
  preservesBiproduct_of_preservesProduct

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type t} [Field k] [Linear k C]
  [HasExt.{w} C] {e : C ≌ C} {J : Type*}

section Admissibility

variable [Finite J]

/-- Finite internal Ext support out of a finite biproduct is equivalent to finite internal
support out of each summand. -/
@[simp]
theorem isGradedExtInternallyFinite_biproduct_left_iff (X : J → C) (Y : C) :
    IsGradedExtInternallyFinite.{w} k e (⨁ X) Y ↔
      ∀ i, IsGradedExtInternallyFinite.{w} k e (X i) Y := by
  let := Fintype.ofFinite J
  constructor
  · intro h i
    exact ⟨fun n ↦ ((h.finiteLaurentSupport n).of_equiv fun j ↦
      Ext.biproductLinearEquiv k (biproduct.isBilimit X) ((e ^ j).functor.obj Y) n).of_pi i⟩
  · intro h
    exact ⟨fun n ↦ (HasFiniteLaurentSupport.pi fun i ↦ (h i).finiteLaurentSupport n).of_equiv
      fun j ↦ (Ext.biproductLinearEquiv k (biproduct.isBilimit X)
        ((e ^ j).functor.obj Y) n).symm⟩

/-- Finite internal Ext support into a finite biproduct is equivalent to finite internal
support into each summand. -/
@[simp]
theorem isGradedExtInternallyFinite_biproduct_right_iff (X : C) (Y : J → C) :
    IsGradedExtInternallyFinite.{w} k e X (⨁ Y) ↔
      ∀ i, IsGradedExtInternallyFinite.{w} k e X (Y i) := by
  let := Fintype.ofFinite J
  constructor
  · intro h i
    exact ⟨fun n ↦ ((h.finiteLaurentSupport n).of_equiv fun j ↦
      Ext.linearEquivBiproduct k X
        (isBilimitOfPreserves (e ^ j).functor (biproduct.isBilimit Y)) n).of_pi i⟩
  · intro h
    exact ⟨fun n ↦ (HasFiniteLaurentSupport.pi fun i ↦ (h i).finiteLaurentSupport n).of_equiv
      fun j ↦ (Ext.linearEquivBiproduct k X
        (isBilimitOfPreserves (e ^ j).functor (biproduct.isBilimit Y)) n).symm⟩

/-- A cohomological bound holds out of a finite biproduct exactly when it holds out of every
summand, with the same bound. -/
@[simp]
theorem isGradedExtBoundedBy_biproduct_left_iff (X : J → C) (Y : C) (N : ℕ) :
    IsGradedExtBoundedBy.{w} e (⨁ X) Y N ↔
      ∀ i, IsGradedExtBoundedBy.{w} e (X i) Y N := by
  classical
  let := Fintype.ofFinite J
  constructor
  · intro h i
    refine ⟨fun n hn j ↦ ?_⟩
    have := h.subsingleton hn j
    have := (Ext.biproductAddEquiv (biproduct.isBilimit X)
      ((e ^ j).functor.obj Y) n).symm.toEquiv.subsingleton
    exact (Pi.single_injective (M := fun i ↦ GradedExt.{w} e (X i) Y n j) i).subsingleton
  · intro h
    refine ⟨fun n hn j ↦ ?_⟩
    have := fun i ↦ (h i).subsingleton hn j
    exact (Ext.biproductAddEquiv (biproduct.isBilimit X)
      ((e ^ j).functor.obj Y) n).toEquiv.subsingleton

/-- A cohomological bound holds into a finite biproduct exactly when it holds into every
summand, with the same bound. -/
@[simp]
theorem isGradedExtBoundedBy_biproduct_right_iff (X : C) (Y : J → C) (N : ℕ) :
    IsGradedExtBoundedBy.{w} e X (⨁ Y) N ↔
      ∀ i, IsGradedExtBoundedBy.{w} e X (Y i) N := by
  classical
  let := Fintype.ofFinite J
  let E (n : ℕ) (j : ℤ) :
      GradedExt.{w} e X (⨁ Y) n j ≃+ ∀ i, GradedExt.{w} e X (Y i) n j :=
    Ext.addEquivBiproduct X
      (isBilimitOfPreserves (e ^ j).functor (biproduct.isBilimit Y)) n
  constructor
  · intro h i
    refine ⟨fun n hn j ↦ ?_⟩
    have := h.subsingleton hn j
    have := (E n j).symm.toEquiv.subsingleton
    exact (Pi.single_injective (M := fun i ↦ GradedExt.{w} e X (Y i) n j) i).subsingleton
  · intro h
    refine ⟨fun n hn j ↦ ?_⟩
    have := fun i ↦ (h i).subsingleton hn j
    exact (E n j).toEquiv.subsingleton

/-- Eventual graded Ext-vanishing out of a finite biproduct is equivalent to eventual
vanishing out of every summand. -/
@[simp]
theorem isGradedExtBounded_biproduct_left_iff (X : J → C) (Y : C) :
    IsGradedExtBounded.{w} e (⨁ X) Y ↔ ∀ i, IsGradedExtBounded.{w} e (X i) Y := by
  constructor
  · rintro ⟨N, hN⟩ i
    exact ((isGradedExtBoundedBy_biproduct_left_iff X Y N).1 hN i).isGradedExtBounded
  · intro h
    obtain ⟨N, hN⟩ := exists_forall_isGradedExtBoundedBy h
    exact ⟨N, (isGradedExtBoundedBy_biproduct_left_iff X Y N).2 hN⟩

/-- Eventual graded Ext-vanishing into a finite biproduct is equivalent to eventual
vanishing into every summand. -/
@[simp]
theorem isGradedExtBounded_biproduct_right_iff (X : C) (Y : J → C) :
    IsGradedExtBounded.{w} e X (⨁ Y) ↔ ∀ i, IsGradedExtBounded.{w} e X (Y i) := by
  constructor
  · rintro ⟨N, hN⟩ i
    exact ((isGradedExtBoundedBy_biproduct_right_iff X Y N).1 hN i).isGradedExtBounded
  · intro h
    obtain ⟨N, hN⟩ := exists_forall_isGradedExtBoundedBy h
    exact ⟨N, (isGradedExtBoundedBy_biproduct_right_iff X Y N).2 hN⟩

/-- A finite biproduct is graded Euler-admissible in the first variable exactly when each
summand is. -/
@[simp]
theorem isGradedEulerAdmissible_biproduct_left_iff (X : J → C) (Y : C) :
    IsGradedEulerAdmissible.{w} k e (⨁ X) Y ↔
      ∀ i, IsGradedEulerAdmissible.{w} k e (X i) Y := by
  constructor
  · intro h i
    exact ⟨(isGradedExtInternallyFinite_biproduct_left_iff X Y).1 h.internallyFinite i,
      (isGradedExtBounded_biproduct_left_iff X Y).1 h.bounded i⟩
  · intro h
    exact ⟨(isGradedExtInternallyFinite_biproduct_left_iff X Y).2 fun i ↦ (h i).internallyFinite,
      (isGradedExtBounded_biproduct_left_iff X Y).2 fun i ↦ (h i).bounded⟩

/-- A finite biproduct is graded Euler-admissible in the second variable exactly when each
summand is. -/
@[simp]
theorem isGradedEulerAdmissible_biproduct_right_iff (X : C) (Y : J → C) :
    IsGradedEulerAdmissible.{w} k e X (⨁ Y) ↔
      ∀ i, IsGradedEulerAdmissible.{w} k e X (Y i) := by
  constructor
  · intro h i
    exact ⟨(isGradedExtInternallyFinite_biproduct_right_iff X Y).1 h.internallyFinite i,
      (isGradedExtBounded_biproduct_right_iff X Y).1 h.bounded i⟩
  · intro h
    exact ⟨(isGradedExtInternallyFinite_biproduct_right_iff X Y).2 fun i ↦ (h i).internallyFinite,
      (isGradedExtBounded_biproduct_right_iff X Y).2 fun i ↦ (h i).bounded⟩

end Admissibility

variable [Fintype J]

/-- The q-Euler characteristic is additive on finite sums in the first variable. -/
@[simp]
theorem gradedExtEuler_biproduct_left {X : J → C} {Y : C}
    (hsum : IsGradedEulerAdmissible.{w} k e (⨁ X) Y) :
    gradedExtEuler k e hsum = ∑ i, gradedExtEuler k e
      ((isGradedEulerAdmissible_biproduct_left_iff X Y).1 hsum i) := by
  let h := (isGradedEulerAdmissible_biproduct_left_iff X Y).1 hsum
  obtain ⟨N, hN⟩ := exists_forall_isGradedExtBoundedBy fun i ↦ (h i).bounded
  ext j
  rw [coeff_gradedExtEuler k e _
    ((isGradedExtBoundedBy_biproduct_left_iff X Y N).2 hN)]
  simp only [AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  calc
    _ = ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n *
        ∑ i, (Module.finrank k (GradedExt.{w} e (X i) Y n (-j)) : ℤ) := by
      apply Finset.sum_congr rfl
      intro n _
      have := fun i ↦ ((h i).internallyFinite.finiteLaurentSupport n).finiteDimensional (-j)
      rw [(Ext.biproductLinearEquiv k (biproduct.isBilimit X)
        ((e ^ (-j)).functor.obj Y) n).finrank_eq, Module.finrank_pi_fintype, Nat.cast_sum]
    _ = ∑ i, ∑ n ∈ Finset.range N,
        (-1 : ℤ) ^ n * (Module.finrank k (GradedExt.{w} e (X i) Y n (-j)) : ℤ) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_congr rfl fun i _ ↦ (coeff_gradedExtEuler k e (h i) (hN i) j).symm

/-- The q-Euler characteristic is additive on finite sums in the second variable. -/
@[simp]
theorem gradedExtEuler_biproduct_right {X : C} {Y : J → C}
    (hsum : IsGradedEulerAdmissible.{w} k e X (⨁ Y)) :
    gradedExtEuler k e hsum = ∑ i, gradedExtEuler k e
      ((isGradedEulerAdmissible_biproduct_right_iff X Y).1 hsum i) := by
  let h := (isGradedEulerAdmissible_biproduct_right_iff X Y).1 hsum
  obtain ⟨N, hN⟩ := exists_forall_isGradedExtBoundedBy fun i ↦ (h i).bounded
  ext j
  rw [coeff_gradedExtEuler k e _
    ((isGradedExtBoundedBy_biproduct_right_iff X Y N).2 hN)]
  simp only [AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  calc
    _ = ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n *
        ∑ i, (Module.finrank k (GradedExt.{w} e X (Y i) n (-j)) : ℤ) := by
      apply Finset.sum_congr rfl
      intro n _
      have := fun i ↦ ((h i).internallyFinite.finiteLaurentSupport n).finiteDimensional (-j)
      have hdim : Module.finrank k (GradedExt.{w} e X (⨁ Y) n (-j)) =
          Module.finrank k (∀ i, GradedExt.{w} e X (Y i) n (-j)) :=
        (Ext.linearEquivBiproduct k X
          (isBilimitOfPreserves (e ^ (-j)).functor (biproduct.isBilimit Y)) n).finrank_eq
      rw [hdim, Module.finrank_pi_fintype, Nat.cast_sum]
    _ = ∑ i, ∑ n ∈ Finset.range N,
        (-1 : ℤ) ^ n * (Module.finrank k (GradedExt.{w} e X (Y i) n (-j)) : ℤ) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_congr rfl fun i _ ↦ (coeff_gradedExtEuler k e (h i) (hN i) j).symm

end TauCeti
