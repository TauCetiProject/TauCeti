/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.EulerCharacteristic
public import TauCeti.Algebra.Category.FGModuleCat.Finrank
public import TauCeti.Algebra.Category.FGModuleCat.Homology
public import TauCeti.Algebra.Category.ModuleCat.Finrank
public import TauCeti.Algebra.Homology.Embedding.CochainComplex
public import TauCeti.CategoryTheory.GrothendieckGroup.EulerCharacteristic

/-!
# Euler--Poincaré for finite-dimensional cochain complexes

Mathlib defines the Euler characteristic of a homological complex using `finsum`.  That definition
is intentionally total: it returns zero when the summand has infinite support, and `finrank` itself
returns zero for modules that are not finite free.  This file identifies those totalized
definitions with honest finite sums for bounded cochain complexes of finite-dimensional vector
spaces, and proves that the term and homology Euler characteristics agree.

Finite-dimensionality is encoded by taking the original complex in `FGModuleCat k`.  The
characteristics are evaluated after applying the forgetful functor to `ModuleCat k`, as required by
Mathlib's definitions.  Boundedness is retained as explicit lower and upper bounds.  Thus neither
possible junk value is used in the Euler--Poincaré identity.

## Main results

* `HomologicalComplex.eulerChar_forgetFG_eq_sum_finrank`: Mathlib's term Euler characteristic is
  the finite sum over any finite set containing the bounding interval.
* `HomologicalComplex.homologyEulerChar_forgetFG_eq_sum_finrank`: Mathlib's homology Euler
  characteristic is the corresponding finite sum of the homology dimensions in `FGModuleCat k`.
* `HomologicalComplex.eulerChar_forgetFG_eq_homologyEulerChar`: the finite-dimensional
  Euler--Poincaré identity in Mathlib's Euler-characteristic API.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 1.3 and 1.6.
* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Proposition 6.6.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace HomologicalComplex

variable {k : Type u} [DivisionRing k]

/-- The finrank support of a strictly bounded complex of vector spaces lies in any interval
supplied by its bounds. -/
theorem finrankSupport_X_subset_Icc (K : CochainComplex (ModuleCat.{v} k) ℤ)
    (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b] :
    GradedObject.finrankSupport K.X ⊆ Finset.Icc a b := by
  rw [GradedObject.finrankSupport_subset_iff]
  intro n hn
  exact ModuleCat.finrank_eq_zero_of_isZero
    (K.isZero_X_of_notMem_Icc a b (fun h => hn (Finset.mem_coe.2 h)))

/-- The finrank support of the homology of a strictly bounded complex of vector spaces lies in any
interval supplied by its bounds. -/
theorem finrankSupport_homology_subset_Icc
    (K : CochainComplex (ModuleCat.{v} k) ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b] :
    GradedObject.finrankSupport (fun n => K.homology n) ⊆ Finset.Icc a b := by
  rw [GradedObject.finrankSupport_subset_iff]
  intro n hn
  exact ModuleCat.finrank_eq_zero_of_isZero
    (K.isZero_homology_of_notMem_Icc a b (fun h => hn (Finset.mem_coe.2 h)))

variable (K : CochainComplex (FGModuleCat.{v} k) ℤ)

/-- Mathlib's `finsum` Euler characteristic of a bounded complex of finite-dimensional vector
spaces is the honest finite sum of its term dimensions over any finite set containing the bounding
interval `Finset.Icc a b`.
-/
theorem eulerChar_forgetFG_eq_sum_finrank (a b : ℤ) [K.IsStrictlyGE a]
    [K.IsStrictlyLE b] {s : Finset ℤ} (hs : Finset.Icc a b ⊆ s) :
    eulerChar (((forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)).mapHomologicalComplex _).obj K) =
      ∑ n ∈ s, (n.negOnePow : ℤ) * Module.finrank k (K.X n) := by
  rw [eulerChar_eq_sum_finSet_of_finrankSupport_subset
    (((forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)).mapHomologicalComplex _).obj K) s]
  · simp only [Functor.mapHomologicalComplex_obj_X, ComplexShape.eulerCharSignsUpInt_χ,
      FGModuleCat.finrank_forget₂_obj]
  · exact (finrankSupport_X_subset_Icc
      (((forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)).mapHomologicalComplex _).obj K)
      a b).trans hs

/-- Forgetting an `FGModuleCat` complex before taking homology does not change homology finrank. -/
@[simp]
theorem finrank_homology_forget (n : ℤ) :
    Module.finrank k
      ((((forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)).mapHomologicalComplex _).obj
        K).homology n) =
      Module.finrank k (K.homology n) :=
  (TauCeti.HomologicalComplex.homologyForgetIso K n).toLinearEquiv.finrank_eq.trans
    (FGModuleCat.finrank_forget₂_obj (K.homology n))

/-- Mathlib's `finsum` homology Euler characteristic of a bounded complex of finite-dimensional
vector spaces is the honest finite sum of the dimensions of its homology objects.  The homology on
the right is computed in `FGModuleCat k`; exactness of the forgetful functor identifies it with the
homology used on the left. -/
theorem homologyEulerChar_forgetFG_eq_sum_finrank (a b : ℤ) [K.IsStrictlyGE a]
    [K.IsStrictlyLE b] {s : Finset ℤ} (hs : Finset.Icc a b ⊆ s) :
    homologyEulerChar
      (((forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)).mapHomologicalComplex _).obj K) =
      ∑ n ∈ s, (n.negOnePow : ℤ) * Module.finrank k (K.homology n) := by
  rw [homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset
    (((forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)).mapHomologicalComplex _).obj K) s]
  · apply Finset.sum_congr rfl
    intro n _
    rw [finrank_homology_forget K n]
    simp only [ComplexShape.eulerCharSignsUpInt_χ]
  · exact (finrankSupport_homology_subset_Icc
      (((forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)).mapHomologicalComplex _).obj K)
      a b).trans hs

/-- **Euler--Poincaré for a bounded finite-dimensional cochain complex.**  Mathlib's Euler
characteristic of the terms agrees with its homology Euler characteristic after forgetting a
bounded complex from `FGModuleCat k` to `ModuleCat k`.

The source category makes every term finite-dimensional, while the explicit bounds make both
`finsum`s finite.  Consequently this equality does not rely on either totalized junk value.
-/
theorem eulerChar_forgetFG_eq_homologyEulerChar (a b : ℤ) [K.IsStrictlyGE a]
    [K.IsStrictlyLE b] :
    eulerChar
        (((forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)).mapHomologicalComplex _).obj K) =
      homologyEulerChar
        (((forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)).mapHomologicalComplex _).obj K) := by
  rw [eulerChar_forgetFG_eq_sum_finrank K a b (s := Finset.Icc a b) subset_rfl,
    homologyEulerChar_forgetFG_eq_sum_finrank K a b (s := Finset.Icc a b) subset_rfl]
  have h := TauCeti.AbelianK0.AdditiveInvariant.sum_negOnePow_obj_X_eq_sum_negOnePow_obj_homology
    (TauCeti.AbelianK0.AdditiveInvariant.finrank k) K a b (s := Finset.Icc a b) subset_rfl
  simpa only [TauCeti.AbelianK0.AdditiveInvariant.finrank_obj, smul_eq_mul] using h

end HomologicalComplex
