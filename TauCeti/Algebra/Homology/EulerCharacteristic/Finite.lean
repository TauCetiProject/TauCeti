/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Finrank
public import TauCeti.Algebra.Category.FGModuleCat.Homology
public import TauCeti.Algebra.Category.ModuleCat.Finrank
public import TauCeti.Algebra.Homology.EulerCharacteristic.Basic
public import TauCeti.Algebra.Homology.Embedding.CochainComplex
public import TauCeti.CategoryTheory.GrothendieckGroup.EulerCharacteristic

/-!
# Euler--Poincaré for complexes of finitely generated modules

Mathlib defines the Euler characteristic of a homological complex using `finsum`.  That definition
is intentionally total: it returns zero when the summand has infinite support, and `finrank`
itself is the natural-number conversion of `Module.rank`, so it returns zero for modules of
infinite rank.  This file identifies those totalized definitions with honest finite sums for
bounded cochain complexes of finitely generated modules, and proves that the term and homology
Euler characteristics agree.

The coefficient ring `R` is Noetherian and satisfies the rank-nullity theorem (`HasRankNullity`).
This covers division rings, where finrank is dimension, and Noetherian commutative domains such as
`ℤ`, where finrank is the rank of the free part of a finitely generated abelian group, so that
torsion in the terms or in the homology contributes nothing.  Noetherianity keeps the homology
finitely generated, and rank-nullity makes finrank additive on short exact sequences.

Finite generation is encoded either by taking the original complex in `FGModuleCat R`, with the
characteristics evaluated after applying the forgetful functor to `ModuleCat R` as required by
Mathlib's definitions, or by an explicit hypothesis on the terms of a complex in `ModuleCat R`.
Finite generation ensures that every term and every homology object has finite rank, without
requiring freeness, and boundedness is retained as explicit lower and upper bounds.  Thus neither
possible junk value is used in the Euler--Poincaré identity.

## Main results

* `HomologicalComplex.eulerChar_forgetFG_eq_sum_finrank`: Mathlib's term Euler characteristic is
  the finite sum over any finite set containing the bounding interval.
* `HomologicalComplex.homologyEulerChar_forgetFG_eq_sum_finrank`: Mathlib's homology Euler
  characteristic is the corresponding finite sum of the homology finranks in `FGModuleCat R`.
* `HomologicalComplex.eulerChar_forgetFG_eq_homologyEulerChar`: the Euler--Poincaré identity for a
  bounded complex in `FGModuleCat R`, in Mathlib's Euler-characteristic API.
* `CochainComplex.eulerChar_eq_homologyEulerChar`: the same identity for a bounded complex in
  `ModuleCat R` whose terms are finitely generated.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 1.3 and 1.6.
* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Proposition 6.6.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace HomologicalComplex

section Ring

variable {R : Type u} [Ring R] [Nontrivial R]

/-- The finrank support of a strictly bounded complex of modules lies in any interval
supplied by its bounds. -/
theorem finrankSupport_X_subset_Icc (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b] :
    GradedObject.finrankSupport K.X ⊆ Finset.Icc a b := by
  rw [GradedObject.finrankSupport_subset_iff]
  intro n hn
  exact ModuleCat.finrank_eq_zero_of_isZero
    (K.isZero_X_of_notMem_Icc a b (fun h => hn (Finset.mem_coe.2 h)))

/-- The finrank support of the homology of a cohomologically bounded complex of modules lies
in any interval supplied by its bounds. -/
theorem finrankSupport_homology_subset_Icc
    (K : CochainComplex (ModuleCat.{v} R) ℤ) (a b : ℤ)
    [K.IsGE a] [K.IsLE b] :
    GradedObject.finrankSupport (fun n => K.homology n) ⊆ Finset.Icc a b := by
  rw [GradedObject.finrankSupport_subset_iff]
  intro n hn
  exact ModuleCat.finrank_eq_zero_of_isZero
    (K.isZero_homology_of_notMem_Icc a b (fun h => hn (Finset.mem_coe.2 h)))

/-- Mathlib's `finsum` Euler characteristic of a bounded complex of finitely generated modules is
the honest finite sum of its term finranks over any finite set containing the bounding interval
`Finset.Icc a b`.
-/
theorem eulerChar_forgetFG_eq_sum_finrank (K : CochainComplex (FGModuleCat.{v} R) ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b] {s : Finset ℤ} (hs : Finset.Icc a b ⊆ s) :
    eulerChar (((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).mapHomologicalComplex _).obj K) =
      ∑ n ∈ s, (n.negOnePow : ℤ) * Module.finrank R (K.X n) := by
  rw [eulerChar_eq_sum_finSet_of_finrankSupport_subset
    (((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).mapHomologicalComplex _).obj K) s]
  · simp only [Functor.mapHomologicalComplex_obj_X, ComplexShape.eulerCharSignsUpInt_χ,
      FGModuleCat.finrank_forget₂_obj]
  · exact (finrankSupport_X_subset_Icc
      (((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).mapHomologicalComplex _).obj K)
      a b).trans hs

end Ring

variable {R : Type u} [Ring R] [IsNoetherianRing R] (K : CochainComplex (FGModuleCat.{v} R) ℤ)

/-- Forgetting an `FGModuleCat` complex before taking homology does not change homology finrank. -/
@[simp]
theorem finrank_homology_forget (n : ℤ) :
    Module.finrank R
      ((((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).mapHomologicalComplex _).obj
        K).homology n) =
      Module.finrank R (K.homology n) :=
  (K.homologyForgetIso n).toLinearEquiv.finrank_eq.trans
    (FGModuleCat.finrank_forget₂_obj (K.homology n))

/-- Mathlib's `finsum` homology Euler characteristic of a bounded complex of finitely generated
modules is the honest finite sum of the finranks of its homology objects.  The homology on the
right is computed in `FGModuleCat R`; exactness of the forgetful functor identifies it with the
homology used on the left. -/
theorem homologyEulerChar_forgetFG_eq_sum_finrank [Nontrivial R] (a b : ℤ) [K.IsGE a]
    [K.IsLE b] {s : Finset ℤ} (hs : Finset.Icc a b ⊆ s) :
    homologyEulerChar
      (((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).mapHomologicalComplex _).obj K) =
      ∑ n ∈ s, (n.negOnePow : ℤ) * Module.finrank R (K.homology n) := by
  let F := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  let _ : CochainComplex.IsGE ((F.mapHomologicalComplex _).obj K) a := by
    rw [CochainComplex.isGE_iff]
    intro i hi
    exact (K.exactAt_of_isGE a i hi).map F
  let _ : CochainComplex.IsLE ((F.mapHomologicalComplex _).obj K) b := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    exact (K.exactAt_of_isLE b i hi).map F
  rw [homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset
    (((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).mapHomologicalComplex _).obj K) s]
  · apply Finset.sum_congr rfl
    intro n _
    rw [finrank_homology_forget K n]
    simp only [ComplexShape.eulerCharSignsUpInt_χ]
  · exact (finrankSupport_homology_subset_Icc
      (((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).mapHomologicalComplex _).obj K)
      a b).trans hs

/-- **Euler--Poincaré for a bounded cochain complex of finitely generated modules.**  Over a
Noetherian ring with the rank-nullity property, Mathlib's Euler characteristic of the terms agrees
with its homology Euler characteristic after forgetting a bounded complex from `FGModuleCat R` to
`ModuleCat R`.

The source category makes every term and homology object finitely generated, hence of finite
rank, while the explicit bounds make both `finsum`s finite.  Consequently this equality does not
rely on either totalized junk value.
-/
theorem eulerChar_forgetFG_eq_homologyEulerChar [HasRankNullity.{v} R] (a b : ℤ)
    [K.IsStrictlyGE a]
    [K.IsStrictlyLE b] :
    eulerChar
        (((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).mapHomologicalComplex _).obj K) =
      homologyEulerChar
        (((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).mapHomologicalComplex _).obj K) := by
  rw [eulerChar_forgetFG_eq_sum_finrank K a b (s := Finset.Icc a b) subset_rfl,
    homologyEulerChar_forgetFG_eq_sum_finrank K a b (s := Finset.Icc a b) subset_rfl]
  have h := TauCeti.AbelianK0.AdditiveInvariant.sum_negOnePow_obj_X_eq_sum_negOnePow_obj_homology
    (TauCeti.AbelianK0.AdditiveInvariant.finrank R) K a b (s := Finset.Icc a b) subset_rfl
  simpa only [TauCeti.AbelianK0.AdditiveInvariant.finrank_obj, smul_eq_mul] using h

end HomologicalComplex

namespace CochainComplex

variable {R : Type u} [Ring R] [IsNoetherianRing R] [HasRankNullity.{v} R]

/-- **Euler--Poincaré for a bounded cochain complex of finitely generated modules.**  Over a
Noetherian ring with the rank-nullity property, such as `ℤ`, a strictly bounded cochain complex in
`ModuleCat R` whose terms are finitely generated has the same Euler characteristic as its
homology. -/
theorem eulerChar_eq_homologyEulerChar (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (hK : ∀ n, Module.Finite R (K.X n)) (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b] :
    K.eulerChar = K.homologyEulerChar := by
  let F := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  -- Lift `K` to `FGModuleCat R`; forgetting the lift gives back `K` up to isomorphism.
  let L : CochainComplex (FGModuleCat.{v} R) ℤ :=
    K.liftObjectProperty (ModuleCat.isFG R) fun n ↦ (ModuleCat.isFG_iff _).2 (hK n)
  let e : (F.mapHomologicalComplex _).obj L ≅ K := K.liftFGModuleCatIso hK
  have : L.IsStrictlyGE a :=
    (isStrictlyGE_mapHomologicalComplex_obj_iff L F a).1 (isStrictlyGE_of_iso e.symm a)
  have : L.IsStrictlyLE b :=
    (isStrictlyLE_mapHomologicalComplex_obj_iff L F b).1 (isStrictlyLE_of_iso e.symm b)
  rw [← HomologicalComplex.eulerChar_eq_of_iso e,
    ← HomologicalComplex.homologyEulerChar_eq_of_iso e]
  exact L.eulerChar_forgetFG_eq_homologyEulerChar a b

end CochainComplex
