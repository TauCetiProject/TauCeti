/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.BaseChange
public import TauCeti.NumberTheory.QuadraticForm.Global.Localization

/-!
# Discriminants of localized quadratic forms

The discriminant of a regular quadratic form over a number field localizes to the image of its
global discriminant at every finite place and along every real or complex embedding.

Thus the discriminant attached to an actual localized form agrees with the square class obtained
by applying the corresponding place map to the global invariant.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace

universe u v

namespace QuadraticForm

variable {K : Type u} [Field K] [NumberField K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- At a finite place, the discriminant of the localized form is the image of its global
discriminant. -/
@[simp]
theorem discr_atFinitePlace (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate)
    (place : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
    letI : Invertible (2 : place.adicCompletion K) :=
      (Invertible.map (algebraMap K (place.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
    let hQv : (atFinitePlace Q place).Nondegenerate := by
      rw [atFinitePlace_def]
      exact QuadraticForm.Nondegenerate.baseChange hQ
    TauCeti.RegularFormClass.discr (TauCeti.formClass (atFinitePlace Q place) hQv) =
      (algebraMap K (place.adicCompletion K)).squareClassMap
        (TauCeti.RegularFormClass.discr (TauCeti.formClass Q hQ)) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let _ : Invertible (2 : place.adicCompletion K) :=
    (Invertible.map (algebraMap K (place.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
  let hQbase : (Q.baseChange (place.adicCompletion K)).Nondegenerate :=
    QuadraticForm.Nondegenerate.baseChange hQ
  let hQlocal : (atFinitePlace Q place).Nondegenerate := by
    rw [atFinitePlace_def]
    exact hQbase
  calc
    _ = TauCeti.RegularFormClass.discr
        (TauCeti.formClass (Q.baseChange (place.adicCompletion K)) hQbase) := by
      apply congrArg TauCeti.RegularFormClass.discr
      rw [TauCeti.formClass_eq_iff]
      have hforms : atFinitePlace Q place = Q.baseChange (place.adicCompletion K) :=
        atFinitePlace_def Q place
      rw [hforms]
      exact QuadraticMap.Equivalent.refl _
    _ = _ := QuadraticForm.discr_formClass_baseChange Q hQ

/-- At a real place, the discriminant of the localized form is the image of its global
discriminant under the place's real embedding. -/
@[simp]
theorem discr_atRealPlace (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate)
    (place : {w : InfinitePlace K // w.IsReal}) :
    letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
    let hQw : (atRealPlace Q place).Nondegenerate := by
      let _ : Algebra K ℝ := (embedding_of_isReal place.2).toAlgebra
      rw [atRealPlace_def]
      exact QuadraticForm.Nondegenerate.baseChange hQ
    TauCeti.RegularFormClass.discr (TauCeti.formClass (atRealPlace Q place) hQw) =
      (embedding_of_isReal place.2).squareClassMap
        (TauCeti.RegularFormClass.discr (TauCeti.formClass Q hQ)) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let _ : Algebra K ℝ := (embedding_of_isReal place.2).toAlgebra
  let hQbase : (Q.baseChange ℝ).Nondegenerate :=
    QuadraticForm.Nondegenerate.baseChange hQ
  let hQlocal : (atRealPlace Q place).Nondegenerate := by
    rw [atRealPlace_def]
    exact hQbase
  calc
    _ = TauCeti.RegularFormClass.discr (TauCeti.formClass (Q.baseChange ℝ) hQbase) := by
      apply congrArg TauCeti.RegularFormClass.discr
      rw [TauCeti.formClass_eq_iff]
      have hforms : atRealPlace Q place = Q.baseChange ℝ := atRealPlace_def Q place
      rw [hforms]
      exact QuadraticMap.Equivalent.refl _
    _ = _ := by
      simpa only [RingHom.algebraMap_toAlgebra] using
        (QuadraticForm.discr_formClass_baseChange (L := ℝ) Q hQ)

/-- Along a complex embedding, the discriminant of the scalar extension is the image of its
global discriminant. -/
@[simp]
theorem discr_atComplexEmbedding (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate)
    (place : InfinitePlace K) :
    letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
    let hQw : (atComplexEmbedding Q place).Nondegenerate := by
      let _ : Algebra K ℂ := place.embedding.toAlgebra
      rw [atComplexEmbedding_def]
      exact QuadraticForm.Nondegenerate.baseChange hQ
    TauCeti.RegularFormClass.discr (TauCeti.formClass (atComplexEmbedding Q place) hQw) =
      place.embedding.squareClassMap
        (TauCeti.RegularFormClass.discr (TauCeti.formClass Q hQ)) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let _ : Algebra K ℂ := place.embedding.toAlgebra
  let hQbase : (Q.baseChange ℂ).Nondegenerate :=
    QuadraticForm.Nondegenerate.baseChange hQ
  let hQlocal : (atComplexEmbedding Q place).Nondegenerate := by
    rw [atComplexEmbedding_def]
    exact hQbase
  calc
    _ = TauCeti.RegularFormClass.discr (TauCeti.formClass (Q.baseChange ℂ) hQbase) := by
      apply congrArg TauCeti.RegularFormClass.discr
      rw [TauCeti.formClass_eq_iff]
      have hforms : atComplexEmbedding Q place = Q.baseChange ℂ :=
        atComplexEmbedding_def Q place
      rw [hforms]
      exact QuadraticMap.Equivalent.refl _
    _ = _ := by
      simpa only [RingHom.algebraMap_toAlgebra] using
        (QuadraticForm.discr_formClass_baseChange (L := ℂ) Q hQ)

end QuadraticForm
