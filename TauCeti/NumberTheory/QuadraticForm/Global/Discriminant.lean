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
    let hQv : (atFinitePlace Q place).Nondegenerate :=
      QuadraticForm.Nondegenerate.atFinitePlace hQ place
    TauCeti.RegularFormClass.discr (TauCeti.formClass (atFinitePlace Q place) hQv) =
      (algebraMap K (place.adicCompletion K)).squareClassMap
        (TauCeti.RegularFormClass.discr (TauCeti.formClass Q hQ)) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let _ : Invertible (2 : place.adicCompletion K) :=
    (Invertible.map (algebraMap K (place.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
  simp only [atFinitePlace_def]
  rw [QuadraticForm.formClass_baseChange Q hQ, TauCeti.RegularFormClass.discr_baseChange]

/-- At a real place, the discriminant of the localized form is the image of its global
discriminant under the place's real embedding. -/
@[simp]
theorem discr_atRealPlace (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate)
    (place : {w : InfinitePlace K // w.IsReal}) :
    letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
    let hQw : (atRealPlace Q place).Nondegenerate :=
      QuadraticForm.Nondegenerate.atRealPlace hQ place
    TauCeti.RegularFormClass.discr (TauCeti.formClass (atRealPlace Q place) hQw) =
      (embedding_of_isReal place.2).squareClassMap
        (TauCeti.RegularFormClass.discr (TauCeti.formClass Q hQ)) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let _ : Algebra K ℝ := (embedding_of_isReal place.2).toAlgebra
  simp only [atRealPlace_def]
  rw [QuadraticForm.formClass_baseChange Q hQ, TauCeti.RegularFormClass.discr_baseChange,
    RingHom.algebraMap_toAlgebra]

/-- Along a complex embedding, the discriminant of the scalar extension is the image of its
global discriminant. -/
@[simp]
theorem discr_atComplexEmbedding (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate)
    (place : InfinitePlace K) :
    letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
    let hQw : (atComplexEmbedding Q place).Nondegenerate :=
      QuadraticForm.Nondegenerate.atComplexEmbedding hQ place
    TauCeti.RegularFormClass.discr (TauCeti.formClass (atComplexEmbedding Q place) hQw) =
      place.embedding.squareClassMap
        (TauCeti.RegularFormClass.discr (TauCeti.formClass Q hQ)) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let _ : Algebra K ℂ := place.embedding.toAlgebra
  simp only [atComplexEmbedding_def]
  rw [QuadraticForm.formClass_baseChange Q hQ, TauCeti.RegularFormClass.discr_baseChange,
    RingHom.algebraMap_toAlgebra]

end QuadraticForm
