/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Real
public import TauCeti.NumberTheory.QuadraticForm.Global.Localization
public import TauCeti.NumberTheory.QuadraticForm.Global.Signature

/-!
# Discriminants of localized quadratic forms

The discriminant of a regular quadratic form over a number field localizes to the image of its
global discriminant at every finite place and along every real or complex embedding.

Thus the discriminant attached to an actual localized form agrees with the square class obtained
by applying the corresponding place map to the global invariant.

At a real place the real square class of the global discriminant is a sign, and it is determined by
the signature there: it is `(-1)^q` for the negative index `q = n - p` of the localized form of
rank `n` and positive index `p`.
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

/-- At a real place, the image of the global discriminant is the class of `(-1)^q`, where `q` is
the negative index of the form at that place. -/
theorem squareClassMap_discr_formClass_eq_realNegativeIndex_nsmul
    (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate)
    (place : {w : InfinitePlace K // w.IsReal}) :
    letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
    (embedding_of_isReal place.2).squareClassMap
        (TauCeti.RegularFormClass.discr (TauCeti.formClass Q hQ)) =
      Q.realNegativeIndex place • TauCeti.squareClass (-1 : ℝˣ) := by
  rw [← discr_atRealPlace, discr_formClass_eq_sigNeg_nsmul, realNegativeIndex_eq_sigNeg]

/-- At a real place, the image of the global discriminant of a form of rank `n` and positive index
`p` is the class of `(-1)^(n - p)`. -/
theorem squareClassMap_discr_formClass_eq_finrank_sub_realPositiveIndex_nsmul
    (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate)
    (place : {w : InfinitePlace K // w.IsReal}) :
    letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
    (embedding_of_isReal place.2).squareClassMap
        (TauCeti.RegularFormClass.discr (TauCeti.formClass Q hQ)) =
      (Module.finrank K V - Q.realPositiveIndex place) • TauCeti.squareClass (-1 : ℝˣ) := by
  have hsum := realPositiveIndex_add_realNegativeIndex_eq_finrank hQ place
  rw [squareClassMap_discr_formClass_eq_realNegativeIndex_nsmul, ← hsum, Nat.add_sub_cancel_left]

/-- At a real place, the image of the global discriminant is trivial exactly when the negative
index of the form at that place is even. -/
@[simp]
theorem squareClassMap_discr_formClass_eq_zero_iff_even_realNegativeIndex
    (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate)
    (place : {w : InfinitePlace K // w.IsReal}) :
    letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
    (embedding_of_isReal place.2).squareClassMap
        (TauCeti.RegularFormClass.discr (TauCeti.formClass Q hQ)) = 0 ↔
      Even (Q.realNegativeIndex place) := by
  rw [squareClassMap_discr_formClass_eq_realNegativeIndex_nsmul,
    TauCeti.nsmul_squareClass_neg_one_eq_zero_iff_even]

end QuadraticForm
