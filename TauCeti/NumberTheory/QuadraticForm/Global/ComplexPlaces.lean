/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Complex
public import TauCeti.NumberTheory.QuadraticForm.Global.ArchimedeanClassification
public import TauCeti.NumberTheory.QuadraticForm.Global.Predicates

/-!
# Complex places in local-to-global statements for quadratic forms

The local predicates `QuadraticForm.IsLocallyIsotropic`, `QuadraticForm.LocallyRepresentsScalar`,
`QuadraticForm.LocallyRepresents`, and `QuadraticForm.LocallyEquivalent` only quantify over the
finite and real places of a number field.  This file proves that each of them already implies the
corresponding statement after scalar extension along the complex embedding of every infinite
place; for `LocallyRepresents` and `LocallyEquivalent`, the forms are finite-dimensional and
nondegenerate.  Consequently, adjoining complex clauses under these hypotheses changes none of
the local-to-global statements formulated with them.

The complex clause is supplied by the classification of quadratic forms over an algebraically
closed field: rank at least two forces isotropy, a nonzero form represents every scalar, and
regular forms are represented or classified by their dimension alone.  The finite-place clauses
supply the missing input in the degenerate cases.  A form on a space of dimension at most one
that is isotropic at one finite place is already isotropic over the number field, and a scalar
represented at one finite place is either zero or represented by a nonzero form.  Representation
is stated for regular forms, where dimension is the only complex invariant.

## Main results

* `QuadraticForm.IsLocallyIsotropic.not_anisotropic_atComplexEmbedding`
* `QuadraticForm.LocallyRepresentsScalar.represents_atComplexEmbedding`
* `QuadraticForm.LocallyRepresents.isRepresentedBy_atComplexEmbedding`
* `QuadraticForm.LocallyEquivalent.equivalent_atComplexEmbedding`
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped TensorProduct

universe u v w

namespace QuadraticForm

variable {K : Type u} [Field K] [NumberField K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]

/-- A locally isotropic quadratic form is isotropic after scalar extension along the complex
embedding of every infinite place. -/
theorem IsLocallyIsotropic.not_anisotropic_atComplexEmbedding [FiniteDimensional K V]
    {Q : _root_.QuadraticForm K V} (h : Q.IsLocallyIsotropic) (w : InfinitePlace K) :
    ¬ (Q.atComplexEmbedding w).Anisotropic := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  rw [atComplexEmbedding_def]
  rcases le_or_gt (Module.finrank K V) 1 with hV | hV
  · -- In dimension at most one, isotropy at a finite place is already isotropy over `K`.
    have hQ := ((isLocallyIsotropic_iff Q).1 h).1 (Classical.arbitrary _)
    rw [atFinitePlace_def, anisotropic_baseChange_iff_of_finrank_le_one hV] at hQ
    exact not_anisotropic_baseChange hQ
  · exact _root_.QuadraticForm.not_anisotropic_of_isAlgClosed _
      (by rw [Module.finrank_baseChange]; omega)

/-- A scalar that a quadratic form represents locally is represented after scalar extension along
the complex embedding of every infinite place. -/
theorem LocallyRepresentsScalar.represents_atComplexEmbedding
    {Q : _root_.QuadraticForm K V} {a : K} (h : Q.LocallyRepresentsScalar a)
    (w : InfinitePlace K) :
    QuadraticMap.Represents (Q.atComplexEmbedding w) (w.embedding a) := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  -- A nonzero scalar represented at a finite place forces the form to be nonzero.
  have hQ : Q ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := (QuadraticMap.represents_iff _ _).1
      (((locallyRepresentsScalar_iff _ a).1 h).1 (Classical.arbitrary _))
    rw [atFinitePlace_def, baseChange_zero, zero_apply, eq_comm,
      map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective K _)] at hx
    exact ha hx
  refine _root_.QuadraticForm.represents_of_ne_zero_of_isAlgClosed ?_ _
  rw [atComplexEmbedding_def]
  exact baseChange_eq_zero_iff.not.mpr hQ

/-- If one regular quadratic form is locally represented by another, then it is represented by the
other after scalar extension along the complex embedding of every infinite place. -/
theorem LocallyRepresents.isRepresentedBy_atComplexEmbedding [FiniteDimensional K V]
    [FiniteDimensional K W] {Q : _root_.QuadraticForm K V} {R : _root_.QuadraticForm K W}
    (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) (h : Q.LocallyRepresents R)
    (w : InfinitePlace K) :
    (Q.atComplexEmbedding w).IsRepresentedBy (R.atComplexEmbedding w) := by
  -- Local representation bounds the dimension, the only invariant over `ℂ`.
  rw [_root_.QuadraticForm.isRepresentedBy_iff_finrank_le_of_isAlgClosed _ _
    (Nondegenerate.atComplexEmbedding hQ w) (Nondegenerate.atComplexEmbedding hR w)]
  simpa only [Module.finrank_baseChange] using h.finrank_le

/-- Locally equivalent regular quadratic forms are equivalent after scalar extension along the
complex embedding of every infinite place. -/
theorem LocallyEquivalent.equivalent_atComplexEmbedding [FiniteDimensional K V]
    [FiniteDimensional K W] {Q : _root_.QuadraticForm K V} {R : _root_.QuadraticForm K W}
    (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) (h : Q.LocallyEquivalent R)
    (w : InfinitePlace K) :
    (Q.atComplexEmbedding w).Equivalent (R.atComplexEmbedding w) :=
  (equivalent_atComplexEmbedding_iff_finrank_eq hQ hR w).mpr h.finrank_eq

end QuadraticForm
