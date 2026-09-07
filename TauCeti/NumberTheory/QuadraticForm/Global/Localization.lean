/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange

/-!
# Localization of quadratic forms over number fields

This file defines scalar extension of a quadratic form from a number field to its canonical
finite completions and to the real or complex field selected by an infinite place.  The
definitions use `QuadraticForm.baseChange`; in particular, their underlying spaces are genuine
tensor products over the global field rather than independently chosen local spaces.

The evaluation and algebraic-compatibility lemmas make the local forms usable without unfolding
the localization definitions.  They are the common input for local isotropy, representation,
and invariant comparisons over number fields.

## References

* `TauCetiRoadmap/GlobalQuadraticForms/README.md`, Layer 0.1
* `TauCetiRoadmap/GlobalQuadraticForms/Suggested.lean`
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped TensorProduct

universe u v

namespace TauCeti

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- The scalar extension of `V` to the finite completion of `K` at `v`. -/
abbrev FiniteScalarExtension [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :=
  v.adicCompletion K ⊗[K] V

/-- The scalar extension of `V` to `ℝ` through the embedding belonging to a real place. -/
abbrev RealScalarExtension (w : {w : InfinitePlace K // w.IsReal}) :=
  letI : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  ℝ ⊗[K] V

/-- The scalar extension of `V` to `ℂ` through the chosen embedding of an infinite place. -/
abbrev ComplexScalarExtension (w : InfinitePlace K) :=
  letI : Algebra K ℂ := w.embedding.toAlgebra
  ℂ ⊗[K] V

/-- Finite localization preserves the rank of a quadratic space. -/
theorem finrank_finiteScalarExtension [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    Module.finrank (v.adicCompletion K) (FiniteScalarExtension (V := V) v) =
      Module.finrank K V :=
  Module.finrank_baseChange

/-- Real localization preserves the rank of a quadratic space. -/
@[simp]
theorem finrank_realScalarExtension (w : {w : InfinitePlace K // w.IsReal}) :
    Module.finrank ℝ (RealScalarExtension (V := V) w) = Module.finrank K V := by
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact Module.finrank_baseChange

/-- Scalar extension to `ℂ` through a chosen embedding preserves the rank of a quadratic space. -/
@[simp]
theorem finrank_complexScalarExtension (w : InfinitePlace K) :
    Module.finrank ℂ (ComplexScalarExtension (V := V) w) = Module.finrank K V := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  exact Module.finrank_baseChange

end TauCeti

namespace QuadraticForm

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

@[instance_reducible]
private noncomputable def invertibleTwoOfInfinitePlace (w : InfinitePlace K) :
    Invertible (2 : K) := by
  letI : CharZero K := RingHom.charZero w.embedding
  exact invertibleOfNonzero two_ne_zero

/-- The localization of a quadratic form at a finite place of a number field. -/
def atFinitePlace [NumberField K] (Q : _root_.QuadraticForm K V)
    (v : HeightOneSpectrum (𝓞 K)) :
    _root_.QuadraticForm (v.adicCompletion K) (TauCeti.FiniteScalarExtension (V := V) v) :=
  Q.baseChange (v.adicCompletion K)

/-- The localization of a quadratic form at a real place of a number field. -/
def atRealPlace (Q : _root_.QuadraticForm K V)
    (w : {w : InfinitePlace K // w.IsReal}) :
    _root_.QuadraticForm ℝ (TauCeti.RealScalarExtension (V := V) w) := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  letI : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact Q.baseChange ℝ

/-- The scalar extension of a quadratic form through the chosen complex embedding of an
infinite place. -/
def atComplexEmbedding (Q : _root_.QuadraticForm K V) (w : InfinitePlace K) :
    _root_.QuadraticForm ℂ (TauCeti.ComplexScalarExtension (V := V) w) := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  letI : Algebra K ℂ := w.embedding.toAlgebra
  exact Q.baseChange ℂ

section Evaluation

variable (Q : _root_.QuadraticForm K V)

/-- A finite localization evaluates on a pure tensor by applying the completion map to the
coefficient of the original form. -/
@[simp]
theorem atFinitePlace_tmul [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a : v.adicCompletion K) (x : V) :
    atFinitePlace Q v (a ⊗ₜ x) = algebraMap K (v.adicCompletion K) (Q x) * a ^ 2 := by
  simp [atFinitePlace, Algebra.smul_def, pow_two, mul_comm]

/-- A real localization evaluates on a pure tensor by applying the real embedding to the
coefficient of the original form. -/
@[simp]
theorem atRealPlace_tmul (w : {w : InfinitePlace K // w.IsReal}) (a : ℝ) (x : V) :
    let _ : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
    atRealPlace Q w (a ⊗ₜ x) = embedding_of_isReal w.2 (Q x) * a ^ 2 := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  simp [atRealPlace, Algebra.smul_def, RingHom.algebraMap_toAlgebra, pow_two, mul_comm]

/-- Scalar extension through a complex embedding evaluates on a pure tensor by applying the
chosen embedding to the coefficient of the original form. -/
@[simp]
theorem atComplexEmbedding_tmul (w : InfinitePlace K) (a : ℂ) (x : V) :
    let _ : Algebra K ℂ := w.embedding.toAlgebra
    atComplexEmbedding Q w (a ⊗ₜ x) = w.embedding (Q x) * a ^ 2 := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℂ := w.embedding.toAlgebra
  simp [atComplexEmbedding, Algebra.smul_def, RingHom.algebraMap_toAlgebra, pow_two, mul_comm]

end Evaluation

section Operations

variable [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))

/-- Finite localization sends the zero form to the zero form. -/
@[simp]
theorem atFinitePlace_zero :
    atFinitePlace (0 : _root_.QuadraticForm K V) v = 0 :=
  QuadraticForm.baseChange_zero

/-- Finite localization commutes with addition of forms. -/
@[simp]
theorem atFinitePlace_add (Q Q' : _root_.QuadraticForm K V) :
    atFinitePlace (Q + Q') v = atFinitePlace Q v + atFinitePlace Q' v :=
  QuadraticForm.baseChange_add Q Q'

/-- Finite localization commutes with negation of forms. -/
@[simp]
theorem atFinitePlace_neg (Q : _root_.QuadraticForm K V) :
    atFinitePlace (-Q) v = -(atFinitePlace Q v) :=
  QuadraticForm.baseChange_neg Q

/-- Finite localization commutes with subtraction of forms. -/
@[simp]
theorem atFinitePlace_sub (Q Q' : _root_.QuadraticForm K V) :
    atFinitePlace (Q - Q') v = atFinitePlace Q v - atFinitePlace Q' v :=
  QuadraticForm.baseChange_sub Q Q'

/-- Scaling before finite localization agrees with scaling by the image in the completion. -/
@[simp]
theorem atFinitePlace_smul (r : K) (Q : _root_.QuadraticForm K V) :
    atFinitePlace (r • Q) v =
      algebraMap K (v.adicCompletion K) r • atFinitePlace Q v :=
  QuadraticForm.baseChange_smul r Q

end Operations

section ArchimedeanOperations

/-- Real localization sends the zero form to the zero form. -/
@[simp]
theorem atRealPlace_zero (w : {w : InfinitePlace K // w.IsReal}) :
    atRealPlace (0 : _root_.QuadraticForm K V) w = 0 := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact QuadraticForm.baseChange_zero

/-- Real localization commutes with addition of forms. -/
@[simp]
theorem atRealPlace_add (Q Q' : _root_.QuadraticForm K V)
    (w : {w : InfinitePlace K // w.IsReal}) :
    atRealPlace (Q + Q') w = atRealPlace Q w + atRealPlace Q' w := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact QuadraticForm.baseChange_add Q Q'

/-- Real localization commutes with negation of forms. -/
@[simp]
theorem atRealPlace_neg (Q : _root_.QuadraticForm K V)
    (w : {w : InfinitePlace K // w.IsReal}) :
    atRealPlace (-Q) w = -(atRealPlace Q w) := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact QuadraticForm.baseChange_neg Q

/-- Real localization commutes with subtraction of forms. -/
@[simp]
theorem atRealPlace_sub (Q Q' : _root_.QuadraticForm K V)
    (w : {w : InfinitePlace K // w.IsReal}) :
    atRealPlace (Q - Q') w = atRealPlace Q w - atRealPlace Q' w := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact QuadraticForm.baseChange_sub Q Q'

/-- Scaling before real localization agrees with scaling by the corresponding real embedding. -/
@[simp]
theorem atRealPlace_smul (r : K) (Q : _root_.QuadraticForm K V)
    (w : {w : InfinitePlace K // w.IsReal}) :
    atRealPlace (r • Q) w = embedding_of_isReal w.2 r • atRealPlace Q w := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact QuadraticForm.baseChange_smul r Q

/-- Scalar extension through a complex embedding sends the zero form to the zero form. -/
@[simp]
theorem atComplexEmbedding_zero (w : InfinitePlace K) :
    atComplexEmbedding (0 : _root_.QuadraticForm K V) w = 0 := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℂ := w.embedding.toAlgebra
  exact QuadraticForm.baseChange_zero

/-- Scalar extension through a complex embedding commutes with addition of forms. -/
@[simp]
theorem atComplexEmbedding_add (Q Q' : _root_.QuadraticForm K V) (w : InfinitePlace K) :
    atComplexEmbedding (Q + Q') w = atComplexEmbedding Q w + atComplexEmbedding Q' w := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℂ := w.embedding.toAlgebra
  exact QuadraticForm.baseChange_add Q Q'

/-- Scalar extension through a complex embedding commutes with negation of forms. -/
@[simp]
theorem atComplexEmbedding_neg (Q : _root_.QuadraticForm K V) (w : InfinitePlace K) :
    atComplexEmbedding (-Q) w = -(atComplexEmbedding Q w) := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℂ := w.embedding.toAlgebra
  exact QuadraticForm.baseChange_neg Q

/-- Scalar extension through a complex embedding commutes with subtraction of forms. -/
@[simp]
theorem atComplexEmbedding_sub (Q Q' : _root_.QuadraticForm K V) (w : InfinitePlace K) :
    atComplexEmbedding (Q - Q') w = atComplexEmbedding Q w - atComplexEmbedding Q' w := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℂ := w.embedding.toAlgebra
  exact QuadraticForm.baseChange_sub Q Q'

/-- Scaling before extension through a complex embedding agrees with scaling by that embedding. -/
@[simp]
theorem atComplexEmbedding_smul (r : K) (Q : _root_.QuadraticForm K V)
    (w : InfinitePlace K) :
    atComplexEmbedding (r • Q) w = w.embedding r • atComplexEmbedding Q w := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℂ := w.embedding.toAlgebra
  exact QuadraticForm.baseChange_smul r Q

end ArchimedeanOperations

section Isometries

variable {W : Type*} [AddCommGroup W] [Module K W]
variable {Q : _root_.QuadraticForm K V} {R : _root_.QuadraticForm K W}

/-- An isometry of global quadratic forms extends to every finite localization. -/
def Isometry.atFinitePlace [NumberField K] (f : Q →qᵢ R)
    (v : HeightOneSpectrum (𝓞 K)) :
    atFinitePlace Q v →qᵢ atFinitePlace R v :=
  QuadraticForm.Isometry.baseChange f (v.adicCompletion K)

/-- An isometry of global quadratic forms extends to every real localization. -/
def Isometry.atRealPlace (f : Q →qᵢ R) (w : {w : InfinitePlace K // w.IsReal}) :
    atRealPlace Q w →qᵢ atRealPlace R w := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  letI : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact QuadraticForm.Isometry.baseChange f ℝ

/-- An isometry of global quadratic forms extends through every chosen complex embedding. -/
def Isometry.atComplexEmbedding (f : Q →qᵢ R) (w : InfinitePlace K) :
    atComplexEmbedding Q w →qᵢ atComplexEmbedding R w := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  letI : Algebra K ℂ := w.embedding.toAlgebra
  exact QuadraticForm.Isometry.baseChange f ℂ

/-- A global isometric equivalence extends to every finite localization. -/
def IsometryEquiv.atFinitePlace [NumberField K] (f : Q.IsometryEquiv R)
    (v : HeightOneSpectrum (𝓞 K)) :
    (atFinitePlace Q v).IsometryEquiv (atFinitePlace R v) :=
  QuadraticForm.IsometryEquiv.baseChange f (v.adicCompletion K)

/-- A global isometric equivalence extends to every real localization. -/
def IsometryEquiv.atRealPlace (f : Q.IsometryEquiv R)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (atRealPlace Q w).IsometryEquiv (atRealPlace R w) := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  letI : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact QuadraticForm.IsometryEquiv.baseChange f ℝ

/-- A global isometric equivalence extends through every chosen complex embedding. -/
def IsometryEquiv.atComplexEmbedding (f : Q.IsometryEquiv R) (w : InfinitePlace K) :
    (atComplexEmbedding Q w).IsometryEquiv (atComplexEmbedding R w) := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  letI : Algebra K ℂ := w.embedding.toAlgebra
  exact QuadraticForm.IsometryEquiv.baseChange f ℂ

/-- Equivalent global quadratic forms remain equivalent at every finite place. -/
theorem Equivalent.atFinitePlace [NumberField K] (h : Q.Equivalent R)
    (v : HeightOneSpectrum (𝓞 K)) :
    (atFinitePlace Q v).Equivalent (atFinitePlace R v) :=
  QuadraticForm.Equivalent.baseChange h (v.adicCompletion K)

/-- Equivalent global quadratic forms remain equivalent at every real place. -/
theorem Equivalent.atRealPlace (h : Q.Equivalent R)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (atRealPlace Q w).Equivalent (atRealPlace R w) := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact QuadraticForm.Equivalent.baseChange h ℝ

/-- Equivalent global quadratic forms remain equivalent after extension through every chosen
complex embedding. -/
theorem Equivalent.atComplexEmbedding (h : Q.Equivalent R) (w : InfinitePlace K) :
    (atComplexEmbedding Q w).Equivalent (atComplexEmbedding R w) := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℂ := w.embedding.toAlgebra
  exact QuadraticForm.Equivalent.baseChange h ℂ

/-- The finite localization of an orthogonal sum is canonically isometric to the orthogonal sum
of the finite localizations. -/
def prodAtFinitePlace [NumberField K] (Q : _root_.QuadraticForm K V)
    (R : _root_.QuadraticForm K W)
    (v : HeightOneSpectrum (𝓞 K)) :
    (atFinitePlace (Q.prod R) v).IsometryEquiv
      ((atFinitePlace Q v).prod (atFinitePlace R v)) :=
  QuadraticForm.baseChangeProd Q R

/-- The real localization of an orthogonal sum is canonically isometric to the orthogonal sum of
the real localizations. -/
def prodAtRealPlace (Q : _root_.QuadraticForm K V) (R : _root_.QuadraticForm K W)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (atRealPlace (Q.prod R) w).IsometryEquiv
      ((atRealPlace Q w).prod (atRealPlace R w)) := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  letI : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact QuadraticForm.baseChangeProd Q R

/-- Extension of an orthogonal sum through a complex embedding is canonically isometric to the
orthogonal sum of the extensions. -/
def prodAtComplexEmbedding (Q : _root_.QuadraticForm K V) (R : _root_.QuadraticForm K W)
    (w : InfinitePlace K) :
    (atComplexEmbedding (Q.prod R) w).IsometryEquiv
      ((atComplexEmbedding Q w).prod (atComplexEmbedding R w)) := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  letI : Algebra K ℂ := w.embedding.toAlgebra
  exact QuadraticForm.baseChangeProd Q R

end Isometries

section FiniteDimensional

variable {Q : _root_.QuadraticForm K V}

/-- A regular quadratic form stays regular at every finite place. -/
theorem Nondegenerate.atFinitePlace [NumberField K] [FiniteDimensional K V]
    (hQ : Q.Nondegenerate)
    (v : HeightOneSpectrum (𝓞 K)) : (atFinitePlace Q v).Nondegenerate := by
  exact QuadraticForm.Nondegenerate.baseChange hQ

/-- A regular quadratic form stays regular at every real place. -/
theorem Nondegenerate.atRealPlace [FiniteDimensional K V] (hQ : Q.Nondegenerate)
    (w : {w : InfinitePlace K // w.IsReal}) : (atRealPlace Q w).Nondegenerate := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact QuadraticForm.Nondegenerate.baseChange hQ

/-- A regular quadratic form stays regular after extension through every chosen complex
embedding. -/
theorem Nondegenerate.atComplexEmbedding [FiniteDimensional K V]
    (hQ : Q.Nondegenerate) (w : InfinitePlace K) :
    (atComplexEmbedding Q w).Nondegenerate := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℂ := w.embedding.toAlgebra
  exact QuadraticForm.Nondegenerate.baseChange hQ

end FiniteDimensional

end QuadraticForm
