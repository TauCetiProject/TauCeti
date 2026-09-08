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

-/

-- Provenance: TauCetiRoadmap/GlobalQuadraticForms/README.md, Layer 0.1, and Suggested.lean.

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped TensorProduct

universe u v

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- The scalar extension of `V` to the finite completion of `K` at `v`. -/
abbrev FiniteScalarExtension [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :=
  v.adicCompletion K ⊗[K] V

/-- The map from global units to units in the completion at a finite place. -/
def unitAtFinitePlace [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    Kˣ →* (v.adicCompletion K)ˣ :=
  Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom

end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- The scalar extension of `V` to `ℝ` through the embedding belonging to a real place. -/
abbrev RealScalarExtension (w : {w : InfinitePlace K // w.IsReal}) :=
  letI : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  ℝ ⊗[K] V

/-- The map from global units to real units induced by a real place. -/
def unitAtRealPlace (w : {w : InfinitePlace K // w.IsReal}) : Kˣ →* ℝˣ :=
  Units.map (embedding_of_isReal w.2).toMonoidHom

end TauCeti

namespace NumberField.InfinitePlace

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- The scalar extension of `V` to `ℂ` through the chosen embedding of an infinite place. -/
abbrev ComplexScalarExtension (w : InfinitePlace K) :=
  letI : Algebra K ℂ := w.embedding.toAlgebra
  ℂ ⊗[K] V

end NumberField.InfinitePlace

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
    _root_.QuadraticForm (v.adicCompletion K) (v.FiniteScalarExtension (V := V)) :=
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
    _root_.QuadraticForm ℂ (w.ComplexScalarExtension (V := V)) := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  letI : Algebra K ℂ := w.embedding.toAlgebra
  exact Q.baseChange ℂ

/-- Finite localization is base change along the canonical map to the completion. -/
theorem atFinitePlace_def [NumberField K] (Q : _root_.QuadraticForm K V)
    (v : HeightOneSpectrum (𝓞 K)) :
    atFinitePlace Q v = Q.baseChange (v.adicCompletion K) := by
  apply _root_.baseChange_ext
  intro x
  simp [atFinitePlace]

/-- Real localization is base change along the embedding belonging to the real place. -/
theorem atRealPlace_def (Q : _root_.QuadraticForm K V)
    (w : {w : InfinitePlace K // w.IsReal}) :
    let _ : Invertible (2 : K) := by
      letI : CharZero K := RingHom.charZero w.1.embedding
      exact invertibleOfNonzero two_ne_zero
    let _ : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
    atRealPlace Q w = Q.baseChange ℝ := by
  rfl

/-- Complex localization is base change along the chosen complex embedding. -/
theorem atComplexEmbedding_def (Q : _root_.QuadraticForm K V) (w : InfinitePlace K) :
    let _ : Invertible (2 : K) := by
      letI : CharZero K := RingHom.charZero w.embedding
      exact invertibleOfNonzero two_ne_zero
    let _ : Algebra K ℂ := w.embedding.toAlgebra
    atComplexEmbedding Q w = Q.baseChange ℂ := by
  rfl

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

end QuadraticForm
