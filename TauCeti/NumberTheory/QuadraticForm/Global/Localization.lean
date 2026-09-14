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

The evaluation, diagonalization, and algebraic-compatibility lemmas make the local forms usable
without unfolding the localization definitions. They are the common input for local isotropy,
representation, and invariant comparisons over number fields.

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

/-- The underlying value of a localized unit is its image under the canonical algebra map. -/
@[simp]
theorem unitAtFinitePlace_apply [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    (unitAtFinitePlace v a : v.adicCompletion K) =
      algebraMap K (v.adicCompletion K) (a : K) := by
  rfl

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

/-- The underlying value of a localized unit is its image under the real-place embedding. -/
@[simp]
theorem unitAtRealPlace_apply (w : {w : InfinitePlace K // w.IsReal}) (a : Kˣ) :
    (unitAtRealPlace w a : ℝ) = embedding_of_isReal w.2 (a : K) := by
  rfl

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

section Diagonal

variable {ι : Type*} [Fintype ι]

/-- A diagonal form localized at a finite place is canonically isometric to the diagonal form
whose coefficients are mapped into the completion. -/
def atFinitePlaceWeightedSumSquares [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a : ι → K) :
    (atFinitePlace (QuadraticMap.weightedSumSquares K a) v).IsometryEquiv
      (QuadraticMap.weightedSumSquares (v.adicCompletion K) fun i =>
        algebraMap K (v.adicCompletion K) (a i)) := by
  classical
  refine
    { toLinearEquiv :=
        TensorProduct.piScalarRight K (v.adicCompletion K) (v.adicCompletion K) ι
      map_app' := fun x => ?_ }
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  rw [atFinitePlace_def]
  change (QuadraticMap.weightedSumSquares (v.adicCompletion K) fun i =>
      algebraMap K (v.adicCompletion K) (a i))
        (TensorProduct.piScalarRight K (v.adicCompletion K) (v.adicCompletion K) ι x) = _
  simpa only [baseChangeWeightedSumSquares_apply, TensorProduct.piScalarRight_apply] using
    (baseChangeWeightedSumSquares (A := v.adicCompletion K) a).map_app x

/-- A diagonal form localized at a real place is canonically isometric to the diagonal form
whose coefficients are evaluated at the place's real embedding. -/
def atRealPlaceWeightedSumSquares (w : {w : InfinitePlace K // w.IsReal}) (a : ι → K) :
    (atRealPlace (QuadraticMap.weightedSumSquares K a) w).IsometryEquiv
      (QuadraticMap.weightedSumSquares ℝ fun i => embedding_of_isReal w.2 (a i)) := by
  classical
  refine
    { toLinearEquiv := by
        let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
        exact TensorProduct.piScalarRight K ℝ ℝ ι
      map_app' := fun x => ?_ }
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  rw [atRealPlace_def]
  change (QuadraticMap.weightedSumSquares ℝ fun i => embedding_of_isReal w.2 (a i))
      (TensorProduct.piScalarRight K ℝ ℝ ι x) = _
  simpa only [RingHom.algebraMap_toAlgebra, baseChangeWeightedSumSquares_apply,
    TensorProduct.piScalarRight_apply] using
    (baseChangeWeightedSumSquares (A := ℝ) a).map_app x

/-- A diagonal form extended through a complex embedding is canonically isometric to the
diagonal form whose coefficients are evaluated at that embedding. -/
def atComplexEmbeddingWeightedSumSquares (w : InfinitePlace K) (a : ι → K) :
    (atComplexEmbedding (QuadraticMap.weightedSumSquares K a) w).IsometryEquiv
      (QuadraticMap.weightedSumSquares ℂ fun i => w.embedding (a i)) := by
  classical
  refine
    { toLinearEquiv := by
        let : Algebra K ℂ := w.embedding.toAlgebra
        exact TensorProduct.piScalarRight K ℂ ℂ ι
      map_app' := fun x => ?_ }
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℂ := w.embedding.toAlgebra
  rw [atComplexEmbedding_def]
  change (QuadraticMap.weightedSumSquares ℂ fun i => w.embedding (a i))
      (TensorProduct.piScalarRight K ℂ ℂ ι x) = _
  simpa only [RingHom.algebraMap_toAlgebra, baseChangeWeightedSumSquares_apply,
    TensorProduct.piScalarRight_apply] using
    (baseChangeWeightedSumSquares (A := ℂ) a).map_app x

/-- On a pure tensor, the finite-place diagonal isometry maps each coordinate through the
completion map and scales it by the tensor coefficient. -/
@[simp]
theorem atFinitePlaceWeightedSumSquares_tmul [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (a : ι → K) (b : v.adicCompletion K) (x : ι → K) :
    atFinitePlaceWeightedSumSquares v a (b ⊗ₜ x) =
      fun i => b * algebraMap K (v.adicCompletion K) (x i) := by
  classical
  change TensorProduct.piScalarRight K (v.adicCompletion K) (v.adicCompletion K) ι
      (b ⊗ₜ x) = _
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  simp [Algebra.smul_def, mul_comm]

/-- On a pure tensor, the real-place diagonal isometry evaluates every coordinate at the
place's real embedding and scales it by the tensor coefficient. -/
@[simp]
theorem atRealPlaceWeightedSumSquares_tmul (w : {w : InfinitePlace K // w.IsReal})
    (a : ι → K) (b : ℝ) (x : ι → K) :
    let _ : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
    atRealPlaceWeightedSumSquares w a (b ⊗ₜ x) =
      fun i => b * embedding_of_isReal w.2 (x i) := by
  classical
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  change TensorProduct.piScalarRight K ℝ ℝ ι (b ⊗ₜ x) = _
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]

/-- On a pure tensor, the complex-embedding diagonal isometry evaluates every coordinate at the
chosen embedding and scales it by the tensor coefficient. -/
@[simp]
theorem atComplexEmbeddingWeightedSumSquares_tmul (w : InfinitePlace K)
    (a : ι → K) (b : ℂ) (x : ι → K) :
    let _ : Algebra K ℂ := w.embedding.toAlgebra
    atComplexEmbeddingWeightedSumSquares w a (b ⊗ₜ x) =
      fun i => b * w.embedding (x i) := by
  classical
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℂ := w.embedding.toAlgebra
  change TensorProduct.piScalarRight K ℂ ℂ ι (b ⊗ₜ x) = _
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]

end Diagonal

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
