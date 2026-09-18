/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.NumberTheory.NumberField.Global.Places.ScalarExtension

/-!
# Localization of quadratic forms over number fields

This file defines scalar extension of a quadratic form from a number field to its canonical
finite completions and to the real or complex field selected by an infinite place.  The
definitions use `QuadraticForm.baseChange`; in particular, their underlying spaces are genuine
tensor products over the global field rather than independently chosen local spaces.

The evaluation, nondegeneracy, localization of diagonal forms, and algebraic-compatibility
lemmas make the local forms usable without unfolding the localization definitions. They are the
common input for local isotropy, representation, and invariant comparisons over number fields.

-/

-- Provenance: TauCetiRoadmap/GlobalQuadraticForms/README.md, Layer 0.1, and Suggested.lean.

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped TensorProduct

universe u v

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type u} [Field K]

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

/-- The map from global units to real units induced by a real place. -/
def unitAtRealPlace (w : {w : InfinitePlace K // w.IsReal}) : Kˣ →* ℝˣ :=
  Units.map (embedding_of_isReal w.2).toMonoidHom

/-- The underlying value of a localized unit is its image under the real-place embedding. -/
@[simp]
theorem unitAtRealPlace_apply (w : {w : InfinitePlace K // w.IsReal}) (a : Kˣ) :
    (unitAtRealPlace w a : ℝ) = embedding_of_isReal w.2 (a : K) := by
  rfl

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

/-- A finite-dimensional nondegenerate quadratic form stays nondegenerate at every finite place. -/
theorem Nondegenerate.atFinitePlace [NumberField K] [FiniteDimensional K V]
    {Q : _root_.QuadraticForm K V} (hQ : Q.Nondegenerate) (v : HeightOneSpectrum (𝓞 K)) :
    (Q.atFinitePlace v).Nondegenerate := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  rw [atFinitePlace_def]
  exact _root_.QuadraticForm.Nondegenerate.baseChange hQ

/-- A finite-dimensional nondegenerate quadratic form stays nondegenerate at every real place. -/
theorem Nondegenerate.atRealPlace [FiniteDimensional K V]
    {Q : _root_.QuadraticForm K V} (hQ : Q.Nondegenerate) (w : {w : InfinitePlace K // w.IsReal}) :
    (Q.atRealPlace w).Nondegenerate := by
  let : CharZero K := RingHom.charZero w.1.embedding
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  rw [atRealPlace_def]
  exact _root_.QuadraticForm.Nondegenerate.baseChange hQ

/-- A finite-dimensional nondegenerate quadratic form stays nondegenerate after scalar extension
through a complex embedding. -/
theorem Nondegenerate.atComplexEmbedding [FiniteDimensional K V]
    {Q : _root_.QuadraticForm K V} (hQ : Q.Nondegenerate) (w : InfinitePlace K) :
    (Q.atComplexEmbedding w).Nondegenerate := by
  let : CharZero K := RingHom.charZero w.embedding
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℂ := w.embedding.toAlgebra
  rw [atComplexEmbedding_def]
  exact _root_.QuadraticForm.Nondegenerate.baseChange hQ

section Diagonal

variable {ι : Type*} [Fintype ι]

/-- A diagonal form localized at a finite place is canonically isometric to the diagonal form
whose coefficients are mapped into the completion. -/
def atFinitePlaceWeightedSumSquares [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a : ι → K) :
    (atFinitePlace (QuadraticMap.weightedSumSquares K a) v).IsometryEquiv
      (QuadraticMap.weightedSumSquares (v.adicCompletion K) fun i =>
        algebraMap K (v.adicCompletion K) (a i)) := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let e := baseChangeWeightedSumSquares (A := v.adicCompletion K) a
  refine { toLinearEquiv := e, map_app' := ?_ }
  intro x
  simpa only [atFinitePlace] using e.map_app' x

/-- A diagonal form localized at a real place is canonically isometric to the diagonal form
whose coefficients are evaluated at the place's real embedding. -/
def atRealPlaceWeightedSumSquares (w : {w : InfinitePlace K // w.IsReal}) (a : ι → K) :
    (atRealPlace (QuadraticMap.weightedSumSquares K a) w).IsometryEquiv
      (QuadraticMap.weightedSumSquares ℝ fun i => embedding_of_isReal w.2 (a i)) := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  let e := baseChangeWeightedSumSquares (A := ℝ) a
  refine { toLinearEquiv := e, map_app' := ?_ }
  intro x
  simpa only [atRealPlace, RingHom.algebraMap_toAlgebra] using e.map_app' x

/-- A diagonal form extended through a complex embedding is canonically isometric to the
diagonal form whose coefficients are evaluated at that embedding. -/
def atComplexEmbeddingWeightedSumSquares (w : InfinitePlace K) (a : ι → K) :
    (atComplexEmbedding (QuadraticMap.weightedSumSquares K a) w).IsometryEquiv
      (QuadraticMap.weightedSumSquares ℂ fun i => w.embedding (a i)) := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℂ := w.embedding.toAlgebra
  let e := baseChangeWeightedSumSquares (A := ℂ) a
  refine { toLinearEquiv := e, map_app' := ?_ }
  intro x
  simpa only [atComplexEmbedding, RingHom.algebraMap_toAlgebra] using e.map_app' x

/-- The underlying linear map of the finite-place diagonal isometry is the canonical distribution
of tensor product over the finite coordinate space. -/
@[simp]
theorem atFinitePlaceWeightedSumSquares_apply [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (a : ι → K)
    (x : v.FiniteScalarExtension (V := ι → K)) :
    atFinitePlaceWeightedSumSquares v a x =
      TensorProduct.piScalarRightHom K (v.adicCompletion K) (v.adicCompletion K) ι x := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  calc
    atFinitePlaceWeightedSumSquares v a x =
        baseChangeWeightedSumSquares (A := v.adicCompletion K) a x := by
      -- The specialized wrapper changes only `map_app'`; it retains the generic linear map.
      rfl
    _ = _ := baseChangeWeightedSumSquares_apply (A := v.adicCompletion K) a x

/-- The underlying linear map of the real-place diagonal isometry is the canonical distribution
of tensor product over the finite coordinate space. -/
@[simp]
theorem atRealPlaceWeightedSumSquares_apply (w : {w : InfinitePlace K // w.IsReal})
    (a : ι → K) (x : TauCeti.RealScalarExtension (V := ι → K) w) :
    let _ : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
    atRealPlaceWeightedSumSquares w a x = TensorProduct.piScalarRightHom K ℝ ℝ ι x := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  calc
    atRealPlaceWeightedSumSquares w a x = baseChangeWeightedSumSquares (A := ℝ) a x := by
      -- The specialized wrapper changes only `map_app'`; it retains the generic linear map.
      rfl
    _ = _ := baseChangeWeightedSumSquares_apply (A := ℝ) a x

/-- The underlying linear map of the complex-embedding diagonal isometry is the canonical
distribution of tensor product over the finite coordinate space. -/
@[simp]
theorem atComplexEmbeddingWeightedSumSquares_apply (w : InfinitePlace K) (a : ι → K)
    (x : w.ComplexScalarExtension (V := ι → K)) :
    let _ : Algebra K ℂ := w.embedding.toAlgebra
    atComplexEmbeddingWeightedSumSquares w a x = TensorProduct.piScalarRightHom K ℂ ℂ ι x := by
  let : Invertible (2 : K) := invertibleTwoOfInfinitePlace w
  let : Algebra K ℂ := w.embedding.toAlgebra
  calc
    atComplexEmbeddingWeightedSumSquares w a x =
        baseChangeWeightedSumSquares (A := ℂ) a x := by
      -- The specialized wrapper changes only `map_app'`; it retains the generic linear map.
      rfl
    _ = _ := baseChangeWeightedSumSquares_apply (A := ℂ) a x

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
