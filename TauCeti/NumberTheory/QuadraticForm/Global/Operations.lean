/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Localization

/-!
# Operations and regularity of localized quadratic forms

This file records how the canonical finite, real, and complex localizations of a quadratic form
interact with orthogonal products, negation, and scalar multiplication.  It also proves that
scalar extension preserves nondegeneracy, completing the finite- and real-place regularity API
alongside the existing complex-place result.

The product comparisons are isometries because scalar extension distributes over a product only
up to the canonical tensor-product equivalence.  The other comparisons are equalities of forms
on the same scalar-extended module.  Together these results let local-global arguments transport
the standard structure of a global quadratic space without unfolding the localization maps.

-/

-- Provenance: TauCetiRoadmap/GlobalQuadraticForms/README.md, Layer 0.1.

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped TensorProduct

universe u v w

namespace QuadraticForm

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]

section Product

/-- Finite localization carries an orthogonal product to the orthogonal product of the finite
localizations. -/
def atFinitePlaceProd [NumberField K] (Q : _root_.QuadraticForm K V)
    (R : _root_.QuadraticForm K W) (place : HeightOneSpectrum (𝓞 K)) :
    (atFinitePlace (Q.prod R) place).IsometryEquiv
      ((atFinitePlace Q place).prod (atFinitePlace R place)) := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let e := baseChangeProd (A := place.adicCompletion K) Q R
  refine { toLinearEquiv := e, map_app' := ?_ }
  intro x
  simpa only [atFinitePlace_def] using e.map_app' x

/-- Real localization carries an orthogonal product to the orthogonal product of the real
localizations. -/
def atRealPlaceProd (Q : _root_.QuadraticForm K V) (R : _root_.QuadraticForm K W)
    (place : {w : InfinitePlace K // w.IsReal}) :
    (atRealPlace (Q.prod R) place).IsometryEquiv
      ((atRealPlace Q place).prod (atRealPlace R place)) := by
  let : CharZero K := RingHom.charZero place.1.embedding
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℝ := (embedding_of_isReal place.2).toAlgebra
  let e := baseChangeProd (A := ℝ) Q R
  refine { toLinearEquiv := e, map_app' := ?_ }
  intro x
  simpa only [atRealPlace_def] using e.map_app' x

/-- Complex localization carries an orthogonal product to the orthogonal product of the complex
localizations. -/
def atComplexEmbeddingProd (Q : _root_.QuadraticForm K V) (R : _root_.QuadraticForm K W)
    (place : InfinitePlace K) :
    (atComplexEmbedding (Q.prod R) place).IsometryEquiv
      ((atComplexEmbedding Q place).prod (atComplexEmbedding R place)) := by
  let : CharZero K := RingHom.charZero place.embedding
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℂ := place.embedding.toAlgebra
  let e := baseChangeProd (A := ℂ) Q R
  refine { toLinearEquiv := e, map_app' := ?_ }
  intro x
  simpa only [atComplexEmbedding_def] using e.map_app' x

/-- The finite-place product isometry separates the components of a pure tensor. -/
@[simp]
theorem atFinitePlaceProd_tmul [NumberField K] (Q : _root_.QuadraticForm K V)
    (R : _root_.QuadraticForm K W) (place : HeightOneSpectrum (𝓞 K))
    (a : place.adicCompletion K) (x : V × W) :
    atFinitePlaceProd Q R place (a ⊗ₜ x) = (a ⊗ₜ x.1, a ⊗ₜ x.2) := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  calc
    atFinitePlaceProd Q R place (a ⊗ₜ x) =
        baseChangeProd (A := place.adicCompletion K) Q R (a ⊗ₜ x) := by
      -- The localized wrapper retains the generic product equivalence as its linear map.
      rfl
    _ = _ := baseChangeProd_tmul Q R a x

/-- The inverse finite-place product isometry combines pure tensors with the same scalar. -/
@[simp]
theorem atFinitePlaceProd_symm_tmul [NumberField K] (Q : _root_.QuadraticForm K V)
    (R : _root_.QuadraticForm K W) (place : HeightOneSpectrum (𝓞 K))
    (a : place.adicCompletion K) (x : V) (y : W) :
    (atFinitePlaceProd Q R place).symm (a ⊗ₜ x, a ⊗ₜ y) = a ⊗ₜ (x, y) := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  calc
    (atFinitePlaceProd Q R place).symm (a ⊗ₜ x, a ⊗ₜ y) =
        (baseChangeProd (A := place.adicCompletion K) Q R).symm
          (a ⊗ₜ x, a ⊗ₜ y) := by
      -- The localized wrapper retains the generic product equivalence as its linear map.
      rfl
    _ = _ := baseChangeProd_symm_tmul Q R a x y

/-- The real-place product isometry separates the components of a pure tensor. -/
@[simp]
theorem atRealPlaceProd_tmul (Q : _root_.QuadraticForm K V)
    (R : _root_.QuadraticForm K W) (place : {w : InfinitePlace K // w.IsReal})
    (a : ℝ) (x : V × W) :
    let _ : Algebra K ℝ := (embedding_of_isReal place.2).toAlgebra
    atRealPlaceProd Q R place (a ⊗ₜ x) = (a ⊗ₜ x.1, a ⊗ₜ x.2) := by
  let : CharZero K := RingHom.charZero place.1.embedding
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℝ := (embedding_of_isReal place.2).toAlgebra
  calc
    atRealPlaceProd Q R place (a ⊗ₜ x) =
        baseChangeProd (A := ℝ) Q R (a ⊗ₜ x) := by
      -- The localized wrapper retains the generic product equivalence as its linear map.
      rfl
    _ = _ := baseChangeProd_tmul Q R a x

/-- The inverse real-place product isometry combines pure tensors with the same scalar. -/
@[simp]
theorem atRealPlaceProd_symm_tmul (Q : _root_.QuadraticForm K V)
    (R : _root_.QuadraticForm K W) (place : {w : InfinitePlace K // w.IsReal})
    (a : ℝ) (x : V) (y : W) :
    let _ : Algebra K ℝ := (embedding_of_isReal place.2).toAlgebra
    (atRealPlaceProd Q R place).symm (a ⊗ₜ x, a ⊗ₜ y) = a ⊗ₜ (x, y) := by
  let : CharZero K := RingHom.charZero place.1.embedding
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℝ := (embedding_of_isReal place.2).toAlgebra
  calc
    (atRealPlaceProd Q R place).symm (a ⊗ₜ x, a ⊗ₜ y) =
        (baseChangeProd (A := ℝ) Q R).symm (a ⊗ₜ x, a ⊗ₜ y) := by
      -- The localized wrapper retains the generic product equivalence as its linear map.
      rfl
    _ = _ := baseChangeProd_symm_tmul Q R a x y

/-- The complex product isometry separates the components of a pure tensor. -/
@[simp]
theorem atComplexEmbeddingProd_tmul (Q : _root_.QuadraticForm K V)
    (R : _root_.QuadraticForm K W) (place : InfinitePlace K) (a : ℂ) (x : V × W) :
    let _ : Algebra K ℂ := place.embedding.toAlgebra
    atComplexEmbeddingProd Q R place (a ⊗ₜ x) = (a ⊗ₜ x.1, a ⊗ₜ x.2) := by
  let : CharZero K := RingHom.charZero place.embedding
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℂ := place.embedding.toAlgebra
  calc
    atComplexEmbeddingProd Q R place (a ⊗ₜ x) =
        baseChangeProd (A := ℂ) Q R (a ⊗ₜ x) := by
      -- The localized wrapper retains the generic product equivalence as its linear map.
      rfl
    _ = _ := baseChangeProd_tmul Q R a x

/-- The inverse complex product isometry combines pure tensors with the same scalar. -/
@[simp]
theorem atComplexEmbeddingProd_symm_tmul (Q : _root_.QuadraticForm K V)
    (R : _root_.QuadraticForm K W) (place : InfinitePlace K) (a : ℂ) (x : V) (y : W) :
    let _ : Algebra K ℂ := place.embedding.toAlgebra
    (atComplexEmbeddingProd Q R place).symm (a ⊗ₜ x, a ⊗ₜ y) = a ⊗ₜ (x, y) := by
  let : CharZero K := RingHom.charZero place.embedding
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℂ := place.embedding.toAlgebra
  calc
    (atComplexEmbeddingProd Q R place).symm (a ⊗ₜ x, a ⊗ₜ y) =
        (baseChangeProd (A := ℂ) Q R).symm (a ⊗ₜ x, a ⊗ₜ y) := by
      -- The localized wrapper retains the generic product equivalence as its linear map.
      rfl
    _ = _ := baseChangeProd_symm_tmul Q R a x y

end Product

section Negation

/-- Finite localization commutes with negation. -/
@[simp]
theorem atFinitePlace_neg [NumberField K] (Q : _root_.QuadraticForm K V)
    (place : HeightOneSpectrum (𝓞 K)) :
    atFinitePlace (-Q) place = -(atFinitePlace Q place) := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  rw [atFinitePlace_def, atFinitePlace_def, baseChange_neg]

/-- Real localization commutes with negation. -/
@[simp]
theorem atRealPlace_neg (Q : _root_.QuadraticForm K V)
    (place : {w : InfinitePlace K // w.IsReal}) :
    atRealPlace (-Q) place = -(atRealPlace Q place) := by
  let : CharZero K := RingHom.charZero place.1.embedding
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℝ := (embedding_of_isReal place.2).toAlgebra
  rw [atRealPlace_def, atRealPlace_def, baseChange_neg]

/-- Complex localization commutes with negation. -/
@[simp]
theorem atComplexEmbedding_neg (Q : _root_.QuadraticForm K V) (place : InfinitePlace K) :
    atComplexEmbedding (-Q) place = -(atComplexEmbedding Q place) := by
  let : CharZero K := RingHom.charZero place.embedding
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℂ := place.embedding.toAlgebra
  rw [atComplexEmbedding_def, atComplexEmbedding_def, baseChange_neg]

end Negation

section Scaling

/-- Finite localization turns scaling by a global scalar into scaling by its image in the
completion. -/
@[simp]
theorem atFinitePlace_smul [NumberField K] (a : K) (Q : _root_.QuadraticForm K V)
    (place : HeightOneSpectrum (𝓞 K)) :
    atFinitePlace (a • Q) place =
      algebraMap K (place.adicCompletion K) a • atFinitePlace Q place := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  rw [atFinitePlace_def, atFinitePlace_def, baseChange_smul]

/-- Real localization turns scaling by a global scalar into scaling by its value at the real
place. -/
@[simp]
theorem atRealPlace_smul (a : K) (Q : _root_.QuadraticForm K V)
    (place : {w : InfinitePlace K // w.IsReal}) :
    atRealPlace (a • Q) place = embedding_of_isReal place.2 a • atRealPlace Q place := by
  let : CharZero K := RingHom.charZero place.1.embedding
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℝ := (embedding_of_isReal place.2).toAlgebra
  rw [atRealPlace_def, atRealPlace_def, baseChange_smul, RingHom.algebraMap_toAlgebra]

/-- Complex localization turns scaling by a global scalar into scaling by its value at the
chosen embedding. -/
@[simp]
theorem atComplexEmbedding_smul (a : K) (Q : _root_.QuadraticForm K V)
    (place : InfinitePlace K) :
    atComplexEmbedding (a • Q) place = place.embedding a • atComplexEmbedding Q place := by
  let : CharZero K := RingHom.charZero place.embedding
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℂ := place.embedding.toAlgebra
  rw [atComplexEmbedding_def, atComplexEmbedding_def, baseChange_smul,
    RingHom.algebraMap_toAlgebra]

end Scaling

section Nondegenerate

variable [FiniteDimensional K V]

/-- A nondegenerate form remains nondegenerate at every finite place. -/
theorem Nondegenerate.atFinitePlace [NumberField K] {Q : _root_.QuadraticForm K V}
    (hQ : Q.Nondegenerate) (place : HeightOneSpectrum (𝓞 K)) :
    (Q.atFinitePlace place).Nondegenerate := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  rw [atFinitePlace_def]
  exact QuadraticForm.Nondegenerate.baseChange hQ

/-- A nondegenerate form remains nondegenerate at every real place. -/
theorem Nondegenerate.atRealPlace {Q : _root_.QuadraticForm K V} (hQ : Q.Nondegenerate)
    (place : {w : InfinitePlace K // w.IsReal}) :
    (Q.atRealPlace place).Nondegenerate := by
  let : CharZero K := RingHom.charZero place.1.embedding
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℝ := (embedding_of_isReal place.2).toAlgebra
  rw [atRealPlace_def]
  exact QuadraticForm.Nondegenerate.baseChange hQ

end Nondegenerate

end QuadraticForm
