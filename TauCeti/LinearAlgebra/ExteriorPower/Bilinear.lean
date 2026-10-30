/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Multilinear

/-!
# Bilinear maps on the exterior square

A quadrilinear map alternating in each consecutive pair descends uniquely to a bilinear
map on the second exterior power. Pair interchange becomes symmetry of the descended map.
This supplies the algebraic passage from a metric-lowered curvature tensor to a form on
bivectors, without choosing a basis.
-/

public section

namespace LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Descend a quadrilinear map alternating in each pair to the exterior square. -/
noncomputable def exteriorSquareBilinear
    (T : M →ₗ[R] M →ₗ[R] M →ₗ[R] M →ₗ[R] N)
    (h₁ : ∀ x z w, T x x z w = 0) (h₂ : ∀ x y, (T x y).IsAlt) :
    (⋀[R]^2 M) →ₗ[R] (⋀[R]^2 M) →ₗ[R] N :=
  exteriorPower.alternatingMapLinearEquiv <|
    -- Keep the proof ascribed to IsAlt so the alternating-map evaluation lemma applies.
    (show (LinearMap.mk₂ R
      (fun x y ↦ exteriorPower.alternatingMapLinearEquiv
        (IsAlt.toAlternatingMap (ω := T x y) (h₂ x y)))
      (by intros; ext v; simp)
      (by intros; ext v; simp)
      (by intros; ext v; simp)
      (by intros; ext v; simp)).IsAlt from
        fun x ↦ by ext v; simp [h₁]).toAlternatingMap

/-- The descended map evaluates on pure wedges as the original quadrilinear map. -/
@[simp]
theorem exteriorSquareBilinear_ιMulti_ιMulti
    (T : M →ₗ[R] M →ₗ[R] M →ₗ[R] M →ₗ[R] N)
    (h₁ : ∀ x z w, T x x z w = 0) (h₂ : ∀ x y, (T x y).IsAlt)
    (v w : Fin 2 → M) :
    T.exteriorSquareBilinear h₁ h₂ (exteriorPower.ιMulti R 2 v)
      (exteriorPower.ιMulti R 2 w) = T (v 0) (v 1) (w 0) (w 1) := by
  simp only [exteriorSquareBilinear,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, IsAlt.toAlternatingMap_apply,
    mk₂_apply]

/-- The descended map is characterized by its values on pure wedges. -/
theorem exteriorSquareBilinear_eq_iff
    (T : M →ₗ[R] M →ₗ[R] M →ₗ[R] M →ₗ[R] N)
    (h₁ : ∀ x z w, T x x z w = 0) (h₂ : ∀ x y, (T x y).IsAlt)
    (B : (⋀[R]^2 M) →ₗ[R] (⋀[R]^2 M) →ₗ[R] N) :
    T.exteriorSquareBilinear h₁ h₂ = B ↔
      ∀ v w : Fin 2 → M, B (exteriorPower.ιMulti R 2 v)
        (exteriorPower.ιMulti R 2 w) = T (v 0) (v 1) (w 0) (w 1) := by
  constructor
  · rintro rfl v w
    exact exteriorSquareBilinear_ιMulti_ιMulti T h₁ h₂ v w
  · intro h
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    simpa using (h v w).symm

/-- Pair interchange of a quadrilinear map gives symmetry on the exterior square. -/
theorem flip_exteriorSquareBilinear
    (T : M →ₗ[R] M →ₗ[R] M →ₗ[R] M →ₗ[R] N)
    (h₁ : ∀ x z w, T x x z w = 0) (h₂ : ∀ x y, (T x y).IsAlt)
    (h : ∀ x y z w, T x y z w = T z w x y) :
    (T.exteriorSquareBilinear h₁ h₂).flip = T.exteriorSquareBilinear h₁ h₂ := by
  symm
  rw [exteriorSquareBilinear_eq_iff]
  intro v w
  simpa using h (w 0) (w 1) (v 0) (v 1)

end LinearMap
