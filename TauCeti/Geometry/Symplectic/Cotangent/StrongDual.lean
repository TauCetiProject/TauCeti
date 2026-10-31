/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Geometry.Symplectic.Cotangent.Basic
public import TauCeti.Geometry.Symplectic.SymplecticTransport

import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# The canonical symplectic form on a continuous-dual cotangent space

For a real normed space `V`, the continuous-dual cotangent model `V × StrongDual ℝ V` carries
the canonical symplectic form

`ω((v, α), (w, β)) = β(v) - α(w)`.

The form is obtained by restricting `TauCeti.cotangentSymplecticForm` along the coercion of the
continuous dual into the algebraic dual, which is why the two models agree by construction; only
nondegeneracy is new, and it comes from Hahn--Banach rather than from a basis. In finite
dimension the two models are moreover identified as symplectic vector spaces.

A continuous linear equivalence `g : V ≃L[ℝ] W` lifts to the symplectomorphism
`(q, p) ↦ (g q, p ∘ g⁻¹)` of the continuous-dual cotangent models, compatibly with identities,
composition and inverses.

## Main declarations

* `TauCeti.strongDualCotangentSymplecticForm`: the canonical symplectic form on
  `V × StrongDual ℝ V`.
* `TauCeti.strongDualCotangentZeroSection`: the zero section of `V × StrongDual ℝ V`.
* `TauCeti.strongDualCotangentEquiv`: the finite-dimensional identification with
  `V × Module.Dual ℝ V`.
* `TauCeti.isSymplectomorphism_strongDualCotangentEquiv`: that identification is a
  symplectomorphism.
* `ContinuousLinearEquiv.cotangent`: the cotangent lift `(q, p) ↦ (g q, p ∘ g⁻¹)` of a continuous
  linear equivalence `g : V ≃L[ℝ] W`.
* `ContinuousLinearEquiv.isSymplectomorphism_cotangent`: the cotangent lift is a
  symplectomorphism.
-/

public section

noncomputable section

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The bilinear form underlying the canonical symplectic form on
`V × StrongDual ℝ V`. -/
private def strongDualCotangentBilinForm :
    LinearMap.BilinForm ℝ (V × StrongDual ℝ V) :=
  (cotangentSymplecticForm (V := V)).toBilinForm.compl₁₂
    (LinearMap.prodMap LinearMap.id (ContinuousLinearMap.coeLM ℝ))
    (LinearMap.prodMap LinearMap.id (ContinuousLinearMap.coeLM ℝ))

@[simp]
private lemma strongDualCotangentBilinForm_apply (x y : V × StrongDual ℝ V) :
    strongDualCotangentBilinForm x y = y.2 x.1 - x.2 y.1 := by
  simp [strongDualCotangentBilinForm]

private lemma strongDualCotangentBilinForm_isAlt :
    (strongDualCotangentBilinForm (V := V)).IsAlt := by
  intro x
  simp

private lemma strongDualCotangentBilinForm_nondegenerate :
    (strongDualCotangentBilinForm (V := V)).Nondegenerate := by
  refine (LinearMap.IsAlt.isRefl
    strongDualCotangentBilinForm_isAlt).nondegenerate_iff_separatingLeft.mpr ?_
  rintro ⟨v, α⟩ h
  have hα : α = 0 := by
    apply ContinuousLinearMap.ext
    intro w
    have := h (w, 0)
    simpa using this
  have hv : v = 0 := by
    exact SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun β ↦ by
      have := h (0, β)
      simpa using this
  exact Prod.ext hv hα

/-- The canonical symplectic form on the normed linear cotangent space
`V × StrongDual ℝ V`. -/
noncomputable def strongDualCotangentSymplecticForm :
    SymplecticForm (V × StrongDual ℝ V) where
  toBilinForm := strongDualCotangentBilinForm
  isAlt := strongDualCotangentBilinForm_isAlt
  nondegenerate := strongDualCotangentBilinForm_nondegenerate

/-- The canonical symplectic form on the continuous-dual model has the usual evaluation formula. -/
@[simp]
lemma strongDualCotangentSymplecticForm_apply (x y : V × StrongDual ℝ V) :
    strongDualCotangentSymplecticForm x y = y.2 x.1 - x.2 y.1 := by
  exact strongDualCotangentBilinForm_apply x y

/-- The zero section in the normed linear cotangent space `V × StrongDual ℝ V`. -/
def strongDualCotangentZeroSection : Submodule ℝ (V × StrongDual ℝ V) :=
  LinearMap.range (LinearMap.inl ℝ V (StrongDual ℝ V))

/-- A point of the normed cotangent space lies in the zero section exactly when its covector
coordinate vanishes. -/
@[simp] theorem mem_strongDualCotangentZeroSection_iff (z : V × StrongDual ℝ V) :
    z ∈ strongDualCotangentZeroSection ↔ z.2 = 0 := by
  simp [strongDualCotangentZeroSection, LinearMap.range_inl]

section FiniteDimensional

variable [FiniteDimensional ℝ V]

/-- Identify the normed linear cotangent space, formed with the continuous dual, with the
algebraic linear cotangent space. -/
noncomputable def strongDualCotangentEquiv :
    (V × StrongDual ℝ V) ≃ₗ[ℝ] (V × Module.Dual ℝ V) :=
  (LinearEquiv.refl ℝ V).prodCongr LinearMap.toContinuousLinearMap.symm

/-- The identification of cotangent models forgets the continuity of the covector. -/
@[simp]
lemma strongDualCotangentEquiv_apply (x : V × StrongDual ℝ V) :
    strongDualCotangentEquiv x = (x.1, (x.2 : Module.Dual ℝ V)) := by
  simp [strongDualCotangentEquiv]

/-- The inverse identification of cotangent models promotes a covector to a continuous one. -/
@[simp]
lemma strongDualCotangentEquiv_symm_apply (x : V × Module.Dual ℝ V) :
    strongDualCotangentEquiv.symm x = (x.1, LinearMap.toContinuousLinearMap x.2) := by
  simp [strongDualCotangentEquiv]

/-- The finite-dimensional identification of cotangent models is a symplectomorphism from the
continuous-dual model to the algebraic one. -/
lemma isSymplectomorphism_strongDualCotangentEquiv :
    SymplecticForm.IsSymplectomorphism (strongDualCotangentSymplecticForm (V := V))
      (cotangentSymplecticForm (V := V)) (strongDualCotangentEquiv (V := V)) := by
  rw [SymplecticForm.isSymplectomorphism_iff]
  intro x y
  simp

end FiniteDimensional

end TauCeti

namespace ContinuousLinearEquiv

open TauCeti

variable {V W X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The **cotangent lift** `(q, p) ↦ (g q, p ∘ g⁻¹)` of a continuous linear equivalence
`g : V ≃L[ℝ] W`, as a continuous linear equivalence of the linear cotangent spaces
`V × StrongDual ℝ V` and `W × StrongDual ℝ W`. -/
def cotangent (g : V ≃L[ℝ] W) : (V × StrongDual ℝ V) ≃L[ℝ] (W × StrongDual ℝ W) :=
  g.prodCongr (g.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))

@[simp]
theorem cotangent_apply_fst (g : V ≃L[ℝ] W) (x : V × StrongDual ℝ V) :
    (g.cotangent x).1 = g x.1 :=
  (rfl)

@[simp]
theorem cotangent_apply_snd_apply (g : V ≃L[ℝ] W) (x : V × StrongDual ℝ V) (w : W) :
    (g.cotangent x).2 w = x.2 (g.symm w) :=
  (rfl)

/-- The cotangent lift of the identity is the identity. -/
@[simp]
theorem cotangent_refl :
    (ContinuousLinearEquiv.refl ℝ V).cotangent = ContinuousLinearEquiv.refl ℝ _ :=
  (rfl)

/-- The cotangent lift of a composite is the composite of the cotangent lifts. -/
@[simp]
theorem cotangent_trans (g : V ≃L[ℝ] W) (h : W ≃L[ℝ] X) :
    (g.trans h).cotangent = g.cotangent.trans h.cotangent :=
  (rfl)

/-- The inverse of the cotangent lift is the cotangent lift of the inverse. -/
@[simp]
theorem cotangent_symm (g : V ≃L[ℝ] W) : g.cotangent.symm = g.symm.cotangent :=
  (rfl)

/-- The cotangent lift of a continuous linear equivalence preserves the canonical symplectic
forms. -/
theorem strongDualCotangentSymplecticForm_cotangent (g : V ≃L[ℝ] W) (x y : V × StrongDual ℝ V) :
    strongDualCotangentSymplecticForm (g.cotangent x) (g.cotangent y) =
      strongDualCotangentSymplecticForm x y := by
  simp

/-- The cotangent lift of a continuous linear equivalence is a symplectomorphism of the linear
cotangent spaces. -/
theorem isSymplectomorphism_cotangent (g : V ≃L[ℝ] W) :
    SymplecticForm.IsSymplectomorphism strongDualCotangentSymplecticForm
      strongDualCotangentSymplecticForm g.cotangent.toLinearEquiv :=
  SymplecticForm.isSymplectomorphism_iff.2 g.strongDualCotangentSymplecticForm_cotangent

end ContinuousLinearEquiv

end
