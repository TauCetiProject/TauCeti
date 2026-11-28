/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Wirtinger
public import TauCeti.Geometry.Manifold.Complex.FormPowIntegral

/-!
# Checks: top powers of a Hermitian metric and the sign of their integral

* On `ℂ²` with the standard form `ω = dx₁ ∧ dy₁ + dx₂ ∧ dy₂`
  (`TauCeti.kahlerTwoForm (EuclideanSpace ℂ (Fin 2))`),
  `ω²(∂x₁, ∂y₁, ∂x₂, ∂y₂) = 2 = 2!`, as `ω^n = n!·dvol_g` requires.
* Against the opposite orientation the integral `∫_X ω^n` of a taming form on a nonempty compact
  complex manifold of positive dimension is negative, so the sign convention of
  `TauCeti.formPowIntegral` matters.
-/

public section

open Complex Module
open scoped ContDiff Manifold TauCeti.ComplexManifold

namespace TauCeti.FormPowIntegralChecks

/-- The real frame `(e₁, i e₁, e₂, i e₂)` of `ℂ²`, that is `(∂x₁, ∂y₁, ∂x₂, ∂y₂)`. -/
noncomputable def frame : Fin 4 → EuclideanSpace ℂ (Fin 2) :=
  ![EuclideanSpace.single 0 1, EuclideanSpace.single 0 I, EuclideanSpace.single 1 1,
    EuclideanSpace.single 1 I]

/-- **`ω²(∂x₁, ∂y₁, ∂x₂, ∂y₂) = 2`** for the standard Kähler form `ω` of `ℂ²`. -/
theorem kahlerTwoForm_wedgePow_two_frame :
    (kahlerTwoForm (EuclideanSpace ℂ (Fin 2))).wedgePow 2 frame = 2 := by
  let b : Fin 2 × Fin 2 → EuclideanSpace ℂ (Fin 2) :=
    fun p ↦ EuclideanSpace.single p.1 (if p.2 = 0 then 1 else I)
  have h := ContinuousAlternatingMap.wedgePow_apply_finProdFinEquiv
    (kahlerTwoForm (EuclideanSpace ℂ (Fin 2))) b
    (fun i j ↦ by
      by_cases hij : i = j
      · subst hij
        simp [b]
      · simp [b, EuclideanSpace.inner_single_left, Ne.symm hij])
    (fun i j ↦ by
      by_cases hij : i = j
      · subst hij
        simp [b, EuclideanSpace.inner_single_left]
      · simp [b, EuclideanSpace.inner_single_left, hij])
  have hb : (fun r ↦ b (finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 2) r))) = frame := by
    funext r
    rw [finProdFinEquiv_symm_apply]
    fin_cases r <;> simp [frame, b, Fin.divNat, Fin.modNat]
  rw [hb] at h
  simpa using h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NeZero (finrank ℂ E)] {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold 𝓘(ℂ, E) ∞ X] [CompactSpace X] [Nonempty X]

/-- **The opposite orientation gives a negative volume.** For a two-form `κ` taming the complex
structure of a nonempty compact complex manifold of positive dimension, `∫_X κ^n` against the
opposite of the canonical orientation is negative. -/
theorem integralTopForm_neg_complexManifoldOrientation_wedgePow_neg {κ : SmoothTwoForm 𝓘(ℝ, E) X}
    (hκ : κ.Tames (SmoothAlmostComplexStructure.ofComplexManifold E X)) :
    integralTopForm (-complexManifoldOrientation E X)
      (fun x ↦ (1 : X → ℝ) x • (SmoothForm.wedgePow κ (finrank ℂ E)).val x) < 0 := by
  rw [integralTopForm_neg, neg_lt_zero]
  exact (formPowIntegral_def κ 1).symm ▸ hκ.formPowIntegral_one_pos

end TauCeti.FormPowIntegralChecks
