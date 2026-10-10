/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import TauCeti.Analysis.Normed.Operator.SylvesterBoundedInverse

/-!
# Sylvester estimates with a partial left block

The Banach-space estimate for `A X - X B = C` only needs the left block to be
defined on the range of `X` and to have an everywhere-defined bounded inverse.
This module states that domain-aware form directly for Mathlib `LinearPMap`.

The proof is the same fixed-point estimate as for a bounded left block.  No
inner product, completeness, closedness, or spectral theory enters the bound.
-/

public section

namespace LinearPMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The domain-aware equation `A X - X B = C` with a partial left block and a
bounded right block. -/
structure BoundedRightSylvesterEquation
    (A : E →ₗ.[𝕜] E) (B : F →L[𝕜] F)
    (X C : F →L[𝕜] E) : Prop where
  mapsTo_domain : ∀ x : F, X x ∈ A.domain
  equation : ∀ x : F,
    A ⟨X x, mapsTo_domain x⟩ - X (B x) = C x

/-- A partial linear map with an everywhere-defined bounded left inverse.

Only this half of invertibility is used in the Davis--Kahan fixed-point estimate:
the inverse is applied after `A` to vectors already known to lie in `A.domain`.
Surjectivity of `A` is neither stated in Theorem 5.1 nor needed by its proof. -/
structure BoundedEverywhereLeftInverseData (A : E →ₗ.[𝕜] E) where
  /-- A bounded operator that is a left inverse on the domain of `A`. -/
  inv : E →L[𝕜] E
  inv_apply : ∀ x : A.domain, inv (A x) = (x : E)

/-- A partial linear map with an everywhere-defined bounded two-sided inverse. -/
structure BoundedEverywhereInverseData (A : E →ₗ.[𝕜] E) where
  /-- The bounded everywhere-defined inverse of `A`. -/
  inv : E →L[𝕜] E
  inv_mapsTo_domain : ∀ y : E, inv y ∈ A.domain
  apply_inv : ∀ y : E, A ⟨inv y, inv_mapsTo_domain y⟩ = y
  inv_apply : ∀ x : A.domain, inv (A x) = (x : E)

/-- Forget the right-inverse half of a bounded everywhere inverse. -/
def BoundedEverywhereInverseData.toBoundedEverywhereLeftInverseData
    {A : E →ₗ.[𝕜] E} (hA : BoundedEverywhereInverseData A) :
    BoundedEverywhereLeftInverseData A where
  inv := hA.inv
  inv_apply := hA.inv_apply

/-- A partial-left Sylvester equation has the bounded fixed-point form as soon
as the partial operator has an everywhere-defined bounded left inverse. -/
theorem eq_leftInverse_comp_add_of_boundedRight_sylvester
    {A : E →ₗ.[𝕜] E} (hA : BoundedEverywhereLeftInverseData A)
    {B : F →L[𝕜] F} {X C : F →L[𝕜] E}
    (hEq : BoundedRightSylvesterEquation A B X C) :
    X = hA.inv ∘L C + hA.inv ∘L (X ∘L B) := by
  apply ContinuousLinearMap.ext
  intro x
  let u : A.domain := ⟨X x, hEq.mapsTo_domain x⟩
  have heq : A u = C x + X (B x) := sub_eq_iff_eq_add.mp (hEq.equation x)
  change X x = hA.inv (C x) + hA.inv (X (B x))
  calc
    X x = hA.inv (A u) := by simpa [u] using (hA.inv_apply u).symm
    _ = hA.inv (C x + X (B x)) := by rw [heq]
    _ = hA.inv (C x) + hA.inv (X (B x)) := by
      exact hA.inv.map_add (C x) (X (B x))

/-- A partial-left Sylvester equation has the same bounded fixed-point form as
the bounded-left equation once the partial operator has a bounded inverse. -/
theorem eq_inverse_comp_add_of_boundedRight_sylvester
    {A : E →ₗ.[𝕜] E} (hA : BoundedEverywhereInverseData A)
    {B : F →L[𝕜] F} {X C : F →L[𝕜] E}
    (hEq : BoundedRightSylvesterEquation A B X C) :
    X = hA.inv ∘L C + hA.inv ∘L (X ∘L B) :=
  eq_leftInverse_comp_add_of_boundedRight_sylvester
    hA.toBoundedEverywhereLeftInverseData hEq

/-- The partial-left Banach Sylvester estimate for any compatible operator
size, assuming only an everywhere-defined bounded left inverse. -/
theorem opNorm_le_of_boundedRight_sylvester_of_everywhereLeftInverse
    {N : (F →L[𝕜] E) → ℝ}
    (hadd : ∀ f g : F →L[𝕜] E, N (f + g) ≤ N f + N g)
    (hidealL : ∀ (D : E →L[𝕜] E) (f : F →L[𝕜] E), N (D ∘L f) ≤ ‖D‖ * N f)
    (hidealR : ∀ (f : F →L[𝕜] E) (D : F →L[𝕜] F), N (f ∘L D) ≤ N f * ‖D‖)
    (hNnonneg : ∀ f : F →L[𝕜] E, 0 ≤ N f)
    {A : E →ₗ.[𝕜] E} (hA : BoundedEverywhereLeftInverseData A)
    {B : F →L[𝕜] F} {X C : F →L[𝕜] E} {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hInvNorm : ‖hA.inv‖ ≤ (ρ + δ)⁻¹) (hB : ‖B‖ ≤ ρ)
    (hEq : BoundedRightSylvesterEquation A B X C) :
    δ * N X ≤ N C :=
  ContinuousLinearMap.opNorm_le_of_leftInverse_fixedPoint
    hadd hidealL hidealR hNnonneg hρ hδ hInvNorm hB
      (eq_leftInverse_comp_add_of_boundedRight_sylvester hA hEq)

/-- The partial-left Banach Sylvester estimate for any compatible operator size. -/
theorem opNorm_le_of_boundedRight_sylvester_of_everywhereInverse
    {N : (F →L[𝕜] E) → ℝ}
    (hadd : ∀ f g : F →L[𝕜] E, N (f + g) ≤ N f + N g)
    (hidealL : ∀ (D : E →L[𝕜] E) (f : F →L[𝕜] E), N (D ∘L f) ≤ ‖D‖ * N f)
    (hidealR : ∀ (f : F →L[𝕜] E) (D : F →L[𝕜] F), N (f ∘L D) ≤ N f * ‖D‖)
    (hNnonneg : ∀ f : F →L[𝕜] E, 0 ≤ N f)
    {A : E →ₗ.[𝕜] E} (hA : BoundedEverywhereInverseData A)
    {B : F →L[𝕜] F} {X C : F →L[𝕜] E} {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hInvNorm : ‖hA.inv‖ ≤ (ρ + δ)⁻¹) (hB : ‖B‖ ≤ ρ)
    (hEq : BoundedRightSylvesterEquation A B X C) :
    δ * N X ≤ N C :=
  opNorm_le_of_boundedRight_sylvester_of_everywhereLeftInverse
    hadd hidealL hidealR hNnonneg hA.toBoundedEverywhereLeftInverseData
      hρ hδ hInvNorm hB hEq

/-- The partial-left Banach Sylvester estimate at the ordinary operator norm. -/
theorem norm_le_of_boundedRight_sylvester_of_everywhereInverse
    {A : E →ₗ.[𝕜] E} (hA : BoundedEverywhereInverseData A)
    {B : F →L[𝕜] F} {X C : F →L[𝕜] E} {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hInvNorm : ‖hA.inv‖ ≤ (ρ + δ)⁻¹) (hB : ‖B‖ ≤ ρ)
    (hEq : BoundedRightSylvesterEquation A B X C) :
    δ * ‖X‖ ≤ ‖C‖ :=
  opNorm_le_of_boundedRight_sylvester_of_everywhereInverse
    (fun f g => norm_add_le f g)
    (fun D f => ContinuousLinearMap.opNorm_comp_le D f)
    (fun f D => ContinuousLinearMap.opNorm_comp_le f D)
    (fun f => norm_nonneg f)
    hA hρ hδ hInvNorm hB hEq

end LinearPMap

end
