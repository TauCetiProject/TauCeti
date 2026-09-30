/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Cone.FaceLocalization

/-!
# Holomorphic transitions between regular affine toric charts

When a regular cone is a face of two regular cones, its affine complex-point chart embeds
biholomorphically as an open subset of each. Passing through this common face gives a complex
partial diffeomorphism between the two ambient charts. Its domain and image are precisely the
images of the face localizations. These transitions supply the complex charts on realizations
glued from affine toric charts.

The coordinate bases and monomial generating families may be chosen independently for all three
cones. The pointwise formula characterizes the transition through the common-face chart without
referring to those choices.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.3–1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.1.
-/

public section

open scoped ContDiff Manifold
open Topology

namespace TauCeti.Toric

private theorem PartialDiffeomorph.symm_trans_symm
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {H₁ H₂ H₃ : Type*} [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace H₃]
    {I : ModelWithCorners 𝕜 E H₁} {J : ModelWithCorners 𝕜 F H₂}
    {K : ModelWithCorners 𝕜 G H₃}
    {M N P : Type*} [TopologicalSpace M] [ChartedSpace H₁ M]
    [TopologicalSpace N] [ChartedSpace H₂ N]
    [TopologicalSpace P] [ChartedSpace H₃ P]
    {n : WithTop ℕ∞} (Φ : PartialDiffeomorph I J M N n)
    (Ψ : PartialDiffeomorph I K M P n) :
    (Φ.symm.trans Ψ).symm = Ψ.symm.trans Φ := by
  rfl

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ τ υ : PointedCone ℝ V} {rσ rτ rυ kσ kτ kυ lσ lτ lυ : ℕ}

variable (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ) (hτ : IsRegularCone i τ)
  (hυσ : υ.IsFaceOf σ) (hυτ : υ.IsFaceOf τ)
  {Bσ : Module.Basis (ToricRay σ ⊕ Fin lσ) ℤ N}
  {Bτ : Module.Basis (ToricRay τ ⊕ Fin lτ) ℤ N}
  {Bυ : Module.Basis (ToricRay υ ⊕ Fin lυ) ℤ N}
  (hBσ : ∀ ρ, IsPrimitiveGenerator i ρ (Bσ (Sum.inl ρ)))
  (hBτ : ∀ ρ, IsPrimitiveGenerator i ρ (Bτ (Sum.inl ρ)))
  (hBυ : ∀ ρ, IsPrimitiveGenerator i ρ (Bυ (Sum.inl ρ)))
  (κσ : ToricRay σ ≃ Fin kσ) (κτ : ToricRay τ ≃ Fin kτ)
  (κυ : ToricRay υ ≃ Fin kυ)
  (gσ : AddGeneratingFamily (dualSemigroup hi σ) rσ)
  (gτ : AddGeneratingFamily (dualSemigroup hi τ) rτ)
  (gυ : AddGeneratingFamily (dualSemigroup hi υ) rυ)
  (n : ℕ∞ω)

/-- The holomorphic transition between two regular affine charts through a common face. Its
source is the image of the common-face chart in `σ`, and its target is that image in `τ`. -/
noncomputable def faceOverlapPartialDiffeomorph :
    let _ := affinePointTopology gσ
    let _ := affinePointTopology gτ
    let _ := coneChartedSpace hi hσ.toIsToricCone hBσ κσ gσ
    let _ := coneChartedSpace hi hτ.toIsToricCone hBτ κτ gτ
    PartialDiffeomorph 𝓘(ℂ, (Fin kσ → ℂ) × (Fin lσ → ℂ))
      𝓘(ℂ, (Fin kτ → ℂ) × (Fin lτ → ℂ))
      (AffineSemigroupComplexPoint (dualSemigroup hi σ))
      (AffineSemigroupComplexPoint (dualSemigroup hi τ)) n := by
  let hυ := hσ.of_isFaceOf hυσ
  let _ := affinePointTopology gσ
  let _ := affinePointTopology gτ
  let _ := affinePointTopology gυ
  let _ := coneChartedSpace hi hσ.toIsToricCone hBσ κσ gσ
  let _ := coneChartedSpace hi hτ.toIsToricCone hBτ κτ gτ
  let _ := coneChartedSpace hi hυ.toIsToricCone hBυ κυ gυ
  exact (hσ.faceAffinePointPartialDiffeomorph hi hυσ hBσ κσ gσ hBυ κυ gυ n).symm.trans
    (hτ.faceAffinePointPartialDiffeomorph hi hυτ hBτ κτ gτ hBυ κυ gυ n)

/-- The transition is defined exactly on the image of the common face in the first chart. -/
@[simp] theorem faceOverlapPartialDiffeomorph_source :
    (faceOverlapPartialDiffeomorph hi hσ hτ hυσ hυτ hBσ hBτ hBυ κσ κτ κυ
      gσ gτ gυ n).source = Set.range (faceAffinePointMap hi hυσ) := by
  simp [faceOverlapPartialDiffeomorph]

/-- The transition maps onto the image of the common face in the second chart. -/
@[simp] theorem faceOverlapPartialDiffeomorph_target :
    (faceOverlapPartialDiffeomorph hi hσ hτ hυσ hυτ hBσ hBτ hBυ κσ κτ κυ
      gσ gτ gυ n).target = Set.range (faceAffinePointMap hi hυτ) := by
  simp [faceOverlapPartialDiffeomorph]

/-- On a point represented in the common-face chart, the transition sends one restriction to
the other restriction. -/
@[simp] theorem faceOverlapPartialDiffeomorph_apply
    (x : AffineSemigroupComplexPoint (dualSemigroup hi υ)) :
    faceOverlapPartialDiffeomorph hi hσ hτ hυσ hυτ hBσ hBτ hBυ κσ κτ κυ
      gσ gτ gυ n (faceAffinePointMap hi hυσ x) = faceAffinePointMap hi hυτ x := by
  have hx : x ∈ (hσ.faceAffinePointPartialDiffeomorph hi hυσ hBσ κσ gσ hBυ κυ gυ n).source :=
    by simp
  have hinv := (hσ.faceAffinePointPartialDiffeomorph hi hυσ hBσ κσ gσ hBυ κυ gυ n).left_inv
    hx
  simpa [faceOverlapPartialDiffeomorph,
    IsRegularCone.faceAffinePointPartialDiffeomorph_apply] using
    congrArg (faceAffinePointMap hi hυτ) hinv

/-- Reversing the two ambient cones reverses the holomorphic overlap transition. -/
@[simp] theorem faceOverlapPartialDiffeomorph_symm :
    let _ := affinePointTopology gσ
    let _ := affinePointTopology gτ
    let _ := coneChartedSpace hi hσ.toIsToricCone hBσ κσ gσ
    let _ := coneChartedSpace hi hτ.toIsToricCone hBτ κτ gτ
    (faceOverlapPartialDiffeomorph hi hσ hτ hυσ hυτ hBσ hBτ hBυ κσ κτ κυ
      gσ gτ gυ n).symm =
      faceOverlapPartialDiffeomorph hi hτ hσ hυτ hυσ hBτ hBσ hBυ κτ κσ κυ
        gτ gσ gυ n := by
  let hυ := hσ.of_isFaceOf hυσ
  let _ := affinePointTopology gσ
  let _ := affinePointTopology gτ
  let _ := affinePointTopology gυ
  let _ := coneChartedSpace hi hσ.toIsToricCone hBσ κσ gσ
  let _ := coneChartedSpace hi hτ.toIsToricCone hBτ κτ gτ
  let _ := coneChartedSpace hi hυ.toIsToricCone hBυ κυ gυ
  unfold faceOverlapPartialDiffeomorph
  exact PartialDiffeomorph.symm_trans_symm _ _

end TauCeti.Toric
