/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Algebra.Monoid

/-!
# Local diffeomorphisms and group homomorphisms

For a group homomorphism, being a local diffeomorphism at one point implies being a local
diffeomorphism everywhere. Only smoothness of individual translations is needed; neither
finite dimensionality nor smooth inversion is required. This lets an inverse function theorem
at the identity supply local inverses throughout a Lie group.
-/

public section

open scoped ContDiff Manifold

namespace MonoidHom

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  {G' : Type*} [Group G'] [TopologicalSpace G'] [ChartedSpace H' G']
  {n : ℕ∞ω} [ContMDiffConstSMul I n G G] [ContMDiffConstSMul I' n G' G']

/-- A group homomorphism is a local diffeomorphism everywhere if and only if it is one at any
chosen point. Smoothness of individual left translations suffices. -/
theorem isLocalDiffeomorph_iff_isLocalDiffeomorphAt (f : G →* G') (a : G) :
    IsLocalDiffeomorph I I' n f ↔ IsLocalDiffeomorphAt I I' n f a := by
  refine ⟨fun hf ↦ hf a, fun hf x ↦ ?_⟩
  have hleft := (Diffeomorph.constSmul I n (a * x⁻¹) (M := G)).isLocalDiffeomorph x
  have hcomp := hleft.comp (hg := by simpa [smul_eq_mul, mul_assoc] using hf)
  have h := hcomp.comp
    (hg := (Diffeomorph.constSmul I' n (f (x * a⁻¹)) (M := G')).isLocalDiffeomorph _)
  convert h using 1
  funext y
  simp [Function.comp_def, smul_eq_mul, ← map_mul, mul_assoc]

end MonoidHom
