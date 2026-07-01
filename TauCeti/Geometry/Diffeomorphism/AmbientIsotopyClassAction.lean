/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Topology.Homotopy.AmbientIsotopyClassAction

/-!
# Diffeomorphisms acting on continuous ambient-isotopy classes

The geometric-topology roadmap first builds the group `Diff(M)` and then uses smooth
presentations of knots and links whose underlying maps have continuous ambient-isotopy classes.
This file records the immediate action available without adding any new smooth-isotopy
technology: a self-diffeomorphism acts on continuous ambient-isotopy classes through its
underlying self-homeomorphism.

This is a thin restriction of the ambient-homeomorphism action along
`TauCeti.Diffeomorph.toHomeomorphHom`. It does not assert that postcomposing a bundled smooth
embedding by a diffeomorphism has been bundled again; that stronger smooth-presentation action is
a later API once the required smooth-embedding composition theorem is available.

## Main results

* `TauCeti.Diffeomorph.ambientIsotopyClassMulAction`: the action of `Diff(M)` on
  `AmbientIsotopyClass X M`.
* `TauCeti.Diffeomorph.ambientIsotopyClass_smul_mk`: the representative formula.
* `TauCeti.Diffeomorph.ambientIsotopyClass_smul_eq_homeomorph_smul`: the action is the
  underlying-homeomorphism action.
-/

public section

namespace TauCeti

open scoped Manifold ContDiff
open ContinuousMap

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  {X : Type*} [TopologicalSpace X]

/-- Self-diffeomorphisms act on continuous ambient-isotopy classes. -/
instance ambientIsotopyClassMulAction : MulAction (M ≃ₘ^n⟮I, I⟯ M)
    (AmbientIsotopyClass X M) :=
  MulAction.compHom (AmbientIsotopyClass X M) (toHomeomorphHom (I := I) (M := M) (n := n))

/-- The diffeomorphism action on continuous ambient-isotopy classes is the underlying
homeomorphism action. -/
@[simp]
theorem ambientIsotopyClass_smul_eq_homeomorph_smul
    (φ : M ≃ₘ^n⟮I, I⟯ M) (x : AmbientIsotopyClass X M) :
    φ • x = φ.toHomeomorph • x := by
  rw [MulAction.compHom_smul_def, toHomeomorphHom_apply]

/-- The diffeomorphism action on representatives is postcomposition by the underlying
homeomorphism. -/
@[simp]
theorem ambientIsotopyClass_smul_mk (φ : M ≃ₘ^n⟮I, I⟯ M) (f : C(X, M)) :
    φ • AmbientIsotopyClass.mk f =
      AmbientIsotopyClass.mk ((φ.toHomeomorph : C(M, M)).comp f) :=
  ambientIsotopyClass_smul_eq_homeomorph_smul φ (AmbientIsotopyClass.mk f) ▸
    AmbientIsotopyClass.smul_mk φ.toHomeomorph f

/-- The homeomorphism-induced quotient equivalence of the underlying homeomorphism agrees with the
diffeomorphism action. -/
@[simp]
theorem ambientIsotopyClass_postcompHomeomorphEquiv_apply_eq_smul
    (φ : M ≃ₘ^n⟮I, I⟯ M) (x : AmbientIsotopyClass X M) :
    AmbientIsotopyClass.postcompHomeomorphEquiv φ.toHomeomorph x = φ • x := by
  rw [AmbientIsotopyClass.postcompHomeomorphEquiv_apply_eq_smul,
    ← ambientIsotopyClass_smul_eq_homeomorph_smul]

end Diffeomorph

end TauCeti
