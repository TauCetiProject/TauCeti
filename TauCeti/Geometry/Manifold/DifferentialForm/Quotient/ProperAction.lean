/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Descent
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.GroupAction.Quotient

/-!
# Basic forms for the orbit projection of a free proper Lie group action

Let a Lie group `G` act smoothly, freely and properly on a manifold `Q`, so that the orbit space
`Q ⧸ G` is a manifold and the orbit projection `Q → Q ⧸ G` is a submersion whose vertical tangent
vectors are the values of the fundamental vector fields (`ProperSMul.ker_mfderiv_quotientMk`). A
form on `Q` that is invariant under `G` and vanishes as soon as one of its arguments is the value of
a fundamental vector field is basic for the orbit projection (`ProperSMul.isBasic_quotientMk`),
hence the pullback of a unique form on `Q ⧸ G`.

This is the Lie group analogue of `TauCeti.RoughForm.isBasic_quotientMk` for properly discontinuous
actions, where the orbit projection is a local diffeomorphism and invariance alone suffices.

## Main results

* `ProperSMul.isBasic_quotientMk`: invariant forms killing the orbit directions are basic for the
  orbit projection.
-/

public section

noncomputable section

open Manifold
open scoped ContDiff Manifold

namespace ProperSMul

open TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} {G : Type*} [TopologicalSpace G]
  [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] {Q : Type*}
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q] [MulAction G Q]
  [ContMDiffSMul IG I ∞ G Q] [ProperSMul G Q] [IsCancelSMul G Q]

/-- **Invariant forms killing the orbit directions are basic.** For a free proper action, a form
on `Q` that is invariant under `G` and vanishes as soon as one of its arguments is the value of a
fundamental vector field is basic for the orbit projection `Q → Q ⧸ G`, hence the pullback of a
unique form on `Q ⧸ G`. -/
theorem isBasic_quotientMk {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
    {φ : SmoothForm I Q F k}
    (hinv : ∀ g : G, SmoothForm.mpullback (fun x : Q ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) (I' := I) g) φ = φ)
    (hvert : ∀ x (v : Fin k → TangentSpace I x) j (ξ : GroupLieAlgebra IG G),
      v j = fundamentalVectorField I ξ x → φ.val x v = 0) :
    letI := orbitRelQuotientChartedSpace IG G I Q
    RoughForm.IsBasic (V := F) 𝓘(ℝ, QuotientModelSpace EG E)
      (Quotient.mk (MulAction.orbitRel G Q)) φ.val := by
  let _ := orbitRelQuotientChartedSpace IG G I Q
  refine RoughForm.isBasic_of_mpullback_eq (σ := fun g : G ↦ (g • ·))
    (fun q ↦ (contMDiff_quotientMk q).mdifferentiableAt (by simp))
    (fun g ↦ (ContMDiffSMul.contMDiff_const_smul (I := IG) (I' := I) (n := ∞) g).mdifferentiable
      (by simp))
    (fun g ↦ funext fun _ ↦ MulAction.orbitRel.Quotient.quotient_smul_eq)
    (fun x y hxy ↦ Or.inr ?_) (fun x v j hv ↦ ?_) fun g ↦ ?_
  · obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1
      (MulAction.orbitRel_apply.1 (Quotient.exact hxy.symm))
    exact ⟨g, hg⟩
  · obtain ⟨ξ, hξ⟩ := (InfinitesimalAction.mem_orbitTangent_iff _ _).1
      ((ker_mfderiv_quotientMk (I := IG) (G := G) x).le hv)
    exact hvert x v j ξ (by rw [← hξ, InfinitesimalAction.fundamental_apply])
  · exact (SmoothForm.coe_mpullback _ _ _).symm.trans (congrArg Subtype.val (hinv g))

end ProperSMul
