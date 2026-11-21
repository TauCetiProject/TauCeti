/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Submersion
public import TauCeti.Geometry.Manifold.GroupAction.Quotient

/-!
# Descending forms to the quotient of a free proper action

Let a finite-dimensional Lie group `G` act smoothly, freely and properly on a boundaryless manifold
`M`. The orbit space `M ⧸ G` is then a manifold, and the orbit projection `π : M → M ⧸ G` is a
surjective smooth submersion whose vertical tangent vectors at `x` are the orbit directions
`𝔤 · x` (`ProperSMul.isSubmersion_quotientMk`, `ProperSMul.ker_mfderiv_quotientMk`).

A smooth form `α` on `M` that is invariant under every element of `G` and that vanishes as soon as
one of its arguments is an orbit direction is the pullback `π^* β` of exactly one smooth form `β`
on `M ⧸ G` (`ProperSMul.existsUnique_mpullback_quotientMk_eq`). At one point, vanishing on the
orbit directions makes `α_x` depend on its arguments only through their images under `dπ_x`;
invariance compares the points of one orbit. This is the general form of the descent of the
restricted symplectic form in symplectic reduction, and of the curvature of a connection to the
base of a principal bundle. For a discrete group the orbit directions are zero, and the descent
of invariant forms is `TauCeti.SmoothForm.descend`.

## Main results

* `ProperSMul.existsUnique_mpullback_quotientMk_eq`: an invariant form vanishing on the orbit
  directions is the pullback of a unique smooth form on the orbit space.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 21 (quotient manifolds) and Chapter 14 (pullbacks of
  differential forms).
-/

public section

noncomputable section

open Manifold
open scoped ContDiff Manifold

namespace ProperSMul

open TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M] [ProperSMul G M] [IsCancelSMul G M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- **Descent of basic forms to the orbit space.** For a free proper smooth action of a Lie group
`G` on `M`, a smooth form `α` on `M` that is invariant under every element of `G` and that vanishes
whenever one of its arguments is an orbit direction is the pullback of a unique smooth form on the
orbit space `M ⧸ G`. -/
theorem existsUnique_mpullback_quotientMk_eq {α : SmoothForm I' M F k}
    (hinv : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') g) α = α)
    (hvert : ∀ x (v : Fin k → TangentSpace I' x) j,
      v j ∈ (InfinitesimalAction.fundamental I G I' M).orbitTangent x → α.val x v = 0) :
    letI := orbitRelQuotientChartedSpace I G I' M
    ∃! β : SmoothForm 𝓘(ℝ, QuotientModelSpace E E') (MulAction.orbitRel.Quotient G M) F k,
      SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel G M))
        (contMDiff_quotientMk (I := I) (G := G) (I' := I') (M := M)) β = α := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  have hπ := isSubmersion_quotientMk (I := I) (G := G) (I' := I') (M := M)
  -- The form is basic: the elements of `G` are maps over `π`, transitive on its fibres.
  have hbasic : RoughForm.IsBasic (V := F) 𝓘(ℝ, QuotientModelSpace E E')
      (Quotient.mk (MulAction.orbitRel G M)) α.val := by
    refine RoughForm.isBasic_of_mpullback_eq (σ := fun g : G ↦ (g • ·))
      (hπ.contMDiff.mdifferentiable (by simp))
      (fun g ↦ (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') (n := ∞)
        g).mdifferentiable (by simp))
      (fun g ↦ funext fun x ↦
        Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit _ g)))
      (fun x y hxy ↦
        .inr (MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact hxy.symm))))
      (fun x v j hj ↦ hvert x v j (by rwa [← ker_mfderiv_quotientMk]))
      fun g ↦ by simpa only [SmoothForm.coe_mpullback] using congrArg Subtype.val (hinv g)
  exact ⟨SmoothForm.descendedForm hπ Quotient.mk_surjective α hbasic,
    SmoothForm.mpullback_descendedForm, fun β hβ ↦ SmoothForm.eq_descendedForm_iff.2 hβ⟩

end ProperSMul
