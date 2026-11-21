/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Quotient.Covering
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local

/-!
# Deck transformations of Riemannian quotient coverings

Let a group `G` act on a Riemannian manifold `M` without boundary, and let `q : M → N` be a
quotient covering map for this action (`IsQuotientCoveringMap q G`) which is a local Riemannian
isometry onto a Riemannian manifold `N`. This is the projection `X → X / H` of a Riemannian
manifold onto its quotient by a group `H` acting freely and properly discontinuously, with the
quotient metric.

Then every deck transformation `x ↦ g • x` is a Riemannian isometry of `M`: it is smooth because
its composite with the local diffeomorphism `q` is `q`
(`IsQuotientCoveringMap.contMDiffConstSMul`), and its differential preserves the metric because
`dq_{g • x} ∘ d(g •)_x = dq_x` and both differentials of `q` preserve it. No separate hypothesis
that `G` acts by isometries is needed: it follows from `q` being a local isometry.

## Main declarations

* `IsQuotientCoveringMap.inner_mfderiv_smul`: the differential of a deck transformation preserves
  the Riemannian inner product.
* `IsQuotientCoveringMap.deckIsometry`: the deck transformation `x ↦ g • x` as a Riemannian
  isometry of `M`, with `IsQuotientCoveringMap.coe_deckIsometry`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (Riemannian coverings).
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace IsQuotientCoveringMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace I' y)]
  {G : Type*} [Group G] [MulAction G M] {q : M → N}

/-- **Deck transformations preserve the metric.** If a quotient covering map `q : M → N` is a local
Riemannian isometry, then the differential of each deck transformation `x ↦ g • x` preserves the
Riemannian inner product. -/
theorem inner_mfderiv_smul [IsManifold I 1 M] [IsManifold I' 1 N]
    (hq : IsQuotientCoveringMap q G) (hf : TauCeti.IsLocalRiemannianIsometry I I' q) (g : G)
    (x : M) (v w : TangentSpace I x) :
    ⟪mfderiv I I (g • ·) x v, mfderiv I I (g • ·) x w⟫_ℝ = ⟪v, w⟫_ℝ := by
  have := hq.contMDiffConstSMul (hf.isLocalDiffeomorph (n := 1) le_rfl (by simp))
  have hg : MDifferentiableAt I I (g • ·) x :=
    (contMDiff_const_smul (I := I) (n := 1) g).mdifferentiableAt one_ne_zero
  have hcomp : q ∘ (g • ·) = q := funext fun _ ↦ hq.map_smul g
  -- the metric of `N` is compared at `q (g • x) = q x`, so transport along `q ∘ (g • ·) = q`
  have key : ∀ p : M → N, p = q → ⟪mfderiv I I' p x v, mfderiv I I' p x w⟫_ℝ = ⟪v, w⟫_ℝ := by
    rintro p rfl
    exact hf.inner_mfderiv x v w
  have h := key _ hcomp
  rw [mfderiv_comp_apply x (hf.mdifferentiableAt _) hg,
    mfderiv_comp_apply x (hf.mdifferentiableAt _) hg] at h
  rw [← hf.inner_mfderiv (g • x)]
  exact h

variable [IsManifold I ∞ M] [IsManifold I' ∞ N]

/-- If a quotient covering map `q : M → N` for an action of `G` is a local Riemannian isometry,
then `G` acts on `M` by smooth maps. -/
theorem contMDiffConstSMul_of_isLocalRiemannianIsometry (hq : IsQuotientCoveringMap q G)
    (hf : TauCeti.IsLocalRiemannianIsometry I I' q) : ContMDiffConstSMul I ∞ G M :=
  hq.contMDiffConstSMul (hf.isLocalDiffeomorph (n := ∞) (by simp) le_rfl)

/-- **Deck transformations are isometries.** If a quotient covering map `q : M → N` for an action
of `G` is a local Riemannian isometry, then each deck transformation `x ↦ g • x` is a Riemannian
isometry of `M` (`IsQuotientCoveringMap.coe_deckIsometry`). -/
def deckIsometry (hq : IsQuotientCoveringMap q G)
    (hf : TauCeti.IsLocalRiemannianIsometry I I' q) (g : G) :
    TauCeti.RiemannianIsometry I I M M :=
  letI := hq.contMDiffConstSMul_of_isLocalRiemannianIsometry hf
  TauCeti.RiemannianIsometry.constSMul g (hq.inner_mfderiv_smul hf g)

/-- The deck isometry given by `g` is the map `x ↦ g • x`. -/
@[simp]
theorem coe_deckIsometry (hq : IsQuotientCoveringMap q G)
    (hf : TauCeti.IsLocalRiemannianIsometry I I' q) (g : G) :
    ⇑(hq.deckIsometry hf g) = (g • ·) :=
  letI := hq.contMDiffConstSMul_of_isLocalRiemannianIsometry hf
  TauCeti.RiemannianIsometry.coe_constSMul

end IsQuotientCoveringMap
