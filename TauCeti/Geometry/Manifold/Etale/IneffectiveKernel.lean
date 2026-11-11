/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Etale.Basic
public import TauCeti.Geometry.Manifold.GroupAction.GermKernel
public import TauCeti.Topology.CategoryTheory.Groupoid.IneffectiveCovering
public import TauCeti.Topology.Covering.Degree

/-!
# Locally constant ineffective isotropy

In a Hausdorff proper étale groupoid with boundaryless object charts and `C¹` source and
target local diffeomorphisms, the ineffective arrows are closed as well as open. In a retained-arrow
isotropy chart, this is the identity principle for a finite-order smooth transformation: the
interior of its fixed-point set is closed.

Consequently the source map on ineffective arrows is a proper finite-fibre covering, and its
degree is the ineffective-kernel order. This order is locally constant both on objects and on
the coarse quotient, hence constant on each connected component. None of these constructions
assumes that the isotropy acts faithfully.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Chapter 1.
-/

public section

open CategoryTheory Set Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {C : Type*} [Groupoid C] [TopologicalSpace C] [ChartedSpace H C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsTopologicalGroupoid C] [T2Space (Quiver.Total C)]

/-- The ineffective arrows of a smooth proper étale groupoid are closed. The object model is
boundaryless, as required by the finite-order identity principle on its local action charts. -/
theorem isClosed_ineffectiveArrows
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hs : IsLocalDiffeomorph J I 1 (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I 1 (Quiver.Total.right : Quiver.Total C → C)) :
    IsClosed (ineffectiveArrows C) := by
  have : T2Space C := (IsTopologicalGroupoid.isEmbedding_unit C).t2Space
  refine closure_subset_iff_isClosed.mp ?_
  rintro ⟨x, y, f⟩ ha
  -- Any limit of ineffective arrows still has equal endpoints.
  have hsub : ineffectiveArrows C ⊆ {a : Quiver.Total C | a.left = a.right} :=
    fun _ h ↦ left_eq_right_of_mem_ineffectiveArrows h
  have hxy : x = y :=
    (isClosed_eq hs.isLocalHomeomorph.continuous ht.isLocalHomeomorph.continuous).closure_subset
      (closure_mono hsub ha)
  subst y
  have := finite_aut_of_proper_source_target hp hs.isLocalHomeomorph x
  obtain ⟨U, hxU, act, F, hsmul, -, -, -, -, hopen, -, hsource, htarget, hcentre⟩ :=
    exists_contMDiff_isotropy_action_of_proper_source_target hp hs ht
      IsTopologicalGroupoid.continuous_unit IsTopologicalGroupoid.continuous_comp x
  let : MulAction (Aut x) U := act
  let σ (g : Aut x) (z : U) : Quiver.Total C :=
    ⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) U).symm (g, z)).hom⟩
  -- A labelled arrow is ineffective precisely on the interior of its fixed-point set.
  have hpre (g : Aut x) : σ g ⁻¹' ineffectiveArrows C = interior (MulAction.fixedBy U g) := by
    ext z
    rw [mem_preimage, mem_ineffectiveArrows_iff, ← (hopen g).map_nhds_eq z,
      Filter.eventually_map, mem_interior_iff_mem_nhds]
    apply Filter.eventually_congr
    exact Filter.Eventually.of_forall fun w ↦ by
      have hl : (σ g w).left = (w : C) := congrFun (hsource g) w
      have hr : (σ g w).right = (g • w : U).val := congrFun (htarget g) w
      rw [hl, hr]
      exact ⟨fun h ↦ Subtype.ext h.symm, fun h ↦ (congrArg Subtype.val h).symm⟩
  let g : Aut x := Aut.of (asIso f)
  have hzero : σ g ⟨x, hxU⟩ = ⟨x, x, f⟩ := hcentre g
  have hcl : (⟨x, hxU⟩ : U) ∈ closure (σ g ⁻¹' ineffectiveArrows C) := by
    rw [← (hopen g).isOpenMap.preimage_closure_eq_closure_preimage (hopen g).continuous]
    rw [mem_preimage, hcentre g]
    exact ha
  rw [hpre, (isClosed_interior_fixedBy g (isOfFinOrder_of_finite g)
    (hsmul.contMDiff_const_smul g)).closure_eq] at hcl
  have hmem : σ g ⟨x, hxU⟩ ∈ ineffectiveArrows C := by
    rw [← hpre] at hcl
    exact hcl
  rwa [hzero] at hmem

/-- The ineffective-kernel order of a smooth proper étale groupoid is locally constant on
objects. It is the degree of the proper covering formed by its ineffective arrows. -/
theorem isLocallyConstant_card_ineffectiveKernel
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hs : IsLocalDiffeomorph J I 1 (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I 1 (Quiver.Total.right : Quiver.Total C → C)) :
    IsLocallyConstant fun x : C ↦ Nat.card (ineffectiveKernel hs.isLocalHomeomorph x) := by
  have h := (isCoveringMap_source_ineffectiveArrows hs.isLocalHomeomorph hp
    (isClosed_ineffectiveArrows hp hs ht)).isLocallyConstant_natCard_fiber
  have heq : (fun x : C ↦ Nat.card
      ((fun a : ineffectiveArrows C ↦ (a : Quiver.Total C).left) ⁻¹' {x})) =
      fun x ↦ Nat.card (ineffectiveKernel hs.isLocalHomeomorph x) := by
    funext x
    exact (Nat.card_congr (ineffectiveKernelEquivFiber hs.isLocalHomeomorph x)).symm
  rwa [heq] at h

/-- The ineffective-kernel order is locally constant on the coarse space of a smooth proper
étale groupoid, so it is constant on each connected orbifold component. -/
theorem isLocallyConstant_coarseCardIneffectiveKernel
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hs : IsLocalDiffeomorph J I 1 (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I 1 (Quiver.Total.right : Quiver.Total C → C)) :
    IsLocallyConstant (coarseCardIneffectiveKernel hs.isLocalHomeomorph) := by
  refine IsLocallyConstant.iff_isOpen_fiber.mpr fun k ↦ ?_
  have hquot : IsQuotientMap (_root_.Quotient.mk (isIsomorphicSetoid C)) :=
    isQuotientMap_quotient_mk'
  rw [← hquot.isOpen_preimage]
  have hcomp : coarseCardIneffectiveKernel hs.isLocalHomeomorph ∘
      _root_.Quotient.mk (isIsomorphicSetoid C) =
      fun x ↦ Nat.card (ineffectiveKernel hs.isLocalHomeomorph x) :=
    funext (coarseCardIneffectiveKernel_mk hs.isLocalHomeomorph)
  rw [← Set.preimage_comp, hcomp]
  exact (isLocallyConstant_card_ineffectiveKernel hp hs ht).isOpen_fiber k

end TauCeti
