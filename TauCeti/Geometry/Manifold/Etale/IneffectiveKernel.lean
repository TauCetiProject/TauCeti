/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Etale.Basic
public import TauCeti.Geometry.Manifold.GroupAction.GermKernel
public import TauCeti.Topology.CategoryTheory.Groupoid.IneffectiveCovering

/-!
# Locally constant ineffective isotropy

In a proper étale groupoid with Hausdorff arrow space, boundaryless object charts over a
complete `RCLike` normed space, and `C^n` source and target local diffeomorphisms (`1 ≤ n`),
the ineffective arrows are closed as well as open. In a retained-arrow
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
  [T2Space (Quiver.Total C)] {n : ℕ∞ω}

/-- In a groupoid with Hausdorff arrow space, continuous units and composition, and boundaryless
object charts over a complete `RCLike` normed space, ineffective arrows are closed if source-target
is proper and source and target are `C^n` local diffeomorphisms with `1 ≤ n`. -/
theorem isClosed_ineffectiveArrows
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C))
    (hu : Continuous fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C))
    (hc : Continuous fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
      p.1.1.comp p.1.2 p.2) (hn : 1 ≤ n) :
    IsClosed (ineffectiveArrows C) := by
  have : T2Space C :=
    (Function.LeftInverse.isEmbedding (fun _ ↦ rfl) hs.isLocalHomeomorph.continuous hu).t2Space
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
    exists_contMDiff_isotropy_action_of_proper_source_target hp hs ht hu hc x
  let : MulAction (Aut x) U := act
  let σ (g : Aut x) (z : U) : Quiver.Total C :=
    ⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) U).symm (g, z)).hom⟩
  -- A labelled arrow is ineffective precisely on the interior of its fixed-point set.
  have hpre (g : Aut x) : σ g ⁻¹' ineffectiveArrows C = interior (MulAction.fixedBy U g) := by
    ext z
    rw [mem_preimage, mem_ineffectiveArrows_iff, ← (hopen g).map_nhds_eq z,
      Filter.eventually_map, mem_interior_iff_mem_nhds, ← Filter.eventually_mem_set]
    apply Filter.eventually_congr
    exact Filter.Eventually.of_forall fun w ↦ by
      have hl : (σ g w).left = (w : C) := congrFun (hsource g) w
      have hr : (σ g w).right = (g • w : U).val := congrFun (htarget g) w
      rw [hl, hr, MulAction.mem_fixedBy]
      exact ⟨fun h ↦ Subtype.ext h.symm, fun h ↦ (congrArg Subtype.val h).symm⟩
  let g : Aut x := Aut.of (asIso f)
  have hzero : σ g ⟨x, hxU⟩ = ⟨x, x, f⟩ := hcentre g
  have hcl : (⟨x, hxU⟩ : U) ∈ closure (σ g ⁻¹' ineffectiveArrows C) := by
    rw [← (hopen g).isOpenMap.preimage_closure_eq_closure_preimage (hopen g).continuous]
    rw [mem_preimage, hcentre g]
    exact ha
  rw [hpre, (isClosed_interior_fixedBy g (isOfFinOrder_of_finite g)
    ((hsmul.contMDiff_const_smul g).of_le hn)).closure_eq] at hcl
  have hmem : σ g ⟨x, hxU⟩ ∈ ineffectiveArrows C := by
    rw [← hpre] at hcl
    exact hcl
  rwa [hzero] at hmem

variable [IsTopologicalGroupoid C]

/-- In a topological groupoid with Hausdorff arrow space and boundaryless object charts over
a complete `RCLike` normed space, the ineffective-kernel order on objects is locally constant
if source-target is proper and source and target are `C^n` local diffeomorphisms with `1 ≤ n`. -/
theorem isLocallyConstant_card_ineffectiveKernel
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C)) (hn : 1 ≤ n) :
    IsLocallyConstant fun x : C ↦ Nat.card (ineffectiveKernel hs.isLocalHomeomorph x) :=
  isLocallyConstant_card_ineffectiveKernel_of_isClosed hs.isLocalHomeomorph hp
    (isClosed_ineffectiveArrows hp hs ht
      IsTopologicalGroupoid.continuous_unit IsTopologicalGroupoid.continuous_comp hn)

/-- In a topological groupoid with Hausdorff arrow space and boundaryless object charts over
a complete `RCLike` normed space, the coarse ineffective-kernel order is locally constant if
source-target is proper and source and target are `C^n` local diffeomorphisms with `1 ≤ n`. -/
theorem isLocallyConstant_coarseCardIneffectiveKernel
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C)) (hn : 1 ≤ n) :
    IsLocallyConstant (coarseCardIneffectiveKernel hs.isLocalHomeomorph) :=
  isLocallyConstant_coarseCardIneffectiveKernel_of_isClosed hs.isLocalHomeomorph hp
    (isClosed_ineffectiveArrows hp hs ht
      IsTopologicalGroupoid.continuous_unit IsTopologicalGroupoid.continuous_comp hn)

end TauCeti
