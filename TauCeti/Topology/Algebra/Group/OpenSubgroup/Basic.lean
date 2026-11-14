/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Topology of open subgroups, their coset spaces, and subtype pushforward

An open subgroup `U : OpenSubgroup G` carries a `Group` structure through `SubgroupClass` and the
subspace topology through `SetLike.coe`, but instance search does not unfold `↥U` to
`↥U.toSubgroup`. Consequently Mathlib's `Subgroup` instances for topological groups do not fire
directly on `U : OpenSubgroup G`, nor does the open-subset theorem `IsOpen.locallyCompactSpace`.

This file registers those instances directly on `OpenSubgroup G` (and `OpenAddSubgroup G`):
separate and joint continuity of multiplication, continuity of inversion, `IsTopologicalGroup`,
`LocallyCompactSpace` (using openness alone), and `WeaklyLocallyCompactSpace` and `CompactSpace`
(using that an open subgroup of a topological group with separately continuous multiplication is
also closed). More generally, when `G` has continuous left translations (`ContinuousConstSMul G G`),
every open subgroup is closed (`OpenSubgroup.isClosed_of_continuousConstSMul`), weakening Mathlib's
`OpenSubgroup.isClosed`.

For any group with a topology, `OpenSubgroup.mapSubtype U V` pushes an open subgroup `V` of
`U : OpenSubgroup G` forward along `U.toSubgroup.subtype : U →* G` to an open subgroup of `G`
contained in `U`, left-adjoint to `W ↦ W.comap U.toSubgroup.subtype continuous_subtype_val` and
inverse to it on `{W : OpenSubgroup G | W ≤ U}`.

The continuity criteria `OpenSubgroup.continuous_mk_inf_iff` and
`OpenSubgroup.continuous_mk_comap_iff` describe maps into coset spaces of intersections and
preimages. These apply to arbitrary open subgroups, without normality. Separate continuity of
multiplication makes the target coset spaces discrete; the preimage criterion only needs this
on the target group of the homomorphism.

## Main declarations

* `OpenSubgroup.instSeparatelyContinuousMul`, `OpenSubgroup.instContinuousMul`,
  `OpenSubgroup.instContinuousInv`, `OpenSubgroup.instIsTopologicalGroup`: topological group
  operations on an open subgroup, with additive versions on `OpenAddSubgroup`.
* `OpenSubgroup.instLocallyCompactSpace`, `OpenSubgroup.instWeaklyLocallyCompactSpace`,
  `OpenSubgroup.instCompactSpace`: local compactness and compactness inherited from the ambient
  group, with additive versions on `OpenAddSubgroup`.
* `OpenSubgroup.isClosed_of_continuousConstSMul`: an open subgroup of a group with continuous left
  translations is closed.
* `OpenSubgroup.mapSubtype`: pushforward of an open subgroup of an open subgroup to the ambient
  group, together with its lattice, pullback, adjunction, and injectivity lemmas.
-/

public section

open Set
open scoped Pointwise

namespace OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- An open subgroup of a group with separately continuous multiplication has separately
continuous multiplication. -/
@[to_additive /-- An open additive subgroup of an additive group with separately continuous
addition has separately continuous addition. -/]
instance instSeparatelyContinuousMul [SeparatelyContinuousMul G] (U : OpenSubgroup G) :
    SeparatelyContinuousMul U :=
  U.toSubgroup.toSubmonoid.separatelyContinuousMul

/-- An open subgroup of a group with continuous multiplication has continuous multiplication. -/
@[to_additive /-- An open additive subgroup of an additive group with continuous addition has
continuous addition. -/]
instance instContinuousMul [ContinuousMul G] (U : OpenSubgroup G) : ContinuousMul U :=
  U.toSubgroup.toSubmonoid.continuousMul

/-- An open subgroup of a group with continuous inversion has continuous inversion. -/
@[to_additive /-- An open additive subgroup of an additive group with continuous negation has
continuous negation. -/]
instance instContinuousInv [ContinuousInv G] (U : OpenSubgroup G) : ContinuousInv U :=
  ⟨continuous_inv.subtype_map fun _ hx ↦ inv_mem hx⟩

/-- An open subgroup of a topological group is a topological group. -/
@[to_additive /-- An open additive subgroup of a topological additive group is a topological
additive group. -/]
instance instIsTopologicalGroup [IsTopologicalGroup G] (U : OpenSubgroup G) :
    IsTopologicalGroup U where

/-- An open subgroup of a locally compact group is locally compact. -/
@[to_additive /-- An open additive subgroup of a locally compact additive group is locally
compact. -/]
instance instLocallyCompactSpace [LocallyCompactSpace G] (U : OpenSubgroup G) :
    LocallyCompactSpace U :=
  U.isOpen.locallyCompactSpace

/-- An open subgroup of a weakly locally compact group with separately continuous multiplication is
weakly locally compact, since it is closed. -/
@[to_additive /-- An open additive subgroup of a weakly locally compact additive group with
separately continuous addition is weakly locally compact, since it is closed. -/]
instance instWeaklyLocallyCompactSpace [SeparatelyContinuousMul G] [WeaklyLocallyCompactSpace G]
    (U : OpenSubgroup G) : WeaklyLocallyCompactSpace U :=
  U.isClosed.weaklyLocallyCompactSpace

/-- An open subgroup of a compact group with separately continuous multiplication is compact, since
it is closed. -/
@[to_additive /-- An open additive subgroup of a compact additive group with separately continuous
addition is compact, since it is closed. -/]
instance instCompactSpace [SeparatelyContinuousMul G] [CompactSpace G] (U : OpenSubgroup G) :
    CompactSpace U :=
  isCompact_iff_compactSpace.mp U.isClosed.isCompact

/-- **An open subgroup of a group with continuous left translations is closed.** Its complement is
the union of its nontrivial left cosets `g • U` for `g ∉ U`. This weakens `OpenSubgroup.isClosed`,
which assumes `[SeparatelyContinuousMul G]`. -/
@[to_additive
/-- **An open additive subgroup of an additive group with continuous left translations is closed.**
Its complement is the union of its nontrivial left cosets `g +ᵥ U` for `g ∉ U`. This weakens
`OpenAddSubgroup.isClosed`, which assumes `[SeparatelyContinuousAdd G]`. -/]
theorem isClosed_of_continuousConstSMul [ContinuousConstSMul G G] (U : OpenSubgroup G) :
    IsClosed (U : Set G) := by
  rw [← isOpen_compl_iff]
  have hcompl : (U : Set G)ᶜ = ⋃ (g : G) (_ : g ∉ U), g • (U : Set G) := by
    ext x
    simp only [mem_compl_iff, SetLike.mem_coe, mem_iUnion, mem_smul_set, smul_eq_mul]
    refine ⟨fun hx ↦ ⟨x, hx, 1, U.one_mem, mul_one x⟩, ?_⟩
    rintro ⟨g, hg, u, hu, rfl⟩ hgu
    exact hg (by simpa only [mul_inv_cancel_right] using mul_mem hgu (inv_mem hu))
  rw [hcompl]
  exact isOpen_iUnion fun (g : G) ↦ isOpen_iUnion fun (_ : g ∉ U) ↦ by
    simpa only [image_smul] using isOpenMap_smul g _ U.isOpen

section MapSubtype

/-- **Pushforward of an open subgroup along an open subgroup's inclusion.** An open subgroup `V` of
`U : OpenSubgroup G` is open in `U`, and `U` is open in `G`, so the image of `V` in `G` is an open
subgroup of `G` contained in `U`. No continuity of the group operations is required. -/
@[to_additive
/-- **Pushforward of an open additive subgroup along an open additive subgroup's inclusion.** An
open additive subgroup `V` of `U : OpenAddSubgroup G` is open in `U`, and `U` is open in `G`, so
the image of `V` in `G` is an open additive subgroup of `G` contained in `U`. No continuity of the
group operations is required. -/]
def mapSubtype (U : OpenSubgroup G) (V : OpenSubgroup U) : OpenSubgroup G :=
  ⟨V.toSubgroup.map U.toSubgroup.subtype, U.isOpen.isOpenMap_subtype_val _ V.isOpen⟩

/-- The underlying subgroup of `U.mapSubtype V` is `V.toSubgroup.map U.toSubgroup.subtype`. -/
@[to_additive (attr := simp, norm_cast)
/-- The underlying additive subgroup of `U.mapSubtype V` is
`V.toAddSubgroup.map U.toAddSubgroup.subtype`. -/]
theorem toSubgroup_mapSubtype (U : OpenSubgroup G) (V : OpenSubgroup U) :
    (U.mapSubtype V : Subgroup G) = V.toSubgroup.map U.toSubgroup.subtype :=
  (rfl)

/-- As a set in `G`, `U.mapSubtype V` is the image of `(V : Set U)` under `Subtype.val`. -/
@[to_additive (attr := simp, norm_cast)
/-- As a set in `G`, `U.mapSubtype V` is the image of `(V : Set U)` under `Subtype.val`. -/]
theorem coe_mapSubtype (U : OpenSubgroup G) (V : OpenSubgroup U) :
    ((U.mapSubtype V : OpenSubgroup G) : Set G) = Subtype.val '' (V : Set U) :=
  Subgroup.coe_map U.toSubgroup.subtype V.toSubgroup

/-- An element `g : G` belongs to `U.mapSubtype V` iff `g ∈ U` and `⟨g, ‹_›⟩ ∈ V`. -/
@[to_additive (attr := simp)
/-- An element `g : G` belongs to `U.mapSubtype V` iff `g ∈ U` and `⟨g, ‹_›⟩ ∈ V`. -/]
theorem mem_mapSubtype_iff {U : OpenSubgroup G} {V : OpenSubgroup U} {g : G} :
    g ∈ U.mapSubtype V ↔ ∃ h : g ∈ U, (⟨g, h⟩ : U) ∈ V := by
  rw [← SetLike.mem_coe, coe_mapSubtype]
  exact ⟨fun ⟨⟨x, hx⟩, hxV, hxeq⟩ ↦ hxeq ▸ ⟨hx, hxV⟩, fun ⟨h, hgV⟩ ↦ ⟨⟨g, h⟩, hgV, rfl⟩⟩

/-- `U.mapSubtype V` is contained in `U`. -/
@[to_additive /-- `U.mapSubtype V` is contained in `U`. -/]
theorem mapSubtype_le (U : OpenSubgroup G) (V : OpenSubgroup U) : U.mapSubtype V ≤ U :=
  fun _ hg ↦ (mem_mapSubtype_iff.mp hg).1

/-- Pushing forward `⊤ : OpenSubgroup U` along `U.toSubgroup.subtype` recovers `U`. -/
@[to_additive (attr := simp)
/-- Pushing forward `⊤ : OpenAddSubgroup U` along `U.toAddSubgroup.subtype` recovers `U`. -/]
theorem mapSubtype_top (U : OpenSubgroup G) : U.mapSubtype ⊤ = U := by
  ext g
  simp [mem_mapSubtype_iff]

/-- `U.mapSubtype` commutes with binary intersections. -/
@[to_additive /-- `U.mapSubtype` commutes with binary intersections. -/]
theorem mapSubtype_inf (U : OpenSubgroup G) (V₁ V₂ : OpenSubgroup U) :
    U.mapSubtype (V₁ ⊓ V₂) = U.mapSubtype V₁ ⊓ U.mapSubtype V₂ := by
  ext g
  exact mem_mapSubtype_iff.trans
    ⟨fun ⟨hg, h₁, h₂⟩ ↦ ⟨mem_mapSubtype_iff.mpr ⟨hg, h₁⟩, mem_mapSubtype_iff.mpr ⟨hg, h₂⟩⟩,
      fun ⟨h₁, h₂⟩ ↦
        let ⟨hg, h₁'⟩ := mem_mapSubtype_iff.mp h₁
        ⟨hg, h₁', (mem_mapSubtype_iff.mp h₂).2⟩⟩

/-- Pulling `U` back along its own inclusion yields `⊤ : OpenSubgroup U`. -/
@[to_additive (attr := simp)
/-- Pulling `U` back along its own inclusion yields `⊤ : OpenAddSubgroup U`. -/]
theorem comap_subtype_self (U : OpenSubgroup G) :
    U.comap U.toSubgroup.subtype continuous_subtype_val = ⊤ := by
  ext x
  exact ⟨fun _ ↦ trivial, fun _ ↦ x.2⟩

/-- Pulling `U.mapSubtype V` back along `U.toSubgroup.subtype` recovers `V`. -/
@[to_additive (attr := simp)
/-- Pulling `U.mapSubtype V` back along `U.toAddSubgroup.subtype` recovers `V`. -/]
theorem comap_subtype_mapSubtype (U : OpenSubgroup G) (V : OpenSubgroup U) :
    (U.mapSubtype V).comap U.toSubgroup.subtype continuous_subtype_val = V := by
  ext ⟨g, hg⟩
  exact mem_mapSubtype_iff.trans ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hg, h⟩⟩

/-- Pushing forward the pullback of any open subgroup `W` along `U.toSubgroup.subtype` yields
`W ⊓ U`. -/
@[to_additive (attr := simp)
/-- Pushing forward the pullback of any open additive subgroup `W` along `U.toAddSubgroup.subtype`
yields `W ⊓ U`. -/]
theorem mapSubtype_comap_subtype (U W : OpenSubgroup G) :
    U.mapSubtype (W.comap U.toSubgroup.subtype continuous_subtype_val) = W ⊓ U := by
  ext g
  exact mem_mapSubtype_iff.trans ⟨fun ⟨hgU, hgW⟩ ↦ ⟨hgW, hgU⟩, fun ⟨hgW, hgU⟩ ↦ ⟨hgU, hgW⟩⟩

/-- Pushing forward the pullback of an open subgroup `W ≤ U` recovers `W`. -/
@[to_additive
/-- Pushing forward the pullback of an open additive subgroup `W ≤ U` recovers `W`. -/]
theorem mapSubtype_comap_subtype_eq_of_le {U W : OpenSubgroup G} (hWU : W ≤ U) :
    U.mapSubtype (W.comap U.toSubgroup.subtype continuous_subtype_val) = W := by
  rw [mapSubtype_comap_subtype, inf_eq_left.mpr hWU]

/-- `U.mapSubtype` is injective. -/
@[to_additive /-- `U.mapSubtype` is injective. -/]
theorem mapSubtype_injective (U : OpenSubgroup G) : Function.Injective U.mapSubtype :=
  Function.LeftInverse.injective U.comap_subtype_mapSubtype

/-- `U.mapSubtype V₁ = U.mapSubtype V₂` if and only if `V₁ = V₂`. -/
@[to_additive (attr := simp) /-- `U.mapSubtype V₁ = U.mapSubtype V₂` if and only if `V₁ = V₂`. -/]
theorem mapSubtype_inj {U : OpenSubgroup G} {V₁ V₂ : OpenSubgroup U} :
    U.mapSubtype V₁ = U.mapSubtype V₂ ↔ V₁ = V₂ :=
  U.mapSubtype_injective.eq_iff

/-- `U.mapSubtype` is left adjoint to pullback along `U.toSubgroup.subtype`. -/
@[to_additive /-- `U.mapSubtype` is left adjoint to pullback along `U.toAddSubgroup.subtype`. -/]
theorem mapSubtype_le_iff {U W : OpenSubgroup G} {V : OpenSubgroup U} :
    U.mapSubtype V ≤ W ↔ V ≤ W.comap U.toSubgroup.subtype continuous_subtype_val := by
  refine ⟨fun h x hx ↦ h (mem_mapSubtype_iff.mpr ⟨x.2, hx⟩), fun h g hg ↦ ?_⟩
  obtain ⟨_, hgV⟩ := mem_mapSubtype_iff.mp hg
  exact h hgV

/-- `U.mapSubtype` reflects and preserves inclusion. -/
@[to_additive (attr := simp) /-- `U.mapSubtype` reflects and preserves inclusion. -/]
theorem mapSubtype_le_mapSubtype_iff {U : OpenSubgroup G} {V₁ V₂ : OpenSubgroup U} :
    U.mapSubtype V₁ ≤ U.mapSubtype V₂ ↔ V₁ ≤ V₂ := by
  rw [mapSubtype_le_iff, comap_subtype_mapSubtype]

end MapSubtype

variable {H X : Type*} [Group H] [TopologicalSpace H] [TopologicalSpace X]

/-- A map into the coset space of an intersection of open subgroups is continuous if and only
if its projections to both coset spaces are continuous. Normality is not required. -/
theorem continuous_mk_inf_iff [SeparatelyContinuousMul G] {U V : OpenSubgroup G} {g : X → G} :
    (Continuous fun x ↦ (g x : G ⧸ (U ⊓ V).toSubgroup)) ↔
      (Continuous fun x ↦ (g x : G ⧸ U.toSubgroup)) ∧
      (Continuous fun x ↦ (g x : G ⧸ V.toSubgroup)) := by
  constructor
  · intro h
    have hU : Continuous (Subgroup.quotientMapOfLE
        (inf_le_left : U.toSubgroup ⊓ V.toSubgroup ≤ U.toSubgroup)) :=
      (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr QuotientGroup.continuous_mk
    have hV : Continuous (Subgroup.quotientMapOfLE
        (inf_le_right : U.toSubgroup ⊓ V.toSubgroup ≤ V.toSubgroup)) :=
      (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr QuotientGroup.continuous_mk
    exact ⟨hU.comp h, hV.comp h⟩
  · rintro ⟨hU, hV⟩
    apply IsLocallyConstant.continuous
    rw [IsLocallyConstant.iff_isOpen_fiber_apply]
    intro x
    have hfiber :
        (fun y ↦ (g y : G ⧸ (U ⊓ V).toSubgroup)) ⁻¹' {(g x : G ⧸ (U ⊓ V).toSubgroup)} =
          (fun y ↦ (g y : G ⧸ U.toSubgroup)) ⁻¹' {(g x : G ⧸ U.toSubgroup)} ∩
          (fun y ↦ (g y : G ⧸ V.toSubgroup)) ⁻¹' {(g x : G ⧸ V.toSubgroup)} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, QuotientGroup.eq]
      exact Subgroup.mem_inf
    rw [hfiber]
    exact (hU.isOpen_preimage _ (isOpen_discrete _)).inter
      (hV.isOpen_preimage _ (isOpen_discrete _))

/-- A map into the coset space of the preimage of an open subgroup is continuous if and only
if its composite with the homomorphism and the target coset projection is continuous.
Normality and continuity of the group operations on the source are not required. -/
theorem continuous_mk_comap_iff [SeparatelyContinuousMul H] (U : OpenSubgroup H) (f : G →* H)
    (hf : Continuous f) {g : X → G} :
    (Continuous fun x ↦ (g x : G ⧸ (U.comap f hf).toSubgroup)) ↔
      (Continuous fun x ↦ (f (g x) : H ⧸ U.toSubgroup)) := by
  let φ : G ⧸ (U.comap f hf).toSubgroup → H ⧸ U.toSubgroup :=
    Quotient.map' f fun a b h ↦ by
      simpa only [QuotientGroup.leftRel_apply, toSubgroup_comap, Subgroup.mem_comap,
        map_mul, map_inv] using h
  constructor
  · intro h
    have hφ : Continuous φ :=
      (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
        (QuotientGroup.continuous_mk.comp hf)
    exact hφ.comp h
  · intro h
    apply IsLocallyConstant.continuous
    rw [IsLocallyConstant.iff_isOpen_fiber_apply]
    intro x
    have hfiber :
        (fun y ↦ (g y : G ⧸ (U.comap f hf).toSubgroup)) ⁻¹'
          {(g x : G ⧸ (U.comap f hf).toSubgroup)} =
        (fun y ↦ (f (g y) : H ⧸ U.toSubgroup)) ⁻¹' {(f (g x) : H ⧸ U.toSubgroup)} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, QuotientGroup.eq]
      simp only [toSubgroup_comap, Subgroup.mem_comap, map_mul, map_inv]
    rw [hfiber]
    exact h.isOpen_preimage _ (isOpen_discrete _)

end OpenSubgroup
