/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.Compact

/-!
# The refinement index of compact open subgroups

For a locally profinite group `G`, such as the `p`-adic points of a reductive group, the
compact open subgroups `K ⊆ G` are the levels of a tower of arithmetic quotients: a refinement
`U ⊆ K` gives a covering from level `U` to level `K`, and cohomology of the tower is a diagram
indexed by the opposite of the inclusion order. This file sets up that index.

* `TauCeti.CompactOpenSubgroup G` is the type of compact open subgroups, ordered by inclusion.
  Two of them have their intersection as common refinement, so the index is codirected; when
  `G` is locally profinite the index is nonempty, hence cofiltered, and its members form a basis
  of neighbourhoods of the identity.
* A family of compact open subgroups indexed by a codirected order is an initial functor into the
  index exactly when it is a neighbourhood basis of the identity. Hence the opposite of such a
  family is final, and a colimit over all levels may be computed along it
  (`CategoryTheory.Functor.Final.colimitIso`). The same holds inside the levels below a fixed
  compact open `K₀`.
* A topological group isomorphism transports compact open subgroups, as an order isomorphism of
  the indices. The resulting action of continuous automorphisms, in particular conjugation, and
  the normal bases below a fixed level are in
  `TauCeti.Topology.Algebra.Group.ContinuousAut.CompactOpenSubgroup`.

## Main definitions

* `TauCeti.CompactOpenSubgroup G`: the compact open subgroups of `G`, with additive version
  `TauCeti.CompactOpenAddSubgroup G`.
* `ContinuousMulEquiv.compactOpenSubgroupOrderIso`: transport of compact open subgroups along an
  isomorphism of topological groups.

## Main results

* `TauCeti.CompactOpenSubgroup.nhds_one_hasBasis`: in a locally profinite group the compact open
  subgroups form a basis of neighbourhoods of the identity.
* `TauCeti.CompactOpenSubgroup.initial_functor_iff`: a monotone codirected family of compact
  open subgroups is initial in the index exactly when it is a neighbourhood basis of the identity;
  `TauCeti.CompactOpenSubgroup.initial_functor_of_forall_mem_nhds` is the unconditional direction,
  and `TauCeti.CompactOpenSubgroup.initial_functor_Iic_of_forall_mem_nhds` its version below a
  fixed level.

## References

* M. Emerton, *On the interpolation of systems of eigenvalues attached to automorphic Hecke
  eigenforms*, author draft of 2 January 2006, §2.1 opening, p. 20, and §2.2, pp. 27–28: the
  tower of levels, computing its colimit along a normal compact basis, and the transport of
  levels by the group action.
* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §1.1, p. 7, for compact open subgroups of locally profinite groups.
-/

public section

open CategoryTheory Filter Topology
open scoped Pointwise

namespace TauCeti

/-- The type of compact open additive subgroups of a topological additive group. -/
structure CompactOpenAddSubgroup (G : Type*) [AddGroup G] [TopologicalSpace G]
    extends OpenAddSubgroup G where
  isCompact' : IsCompact (carrier : Set G)

/-- The type of compact open subgroups of a topological group, the levels of a tower of
arithmetic quotients. -/
@[to_additive]
structure CompactOpenSubgroup (G : Type*) [Group G] [TopologicalSpace G]
    extends OpenSubgroup G where
  isCompact' : IsCompact (carrier : Set G)

namespace CompactOpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- A compact open subgroup is determined by its underlying open subgroup. -/
@[to_additive /-- A compact open additive subgroup is determined by its underlying open additive
subgroup. -/]
theorem toOpenSubgroup_injective :
    Function.Injective (toOpenSubgroup : CompactOpenSubgroup G → OpenSubgroup G) := by
  rintro ⟨U, hU⟩ ⟨V, hV⟩ (rfl : U = V)
  rfl

@[to_additive]
instance : SetLike (CompactOpenSubgroup G) G where
  coe U := U.carrier
  coe_injective _ _ h := toOpenSubgroup_injective (SetLike.coe_injective h)

@[to_additive]
instance : PartialOrder (CompactOpenSubgroup G) := .ofSetLike (CompactOpenSubgroup G)

@[to_additive]
instance : SubgroupClass (CompactOpenSubgroup G) G where
  mul_mem := Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

/-- Two compact open subgroups with the same elements are equal. -/
@[to_additive (attr := ext) /-- Two compact open additive subgroups with the same elements are
equal. -/]
theorem ext {U V : CompactOpenSubgroup G} (h : ∀ x, x ∈ U ↔ x ∈ V) : U = V :=
  SetLike.ext h

variable (U V : CompactOpenSubgroup G)

@[to_additive (attr := simp)]
theorem coe_toOpenSubgroup : ((U.toOpenSubgroup : OpenSubgroup G) : Set G) = U :=
  (rfl)

@[to_additive (attr := simp)]
theorem mem_mk {W : OpenSubgroup G} (hW : IsCompact (W : Set G)) {x : G} :
    x ∈ (⟨W, hW⟩ : CompactOpenSubgroup G) ↔ x ∈ W :=
  Iff.rfl

@[to_additive (attr := simp)]
theorem mem_toOpenSubgroup {x : G} : x ∈ U.toOpenSubgroup ↔ x ∈ U :=
  Iff.rfl

@[to_additive]
theorem mem_toSubgroup {x : G} : x ∈ U.toSubgroup ↔ x ∈ U :=
  Iff.rfl

/-- A compact open subgroup is determined by its underlying subgroup. -/
@[to_additive /-- A compact open additive subgroup is determined by its underlying additive
subgroup. -/]
theorem toSubgroup_injective :
    Function.Injective (fun U : CompactOpenSubgroup G ↦ U.toSubgroup) :=
  OpenSubgroup.toSubgroup_injective.comp toOpenSubgroup_injective

/-- Compact open subgroups compare through their underlying open subgroups. -/
@[to_additive (attr := simp) /-- Compact open additive subgroups compare through their underlying
open additive subgroups. -/]
theorem toOpenSubgroup_le : U.toOpenSubgroup ≤ V.toOpenSubgroup ↔ U ≤ V :=
  Iff.rfl

/-- Compact open subgroups compare through their underlying subgroups. -/
@[to_additive /-- Compact open additive subgroups compare through their underlying additive
subgroups. -/]
theorem toSubgroup_le : U.toSubgroup ≤ V.toSubgroup ↔ U ≤ V :=
  Iff.rfl

@[to_additive]
protected theorem isCompact : IsCompact (U : Set G) :=
  U.isCompact'

@[to_additive]
protected theorem isOpen : IsOpen (U : Set G) :=
  U.isOpen'

@[to_additive]
theorem mem_nhds_one : (U : Set G) ∈ 𝓝 (1 : G) :=
  U.isOpen.mem_nhds (one_mem U)

@[to_additive]
protected theorem isClosed [SeparatelyContinuousMul G] : IsClosed (U : Set G) :=
  U.toOpenSubgroup.isClosed

/-- A compact open subgroup is a compact space. -/
@[to_additive /-- A compact open additive subgroup is a compact space. -/]
instance compactSpace_toSubgroup : CompactSpace U.toSubgroup :=
  isCompact_iff_compactSpace.mp U.isCompact

/-! ### Common refinements -/

section Inf

variable [SeparatelyContinuousMul G]

/-- The intersection of two compact open subgroups, their common refinement, is a compact open
subgroup. -/
@[to_additive /-- The intersection of two compact open additive subgroups is a compact open
additive subgroup. -/]
instance : Min (CompactOpenSubgroup G) :=
  ⟨fun U V ↦ ⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup, U.isCompact.inter_right V.isClosed⟩⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_inf : ((U ⊓ V : CompactOpenSubgroup G) : Set G) = (U : Set G) ∩ V :=
  (rfl)

@[to_additive (attr := simp)]
theorem mem_inf {x : G} : x ∈ U ⊓ V ↔ x ∈ U ∧ x ∈ V :=
  Iff.rfl

@[to_additive (attr := simp)]
theorem toOpenSubgroup_inf : (U ⊓ V).toOpenSubgroup = U.toOpenSubgroup ⊓ V.toOpenSubgroup :=
  (rfl)

/-- The compact open subgroups form a meet-semilattice under inclusion, the meet being the
intersection. -/
@[to_additive /-- The compact open additive subgroups form a meet-semilattice under inclusion. -/]
instance : SemilatticeInf (CompactOpenSubgroup G) :=
  SetLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ ↦ rfl

end Inf

/-- In a compact group the whole group is the largest compact open subgroup. -/
@[to_additive /-- In a compact additive group the whole group is the largest compact open
additive subgroup. -/]
instance [CompactSpace G] : OrderTop (CompactOpenSubgroup G) where
  top := ⟨⊤, isCompact_univ⟩
  le_top _ _ _ := Set.mem_univ _

@[to_additive (attr := simp)]
theorem mem_top [CompactSpace G] (x : G) : x ∈ (⊤ : CompactOpenSubgroup G) :=
  Set.mem_univ x

/-! ### Locally profinite groups -/

section NonarchimedeanGroup

variable [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]

/-- In a locally profinite group the compact open subgroups form a basis of neighbourhoods of the
identity. -/
@[to_additive /-- In a locally profinite additive group the compact open additive subgroups form a
basis of neighbourhoods of zero. -/]
theorem nhds_one_hasBasis :
    (𝓝 (1 : G)).HasBasis (fun _ : CompactOpenSubgroup G ↦ True) (↑) := by
  refine NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup.to_hasBasis ?_ ?_
  · exact fun U hU ↦ ⟨⟨U, hU⟩, trivial, subset_rfl⟩
  · exact fun U _ ↦ ⟨U.toOpenSubgroup, U.isCompact, subset_rfl⟩

/-- A locally profinite group has a compact open subgroup. -/
@[to_additive /-- A locally profinite additive group has a compact open additive subgroup. -/]
instance : Nonempty (CompactOpenSubgroup G) :=
  let ⟨U, _⟩ := (nhds_one_hasBasis (G := G)).ex_mem
  ⟨U⟩

end NonarchimedeanGroup

/-! ### Neighbourhood bases are initial -/

section Initial

variable {ι : Type*} [Preorder ι] [IsCodirectedOrder ι] {U : ι → CompactOpenSubgroup G}

/-- A monotone codirected family of compact open subgroups which is a neighbourhood basis of the
identity is an initial functor into the compact open subgroups. Its opposite is then final, so a
colimit over the opposite of all levels is computed along the family. -/
@[to_additive /-- A monotone codirected family of compact open additive subgroups which is a
neighbourhood basis of zero is an initial functor into the compact open additive subgroups. -/]
theorem initial_functor_of_forall_mem_nhds (hU : Monotone U)
    (h : ∀ s ∈ 𝓝 (1 : G), ∃ i, (U i : Set G) ⊆ s) : hU.functor.Initial :=
  hU.initial_functor_iff.2 fun V ↦ h V V.mem_nhds_one

/-- In a locally profinite group, a monotone codirected family of compact open subgroups is an
initial functor into the compact open subgroups exactly when it is a neighbourhood basis of the
identity. -/
@[to_additive /-- In a locally profinite additive group, a monotone codirected family of compact
open additive subgroups is an initial functor into the compact open additive subgroups exactly
when it is a neighbourhood basis of zero. -/]
theorem initial_functor_iff [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]
    (hU : Monotone U) : hU.functor.Initial ↔ ∀ s ∈ 𝓝 (1 : G), ∃ i, (U i : Set G) ⊆ s := by
  refine ⟨fun h s hs ↦ ?_, initial_functor_of_forall_mem_nhds hU⟩
  obtain ⟨V, -, hVs⟩ := nhds_one_hasBasis.mem_iff.1 hs
  obtain ⟨i, hi⟩ := hU.initial_functor_iff.1 h V
  exact ⟨i, (SetLike.coe_subset_coe.2 hi).trans hVs⟩

/-- Below a fixed compact open subgroup `K₀`, a monotone codirected family of compact open
subgroups contained in `K₀` which is a neighbourhood basis of the identity is an initial functor
into the compact open subgroups contained in `K₀`. -/
@[to_additive /-- Below a fixed compact open additive subgroup `K₀`, a monotone codirected family
of compact open additive subgroups contained in `K₀` which is a neighbourhood basis of zero is an
initial functor into the compact open additive subgroups contained in `K₀`. -/]
theorem initial_functor_Iic_of_forall_mem_nhds {K₀ : CompactOpenSubgroup G}
    {U : ι → Set.Iic K₀} (hU : Monotone U)
    (h : ∀ s ∈ 𝓝 (1 : G), ∃ i, ((U i : CompactOpenSubgroup G) : Set G) ⊆ s) :
    hU.functor.Initial :=
  hU.initial_functor_iff.2 fun V ↦ h _ (V : CompactOpenSubgroup G).mem_nhds_one

/-- The compact open subgroups contained in a fixed one, `K₀`, form an initial subcategory of all
compact open subgroups: every compact open subgroup `V` contains `V ⊓ K₀`. -/
@[to_additive /-- The compact open additive subgroups contained in a fixed one form an initial
subcategory of all compact open additive subgroups. -/]
instance initial_functor_coe_Iic [SeparatelyContinuousMul G] (K₀ : CompactOpenSubgroup G) :
    (Subtype.mono_coe (· ∈ Set.Iic K₀)).functor.Initial :=
  (Subtype.mono_coe _).initial_functor_iff.2 fun V ↦
    ⟨⟨V ⊓ K₀, Set.mem_Iic.2 inf_le_right⟩, inf_le_left⟩

end Initial

end CompactOpenSubgroup

end TauCeti

/-! ### Transport along isomorphisms and conjugation -/

namespace ContinuousMulEquiv

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- A topological group isomorphism transports compact open subgroups, preserving inclusion. -/
def compactOpenSubgroupOrderIso (e : G ≃ₜ* H) :
    TauCeti.CompactOpenSubgroup G ≃o TauCeti.CompactOpenSubgroup H where
  -- Each topological field is stated for the carrier; restate it through the set coercion, which
  -- `Subgroup.coe_map` computes as an image.
  toFun U :=
    { toSubgroup := e.toMulEquiv.mapSubgroup U.toSubgroup
      isOpen' := by
        change IsOpen (e.toMulEquiv.mapSubgroup U.toSubgroup : Set H)
        rw [MulEquiv.coe_mapSubgroup, Subgroup.coe_map]
        exact e.toHomeomorph.isOpen_image.mpr U.isOpen
      isCompact' := by
        change IsCompact (e.toMulEquiv.mapSubgroup U.toSubgroup : Set H)
        rw [MulEquiv.coe_mapSubgroup, Subgroup.coe_map]
        exact U.isCompact.image e.continuous }
  invFun V :=
    { toSubgroup := e.toMulEquiv.mapSubgroup.symm V.toSubgroup
      isOpen' := by
        change IsOpen (e.toMulEquiv.mapSubgroup.symm V.toSubgroup : Set G)
        rw [MulEquiv.symm_mapSubgroup, MulEquiv.coe_mapSubgroup, Subgroup.coe_map]
        exact e.toHomeomorph.symm.isOpen_image.mpr V.isOpen
      isCompact' := by
        change IsCompact (e.toMulEquiv.mapSubgroup.symm V.toSubgroup : Set G)
        rw [MulEquiv.symm_mapSubgroup, MulEquiv.coe_mapSubgroup, Subgroup.coe_map]
        exact V.isCompact.image e.symm.continuous }
  left_inv U :=
    TauCeti.CompactOpenSubgroup.toSubgroup_injective
      (e.toMulEquiv.mapSubgroup.left_inv U.toSubgroup)
  right_inv V :=
    TauCeti.CompactOpenSubgroup.toSubgroup_injective
      (e.toMulEquiv.mapSubgroup.right_inv V.toSubgroup)
  map_rel_iff' := e.toMulEquiv.mapSubgroup.map_rel_iff

/-- The underlying subgroup transported by `ContinuousMulEquiv.compactOpenSubgroupOrderIso` is the
image of the original subgroup. -/
@[simp]
theorem compactOpenSubgroupOrderIso_apply_toSubgroup (e : G ≃ₜ* H)
    (U : TauCeti.CompactOpenSubgroup G) :
    (e.compactOpenSubgroupOrderIso U).toSubgroup = U.toSubgroup.map e.toMulEquiv.toMonoidHom :=
  (rfl)

/-- The underlying subgroup of the inverse transport of a compact open subgroup is its image under
the inverse topological group isomorphism. -/
@[simp]
theorem compactOpenSubgroupOrderIso_symm_apply_toSubgroup (e : G ≃ₜ* H)
    (V : TauCeti.CompactOpenSubgroup H) :
    (e.compactOpenSubgroupOrderIso.symm V).toSubgroup =
      V.toSubgroup.map e.symm.toMulEquiv.toMonoidHom :=
  (rfl)

/-- The transport of a compact open subgroup is its image. -/
@[simp, norm_cast]
theorem coe_compactOpenSubgroupOrderIso (e : G ≃ₜ* H) (U : TauCeti.CompactOpenSubgroup G) :
    (e.compactOpenSubgroupOrderIso U : Set H) = e '' U :=
  (rfl)

/-- The inverse transport of a compact open subgroup is its image under the inverse isomorphism. -/
@[simp, norm_cast]
theorem coe_compactOpenSubgroupOrderIso_symm (e : G ≃ₜ* H) (V : TauCeti.CompactOpenSubgroup H) :
    (e.compactOpenSubgroupOrderIso.symm V : Set G) = e.symm '' V :=
  (rfl)

/-- An element lies in a transported compact open subgroup exactly when its inverse image lies in
the original one. -/
@[simp]
theorem mem_compactOpenSubgroupOrderIso (e : G ≃ₜ* H) (U : TauCeti.CompactOpenSubgroup G)
    {h : H} : h ∈ e.compactOpenSubgroupOrderIso U ↔ e.symm h ∈ U :=
  Subgroup.mem_map_equiv

/-- An element lies in an inversely transported compact open subgroup exactly when its image lies
in the original one. -/
@[simp]
theorem mem_compactOpenSubgroupOrderIso_symm (e : G ≃ₜ* H) (V : TauCeti.CompactOpenSubgroup H)
    {g : G} : g ∈ e.compactOpenSubgroupOrderIso.symm V ↔ e g ∈ V :=
  Subgroup.mem_map_equiv

/-- The image of an element lies in a transported compact open subgroup exactly when the element
lies in the original one. This is not marked `@[simp]`: `simp` already reaches `g ∈ U` through
`ContinuousMulEquiv.mem_compactOpenSubgroupOrderIso` and `ContinuousMulEquiv.symm_apply_apply`. -/
theorem apply_mem_compactOpenSubgroupOrderIso (e : G ≃ₜ* H) (U : TauCeti.CompactOpenSubgroup G)
    {g : G} : e g ∈ e.compactOpenSubgroupOrderIso U ↔ g ∈ U := by
  rw [e.mem_compactOpenSubgroupOrderIso, e.symm_apply_apply]

end ContinuousMulEquiv
