/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Order.Filter.CountablyGenerated
public import TauCeti.Topology.Algebra.Group.ContinuousAut.Basic
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.Compact
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

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
* A topological group isomorphism transports compact open subgroups. In particular the group of
  continuous automorphisms acts on the index by order isomorphisms, and conjugation by `g`,
  `U ↦ g U g⁻¹`, through `TauCeti.ContinuousAut.conj`. This is a reindexing of the levels, not an
  arrow of the index: conjugation by `diag(p, 1)` moves `GL₂(ℤ_p)` to a different compact open
  subgroup of `GL₂(ℚ_p)`. Transport by `g` followed by transport by `h` is transport by `h * g`.
* In a first countable nonarchimedean group, such as a `p`-adic Lie group, every compact open
  `K₀` contains a descending sequence of compact open subgroups, each normalized by `K₀`, that is
  a neighbourhood basis of the identity. Their quotients `K₀ ⧸ U r` are the finite deck groups
  of a tower over level `K₀`.

## Main definitions

* `TauCeti.CompactOpenSubgroup G`: the compact open subgroups of `G`, with additive version
  `TauCeti.CompactOpenAddSubgroup G`.
* `ContinuousMulEquiv.compactOpenSubgroupOrderIso`: transport of compact open subgroups along an
  isomorphism of topological groups.
* The action of `TauCeti.ContinuousAut G` on `TauCeti.CompactOpenSubgroup G` by images.

## Main results

* `TauCeti.CompactOpenSubgroup.nhds_one_hasBasis`: in a locally profinite group the compact open
  subgroups form a basis of neighbourhoods of the identity.
* `TauCeti.CompactOpenSubgroup.initial_functor_iff`: a monotone codirected family of compact
  open subgroups is initial in the index exactly when it is a neighbourhood basis of the identity;
  `TauCeti.CompactOpenSubgroup.initial_functor_of_forall_mem_nhds` is the unconditional direction,
  and `TauCeti.CompactOpenSubgroup.initial_functor_Iic_of_forall_mem_nhds` its version below a
  fixed level.
* `TauCeti.CompactOpenSubgroup.exists_le_conj_smul_eq`: every open subgroup contains a compact
  open subgroup of a given compact open `K₀` which is normalized by `K₀`.
* `TauCeti.CompactOpenSubgroup.exists_hasAntitoneBasis_conj_smul_eq`: a descending sequence of
  compact open subgroups normalized by `K₀` forms a neighbourhood basis of the identity.

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
subgroup: an open subgroup is closed, and a closed subset of a compact set is compact. -/
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
  toFun U :=
    { toSubgroup := e.toMulEquiv.mapSubgroup U.toSubgroup
      isOpen' := by
        -- The carrier of `Subgroup.map` is stored as an existential rather than an image.
        change IsOpen (e '' (U : Set G))
        exact e.toHomeomorph.isOpen_image.mpr U.isOpen
      isCompact' := by
        -- The carrier of `Subgroup.map` is stored as an existential rather than an image.
        change IsCompact (e '' (U : Set G))
        exact U.isCompact.image e.continuous }
  invFun V :=
    { toSubgroup := e.toMulEquiv.mapSubgroup.symm V.toSubgroup
      isOpen' := by
        -- The carrier of `Subgroup.map` is stored as an existential rather than an image.
        change IsOpen (e.symm '' (V : Set H))
        exact e.symm.toHomeomorph.isOpen_image.mpr V.isOpen
      isCompact' := by
        -- The carrier of `Subgroup.map` is stored as an existential rather than an image.
        change IsCompact (e.symm '' (V : Set H))
        exact V.isCompact.image e.symm.continuous }
  left_inv U := TauCeti.CompactOpenSubgroup.toOpenSubgroup_injective <|
    OpenSubgroup.toSubgroup_injective (e.toMulEquiv.mapSubgroup.left_inv U.toSubgroup)
  right_inv V := TauCeti.CompactOpenSubgroup.toOpenSubgroup_injective <|
    OpenSubgroup.toSubgroup_injective (e.toMulEquiv.mapSubgroup.right_inv V.toSubgroup)
  map_rel_iff' := e.toMulEquiv.mapSubgroup.map_rel_iff

/-- The transport of a compact open subgroup is its image. -/
@[simp, norm_cast]
theorem coe_compactOpenSubgroupOrderIso (e : G ≃ₜ* H) (U : TauCeti.CompactOpenSubgroup G) :
    (e.compactOpenSubgroupOrderIso U : Set H) = e '' U :=
  Set.ext fun _ ↦ Subgroup.mem_map

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

end ContinuousMulEquiv

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace ContinuousAut

/-- A continuous automorphism acts on compact open subgroups by taking images. -/
instance : MulAction (ContinuousAut G) (CompactOpenSubgroup G) where
  smul φ U := φ.compactOpenSubgroupOrderIso U
  one_smul U :=
    CompactOpenSubgroup.ext fun _ ↦ ContinuousMulEquiv.mem_compactOpenSubgroupOrderIso _ U
  mul_smul φ ψ U := CompactOpenSubgroup.ext fun _ ↦
    ((φ * ψ).mem_compactOpenSubgroupOrderIso U).trans <|
      (ψ.mem_compactOpenSubgroupOrderIso U).symm.trans (φ.mem_compactOpenSubgroupOrderIso _).symm

/-- The action of a continuous automorphism on compact open subgroups is transport along it by
`ContinuousMulEquiv.compactOpenSubgroupOrderIso`, so that order isomorphism API applies to it. -/
theorem smul_compactOpenSubgroup_def (φ : ContinuousAut G) (U : CompactOpenSubgroup G) :
    φ • U = φ.compactOpenSubgroupOrderIso U :=
  (rfl)

/-- An element lies in `φ • U` exactly when its preimage under `φ` lies in `U`. -/
@[simp]
theorem mem_smul_compactOpenSubgroup_iff {φ : ContinuousAut G} {U : CompactOpenSubgroup G}
    {x : G} : x ∈ φ • U ↔ φ.symm x ∈ U :=
  φ.mem_compactOpenSubgroupOrderIso U

/-- The underlying set of `φ • U` is the image of `U` under `φ`. -/
@[simp, norm_cast]
theorem coe_smul_compactOpenSubgroup (φ : ContinuousAut G) (U : CompactOpenSubgroup G) :
    ((φ • U : CompactOpenSubgroup G) : Set G) = φ '' U :=
  φ.coe_compactOpenSubgroupOrderIso U

/-- Transport by a continuous automorphism preserves and reflects inclusion. -/
@[simp]
theorem smul_compactOpenSubgroup_le_smul_iff {φ : ContinuousAut G}
    {U V : CompactOpenSubgroup G} : φ • U ≤ φ • V ↔ U ≤ V :=
  φ.compactOpenSubgroupOrderIso.le_iff_le

/-- Transport by a continuous automorphism commutes with common refinements. -/
theorem smul_compactOpenSubgroup_inf [SeparatelyContinuousMul G] (φ : ContinuousAut G)
    (U V : CompactOpenSubgroup G) : φ • (U ⊓ V) = φ • U ⊓ φ • V :=
  φ.compactOpenSubgroupOrderIso.map_inf U V

section Conj

variable [SeparatelyContinuousMul G]

/-- An element lies in the conjugate `g U g⁻¹` exactly when its conjugate `g⁻¹ x g` lies
in `U`. -/
theorem mem_conj_smul_compactOpenSubgroup_iff {g x : G} {U : CompactOpenSubgroup G} :
    x ∈ conj g • U ↔ g⁻¹ * x * g ∈ U := by
  rw [mem_smul_compactOpenSubgroup_iff, conj_symm_apply]

/-- Conjugating a compact open subgroup by one of its own elements does not move it. -/
theorem conj_smul_compactOpenSubgroup_eq_self_of_mem {g : G} {U : CompactOpenSubgroup G}
    (hg : g ∈ U) : conj g • U = U :=
  CompactOpenSubgroup.ext fun x ↦ by
    rw [mem_conj_smul_compactOpenSubgroup_iff]
    refine ⟨fun h ↦ ?_, fun h ↦ mul_mem (mul_mem (inv_mem hg) h) hg⟩
    simpa [mul_assoc] using mul_mem (mul_mem hg h) (inv_mem hg)

end Conj

end ContinuousAut

namespace CompactOpenSubgroup

/-! ### Normal bases below a level -/

section NormalBasis

/-- **Normal cores below a level.** Every open subgroup `W` contains a compact open subgroup of a
given compact open subgroup `K₀` which is normalized by `K₀`: the normal core in `K₀` of
`W ∩ K₀`, which is open because `W ∩ K₀` has finite index in the compact group `K₀`. -/
theorem exists_le_conj_smul_eq [SeparatelyContinuousMul G] (K₀ : CompactOpenSubgroup G)
    (W : OpenSubgroup G) :
    ∃ N : CompactOpenSubgroup G, N.toOpenSubgroup ≤ W ∧ N ≤ K₀ ∧
      ∀ k ∈ K₀, ContinuousAut.conj k • N = N := by
  set K := K₀.toSubgroup
  -- The normal core in `K₀` of the trace of `W` on `K₀`, an open normal subgroup of `K₀`.
  let W' : OpenSubgroup K := W.comap K.subtype continuous_subtype_val
  let C : Subgroup K := W'.toSubgroup.normalCore
  have hCK : ((C.map K.subtype : Subgroup G) : Set G) ⊆ K₀ := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  let N₀ : OpenSubgroup G :=
    ⟨C.map K.subtype, K₀.isOpen.isOpenMap_subtype_val _ W'.isOpen_normalCore⟩
  let N : CompactOpenSubgroup G := ⟨N₀, K₀.isCompact.of_isClosed_subset N₀.isClosed hCK⟩
  have hmem (x : G) : x ∈ N ↔ x ∈ C.map K.subtype := Iff.rfl
  -- Conjugation by elements of `K₀` maps the core into itself, hence onto itself.
  have hle : ∀ k ∈ K₀, ∀ x ∈ N, k * x * k⁻¹ ∈ N := by
    rintro k hk x hx
    obtain ⟨c, hc, rfl⟩ := (hmem x).1 hx
    exact (hmem _).2 ⟨⟨k, hk⟩ * c * ⟨k, hk⟩⁻¹,
      (Subgroup.normalCore_normal _).conj_mem c hc ⟨k, hk⟩, rfl⟩
  refine ⟨N, ?_, hCK, fun k hk ↦ CompactOpenSubgroup.ext fun x ↦ ?_⟩
  · intro y hy
    obtain ⟨c, hc, rfl⟩ := (hmem y).1 hy
    exact Subgroup.normalCore_le W'.toSubgroup hc
  rw [ContinuousAut.mem_conj_smul_compactOpenSubgroup_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hle k hk _ h
  · simpa only [inv_inv] using hle k⁻¹ (inv_mem hk) x h

/-- **A descending normal basis below a level.** In a first countable nonarchimedean group, every
compact open subgroup `K₀` contains a descending sequence of compact open subgroups, each
normalized by `K₀`, which is a basis of neighbourhoods of the identity. -/
theorem exists_hasAntitoneBasis_conj_smul_eq [NonarchimedeanGroup G] [FirstCountableTopology G]
    (K₀ : CompactOpenSubgroup G) :
    ∃ U : ℕ → CompactOpenSubgroup G, (𝓝 (1 : G)).HasAntitoneBasis (fun r ↦ (U r : Set G)) ∧
      (∀ r, U r ≤ K₀) ∧ ∀ r, ∀ k ∈ K₀, ContinuousAut.conj k • U r = U r := by
  obtain ⟨x, hx⟩ := (𝓝 (1 : G)).exists_antitone_basis
  -- An open subgroup inside each `x n`, and the normal core in `K₀` of its trace on `K₀`.
  have hW (n : ℕ) : ∃ W : OpenSubgroup G, (W : Set G) ⊆ x n :=
    NonarchimedeanGroup.is_nonarchimedean _ (hx.mem n)
  choose W hW using hW
  choose N hNW hNK hNc using fun n ↦ K₀.exists_le_conj_smul_eq (W n)
  -- The running intersections of the normal cores.
  let U : ℕ → CompactOpenSubgroup G := fun k ↦ Nat.rec (N 0) (fun i M ↦ M ⊓ N (i + 1)) k
  have hUN (n : ℕ) : U n ≤ N n := by
    cases n with
    | zero => exact le_rfl
    | succ i => exact inf_le_right
  have hUc (n : ℕ) : ∀ k ∈ K₀, ContinuousAut.conj k • U n = U n := by
    intro k hk
    induction n with
    | zero => exact hNc 0 k hk
    | succ i ih =>
      -- `U (i + 1)` is `U i ⊓ N (i + 1)` by the recursion defining `U`.
      change ContinuousAut.conj k • (U i ⊓ N (i + 1)) = U i ⊓ N (i + 1)
      rw [ContinuousAut.smul_compactOpenSubgroup_inf, ih, hNc _ k hk]
  have hUx (n : ℕ) : ∀ y ∈ U n, y ∈ x n :=
    fun _ h ↦ hW n (hNW n (hUN n h))
  refine ⟨U, ⟨hx.1.to_hasBasis (fun n _ ↦ ⟨n, trivial, hUx n⟩)
    fun n _ ↦ hx.1.mem_iff.1 (U n).mem_nhds_one,
    antitone_nat_of_succ_le fun _ ↦ SetLike.coe_subset_coe.2 inf_le_left⟩,
    fun n ↦ (hUN n).trans (hNK n), hUc⟩

end NormalBasis

end CompactOpenSubgroup

end TauCeti
