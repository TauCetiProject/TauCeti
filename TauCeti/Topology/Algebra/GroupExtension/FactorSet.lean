/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Homeomorph.TransferInstance
public import TauCeti.Algebra.GroupAction.TypeTags
public import TauCeti.GroupTheory.GroupExtension.Of.FactorSet
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree

/-!
# The topological group extension built from a continuous factor set

A factor set `α : FactorSet G M` builds the group extension `1 → M → E_α → G → 1` whose underlying
set is `M × G` and whose multiplication is twisted by `α`. When `G` and `M` are topological groups
and `α` is continuous, the product topology on `M × G` makes `E_α` a topological group, the
inclusion of `M` a closed embedding and the projection to `G` an open quotient map. For `G` a
profinite group and `M` a finite discrete module this exhibits `E_α` as a profinite group, which is
the extension attached to a continuous `2`-cocycle.

The topology is put on `TauCeti.FactorSet.Extension` unconditionally, as the product topology
transported along the coordinate equivalence `TauCeti.FactorSet.Extension.equivProd`; it is the
group structure, not the topology, that needs `α` to be continuous, and the separation, compactness
and disconnectedness instances below hold for every factor set.

Continuity of a factor set is membership of the explicit complex of continuous cochains:
`TauCeti.FactorSet.ofMul_mem_Z2_iff` says that `α` is continuous exactly when it is a continuous
`2`-cocycle in the sense of `TauCeti.ContCohomology.Z2`, once read additively through
`Additive.ofMul`. Conversely `TauCeti.FactorSet.ofMemZ2` names the factor set of a normalized
continuous `2`-cocycle, so the two descriptions of the data are interchangeable.

## Main definitions

* `TauCeti.FactorSet.Extension.equivProd`: the twisted product is `M × G` as a type, and
  `TauCeti.FactorSet.Extension.instTopologicalSpace` transports the product topology along it.
* `TauCeti.FactorSet.Extension.homeomorphProd`: the twisted product is `M × G` as a space.
* `TauCeti.FactorSet.ofMemZ2`: the factor set named by a normalized continuous `2`-cocycle.

## Main results

* `TauCeti.FactorSet.Extension.isTopologicalGroup`: a continuous factor set builds a topological
  group.
* `TauCeti.FactorSet.isClosedEmbedding_inl` and `TauCeti.FactorSet.isQuotientMap_rightHom`: the
  copy of `M` is a closed subgroup and the projection to `G` is an open quotient map, so
  `1 → M → E_α → G → 1` is an extension of topological groups.
* `TauCeti.FactorSet.continuous_canonicalSection`: the canonical section is continuous, so the
  extension built from a continuous factor set carries a continuous normalized section.
* `TauCeti.FactorSet.ofMul_mem_Z2_iff`: continuity of a factor set is membership of the explicit
  complex of continuous cochains.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §2, for the
  description of an extension of profinite groups by a continuous `2`-cocycle.
* L. Ribes, P. Zalesskii, *Profinite Groups*, 2nd ed., Ch. 6, §8.
-/

public section

namespace TauCeti

namespace FactorSet

universe u v

variable {G : Type u} {M : Type v} [Group G] [CommGroup M] [MulDistribMulAction G M]
  [TopologicalSpace G] [TopologicalSpace M]

namespace Extension

/-- **The twisted product is `M × G` as a type.** It is the multiplication that the factor set
twists, not the underlying set, so this is the equivalence along which the topology is
transported. -/
def equivProd (α : FactorSet G M) : α.Extension ≃ M × G where
  toFun x := (x.left, x.right)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [TopologicalSpace G] [TopologicalSpace M] in
@[simp]
theorem equivProd_apply {α : FactorSet G M} (x : α.Extension) :
    equivProd α x = (x.left, x.right) :=
  (rfl)

omit [TopologicalSpace G] [TopologicalSpace M] in
@[simp]
theorem equivProd_symm_apply {α : FactorSet G M} (p : M × G) :
    (equivProd α).symm p = ⟨p.1, p.2⟩ :=
  (rfl)

/-- The twisted product carries the product topology of `M × G`, transported along
`TauCeti.FactorSet.Extension.equivProd`; see `TauCeti.FactorSet.Extension.homeomorphProd`. -/
instance instTopologicalSpace (α : FactorSet G M) : TopologicalSpace α.Extension :=
  (equivProd α).topologicalSpace

variable {α : FactorSet G M}

/-- **The twisted product is `M × G` as a topological space.** The multiplication is twisted by the
factor set, the topology is not. -/
def homeomorphProd (α : FactorSet G M) : α.Extension ≃ₜ M × G := (equivProd α).homeomorph

@[simp]
theorem homeomorphProd_apply (x : α.Extension) : homeomorphProd α x = (x.left, x.right) := (rfl)

@[simp]
theorem homeomorphProd_symm_apply (p : M × G) :
    (homeomorphProd α).symm p = ⟨p.1, p.2⟩ :=
  (rfl)

/-- The defining property of the topology on the twisted product: it is induced from `M × G`.
This is the lemma every continuity argument about the twisted product goes through. -/
theorem isInducing_leftRight :
    Topology.IsInducing fun x : α.Extension => (x.left, x.right) :=
  (homeomorphProd α).isInducing

theorem continuous_left : Continuous (Extension.left : α.Extension → M) :=
  continuous_fst.comp isInducing_leftRight.continuous

theorem continuous_right : Continuous (Extension.right : α.Extension → G) :=
  continuous_snd.comp isInducing_leftRight.continuous

instance [T2Space M] [T2Space G] : T2Space α.Extension :=
  (homeomorphProd α).isEmbedding.t2Space

instance [CompactSpace M] [CompactSpace G] : CompactSpace α.Extension :=
  (homeomorphProd α).symm.compactSpace

instance [TotallyDisconnectedSpace M] [TotallyDisconnectedSpace G] :
    TotallyDisconnectedSpace α.Extension :=
  (homeomorphProd α).symm.totallyDisconnectedSpace

instance [DiscreteTopology M] [DiscreteTopology G] : DiscreteTopology α.Extension :=
  (homeomorphProd α).symm.discreteTopology

instance [Finite M] [Finite G] : Finite α.Extension :=
  .of_equiv _ (homeomorphProd α).symm.toEquiv

/-! ### The topological group structure -/

section TopologicalGroup

variable [IsTopologicalGroup G] [IsTopologicalGroup M] [ContinuousSMul G M]
  (hα : Continuous ⇑α)

include hα

private theorem continuous_mul_extension :
    Continuous fun p : α.Extension × α.Extension => p.1 * p.2 := by
  have hl₁ : Continuous fun p : α.Extension × α.Extension => p.1.left :=
    continuous_left.comp continuous_fst
  have hl₂ : Continuous fun p : α.Extension × α.Extension => p.2.left :=
    continuous_left.comp continuous_snd
  have hr₁ : Continuous fun p : α.Extension × α.Extension => p.1.right :=
    continuous_right.comp continuous_fst
  have hr₂ : Continuous fun p : α.Extension × α.Extension => p.2.right :=
    continuous_right.comp continuous_snd
  refine isInducing_leftRight.continuous_iff.2 ?_
  simp only [Function.comp_def, mul_left, mul_right]
  exact ((hl₁.mul (hr₁.smul hl₂)).mul (hα.comp (hr₁.prodMk hr₂))).prodMk (hr₁.mul hr₂)

private theorem continuous_inv_extension : Continuous fun x : α.Extension => x⁻¹ := by
  refine isInducing_leftRight.continuous_iff.2 ?_
  simp only [Function.comp_def, inv_left, inv_right]
  exact ((continuous_right.inv).smul
    ((continuous_left.mul (hα.comp (continuous_right.prodMk continuous_right.inv))).inv)).prodMk
    continuous_right.inv

/-- **A continuous factor set builds a topological group.** The twisted multiplication of
`TauCeti.FactorSet.Extension` is continuous for the product topology exactly because the factor set
appearing in it is. -/
theorem isTopologicalGroup : IsTopologicalGroup α.Extension where
  continuous_mul := continuous_mul_extension hα
  continuous_inv := continuous_inv_extension hα

end TopologicalGroup

end Extension

/-! ### The maps of the extension -/

section Maps

variable (α : FactorSet G M)

theorem continuous_inl : Continuous (inl α) := by
  refine Extension.isInducing_leftRight.continuous_iff.2 ?_
  simp only [Function.comp_def, inl_left, inl_right]
  exact continuous_id.prodMk continuous_const

theorem continuous_rightHom : Continuous (rightHom α) :=
  Extension.continuous_right.congr fun x => (rightHom_apply α x).symm

/-- The canonical section `g ↦ ⟨1, g⟩` of the projection is continuous: the extension built from a
continuous factor set comes with a continuous normalized section, and
`TauCeti.GroupExtension.factorSet_canonicalSection` reads the factor set back off it. -/
theorem continuous_canonicalSection : Continuous ⇑α.canonicalSection := by
  refine Extension.isInducing_leftRight.continuous_iff.2 ?_
  simp only [Function.comp_def, canonicalSection_apply]
  exact continuous_const.prodMk continuous_id

/-- The copy of `M` inside the twisted product is a closed subgroup, and carries the topology of
`M`. Only `G` needs a separation assumption: under `TauCeti.FactorSet.Extension.homeomorphProd`
the inclusion is `a ↦ (a, 1)`, whose range is the preimage of `{1}` under the projection to `G`. -/
theorem isClosedEmbedding_inl [T1Space G] : Topology.IsClosedEmbedding (inl α) := by
  have hcomp : (fun x : α.Extension => (x.left, x.right)) ∘ ⇑(inl α) = fun a : M => (a, (1 : G)) :=
    funext fun a => by simp
  have hrange : Set.range (inl α) = (Extension.right : α.Extension → G) ⁻¹' {1} := by
    ext x
    refine ⟨?_, fun hx => ⟨x.left, ?_⟩⟩
    · rintro ⟨a, rfl⟩
      simp
    · simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
      ext <;> simp [hx]
  refine ⟨⟨Topology.IsInducing.of_comp (continuous_inl α)
    Extension.isInducing_leftRight.continuous ?_, inl_injective α⟩, ?_⟩
  · rw [hcomp]
    exact isInducing_prodMkLeft 1
  · rw [hrange]
    exact isClosed_singleton.preimage Extension.continuous_right

/-- The projection of the twisted product onto `G` is open: under
`TauCeti.FactorSet.Extension.homeomorphProd` it is the projection `M × G → G`. -/
theorem isOpenMap_rightHom : IsOpenMap (rightHom α) := by
  have : ⇑(rightHom α) = Prod.snd ∘ Extension.homeomorphProd α := funext (rightHom_apply α)
  rw [this]
  exact isOpenMap_snd.comp (Extension.homeomorphProd α).isOpenMap

/-- **The projection of the twisted product onto `G` is a quotient map**, so `G` carries the
quotient topology of the extension by the copy of `M`. -/
theorem isQuotientMap_rightHom : Topology.IsQuotientMap (rightHom α) :=
  (isOpenMap_rightHom α).isQuotientMap (continuous_rightHom α) (rightHom_surjective α)

end Maps

/-! ### Continuity as membership of the explicit complex of continuous cochains -/

section Cocycle

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- A factor set, read additively, satisfies the additive `2`-cocycle identity: the two identities
are the same statement in the two notations. -/
theorem isCocycle₂_ofMul (α : FactorSet G M) :
    groupCohomology.IsCocycle₂ fun p : G × G => Additive.ofMul (α p) := fun g h j =>
  congrArg Additive.ofMul (α.isMulCocycle₂ g h j)

variable [IsTopologicalGroup M]

/-- **Continuity of a factor set is membership of the explicit complex of continuous cochains.**
Read additively, a factor set is a continuous `2`-cocycle in the sense of
`TauCeti.ContCohomology.Z2` exactly when it is continuous as a function. -/
theorem ofMul_mem_Z2_iff (α : FactorSet G M) :
    (fun p : G × G => Additive.ofMul (α p)) ∈ ContCohomology.Z2 G (Additive M) ↔
      Continuous ⇑α :=
  ContCohomology.mem_Z2_iff.trans
    ⟨fun h => h.1, fun h => ⟨h, α.isCocycle₂_ofMul⟩⟩

variable {z : G × G → Additive M}

/-- **The factor set named by a normalized continuous `2`-cocycle** of the explicit complex of
continuous cochains. Normalization is a hypothesis rather than a consequence: the cochains of that
complex are not normalized, and `TauCeti.ContCohomology.map_one_fst_of_mem_Z2` only says that the
value at `(1, g)` is the value at `(1, 1)`. -/
def ofMemZ2 (hz : z ∈ ContCohomology.Z2 G (Additive M)) (hz₁ : z (1, 1) = 0) : FactorSet G M where
  toFun p := (z p).toMul
  isMulCocycle₂' g h j := congrArg Additive.toMul ((ContCohomology.mem_Z2_iff.1 hz).2 g h j)
  map_one_one' := congrArg Additive.toMul hz₁

@[simp]
theorem ofMemZ2_apply (hz : z ∈ ContCohomology.Z2 G (Additive M)) (hz₁ : z (1, 1) = 0)
    (p : G × G) : ofMemZ2 hz hz₁ p = (z p).toMul :=
  (rfl)

theorem continuous_ofMemZ2 (hz : z ∈ ContCohomology.Z2 G (Additive M)) (hz₁ : z (1, 1) = 0) :
    Continuous ⇑(ofMemZ2 hz hz₁) :=
  (ContCohomology.mem_Z2_iff.1 hz).1

end Cocycle

end FactorSet

end TauCeti
