/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Rep.Res
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Basic

/-!
# Restrictions of a finite normal layer, and its finite quotient system

Let `V ◁ U` be a finite normal layer of a formation, the layer `K/F` in field notation. Raising
the ground field to an intermediate field `F ⊆ E ⊆ K` leaves a layer `K/E`, again normal because
`V` stays normal in the smaller ground subgroup. Two layers are related by a **restriction** when
they have the same top subgroup and the ground subgroup of the first lies in the ground subgroup
of the second; `LayerRestriction small big` is that relation. Its **relative degree** is
`[U : U']`, the degree `[E : F]` of the new ground field over the old one. This convention is
intended to support the corestriction normalisation `cor ∘ res = [E : F]`; `⚠` it is the index
of the *sub*group `U'` in `U`, not the other way round.

Restrictions of a fixed layer are the same thing as subgroups of its Galois group: `U'` is
recovered from `H = U'/V ≤ Γ`, and this **finite quotient system** `H ↦ subgroupLayer H` is what
Tate's theorem quantifies over. The two directions of the correspondence appear below as
`NormalLayer.subgroupGround`, which builds the intermediate subgroup out of `H`, and
`NormalLayer.subgroupGalEquiv`, which identifies the Galois group of the resulting layer with `H`
again.

Three facts make the system usable in the cohomological arguments downstream. The Galois group of
the smaller layer maps to the Galois group of the bigger one (`LayerRestriction.galHom`), and does
so injectively; the degrees multiply along the restriction
(`LayerRestriction.degree_mul_relativeDegree`); and — because the two layers have the *same* top
subgroup, hence the same coefficient module `A^V` — the coefficient module of the smaller layer
*is* the coefficient module of the bigger one, restricted along `galHom`
(`LayerRestriction.repIso`). It is that last identification which lets a cohomology class of the
layer be restricted to a subgroup of its Galois group at all.

## Main definitions

* `TauCeti.ClassFieldTheory.LayerRestriction`: the relation `small` is `big` with its ground field
  raised to an intermediate field.
* `TauCeti.ClassFieldTheory.LayerRestriction.relativeDegree`: the relative degree `[U : U']`.
* `TauCeti.ClassFieldTheory.LayerRestriction.galHom`: the induced homomorphism `U'/V → U/V`.
* `TauCeti.ClassFieldTheory.LayerRestriction.repIso`: the coefficient module of the smaller layer
  is the coefficient module of the bigger layer, restricted along `galHom`.
* `TauCeti.ClassFieldTheory.NormalLayer.subgroupGround`: the intermediate open subgroup attached
  to a subgroup of the Galois group.
* `TauCeti.ClassFieldTheory.NormalLayer.subgroupLayer`: the layer of a subgroup of the Galois
  group, and `TauCeti.ClassFieldTheory.NormalLayer.subgroupRestriction`, the restriction relating
  it to the layer it comes from.
* `TauCeti.ClassFieldTheory.NormalLayer.subgroupGalEquiv`: the Galois group of that layer is the
  chosen subgroup.

## Main statements

* `TauCeti.ClassFieldTheory.LayerRestriction.galHom_injective`: the Galois group of the smaller
  layer embeds in the Galois group of the bigger one.
* `TauCeti.ClassFieldTheory.LayerRestriction.degree_mul_relativeDegree`:
  `[U' : V] * [U : U'] = [U : V]`.
* `TauCeti.ClassFieldTheory.NormalLayer.degree_subgroupLayer`: the layer of `H` has degree `#H`.
* `TauCeti.ClassFieldTheory.NormalLayer.relativeDegree_subgroupRestriction`: its relative degree
  is the index of `H`.
* `TauCeti.ClassFieldTheory.NormalLayer.galHom_subgroupRestriction`: the homomorphism of Galois
  groups it induces is the inclusion of `H`.
* `TauCeti.ClassFieldTheory.NormalLayer.subgroupLayer_top`: the layer of the whole Galois group is
  the layer itself.

## Implementation notes

`LayerRestriction` is a relation between two layers that already exist, not a bundle carrying a
layer and constructing a second one. This is what lets the downstream restriction and
corestriction maps be stated for an arbitrary pair `small`, `big` of layers, and it makes towers
of restrictions compose without transporting a layer along an equality. Because it is a `Prop`,
the relative degree cannot be read off the datum itself: `relativeDegree` is a function of the two
layers, and takes the restriction proof to make that dependency explicit and support the notation
`T.relativeDegree`.

`NormalLayer.subgroupGround` is the correspondence-theorem preimage of `H` — the subgroup
`QuotientGroup.comapMk'OrderIso` attaches to `H` — pushed from `U` into the ambient group `G`, so
that it can be an `OpenSubgroup G` and be compared with the other subgroups of a formation.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§1–2.
* J. Neukirch, *Class Field Theory*, Chapter III, §1.
* J. Tate, *The higher dimensional cohomology groups of class field theory*, Ann. of Math. **56**
  (1952), 294–297.
* TauCetiRoadmap, `TauCetiRoadmap/ClassFieldTheory/Suggested.lean`.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-! ### Restrictions -/

/-- A **restriction** of finite normal layers: `small` is `big` with its ground field raised to an
intermediate field. In field notation, `F ⊆ E ⊆ K` takes the layer `K/F` to the layer `K/E`, so
the top subgroup is unchanged and the ground subgroup shrinks. -/
structure LayerRestriction (small big : NormalLayer G) : Prop where
  /-- a restriction does not move the top subgroup -/
  same_top : small.top = big.top
  /-- a restriction shrinks the ground subgroup -/
  ground_le : small.ground ≤ big.ground

namespace LayerRestriction

variable {small big : NormalLayer G}

/-- The ground subgroups of a restriction, compared as subgroups of the ambient group. -/
theorem ground_toSubgroup_le (T : LayerRestriction small big) :
    small.ground.toSubgroup ≤ big.ground.toSubgroup :=
  OpenSubgroup.toSubgroup_le.2 T.ground_le

/-- The top subgroups of a restriction, compared as subgroups of the ambient group. -/
theorem same_top_toSubgroup (T : LayerRestriction small big) :
    small.top.toSubgroup = big.top.toSubgroup :=
  congrArg OpenSubgroup.toSubgroup T.same_top

/-- The **relative degree** `[U : U']` of a restriction, the degree of the new ground field over
the old one. `⚠` `U'` is the subgroup, so the relative degree is the index of `U'` in `U`. -/
def relativeDegree (_T : LayerRestriction small big) : ℕ :=
  small.ground.toSubgroup.relIndex big.ground.toSubgroup

/-- The relative degree is the relative index of the two ground subgroups. -/
@[simp]
theorem relativeDegree_def (T : LayerRestriction small big) :
    T.relativeDegree = small.ground.toSubgroup.relIndex big.ground.toSubgroup :=
  relativeDegree.eq_1 T

/-- **The degree of a layer is multiplicative along a restriction:** `[U' : V] * [U : U'] =
[U : V]`. -/
theorem degree_mul_relativeDegree (T : LayerRestriction small big) :
    small.degree * T.relativeDegree = big.degree := by
  rw [NormalLayer.degree_eq_relIndex, NormalLayer.degree_eq_relIndex, relativeDegree_def,
    ← T.same_top_toSubgroup]
  exact Subgroup.relIndex_mul_relIndex _ _ _
    (OpenSubgroup.toSubgroup_le.2 small.top_le_ground) T.ground_toSubgroup_le

/-- The relative degree of a restriction is positive: the Galois groups involved are finite. -/
theorem relativeDegree_pos (T : LayerRestriction small big) : 0 < T.relativeDegree :=
  Nat.pos_of_mul_pos_left (T.degree_mul_relativeDegree ▸ big.degree_pos)

/-- The homomorphism `U'/V → U/V` of Galois groups induced by a restriction. It is injective
(`galHom_injective`), and its image is the subgroup of `U/V` that the intermediate subgroup `U'`
cuts out. -/
def galHom (T : LayerRestriction small big) : small.Gal →* big.Gal :=
  @QuotientGroup.quotientMapSubgroupOfOfLe G _ small.top.toSubgroup small.ground.toSubgroup
    big.top.toSubgroup big.ground.toSubgroup small.normal big.normal
    T.same_top_toSubgroup.le T.ground_toSubgroup_le

/-- The homomorphism of Galois groups is induced by the inclusion of ground subgroups. -/
@[simp]
theorem galHom_mk (T : LayerRestriction small big) (w : small.ground) :
    T.galHom (QuotientGroup.mk w) =
      QuotientGroup.mk (Subgroup.inclusion T.ground_toSubgroup_le w) :=
  @QuotientGroup.quotientMapSubgroupOfOfLe_mk G _ small.top.toSubgroup
    small.ground.toSubgroup big.top.toSubgroup big.ground.toSubgroup small.normal big.normal
    T.same_top_toSubgroup.le T.ground_toSubgroup_le w

/-- **The Galois group of the smaller layer of a restriction embeds in the Galois group of the
bigger one.** Both are quotients of subgroups of `U` by the *same* top subgroup `V`. -/
theorem galHom_injective (T : LayerRestriction small big) : Function.Injective T.galHom := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  induction γ using QuotientGroup.induction_on with
  | H w =>
    rw [galHom_mk] at hγ
    have hw := Subgroup.mem_subgroupOf.1
      ((QuotientGroup.eq_one_iff (N := big.relativeTop) _).1 hγ)
    refine (QuotientGroup.eq_one_iff w).2 (Subgroup.mem_subgroupOf.2 ?_)
    rw [T.same_top_toSubgroup]
    exact hw

/-- **The coefficient module of the smaller layer of a restriction is the coefficient module of
the bigger one**, read as a representation of the smaller Galois group along `galHom`. The two
modules are the level `A^V` of one and the same top subgroup — a restriction does not move the top
subgroup — so this isomorphism moves no element of the ambient module. -/
def repIso (T : LayerRestriction small big) (F : Formation G) :
    small.rep F ≅ Rep.res T.galHom (big.rep F) :=
  Rep.mkIso <| Representation.Equiv.mk
    (LinearEquiv.ofEq _ _ (congrArg F.level T.same_top)) fun γ ↦ by
      induction γ using QuotientGroup.induction_on with
      | H w =>
        simp only [MonoidHom.coe_comp, Function.comp_apply]
        rw [galHom_mk]
        ext x
        -- `Rep.mkIso` hides the common ambient-module coercions behind nested representation and
        -- linear-equivalence wrappers, so expose them before applying the public coercion lemmas.
        change
          ((LinearEquiv.ofEq _ _ (congrArg F.level T.same_top)
              ((small.rep F).ρ (QuotientGroup.mk w) x) : F.level big.top) : F.toRep.V) =
            (((big.rep F).ρ
              (QuotientGroup.mk (Subgroup.inclusion T.ground_toSubgroup_le w))
              (LinearEquiv.ofEq _ _ (congrArg F.level T.same_top) x) : F.level big.top) :
                F.toRep.V)
        calc
          _ = (((small.rep F).ρ (QuotientGroup.mk w) x : F.level small.top) : F.toRep.V) :=
            LinearEquiv.coe_ofEq_apply (congrArg F.level T.same_top) _
          _ = F.toRep.ρ (w : G) x := small.rep_ρ_mk_apply_coe F w x
          _ = F.toRep.ρ
                ((Subgroup.inclusion T.ground_toSubgroup_le w : big.ground) : G)
                (LinearEquiv.ofEq _ _ (congrArg F.level T.same_top) x) := by
            rw [Subgroup.coe_inclusion, LinearEquiv.coe_ofEq_apply]
          _ = _ := (big.rep_ρ_mk_apply_coe F
            (Subgroup.inclusion T.ground_toSubgroup_le w) _).symm

/-- The identification of coefficient modules moves no element of the ambient module. -/
@[simp]
theorem repIso_hom_apply_coe (T : LayerRestriction small big) (F : Formation G)
    (x : F.level small.top) :
    (((T.repIso F).hom.hom x : F.level big.top) : F.toRep.V) = (x : F.toRep.V) :=
  LinearEquiv.coe_ofEq_apply (congrArg F.level T.same_top) x

end LayerRestriction

/-! ### The finite quotient system -/

namespace NormalLayer

variable (L : NormalLayer G) (H : Subgroup L.Gal)

/-- The intermediate subgroup `V ≤ W ≤ U` attached to a subgroup `H` of the Galois group `U ⧸ V`:
the preimage of `H` in `U`, read inside `G`. -/
def subgroupGround : Subgroup G :=
  ((QuotientGroup.comapMk'OrderIso L.relativeTop H).1).map L.ground.toSubgroup.subtype

/-- Membership in the intermediate subgroup: an element of `U` lies in it exactly when its class
in the Galois group lies in `H`. -/
@[simp]
theorem mem_subgroupGround {g : G} :
    g ∈ L.subgroupGround H ↔ ∃ hg : g ∈ L.ground, (QuotientGroup.mk ⟨g, hg⟩ : L.Gal) ∈ H := by
  constructor
  · rintro ⟨⟨u, hu⟩, hmem, rfl⟩
    exact ⟨hu, hmem⟩
  · rintro ⟨hg, hmem⟩
    exact ⟨⟨g, hg⟩, hmem, rfl⟩

/-- The intermediate subgroup lies in the ground subgroup. -/
theorem subgroupGround_le_ground : L.subgroupGround H ≤ L.ground.toSubgroup :=
  fun _ hg ↦ ((L.mem_subgroupGround H).1 hg).fst

/-- The intermediate subgroup contains the top subgroup, which is where the layer of `H` gets its
normality from. -/
theorem top_le_subgroupGround : L.top.toSubgroup ≤ L.subgroupGround H := by
  intro v hv
  refine (L.mem_subgroupGround H).2 ⟨L.top_le_ground hv, ?_⟩
  have h1 : (QuotientGroup.mk (⟨v, L.top_le_ground hv⟩ : L.ground) : L.Gal) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hv)
  rw [h1]
  exact one_mem H

/-- The **layer of a subgroup** `H ≤ U ⧸ V`: the finite normal layer `V ◁ W` whose ground subgroup
is the preimage `W` of `H`. The family `H ↦ subgroupLayer H` is the finite quotient system that
Tate's theorem quantifies over. -/
def subgroupLayer : NormalLayer G where
  ground := ⟨L.subgroupGround H, Subgroup.isOpen_mono (L.top_le_subgroupGround H) L.top.isOpen⟩
  top := L.top
  top_le_ground := OpenSubgroup.toSubgroup_le.1 (L.top_le_subgroupGround H)
  normal := ⟨fun _v hv w ↦ Subgroup.mem_subgroupOf.2 (L.conj_mem_top
    (L.subgroupGround_le_ground H w.2) (Subgroup.mem_subgroupOf.1 hv))⟩

/-- The ground subgroup of the layer of `H` is the preimage of `H`. -/
@[simp]
theorem ground_subgroupLayer :
    (L.subgroupLayer H).ground.toSubgroup = L.subgroupGround H :=
  congrArg (fun M : NormalLayer G ↦ M.ground.toSubgroup) (subgroupLayer.eq_1 L H)

/-- The layer of `H` has the same top subgroup, hence the same coefficient module, as the layer
it comes from. -/
@[simp]
theorem top_subgroupLayer : (L.subgroupLayer H).top = L.top := by
  simpa only using
    congrArg (fun M : NormalLayer G ↦ M.top) (subgroupLayer.eq_1 L H)

/-- **The layer of `H` is a restriction of the layer it comes from:** it has the same top field
and a smaller ground field. This is the datum through which cohomology of the layer restricts to
the layer of `H`. -/
theorem subgroupRestriction : LayerRestriction (L.subgroupLayer H) L :=
  ⟨rfl, OpenSubgroup.toSubgroup_le.1 (L.subgroupGround_le_ground H)⟩

/-- The image of the Galois group of the layer of `H` is `H`. -/
theorem range_galHom_subgroupRestriction : (L.subgroupRestriction H).galHom.range = H := by
  ext γ
  constructor
  · rintro ⟨δ, rfl⟩
    induction δ using QuotientGroup.induction_on with
    | H w =>
      obtain ⟨_, hmem⟩ := (L.mem_subgroupGround H).1 w.2
      rw [LayerRestriction.galHom_mk]
      exact congrArg (fun x : L.ground ↦ (QuotientGroup.mk x : L.Gal)) (Subtype.ext rfl) ▸ hmem
  · intro hγ
    induction γ using QuotientGroup.induction_on with
    | H u =>
      refine ⟨QuotientGroup.mk ⟨(u : G), (L.mem_subgroupGround H).2 ⟨u.2, hγ⟩⟩, ?_⟩
      rw [LayerRestriction.galHom_mk]
      congr 1

/-- **The Galois group of the layer of `H` is `H`.** -/
def subgroupGalEquiv : (L.subgroupLayer H).Gal ≃* H :=
  (MonoidHom.ofInjective (L.subgroupRestriction H).galHom_injective).trans
    (MulEquiv.subgroupCongr (L.range_galHom_subgroupRestriction H))

/-- The identification of the Galois group of the layer of `H` with `H` is the homomorphism of
Galois groups of the restriction. -/
@[simp]
theorem subgroupGalEquiv_apply_coe (γ : (L.subgroupLayer H).Gal) :
    ((L.subgroupGalEquiv H γ : H) : L.Gal) = (L.subgroupRestriction H).galHom γ :=
  (MulEquiv.subgroupCongr_apply (L.range_galHom_subgroupRestriction H)
      (MonoidHom.ofInjective (L.subgroupRestriction H).galHom_injective γ)).trans
    (MonoidHom.ofInjective_apply (L.subgroupRestriction H).galHom_injective)

/-- **The degree of the layer of `H` is the order of `H`.** -/
theorem degree_subgroupLayer : (L.subgroupLayer H).degree = Nat.card H := by
  rw [degree_eq_natCard_gal]
  exact Nat.card_congr (L.subgroupGalEquiv H).toEquiv

/-- The homomorphism of Galois groups attached to the restriction to `H` is the inclusion of `H`,
read through `subgroupGalEquiv`. -/
theorem galHom_subgroupRestriction :
    (L.subgroupRestriction H).galHom = H.subtype.comp (L.subgroupGalEquiv H).toMonoidHom :=
  MonoidHom.ext fun γ ↦ (L.subgroupGalEquiv_apply_coe H γ).symm

/-- **The relative degree of the restriction to `H` is the index of `H`.** -/
theorem relativeDegree_subgroupRestriction :
    (L.subgroupRestriction H).relativeDegree = H.index := by
  rw [LayerRestriction.relativeDegree_def, ground_subgroupLayer, Subgroup.relIndex,
    ← Subgroup.comap_subtype, subgroupGround,
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
  exact Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective L.relativeTop)

/-- The intermediate subgroup of the whole Galois group is the ground subgroup. -/
@[simp]
theorem subgroupGround_top : L.subgroupGround ⊤ = L.ground.toSubgroup := by
  ext g
  simp [mem_subgroupGround]

/-- The layer of the whole Galois group is the layer itself. -/
@[simp]
theorem subgroupLayer_top : L.subgroupLayer ⊤ = L :=
  NormalLayer.ext
    (OpenSubgroup.toSubgroup_injective (by rw [ground_subgroupLayer, subgroupGround_top]))
    (L.top_subgroupLayer ⊤)

end NormalLayer

end TauCeti.ClassFieldTheory
