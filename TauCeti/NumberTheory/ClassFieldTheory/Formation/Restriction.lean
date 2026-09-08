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
`V` stays normal in the smaller ground subgroup. A **restriction datum** for the layer is exactly
the choice of that intermediate field: an open subgroup `U'` with `V ≤ U' ≤ U`. Its
**relative degree** is `[U : U']`, the degree `[E : F]` of the new ground field over the old one;
the roadmap's corestriction normalisation `cor ∘ res = [E : F]` is stated with this number, and
`⚠` it is the index of the *sub*group `U'` in `U`, not the other way round.

Restriction data on a fixed layer are the same thing as subgroups of its Galois group: `U'` is
recovered from `H = U'/V ≤ Γ`, and this **finite quotient system** `H ↦ subgroupLayer H` is what
Tate's theorem quantifies over. The two directions of the correspondence appear below as
`NormalLayer.subgroupGround`, which builds the intermediate subgroup out of `H`, and
`NormalLayer.subgroupGalEquiv`, which identifies the Galois group of the resulting layer with `H`
again.

Three facts make the system usable in the cohomological arguments downstream. The Galois group of
a restricted layer maps to the Galois group of the original one (`LayerRestriction.galHom`), and
does so injectively; the degrees multiply along the restriction
(`LayerRestriction.degree_layer_mul_relativeDegree`); and — because the two layers have the *same*
top subgroup, hence literally the same coefficient module `A^V` — the coefficient module of the
restricted layer *is* the coefficient module of the original one, restricted along `galHom`
(`LayerRestriction.repIso`). It is that last identification which lets a cohomology class of the
layer be restricted to a subgroup of its Galois group at all.

## Main definitions

* `TauCeti.ClassFieldTheory.LayerRestriction`: a restriction datum for a finite normal layer, an
  intermediate open subgroup `V ≤ U' ≤ U`.
* `TauCeti.ClassFieldTheory.LayerRestriction.layer`: the restricted layer `V ◁ U'`.
* `TauCeti.ClassFieldTheory.LayerRestriction.relativeDegree`: the relative degree `[U : U']`.
* `TauCeti.ClassFieldTheory.LayerRestriction.galHom`: the induced homomorphism `U'/V → U/V`.
* `TauCeti.ClassFieldTheory.LayerRestriction.repIso`: the coefficient module of the restricted
  layer is the coefficient module of the original layer, restricted along `galHom`.
* `TauCeti.ClassFieldTheory.NormalLayer.subgroupGround`: the intermediate open subgroup attached
  to a subgroup of the Galois group.
* `TauCeti.ClassFieldTheory.NormalLayer.subgroupRestriction`,
  `TauCeti.ClassFieldTheory.NormalLayer.subgroupLayer`: the restriction datum and the layer of a
  subgroup of the Galois group.
* `TauCeti.ClassFieldTheory.NormalLayer.subgroupGalEquiv`: the Galois group of that layer is the
  chosen subgroup.

## Main statements

* `TauCeti.ClassFieldTheory.LayerRestriction.galHom_injective`: the Galois group of a restricted
  layer embeds in the Galois group of the layer.
* `TauCeti.ClassFieldTheory.LayerRestriction.degree_layer_mul_relativeDegree`:
  `[U' : V] * [U : U'] = [U : V]`.
* `TauCeti.ClassFieldTheory.NormalLayer.degree_subgroupLayer`: the layer of `H` has degree `#H`.
* `TauCeti.ClassFieldTheory.NormalLayer.relativeDegree_subgroupRestriction`: its relative degree
  is the index of `H`.
* `TauCeti.ClassFieldTheory.NormalLayer.galHom_subgroupRestriction`: the homomorphism of Galois
  groups it induces is the inclusion of `H`.
* `TauCeti.ClassFieldTheory.NormalLayer.subgroupLayer_top`: the layer of the whole Galois group is
  the layer itself.

## Implementation notes

`NormalLayer.subgroupGround` is the correspondence-theorem preimage of `H` — the subgroup
`QuotientGroup.comapMk'OrderIso` attaches to `H` — pushed from `U` into the ambient group `G`, so
that it can be an `OpenSubgroup G` and be compared with the other subgroups of a formation. It is
spelled with `Subgroup.comap` and `Subgroup.map` directly, because only that subgroup, and not the
order isomorphism, is used.

The restricted layer is *built from* the layer being restricted rather than assumed alongside it:
the field `LayerRestriction.ground` is the intermediate subgroup and `LayerRestriction.layer` is
the layer it determines. This is what makes `LayerRestriction.top_layer` a definitional equality,
so that the two coefficient modules are the same submodule of the ambient module and
`LayerRestriction.repIso` can be the identity on elements.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§1–2.
* J. Neukirch, *Class Field Theory*, Chapter III, §1.
* J. Tate, *The higher dimensional cohomology groups of class field theory*, Ann. of Math. **56**
  (1952), 294–297.
-/

@[expose] public noncomputable section

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- The degree of a layer is the relative index of its top subgroup in its ground subgroup. This
is the form in which the degree multiplies along a restriction. -/
theorem NormalLayer.degree_eq_relIndex (L : NormalLayer G) :
    L.degree = L.top.toSubgroup.relIndex L.ground.toSubgroup :=
  L.degree_eq_natCard_gal

/-! ### Restriction data -/

/-- A **restriction datum** for a finite normal layer `V ◁ U`: an open subgroup `U'` with
`V ≤ U' ≤ U`. In field notation it raises the ground field of the layer `K/F` to an intermediate
field `E`, leaving the layer `K/E`. -/
structure LayerRestriction (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] where
  /-- the layer `V ◁ U` that is being restricted -/
  base : NormalLayer G
  /-- the new ground subgroup `U'`, cutting out the intermediate field -/
  ground : OpenSubgroup G
  /-- the new ground subgroup lies in the old one -/
  ground_le_base : ground ≤ base.ground
  /-- the new ground subgroup still contains the top subgroup -/
  top_le_ground : base.top ≤ ground

namespace LayerRestriction

variable (T : LayerRestriction G)

/-- The **restricted layer** `V ◁ U'`. Its top subgroup, hence its coefficient module, is the top
subgroup of the layer being restricted. -/
def layer : NormalLayer G where
  ground := T.ground
  top := T.base.top
  top_le_ground := T.top_le_ground
  normal := ⟨fun _v hv w => Subgroup.mem_subgroupOf.2 (T.base.conj_mem_top
    (T.ground_le_base w.2) (Subgroup.mem_subgroupOf.1 hv))⟩

/-- The ground subgroup of the restricted layer is the intermediate subgroup. -/
@[simp]
theorem ground_layer : T.layer.ground = T.ground := rfl

/-- The restricted layer has the same top subgroup as the layer it comes from. -/
@[simp]
theorem top_layer : T.layer.top = T.base.top := rfl

/-- The ground subgroup of a restricted layer sits inside the ground subgroup of the layer. -/
theorem layer_ground_le : T.layer.ground.toSubgroup ≤ T.base.ground.toSubgroup := by
  rw [ground_layer]
  exact T.ground_le_base

/-- The **relative degree** `[U : U']` of a restriction datum, the degree of the new ground field
over the old one. `⚠` `U'` is the subgroup, so the relative degree is the index of `U'` in `U`. -/
def relativeDegree : ℕ := T.ground.toSubgroup.relIndex T.base.ground.toSubgroup

/-- **The degree of a layer is multiplicative along a restriction:** `[U' : V] * [U : U'] =
[U : V]`. -/
theorem degree_layer_mul_relativeDegree : T.layer.degree * T.relativeDegree = T.base.degree := by
  rw [NormalLayer.degree_eq_relIndex, NormalLayer.degree_eq_relIndex, relativeDegree, top_layer,
    ground_layer]
  exact Subgroup.relIndex_mul_relIndex _ _ _ T.top_le_ground T.ground_le_base

/-- The homomorphism `U'/V → U/V` of Galois groups induced by a restriction datum. It is injective
(`galHom_injective`), and its image is the subgroup of `U/V` that the intermediate subgroup `U'`
cuts out. -/
def galHom : T.layer.Gal →* T.base.Gal :=
  QuotientGroup.lift T.layer.relativeTop
    ((QuotientGroup.mk' T.base.relativeTop).comp (Subgroup.inclusion T.layer_ground_le))
    fun x hx ↦ (QuotientGroup.eq_one_iff _).2 <| Subgroup.mem_subgroupOf.2 <| by
      rw [← top_layer]
      exact Subgroup.mem_subgroupOf.1 hx

/-- The homomorphism of Galois groups is induced by the inclusion of ground subgroups. -/
@[simp]
theorem galHom_mk (w : T.layer.ground) :
    T.galHom (QuotientGroup.mk w) =
      QuotientGroup.mk (Subgroup.inclusion T.layer_ground_le w) :=
  rfl

/-- The relative degree of a restriction datum is positive: the Galois groups involved are
finite. -/
theorem relativeDegree_pos : 0 < T.relativeDegree :=
  Nat.pos_of_mul_pos_left (T.degree_layer_mul_relativeDegree ▸ T.base.degree_pos)

/-- **The Galois group of a restricted layer embeds in the Galois group of the layer.** Both are
quotients of subgroups of `U` by the *same* top subgroup `V`. -/
theorem galHom_injective : Function.Injective T.galHom := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  induction γ using QuotientGroup.induction_on with
  | H w =>
    rw [galHom_mk] at hγ
    have hw : (w : G) ∈ T.base.top := Subgroup.mem_subgroupOf.1
      ((QuotientGroup.eq_one_iff (N := T.base.relativeTop)
        (Subgroup.inclusion T.layer_ground_le w)).1 hγ)
    refine (QuotientGroup.eq_one_iff w).2 (Subgroup.mem_subgroupOf.2 ?_)
    rw [top_layer]
    exact hw

/-- **The coefficient module of a restricted layer is the coefficient module of the layer**, read
as a representation of the smaller Galois group along `galHom`. The two modules are the same
submodule `A^V` of the ambient module — the restriction does not move the top subgroup — so this
isomorphism is the identity on elements. -/
def repIso (F : Formation G) :
    T.layer.rep F ≅ Rep.res T.galHom (T.base.rep F) :=
  Rep.mkIso <| Representation.Equiv.mk (LinearEquiv.refl ℤ _) fun γ ↦ by
    induction γ using QuotientGroup.induction_on with
    | H w => rfl

/-- The identification of coefficient modules moves no element. It is not a `simp` lemma: its
left-hand side is not in simp-normal form, since `simp` unfolds the two coefficient modules to
the level `A^V` they are both built on. -/
theorem repIso_hom_apply (F : Formation G) (x : T.layer.rep F) :
    (T.repIso F).hom.hom x = x :=
  rfl

end LayerRestriction

/-! ### The finite quotient system -/

namespace NormalLayer

variable (L : NormalLayer G) (H : Subgroup L.Gal)

/-- The intermediate subgroup `V ≤ W ≤ U` attached to a subgroup `H` of the Galois group `U ⧸ V`:
the preimage of `H` in `U`, read inside `G`. -/
def subgroupGround : Subgroup G :=
  (H.comap (QuotientGroup.mk' L.relativeTop)).map L.ground.toSubgroup.subtype

/-- Membership in the intermediate subgroup: an element of `U` lies in it exactly when its class
in the Galois group lies in `H`. -/
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

/-- The restriction datum attached to a subgroup `H` of the Galois group: its intermediate ground
subgroup is the preimage of `H`. -/
def subgroupRestriction : LayerRestriction G where
  base := L
  ground := ⟨L.subgroupGround H, Subgroup.isOpen_mono (L.top_le_subgroupGround H) L.top.isOpen⟩
  ground_le_base := L.subgroupGround_le_ground H
  top_le_ground := L.top_le_subgroupGround H

/-- The layer restricted by `subgroupRestriction` is the original layer. -/
@[simp]
theorem base_subgroupRestriction : (L.subgroupRestriction H).base = L := rfl

/-- The intermediate ground subgroup of `subgroupRestriction H` is the preimage of `H`. -/
@[simp]
theorem ground_subgroupRestriction :
    (L.subgroupRestriction H).ground.toSubgroup = L.subgroupGround H := rfl

/-- The **layer of a subgroup** `H ≤ U ⧸ V`: the finite normal layer `V ◁ W` whose ground subgroup
is the preimage `W` of `H`. The family `H ↦ subgroupLayer H` is the finite quotient system that
Tate's theorem quantifies over. -/
def subgroupLayer : NormalLayer G := (L.subgroupRestriction H).layer

/-- The layer of `H` is the restricted layer of the restriction datum of `H`. -/
theorem subgroupLayer_eq : L.subgroupLayer H = (L.subgroupRestriction H).layer := rfl

/-- The ground subgroup of the layer of `H` is the preimage of `H`. -/
@[simp]
theorem ground_subgroupLayer :
    (L.subgroupLayer H).ground.toSubgroup = L.subgroupGround H := by
  rw [subgroupLayer_eq, LayerRestriction.ground_layer, ground_subgroupRestriction]

/-- The layer of `H` has the same top subgroup, hence the same coefficient module, as the layer
it comes from. -/
@[simp]
theorem top_subgroupLayer : (L.subgroupLayer H).top = L.top := by
  rw [subgroupLayer_eq, LayerRestriction.top_layer, base_subgroupRestriction]

/-- The image of the Galois group of the layer of `H` is `H`. -/
theorem range_galHom_subgroupRestriction : (L.subgroupRestriction H).galHom.range = H := by
  ext γ
  constructor
  · rintro ⟨δ, rfl⟩
    induction δ using QuotientGroup.induction_on with
    | H w =>
      obtain ⟨hw, hmem⟩ := (L.mem_subgroupGround H).1 w.2
      exact hmem
  · intro hγ
    induction γ using QuotientGroup.induction_on with
    | H u =>
      exact ⟨QuotientGroup.mk ⟨(u : G), (L.mem_subgroupGround H).2 ⟨u.2, hγ⟩⟩, rfl⟩

/-- **The Galois group of the layer of `H` is `H`.** -/
def subgroupGalEquiv : (L.subgroupLayer H).Gal ≃* H :=
  (MonoidHom.ofInjective (L.subgroupRestriction H).galHom_injective).trans
    (MulEquiv.subgroupCongr (L.range_galHom_subgroupRestriction H))

/-- The identification of the Galois group of the layer of `H` with `H` is the homomorphism of
Galois groups of the restriction datum. -/
@[simp]
theorem subgroupGalEquiv_apply_coe (γ : (L.subgroupLayer H).Gal) :
    ((L.subgroupGalEquiv H γ : H) : L.Gal) = (L.subgroupRestriction H).galHom γ :=
  rfl

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
  rw [LayerRestriction.relativeDegree, ground_subgroupRestriction, base_subgroupRestriction,
    Subgroup.relIndex, ← Subgroup.comap_subtype, subgroupGround,
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
