/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Products.Basic
public import TauCeti.CategoryTheory.Groupoid.ChartAtlas.Basic

/-!
# Constructions on retained-arrow chart atlases and induced chart atlases

This file develops standard constructions on `TauCeti.ChartAtlas` and establishes the bidirectional
bridge between retained-arrow chart atlases and families of fully faithful action-groupoid charts
into an ambient groupoid:

1. **Restriction (`TauCeti.ChartAtlas.restrict`).** Restricting a chart atlas `𝓐` to a family of
   `G i`-invariant subsets `S i : SubMulAction (G i) (U i)` yields a chart atlas `𝓐.restrict S`
   together with a canonical inclusion morphism `𝓐.restrictHom S` whose induced functor on
   presenting groupoids is full and faithful.
2. **Binary products (`TauCeti.ChartAtlas.prod`).** The componentwise product `𝓐.prod 𝓑` of two
   chart atlases comes with projection morphisms `fstHom` and `sndHom`, universal pairing
   `TauCeti.ChartAtlas.Hom.prod`, and a categorical equivalence `(𝓐.prod 𝓑).Obj ≌ 𝓐.Obj × 𝓑.Obj`
   (`TauCeti.ChartAtlas.prodObjEquivalence`).
3. **Induced atlas of action charts (`TauCeti.ChartAtlas.ofCharts`).** Any family of fully faithful
   functors `F i : ActionCategory (G i) (U i) ⥤ C` into a groupoid `C` induces a chart atlas
   `ofCharts F` on `fun i j ↦ ChartOverlap (F i) (F j)` together with a canonical fully faithful
   comparison functor `toGroupoid F : (ofCharts F).Obj ⥤ C`, which is essentially surjective
   precisely when the chart images meet every isomorphism class of `C`.
4. **Round-trip and disjoint-union comparisons (`toOfCharts`, `fromOfCharts`, `sumCharts`).**
   Applying `ofCharts` to `𝓐.chartFunctor` recovers `𝓐` up to strict mutual inverse atlas
   morphisms, reindexing chart families induces full and faithful morphisms via
   `ofChartsReindexHom`, and two chart families `F₁`, `F₂` into `C` embed fully and faithfully into
   the combined disjoint-union atlas `ofCharts (sumCharts F₁ F₂)` compatibly with `toGroupoid`.

## Main declarations

* `TauCeti.ChartAtlas.restrict`, `TauCeti.ChartAtlas.restrictHom`: restriction of a chart atlas to
  invariant subactions and its full and faithful inclusion.
* `TauCeti.ChartAtlas.prod`, `TauCeti.ChartAtlas.Hom.prod`,
  `TauCeti.ChartAtlas.prodObjEquivalence`: binary product of chart atlases, pairing morphism, and
  equivalence of presenting groupoids.
* `TauCeti.ChartAtlas.ChartOverlap`, `TauCeti.ChartAtlas.ofCharts`,
  `TauCeti.ChartAtlas.toGroupoid`: chart atlas induced by a family of fully faithful action charts
  and its comparison functor.
* `TauCeti.ChartAtlas.toOfCharts`, `TauCeti.ChartAtlas.fromOfCharts`: mutual inverse atlas
  morphisms between `𝓐` and `ofCharts 𝓐.chartFunctor`.
* `TauCeti.ChartAtlas.ofChartsReindexHom`, `TauCeti.ChartAtlas.sumCharts`,
  `TauCeti.ChartAtlas.sumInlHom`, `TauCeti.ChartAtlas.sumInrHom`: reindexing morphisms on induced
  chart atlases, and the disjoint-sum chart family and inclusions embedding `ofCharts F₁` and
  `ofCharts F₂` into the combined chart atlas `ofCharts (sumCharts F₁ F₂)` over `C`.
-/

public section

open CategoryTheory MulAction

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

namespace TauCeti.ChartAtlas

section Restrict

variable {ι : Type u₁} {G : ι → Type u₂} [∀ i, Group (G i)]
  {U : ι → Type u₃} [∀ i, MulAction (G i) (U i)]
  {R : ι → ι → Type u₄} [∀ i j, MulAction (G j) (R i j)]
  (𝓐 : ChartAtlas G U R) (S : ∀ i, SubMulAction (G i) (U i))

/-- Overlap arrows of `𝓐` whose source lies in `S i` and whose target lies in `S j`. -/
abbrev RestrictArrow (i j : ι) : Type u₄ :=
  { α : R i j // 𝓐.src α ∈ S i ∧ 𝓐.tgt α ∈ S j }

/-- Because `S j` is `G j`-invariant, `G j` acts on `RestrictArrow 𝓐 S i j`. -/
instance instMulActionRestrictArrow (i j : ι) :
    MulAction (G j) (𝓐.RestrictArrow S i j) where
  smul g α := ⟨g • α.1, by rw [𝓐.src_smul]; exact α.2.1,
    by rw [𝓐.tgt_smul]; exact (S j).smul_mem g α.2.2⟩
  one_smul α := Subtype.ext (one_smul _ α.1)
  mul_smul g₁ g₂ α := Subtype.ext (mul_smul g₁ g₂ α.1)

/-- Coercion from `RestrictArrow` commutes with the `G j`-action. -/
@[simp]
theorem val_smul_restrictArrow {i j : ι} (g : G j) (α : 𝓐.RestrictArrow S i j) :
    (g • α).1 = g • α.1 := (rfl)

/-- The restriction of a chart atlas `𝓐` to a family of `G i`-invariant subsets `S i ⊆ U i`. -/
def restrict : ChartAtlas G (fun i ↦ S i) (𝓐.RestrictArrow S) where
  src α := ⟨𝓐.src α.1, α.2.1⟩
  tgt α := ⟨𝓐.tgt α.1, α.2.2⟩
  unit i x := ⟨𝓐.unit i x.1, by simp [x.2]⟩
  inv α := ⟨𝓐.inv α.1, by simp [α.2.2, α.2.1]⟩
  comp α β h := ⟨𝓐.comp α.1 β.1 (congrArg Subtype.val h), by simp [α.2.1, β.2.2]⟩
  src_unit _ _ := Subtype.ext (𝓐.src_unit _ _)
  tgt_unit _ _ := Subtype.ext (𝓐.tgt_unit _ _)
  src_inv _ := Subtype.ext (𝓐.src_inv _)
  tgt_inv _ := Subtype.ext (𝓐.tgt_inv _)
  src_comp _ _ _ := Subtype.ext (𝓐.src_comp _ _ _)
  tgt_comp _ _ _ := Subtype.ext (𝓐.tgt_comp _ _ _)
  unit_comp _ _ _ := Subtype.ext (𝓐.unit_comp _ _ _)
  comp_unit _ _ _ := Subtype.ext (𝓐.comp_unit _ _ _)
  comp_assoc _ _ _ _ _ := Subtype.ext (𝓐.comp_assoc _ _ _ _ _)
  comp_inv _ := Subtype.ext (𝓐.comp_inv _)
  inv_comp _ := Subtype.ext (𝓐.inv_comp _)
  src_smul _ _ := Subtype.ext (𝓐.src_smul _ _)
  tgt_smul _ _ := Subtype.ext (𝓐.tgt_smul _ _)
  comp_smul _ _ _ _ := Subtype.ext (𝓐.comp_smul _ _ _ _)
  existsUnique_smul_eq α β h :=
    let ⟨g, hg, hu⟩ := 𝓐.existsUnique_smul_eq α.1 β.1 (congrArg Subtype.val h)
    ⟨g, Subtype.ext hg, fun g' hg' ↦ hu g' (congrArg Subtype.val hg')⟩

/-- Source of a restricted overlap arrow in `𝓐.restrict S`. -/
@[simp]
theorem restrict_src {i j : ι} (α : 𝓐.RestrictArrow S i j) :
    (𝓐.restrict S).src α = ⟨𝓐.src α.1, α.2.1⟩ := (rfl)

/-- Target of a restricted overlap arrow in `𝓐.restrict S`. -/
@[simp]
theorem restrict_tgt {i j : ι} (α : 𝓐.RestrictArrow S i j) :
    (𝓐.restrict S).tgt α = ⟨𝓐.tgt α.1, α.2.2⟩ := (rfl)

/-- Unit overlap arrow in `𝓐.restrict S`. -/
@[simp]
theorem restrict_unit (i : ι) (x : S i) :
    (𝓐.restrict S).unit i x =
      ⟨𝓐.unit i x.1, by rw [𝓐.src_unit, 𝓐.tgt_unit]; exact ⟨x.2, x.2⟩⟩ := (rfl)

/-- Inverse overlap arrow in `𝓐.restrict S`. -/
@[simp]
theorem restrict_inv {i j : ι} (α : 𝓐.RestrictArrow S i j) :
    (𝓐.restrict S).inv α =
      ⟨𝓐.inv α.1, by rw [𝓐.src_inv, 𝓐.tgt_inv]; exact ⟨α.2.2, α.2.1⟩⟩ := (rfl)

/-- Composition of overlap arrows in `𝓐.restrict S`. -/
@[simp]
theorem restrict_comp {i j k : ι} (α : 𝓐.RestrictArrow S i j) (β : 𝓐.RestrictArrow S j k)
    (h : (𝓐.restrict S).tgt α = (𝓐.restrict S).src β) :
    (𝓐.restrict S).comp α β h =
      ⟨𝓐.comp α.1 β.1
        (congrArg Subtype.val ((𝓐.restrict_tgt S α).symm.trans (h.trans (𝓐.restrict_src S β)))),
        by rw [𝓐.src_comp, 𝓐.tgt_comp]; exact ⟨α.2.1, β.2.2⟩⟩ := (rfl)

/-- The canonical inclusion morphism `(𝓐.restrict S).Hom 𝓐`, keeping all group labels. -/
-- `expose, implicit_reducible`: unification of dependent chart types in `groupHom`, `obj`, and
-- `map` must see `(𝓐.restrictHom S).index i` as `i`.
@[expose, implicit_reducible]
def restrictHom : (𝓐.restrict S).Hom 𝓐 where
  index := id
  groupHom i := MonoidHom.id (G i)
  obj _ := Subtype.val
  map α := α.1
  src_map _ := by simp
  tgt_map _ := by simp
  map_unit _ _ := by simp
  map_comp _ _ _ := by simp
  map_smul _ _ := by simp

/-- The index map of `restrictHom` is the identity. -/
@[simp]
theorem restrictHom_index : (𝓐.restrictHom S).index = id := (rfl)

/-- The group homomorphism of `restrictHom` on chart `i` is `MonoidHom.id (G i)`. -/
@[simp]
theorem restrictHom_groupHom (i : ι) : (𝓐.restrictHom S).groupHom i = MonoidHom.id (G i) := (rfl)

/-- `restrictHom` sends a point in `S i` to its underlying point in `U i`. -/
@[simp]
theorem restrictHom_obj (i : ι) (x : S i) : (𝓐.restrictHom S).obj i x = x.1 := (rfl)

/-- `restrictHom` sends a restricted overlap arrow to its underlying arrow in `R i j`. -/
@[simp]
theorem restrictHom_map {i j : ι} (α : 𝓐.RestrictArrow S i j) :
    (𝓐.restrictHom S).map α = α.1 := (rfl)

/-- The inclusion functor `(𝓐.restrict S).Obj ⥤ 𝓐.Obj` is faithful. -/
instance instFaithfulRestrictHom : (𝓐.restrictHom S).toFunctor.Faithful :=
  (Hom.faithful_toFunctor_iff _).mpr fun _ _ _ _ hm ↦ Subtype.ext hm

/-- The inclusion functor `(𝓐.restrict S).Obj ⥤ 𝓐.Obj` is full. -/
instance instFullRestrictHom : (𝓐.restrictHom S).toFunctor.Full :=
  (Hom.full_toFunctor_iff _).mpr fun x y β hs ht ↦
    ⟨⟨β, hs.symm ▸ x.2, ht.symm ▸ y.2⟩, Subtype.ext hs, Subtype.ext ht, rfl⟩

end Restrict

section Prod

/-- Pair carrier `α × β` equipped with the componentwise action of a product monoid `M₁ × M₂`, used
for both chart domains and overlap-arrow spaces of `ChartAtlas.prod` without clashing with Mathlib's
diagonal `MulAction M (α × β)` instance. -/
@[ext]
structure ProdCarrier (α : Type*) (β : Type*) where
  /-- First coordinate. -/
  fst : α
  /-- Second coordinate. -/
  snd : β

namespace ProdCarrier

/-- Componentwise scalar action of `M₁ × M₂` on `ProdCarrier α β`. -/
instance instSMul {M₁ M₂ α β : Type*} [SMul M₁ α] [SMul M₂ β] :
    SMul (M₁ × M₂) (ProdCarrier α β) where
  smul g x := ⟨g.1 • x.fst, g.2 • x.snd⟩

/-- First coordinate of componentwise scalar multiplication on `ProdCarrier`. -/
@[simp]
theorem fst_smul {M₁ M₂ α β : Type*} [SMul M₁ α] [SMul M₂ β]
    (g : M₁ × M₂) (x : ProdCarrier α β) : (g • x).fst = g.1 • x.fst := (rfl)

/-- Second coordinate of componentwise scalar multiplication on `ProdCarrier`. -/
@[simp]
theorem snd_smul {M₁ M₂ α β : Type*} [SMul M₁ α] [SMul M₂ β]
    (g : M₁ × M₂) (x : ProdCarrier α β) : (g • x).snd = g.2 • x.snd := (rfl)

/-- Componentwise `MulAction` of `M₁ × M₂` on `ProdCarrier α β` for any two acting monoids. -/
instance instMulAction {M₁ M₂ α β : Type*} [Monoid M₁] [Monoid M₂]
    [MulAction M₁ α] [MulAction M₂ β] : MulAction (M₁ × M₂) (ProdCarrier α β) where
  one_smul x := ProdCarrier.ext (one_smul _ x.fst) (one_smul _ x.snd)
  mul_smul g h x := ProdCarrier.ext (mul_smul g.1 h.1 x.fst) (mul_smul g.2 h.2 x.snd)

end ProdCarrier

variable {ι : Type u₁} {G₁ : ι → Type u₂} [∀ i, Group (G₁ i)]
  {U₁ : ι → Type u₃} [∀ i, MulAction (G₁ i) (U₁ i)]
  {R₁ : ι → ι → Type u₄} [∀ i j, MulAction (G₁ j) (R₁ i j)]
  {κ : Type v₁} {G₂ : κ → Type v₂} [∀ k, Group (G₂ k)]
  {U₂ : κ → Type v₃} [∀ k, MulAction (G₂ k) (U₂ k)]
  {R₂ : κ → κ → Type v₄} [∀ k l, MulAction (G₂ l) (R₂ k l)]
  (𝓐 : ChartAtlas G₁ U₁ R₁) (𝓑 : ChartAtlas G₂ U₂ R₂)

/-- The binary product `𝓐.prod 𝓑` of two retained-arrow chart atlases. -/
def prod : ChartAtlas (fun p : ι × κ ↦ G₁ p.1 × G₂ p.2)
    (fun p ↦ ProdCarrier (U₁ p.1) (U₂ p.2))
    (fun p q ↦ ProdCarrier (R₁ p.1 q.1) (R₂ p.2 q.2)) where
  src α := ⟨𝓐.src α.fst, 𝓑.src α.snd⟩
  tgt α := ⟨𝓐.tgt α.fst, 𝓑.tgt α.snd⟩
  unit p x := ⟨𝓐.unit p.1 x.fst, 𝓑.unit p.2 x.snd⟩
  inv α := ⟨𝓐.inv α.fst, 𝓑.inv α.snd⟩
  comp α β h :=
    ⟨𝓐.comp α.fst β.fst (congrArg ProdCarrier.fst h),
      𝓑.comp α.snd β.snd (congrArg ProdCarrier.snd h)⟩
  src_unit p x := ProdCarrier.ext (𝓐.src_unit p.1 x.fst) (𝓑.src_unit p.2 x.snd)
  tgt_unit p x := ProdCarrier.ext (𝓐.tgt_unit p.1 x.fst) (𝓑.tgt_unit p.2 x.snd)
  src_inv α := ProdCarrier.ext (𝓐.src_inv α.fst) (𝓑.src_inv α.snd)
  tgt_inv α := ProdCarrier.ext (𝓐.tgt_inv α.fst) (𝓑.tgt_inv α.snd)
  src_comp _ _ _ := ProdCarrier.ext (𝓐.src_comp _ _ _) (𝓑.src_comp _ _ _)
  tgt_comp _ _ _ := ProdCarrier.ext (𝓐.tgt_comp _ _ _) (𝓑.tgt_comp _ _ _)
  unit_comp _ _ _ := ProdCarrier.ext (𝓐.unit_comp _ _ _) (𝓑.unit_comp _ _ _)
  comp_unit _ _ _ := ProdCarrier.ext (𝓐.comp_unit _ _ _) (𝓑.comp_unit _ _ _)
  comp_assoc _ _ _ _ _ := ProdCarrier.ext (𝓐.comp_assoc _ _ _ _ _) (𝓑.comp_assoc _ _ _ _ _)
  comp_inv α := ProdCarrier.ext (𝓐.comp_inv α.fst) (𝓑.comp_inv α.snd)
  inv_comp α := ProdCarrier.ext (𝓐.inv_comp α.fst) (𝓑.inv_comp α.snd)
  src_smul g α := ProdCarrier.ext (𝓐.src_smul g.1 α.fst) (𝓑.src_smul g.2 α.snd)
  tgt_smul g α := ProdCarrier.ext (𝓐.tgt_smul g.1 α.fst) (𝓑.tgt_smul g.2 α.snd)
  comp_smul α g β _ :=
    ProdCarrier.ext (𝓐.comp_smul α.fst g.1 β.fst _) (𝓑.comp_smul α.snd g.2 β.snd _)
  existsUnique_smul_eq α β h :=
    let ⟨g₁, hg₁, hu₁⟩ := 𝓐.existsUnique_smul_eq α.fst β.fst (congrArg ProdCarrier.fst h)
    let ⟨g₂, hg₂, hu₂⟩ := 𝓑.existsUnique_smul_eq α.snd β.snd (congrArg ProdCarrier.snd h)
    ⟨(g₁, g₂), ProdCarrier.ext hg₁ hg₂, fun g hg ↦
      Prod.ext (hu₁ g.1 (congrArg ProdCarrier.fst hg)) (hu₂ g.2 (congrArg ProdCarrier.snd hg))⟩

/-- Source of an overlap arrow in `𝓐.prod 𝓑`. -/
@[simp]
theorem prod_src {p q : ι × κ} (α : ProdCarrier (R₁ p.1 q.1) (R₂ p.2 q.2)) :
    (𝓐.prod 𝓑).src α = ⟨𝓐.src α.fst, 𝓑.src α.snd⟩ := (rfl)

/-- Target of an overlap arrow in `𝓐.prod 𝓑`. -/
@[simp]
theorem prod_tgt {p q : ι × κ} (α : ProdCarrier (R₁ p.1 q.1) (R₂ p.2 q.2)) :
    (𝓐.prod 𝓑).tgt α = ⟨𝓐.tgt α.fst, 𝓑.tgt α.snd⟩ := (rfl)

/-- Unit overlap arrow in `𝓐.prod 𝓑`. -/
@[simp]
theorem prod_unit (p : ι × κ) (x : ProdCarrier (U₁ p.1) (U₂ p.2)) :
    (𝓐.prod 𝓑).unit p x = ⟨𝓐.unit p.1 x.fst, 𝓑.unit p.2 x.snd⟩ := (rfl)

/-- Inverse overlap arrow in `𝓐.prod 𝓑`. -/
@[simp]
theorem prod_inv {p q : ι × κ} (α : ProdCarrier (R₁ p.1 q.1) (R₂ p.2 q.2)) :
    (𝓐.prod 𝓑).inv α = ⟨𝓐.inv α.fst, 𝓑.inv α.snd⟩ := (rfl)

/-- Composition of overlap arrows in `𝓐.prod 𝓑`. -/
@[simp]
theorem prod_comp {p q r : ι × κ}
    (α : ProdCarrier (R₁ p.1 q.1) (R₂ p.2 q.2))
    (β : ProdCarrier (R₁ q.1 r.1) (R₂ q.2 r.2))
    (h : (𝓐.prod 𝓑).tgt α = (𝓐.prod 𝓑).src β) :
    (𝓐.prod 𝓑).comp α β h =
      ⟨𝓐.comp α.fst β.fst
          (congrArg ProdCarrier.fst ((𝓐.prod_tgt 𝓑 α).symm.trans (h.trans (𝓐.prod_src 𝓑 β)))),
        𝓑.comp α.snd β.snd
          (congrArg ProdCarrier.snd ((𝓐.prod_tgt 𝓑 α).symm.trans (h.trans (𝓐.prod_src 𝓑 β))))⟩ :=
  (rfl)

/-- First projection morphism `(𝓐.prod 𝓑).Hom 𝓐`. -/
-- `expose, implicit_reducible`: unification of dependent chart types in `groupHom`, `obj`, and
-- `map` must see `(𝓐.fstHom 𝓑).index p` as `p.1`.
@[expose, implicit_reducible]
def fstHom : (𝓐.prod 𝓑).Hom 𝓐 where
  index := Prod.fst
  groupHom _ := MonoidHom.fst _ _
  obj _ := ProdCarrier.fst
  map := ProdCarrier.fst
  src_map _ := by simp
  tgt_map _ := by simp
  map_unit _ _ := by simp
  map_comp _ _ _ := by simp
  map_smul _ _ := by simp

/-- Index map of `fstHom`. -/
@[simp]
theorem fstHom_index : (𝓐.fstHom 𝓑).index = Prod.fst := (rfl)

/-- Group homomorphism of `fstHom` at chart `p`. -/
@[simp]
theorem fstHom_groupHom (p : ι × κ) :
    (𝓐.fstHom 𝓑).groupHom p = MonoidHom.fst (G₁ p.1) (G₂ p.2) := (rfl)

/-- Point map of `fstHom` at chart `p`. -/
@[simp]
theorem fstHom_obj (p : ι × κ) (x : ProdCarrier (U₁ p.1) (U₂ p.2)) :
    (𝓐.fstHom 𝓑).obj p x = x.fst := (rfl)

/-- Overlap-arrow map of `fstHom`. -/
@[simp]
theorem fstHom_map {p q : ι × κ} (α : ProdCarrier (R₁ p.1 q.1) (R₂ p.2 q.2)) :
    (𝓐.fstHom 𝓑).map α = α.fst := (rfl)

/-- Second projection morphism `(𝓐.prod 𝓑).Hom 𝓑`. -/
-- `expose, implicit_reducible`: unification of dependent chart types in `groupHom`, `obj`, and
-- `map` must see `(𝓐.sndHom 𝓑).index p` as `p.2`.
@[expose, implicit_reducible]
def sndHom : (𝓐.prod 𝓑).Hom 𝓑 where
  index := Prod.snd
  groupHom _ := MonoidHom.snd _ _
  obj _ := ProdCarrier.snd
  map := ProdCarrier.snd
  src_map _ := by simp
  tgt_map _ := by simp
  map_unit _ _ := by simp
  map_comp _ _ _ := by simp
  map_smul _ _ := by simp

/-- Index map of `sndHom`. -/
@[simp]
theorem sndHom_index : (𝓐.sndHom 𝓑).index = Prod.snd := (rfl)

/-- Group homomorphism of `sndHom` at chart `p`. -/
@[simp]
theorem sndHom_groupHom (p : ι × κ) :
    (𝓐.sndHom 𝓑).groupHom p = MonoidHom.snd (G₁ p.1) (G₂ p.2) := (rfl)

/-- Point map of `sndHom` at chart `p`. -/
@[simp]
theorem sndHom_obj (p : ι × κ) (x : ProdCarrier (U₁ p.1) (U₂ p.2)) :
    (𝓐.sndHom 𝓑).obj p x = x.snd := (rfl)

/-- Overlap-arrow map of `sndHom`. -/
@[simp]
theorem sndHom_map {p q : ι × κ} (α : ProdCarrier (R₁ p.1 q.1) (R₂ p.2 q.2)) :
    (𝓐.sndHom 𝓑).map α = α.snd := (rfl)

section ProdPairing

variable {𝓐 𝓑}
  {μ : Type*} {G₃ : μ → Type*} [∀ m, Group (G₃ m)]
  {U₃ : μ → Type*} [∀ m, MulAction (G₃ m) (U₃ m)]
  {R₃ : μ → μ → Type*} [∀ m n, MulAction (G₃ n) (R₃ m n)]
  {𝓒 : ChartAtlas G₃ U₃ R₃}

/-- Product pairing morphism `𝓒.Hom (𝓐.prod 𝓑)` assembled from morphisms into each factor. -/
-- `expose, implicit_reducible`: unification of dependent chart types in `groupHom`, `obj`, and
-- `map` must see `(Φ₁.prod Φ₂).index m` as `(Φ₁.index m, Φ₂.index m)`.
@[expose, implicit_reducible]
def Hom.prod (Φ₁ : 𝓒.Hom 𝓐) (Φ₂ : 𝓒.Hom 𝓑) : 𝓒.Hom (𝓐.prod 𝓑) where
  index m := (Φ₁.index m, Φ₂.index m)
  groupHom m := (Φ₁.groupHom m).prod (Φ₂.groupHom m)
  obj m x := ⟨Φ₁.obj m x, Φ₂.obj m x⟩
  map α := ⟨Φ₁.map α, Φ₂.map α⟩
  src_map _ := by ext <;> simp
  tgt_map _ := by ext <;> simp
  map_unit _ _ := by ext <;> simp
  map_comp _ _ _ := by ext <;> simp [Φ₁.map_comp, Φ₂.map_comp]
  map_smul _ _ := by ext <;> simp

/-- Index map of `Hom.prod`. -/
@[simp]
theorem Hom.prod_index (Φ₁ : 𝓒.Hom 𝓐) (Φ₂ : 𝓒.Hom 𝓑) (m : μ) :
    (Φ₁.prod Φ₂).index m = (Φ₁.index m, Φ₂.index m) := (rfl)

/-- Group homomorphism of `Hom.prod` at chart `m`. -/
@[simp]
theorem Hom.prod_groupHom (Φ₁ : 𝓒.Hom 𝓐) (Φ₂ : 𝓒.Hom 𝓑) (m : μ) :
    (Φ₁.prod Φ₂).groupHom m = (Φ₁.groupHom m).prod (Φ₂.groupHom m) := (rfl)

/-- Point map of `Hom.prod` at chart `m`. -/
@[simp]
theorem Hom.prod_obj (Φ₁ : 𝓒.Hom 𝓐) (Φ₂ : 𝓒.Hom 𝓑) (m : μ) (x : U₃ m) :
    (Φ₁.prod Φ₂).obj m x = ⟨Φ₁.obj m x, Φ₂.obj m x⟩ := (rfl)

/-- Overlap-arrow map of `Hom.prod`. -/
@[simp]
theorem Hom.prod_map (Φ₁ : 𝓒.Hom 𝓐) (Φ₂ : 𝓒.Hom 𝓑) {m n : μ} (α : R₃ m n) :
    (Φ₁.prod Φ₂).map α = ⟨Φ₁.map α, Φ₂.map α⟩ := (rfl)

/-- Projecting `Φ₁.prod Φ₂` onto the first factor recovers `Φ₁`. -/
@[simp]
theorem fstHom_comp_prod (Φ₁ : 𝓒.Hom 𝓐) (Φ₂ : 𝓒.Hom 𝓑) :
    (𝓐.fstHom 𝓑).comp (Φ₁.prod Φ₂) = Φ₁ :=
  Hom.ext rfl (fun _ ↦ HEq.rfl) (fun _ ↦ HEq.rfl)

/-- Projecting `Φ₁.prod Φ₂` onto the second factor recovers `Φ₂`. -/
@[simp]
theorem sndHom_comp_prod (Φ₁ : 𝓒.Hom 𝓐) (Φ₂ : 𝓒.Hom 𝓑) :
    (𝓐.sndHom 𝓑).comp (Φ₁.prod Φ₂) = Φ₂ :=
  Hom.ext rfl (fun _ ↦ HEq.rfl) (fun _ ↦ HEq.rfl)

/-- Pairing the two projections of `𝓐.prod 𝓑` gives the identity morphism. -/
@[simp]
theorem fstHom_prod_sndHom :
    (𝓐.fstHom 𝓑).prod (𝓐.sndHom 𝓑) = Hom.id (𝓐.prod 𝓑) :=
  Hom.ext rfl (fun _ ↦ heq_of_eq (MonoidHom.ext fun _ ↦ rfl)) (fun _ ↦ HEq.rfl)

/-- Universal property of `ChartAtlas.prod`: a morphism into `𝓐.prod 𝓑` equals `Φ₁.prod Φ₂` if and
only if its projections equal `Φ₁` and `Φ₂`. -/
theorem Hom.eq_prod_iff {Θ : 𝓒.Hom (𝓐.prod 𝓑)} {Φ₁ : 𝓒.Hom 𝓐} {Φ₂ : 𝓒.Hom 𝓑} :
    Θ = Φ₁.prod Φ₂ ↔ (𝓐.fstHom 𝓑).comp Θ = Φ₁ ∧ (𝓐.sndHom 𝓑).comp Θ = Φ₂ :=
  ⟨by rintro rfl; exact ⟨fstHom_comp_prod Φ₁ Φ₂, sndHom_comp_prod Φ₁ Φ₂⟩,
    by rintro ⟨rfl, rfl⟩; exact
      Hom.ext rfl (fun _ ↦ heq_of_eq (MonoidHom.ext fun _ ↦ rfl)) (fun _ ↦ HEq.rfl)⟩

end ProdPairing

/-- Categorical equivalence `(𝓐.prod 𝓑).Obj ≌ 𝓐.Obj × 𝓑.Obj` identifying the presenting groupoid
of a product atlas with the product of the presenting groupoids. -/
-- `expose, implicit_reducible`: dependent chart indices in `inverse_map_arrow`, `unitIso`, and
-- `counitIso` require `functor` and `inverse` object maps to reduce.
@[expose, implicit_reducible]
def prodObjEquivalence : (𝓐.prod 𝓑).Obj ≌ 𝓐.Obj × 𝓑.Obj where
  functor := (𝓐.fstHom 𝓑).toFunctor.prod' (𝓐.sndHom 𝓑).toFunctor
  inverse :=
    { obj p := ⟨(p.1.chart, p.2.chart), ⟨p.1.point, p.2.point⟩⟩
      map f := ⟨⟨f.1.arrow, f.2.arrow⟩, by simp, by simp⟩
      map_id _ := by ext <;> simp
      map_comp _ _ := by ext <;> simp }
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := by ext <;> simp

/-- Forward functor of `prodObjEquivalence`. -/
@[simp]
theorem prodObjEquivalence_functor :
    (𝓐.prodObjEquivalence 𝓑).functor = (𝓐.fstHom 𝓑).toFunctor.prod' (𝓐.sndHom 𝓑).toFunctor :=
  (rfl)

/-- Object action of the inverse functor of `prodObjEquivalence`. -/
@[simp]
theorem prodObjEquivalence_inverse_obj (p : 𝓐.Obj × 𝓑.Obj) :
    (𝓐.prodObjEquivalence 𝓑).inverse.obj p = ⟨(p.1.chart, p.2.chart), ⟨p.1.point, p.2.point⟩⟩ :=
  (rfl)

/-- Arrow action of the inverse functor of `prodObjEquivalence`. -/
@[simp]
theorem prodObjEquivalence_inverse_map_arrow {p q : 𝓐.Obj × 𝓑.Obj} (f : p ⟶ q) :
    ((𝓐.prodObjEquivalence 𝓑).inverse.map f).arrow = ⟨f.1.arrow, f.2.arrow⟩ := (rfl)

/-- Unit isomorphism of `prodObjEquivalence`. -/
@[simp]
theorem prodObjEquivalence_unitIso :
    (𝓐.prodObjEquivalence 𝓑).unitIso = Iso.refl (𝟭 (𝓐.prod 𝓑).Obj) := (rfl)

/-- Counit isomorphism of `prodObjEquivalence`. -/
@[simp]
theorem prodObjEquivalence_counitIso :
    (𝓐.prodObjEquivalence 𝓑).counitIso = Iso.refl (𝟭 (𝓐.Obj × 𝓑.Obj)) := (rfl)

end Prod

section OfCharts

variable {C : Type*} [Category* C]

section MonoidCharts

variable {M₁ : Type u₁} {M₂ : Type u₂} [Monoid M₁] [Monoid M₂]
  {U₁ : Type u₃} {U₂ : Type u₄} [MulAction M₁ U₁] [MulAction M₂ U₂]

/-- An overlap arrow between two action-category charts `F₁ : ActionCategory M₁ U₁ ⥤ C` and
`F₂ : ActionCategory M₂ U₂ ⥤ C`: a source point `src : U₁`, a target point `tgt : U₂`, and a
morphism in `C` between their chart images. -/
@[ext]
structure ChartOverlap (F₁ : ActionCategory M₁ U₁ ⥤ C) (F₂ : ActionCategory M₂ U₂ ⥤ C) where
  /-- Source point in the first chart. -/
  src : U₁
  /-- Target point in the second chart. -/
  tgt : U₂
  /-- Morphism in `C` from the image of `src` to the image of `tgt`. -/
  hom : F₁.obj (ActionCategory.objEquiv M₁ U₁ src) ⟶
    F₂.obj (ActionCategory.objEquiv M₂ U₂ tgt)

/-- `M₂` acts on `ChartOverlap F₁ F₂` by translating `tgt` and postcomposing `hom` with the
image under `F₂` of the action-category arrow labelled by `m`. -/
instance instSMulChartOverlap (F₁ : ActionCategory M₁ U₁ ⥤ C) (F₂ : ActionCategory M₂ U₂ ⥤ C) :
    SMul M₂ (ChartOverlap F₁ F₂) where
  smul m α := ⟨α.src, m • α.tgt,
    α.hom ≫ F₂.map (Functor.Elements.homMk m rfl :
      ActionCategory.objEquiv M₂ U₂ α.tgt ⟶
        ActionCategory.objEquiv M₂ U₂ (m • α.tgt))⟩

/-- `smul` on `ChartOverlap` preserves `src`. -/
@[simp]
theorem chartOverlap_smul_src {F₁ : ActionCategory M₁ U₁ ⥤ C} {F₂ : ActionCategory M₂ U₂ ⥤ C}
    (m : M₂) (α : ChartOverlap F₁ F₂) : (m • α).src = α.src := (rfl)

/-- `smul` on `ChartOverlap` translates `tgt` by `m`. -/
@[simp]
theorem chartOverlap_smul_tgt {F₁ : ActionCategory M₁ U₁ ⥤ C} {F₂ : ActionCategory M₂ U₂ ⥤ C}
    (m : M₂) (α : ChartOverlap F₁ F₂) : (m • α).tgt = m • α.tgt := (rfl)

/-- `smul` on `ChartOverlap` postcomposes `hom` with the image under `F₂` of the action-category
arrow labelled by `m`. -/
@[simp]
theorem chartOverlap_smul_hom {F₁ : ActionCategory M₁ U₁ ⥤ C} {F₂ : ActionCategory M₂ U₂ ⥤ C}
    (m : M₂) (α : ChartOverlap F₁ F₂) :
    (m • α).hom = α.hom ≫ F₂.map (Functor.Elements.homMk m rfl :
      ActionCategory.objEquiv M₂ U₂ α.tgt ⟶
        ActionCategory.objEquiv M₂ U₂ (m • α.tgt)) := (rfl)

/-- `MulAction` of `M₂` on `ChartOverlap F₁ F₂`. -/
instance instMulActionChartOverlap (F₁ : ActionCategory M₁ U₁ ⥤ C)
    (F₂ : ActionCategory M₂ U₂ ⥤ C) : MulAction M₂ (ChartOverlap F₁ F₂) where
  one_smul α := by
    have h1 : (1 : M₂) • α.tgt = α.tgt := one_smul M₂ α.tgt
    have heq : (Functor.Elements.homMk (1 : M₂) rfl :
        ActionCategory.objEquiv M₂ U₂ α.tgt ⟶
          ActionCategory.objEquiv M₂ U₂ ((1 : M₂) • α.tgt)) =
        eqToHom (congrArg (ActionCategory.objEquiv M₂ U₂) h1.symm) :=
      Functor.Elements.hom_ext (ActionCategory.eqToHom_hom _).symm
    have hhom : ((1 : M₂) • α).hom =
        α.hom ≫ eqToHom
          (congrArg (fun u ↦ F₂.obj (ActionCategory.objEquiv M₂ U₂ u)) h1.symm) :=
      (congrArg (α.hom ≫ F₂.map ·) heq).trans
        (congrArg (α.hom ≫ ·) (eqToHom_map F₂ _))
    exact ChartOverlap.ext rfl h1
      ((heq_of_eq hhom).trans (CategoryTheory.comp_eqToHom_heq α.hom _))
  mul_smul m₁ m₂ α := by
    have hm : (m₁ * m₂) • α.tgt = m₁ • m₂ • α.tgt := mul_smul m₁ m₂ α.tgt
    have hcomp :
        (Functor.Elements.homMk m₂ rfl :
            ActionCategory.objEquiv M₂ U₂ α.tgt ⟶
              ActionCategory.objEquiv M₂ U₂ (m₂ • α.tgt)) ≫
          Functor.Elements.homMk m₁ rfl =
        Functor.Elements.homMk (m₁ * m₂) rfl ≫
          eqToHom (congrArg (ActionCategory.objEquiv M₂ U₂) hm) :=
      Functor.Elements.hom_ext <|
        (SingleObj.comp_as_mul M₂ m₂ m₁).trans
          ((SingleObj.comp_as_mul M₂ (m₁ * m₂) _).trans
            ((congrArg (· * (m₁ * m₂)) (ActionCategory.eqToHom_hom _)).trans (one_mul _))).symm
    have hhom : (m₁ • m₂ • α).hom =
        ((m₁ * m₂) • α).hom ≫ eqToHom
          (congrArg (fun u ↦ F₂.obj (ActionCategory.objEquiv M₂ U₂ u)) hm) :=
      (Category.assoc α.hom _ _).trans <|
        (congrArg (α.hom ≫ ·) ((F₂.map_comp _ _).symm.trans
          ((congrArg F₂.map hcomp).trans
            ((F₂.map_comp _ _).trans (congrArg (_ ≫ ·) (eqToHom_map F₂ _)))))).trans
        (Category.assoc α.hom _ _).symm
    exact ChartOverlap.ext rfl hm
      ((CategoryTheory.comp_eqToHom_heq ((m₁ * m₂) • α).hom _).symm.trans (heq_of_eq hhom.symm))

end MonoidCharts

section GroupoidCharts

variable [IsGroupoid C]
  {ι : Type u₁} {G : ι → Type u₂} [∀ i, Group (G i)]
  {U : ι → Type u₃} [∀ i, MulAction (G i) (U i)]

/-- **Induced retained-arrow chart atlas.** Any family of fully faithful action-groupoid charts
`F i : ActionCategory (G i) (U i) ⥤ C` into a groupoid `C` induces a `ChartAtlas` on
`fun i j ↦ ChartOverlap (F i) (F j)`, retaining all ineffective isotropy labels. -/
noncomputable def ofCharts (F : ∀ i, ActionCategory (G i) (U i) ⥤ C)
    [∀ i, (F i).Full] [∀ i, (F i).Faithful] :
    ChartAtlas G U (fun i j ↦ ChartOverlap (F i) (F j)) where
  src α := α.src
  tgt α := α.tgt
  unit _ x := ⟨x, x, 𝟙 _⟩
  inv α := ⟨α.tgt, α.src, CategoryTheory.inv α.hom⟩
  comp {_ j _} α β h := ⟨α.src, β.tgt,
    α.hom ≫ eqToHom (congrArg (fun u ↦ (F j).obj (ActionCategory.objEquiv (G j) (U j) u)) h) ≫
      β.hom⟩
  src_unit _ _ := rfl
  tgt_unit _ _ := rfl
  src_inv _ := rfl
  tgt_inv _ := rfl
  src_comp _ _ _ := rfl
  tgt_comp _ _ _ := rfl
  unit_comp _ α h := by
    obtain ⟨_, _, _⟩ := α
    dsimp only at h
    subst h
    exact ChartOverlap.ext rfl rfl (by simp)
  comp_unit α _ h := by
    obtain ⟨_, _, _⟩ := α
    dsimp only at h
    subst h
    exact ChartOverlap.ext rfl rfl (by simp)
  comp_assoc α β γ h₁ h₂ := by
    obtain ⟨_, _, _⟩ := α
    obtain ⟨_, _, _⟩ := β
    obtain ⟨_, _, _⟩ := γ
    dsimp only at h₁ h₂
    subst h₁ h₂
    exact ChartOverlap.ext rfl rfl (by simp)
  comp_inv _ := ChartOverlap.ext rfl rfl (by simp)
  inv_comp _ := ChartOverlap.ext rfl rfl (by simp)
  src_smul _ _ := rfl
  tgt_smul _ _ := rfl
  comp_smul α g β h := by
    obtain ⟨_, _, _⟩ := α
    obtain ⟨_, _, _⟩ := β
    dsimp only at h
    subst h
    exact ChartOverlap.ext rfl rfl (by simp)
  existsUnique_smul_eq {i j} α β h := by
    obtain ⟨x₁, y₁, f₁⟩ := α
    obtain ⟨x₂, y₂, f₂⟩ := β
    dsimp only at h
    subst h
    obtain ⟨e, he⟩ := (F j).map_surjective (CategoryTheory.inv f₁ ≫ f₂)
    let g₀ : G j := e.hom
    have hey : g₀ • y₁ = y₂ := ActionCategory.hom_smul e
    refine ⟨g₀, ?_, fun g hg ↦ ?_⟩
    · have he' : (Functor.Elements.homMk g₀ rfl :
          ActionCategory.objEquiv (G j) (U j) y₁ ⟶
            ActionCategory.objEquiv (G j) (U j) (g₀ • y₁)) =
          e ≫ eqToHom (congrArg (ActionCategory.objEquiv (G j) (U j)) hey.symm) :=
        Functor.Elements.hom_ext (by simp [g₀])
      have hhom : (g₀ • (⟨x₁, y₁, f₁⟩ : ChartOverlap (F i) (F j))).hom =
          f₂ ≫ eqToHom
            (congrArg (fun u ↦ (F j).obj (ActionCategory.objEquiv (G j) (U j) u)) hey.symm) := by
        rw [chartOverlap_smul_hom, he', (F j).map_comp, eqToHom_map, he, Category.assoc,
          IsIso.hom_inv_id_assoc]
      exact ChartOverlap.ext rfl hey
        ((heq_of_eq hhom).trans (CategoryTheory.comp_eqToHom_heq f₂ _))
    · have hg_tgt : g • y₁ = y₂ := congrArg ChartOverlap.tgt hg
      subst hg_tgt
      have hg_hom : f₁ ≫ (F j).map (Functor.Elements.homMk g rfl :
          ActionCategory.objEquiv (G j) (U j) y₁ ⟶
            ActionCategory.objEquiv (G j) (U j) (g • y₁)) = f₂ :=
        eq_of_heq (ChartOverlap.ext_iff.mp hg).2.2
      have hmap : (F j).map (Functor.Elements.homMk g rfl :
          ActionCategory.objEquiv (G j) (U j) y₁ ⟶
            ActionCategory.objEquiv (G j) (U j) (g • y₁)) = (F j).map e := by
        rw [he, ← hg_hom, IsIso.inv_hom_id_assoc]
      exact congrArg Functor.Elements.Hom.hom ((F j).map_injective hmap)

/-- Source of an overlap arrow in `ofCharts F`. -/
@[simp]
theorem ofCharts_src (F : ∀ i, ActionCategory (G i) (U i) ⥤ C)
    [∀ i, (F i).Full] [∀ i, (F i).Faithful] {i j : ι} (α : ChartOverlap (F i) (F j)) :
    (ofCharts F).src α = α.src := (rfl)

/-- Target of an overlap arrow in `ofCharts F`. -/
@[simp]
theorem ofCharts_tgt (F : ∀ i, ActionCategory (G i) (U i) ⥤ C)
    [∀ i, (F i).Full] [∀ i, (F i).Faithful] {i j : ι} (α : ChartOverlap (F i) (F j)) :
    (ofCharts F).tgt α = α.tgt := (rfl)

/-- Unit overlap arrow in `ofCharts F`. -/
@[simp]
theorem ofCharts_unit (F : ∀ i, ActionCategory (G i) (U i) ⥤ C)
    [∀ i, (F i).Full] [∀ i, (F i).Faithful] (i : ι) (x : U i) :
    (ofCharts F).unit i x = ⟨x, x, 𝟙 _⟩ := (rfl)

/-- Inverse overlap arrow in `ofCharts F`. -/
@[simp]
theorem ofCharts_inv (F : ∀ i, ActionCategory (G i) (U i) ⥤ C)
    [∀ i, (F i).Full] [∀ i, (F i).Faithful] {i j : ι} (α : ChartOverlap (F i) (F j)) :
    (ofCharts F).inv α = ⟨α.tgt, α.src, CategoryTheory.inv α.hom⟩ := (rfl)

/-- Composition of overlap arrows in `ofCharts F`. -/
@[simp]
theorem ofCharts_comp (F : ∀ i, ActionCategory (G i) (U i) ⥤ C)
    [∀ i, (F i).Full] [∀ i, (F i).Faithful] {i j k : ι}
    (α : ChartOverlap (F i) (F j)) (β : ChartOverlap (F j) (F k))
    (h : (ofCharts F).tgt α = (ofCharts F).src β) :
    (ofCharts F).comp α β h =
      ⟨α.src, β.tgt,
        α.hom ≫ eqToHom (congrArg (fun u ↦ (F j).obj (ActionCategory.objEquiv (G j) (U j) u))
          ((ofCharts_tgt F α).symm.trans (h.trans (ofCharts_src F β)))) ≫ β.hom⟩ := (rfl)

/-- The canonical comparison functor `(ofCharts F).Obj ⥤ C` from the presenting groupoid of the
induced chart atlas back to `C`. -/
-- `expose, implicit_reducible`: morphism types `(toGroupoid F).map f` must reduce their endpoints
-- `(toGroupoid F).obj x` to the chart images `(F x.chart).obj (...)` in `C`.
@[expose, implicit_reducible]
noncomputable def toGroupoid (F : ∀ i, ActionCategory (G i) (U i) ⥤ C)
    [∀ i, (F i).Full] [∀ i, (F i).Faithful] : (ofCharts F).Obj ⥤ C where
  obj x := (F x.chart).obj (ActionCategory.objEquiv (G x.chart) (U x.chart) x.point)
  map {x y} f :=
    eqToHom (congrArg (fun u ↦ (F x.chart).obj (ActionCategory.objEquiv (G x.chart) (U x.chart) u))
      ((ofCharts_src F f.arrow).symm.trans f.src_arrow).symm) ≫
      f.arrow.hom ≫
      eqToHom (congrArg
        (fun u ↦ (F y.chart).obj (ActionCategory.objEquiv (G y.chart) (U y.chart) u))
        ((ofCharts_tgt F f.arrow).symm.trans f.tgt_arrow))
  map_id x := by
    have h : (𝟙 x : x ⟶ x).arrow = ⟨x.point, x.point, 𝟙 _⟩ :=
      ((ofCharts F).id_arrow x).trans (ofCharts_unit F x.chart x.point)
    generalize (𝟙 x : x ⟶ x) = e at h ⊢
    rcases e with ⟨_, _, _⟩
    subst h
    simp
  map_comp {x y z} f g := by
    rcases f with ⟨⟨sx₁, sy₁, m₁⟩, hs₁, ht₁⟩
    rcases g with ⟨⟨sx₂, sy₂, m₂⟩, hs₂, ht₂⟩
    obtain rfl : sx₁ = x.point := (ofCharts_src F _).symm.trans hs₁
    obtain rfl : sy₁ = y.point := (ofCharts_tgt F _).symm.trans ht₁
    obtain rfl : sx₂ = y.point := (ofCharts_src F _).symm.trans hs₂
    obtain rfl : sy₂ = z.point := (ofCharts_tgt F _).symm.trans ht₂
    have h : (⟨⟨x.point, y.point, m₁⟩, hs₁, ht₁⟩ ≫ ⟨⟨y.point, z.point, m₂⟩, hs₂, ht₂⟩ :
        x ⟶ z).arrow = ⟨x.point, z.point, m₁ ≫ eqToHom rfl ≫ m₂⟩ :=
      ((ofCharts F).comp_arrow _ _).trans (ofCharts_comp F _ _ _)
    generalize (⟨⟨x.point, y.point, m₁⟩, hs₁, ht₁⟩ ≫ ⟨⟨y.point, z.point, m₂⟩, hs₂, ht₂⟩ :
      x ⟶ z) = e at h ⊢
    rcases e with ⟨_, _, _⟩
    subst h
    simp

/-- `toGroupoid F` evaluates on `⟨i, x⟩` as `(F i).obj (objEquiv (G i) (U i) x)`. -/
@[simp]
theorem toGroupoid_obj (F : ∀ i, ActionCategory (G i) (U i) ⥤ C)
    [∀ i, (F i).Full] [∀ i, (F i).Faithful] (x : (ofCharts F).Obj) :
    (toGroupoid F).obj x =
      (F x.chart).obj (ActionCategory.objEquiv (G x.chart) (U x.chart) x.point) := (rfl)

/-- Action of `toGroupoid F` on morphisms. -/
theorem toGroupoid_map (F : ∀ i, ActionCategory (G i) (U i) ⥤ C)
    [∀ i, (F i).Full] [∀ i, (F i).Faithful] {x y : (ofCharts F).Obj} (f : x ⟶ y) :
    (toGroupoid F).map f =
      eqToHom (congrArg
        (fun u ↦ (F x.chart).obj (ActionCategory.objEquiv (G x.chart) (U x.chart) u))
        ((ofCharts_src F f.arrow).symm.trans f.src_arrow).symm) ≫ f.arrow.hom ≫
        eqToHom (congrArg
          (fun u ↦ (F y.chart).obj (ActionCategory.objEquiv (G y.chart) (U y.chart) u))
          ((ofCharts_tgt F f.arrow).symm.trans f.tgt_arrow)) := (rfl)

private theorem toGroupoid_map_of_arrow_eq (F : ∀ i, ActionCategory (G i) (U i) ⥤ C)
    [∀ i, (F i).Full] [∀ i, (F i).Faithful] {x y : (ofCharts F).Obj} (f : x ⟶ y)
    {α : ChartOverlap (F x.chart) (F y.chart)} (hf : f.arrow = α)
    (hs : α.src = x.point) (ht : α.tgt = y.point) :
    (toGroupoid F).map f =
      eqToHom (congrArg
        (fun u ↦ (F x.chart).obj (ActionCategory.objEquiv (G x.chart) (U x.chart) u)) hs.symm) ≫
        α.hom ≫
        eqToHom (congrArg
          (fun u ↦ (F y.chart).obj (ActionCategory.objEquiv (G y.chart) (U y.chart) u)) ht) := by
  rcases f with ⟨_, _, _⟩
  subst hf
  rfl

/-- Action of `toGroupoid F` on a morphism constructed directly from chart points and a morphism in
`C`. -/
@[simp]
theorem toGroupoid_map_mk (F : ∀ i, ActionCategory (G i) (U i) ⥤ C)
    [∀ i, (F i).Full] [∀ i, (F i).Faithful] {i j : ι} (x : U i) (y : U j)
    (m : (F i).obj (ActionCategory.objEquiv (G i) (U i) x) ⟶
      (F j).obj (ActionCategory.objEquiv (G j) (U j) y))
    (hs : (ofCharts F).src ⟨x, y, m⟩ = x) (ht : (ofCharts F).tgt ⟨x, y, m⟩ = y) :
    (toGroupoid F).map (⟨⟨x, y, m⟩, hs, ht⟩ : (⟨i, x⟩ : (ofCharts F).Obj) ⟶ ⟨j, y⟩) = m := by
  simp [toGroupoid_map]

/-- `toGroupoid F` is faithful. -/
instance instFaithfulToGroupoid (F : ∀ i, ActionCategory (G i) (U i) ⥤ C)
    [∀ i, (F i).Full] [∀ i, (F i).Faithful] : (toGroupoid F).Faithful where
  map_injective {x y} f₁ f₂ h := by
    obtain ⟨⟨sx₁, sy₁, m₁⟩, hs₁, ht₁⟩ := f₁
    obtain ⟨⟨sx₂, sy₂, m₂⟩, hs₂, ht₂⟩ := f₂
    have hs₁' : sx₁ = x.point := (ofCharts_src F _).symm.trans hs₁
    have ht₁' : sy₁ = y.point := (ofCharts_tgt F _).symm.trans ht₁
    have hs₂' : sx₂ = x.point := (ofCharts_src F _).symm.trans hs₂
    have ht₂' : sy₂ = y.point := (ofCharts_tgt F _).symm.trans ht₂
    subst hs₁' ht₁' hs₂' ht₂'
    refine Obj.Hom.ext (ChartOverlap.ext rfl rfl (heq_of_eq ?_))
    simpa [toGroupoid_map] using h

/-- `toGroupoid F` is full. -/
instance instFullToGroupoid (F : ∀ i, ActionCategory (G i) (U i) ⥤ C)
    [∀ i, (F i).Full] [∀ i, (F i).Faithful] : (toGroupoid F).Full where
  map_surjective {x y} m :=
    ⟨⟨⟨x.point, y.point, m⟩, ofCharts_src F _, ofCharts_tgt F _⟩,
      toGroupoid_map_mk F x.point y.point m _ _⟩

/-- `toGroupoid F` is essentially surjective precisely when every object of `C` is isomorphic to a
point in the image of one of the charts `F i`. -/
theorem essSurj_toGroupoid_iff (F : ∀ i, ActionCategory (G i) (U i) ⥤ C)
    [∀ i, (F i).Full] [∀ i, (F i).Faithful] :
    (toGroupoid F).EssSurj ↔
      ∀ c : C, ∃ (i : ι) (x : U i),
        Nonempty ((F i).obj (ActionCategory.objEquiv (G i) (U i) x) ≅ c) := by
  constructor
  · intro h c
    obtain ⟨y, ⟨e⟩⟩ := h.mem_essImage c
    exact ⟨y.chart, y.point, ⟨e⟩⟩
  · refine fun h ↦ ⟨fun c ↦ ?_⟩
    obtain ⟨i, x, ⟨e⟩⟩ := h c
    exact ⟨⟨i, x⟩, ⟨e⟩⟩

/-- Restricting `toGroupoid F` along the `i`-th chart inclusion recovers `F i`. -/
@[simp]
theorem chartFunctor_comp_toGroupoid (F : ∀ i, ActionCategory (G i) (U i) ⥤ C)
    [∀ i, (F i).Full] [∀ i, (F i).Faithful] (i : ι) :
    (ofCharts F).chartFunctor i ⋙ toGroupoid F = F i := by
  refine CategoryTheory.Functor.hext (fun a ↦ congrArg (F i).obj (ActionCategory.back_coe a))
    fun {a b} f ↦ ?_
  let g₀ : G i := f.hom
  have ea : ActionCategory.objEquiv (G i) (U i) a.back = a := ActionCategory.back_coe a
  have eb : ActionCategory.objEquiv (G i) (U i) (g₀ • a.back) = b :=
    (congrArg (ActionCategory.objEquiv (G i) (U i)) (ActionCategory.hom_smul f)).trans
      (ActionCategory.back_coe b)
  have hact : (Functor.Elements.homMk g₀ rfl :
      ActionCategory.objEquiv (G i) (U i) a.back ⟶
        ActionCategory.objEquiv (G i) (U i) (g₀ • a.back)) =
      eqToHom ea ≫ f ≫ eqToHom eb.symm :=
    Functor.Elements.hom_ext (by simp [g₀])
  have hf : (((ofCharts F).chartFunctor i).map f).arrow =
      ⟨a.back, g₀ • a.back,
        𝟙 _ ≫ (F i).map (Functor.Elements.homMk g₀ rfl :
          ActionCategory.objEquiv (G i) (U i) a.back ⟶
            ActionCategory.objEquiv (G i) (U i) (g₀ • a.back))⟩ :=
    ((ofCharts F).chartFunctor_map_arrow i f).trans (congrArg (g₀ • ·) (ofCharts_unit F i a.back))
  rw [Functor.comp_map, toGroupoid_map_of_arrow_eq F _ hf rfl (ActionCategory.hom_smul f)]
  dsimp only
  rw [Category.id_comp, hact, (F i).map_comp, (F i).map_comp, eqToHom_map, eqToHom_map]
  simp

section Reindex

variable {ν μ : Type*} {G' : μ → Type*} [∀ m, Group (G' m)]
  {U' : μ → Type*} [∀ m, MulAction (G' m) (U' m)]
  (F : ∀ m, ActionCategory (G' m) (U' m) ⥤ C) [∀ m, (F m).Full] [∀ m, (F m).Faithful]

/-- Reindexing a family of fully faithful action charts along `σ : ν → μ` induces a canonical
morphism of chart atlases `(ofCharts (fun n ↦ F (σ n))).Hom (ofCharts F)`. -/
-- `expose, implicit_reducible`: unification of dependent chart types in `groupHom`, `obj`, and
-- `map` must see `(ofChartsReindexHom F σ).index n` as `σ n`.
@[expose, implicit_reducible]
noncomputable def ofChartsReindexHom (σ : ν → μ) :
    (ofCharts (fun n ↦ F (σ n))).Hom (ofCharts F) where
  index := σ
  groupHom n := MonoidHom.id (G' (σ n))
  obj _ := id
  map α := α
  src_map _ := by simp
  tgt_map _ := by simp
  map_unit _ _ := by simp
  map_comp _ _ _ := by simp
  map_smul _ _ := by simp

/-- Index map of `ofChartsReindexHom`. -/
@[simp]
theorem ofChartsReindexHom_index (σ : ν → μ) :
    (ofChartsReindexHom F σ).index = σ := (rfl)

/-- Group homomorphism of `ofChartsReindexHom` at chart `n`. -/
@[simp]
theorem ofChartsReindexHom_groupHom (σ : ν → μ) (n : ν) :
    (ofChartsReindexHom F σ).groupHom n = MonoidHom.id (G' (σ n)) := (rfl)

/-- Point map of `ofChartsReindexHom` at chart `n`. -/
@[simp]
theorem ofChartsReindexHom_obj (σ : ν → μ) (n : ν) (x : U' (σ n)) :
    (ofChartsReindexHom F σ).obj n x = x := (rfl)

/-- Overlap-arrow map of `ofChartsReindexHom`. -/
@[simp]
theorem ofChartsReindexHom_map (σ : ν → μ) {n₁ n₂ : ν}
    (α : ChartOverlap (F (σ n₁)) (F (σ n₂))) :
    (ofChartsReindexHom F σ).map α = α := (rfl)

/-- `ofChartsReindexHom` commutes strictly with `toGroupoid`. -/
@[simp]
theorem ofChartsReindexHom_toFunctor_comp_toGroupoid (σ : ν → μ) :
    (ofChartsReindexHom F σ).toFunctor ⋙ toGroupoid F = toGroupoid (fun n ↦ F (σ n)) := (rfl)

/-- Any chart-family reindexing morphism is faithful on presenting groupoids. -/
instance instFaithfulOfChartsReindexHom (σ : ν → μ) :
    (ofChartsReindexHom F σ).toFunctor.Faithful :=
  Functor.Faithful.of_comp_eq (ofChartsReindexHom_toFunctor_comp_toGroupoid F σ)

/-- Any chart-family reindexing morphism is full on presenting groupoids. -/
instance instFullOfChartsReindexHom (σ : ν → μ) :
    (ofChartsReindexHom F σ).toFunctor.Full :=
  Functor.Full.of_comp_faithful_iso (eqToIso (ofChartsReindexHom_toFunctor_comp_toGroupoid F σ))

end Reindex

end GroupoidCharts

end OfCharts

section RoundTrip

variable {ι : Type u₁} {G : ι → Type u₂} [∀ i, Group (G i)]
  {U : ι → Type u₃} [∀ i, MulAction (G i) (U i)]
  {R : ι → ι → Type u₄} [∀ i j, MulAction (G j) (R i j)]
  (𝓐 : ChartAtlas G U R)

private theorem chartOverlap_chartFunctor_ext {i j : ι}
    {α β : ChartOverlap (𝓐.chartFunctor i) (𝓐.chartFunctor j)}
    (h : α.hom.arrow = β.hom.arrow) : α = β := by
  have hs : α.src = β.src :=
    (ActionCategory.coe_back (M := G i) α.src).symm.trans <|
      α.hom.src_arrow.symm.trans ((congrArg 𝓐.src h).trans
        (β.hom.src_arrow.trans (ActionCategory.coe_back (M := G i) β.src)))
  have ht : α.tgt = β.tgt :=
    (ActionCategory.coe_back (M := G j) α.tgt).symm.trans <|
      α.hom.tgt_arrow.symm.trans ((congrArg 𝓐.tgt h).trans
        (β.hom.tgt_arrow.trans (ActionCategory.coe_back (M := G j) β.tgt)))
  exact ChartOverlap.ext hs ht <|
    Obj.Hom.hext
      (congrArg (fun u ↦ (𝓐.chartFunctor i).obj (ActionCategory.objEquiv (G i) (U i) u)) hs)
      (congrArg (fun u ↦ (𝓐.chartFunctor j).obj (ActionCategory.objEquiv (G j) (U j) u)) ht)
      (heq_of_eq h)

/-- Inverse atlas morphism from `ofCharts 𝓐.chartFunctor` back to `𝓐`, extracting the underlying
overlap arrow of each morphism in `𝓐.Obj`. -/
-- `expose, implicit_reducible`: unification of dependent chart types in `groupHom`, `obj`, and
-- `map` must see `𝓐.fromOfCharts.index i` as `i`.
@[expose, implicit_reducible]
noncomputable def fromOfCharts : (ofCharts 𝓐.chartFunctor).Hom 𝓐 where
  index i := i
  groupHom i := MonoidHom.id (G i)
  obj _ x := x
  map α := α.hom.arrow
  src_map {i _} α := by
    simpa using (α.hom.src_arrow).trans (ActionCategory.coe_back (M := G i) α.src)
  tgt_map {_ j} α := by
    simpa using (α.hom.tgt_arrow).trans (ActionCategory.coe_back (M := G j) α.tgt)
  map_unit i x := by
    rw [ofCharts_unit, id_arrow]
    exact congrArg (𝓐.unit i) (ActionCategory.coe_back (M := G i) x)
  map_comp {_ j _} α β h := by
    have h' : α.tgt = β.src := (ofCharts_tgt _ α).symm.trans (h.trans (ofCharts_src _ β))
    have hsrc : 𝓐.tgt (𝓐.unit j (ActionCategory.objEquiv (G j) (U j) α.tgt).back) =
        𝓐.src β.hom.arrow :=
      (𝓐.tgt_unit j _).trans
        ((congrArg (fun s ↦ (ActionCategory.objEquiv (G j) (U j) s).back) h').trans
          β.hom.src_arrow.symm)
    rw [ofCharts_comp, comp_arrow]
    exact 𝓐.comp_congr rfl
      ((𝓐.comp_congr (𝓐.eqToHom_mk_arrow _) rfl _ hsrc).trans
        (𝓐.unit_comp _ β.hom.arrow hsrc)) _ _
  map_smul {_ j} g α := by
    have htgt : 𝓐.tgt α.hom.arrow = 𝓐.src (g • 𝓐.unit j (𝓐.tgt α.hom.arrow)) :=
      (𝓐.src_unit j _).symm.trans (𝓐.src_smul g _).symm
    rw [chartOverlap_smul_hom, comp_arrow]
    exact (𝓐.comp_congr rfl
      ((𝓐.chartFunctor_map_arrow j _).trans (congrArg (g • 𝓐.unit j ·) α.hom.tgt_arrow.symm))
      _ htgt).trans (𝓐.comp_smul_unit_tgt α.hom.arrow g htgt)

/-- Index map of `fromOfCharts`. -/
@[simp]
theorem fromOfCharts_index (i : ι) : 𝓐.fromOfCharts.index i = i := (rfl)

/-- Group homomorphism of `fromOfCharts` at chart `i`. -/
@[simp]
theorem fromOfCharts_groupHom (i : ι) : 𝓐.fromOfCharts.groupHom i = MonoidHom.id (G i) := (rfl)

/-- Point map of `fromOfCharts` at chart `i`. -/
@[simp]
theorem fromOfCharts_obj (i : ι) (x : U i) : 𝓐.fromOfCharts.obj i x = x := (rfl)

/-- Overlap-arrow map of `fromOfCharts`. -/
@[simp]
theorem fromOfCharts_map {i j : ι} (α : ChartOverlap (𝓐.chartFunctor i) (𝓐.chartFunctor j)) :
    𝓐.fromOfCharts.map α = α.hom.arrow := (rfl)

/-- Forward atlas morphism from `𝓐` to `ofCharts 𝓐.chartFunctor`, sending each overlap arrow to the
morphism it defines in `𝓐.Obj`. -/
-- `expose, implicit_reducible`: unification of dependent chart types in `groupHom`, `obj`, and
-- `map` must see `𝓐.toOfCharts.index i` as `i`.
@[expose, implicit_reducible]
noncomputable def toOfCharts : 𝓐.Hom (ofCharts 𝓐.chartFunctor) where
  index i := i
  groupHom i := MonoidHom.id (G i)
  obj _ x := x
  map {i j} α := ⟨𝓐.src α, 𝓐.tgt α,
    ⟨α, (ActionCategory.coe_back (M := G i) (𝓐.src α)).symm,
      (ActionCategory.coe_back (M := G j) (𝓐.tgt α)).symm⟩⟩
  src_map _ := by simp
  tgt_map _ := by simp
  map_unit i x := by exact chartOverlap_chartFunctor_ext 𝓐 (𝓐.fromOfCharts.map_unit i x).symm
  map_comp {i j k} α β h := by
    let α' : ChartOverlap (𝓐.chartFunctor i) (𝓐.chartFunctor j) := ⟨𝓐.src α, 𝓐.tgt α,
      ⟨α, (ActionCategory.coe_back (M := G i) (𝓐.src α)).symm,
        (ActionCategory.coe_back (M := G j) (𝓐.tgt α)).symm⟩⟩
    let β' : ChartOverlap (𝓐.chartFunctor j) (𝓐.chartFunctor k) := ⟨𝓐.src β, 𝓐.tgt β,
      ⟨β, (ActionCategory.coe_back (M := G j) (𝓐.src β)).symm,
        (ActionCategory.coe_back (M := G k) (𝓐.tgt β)).symm⟩⟩
    exact chartOverlap_chartFunctor_ext 𝓐
      (𝓐.fromOfCharts.map_comp α' β'
        ((ofCharts_tgt _ α').trans (h.trans (ofCharts_src _ β').symm))).symm
  map_smul {i j} g α := by
    let α' : ChartOverlap (𝓐.chartFunctor i) (𝓐.chartFunctor j) := ⟨𝓐.src α, 𝓐.tgt α,
      ⟨α, (ActionCategory.coe_back (M := G i) (𝓐.src α)).symm,
        (ActionCategory.coe_back (M := G j) (𝓐.tgt α)).symm⟩⟩
    exact chartOverlap_chartFunctor_ext 𝓐 (𝓐.fromOfCharts.map_smul g α').symm

/-- Index map of `toOfCharts`. -/
@[simp]
theorem toOfCharts_index (i : ι) : 𝓐.toOfCharts.index i = i := (rfl)

/-- Group homomorphism of `toOfCharts` at chart `i`. -/
@[simp]
theorem toOfCharts_groupHom (i : ι) : 𝓐.toOfCharts.groupHom i = MonoidHom.id (G i) := (rfl)

/-- Point map of `toOfCharts` at chart `i`. -/
@[simp]
theorem toOfCharts_obj (i : ι) (x : U i) : 𝓐.toOfCharts.obj i x = x := (rfl)

/-- Underlying arrow of `toOfCharts.map α`. -/
@[simp]
theorem toOfCharts_map_hom_arrow {i j : ι} (α : R i j) :
    (𝓐.toOfCharts.map α).hom.arrow = α := (rfl)

/-- The functor induced by `fromOfCharts` on presenting groupoids coincides with
`toGroupoid 𝓐.chartFunctor`. -/
@[simp]
theorem fromOfCharts_toFunctor :
    𝓐.fromOfCharts.toFunctor = toGroupoid 𝓐.chartFunctor := by
  have hobj (x : (ofCharts 𝓐.chartFunctor).Obj) :
      𝓐.fromOfCharts.toFunctor.obj x = (toGroupoid 𝓐.chartFunctor).obj x :=
    congrArg (Obj.mk x.chart) (ActionCategory.coe_back (M := G x.chart) x.point).symm
  refine CategoryTheory.Functor.hext hobj fun {x y} f ↦
    Obj.Hom.hext (hobj x) (hobj y) (heq_of_eq ?_)
  obtain ⟨⟨sx, sy, m⟩, hs, ht⟩ := f
  have hs' : sx = x.point := (ofCharts_src _ _).symm.trans hs
  have ht' : sy = y.point := (ofCharts_tgt _ _).symm.trans ht
  subst hs' ht'
  simp [toGroupoid_map]

/-- `fromOfCharts` is a strict left inverse to `toOfCharts`. -/
@[simp]
theorem fromOfCharts_comp_toOfCharts :
    𝓐.fromOfCharts.comp 𝓐.toOfCharts = Hom.id 𝓐 :=
  Hom.ext rfl (fun _ ↦ HEq.rfl) (fun _ ↦ HEq.rfl)

/-- `fromOfCharts` is a strict right inverse to `toOfCharts` (equivalently, `toOfCharts` is a
strict left inverse to `fromOfCharts`). -/
@[simp]
theorem toOfCharts_comp_fromOfCharts :
    𝓐.toOfCharts.comp 𝓐.fromOfCharts = Hom.id (ofCharts 𝓐.chartFunctor) :=
  Hom.ext rfl (fun _ ↦ HEq.rfl) fun _ ↦ heq_of_eq (chartOverlap_chartFunctor_ext 𝓐 rfl)

end RoundTrip

section SumElim

variable {C : Type*} [Category* C]
  {ι : Type u₁} {G : ι → Type u₂} [∀ i, Group (G i)]
  {U : ι → Type u₃} [∀ i, MulAction (G i) (U i)]
  {κ : Type v₁} {G' : κ → Type u₂} [∀ k, Group (G' k)]
  {U' : κ → Type u₃} [∀ k, MulAction (G' k) (U' k)]

/-- Group structure on the disjoint-sum group family `Sum.elim G G' s`. -/
instance instGroupSumElim : ∀ s : ι ⊕ κ, Group (Sum.elim G G' s)
  | .inl i => inferInstanceAs (Group (G i))
  | .inr k => inferInstanceAs (Group (G' k))

/-- Group action of `Sum.elim G G' s` on `Sum.elim U U' s`. -/
instance instMulActionSumElim :
    ∀ s : ι ⊕ κ, MulAction (Sum.elim G G' s) (Sum.elim U U' s)
  | .inl i => inferInstanceAs (MulAction (G i) (U i))
  | .inr k => inferInstanceAs (MulAction (G' k) (U' k))

variable (F₁ : ∀ i, ActionCategory (G i) (U i) ⥤ C)
  (F₂ : ∀ k, ActionCategory (G' k) (U' k) ⥤ C)

/-- Combining two families of action charts into `C` over `ι ⊕ κ`. -/
-- The body is exposed: `sumCharts` must reduce definitionally on `Sum.inl` and `Sum.inr` in the
-- dependent functor types of `sumCharts_inl` and `sumCharts_inr`.
@[expose]
def sumCharts : ∀ s : ι ⊕ κ, ActionCategory (Sum.elim G G' s) (Sum.elim U U' s) ⥤ C
  | .inl i => F₁ i
  | .inr k => F₂ k

/-- `sumCharts` evaluates on `Sum.inl i` as `F₁ i`. -/
@[simp]
theorem sumCharts_inl (i : ι) : sumCharts F₁ F₂ (.inl i) = F₁ i := (rfl)

/-- `sumCharts` evaluates on `Sum.inr k` as `F₂ k`. -/
@[simp]
theorem sumCharts_inr (k : κ) : sumCharts F₁ F₂ (.inr k) = F₂ k := (rfl)

variable [∀ i, (F₁ i).Full] [∀ i, (F₁ i).Faithful]
  [∀ k, (F₂ k).Full] [∀ k, (F₂ k).Faithful]

/-- Each chart of `sumCharts F₁ F₂` is full. -/
instance instFullSumCharts : ∀ s : ι ⊕ κ, (sumCharts F₁ F₂ s).Full
  | .inl i => inferInstanceAs (F₁ i).Full
  | .inr k => inferInstanceAs (F₂ k).Full

/-- Each chart of `sumCharts F₁ F₂` is faithful. -/
instance instFaithfulSumCharts : ∀ s : ι ⊕ κ, (sumCharts F₁ F₂ s).Faithful
  | .inl i => inferInstanceAs (F₁ i).Faithful
  | .inr k => inferInstanceAs (F₂ k).Faithful

section GroupoidSum

variable [IsGroupoid C]

/-- Left inclusion of `ofCharts F₁` into the combined chart atlas `ofCharts (sumCharts F₁ F₂)`. -/
-- `expose, implicit_reducible`: unification of dependent chart types must see
-- `(sumInlHom F₁ F₂).index i` as `Sum.inl i`.
@[expose, implicit_reducible]
noncomputable def sumInlHom : (ofCharts F₁).Hom (ofCharts (sumCharts F₁ F₂)) :=
  ofChartsReindexHom (sumCharts F₁ F₂) Sum.inl

/-- Index map of `sumInlHom`. -/
@[simp]
theorem sumInlHom_index : (sumInlHom F₁ F₂).index = Sum.inl := (rfl)

/-- Group homomorphism of `sumInlHom` at chart `i`. -/
@[simp]
theorem sumInlHom_groupHom (i : ι) : (sumInlHom F₁ F₂).groupHom i = MonoidHom.id (G i) := (rfl)

/-- Point map of `sumInlHom` at chart `i`. -/
@[simp]
theorem sumInlHom_obj (i : ι) (x : U i) : (sumInlHom F₁ F₂).obj i x = x := (rfl)

/-- Overlap-arrow map of `sumInlHom`. -/
@[simp]
theorem sumInlHom_map {i j : ι} (α : ChartOverlap (F₁ i) (F₁ j)) :
    (sumInlHom F₁ F₂).map α = α := (rfl)

/-- `sumInlHom` commutes strictly with `toGroupoid`. -/
@[simp]
theorem sumInlHom_toFunctor_comp_toGroupoid :
    (sumInlHom F₁ F₂).toFunctor ⋙ toGroupoid (sumCharts F₁ F₂) = toGroupoid F₁ :=
  ofChartsReindexHom_toFunctor_comp_toGroupoid (sumCharts F₁ F₂) Sum.inl

/-- The left chart-family inclusion is faithful on presenting groupoids. -/
instance instFaithfulSumInlHom : (sumInlHom F₁ F₂).toFunctor.Faithful :=
  Functor.Faithful.of_comp_eq (sumInlHom_toFunctor_comp_toGroupoid F₁ F₂)

/-- The left chart-family inclusion is full on presenting groupoids. -/
instance instFullSumInlHom : (sumInlHom F₁ F₂).toFunctor.Full :=
  Functor.Full.of_comp_faithful_iso (eqToIso (sumInlHom_toFunctor_comp_toGroupoid F₁ F₂))

/-- Right inclusion of `ofCharts F₂` into the combined chart atlas `ofCharts (sumCharts F₁ F₂)`. -/
-- `expose, implicit_reducible`: unification of dependent chart types must see
-- `(sumInrHom F₁ F₂).index k` as `Sum.inr k`.
@[expose, implicit_reducible]
noncomputable def sumInrHom : (ofCharts F₂).Hom (ofCharts (sumCharts F₁ F₂)) :=
  ofChartsReindexHom (sumCharts F₁ F₂) Sum.inr

/-- Index map of `sumInrHom`. -/
@[simp]
theorem sumInrHom_index : (sumInrHom F₁ F₂).index = Sum.inr := (rfl)

/-- Group homomorphism of `sumInrHom` at chart `k`. -/
@[simp]
theorem sumInrHom_groupHom (k : κ) : (sumInrHom F₁ F₂).groupHom k = MonoidHom.id (G' k) := (rfl)

/-- Point map of `sumInrHom` at chart `k`. -/
@[simp]
theorem sumInrHom_obj (k : κ) (x : U' k) : (sumInrHom F₁ F₂).obj k x = x := (rfl)

/-- Overlap-arrow map of `sumInrHom`. -/
@[simp]
theorem sumInrHom_map {k l : κ} (α : ChartOverlap (F₂ k) (F₂ l)) :
    (sumInrHom F₁ F₂).map α = α := (rfl)

/-- `sumInrHom` commutes strictly with `toGroupoid`. -/
@[simp]
theorem sumInrHom_toFunctor_comp_toGroupoid :
    (sumInrHom F₁ F₂).toFunctor ⋙ toGroupoid (sumCharts F₁ F₂) = toGroupoid F₂ :=
  ofChartsReindexHom_toFunctor_comp_toGroupoid (sumCharts F₁ F₂) Sum.inr

/-- The right chart-family inclusion is faithful on presenting groupoids. -/
instance instFaithfulSumInrHom : (sumInrHom F₁ F₂).toFunctor.Faithful :=
  Functor.Faithful.of_comp_eq (sumInrHom_toFunctor_comp_toGroupoid F₁ F₂)

/-- The right chart-family inclusion is full on presenting groupoids. -/
instance instFullSumInrHom : (sumInrHom F₁ F₂).toFunctor.Full :=
  Functor.Full.of_comp_faithful_iso (eqToIso (sumInrHom_toFunctor_comp_toGroupoid F₁ F₂))

end GroupoidSum

end SumElim

end TauCeti.ChartAtlas
