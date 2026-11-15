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
   chart atlases comes with projection morphisms `fstHom` and `sndHom` assembling into a categorical
   equivalence `(𝓐.prod 𝓑).Obj ≌ 𝓐.Obj × 𝓑.Obj` (`TauCeti.ChartAtlas.prodObjEquivalence`).
3. **Induced atlas of action charts (`TauCeti.ChartAtlas.ofCharts`).** Any family of fully faithful
   functors `F i : ActionCategory (G i) (U i) ⥤ C` into a groupoid `C` induces a chart atlas
   `ofCharts F` on `ChartOverlap F` together with a canonical fully faithful comparison functor
   `toGroupoid F : (ofCharts F).Obj ⥤ C`, which is essentially surjective precisely when the chart
   images meet every isomorphism class of `C`.
4. **Round-trip and union comparisons (`toOfCharts`, `fromOfCharts`, `sumCharts`).** Applying
   `ofCharts` to `𝓐.chartFunctor` recovers `𝓐` up to strict mutual inverse atlas morphisms, and two
   chart families `F₁`, `F₂` into `C` embed fully and faithfully into the combined atlas
   `ofCharts (sumCharts F₁ F₂)` compatibly with `toGroupoid`.

## Main declarations

* `TauCeti.ChartAtlas.restrict`, `TauCeti.ChartAtlas.restrictHom`: restriction of a chart atlas to
  invariant subactions and its full and faithful inclusion.
* `TauCeti.ChartAtlas.prod`, `TauCeti.ChartAtlas.prodObjEquivalence`: binary product of chart
  atlases and equivalence of presenting groupoids.
* `TauCeti.ChartAtlas.ChartOverlap`, `TauCeti.ChartAtlas.ofCharts`,
  `TauCeti.ChartAtlas.toGroupoid`: chart atlas induced by a family of fully faithful action charts
  and its comparison functor.
* `TauCeti.ChartAtlas.toOfCharts`, `TauCeti.ChartAtlas.fromOfCharts`: mutual inverse atlas
  morphisms between `𝓐` and `ofCharts 𝓐.chartFunctor`.
* `TauCeti.ChartAtlas.sumCharts`, `TauCeti.ChartAtlas.sumInlHom`,
  `TauCeti.ChartAtlas.sumInrHom`: disjoint-sum chart family providing a common refinement of two
  chart atlases into the same groupoid.
-/

@[expose] public section

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

/-- The canonical inclusion morphism `(𝓐.restrict S).Hom 𝓐`, keeping all group labels. -/
def restrictHom : (𝓐.restrict S).Hom 𝓐 where
  index := id
  groupHom i := MonoidHom.id (G i)
  obj _ := Subtype.val
  map α := α.1
  src_map _ := rfl
  tgt_map _ := rfl
  map_unit _ _ := rfl
  map_comp _ _ _ := rfl
  map_smul _ _ := rfl

/-- The inclusion functor `(𝓐.restrict S).Obj ⥤ 𝓐.Obj` is faithful. -/
instance instFaithfulRestrictHom : (𝓐.restrictHom S).toFunctor.Faithful :=
  (Hom.faithful_toFunctor_iff _).mpr fun _ _ _ _ hm ↦ Subtype.ext hm

/-- The inclusion functor `(𝓐.restrict S).Obj ⥤ 𝓐.Obj` is full. -/
instance instFullRestrictHom : (𝓐.restrictHom S).toFunctor.Full :=
  (Hom.full_toFunctor_iff _).mpr fun x y β hs ht ↦
    ⟨⟨β, hs.symm ▸ x.2, ht.symm ▸ y.2⟩, Subtype.ext hs, Subtype.ext ht, rfl⟩

end Restrict

section Prod

variable {ι : Type u₁} {G₁ : ι → Type u₂} [∀ i, Group (G₁ i)]
  {U₁ : ι → Type u₃} [∀ i, MulAction (G₁ i) (U₁ i)]
  {R₁ : ι → ι → Type u₄} [∀ i j, MulAction (G₁ j) (R₁ i j)]
  {κ : Type v₁} {G₂ : κ → Type v₂} [∀ k, Group (G₂ k)]
  {U₂ : κ → Type v₃} [∀ k, MulAction (G₂ k) (U₂ k)]
  {R₂ : κ → κ → Type v₄} [∀ k l, MulAction (G₂ l) (R₂ k l)]
  (𝓐 : ChartAtlas G₁ U₁ R₁) (𝓑 : ChartAtlas G₂ U₂ R₂)

/-- Componentwise product domain `U₁ p.1 × U₂ p.2` for a binary product of chart atlases, equipped
with the componentwise action of `G₁ p.1 × G₂ p.2`. -/
@[ext]
structure ProdDomain (U₁ : ι → Type u₃) (U₂ : κ → Type v₃) (p : ι × κ) where
  /-- First chart coordinate. -/
  fst : U₁ p.1
  /-- Second chart coordinate. -/
  snd : U₂ p.2

/-- Componentwise action of `G₁ p.1 × G₂ p.2` on `ProdDomain U₁ U₂ p`. -/
instance instMulActionProdDomain (p : ι × κ) :
    MulAction (G₁ p.1 × G₂ p.2) (ProdDomain U₁ U₂ p) where
  smul g x := ⟨g.1 • x.fst, g.2 • x.snd⟩
  one_smul x := ProdDomain.ext (one_smul _ x.fst) (one_smul _ x.snd)
  mul_smul g h x := ProdDomain.ext (mul_smul g.1 h.1 x.fst) (mul_smul g.2 h.2 x.snd)

/-- Product overlap-arrow carrier on `ι × κ`, equipped with the componentwise action of
`G₁ q.1 × G₂ q.2`. -/
@[ext]
structure ProdArrow (R₁ : ι → ι → Type u₄) (R₂ : κ → κ → Type v₄) (p q : ι × κ) where
  /-- First overlap arrow. -/
  fst : R₁ p.1 q.1
  /-- Second overlap arrow. -/
  snd : R₂ p.2 q.2

/-- Componentwise action of `G₁ q.1 × G₂ q.2` on `ProdArrow R₁ R₂ p q`. -/
instance instMulActionProdArrow (p q : ι × κ) :
    MulAction (G₁ q.1 × G₂ q.2) (ProdArrow R₁ R₂ p q) where
  smul g α := ⟨g.1 • α.fst, g.2 • α.snd⟩
  one_smul α := ProdArrow.ext (one_smul _ α.fst) (one_smul _ α.snd)
  mul_smul g h α := ProdArrow.ext (mul_smul g.1 h.1 α.fst) (mul_smul g.2 h.2 α.snd)

/-- The binary product `𝓐.prod 𝓑` of two retained-arrow chart atlases. -/
def prod : ChartAtlas (fun p : ι × κ ↦ G₁ p.1 × G₂ p.2)
    (ProdDomain U₁ U₂) (ProdArrow R₁ R₂) where
  src α := ⟨𝓐.src α.fst, 𝓑.src α.snd⟩
  tgt α := ⟨𝓐.tgt α.fst, 𝓑.tgt α.snd⟩
  unit p x := ⟨𝓐.unit p.1 x.fst, 𝓑.unit p.2 x.snd⟩
  inv α := ⟨𝓐.inv α.fst, 𝓑.inv α.snd⟩
  comp α β h :=
    ⟨𝓐.comp α.fst β.fst (congrArg ProdDomain.fst h),
      𝓑.comp α.snd β.snd (congrArg ProdDomain.snd h)⟩
  src_unit p x := ProdDomain.ext (𝓐.src_unit p.1 x.fst) (𝓑.src_unit p.2 x.snd)
  tgt_unit p x := ProdDomain.ext (𝓐.tgt_unit p.1 x.fst) (𝓑.tgt_unit p.2 x.snd)
  src_inv α := ProdDomain.ext (𝓐.src_inv α.fst) (𝓑.src_inv α.snd)
  tgt_inv α := ProdDomain.ext (𝓐.tgt_inv α.fst) (𝓑.tgt_inv α.snd)
  src_comp _ _ _ := ProdDomain.ext (𝓐.src_comp _ _ _) (𝓑.src_comp _ _ _)
  tgt_comp _ _ _ := ProdDomain.ext (𝓐.tgt_comp _ _ _) (𝓑.tgt_comp _ _ _)
  unit_comp _ _ _ := ProdArrow.ext (𝓐.unit_comp _ _ _) (𝓑.unit_comp _ _ _)
  comp_unit _ _ _ := ProdArrow.ext (𝓐.comp_unit _ _ _) (𝓑.comp_unit _ _ _)
  comp_assoc _ _ _ _ _ := ProdArrow.ext (𝓐.comp_assoc _ _ _ _ _) (𝓑.comp_assoc _ _ _ _ _)
  comp_inv α := ProdArrow.ext (𝓐.comp_inv α.fst) (𝓑.comp_inv α.snd)
  inv_comp α := ProdArrow.ext (𝓐.inv_comp α.fst) (𝓑.inv_comp α.snd)
  src_smul g α := ProdDomain.ext (𝓐.src_smul g.1 α.fst) (𝓑.src_smul g.2 α.snd)
  tgt_smul g α := ProdDomain.ext (𝓐.tgt_smul g.1 α.fst) (𝓑.tgt_smul g.2 α.snd)
  comp_smul α g β _ := ProdArrow.ext (𝓐.comp_smul α.fst g.1 β.fst _) (𝓑.comp_smul α.snd g.2 β.snd _)
  existsUnique_smul_eq α β h :=
    let ⟨g₁, hg₁, hu₁⟩ := 𝓐.existsUnique_smul_eq α.fst β.fst (congrArg ProdDomain.fst h)
    let ⟨g₂, hg₂, hu₂⟩ := 𝓑.existsUnique_smul_eq α.snd β.snd (congrArg ProdDomain.snd h)
    ⟨(g₁, g₂), ProdArrow.ext hg₁ hg₂, fun g hg ↦
      Prod.ext (hu₁ g.1 (congrArg ProdArrow.fst hg)) (hu₂ g.2 (congrArg ProdArrow.snd hg))⟩

/-- First projection morphism `(𝓐.prod 𝓑).Hom 𝓐`. -/
def fstHom : (𝓐.prod 𝓑).Hom 𝓐 where
  index := Prod.fst
  groupHom _ := MonoidHom.fst _ _
  obj _ := ProdDomain.fst
  map := ProdArrow.fst
  src_map _ := rfl
  tgt_map _ := rfl
  map_unit _ _ := rfl
  map_comp _ _ _ := rfl
  map_smul _ _ := rfl

/-- Second projection morphism `(𝓐.prod 𝓑).Hom 𝓑`. -/
def sndHom : (𝓐.prod 𝓑).Hom 𝓑 where
  index := Prod.snd
  groupHom _ := MonoidHom.snd _ _
  obj _ := ProdDomain.snd
  map := ProdArrow.snd
  src_map _ := rfl
  tgt_map _ := rfl
  map_unit _ _ := rfl
  map_comp _ _ _ := rfl
  map_smul _ _ := rfl

/-- Categorical equivalence `(𝓐.prod 𝓑).Obj ≌ 𝓐.Obj × 𝓑.Obj` identifying the presenting groupoid
of a product atlas with the product of the presenting groupoids. -/
def prodObjEquivalence : (𝓐.prod 𝓑).Obj ≌ 𝓐.Obj × 𝓑.Obj where
  functor := (𝓐.fstHom 𝓑).toFunctor.prod' (𝓐.sndHom 𝓑).toFunctor
  inverse :=
    { obj p := ⟨(p.1.chart, p.2.chart), ⟨p.1.point, p.2.point⟩⟩
      map f := ⟨⟨f.1.arrow, f.2.arrow⟩, ProdDomain.ext f.1.src_arrow f.2.src_arrow,
        ProdDomain.ext f.1.tgt_arrow f.2.tgt_arrow⟩
      map_id _ := rfl
      map_comp _ _ := rfl }
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp x := Prod.ext
    (by change (𝓐.fstHom 𝓑).toFunctor.map (𝟙 x) ≫ 𝟙 _ = _; simp)
    (by change (𝓐.sndHom 𝓑).toFunctor.map (𝟙 x) ≫ 𝟙 _ = _; simp)

end Prod

section OfCharts

variable {C : Type*} [Groupoid C]
  {ι : Type u₁} {G : ι → Type u₂} [∀ i, Group (G i)]
  {U : ι → Type u₃} [∀ i, MulAction (G i) (U i)]

/-- An overlap arrow between the `i`-th and `j`-th charts of a family
`F : ∀ i, ActionCategory (G i) (U i) ⥤ C`: a source point `src : U i`, a target point `tgt : U j`,
and a morphism in `C` between their chart images. -/
@[ext]
structure ChartOverlap (F : ∀ i, ActionCategory (G i) (U i) ⥤ C) (i j : ι) where
  /-- Source point in the `i`-th chart. -/
  src : U i
  /-- Target point in the `j`-th chart. -/
  tgt : U j
  /-- Morphism in `C` from the image of `src` to the image of `tgt`. -/
  hom : (F i).obj (ActionCategory.objEquiv (G i) (U i) src) ⟶
    (F j).obj (ActionCategory.objEquiv (G j) (U j) tgt)

/-- The action-category morphism from `x` to `g • x` labelled by `g`. -/
def actionHom {M X : Type*} [Monoid M] [MulAction M X] (m : M) (x : X) :
    ActionCategory.objEquiv M X x ⟶ ActionCategory.objEquiv M X (m • x) :=
  Functor.Elements.homMk m rfl

/-- `G j` acts on `ChartOverlap F i j` by translating `tgt` and postcomposing `hom` with the
image under `F j` of `actionHom g α.tgt`. -/
instance instSMulChartOverlap (F : ∀ i, ActionCategory (G i) (U i) ⥤ C) (i j : ι) :
    SMul (G j) (ChartOverlap F i j) where
  smul g α := ⟨α.src, g • α.tgt, α.hom ≫ (F j).map (actionHom g α.tgt)⟩

/-- `smul` on `ChartOverlap` preserves `src`. -/
@[simp]
theorem chartOverlap_smul_src (F : ∀ i, ActionCategory (G i) (U i) ⥤ C) {i j : ι}
    (g : G j) (α : ChartOverlap F i j) : (g • α).src = α.src := (rfl)

/-- `smul` on `ChartOverlap` translates `tgt` by `g`. -/
@[simp]
theorem chartOverlap_smul_tgt (F : ∀ i, ActionCategory (G i) (U i) ⥤ C) {i j : ι}
    (g : G j) (α : ChartOverlap F i j) : (g • α).tgt = g • α.tgt := (rfl)

/-- `smul` on `ChartOverlap` postcomposes `hom` with `(F j).map (actionHom g α.tgt)`. -/
@[simp]
theorem chartOverlap_smul_hom (F : ∀ i, ActionCategory (G i) (U i) ⥤ C) {i j : ι}
    (g : G j) (α : ChartOverlap F i j) :
    (g • α).hom = α.hom ≫ (F j).map (actionHom g α.tgt) := (rfl)

/-- Composing a morphism on the right with `eqToHom` yields a heterogeneously equal morphism. -/
theorem comp_eqToHom_heq {X Y Y' : C} (f : X ⟶ Y) (h : Y = Y') : f ≫ eqToHom h ≍ f := by
  cases h
  simp

/-- `MulAction` of `G j` on `ChartOverlap F i j`. -/
instance instMulActionChartOverlap (F : ∀ i, ActionCategory (G i) (U i) ⥤ C) (i j : ι) :
    MulAction (G j) (ChartOverlap F i j) where
  one_smul α := by
    obtain ⟨x, y, f⟩ := α
    have h1 : (1 : G j) • y = y := one_smul (G j) y
    refine ChartOverlap.ext rfl h1 ?_
    have heq : actionHom (1 : G j) y =
        eqToHom (congrArg (ActionCategory.objEquiv (G j) (U j)) h1.symm) :=
      Functor.Elements.hom_ext (ActionCategory.eqToHom_hom _).symm
    change (f ≫ (F j).map (actionHom (1 : G j) y)) ≍ f
    rw [heq, eqToHom_map]
    exact comp_eqToHom_heq f _
  mul_smul g₁ g₂ α := by
    obtain ⟨x, y, f⟩ := α
    have hm : (g₁ * g₂) • y = g₁ • g₂ • y := mul_smul g₁ g₂ y
    refine ChartOverlap.ext rfl hm ?_
    have hcomp : actionHom g₂ y ≫ actionHom g₁ (g₂ • y) =
        actionHom (g₁ * g₂) y ≫ eqToHom (congrArg (ActionCategory.objEquiv (G j) (U j)) hm) :=
      Functor.Elements.hom_ext (by simp [actionHom])
    change (f ≫ (F j).map (actionHom (g₁ * g₂) y)) ≍
      ((f ≫ (F j).map (actionHom g₂ y)) ≫ (F j).map (actionHom g₁ (g₂ • y)))
    rw [Category.assoc, ← (F j).map_comp, hcomp, (F j).map_comp, eqToHom_map, ← Category.assoc]
    exact (comp_eqToHom_heq _ _).symm

/-- **Induced retained-arrow chart atlas.** Any family of fully faithful action-groupoid charts
`F i : ActionCategory (G i) (U i) ⥤ C` into a groupoid `C` induces a `ChartAtlas` on
`ChartOverlap F`, retaining all ineffective isotropy labels. -/
def ofCharts (F : ∀ i, ActionCategory (G i) (U i) ⥤ C)
    [∀ i, (F i).Full] [∀ i, (F i).Faithful] : ChartAtlas G U (ChartOverlap F) where
  src α := α.src
  tgt α := α.tgt
  unit _ x := ⟨x, x, 𝟙 _⟩
  inv α := ⟨α.tgt, α.src, Groupoid.inv α.hom⟩
  comp {i j k} α β h := ⟨α.src, β.tgt,
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
    obtain ⟨e, he⟩ := (F j).map_surjective (Groupoid.inv f₁ ≫ f₂)
    have hey : e.hom • y₁ = y₂ := ActionCategory.hom_smul e
    refine ⟨e.hom, ?_, fun g hg ↦ ?_⟩
    · refine ChartOverlap.ext rfl hey ?_
      have he' : actionHom e.hom y₁ =
          e ≫ eqToHom (congrArg (ActionCategory.objEquiv (G j) (U j)) hey.symm) :=
        Functor.Elements.hom_ext (by simp [actionHom])
      change (f₁ ≫ (F j).map (actionHom e.hom y₁)) ≍ f₂
      rw [he', (F j).map_comp, eqToHom_map, ← Category.assoc, he, Groupoid.inv_eq_inv,
        IsIso.hom_inv_id_assoc]
      exact comp_eqToHom_heq f₂ _
    · have hg_tgt : g • y₁ = y₂ := congrArg ChartOverlap.tgt hg
      subst hg_tgt
      have hg_hom : f₁ ≫ (F j).map (actionHom g y₁) = f₂ :=
        eq_of_heq (ChartOverlap.ext_iff.mp hg).2.2
      have hmap : (F j).map (actionHom g y₁) = (F j).map e := by
        rw [he, ← hg_hom, Groupoid.inv_eq_inv, IsIso.inv_hom_id_assoc]
      exact congrArg Functor.Elements.Hom.hom ((F j).map_injective hmap)

/-- The canonical comparison functor `(ofCharts F).Obj ⥤ C` from the presenting groupoid of the
induced chart atlas back to `C`. -/
def toGroupoid (F : ∀ i, ActionCategory (G i) (U i) ⥤ C)
    [∀ i, (F i).Full] [∀ i, (F i).Faithful] : (ofCharts F).Obj ⥤ C where
  obj x := (F x.chart).obj (ActionCategory.objEquiv (G x.chart) (U x.chart) x.point)
  map {x y} f :=
    eqToHom (congrArg (fun u ↦ (F x.chart).obj (ActionCategory.objEquiv (G x.chart) (U x.chart) u))
      f.src_arrow.symm) ≫
      f.arrow.hom ≫
      eqToHom (congrArg
        (fun u ↦ (F y.chart).obj (ActionCategory.objEquiv (G y.chart) (U y.chart) u)) f.tgt_arrow)
  map_id x := by
    change eqToHom rfl ≫ (𝟙 _ : _ ⟶ _) ≫ eqToHom rfl = 𝟙 _
    simp
  map_comp {x y z} f g := by
    obtain ⟨⟨sx₁, sy₁, m₁⟩, hs₁, ht₁⟩ := f
    obtain ⟨⟨sx₂, sy₂, m₂⟩, hs₂, ht₂⟩ := g
    dsimp only [ofCharts] at hs₁ ht₁ hs₂ ht₂
    cases hs₁
    cases ht₁
    cases hs₂
    cases ht₂
    change eqToHom rfl ≫ (m₁ ≫ eqToHom rfl ≫ m₂) ≫ eqToHom rfl =
      (eqToHom rfl ≫ m₁ ≫ eqToHom rfl) ≫ (eqToHom rfl ≫ m₂ ≫ eqToHom rfl)
    simp

/-- `toGroupoid F` evaluates on `⟨i, x⟩` as `(F i).obj (objEquiv (G i) (U i) x)`. -/
@[simp]
theorem toGroupoid_obj (F : ∀ i, ActionCategory (G i) (U i) ⥤ C)
    [∀ i, (F i).Full] [∀ i, (F i).Faithful] (x : (ofCharts F).Obj) :
    (toGroupoid F).obj x =
      (F x.chart).obj (ActionCategory.objEquiv (G x.chart) (U x.chart) x.point) := (rfl)

/-- Action of `toGroupoid F` on morphisms. -/
@[simp]
theorem toGroupoid_map (F : ∀ i, ActionCategory (G i) (U i) ⥤ C)
    [∀ i, (F i).Full] [∀ i, (F i).Faithful] {x y : (ofCharts F).Obj} (f : x ⟶ y) :
    (toGroupoid F).map f =
      eqToHom (congrArg
        (fun u ↦ (F x.chart).obj (ActionCategory.objEquiv (G x.chart) (U x.chart) u))
        f.src_arrow.symm) ≫ f.arrow.hom ≫
        eqToHom (congrArg
          (fun u ↦ (F y.chart).obj (ActionCategory.objEquiv (G y.chart) (U y.chart) u))
          f.tgt_arrow) := (rfl)

/-- `toGroupoid F` is faithful. -/
instance instFaithfulToGroupoid (F : ∀ i, ActionCategory (G i) (U i) ⥤ C)
    [∀ i, (F i).Full] [∀ i, (F i).Faithful] : (toGroupoid F).Faithful where
  map_injective {x y} f₁ f₂ h := by
    obtain ⟨⟨sx₁, sy₁, m₁⟩, hs₁, ht₁⟩ := f₁
    obtain ⟨⟨sx₂, sy₂, m₂⟩, hs₂, ht₂⟩ := f₂
    dsimp only [ofCharts] at hs₁ ht₁ hs₂ ht₂
    cases hs₁
    cases ht₁
    cases hs₂
    cases ht₂
    refine Obj.Hom.ext (ChartOverlap.ext rfl rfl (heq_of_eq ?_))
    change eqToHom rfl ≫ m₁ ≫ eqToHom rfl = eqToHom rfl ≫ m₂ ≫ eqToHom rfl at h
    simpa using h

/-- `toGroupoid F` is full. -/
instance instFullToGroupoid (F : ∀ i, ActionCategory (G i) (U i) ⥤ C)
    [∀ i, (F i).Full] [∀ i, (F i).Faithful] : (toGroupoid F).Full where
  map_surjective {x y} m :=
    ⟨⟨⟨x.point, y.point, m⟩, rfl, rfl⟩, by
      dsimp only [toGroupoid] at m ⊢
      change eqToHom rfl ≫ m ≫ eqToHom rfl = m
      simp⟩

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

/-- Conjugating a morphism on both sides by `eqToHom`s yields a heterogeneously equal morphism. -/
theorem eqToHom_comp_eqToHom_heq {X X' Y Y' : C} (hX : X = X') (hY : Y = Y') (g : X' ⟶ Y') :
    eqToHom hX ≫ g ≫ eqToHom hY.symm ≍ g := by
  cases hX
  cases hY
  simp

/-- Restricting `toGroupoid F` along the `i`-th chart inclusion recovers `F i`. -/
@[simp]
theorem chartFunctor_comp_toGroupoid (F : ∀ i, ActionCategory (G i) (U i) ⥤ C)
    [∀ i, (F i).Full] [∀ i, (F i).Faithful] (i : ι) :
    (ofCharts F).chartFunctor i ⋙ toGroupoid F = F i := by
  refine CategoryTheory.Functor.hext (fun a ↦ congrArg (F i).obj (ActionCategory.back_coe a))
    fun {a b} f ↦ ?_
  have ea : ActionCategory.objEquiv (G i) (U i) a.back = a := ActionCategory.back_coe a
  have eb : ActionCategory.objEquiv (G i) (U i) (f.hom • a.back) = b :=
    (congrArg (ActionCategory.objEquiv (G i) (U i)) (ActionCategory.hom_smul f)).trans
      (ActionCategory.back_coe b)
  have hact : actionHom f.hom a.back = eqToHom ea ≫ f ≫ eqToHom eb.symm := by
    apply Functor.Elements.hom_ext
    rw [ActionCategory.comp_hom, ActionCategory.comp_hom, ActionCategory.eqToHom_hom,
      ActionCategory.eqToHom_hom, one_mul, mul_one]
    rfl
  let htgt : f.hom • a.back = b.back := (((ofCharts F).chartFunctor i).map f).tgt_arrow
  let m : (F i).obj (ActionCategory.objEquiv (G i) (U i) a.back) ⟶
      (F i).obj (ActionCategory.objEquiv (G i) (U i) b.back) :=
    eqToHom rfl ≫ (𝟙 _ ≫ (F i).map (actionHom f.hom a.back)) ≫
      eqToHom (congrArg (fun u ↦ (F i).obj (ActionCategory.objEquiv (G i) (U i) u)) htgt)
  change m ≍ (F i).map f
  have hm : m = eqToHom (congrArg (F i).obj ea) ≫ (F i).map f ≫
      eqToHom (congrArg (F i).obj (ActionCategory.back_coe b)).symm := by
    simp [m, hact, eqToHom_map]
    rfl
  rw [hm]
  exact eqToHom_comp_eqToHom_heq (congrArg (F i).obj ea)
    (congrArg (F i).obj (ActionCategory.back_coe b)) ((F i).map f)

section RoundTrip

variable {R : ι → ι → Type u₄} [∀ i j, MulAction (G j) (R i j)] (𝓐 : ChartAtlas G U R)

/-- Heterogeneous extensionality for morphisms in `𝓐.Obj` sharing chart indices. -/
theorem objHom_hext {i j : ι} {x₁ x₂ : U i} {y₁ y₂ : U j} (hx : x₁ = x₂) (hy : y₁ = y₂)
    (f₁ : (⟨i, x₁⟩ : 𝓐.Obj) ⟶ ⟨j, y₁⟩) (f₂ : (⟨i, x₂⟩ : 𝓐.Obj) ⟶ ⟨j, y₂⟩)
    (h : f₁.arrow = f₂.arrow) : f₁ ≍ f₂ := by
  cases hx
  cases hy
  exact heq_of_eq (Obj.Hom.ext h)

/-- Forward atlas morphism from `𝓐` to `ofCharts 𝓐.chartFunctor`, sending each overlap arrow to the
morphism it defines in `𝓐.Obj`. -/
def toOfCharts : 𝓐.Hom (ofCharts 𝓐.chartFunctor) where
  index i := i
  groupHom i := MonoidHom.id (G i)
  obj _ x := x
  map {i j} α := ⟨𝓐.src α, 𝓐.tgt α,
    ⟨α, (ActionCategory.coe_back (M := G i) (𝓐.src α)).symm,
      (ActionCategory.coe_back (M := G j) (𝓐.tgt α)).symm⟩⟩
  src_map _ := rfl
  tgt_map _ := rfl
  map_unit i x := ChartOverlap.ext (𝓐.src_unit i x) (𝓐.tgt_unit i x) <|
    𝓐.objHom_hext
      (congrArg (fun s ↦ (ActionCategory.objEquiv (G i) (U i) s).back) (𝓐.src_unit i x))
      (congrArg (fun s ↦ (ActionCategory.objEquiv (G i) (U i) s).back) (𝓐.tgt_unit i x)) _ _ rfl
  map_comp {i j k} α β h := ChartOverlap.ext (𝓐.src_comp α β h) (𝓐.tgt_comp α β h) <|
    𝓐.objHom_hext
      (congrArg (fun s ↦ (ActionCategory.objEquiv (G i) (U i) s).back) (𝓐.src_comp α β h))
      (congrArg (fun s ↦ (ActionCategory.objEquiv (G k) (U k) s).back) (𝓐.tgt_comp α β h)) _ _ <|
      have hsrc : 𝓐.tgt (𝓐.unit j (ActionCategory.objEquiv (G j) (U j) (𝓐.tgt α)).back) = 𝓐.src β :=
        (𝓐.tgt_unit j _).trans ((ActionCategory.coe_back (M := G j) (𝓐.tgt α)).trans h)
      (𝓐.comp_congr rfl
        ((𝓐.comp_congr (𝓐.eqToHom_mk_arrow _) rfl _ hsrc).trans (𝓐.unit_comp _ β hsrc)).symm _ _)
  map_smul {i j} g α := ChartOverlap.ext (𝓐.src_smul g α) (𝓐.tgt_smul g α) <|
    𝓐.objHom_hext
      (congrArg (fun s ↦ (ActionCategory.objEquiv (G i) (U i) s).back) (𝓐.src_smul g α))
      (congrArg (fun s ↦ (ActionCategory.objEquiv (G j) (U j) s).back) (𝓐.tgt_smul g α)) _ _ <|
      (𝓐.comp_smul_unit_tgt α g
        ((𝓐.src_unit j _).symm.trans (𝓐.src_smul g _).symm)).symm.trans <|
        𝓐.comp_congr rfl
          (congrArg (g • 𝓐.unit j ·) (ActionCategory.coe_back (M := G j) (𝓐.tgt α)).symm) _ _

/-- Inverse atlas morphism from `ofCharts 𝓐.chartFunctor` back to `𝓐`, extracting the underlying
overlap arrow of each morphism in `𝓐.Obj`. -/
def fromOfCharts : (ofCharts 𝓐.chartFunctor).Hom 𝓐 where
  index i := i
  groupHom i := MonoidHom.id (G i)
  obj _ x := x
  map α := α.hom.arrow
  src_map {i _} α := (α.hom.src_arrow).trans (ActionCategory.coe_back (M := G i) α.src)
  tgt_map {_ j} α := (α.hom.tgt_arrow).trans (ActionCategory.coe_back (M := G j) α.tgt)
  map_unit i x := congrArg (𝓐.unit i) (ActionCategory.coe_back (M := G i) x)
  map_comp {_ j _} α β h :=
    have hsrc : 𝓐.tgt (𝓐.unit j (ActionCategory.objEquiv (G j) (U j) α.tgt).back) =
        𝓐.src β.hom.arrow :=
      (𝓐.tgt_unit j _).trans
        ((congrArg (fun s ↦ (ActionCategory.objEquiv (G j) (U j) s).back) h).trans
          β.hom.src_arrow.symm)
    𝓐.comp_congr rfl
      ((𝓐.comp_congr (𝓐.eqToHom_mk_arrow _) rfl _ hsrc).trans
        (𝓐.unit_comp _ β.hom.arrow hsrc)) _ _
  map_smul {_ j} g α :=
    have htgt : 𝓐.tgt α.hom.arrow = 𝓐.src (g • 𝓐.unit j (𝓐.tgt α.hom.arrow)) :=
      (𝓐.src_unit j _).symm.trans (𝓐.src_smul g _).symm
    (𝓐.comp_congr rfl (congrArg (g • 𝓐.unit j ·) α.hom.tgt_arrow.symm) _ htgt).trans
      (𝓐.comp_smul_unit_tgt α.hom.arrow g htgt)

/-- `fromOfCharts` is a strict left inverse to `toOfCharts`. -/
@[simp]
theorem fromOfCharts_comp_toOfCharts :
    𝓐.fromOfCharts.comp 𝓐.toOfCharts = Hom.id 𝓐 := by
  ext <;> rfl

/-- `toOfCharts` is a strict right inverse to `fromOfCharts`. -/
@[simp]
theorem toOfCharts_comp_fromOfCharts :
    𝓐.toOfCharts.comp 𝓐.fromOfCharts = Hom.id (ofCharts 𝓐.chartFunctor) := by
  ext
  · rfl
  · rfl
  · rfl
  · rename_i i j α
    have hs' : 𝓐.src α.hom.arrow = α.src :=
      α.hom.src_arrow.trans (ActionCategory.coe_back (M := G i) α.src)
    have ht' : 𝓐.tgt α.hom.arrow = α.tgt :=
      α.hom.tgt_arrow.trans (ActionCategory.coe_back (M := G j) α.tgt)
    exact heq_of_eq <| ChartOverlap.ext hs' ht' <|
      𝓐.objHom_hext
        (congrArg (fun s ↦ (ActionCategory.objEquiv (G i) (U i) s).back) hs')
        (congrArg (fun s ↦ (ActionCategory.objEquiv (G j) (U j) s).back) ht') _ _ rfl

end RoundTrip

section SumElim

variable {κ : Type v₁} {G' : κ → Type u₂} [∀ k, Group (G' k)]
  {U' : κ → Type u₃} [∀ k, MulAction (G' k) (U' k)]
  (F₁ : ∀ i, ActionCategory (G i) (U i) ⥤ C) [∀ i, (F₁ i).Full] [∀ i, (F₁ i).Faithful]
  (F₂ : ∀ k, ActionCategory (G' k) (U' k) ⥤ C) [∀ k, (F₂ k).Full] [∀ k, (F₂ k).Faithful]

/-- Disjoint-sum group family over `ι ⊕ κ`. -/
def SumGroup (G : ι → Type u₂) (G' : κ → Type u₂) : ι ⊕ κ → Type u₂
  | .inl i => G i
  | .inr k => G' k

/-- Group structure on `SumGroup G G' s`. -/
instance instGroupSumGroup : ∀ s : ι ⊕ κ, Group (SumGroup G G' s)
  | .inl i => inferInstanceAs (Group (G i))
  | .inr k => inferInstanceAs (Group (G' k))

/-- Disjoint-sum chart-domain family over `ι ⊕ κ`. -/
def SumDomain (U : ι → Type u₃) (U' : κ → Type u₃) : ι ⊕ κ → Type u₃
  | .inl i => U i
  | .inr k => U' k

/-- Group action of `SumGroup G G' s` on `SumDomain U U' s`. -/
instance instMulActionSumDomain :
    ∀ s : ι ⊕ κ, MulAction (SumGroup G G' s) (SumDomain U U' s)
  | .inl i => inferInstanceAs (MulAction (G i) (U i))
  | .inr k => inferInstanceAs (MulAction (G' k) (U' k))

/-- Combining two families of fully faithful action charts into `C` over `ι ⊕ κ`. -/
def sumCharts : ∀ s : ι ⊕ κ, ActionCategory (SumGroup G G' s) (SumDomain U U' s) ⥤ C
  | .inl i => F₁ i
  | .inr k => F₂ k

/-- Each chart of `sumCharts F₁ F₂` is full. -/
instance instFullSumCharts : ∀ s : ι ⊕ κ, (sumCharts F₁ F₂ s).Full
  | .inl i => inferInstanceAs (F₁ i).Full
  | .inr k => inferInstanceAs (F₂ k).Full

/-- Each chart of `sumCharts F₁ F₂` is faithful. -/
instance instFaithfulSumCharts : ∀ s : ι ⊕ κ, (sumCharts F₁ F₂ s).Faithful
  | .inl i => inferInstanceAs (F₁ i).Faithful
  | .inr k => inferInstanceAs (F₂ k).Faithful

/-- Left inclusion of `ofCharts F₁` into the combined chart atlas `ofCharts (sumCharts F₁ F₂)`. -/
def sumInlHom : (ofCharts F₁).Hom (ofCharts (sumCharts F₁ F₂)) where
  index := Sum.inl
  groupHom i := MonoidHom.id (G i)
  obj _ := id
  map α := ⟨α.src, α.tgt, α.hom⟩
  src_map _ := rfl
  tgt_map _ := rfl
  map_unit _ _ := rfl
  map_comp _ _ _ := rfl
  map_smul _ _ := rfl

/-- Right inclusion of `ofCharts F₂` into the combined chart atlas `ofCharts (sumCharts F₁ F₂)`. -/
def sumInrHom : (ofCharts F₂).Hom (ofCharts (sumCharts F₁ F₂)) where
  index := Sum.inr
  groupHom k := MonoidHom.id (G' k)
  obj _ := id
  map α := ⟨α.src, α.tgt, α.hom⟩
  src_map _ := rfl
  tgt_map _ := rfl
  map_unit _ _ := rfl
  map_comp _ _ _ := rfl
  map_smul _ _ := rfl

/-- The left chart-family inclusion is faithful on presenting groupoids. -/
instance instFaithfulSumInlHom : (sumInlHom F₁ F₂).toFunctor.Faithful :=
  (Hom.faithful_toFunctor_iff _).mpr fun α₁ α₂ hs ht hm ↦ by
    obtain ⟨_, _, _⟩ := α₁
    obtain ⟨_, _, _⟩ := α₂
    dsimp only [ofCharts] at hs ht
    cases hs
    cases ht
    exact ChartOverlap.ext rfl rfl (ChartOverlap.ext_iff.mp hm).2.2

/-- The left chart-family inclusion is full on presenting groupoids. -/
instance instFullSumInlHom : (sumInlHom F₁ F₂).toFunctor.Full :=
  (Hom.full_toFunctor_iff _).mpr fun x y β hs ht ↦ by
    obtain ⟨_, _, hβ⟩ := β
    dsimp only [ofCharts, sumInlHom] at hs ht
    cases hs
    cases ht
    exact ⟨⟨x, y, hβ⟩, rfl, rfl, rfl⟩

/-- The right chart-family inclusion is faithful on presenting groupoids. -/
instance instFaithfulSumInrHom : (sumInrHom F₁ F₂).toFunctor.Faithful :=
  (Hom.faithful_toFunctor_iff _).mpr fun α₁ α₂ hs ht hm ↦ by
    obtain ⟨_, _, _⟩ := α₁
    obtain ⟨_, _, _⟩ := α₂
    dsimp only [ofCharts] at hs ht
    cases hs
    cases ht
    exact ChartOverlap.ext rfl rfl (ChartOverlap.ext_iff.mp hm).2.2

/-- The right chart-family inclusion is full on presenting groupoids. -/
instance instFullSumInrHom : (sumInrHom F₁ F₂).toFunctor.Full :=
  (Hom.full_toFunctor_iff _).mpr fun x y β hs ht ↦ by
    obtain ⟨_, _, hβ⟩ := β
    dsimp only [ofCharts, sumInrHom] at hs ht
    cases hs
    cases ht
    exact ⟨⟨x, y, hβ⟩, rfl, rfl, rfl⟩

/-- `sumInlHom` commutes strictly with `toGroupoid`. -/
@[simp]
theorem sumInlHom_toFunctor_comp_toGroupoid :
    (sumInlHom F₁ F₂).toFunctor ⋙ toGroupoid (sumCharts F₁ F₂) = toGroupoid F₁ := (rfl)

/-- `sumInrHom` commutes strictly with `toGroupoid`. -/
@[simp]
theorem sumInrHom_toFunctor_comp_toGroupoid :
    (sumInrHom F₁ F₂).toFunctor ⋙ toGroupoid (sumCharts F₁ F₂) = toGroupoid F₂ := (rfl)

end SumElim

end OfCharts

end TauCeti.ChartAtlas
