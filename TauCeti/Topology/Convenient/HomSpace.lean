/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
public import Mathlib.Topology.Category.CompactlyGenerated
public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.Topology.Convenient.HomSpace
public import TauCeti.Topology.Convenient.CompactlyGenerated

/-!
# Exponential law and colimit preservation for convenient categories of spaces

Given a generating family of topological spaces `X : ι → Type u`, Mathlib introduces the category
`GeneratedByTopCat X` of `X`-generated spaces and the equivalent category
`ContinuousGeneratedByCat X` of all topological spaces with `X`-continuous maps
(`ContinuousMapGeneratedBy X Y Z`), following Escardó, Lawson and Simpson. It also equips
`ContinuousMapGeneratedBy X Y Z` with a natural function-space topology and establishes the
currying bijection `Topology.ContinuousMapGeneratedBy.curryEquiv` whenever each generator `X i` is
locally compact and each product `X i × X j` is `X`-generated.

Here we promote this currying bijection to an adjunction and deduce that binary products preserve
colimits of all sizes in `GeneratedByTopCat X` and in `CompactlyGenerated`:

* Any colimit in `TopCat` of `X`-generated spaces is `X`-generated
  (`TauCeti.TopCat.isGeneratedBy_of_isColimit`).
* Binary products in `ContinuousGeneratedByCat X` are given directly by the ordinary Cartesian
  product `Y × Z` of topological spaces (`ContinuousGeneratedByCat.isLimitProdBinaryFan`), for an
  arbitrary generating family `X`.
* Under `[∀ i, LocallyCompactSpace (X i)]` and `[∀ i j, IsGeneratedBy X (X i × X j)]`, the
  product functor `Z ↦ Y × Z` on `ContinuousGeneratedByCat X` is left adjoint to the internal
  mapping-space functor `Z ↦ ContinuousMapGeneratedBy X Y Z`
  (`ContinuousGeneratedByCat.prodFunctorAdjunction`), so `Limits.prod.functor.obj Y` preserves
  colimits of every size in `ContinuousGeneratedByCat X`.
* Transporting colimit preservation along binary-product-preserving colimit-reflecting functors via
  `CategoryTheory.Functor.preservesColimitsOfSize_prodFunctor`, `Limits.prod.functor.obj Y`
  preserves colimits of every size in `GeneratedByTopCat X`.
* Identifying `CompactlyGenerated.{u, v}` with
  `GeneratedByTopCat.{v} (fun K : CompHaus.{u} ↦ K)` via
  `CompactlyGenerated.generatedByEquivalence`, every compact Hausdorff generator is locally
  compact and products of two compact Hausdorff spaces are compact Hausdorff (hence
  `u`-compactly generated), so `Limits.prod.functor.obj Y` preserves colimits of every size in
  `CompactlyGenerated.{u, v}` whenever binary products exist there.

## References

* Martín Escardó, Jimmie Lawson and Alex Simpson, *Comparing Cartesian closed categories of
  (core) compactly generated spaces*, Topology Appl. 143 (2004), 105–145.
* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*, Arch. Math.
  (Basel) 22 (1971), 545–555.
-/

public section

universe w w' v v' v'' t u

open CategoryTheory Limits Topology

namespace CategoryTheory.Functor

/-- If `E : C ⥤ D` preserves binary products and preserves and reflects colimits of size `{w', w}`,
and `Limits.prod.functor.obj (E.obj A)` preserves colimits of size `{w', w}`, then
`Limits.prod.functor.obj A` also preserves colimits of size `{w', w}`. -/
theorem preservesColimitsOfSize_prodFunctor {C : Type*} [Category* C] {D : Type*} [Category* D]
    [HasBinaryProducts C] [HasBinaryProducts D] (E : C ⥤ D)
    [PreservesLimitsOfShape (Discrete WalkingPair) E] [PreservesColimitsOfSize.{w', w} E]
    [ReflectsColimitsOfSize.{w', w} E] (A : C)
    [PreservesColimitsOfSize.{w', w} (prod.functor.obj (E.obj A))] :
    PreservesColimitsOfSize.{w', w} (prod.functor.obj A) := by
  have : PreservesColimitsOfSize.{w', w} (prod.functor.obj A ⋙ E) :=
    preservesColimits_of_natIso (prodComparisonNatIso E A).symm
  exact preservesColimits_of_reflects_of_preserves (prod.functor.obj A) E

end CategoryTheory.Functor

namespace TauCeti.TopCat

/-- A colimit of `X`-generated spaces in `TopCat` is `X`-generated. -/
theorem isGeneratedBy_of_isColimit {ι : Type t} {X : ι → Type u}
    [∀ i, TopologicalSpace (X i)] {J : Type w} [Category.{w'} J] {F : J ⥤ TopCat.{v}}
    {c : Cocone F} [∀ j, IsGeneratedBy X (F.obj j)] (hc : IsColimit c) :
    IsGeneratedBy X c.pt :=
  IsGeneratedBy.iff_le_generatedBy.2 fun U hU ↦ (TopCat.isOpen_iff_of_isColimit _ hc U).2 fun j ↦
    (IsGeneratedBy.isOpen_iff X).2 fun _ f ↦
      WithGeneratedByTopology.isOpen_iff.1 hU ((c.ι.app j).hom.comp f)

end TauCeti.TopCat

namespace Topology

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
  {T : Type v} [TopologicalSpace T] {Y : Type v'} [TopologicalSpace Y]
  {Z : Type v''} [TopologicalSpace Z]

/-- Pairing two `X`-continuous maps into a topological product gives an `X`-continuous map. -/
theorem ContinuousGeneratedBy.prodMk {f : T → Y} {g : T → Z}
    (hf : ContinuousGeneratedBy X f) (hg : ContinuousGeneratedBy X g) :
    ContinuousGeneratedBy X (fun t ↦ (f t, g t)) :=
  fun _ φ ↦ (hf φ).prodMk (hg φ)

namespace ContinuousMapGeneratedBy

/-- The first projection `Y × Z → Y` as an `X`-continuous map. -/
@[expose, simps]
def fst : ContinuousMapGeneratedBy X (Y × Z) Y where
  toFun := Prod.fst
  prop := continuous_fst.continuousGeneratedBy

/-- The second projection `Y × Z → Z` as an `X`-continuous map. -/
@[expose, simps]
def snd : ContinuousMapGeneratedBy X (Y × Z) Z where
  toFun := Prod.snd
  prop := continuous_snd.continuousGeneratedBy

/-- The pairing of two `X`-continuous maps `T → Y` and `T → Z` into `Y × Z`. -/
@[expose, simps]
def prodMk (f : ContinuousMapGeneratedBy X T Y) (g : ContinuousMapGeneratedBy X T Z) :
    ContinuousMapGeneratedBy X T (Y × Z) where
  toFun t := (f t, g t)
  prop := f.prop.prodMk g.prop

/-- Cartesian product of two `X`-continuous maps `T → Y` and `T' → Z`. -/
@[expose, simps!]
def prodMap (f : ContinuousMapGeneratedBy X T Y)
    {T' : Type*} [TopologicalSpace T'] (g : ContinuousMapGeneratedBy X T' Z) :
    ContinuousMapGeneratedBy X (T × T') (Y × Z) :=
  prodMk (f.comp fst) (g.comp snd)

end ContinuousMapGeneratedBy

end Topology

namespace ContinuousGeneratedByCat

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]

@[ext]
theorem Hom.ext {Y Z : ContinuousGeneratedByCat.{v} X} {f g : Y ⟶ Z} (h : ∀ y, f y = g y) :
    f = g := by
  cases f; cases g; congr; ext y; exact h y

/-- In `ContinuousGeneratedByCat X`, the Cartesian product `Y × Z` with its usual product topology
forms a binary fan over `Y` and `Z`. -/
@[expose, simps! pt]
def prodBinaryFan (Y Z : ContinuousGeneratedByCat.{v} X) : BinaryFan Y Z :=
  BinaryFan.mk (P := of (X := X) (Y × Z)) ⟨.fst⟩ ⟨.snd⟩

@[simp]
theorem prodBinaryFan_fst_apply (Y Z : ContinuousGeneratedByCat.{v} X) (p : Y × Z) :
    (prodBinaryFan Y Z).fst p = p.1 :=
  (rfl)

@[simp]
theorem prodBinaryFan_snd_apply (Y Z : ContinuousGeneratedByCat.{v} X) (p : Y × Z) :
    (prodBinaryFan Y Z).snd p = p.2 :=
  (rfl)

/-- The binary fan `ContinuousGeneratedByCat.prodBinaryFan Y Z` is a limit cone: an `X`-continuous
map into `Y × Z` is simply a pair of `X`-continuous maps into `Y` and `Z`. -/
@[expose]
def isLimitProdBinaryFan (Y Z : ContinuousGeneratedByCat.{v} X) :
    IsLimit (prodBinaryFan Y Z) :=
  BinaryFan.IsLimit.mk _ (fun f g ↦ ⟨f.hom.prodMk g.hom⟩) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    fun f g m h₁ h₂ ↦ by
      ext t
      exact Prod.ext (DFunLike.congr_fun (congrArg Hom.hom h₁) t)
        (DFunLike.congr_fun (congrArg Hom.hom h₂) t)

instance instHasBinaryProduct (Y Z : ContinuousGeneratedByCat.{v} X) : HasBinaryProduct Y Z :=
  HasLimit.mk ⟨prodBinaryFan Y Z, isLimitProdBinaryFan Y Z⟩

instance instHasBinaryProducts : HasBinaryProducts (ContinuousGeneratedByCat.{v} X) :=
  hasBinaryProducts_of_hasLimit_pair _

/-- Left Cartesian product with `Y` as an explicit endofunctor on `ContinuousGeneratedByCat X`. -/
@[expose, simps! obj map_hom_apply]
def prodFunctor (Y : ContinuousGeneratedByCat.{v} X) :
    ContinuousGeneratedByCat.{v} X ⥤ ContinuousGeneratedByCat.{v} X where
  obj Z := of (X := X) (Y × Z)
  map f := ⟨ContinuousMapGeneratedBy.id.prodMap f.hom⟩

/-- The first projection `of (Y × Z) ⟶ Y` in `ContinuousGeneratedByCat X`. -/
abbrev prodFst (Y Z : ContinuousGeneratedByCat.{v} X) : of (X := X) (Y × Z) ⟶ Y := ⟨.fst⟩

/-- The second projection `of (Y × Z) ⟶ Z` in `ContinuousGeneratedByCat X`. -/
abbrev prodSnd (Y Z : ContinuousGeneratedByCat.{v} X) : of (X := X) (Y × Z) ⟶ Z := ⟨.snd⟩

/-- The canonical isomorphism `of (Y × Z) ≅ Y ⨯ Z` in `ContinuousGeneratedByCat X`. -/
@[expose, simps]
noncomputable def prodObjIso (Y Z : ContinuousGeneratedByCat.{v} X) :
    of (X := X) (Y × Z) ≅ Y ⨯ Z where
  hom := prod.lift (prodFst Y Z) (prodSnd Y Z)
  inv := ⟨(prod.fst : Y ⨯ Z ⟶ Y).hom.prodMk (prod.snd : Y ⨯ Z ⟶ Z).hom⟩
  hom_inv_id := by
    apply BinaryFan.IsLimit.hom_ext (isLimitProdBinaryFan Y Z)
    · -- Postcomposing the paired projections with the first coordinate recovers `prod.fst`.
      dsimp only [prodBinaryFan, BinaryFan.mk_pt, BinaryFan.mk_fst]
      rw [Category.assoc, show (⟨(prod.fst : Y ⨯ Z ⟶ Y).hom.prodMk (prod.snd : Y ⨯ Z ⟶ Z).hom⟩ :
          Y ⨯ Z ⟶ of (X := X) (Y × Z)) ≫ prodFst Y Z = prod.fst from rfl,
        prod.lift_fst, Category.id_comp]
    · -- Postcomposing the paired projections with the second coordinate recovers `prod.snd`.
      dsimp only [prodBinaryFan, BinaryFan.mk_pt, BinaryFan.mk_snd]
      rw [Category.assoc, show (⟨(prod.fst : Y ⨯ Z ⟶ Y).hom.prodMk (prod.snd : Y ⨯ Z ⟶ Z).hom⟩ :
          Y ⨯ Z ⟶ of (X := X) (Y × Z)) ≫ prodSnd Y Z = prod.snd from rfl,
        prod.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply prod.hom_ext <;> simp <;> rfl

/-- The explicit Cartesian product functor `prodFunctor Y` is naturally isomorphic to the
categorical binary product functor `Limits.prod.functor.obj Y`. -/
@[expose, simps!]
noncomputable def prodFunctorIso (Y : ContinuousGeneratedByCat.{v} X) :
    prodFunctor Y ≅ prod.functor.obj Y :=
  NatIso.ofComponents (fun Z ↦ prodObjIso Y Z) fun {Z₁ Z₂} f ↦ by
    apply prod.hom_ext
    · dsimp only [prodFunctor, prod.functor_obj_obj, prodObjIso]
      rw [prod.functor_obj_map, Category.assoc, prod.lift_fst, Category.assoc, prod.map_fst,
        Category.comp_id, prod.lift_fst]
      rfl
    · dsimp only [prodFunctor, prod.functor_obj_obj, prodObjIso]
      rw [prod.functor_obj_map, Category.assoc, prod.lift_snd, Category.assoc, prod.map_snd,
        prod.lift_snd_assoc]
      rfl

section Exponential

variable [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]

/-- The internal mapping-space functor `Z ↦ ContinuousMapGeneratedBy X Y Z` on
`ContinuousGeneratedByCat X`, acting on morphisms by postcomposition. -/
@[expose, simps! obj map_hom_apply]
def mappingSpace (Y : ContinuousGeneratedByCat.{v} X) :
    ContinuousGeneratedByCat.{v} X ⥤ ContinuousGeneratedByCat.{v} X where
  obj Z := of (X := X) (ContinuousMapGeneratedBy X Y Z)
  map f := ⟨f.hom.postcomp⟩

/-- Currying in `ContinuousGeneratedByCat X` identifies morphisms `(prodFunctor Y).obj Z ⟶ T` with
morphisms `Z ⟶ of (ContinuousMapGeneratedBy X Y T)`. -/
@[expose]
def curryEquiv (Y Z T : ContinuousGeneratedByCat.{v} X) :
    ((prodFunctor Y).obj Z ⟶ T) ≃ (Z ⟶ of (X := X) (ContinuousMapGeneratedBy X Y T)) where
  toFun f := ⟨ContinuousMapGeneratedBy.curryEquiv f.hom⟩
  invFun g := ⟨ContinuousMapGeneratedBy.curryEquiv.symm g.hom⟩
  left_inv f := congrArg Hom.mk (ContinuousMapGeneratedBy.curryEquiv.symm_apply_apply f.hom)
  right_inv g := congrArg Hom.mk (ContinuousMapGeneratedBy.curryEquiv.apply_symm_apply g.hom)

@[simp]
theorem curryEquiv_apply_hom_apply_apply (Y Z T : ContinuousGeneratedByCat.{v} X)
    (f : (prodFunctor Y).obj Z ⟶ T) (z : Z) (y : Y) :
    (curryEquiv Y Z T f).hom z y = f.hom (y, z) :=
  (rfl)

@[simp]
theorem curryEquiv_symm_apply_hom_apply (Y Z T : ContinuousGeneratedByCat.{v} X)
    (g : Z ⟶ of (X := X) (ContinuousMapGeneratedBy X Y T)) (y : Y) (z : Z) :
    ((curryEquiv Y Z T).symm g).hom (y, z) = g.hom z y :=
  (rfl)

/-- Under local compactness of the generators `X i` and `X`-generation of their pairwise products
`X i × X j`, left Cartesian product with `Y` on `ContinuousGeneratedByCat X` is left adjoint to
`mappingSpace Y`. -/
@[expose]
def prodFunctorAdjunction (Y : ContinuousGeneratedByCat.{v} X) :
    prodFunctor Y ⊣ mappingSpace Y :=
  Adjunction.mkOfHomEquiv
    { homEquiv := curryEquiv Y
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := rfl }

/-- Left product with any object in `ContinuousGeneratedByCat X` preserves colimits of every size
when the generators are locally compact and closed under binary products as `X`-generated
spaces. -/
noncomputable instance instPreservesColimitsOfSizeProdFunctor
    (Y : ContinuousGeneratedByCat.{v} X) :
    PreservesColimitsOfSize.{w', w} (prod.functor.obj Y) :=
  have : PreservesColimitsOfSize.{w', w} (prodFunctor Y) :=
    (prodFunctorAdjunction Y).leftAdjoint_preservesColimits
  preservesColimits_of_natIso (prodFunctorIso Y)

end Exponential

end ContinuousGeneratedByCat

namespace GeneratedByTopCat

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]

/-- When the generators `X i` are locally compact and their pairwise products `X i × X j` are
`X`-generated, left binary product with any `Y : GeneratedByTopCat X` preserves colimits of all
sizes. -/
noncomputable instance instPreservesColimitsOfSizeProdFunctor
    [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]
    (Y : GeneratedByTopCat.{v} X) :
    PreservesColimitsOfSize.{w', w} (prod.functor.obj Y) :=
  ContinuousGeneratedByCat.fromGeneratedByTopCat.preservesColimitsOfSize_prodFunctor Y

end GeneratedByTopCat

namespace CompactlyGenerated

/-- The functor sending a `u`-compactly generated space in `CompactlyGenerated.{u, v}` to the same
space viewed as an object of `GeneratedByTopCat.{v} (fun K : CompHaus.{u} ↦ K)`. -/
@[expose, simps! obj]
def toGeneratedByTopCat :
    CompactlyGenerated.{u, v} ⥤ GeneratedByTopCat.{v} (fun K : CompHaus.{u} ↦ K) :=
  ObjectProperty.lift _ compactlyGeneratedToTop.{u, v} fun Y ↦
    (Topology.isGeneratedBy_compHaus_iff Y.toTop).2 Y.is_compactly_generated

/-- The functor sending an object of `GeneratedByTopCat.{v} (fun K : CompHaus.{u} ↦ K)` to the
same topological space in `CompactlyGenerated.{u, v}`. -/
@[expose, simps obj_toTop]
def fromGeneratedByTopCat :
    GeneratedByTopCat.{v} (fun K : CompHaus.{u} ↦ K) ⥤ CompactlyGenerated.{u, v} where
  obj Y :=
    { toTop := Y.obj
      is_compactly_generated := (Topology.isGeneratedBy_compHaus_iff Y.obj).1 Y.property }
  map f := fullyFaithfulCompactlyGeneratedToTop.preimage f.hom

@[simp]
theorem fromGeneratedByTopCat_map_hom
    {Y Z : GeneratedByTopCat.{v} (fun K : CompHaus.{u} ↦ K)} (f : Y ⟶ Z) :
    (fromGeneratedByTopCat.map f).hom = f.hom :=
  (rfl)

/-- `CompactlyGenerated.{u, v}` is equivalent to the category of spaces generated by
`CompHaus.{u}`, via the identity on underlying topological spaces and continuous maps. -/
@[expose, simps]
def generatedByEquivalence :
    CompactlyGenerated.{u, v} ≌ GeneratedByTopCat.{v} (fun K : CompHaus.{u} ↦ K) where
  functor := toGeneratedByTopCat
  inverse := fromGeneratedByTopCat
  unitIso := Iso.refl _
  counitIso := Iso.refl _

instance : (toGeneratedByTopCat.{u, v}).IsEquivalence :=
  generatedByEquivalence.isEquivalence_functor

instance : (fromGeneratedByTopCat.{u, v}).IsEquivalence :=
  generatedByEquivalence.isEquivalence_inverse

/-- Left binary product with any object in `CompactlyGenerated.{u, v}` preserves colimits of all
sizes whenever binary products exist in `CompactlyGenerated.{u, v}`. -/
noncomputable instance instPreservesColimitsOfSizeProdFunctor
    [HasBinaryProducts CompactlyGenerated.{u, v}] (Y : CompactlyGenerated.{u, v}) :
    PreservesColimitsOfSize.{w', w} (prod.functor.obj Y) :=
  toGeneratedByTopCat.preservesColimitsOfSize_prodFunctor Y

end CompactlyGenerated
