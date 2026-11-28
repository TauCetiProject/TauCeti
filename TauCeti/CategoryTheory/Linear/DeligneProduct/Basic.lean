/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Linear.LinearTensor.Basic
public import TauCeti.CategoryTheory.Linear.Mat
public import TauCeti.CategoryTheory.Linear.SplitSimpleFamily
public import TauCeti.CategoryTheory.Preadditive.Mat

/-!
# The Deligne tensor product of linear categories

The **Deligne tensor product** `DeligneProduct k C D` is the additive envelope
`Mat_ (LinearTensor k C D)` of the linear tensor product, whose objects are formal finite
biproducts of pairs `X ⊠ Y`. It has finite biproducts, and the same universal property holds for
functors into additive `k`-linear categories (in the universes of `Mat_.lift`), now with
`DeligneProduct.lift k F` extending `F` additively over finite biproducts. For finite semisimple
categories whose simple objects have endomorphisms `k`, for instance over an algebraically closed
field, this is the Deligne tensor product `C ⊠ D` of Etingof–Gelaki–Nikshych–Ostrik.

Finally, if `S : ι → C` and `T : ι' → D` are split simple families over `k` (every member has
scalar endomorphisms, there are no morphisms between distinct members, and every object is a
finite biproduct of members), then so is the family of pairs `S i ⊠ T j` in `DeligneProduct k C D`,
indexed by `ι × ι'` (`TauCeti.IsSplitSimpleFamily.deligneProduct`). So every object of `C ⊠ D` is a
finite biproduct of the objects `S i ⊠ T j`, which have scalar endomorphisms and admit no nonzero
morphisms between distinct members; this is the semisimplicity of the Deligne product.

## Main declarations

* `TauCeti.DeligneProduct`, with `TauCeti.DeligneProduct.bifunctor`, `TauCeti.DeligneProduct.lift`,
  `TauCeti.DeligneProduct.bifunctorCompLiftIso`, `TauCeti.DeligneProduct.ext` (with its components
  `TauCeti.DeligneProduct.ext_hom_app`) and `TauCeti.DeligneProduct.liftUnique`;
* `TauCeti.DeligneProduct.biproductIso`: `(⨁ f) ⊠ (⨁ g)` is the biproduct of the `f j ⊠ g j'`, with
  components `TauCeti.DeligneProduct.biproductIso_hom_π` and
  `TauCeti.DeligneProduct.ι_biproductIso_inv`;
* `TauCeti.IsSplitSimpleFamily.deligneProduct`: products of split simple families.

## References

* [P. Deligne, *Catégories tannakiennes*][deligne1990], §5
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], Definition 1.11.1,
  Proposition 1.11.2 and §4.6
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe w v₁ v₂ u₁ u₂

namespace TauCeti

/-- The **Deligne tensor product** of `k`-linear categories `C` and `D`: the additive envelope
`Mat_` of their `k`-linear tensor product `LinearTensor k C D`. Its objects are formal finite
biproducts of pairs `X ⊠ Y`; its category, preadditive and `k`-linear structures are those of
`Mat_` over the `k`-linear category `LinearTensor k C D`. -/
abbrev DeligneProduct (k : Type w) (C : Type u₁) (D : Type u₂) :=
  Mat_ (LinearTensor k C D)

namespace DeligneProduct

variable (k : Type w) [CommSemiring k]
  (C : Type u₁) [Category.{v₁} C] [Preadditive C] [Linear k C]
  (D : Type u₂) [Category.{v₂} D] [Preadditive D] [Linear k D]

/-- The canonical functor `C ⥤ D ⥤ DeligneProduct k C D`, sending `X` and `Y` to `X ⊠ Y`. It is
additive and `k`-linear in each variable. -/
def bifunctor : C ⥤ D ⥤ DeligneProduct k C D :=
  LinearTensor.bifunctor k C D ⋙
    (Functor.whiskeringRight D _ _).obj (Mat_.embedding (LinearTensor k C D))

variable {k C D}

@[simp]
theorem bifunctor_obj_obj (X : C) (Y : D) :
    ((bifunctor k C D).obj X).obj Y = (Mat_.embedding _).obj ⟨X, Y⟩ :=
  rfl

@[simp]
theorem bifunctor_obj_map (X : C) {Y Y' : D} (g : Y ⟶ Y') :
    ((bifunctor k C D).obj X).map g = (Mat_.embedding _).map (LinearTensor.tmul (𝟙 X) g) :=
  rfl

@[simp]
theorem bifunctor_map_app {X X' : C} (f : X ⟶ X') (Y : D) :
    ((bifunctor k C D).map f).app Y = (Mat_.embedding _).map (LinearTensor.tmul f (𝟙 Y)) :=
  rfl

instance (X : C) : ((bifunctor k C D).obj X).Additive :=
  inferInstanceAs <| Functor.Additive
    ((LinearTensor.bifunctor k C D).obj X ⋙ Mat_.embedding (LinearTensor k C D))

instance (X : C) : ((bifunctor k C D).obj X).Linear k :=
  inferInstanceAs <| Functor.Linear k
    ((LinearTensor.bifunctor k C D).obj X ⋙ Mat_.embedding (LinearTensor k C D))

instance : (bifunctor k C D).Additive where
  map_add {_ _ f f'} := by
    ext Y : 2
    rw [NatTrans.app_add, bifunctor_map_app, bifunctor_map_app, bifunctor_map_app,
      LinearTensor.add_tmul]
    exact Functor.map_add _

instance : (bifunctor k C D).Linear k where
  map_smul f r := by
    ext Y : 2
    rw [NatTrans.app_smul, bifunctor_map_app, bifunctor_map_app, LinearTensor.smul_tmul]
    exact Functor.map_smul _ _ _

/-- **`⊠` preserves finite biproducts in both variables**: for finite families `f` in `C` and `g`
in `D`, the object `(⨁ f) ⊠ (⨁ g)` is the biproduct of the objects `f j ⊠ g j'`. -/
def biproductIso {J J' : Type} [Fintype J] [Fintype J'] (f : J → C) (g : J' → D)
    [HasBiproduct f] [HasBiproduct g] :
    (Mat_.embedding (LinearTensor k C D)).obj ⟨⨁ f, ⨁ g⟩ ≅
      ⨁ fun p : J × J' ↦ (Mat_.embedding (LinearTensor k C D)).obj ⟨f p.1, g p.2⟩ :=
  biproduct.uniqueUpToIso _ (isBilimitOfPreserves (Mat_.embedding (LinearTensor k C D))
    (LinearTensor.isBilimitBiconeTmul (biproduct.isBilimit f) (biproduct.isBilimit g)))

/-- The components of `biproductIso` towards the summands: the projection onto `f p.1 ⊠ g p.2`
is the pure tensor of the two projections. -/
@[reassoc (attr := simp)]
theorem biproductIso_hom_π {J J' : Type} [Fintype J] [Fintype J'] (f : J → C) (g : J' → D)
    [HasBiproduct f] [HasBiproduct g] (p : J × J') :
    (biproductIso (k := k) f g).hom ≫ biproduct.π _ p =
      (Mat_.embedding _).map (LinearTensor.tmul (biproduct.π f p.1) (biproduct.π g p.2)) :=
  biproduct.lift_π _ _

/-- The components of `biproductIso` from the summands: the inclusion of `f p.1 ⊠ g p.2` is the
pure tensor of the two inclusions. -/
@[reassoc (attr := simp)]
theorem ι_biproductIso_inv {J J' : Type} [Fintype J] [Fintype J'] (f : J → C) (g : J' → D)
    [HasBiproduct f] [HasBiproduct g] (p : J × J') :
    biproduct.ι _ p ≫ (biproductIso (k := k) f g).inv =
      (Mat_.embedding _).map (LinearTensor.tmul (biproduct.ι f p.1) (biproduct.ι g p.2)) :=
  biproduct.ι_desc _ _

variable {E : Type (max u₁ u₂)} [Category.{max v₁ v₂} E] [Preadditive E] [HasFiniteBiproducts E]

section Lift

variable [Linear k E] (F : C ⥤ D ⥤ E) [F.Additive] [F.Linear k] [∀ X, (F.obj X).Additive]
  [∀ X, (F.obj X).Linear k]

variable (k) in
/-- The extension of a bifunctor `F : C ⥤ D ⥤ E`, additive and `k`-linear in each variable, to a
`k`-linear functor `DeligneProduct k C D ⥤ E` into an additive `k`-linear category: it sends
`X ⊠ Y` to `F X Y` and formal biproducts to biproducts. -/
def lift : DeligneProduct k C D ⥤ E :=
  Mat_.lift (LinearTensor.lift k F)

instance : (lift k F).Additive :=
  inferInstanceAs <| Functor.Additive (Mat_.lift (LinearTensor.lift k F))

instance : (lift k F).Linear k :=
  inferInstanceAs <| Functor.Linear k (Mat_.lift (LinearTensor.lift k F))

/-- `lift k F` sends a formal biproduct of pairs `X ⊠ Y` to the biproduct of the objects
`F X Y`. -/
@[simp]
theorem lift_obj (M : DeligneProduct k C D) :
    (lift k F).obj M = ⨁ fun i ↦ (F.obj (M.X i).fst).obj (M.X i).snd :=
  rfl

/-- `lift k F` sends a matrix of morphisms to the matrix of their images under
`LinearTensor.lift k F`. -/
@[simp]
theorem lift_map {M N : DeligneProduct k C D} (t : M ⟶ N) :
    (lift k F).map t = biproduct.matrix fun i j ↦ (LinearTensor.lift k F).map (t i j) :=
  rfl

variable (k) in
/-- The extension `lift k F` restricts along `bifunctor` to `F`. -/
def bifunctorCompLiftIso : bifunctor k C D ⋙ (Functor.whiskeringRight D _ E).obj (lift k F) ≅ F :=
  Functor.isoWhiskerLeft (LinearTensor.bifunctor k C D)
      ((Functor.whiskeringRight D _ E).mapIso (Mat_.embeddingLiftIso (LinearTensor.lift k F))) ≪≫
    LinearTensor.bifunctorCompLiftIso k F

/-- The component of `bifunctorCompLiftIso k F` at `X ⊠ Y` is the identity of `F X Y`, seen as a
map out of the one-term biproduct `(lift k F).obj (X ⊠ Y)`. -/
@[simp]
theorem bifunctorCompLiftIso_hom_app_app (X : C) (Y : D) :
    ((bifunctorCompLiftIso k F).hom.app X).app Y = biproduct.desc fun _ ↦ 𝟙 ((F.obj X).obj Y) :=
  -- By definition, the component is that of `Mat_.embeddingLiftIso`, which is this
  -- `biproduct.desc`, followed by the identity component of `LinearTensor.bifunctorCompLiftIso`.
  Category.comp_id _

/-- The inverse component of `bifunctorCompLiftIso k F` at `X ⊠ Y` is the identity of `F X Y`, seen
as a map into the one-term biproduct `(lift k F).obj (X ⊠ Y)`. -/
@[simp]
theorem bifunctorCompLiftIso_inv_app_app (X : C) (Y : D) :
    ((bifunctorCompLiftIso k F).inv.app X).app Y = biproduct.lift fun _ ↦ 𝟙 ((F.obj X).obj Y) :=
  -- By definition, the identity component of `LinearTensor.bifunctorCompLiftIso` followed by the
  -- inverse component of `Mat_.embeddingLiftIso`, which is this `biproduct.lift`.
  Category.id_comp _

end Lift

/-- Two additive functors out of `DeligneProduct k C D` whose restrictions along `bifunctor` are
isomorphic are isomorphic. -/
def ext {G G' : DeligneProduct k C D ⥤ E} [G.Additive] [G'.Additive]
    (α : bifunctor k C D ⋙ (Functor.whiskeringRight D _ E).obj G ≅
      bifunctor k C D ⋙ (Functor.whiskeringRight D _ E).obj G') :
    G ≅ G' :=
  Mat_.ext (LinearTensor.ext α)

/-- The components of `ext α`: on a formal biproduct `M` of pairs, decompose `G M` as the
biproduct of the `G (X ⊠ Y)` over the entries `(X, Y)` of `M`, apply the components of `α`, and
reassemble. -/
theorem ext_hom_app {G G' : DeligneProduct k C D ⥤ E} [G.Additive] [G'.Additive]
    (α : bifunctor k C D ⋙ (Functor.whiskeringRight D _ E).obj G ≅
      bifunctor k C D ⋙ (Functor.whiskeringRight D _ E).obj G') (M : DeligneProduct k C D) :
    (ext α).hom.app M = (Mat_.additiveObjIsoBiproduct G M).hom ≫
      biproduct.map (fun i ↦ (α.hom.app (M.X i).fst).app (M.X i).snd) ≫
        (Mat_.additiveObjIsoBiproduct G' M).inv :=
  -- `ext α` is `Mat_.ext (LinearTensor.ext α)`, and the components of `LinearTensor.ext α` are
  -- those of `α` (`LinearTensor.ext_hom_app`, which holds by `rfl`).
  Mat_.ext_hom_app (LinearTensor.ext α) M

/-- **Uniqueness of the extension**: an additive functor `L` out of `DeligneProduct k C D` whose
restriction along `bifunctor` is isomorphic to `F` is isomorphic to `lift k F`. -/
def liftUnique [Linear k E] (F : C ⥤ D ⥤ E) [F.Additive] [F.Linear k] [∀ X, (F.obj X).Additive]
    [∀ X, (F.obj X).Linear k] (L : DeligneProduct k C D ⥤ E) [L.Additive]
    (α : bifunctor k C D ⋙ (Functor.whiskeringRight D _ E).obj L ≅ F) : L ≅ lift k F :=
  ext (α ≪≫ (bifunctorCompLiftIso k F).symm)

end DeligneProduct

namespace IsSplitSimpleFamily

variable {k : Type w} [CommSemiring k]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear k C] [HasFiniteBiproducts C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear k D] [HasFiniteBiproducts D]
  {ι : Type*} {ι' : Type*} {S : ι → C} {T : ι' → D}

/-- **Products of split simple families**: if `S` and `T` are split simple families in `C` and
`D`, then the objects `S i ⊠ T j` form a split simple family in the Deligne product
`DeligneProduct k C D`, indexed by `ι × ι'`. -/
theorem deligneProduct (hS : IsSplitSimpleFamily k S) (hT : IsSplitSimpleFamily k T) :
    IsSplitSimpleFamily k
      (fun p : ι × ι' ↦ ((DeligneProduct.bifunctor k C D).obj (S p.1)).obj (T p.2)) where
  bijective_algebraMap p := by
    have h : algebraMap k (End ((Mat_.embedding (LinearTensor k C D)).obj ⟨S p.1, T p.2⟩)) =
        (Mat_.embedding _).mapEndAlgHom k _ ∘
          algebraMap k (End (⟨S p.1, T p.2⟩ : LinearTensor k C D)) :=
      funext fun r ↦ (((Mat_.embedding _).mapEndAlgHom k _).commutes r).symm
    have key := ((Mat_.embedding _).mapEndAlgHom_bijective k _
      ⟨(Mat_.embedding _).map_injective, (Mat_.embedding _).map_surjective⟩).comp
        (LinearTensor.bijective_algebraMap_mk (hS.bijective_algebraMap p.1)
          (hT.bijective_algebraMap p.2))
    rw [← h] at key
    exact key
  homOrthogonal p q hpq := by
    have : Subsingleton ((⟨S p.1, T p.2⟩ : LinearTensor k C D) ⟶ ⟨S q.1, T q.2⟩) := by
      by_cases h : p.1 = q.1
      · have : Subsingleton (T p.2 ⟶ T q.2) := hT.homOrthogonal fun h' ↦ hpq (Prod.ext h h')
        infer_instance
      · have : Subsingleton (S p.1 ⟶ S q.1) := hS.homOrthogonal h
        infer_instance
    exact ((Mat_.embedding (LinearTensor k C D)).map_surjective (X := ⟨S p.1, T p.2⟩)
      (Y := ⟨S q.1, T q.2⟩)).subsingleton
  exists_iso_biproduct M := by
    choose κ hκ a ha using fun i ↦ hS.exists_iso_biproduct (M.X i).fst
    choose κ' hκ' b hb using fun i ↦ hT.exists_iso_biproduct (M.X i).snd
    refine ⟨Σ i, κ i × κ' i, inferInstance, fun x ↦ (a x.1 x.2.1, b x.1 x.2.2), ⟨?_⟩⟩
    exact M.isoBiproductEmbedding ≪≫
      biproduct.mapIso (fun i ↦ (Mat_.embedding _).mapIso
        (LinearTensor.isoMk (ha i).some (hb i).some) ≪≫
          DeligneProduct.biproductIso (fun x ↦ S (a i x)) (fun y ↦ T (b i y))) ≪≫
      biproductBiproductIso _ _

end IsSplitSimpleFamily

end TauCeti
