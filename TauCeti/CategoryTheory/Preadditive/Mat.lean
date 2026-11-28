/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Mat

/-!
# Monomial isomorphisms and additive functors on the matrix category

An object of `Mat_ C` is a finite family `M.X : M.ι → C` of objects of a preadditive category
`C`, and a morphism is a matrix of morphisms of `C`. Given an equivalence `e : M.ι ≃ N.ι` of index
types and isomorphisms `φ i : M.X i ≅ N.X (e i)`, the matrix whose only nonzero entries are the
`φ i`, placed at the positions `(i, e i)`, is an isomorphism `M ≅ N`: a *monomial* matrix, the
categorical form of a permutation matrix with invertible entries. These isomorphisms relabel the
summands of an object, and they compose and invert like their index equivalences.

The structure isomorphisms of the monoidal structure on `Mat_ C`
(`CategoryTheory.Mat_.instMonoidalCategory`) are monomial: the associator lies over
`Equiv.prodAssoc` and the unitors over `Equiv.punitProd` and `Equiv.prodPUnit`.

Composing a matrix with a monomial isomorphism on the side where the equivalence is applied only
permutes and rescales its entries: `Mat_.isoOfEquiv_hom_comp_apply` and
`Mat_.comp_isoOfEquiv_inv_apply` compute these composites without any `eqToHom`.

An additive functor into a category with finite biproducts extends to matrices by taking
biproducts of the images of the entries of each finite family. The source and target may have
independent object and morphism universes.

## Main declarations

* `CategoryTheory.Mat_.isoOfEquiv e φ`: the monomial isomorphism `M ≅ N` determined by
  `e : M.ι ≃ N.ι` and `φ i : M.X i ≅ N.X (e i)`.
* `CategoryTheory.Mat_.isoOfEquiv_refl`, `CategoryTheory.Mat_.isoOfEquiv_trans`,
  `CategoryTheory.Mat_.isoOfEquiv_symm`: monomial isomorphisms over the identity, a composite and
  an inverse equivalence.
* `CategoryTheory.Functor.liftToBiproducts`: the extension of an additive functor to matrices.
* `CategoryTheory.Functor.embeddingLiftToBiproductsIso`: the restriction of the extension to
  one-term families recovers the original functor.
* `CategoryTheory.Functor.FullyFaithful.liftToBiproducts`: the extension of a fully faithful
  additive functor is fully faithful.
* `CategoryTheory.Functor.liftToBiproductsUnique`: comparison with any additive extension
  equipped with a restriction isomorphism.

The file also records the entries of the zero matrix (`Mat_.zero_apply`) and of the one-by-one
matrices `(Mat_.embedding C).map f` (`Mat_.embedding_map_apply`), with the indices typed as those of
the one-term families `(Mat_.embedding C).obj X`, whose index types are singletons.

`CategoryTheory.Mat_.ext_hom_app` gives the components of the isomorphism `Mat_.ext α` of
additive functors out of `Mat_ C`.
-/

public section

open CategoryTheory

noncomputable section

namespace CategoryTheory.Mat_

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

@[simp]
theorem zero_apply {M N : Mat_ C} (i : M.ι) (j : N.ι) : (0 : M ⟶ N) i j = 0 := rfl

/-- A one-term family is indexed by a singleton. -/
instance (X : C) : Unique ((embedding C).obj X).ι := inferInstanceAs (Unique PUnit)

/-- The entry of a one-by-one matrix, with the indices typed as those of the one-term families.
Mathlib's `Mat_.embedding_map` types the indices by the unfolded structure instead, so `simp` does
not apply it to indices of type `((embedding C).obj X).ι`. -/
@[simp]
theorem embedding_map_apply {X Y : C} (f : X ⟶ Y) (i : ((embedding C).obj X).ι)
    (j : ((embedding C).obj Y).ι) : (embedding C).map f i j = f :=
  rfl

open scoped Classical in
/-- The matrix of `Mat_.isoOfEquiv e φ`. -/
private def homOfEquiv {M N : Mat_ C} (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) : M ⟶ N :=
  fun i j ↦ if h : e i = j then (φ i).hom ≫ eqToHom (congrArg N.X h) else 0

open scoped Classical in
/-- The matrix of the inverse of `Mat_.isoOfEquiv e φ`. -/
private def invOfEquiv {M N : Mat_ C} (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) : N ⟶ M :=
  fun j i ↦ if h : e i = j then eqToHom (congrArg N.X h.symm) ≫ (φ i).inv else 0

/-- The **monomial isomorphism** `M ≅ N` determined by an equivalence `e : M.ι ≃ N.ι` of index types
and isomorphisms `φ i : M.X i ≅ N.X (e i)`: its matrix has the entry `φ i` at the position
`(i, e i)` and zeros elsewhere. -/
def isoOfEquiv {M N : Mat_ C} (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) : M ≅ N where
  hom := homOfEquiv e φ
  inv := invOfEquiv e φ
  hom_inv_id := by
    ext i i'
    rw [Mat_.comp_apply,
      Finset.sum_eq_single (e i) (fun j _ hj ↦ by simp [homOfEquiv, Ne.symm hj]) (by simp)]
    by_cases h : i = i'
    · subst h
      simp [homOfEquiv, invOfEquiv]
    · simp [homOfEquiv, invOfEquiv, h, Ne.symm h]
  inv_hom_id := by
    ext j j'
    rw [Mat_.comp_apply, Finset.sum_eq_single (e.symm j) (fun i _ hi ↦ by
      simp [invOfEquiv, show e i ≠ j from fun h ↦ hi (by simp [← h])]) (by simp)]
    by_cases h : j = j'
    · subst h
      simp [homOfEquiv, invOfEquiv]
    · simp [homOfEquiv, invOfEquiv, h]

variable {M N P : Mat_ C}

open scoped Classical in
theorem isoOfEquiv_hom_apply (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) (i : M.ι) (j : N.ι) :
    (isoOfEquiv e φ).hom i j = if h : e i = j then (φ i).hom ≫ eqToHom (congrArg N.X h) else 0 :=
  (rfl)

open scoped Classical in
theorem isoOfEquiv_inv_apply (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) (j : N.ι) (i : M.ι) :
    (isoOfEquiv e φ).inv j i =
      if h : e i = j then eqToHom (congrArg N.X h.symm) ≫ (φ i).inv else 0 :=
  (rfl)

@[simp]
theorem isoOfEquiv_hom_apply_self (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) (i : M.ι) :
    (isoOfEquiv e φ).hom i (e i) = (φ i).hom := by
  simp [isoOfEquiv_hom_apply]

@[simp]
theorem isoOfEquiv_inv_apply_self (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) (i : M.ι) :
    (isoOfEquiv e φ).inv (e i) i = (φ i).inv := by
  simp [isoOfEquiv_inv_apply]

/-- Precomposing with a monomial isomorphism moves the rows along the equivalence and multiplies
them by the entries. -/
theorem isoOfEquiv_hom_comp_apply (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) (g : N ⟶ P)
    (i : M.ι) (k : P.ι) : ((isoOfEquiv e φ).hom ≫ g) i k = (φ i).hom ≫ g (e i) k := by
  rw [comp_apply, Finset.sum_eq_single (e i)]
  · simp
  · intro j _ hj
    simp [isoOfEquiv_hom_apply, Ne.symm hj]
  · simp

/-- Postcomposing with the inverse of a monomial isomorphism moves the columns along the
equivalence and multiplies them by the inverse entries. -/
theorem comp_isoOfEquiv_inv_apply (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) (f : P ⟶ N)
    (k : P.ι) (i : M.ι) : (f ≫ (isoOfEquiv e φ).inv) k i = f k (e i) ≫ (φ i).inv := by
  rw [comp_apply, Finset.sum_eq_single (e i)]
  · simp
  · intro j _ hj
    simp [isoOfEquiv_inv_apply, Ne.symm hj]
  · simp

/-- The monomial isomorphism over the identity equivalence with identity entries is the identity
isomorphism. -/
@[simp]
theorem isoOfEquiv_refl (M : Mat_ C) : isoOfEquiv (Equiv.refl M.ι) (fun _ ↦ Iso.refl _) =
    Iso.refl M := by
  ext i j
  rw [isoOfEquiv_hom_apply (Equiv.refl _) (fun _ ↦ Iso.refl _)]
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

/-- Monomial isomorphisms compose along the composite equivalence, with composite entries. -/
theorem isoOfEquiv_trans (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) (e' : N.ι ≃ P.ι)
    (ψ : ∀ j, N.X j ≅ P.X (e' j)) :
    isoOfEquiv e φ ≪≫ isoOfEquiv e' ψ = isoOfEquiv (e.trans e') fun i ↦ φ i ≪≫ ψ (e i) := by
  ext i k
  rw [Iso.trans_hom, isoOfEquiv_hom_comp_apply, isoOfEquiv_hom_apply, isoOfEquiv_hom_apply]
  by_cases h : e' (e i) = k
  · subst h
    simp
  · simp [h]

/-- The inverse of a monomial isomorphism is monomial over the inverse equivalence. -/
theorem isoOfEquiv_symm (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) :
    (isoOfEquiv e φ).symm =
      isoOfEquiv e.symm fun j ↦ eqToIso (congrArg N.X (e.apply_symm_apply j).symm) ≪≫
        (φ (e.symm j)).symm := by
  ext j i
  by_cases h : e i = j
  · subst h
    simp [isoOfEquiv_hom_apply, isoOfEquiv_inv_apply]
  · simp [isoOfEquiv_hom_apply, isoOfEquiv_inv_apply, h, e.symm_apply_eq, Ne.symm h]

section Ext

open Limits

variable {E : Type u} [Category.{v} E] [Preadditive E] [HasFiniteBiproducts E]

/-- The components of `Mat_.ext α`: on `M`, decompose `G M` as the biproduct of the `G` of the
entries of `M`, apply `α` entrywise, and reassemble. -/
theorem ext_hom_app {G G' : Mat_ C ⥤ E} [G.Additive] [G'.Additive]
    (α : embedding C ⋙ G ≅ embedding C ⋙ G') (M : Mat_ C) :
    (ext α).hom.app M = (additiveObjIsoBiproduct G M).hom ≫
      biproduct.map (fun i ↦ α.hom.app (M.X i)) ≫ (additiveObjIsoBiproduct G' M).inv := by
  simp only [ext, liftUnique, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app, Iso.trans_inv, Iso.symm_inv,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.cancel_iso_hom_left]
  simp only [biproduct.mapIso_hom, biproduct.mapIso_inv, Iso.app_hom, Iso.app_inv, Iso.refl_inv,
    NatTrans.id_app]
  -- The remaining middle factor is the biproduct of identities.
  congr 1
  conv_rhs => rw [← Category.id_comp (additiveObjIsoBiproduct G' M).inv]
  congr 1
  ext j
  simp

end Ext

end CategoryTheory.Mat_

namespace CategoryTheory.Functor

open Limits

variable {C E : Type*} [Category* C] [Preadditive C]
  [Category* E] [Preadditive E] [HasFiniteBiproducts E]

/-- Extend an additive functor to matrices by taking biproducts. This version of `Mat_.lift`
allows the source and target to have independent object and morphism universes. -/
def liftToBiproducts (F : C ⥤ E) [F.Additive] : Mat_ C ⥤ E where
  obj X := ⨁ fun i ↦ F.obj (X.X i)
  map f := biproduct.matrix fun i j ↦ F.map (f i j)
  map_id X := by
    ext i j : 2
    by_cases h : i = j
    · subst j
      simp
    · simp [Mat_.id_apply_of_ne _ _ _ (Ne.symm h), biproduct.ι_π_ne _ (Ne.symm h)]
  map_comp f g := by
    ext i j : 2
    simp [biproduct.lift_desc, ← Functor.map_comp]

/-- The image of a matrix object is canonically the biproduct of the images of its summands. -/
def liftToBiproductsObjIso (F : C ⥤ E) [F.Additive] (X : Mat_ C) :
    F.liftToBiproducts.obj X ≅ ⨁ fun i ↦ F.obj (X.X i) :=
  Iso.refl _

@[reassoc (attr := simp)]
theorem liftToBiproducts_map (F : C ⥤ E) [F.Additive] {X Y : Mat_ C} (f : X ⟶ Y) :
    (F.liftToBiproductsObjIso X).inv ≫ F.liftToBiproducts.map f ≫
      (F.liftToBiproductsObjIso Y).hom = biproduct.matrix (fun i j ↦ F.map (f i j)) := by
  change 𝟙 _ ≫ _ ≫ 𝟙 _ = _
  simp [liftToBiproducts]

instance (F : C ⥤ E) [F.Additive] : F.liftToBiproducts.Additive where
  map_add {X Y f g} := by
    apply (cancel_epi (F.liftToBiproductsObjIso X).inv).1
    apply (cancel_mono (F.liftToBiproductsObjIso Y).hom).1
    simp only [Category.assoc, Preadditive.add_comp, Preadditive.comp_add,
      liftToBiproducts_map, Mat_.add_apply, Functor.map_add]
    ext i j : 2
    simp [Preadditive.add_comp, Preadditive.comp_add]

omit [HasFiniteBiproducts E] in
/-- The hom of the singleton biproduct isomorphism is its sole projection. -/
private theorem biproductUniqueIso_hom_eq_π {J : Type*} [Unique J] (A : J → E)
    [HasBiproduct A] : (biproductUniqueIso A).hom = biproduct.π A default := by
  apply biproduct.hom_ext'
  intro i
  obtain rfl : i = default := Subsingleton.elim _ _
  simp [biproductUniqueIso_hom, limitBiconeOfUnique]

/-- Restricting the biproduct extension along the embedding as one-term families recovers
the original additive functor. -/
def embeddingLiftToBiproductsIso (F : C ⥤ E) [F.Additive] :
    Mat_.embedding C ⋙ F.liftToBiproducts ≅ F := by
  let e (X : C) := F.liftToBiproductsObjIso ((Mat_.embedding C).obj X)
  refine NatIso.ofComponents (fun X ↦ e X ≪≫ biproductUniqueIso _) ?_
  intro X Y f
  apply (cancel_epi (e X).inv).1
  change (e X).inv ≫ (F.liftToBiproducts.map ((Mat_.embedding C).map f) ≫
      (e Y).hom ≫ (biproductUniqueIso _).hom) =
    (e X).inv ≫ ((e X).hom ≫ (biproductUniqueIso _).hom) ≫ F.map f
  simp only [e, Category.assoc, liftToBiproducts_map_assoc, Iso.inv_hom_id_assoc,
    biproductUniqueIso_hom_eq_π, biproduct.matrix_π]
  apply biproduct.hom_ext'
  intro i
  obtain rfl : i = default := Subsingleton.elim _ _
  simp only [biproduct.ι_desc, Mat_.embedding_map_apply]
  let A := fun j : ((Mat_.embedding C).obj X).ι ↦ F.obj (((Mat_.embedding C).obj X).X j)
  exact (biproduct.ι_π_self_assoc A default (F.map f)).symm

@[simp]
theorem embeddingLiftToBiproductsIso_hom_app (F : C ⥤ E) [F.Additive] (X : C) :
    (F.embeddingLiftToBiproductsIso).hom.app X =
      (F.liftToBiproductsObjIso ((Mat_.embedding C).obj X)).hom ≫ biproduct.π _ default :=
  congrArg (_ ≫ ·) (biproductUniqueIso_hom_eq_π _)

@[simp]
theorem embeddingLiftToBiproductsIso_inv_app (F : C ⥤ E) [F.Additive] (X : C) :
    (F.embeddingLiftToBiproductsIso).inv.app X =
      biproduct.ι _ default ≫ (F.liftToBiproductsObjIso ((Mat_.embedding C).obj X)).inv := by
  apply (cancel_mono (F.embeddingLiftToBiproductsIso.hom.app X)).1
  rw [Iso.inv_hom_id_app, embeddingLiftToBiproductsIso_hom_app]
  let M := (Mat_.embedding C).obj X
  let A := fun i : M.ι ↦ F.obj (M.X i)
  change 𝟙 (A default) = (biproduct.ι A default ≫ (F.liftToBiproductsObjIso M).inv) ≫
    (F.liftToBiproductsObjIso M).hom ≫ biproduct.π A default
  rw [Category.assoc, Iso.inv_hom_id_assoc, biproduct.ι_π_self]

/-- The extension of a fully faithful additive functor to matrices is fully faithful.
The preimage takes the preimage of each transported matrix component. -/
def FullyFaithful.liftToBiproducts {F : C ⥤ E} [F.Additive] (hF : F.FullyFaithful) :
    F.liftToBiproducts.FullyFaithful where
  preimage {X Y} f i j := hF.preimage (biproduct.components
    ((F.liftToBiproductsObjIso X).inv ≫ f ≫ (F.liftToBiproductsObjIso Y).hom) i j)
  map_preimage {X Y} f := by
    apply (cancel_epi (F.liftToBiproductsObjIso X).inv).1
    apply (cancel_mono (F.liftToBiproductsObjIso Y).hom).1
    let p : X ⟶ Y := fun i j ↦ hF.preimage (biproduct.components
      ((F.liftToBiproductsObjIso X).inv ≫ f ≫ (F.liftToBiproductsObjIso Y).hom) i j)
    change (_ ≫ F.liftToBiproducts.map p) ≫ _ = _
    rw [Category.assoc, liftToBiproducts_map, Category.assoc]
    simpa only [p, hF.map_preimage] using! biproduct.components_matrix
      ((F.liftToBiproductsObjIso X).inv ≫ f ≫ (F.liftToBiproductsObjIso Y).hom)
  preimage_map f := by
    funext i j
    simp only [liftToBiproducts_map, biproduct.matrix_components, hF.preimage_map]

@[simp]
theorem FullyFaithful.liftToBiproducts_preimage_apply {F : C ⥤ E} [F.Additive]
    (hF : F.FullyFaithful) {X Y : Mat_ C} (f : F.liftToBiproducts.obj X ⟶ F.liftToBiproducts.obj Y)
    (i : X.ι) (j : Y.ι) :
    hF.liftToBiproducts.preimage f i j = hF.preimage (biproduct.components
      ((F.liftToBiproductsObjIso X).inv ≫ f ≫ (F.liftToBiproductsObjIso Y).hom) i j) := (rfl)

/-- The biproduct comparison for an additive functor on matrices, in independent universes. -/
private def matrixObjIso (L : Mat_ C ⥤ E) [L.Additive] (X : Mat_ C) :
    L.obj X ≅ ⨁ fun i ↦ L.obj ((Mat_.embedding C).obj (X.X i)) :=
  L.mapIso X.isoBiproductEmbedding ≪≫ L.mapBiproduct _

omit [HasFiniteBiproducts E] in
@[reassoc]
private theorem matrixObjIso_hom_π (L : Mat_ C ⥤ E) [L.Additive] (X : Mat_ C) (i : X.ι) :
    (matrixObjIso L X).hom ≫ biproduct.π _ i =
      L.map (X.isoBiproductEmbedding.hom ≫ biproduct.π _ i) := by
  rw [matrixObjIso, Iso.trans_hom, mapIso_hom, mapBiproduct_hom, Category.assoc,
    biproduct.lift_π, L.map_comp]

omit [HasFiniteBiproducts E] in
@[reassoc]
private theorem ι_matrixObjIso_inv (L : Mat_ C ⥤ E) [L.Additive] (X : Mat_ C) (i : X.ι) :
    biproduct.ι _ i ≫ (matrixObjIso L X).inv =
      L.map (biproduct.ι _ i ≫ X.isoBiproductEmbedding.inv) := by
  rw [matrixObjIso, Iso.trans_inv, mapIso_inv, mapBiproduct_inv, ← Category.assoc,
    biproduct.ι_desc, L.map_comp]

open scoped Classical in
private theorem matrixEmbedding_hom_π (Y : Mat_ C) (j : Y.ι) :
    Y.isoBiproductEmbedding.hom ≫ biproduct.π _ j =
      (fun k _ ↦ if h : k = j then eqToHom (congrArg Y.X h) else 0) := by
  let π (s : Y.ι) : Y ⟶ (Mat_.embedding C).obj (Y.X s) :=
    fun k _ ↦ if h : k = s then eqToHom (congrArg Y.X h) else 0
  exact biproduct.lift_π π j

@[reassoc]
private theorem matrixObjIso_naturality (L : Mat_ C ⥤ E) [L.Additive] {X Y : Mat_ C}
    (f : X ⟶ Y) :
    L.map f ≫ (matrixObjIso L Y).hom =
      (matrixObjIso L X).hom ≫
        biproduct.matrix (fun i j ↦ L.map ((Mat_.embedding C).map (f i j))) := by
  classical
  apply (cancel_epi (matrixObjIso L X).inv).1
  simp only [Iso.inv_hom_id_assoc]
  refine biproduct.hom_ext _ _ (fun j ↦ biproduct.hom_ext' _ _ fun i ↦ ?_)
  simp only [Category.assoc, ι_matrixObjIso_inv_assoc, matrixObjIso_hom_π,
    biproduct.ι_matrix_assoc, biproduct.lift_π, ← L.map_comp]
  apply congrArg L.map
  let ι (s : X.ι) : (Mat_.embedding C).obj (X.X s) ⟶ X :=
    fun _ k ↦ if h : s = k then eqToHom (congrArg X.X h) else 0
  have hi : biproduct.ι _ i ≫ X.isoBiproductEmbedding.inv = ι i :=
    biproduct.ι_desc ι i
  let π : Y ⟶ (Mat_.embedding C).obj (Y.X j) :=
    fun k _ ↦ if h : k = j then eqToHom (congrArg Y.X h) else 0
  have hj : Y.isoBiproductEmbedding.hom ≫ biproduct.π _ j = π :=
    matrixEmbedding_hom_π Y j
  let d : X.X i ⟶ Y.X j := f i j
  change _ = (Mat_.embedding C).map d
  rw [← Category.assoc (biproduct.ι _ i), hi, hj]
  apply Mat_.hom_ext
  intro a b
  have h : (ι i ≫ f ≫ π) a b = (f ≫ π) i b := by
    rw [Mat_.comp_apply, Finset.sum_eq_single i]
    · have h : ι i a i = 𝟙 (X.X i) := by
        change (if h : i = i then eqToHom (congrArg X.X h) else 0) = _
        simp
      rw [h]
      exact Category.id_comp ((f ≫ π) i b : X.X i ⟶ Y.X j)
    · intro k _ hk
      have h : ι i a k = 0 := dite_eq_right (Ne.symm hk)
      rw [h, zero_comp]
    · simp
  refine h.trans ?_
  change (f ≫ π) i b = d
  rw [Mat_.comp_apply, Finset.sum_eq_single j]
  · have h : π j b = 𝟙 (Y.X j) := by
      change (if h : j = j then eqToHom (congrArg Y.X h) else 0) = _
      simp
    rw [h]
    exact Category.comp_id d
  · intro k _ hk
    have h : π k b = 0 := dite_eq_right hk
    rw [h, comp_zero]
  · simp

/-- Compare an additive extension with the biproduct lift using its given restriction
isomorphism. This is the universe-polymorphic form of `Mat_.liftUnique`. -/
def liftToBiproductsUnique (F : C ⥤ E) [F.Additive] (L : Mat_ C ⥤ E) [L.Additive]
    (α : Mat_.embedding C ⋙ L ≅ F) : L ≅ F.liftToBiproducts :=
  NatIso.ofComponents
    (fun X ↦ matrixObjIso L X ≪≫ biproduct.mapIso (fun i ↦ α.app (X.X i)) ≪≫
      (F.liftToBiproductsObjIso X).symm)
    (fun {X Y} f ↦ by
      apply (cancel_mono (F.liftToBiproductsObjIso Y).hom).1
      simp only [Iso.trans_hom, Iso.symm_hom, biproduct.mapIso_hom, Category.assoc,
        Iso.inv_hom_id, Category.comp_id, liftToBiproducts_map, matrixObjIso_naturality_assoc]
      simp only [biproduct.matrix_map, biproduct.map_matrix]
      congr 2
      funext i j
      exact α.hom.naturality (f i j))

/-- The comparison of extensions recovers the given isomorphism on one-term families. -/
@[simp]
theorem liftToBiproductsUnique_restrict (F : C ⥤ E) [F.Additive] (L : Mat_ C ⥤ E) [L.Additive]
    (α : Mat_.embedding C ⋙ L ≅ F) :
    isoWhiskerLeft (Mat_.embedding C) (F.liftToBiproductsUnique L α) ≪≫
      F.embeddingLiftToBiproductsIso = α := by
  apply Iso.ext
  ext X
  let M := (Mat_.embedding C).obj X
  have h : M.isoBiproductEmbedding.hom ≫ biproduct.π _ default = 𝟙 M := by
    have hp := matrixEmbedding_hom_π M (default : M.ι)
    refine hp.trans ?_
    apply Mat_.hom_ext
    intro i j
    obtain rfl : i = default := Subsingleton.elim _ _
    obtain rfl : j = default := Subsingleton.elim _ _
    exact (dite_eq_left rfl).trans ((eqToHom_refl _ _).trans (Mat_.id_apply_self _ _).symm)
  let a (i : M.ι) : L.obj ((Mat_.embedding C).obj (M.X i)) ⟶ F.obj (M.X i) :=
    α.hom.app (M.X i)
  change ((matrixObjIso L M).hom ≫ biproduct.map a ≫ (F.liftToBiproductsObjIso M).inv) ≫
    (F.embeddingLiftToBiproductsIso).hom.app X = α.hom.app X
  rw [embeddingLiftToBiproductsIso_hom_app]
  change ((matrixObjIso L M).hom ≫ biproduct.map a ≫ (F.liftToBiproductsObjIso M).inv) ≫
    ((F.liftToBiproductsObjIso M).hom ≫
      biproduct.π (fun i : M.ι ↦ F.obj (M.X i)) default) = a default
  simp only [Category.assoc, Iso.inv_hom_id_assoc, biproduct.map_π, matrixObjIso_hom_π_assoc,
    h]
  exact (congrArg (· ≫ a default) (L.map_id M)).trans (Category.id_comp _)

end CategoryTheory.Functor
