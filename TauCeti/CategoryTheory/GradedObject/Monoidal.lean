/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Exactness and reindexing for tensor products of graded objects

The tensor product of two graded objects `X` and `Y` has the coproduct of the `X i ⊗ Y j` with
`i + j = n` in degree `n` (`CategoryTheory.GradedObject.Monoidal.tensorObj`).  This file records
facts about these coproducts which are used to compare homology of tensor products of complexes.

* The map of coproducts over the fibres of a map induced by a morphism of graded objects is a
  map of colimits of discrete diagrams (`CategoryTheory.GradedObject.mapMap_eq_colimMap`).
* A family of monomorphisms induces a monomorphism on coproducts over the fibres of a map, when
  these coproducts are exact (`CategoryTheory.GradedObject.mono_mapMap`), and likewise a family of
  short exact sequences induces a short exact sequence
  (`CategoryTheory.GradedObject.shortExact_mapMap`), a family of exact sequences induces an exact
  sequence (`CategoryTheory.GradedObject.exact_mapMap`), and a family of epimorphisms induces an
  epimorphism (`CategoryTheory.GradedObject.epi_mapMap`).  In particular the tensor
  product of morphisms of graded objects is a monomorphism in a degree with finitely many
  summands as soon as each summand is (`CategoryTheory.GradedObject.Monoidal.mono_tensorHom`), for
  instance in every degree for graded objects indexed by `ℕ`.  Tensoring with an identity is the
  map of coproducts induced by the whiskerings
  (`CategoryTheory.GradedObject.Monoidal.id_tensorHom_eq_mapMap`), so these facts apply to it.
* For graded objects indexed by `ℕ`, if `Y 0 = 0` then the summands of `X ⊗ Y` in degree
  `m + 1` are those of `X` tensored with `Y` shifted down by one, in degree `m`
  (`CategoryTheory.GradedObject.Monoidal.tensorObjSuccIso`), naturally in `X` and `Y`
  (`CategoryTheory.GradedObject.Monoidal.tensorObjSuccIso_hom_naturality`).  This identifies the
  degree shift of a connecting morphism between tensor products.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.GradedObject

variable {I J C : Type*} [Category* C]

/-- The map of coproducts over the fibre of `p : I → J` over `j` induced by a morphism of graded
objects is the map of colimits of the corresponding discrete diagrams. -/
lemma mapMap_eq_colimMap {X Y : GradedObject I C} (φ : X ⟶ Y) (p : I → J) [X.HasMap p]
    [Y.HasMap p] (j : J) :
    mapMap φ p j = colimMap (Discrete.natTrans fun i ↦ φ i.as.1 :
      Discrete.functor (X.mapObjFun p j) ⟶ Discrete.functor (Y.mapObjFun p j)) := by
  refine mapObj_ext _ _ _ _ fun i hi ↦ ?_
  rw [ι_mapMap]
  -- `ιMapObj` is the colimit inclusion `Sigma.ι` of the discrete diagram `mapObjFun`
  exact (ι_colimMap (Discrete.natTrans fun i ↦ φ i.as.1 :
    Discrete.functor (X.mapObjFun p j) ⟶ Discrete.functor (Y.mapObjFun p j)) ⟨⟨i, hi⟩⟩).symm

/-- A morphism of graded objects which is a monomorphism in each degree induces a monomorphism on
the coproducts over the fibre of `p : I → J` over `j`, when coproducts of that shape are exact. -/
lemma mono_mapMap [Abelian C] {X Y : GradedObject I C} (φ : X ⟶ Y) (p : I → J) [X.HasMap p]
    [Y.HasMap p] (j : J) [HasColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    [HasExactColimitsOfShape (Discrete (p ⁻¹' {j})) C] [∀ i, Mono (φ i)] :
    Mono (mapMap φ p j) := by
  let α : Discrete.functor (X.mapObjFun p j) ⟶ Discrete.functor (Y.mapObjFun p j) :=
    Discrete.natTrans fun i ↦ φ i.as.1
  have : ∀ i, Mono (α.app i) := fun i ↦ inferInstanceAs (Mono (φ i.as.1))
  have : Mono α := NatTrans.mono_of_mono_app _
  rw [mapMap_eq_colimMap, ← colim_map]
  exact Functor.map_mono colim α

/-- A morphism of graded objects which is an epimorphism in each degree induces an epimorphism on
the coproducts over the fibre of `p : I → J` over `j`. -/
lemma epi_mapMap {X Y : GradedObject I C} (φ : X ⟶ Y) (p : I → J) [X.HasMap p]
    [Y.HasMap p] (j : J) [HasColimitsOfShape (Discrete (p ⁻¹' {j})) C] [∀ i, Epi (φ i)] :
    Epi (mapMap φ p j) := by
  let α : Discrete.functor (X.mapObjFun p j) ⟶ Discrete.functor (Y.mapObjFun p j) :=
    Discrete.natTrans fun i ↦ φ i.as.1
  have : ∀ i, Epi (α.app i) := fun i ↦ inferInstanceAs (Epi (φ i.as.1))
  have : Epi α := NatTrans.epi_of_epi_app _
  rw [mapMap_eq_colimMap, ← colim_map]
  exact Functor.map_epi colim α

/-- A short complex of graded objects which is exact in each degree induces an exact sequence on
the coproducts over the fibre of `p : I → J` over `j`, when coproducts of that shape are exact. -/
lemma exact_mapMap [Abelian C] (S : ShortComplex (GradedObject I C)) (p : I → J)
    [S.X₁.HasMap p] [S.X₂.HasMap p] [S.X₃.HasMap p] (j : J)
    [HasColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    [HasExactColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    (hS : ∀ i, (ShortComplex.mk (S.f i) (S.g i) (congr_fun S.zero i)).Exact) :
    (ShortComplex.mk (mapMap S.f p j) (mapMap S.g p j) (mapObj_ext _ _ _ _ fun i _ ↦ by
      rw [ι_mapMap_assoc, ι_mapMap, ← Category.assoc, ← Pi.comp_apply, S.zero]
      simp)).Exact := by
  -- the coproducts over the fibre are the colimits of the corresponding discrete diagrams, and
  -- `colim` is exact
  let T : ShortComplex (Discrete (p ⁻¹' {j}) ⥤ C) :=
    ShortComplex.mk (X₁ := Discrete.functor (S.X₁.mapObjFun p j))
      (X₂ := Discrete.functor (S.X₂.mapObjFun p j)) (X₃ := Discrete.functor (S.X₃.mapObjFun p j))
      (Discrete.natTrans fun i ↦ S.f i.as.1) (Discrete.natTrans fun i ↦ S.g i.as.1)
      (by ext i; exact congr_fun S.zero i.as.1)
  have hT : T.Exact := by
    have hP : JointlyReflectIsomorphisms fun i : Discrete (p ⁻¹' {j}) ↦ (evaluation _ C).obj i :=
      ⟨fun f h ↦ have : ∀ i, IsIso (f.app i) := h; NatIso.isIso_of_isIso_app f⟩
    rw [hP.exact_iff]
    exact fun i ↦ hS i.as.1
  exact colim.exact_mapShortComplex hT (colimit.isColimit _) (colimit.isColimit _)
    (colimit.isColimit _) (mapMap S.f p j) (mapMap S.g p j)
    (fun i ↦ ι_mapMap S.f p i.as.1 j i.as.2) (fun i ↦ ι_mapMap S.g p i.as.1 j i.as.2)

/-- A short complex of graded objects which is short exact in each degree induces a short exact
sequence on the coproducts over the fibre of `p : I → J` over `j`, when coproducts of that shape
are exact. -/
lemma shortExact_mapMap [Abelian C] (S : ShortComplex (GradedObject I C)) (p : I → J)
    [S.X₁.HasMap p] [S.X₂.HasMap p] [S.X₃.HasMap p] (j : J)
    [HasColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    [HasExactColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    (hS : ∀ i, (ShortComplex.mk (S.f i) (S.g i) (congr_fun S.zero i)).ShortExact) :
    (ShortComplex.mk (mapMap S.f p j) (mapMap S.g p j) (mapObj_ext _ _ _ _ fun i _ ↦ by
      rw [ι_mapMap_assoc, ι_mapMap, ← Category.assoc, ← Pi.comp_apply, S.zero]
      simp)).ShortExact :=
  have (i : I) : Mono (S.f i) := (hS i).mono_f
  have (i : I) : Epi (S.g i) := (hS i).epi_g
  { exact := exact_mapMap S p j fun i ↦ (hS i).exact
    mono_f := mono_mapMap S.f p j
    epi_g := epi_mapMap S.g p j }

namespace Monoidal

/-- In a degree `n` with finitely many pairs `i + j = n`, the tensor product of two morphisms of
graded objects is a monomorphism as soon as each of its summands `f i ⊗ g j` is. -/
lemma mono_tensorHom [AddMonoid I] [MonoidalCategory C] [Abelian C] {X₁ X₂ Y₁ Y₂ : GradedObject I C}
    (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) [HasTensor X₁ Y₁] [HasTensor X₂ Y₂] (n : I)
    (hn : Set.Finite {x : I × I | x.1 + x.2 = n}) [∀ i j, Mono (f i ⊗ₘ g j)] :
    Mono (tensorHom f g n) := by
  unfold tensorHom mapBifunctorMapMap
  -- the summands of degree `n` are indexed by a finite type, over which coproducts are exact
  refine @mono_mapMap _ _ _ _ _ _ _ _ _ _ _ n
    (@hasColimitsOfShape_discrete C _ _ _ (Set.Finite.to_subtype (hn.subset fun ⟨i, j⟩ h ↦ h)))
    (@hasExactColimitsOfShape_discrete_finite C _ _ Abelian.hasFiniteBiproducts _
      (Set.Finite.to_subtype (hn.subset fun ⟨i, j⟩ h ↦ h))) fun ⟨i, j⟩ ↦ ?_
  have := (inferInstance : Mono (f i ⊗ₘ g j))
  rw [MonoidalCategory.tensorHom_def] at this
  -- the component of the map of coproducts at `(i, j)` is `f i ▷ Y₁ j ≫ X₂ i ◁ g j`
  exact this

/-- Tensoring a morphism of graded objects with the identity of `X` is, in each degree, the map of
coproducts induced by the morphisms `X i ◁ g j`. -/
lemma id_tensorHom_eq_mapMap [AddMonoid I] [MonoidalCategory C] (X : GradedObject I C)
    {Y Y' : GradedObject I C} (g : Y ⟶ Y') [HasTensor X Y] [HasTensor X Y'] (n : I) :
    tensorHom (𝟙 X) g n =
      mapMap (((mapBifunctor (curriedTensor C) I I).obj X).map g) (fun x ↦ x.1 + x.2) n := by
  dsimp [tensorHom, mapBifunctorMapMap]
  simp only [Functor.map_id, NatTrans.id_app, Category.id_comp]
  rfl

variable [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C] (X Y : GradedObject ℕ C)
  (hY : IsZero (Y 0)) [HasTensor X Y] [HasTensor X (fun q ↦ Y (q + 1))] (m : ℕ)

/-- For graded objects indexed by `ℕ` with `Y 0 = 0`, the tensor product of `X` with `Y` shifted
down by one in degree `m` is the tensor product of `X` and `Y` in degree `m + 1`: both are the
coproduct of the `X p ⊗ Y (q + 1)` with `p + q = m`. -/
def tensorObjSuccIso : tensorObj X (fun q ↦ Y (q + 1)) m ≅ tensorObj X Y (m + 1) where
  hom := tensorObjDesc fun p q h ↦ ιTensorObj X Y p (q + 1) (m + 1) (by omega)
  inv := tensorObjDesc fun p q h ↦ match q, h with
    | 0, _ => 0
    | q + 1, h => ιTensorObj X (fun q ↦ Y (q + 1)) p q m (by omega)
  hom_inv_id := by ext; simp
  inv_hom_id := by
    ext p q h
    match q, h with
    | 0, _ => exact ((tensorLeft _).map_isZero hY).eq_of_src _ _
    | q + 1, h => simp

/-- `tensorObjSuccIso` sends the summand `X p ⊗ Y (q + 1)` of degree `m` to the same summand of
degree `m + 1`. -/
@[reassoc (attr := simp)]
lemma ι_tensorObjSuccIso_hom (p q : ℕ) (h : p + q = m) :
    ιTensorObj X (fun q ↦ Y (q + 1)) p q m h ≫ (tensorObjSuccIso X Y hY m).hom =
      ιTensorObj X Y p (q + 1) (m + 1) (by omega) := by
  simp [tensorObjSuccIso]

/-- The inverse of `tensorObjSuccIso` sends the summand `X p ⊗ Y (q + 1)` of degree `m + 1` to the
same summand of degree `m`. -/
@[reassoc (attr := simp)]
lemma ι_tensorObjSuccIso_inv (p q : ℕ) (h : p + (q + 1) = m + 1) :
    ιTensorObj X Y p (q + 1) (m + 1) h ≫ (tensorObjSuccIso X Y hY m).inv =
      ιTensorObj X (fun q ↦ Y (q + 1)) p q m (by omega) := by
  simp [tensorObjSuccIso]

variable {X Y} {X' Y' : GradedObject ℕ C} (hY' : IsZero (Y' 0)) [HasTensor X' Y']
  [HasTensor X' (fun q ↦ Y' (q + 1))]

/-- `tensorObjSuccIso` is natural in both graded objects. -/
@[reassoc]
lemma tensorObjSuccIso_hom_naturality (f : X ⟶ X') (g : Y ⟶ Y') :
    (tensorObjSuccIso X Y hY m).hom ≫ tensorHom f g (m + 1) =
      tensorHom f (fun q ↦ g (q + 1)) m ≫ (tensorObjSuccIso X' Y' hY' m).hom := by
  refine tensorObj_ext _ _ fun p q h ↦ ?_
  simp

end Monoidal

end CategoryTheory.GradedObject
