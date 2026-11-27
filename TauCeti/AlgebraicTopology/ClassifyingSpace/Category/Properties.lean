/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Category.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.FundamentalGroupoid
public import TauCeti.AlgebraicTopology.SimplicialSet.Realization.FundamentalGroupoid
import TauCeti.AlgebraicTopology.FundamentalGroupoid.Basic
import TauCeti.CategoryTheory.Category.ULift

/-!
# Further properties and examples of classifying spaces of categories

Building on `TauCeti.AlgebraicTopology.ClassifyingSpace.Category.Basic`, this file establishes
universe changes via `CategoryTheory.nerve.asSmallIso` (`classifyingSpace.asSmallHomeomorph`,
`classifyingSpace.mapOfFunctor`, `classifyingSpace.homeomorphOfStrictIso`), faithfulness
(`CategoryTheory.Functor.classifyingSpaceMap_injective`, `classifyingSpace.mapOfFunctor_injective`,
`TauCeti.CategoryTheory.classifyingSpaceFunctor.Faithful`), non-fullness
(`TauCeti.CategoryTheory.not_full_classifyingSpaceFunctor`), naturality of
`classifyingSpace.toFundamentalGroupoid`
(`classifyingSpace.toFundamentalGroupoidMapOfFunctorNatIso`), vertex injectivity
(`classifyingSpace.vertex_injective`), and identifications for empty, discrete, contractible
linear-order, `Fin 2`, and constant-functor examples.

## References

* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Mathematics 341, Springer, 1973, §1.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, AMS, 2013, Chapter IV, §3.
-/

public section

open CategoryTheory Limits Opposite Simplicial Convexity

universe w u₁ v₁ u₂ v₂ u₃ v₃ v u

namespace CategoryTheory.Functor

open TauCeti.CategoryTheory

lemma classifyingSpaceMap_toTopObjMk {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {n : ℕ} (s : (nerve C) _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    F.classifyingSpaceMap (SSet.toTopObjMk s w) =
      SSet.toTopObjMk ((nerveMap F).app (op ⦋n⦌) s) w :=
  SSet.toTop_map_toTopObjMk (nerveMap F) s w

/-- `Functor.classifyingSpaceMap` is injective on functors. -/
theorem classifyingSpaceMap_injective {C D : Type u} [Category.{v} C] [Category.{v} D] :
    Function.Injective
      (classifyingSpaceMap : (C ⥤ D) → (classifyingSpace C ⟶ classifyingSpace D)) :=
  fun _ _ h ↦ TauCeti.nerveMap_injective (SSet.toTop.map_injective h)

end CategoryTheory.Functor

namespace TauCeti.CategoryTheory

lemma classifyingSpaceFunctor_obj (C : Cat.{v, u}) :
    classifyingSpaceFunctor.obj C = classifyingSpace C := (rfl)

namespace classifyingSpace

section Vertices

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

lemma vertex_eq_toTopPoint (X : C) :
    vertex X = SSet.toTopPoint (nerve.objEquiv.symm (nerveEquiv.symm X)) :=
  congrArg SSet.toTopPoint (nerve.objEquiv_symm_eq (nerveEquiv.symm X)).symm

lemma vertex_eq_toTopObjMk (X : C) (w : StdSimplex ℝ (Fin 1)) :
    vertex X = SSet.toTopObjMk (nerve.objEquiv.symm (nerveEquiv.symm X)) w :=
  (vertex_eq_toTopPoint X).trans (SSet.toTopPoint_eq_toTopObjMk _ w)

@[simp] lemma toTopPoint_objEquiv_symm_nerveEquiv_symm (X : C) :
    SSet.toTopPoint (nerve.objEquiv.symm (nerveEquiv.symm X)) = vertex X :=
  (vertex_eq_toTopPoint X).symm

/-- Distinct objects of `C` give distinct vertices of `classifyingSpace C`. -/
theorem vertex_injective (C : Type u) [Category.{v} C] :
    Function.Injective (vertex (C := C)) :=
  (SSet.toTopPoint_injective (nerve C)).comp nerveEquiv.symm.injective

@[simp] lemma vertex_inj {X Y : C} : vertex X = vertex Y ↔ X = Y := (vertex_injective C).eq_iff

end Vertices

section UniverseChange

/-- Lifting `C` to `AsSmall.{w} C` produces a homeomorphic classifying space. -/
noncomputable def asSmallHomeomorph (C : Type u) [Category.{v} C] :
    classifyingSpace C ≃ₜ classifyingSpace (AsSmall.{w} C) :=
  ((nerve C).toTopUliftHomeomorph.{w}).trans
    (TopCat.homeoOfIso (SSet.toTop.mapIso (nerve.asSmallIso.{w} C).symm))

@[simp] lemma asSmallHomeomorph_toTopObjMk {C : Type u} [Category.{v} C] {n : ℕ}
    (s : (nerve C) _⦋n⦌) (w₀ : StdSimplex ℝ (Fin (n + 1))) :
    asSmallHomeomorph.{w} C (SSet.toTopObjMk s w₀) =
      SSet.toTopObjMk
        (nerve.objEquiv.symm ((AsSmall.up.mapComposableArrows n).obj (nerve.objEquiv s))) w₀ := by
  simp only [asSmallHomeomorph, Homeomorph.trans_apply, TopCat.homeoOfIso_apply,
    Functor.mapIso_symm, Iso.symm_hom, Functor.mapIso_inv]
  rw [SSet.toTopUliftHomeomorph_toTopObjMk, SSet.toTop_map_toTopObjMk, nerve.asSmallIso_inv_app,
    Equiv.symm_apply_apply]

@[simp] lemma asSmallHomeomorph_symm_toTopObjMk {C : Type u} [Category.{v} C] {n : ℕ}
    (s : (nerve (AsSmall.{w} C)) _⦋n⦌) (w₀ : StdSimplex ℝ (Fin (n + 1))) :
    (asSmallHomeomorph.{w} C).symm (SSet.toTopObjMk s w₀) =
      SSet.toTopObjMk
        (nerve.objEquiv.symm ((AsSmall.down.mapComposableArrows n).obj (nerve.objEquiv s))) w₀ := by
  simp only [asSmallHomeomorph, Homeomorph.symm_trans_apply, TopCat.homeoOfIso_symm_apply,
    Functor.mapIso_symm, Iso.symm_inv, Functor.mapIso_hom]
  rw [SSet.toTop_map_toTopObjMk, nerve.asSmallIso_hom_app,
    SSet.toTopUliftHomeomorph_symm_toTopObjMk, Equiv.symm_apply_apply]

@[simp] lemma asSmallHomeomorph_vertex {C : Type u} [Category.{v} C] (X : C) :
    asSmallHomeomorph.{w} C (vertex X) = vertex (AsSmall.up.obj X) := by
  rw [vertex_eq_toTopObjMk X default, asSmallHomeomorph_toTopObjMk]; simp

@[simp] lemma asSmallHomeomorph_symm_vertex {C : Type u} [Category.{v} C] (X : AsSmall.{w} C) :
    (asSmallHomeomorph.{w} C).symm (vertex X) = vertex (AsSmall.down.obj X) := by
  rw [vertex_eq_toTopObjMk X default, asSmallHomeomorph_symm_toTopObjMk]; simp

/-- Continuous map `C(classifyingSpace C, classifyingSpace D)` induced by a functor `F : C ⥤ D`
across arbitrary object and morphism universes. -/
noncomputable def mapOfFunctor {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) : C(classifyingSpace C, classifyingSpace D) :=
  ((asSmallHomeomorph.{max u₁ v₁} D).symm :
      C(classifyingSpace (AsSmall.{max u₁ v₁} D), classifyingSpace D)).comp
    ((Functor.classifyingSpaceMap
        (AsSmall.down (C := C) ⋙ F ⋙ AsSmall.up :
          AsSmall.{max u₂ v₂} C ⥤ AsSmall.{max u₁ v₁} D)).hom.comp
      (asSmallHomeomorph.{max u₂ v₂} C :
        C(classifyingSpace C, classifyingSpace (AsSmall.{max u₂ v₂} C))))

@[simp] lemma mapOfFunctor_toTopObjMk {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) {n : ℕ} (s : (nerve C) _⦋n⦌)
    (w₀ : StdSimplex ℝ (Fin (n + 1))) :
    mapOfFunctor F (SSet.toTopObjMk s w₀) =
      SSet.toTopObjMk (nerve.objEquiv.symm ((F.mapComposableArrows n).obj (nerve.objEquiv s)))
        w₀ := by
  simp [mapOfFunctor, ← Functor.comp_mapComposableArrows_obj,
    AsSmall.up_comp_down_comp_up_comp_down]

@[simp] lemma mapOfFunctor_vertex {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (X : C) :
    mapOfFunctor F (vertex X) = vertex (F.obj X) := by
  rw [vertex_eq_toTopObjMk X default, mapOfFunctor_toTopObjMk]; simp

@[simp] lemma mapOfFunctor_id (C : Type u₁) [Category.{v₁} C] :
    mapOfFunctor (𝟭 C) = ContinuousMap.id (classifyingSpace C) := by
  ext p; obtain ⟨n, s, w₀, rfl⟩ := SSet.exists_toTopObjMk p; simp

@[simp] lemma mapOfFunctor_comp {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E) :
    mapOfFunctor (F ⋙ G) = (mapOfFunctor G).comp (mapOfFunctor F) := by
  ext p; obtain ⟨n, s, w₀, rfl⟩ := SSet.exists_toTopObjMk p; simp

/-- For `C` and `D` in the same universes, `mapOfFunctor F` agrees with
`F.classifyingSpaceMap.hom`. -/
lemma mapOfFunctor_eq_classifyingSpaceMap {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) : mapOfFunctor F = F.classifyingSpaceMap.hom := by
  ext p; obtain ⟨n, s, w₀, rfl⟩ := SSet.exists_toTopObjMk p
  have hs : nerve.objEquiv.symm ((F.mapComposableArrows n).obj (nerve.objEquiv s)) =
      (nerveMap F).app (op ⦋n⦌) s :=
    nerve.objEquiv.injective (by simp)
  simp [hs]

/-- A constant functor `(Functor.const C).obj Y` realizes to the constant map at `vertex Y`. -/
@[simp] lemma _root_.CategoryTheory.Functor.classifyingSpaceMap_const (C D : Type u)
    [Category.{v} C] [Category.{v} D] (Y : D) :
    ((Functor.const C).obj Y).classifyingSpaceMap =
      TopCat.const (X := classifyingSpace C) (vertex Y) := by
  rw [Functor.classifyingSpaceMap, TauCeti.nerveMap_const, SSet.toTop_map_const,
    ← vertex_eq_toTopPoint]

/-- A constant functor `(Functor.const C).obj Y` across arbitrary universes induces the constant
continuous map at `vertex Y`. -/
@[simp] lemma mapOfFunctor_const (C : Type u₁) [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (Y : D) :
    mapOfFunctor ((Functor.const C).obj Y) =
      ContinuousMap.const (classifyingSpace C) (vertex Y) := by
  ext p
  have hconst : (AsSmall.down (C := C) ⋙ (Functor.const C).obj Y ⋙ AsSmall.up :
      AsSmall.{max u₂ v₂} C ⥤ AsSmall.{max u₁ v₁} D) =
      (Functor.const _).obj (AsSmall.up.obj Y) :=
    CategoryTheory.Functor.ext (fun _ ↦ rfl) fun _ _ _ ↦ by
      simp only [Functor.comp_map, Functor.const_obj_map, eqToHom_refl, Category.id_comp,
        Category.comp_id]
      exact CategoryTheory.Functor.map_id _ _
  simp [mapOfFunctor, hconst]

/-- `mapOfFunctor` is injective on functors across arbitrary object and morphism universes. -/
theorem mapOfFunctor_injective {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] :
    Function.Injective (mapOfFunctor : (C ⥤ D) → C(classifyingSpace C, classifyingSpace D)) := by
  intro F G h
  have hmap : Functor.classifyingSpaceMap
      (AsSmall.down (C := C) ⋙ F ⋙ AsSmall.up :
        AsSmall.{max u₂ v₂} C ⥤ AsSmall.{max u₁ v₁} D) =
      Functor.classifyingSpaceMap (AsSmall.down (C := C) ⋙ G ⋙ AsSmall.up) := by
    ext q
    obtain ⟨p, rfl⟩ := (asSmallHomeomorph.{max u₂ v₂} C).surjective q
    exact (asSmallHomeomorph.{max u₁ v₁} D).symm.injective
      (by simpa [mapOfFunctor] using congrArg (· p) h)
  simpa only [AsSmall.up_comp_down_comp_up_comp_down] using
    congrArg (fun H ↦ (AsSmall.up ⋙ H) ⋙ AsSmall.down)
      (Functor.classifyingSpaceMap_injective hmap)

/-- Strictly mutually inverse functors `F : C ⥤ D` and `G : D ⥤ C` induce a homeomorphism on
classifying spaces. -/
noncomputable def homeomorphOfStrictIso {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (G : D ⥤ C)
    (hFG : F ⋙ G = 𝟭 C) (hGF : G ⋙ F = 𝟭 D) :
    classifyingSpace C ≃ₜ classifyingSpace D where
  toFun := mapOfFunctor F
  invFun := mapOfFunctor G
  left_inv p := congrArg (· p) ((mapOfFunctor_comp F G).symm.trans (by rw [hFG, mapOfFunctor_id]))
  right_inv q := congrArg (· q) ((mapOfFunctor_comp G F).symm.trans (by rw [hGF, mapOfFunctor_id]))
  continuous_toFun := (mapOfFunctor F).continuous
  continuous_invFun := (mapOfFunctor G).continuous

@[simp] lemma homeomorphOfStrictIso_apply {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (G : D ⥤ C) (hFG : F ⋙ G = 𝟭 C)
    (hGF : G ⋙ F = 𝟭 D) (p : classifyingSpace C) :
    homeomorphOfStrictIso F G hFG hGF p = mapOfFunctor F p := (rfl)

@[simp] lemma homeomorphOfStrictIso_symm_apply {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (G : D ⥤ C) (hFG : F ⋙ G = 𝟭 C)
    (hGF : G ⋙ F = 𝟭 D) (q : classifyingSpace D) :
    (homeomorphOfStrictIso F G hFG hGF).symm q = mapOfFunctor G q := (rfl)

/-- Conjugating `mapOfFunctor H` by `homeomorphOfStrictIso F G` equals
`mapOfFunctor (G ⋙ H ⋙ F)`. -/
lemma mapOfFunctor_conj_of_strictIso {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (G : D ⥤ C)
    (hFG : F ⋙ G = 𝟭 C) (hGF : G ⋙ F = 𝟭 D) (H : C ⥤ C) :
    mapOfFunctor (G ⋙ H ⋙ F) =
      ((homeomorphOfStrictIso F G hFG hGF : C(classifyingSpace C, classifyingSpace D)).comp
        ((mapOfFunctor H).comp
          ((homeomorphOfStrictIso F G hFG hGF).symm :
            C(classifyingSpace D, classifyingSpace C)))) := by
  ext p
  simp [mapOfFunctor_comp]

end UniverseChange

section EdgesAndFundamentalGroupoid

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

lemma edge_apply {X Y : C} (f : X ⟶ Y) (t : unitInterval) :
    edge f t =
      SSet.toTopObjMk (nerve.objEquiv.symm (ComposableArrows.mk₁ f))
        (StdSimplex.homeomorphI.symm t) := by
  rw [edge_eq_toTopPath]
  exact ((nerve.edgeMk f).toTopPath_apply t).trans
    (congrArg (SSet.toTopObjMk · _) (nerve.objEquiv_symm_eq _).symm)

/-- Pushing `edge f` forward along `mapOfFunctor F` gives `edge (F.map f)` up to `Path.cast`. -/
lemma edge_mapOfFunctor {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    edge (F.map f) =
      ((edge f).map (mapOfFunctor F).continuous).cast
        (mapOfFunctor_vertex F X).symm (mapOfFunctor_vertex F Y).symm := by
  ext t
  rw [edge_apply, Path.cast_coe, Path.map_coe, Function.comp_apply, edge_apply,
    mapOfFunctor_toTopObjMk, Equiv.apply_symm_apply, Functor.mapComposableArrows_obj_mk₁]

/-- Naturality isomorphism comparing `toFundamentalGroupoid` along `F : C ⥤ D` across arbitrary
universes with `FundamentalGroupoid.map (mapOfFunctor F)`. -/
noncomputable def toFundamentalGroupoidMapOfFunctorNatIso {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) :
    F ⋙ toFundamentalGroupoid D ≅
      toFundamentalGroupoid C ⋙ FundamentalGroupoid.map (mapOfFunctor F) :=
  NatIso.ofComponents
    (fun X ↦ eqToIso (_root_.FundamentalGroupoid.ext (mapOfFunctor_vertex F X).symm))
    fun f ↦ by
      dsimp only [Functor.comp_obj, Functor.comp_map]
      rw [toFundamentalGroupoid_map, toFundamentalGroupoid_map]
      exact _root_.FundamentalGroupoid.fromPath_naturality_eqToHom (φ := mapOfFunctor F)
        (mapOfFunctor_vertex F _) (mapOfFunctor_vertex F _)
        (edge f) (edge (F.map f)) (edge_mapOfFunctor F f)

@[simp] lemma toFundamentalGroupoidMapOfFunctorNatIso_hom_app {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (X : C) :
    (toFundamentalGroupoidMapOfFunctorNatIso F).hom.app X = eqToHom (by ext; simp) := (rfl)

@[simp] lemma toFundamentalGroupoidMapOfFunctorNatIso_inv_app {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (X : C) :
    (toFundamentalGroupoidMapOfFunctorNatIso F).inv.app X = eqToHom (by ext; simp) := (rfl)

end EdgesAndFundamentalGroupoid

section Examples

/-- The classifying space `classifyingSpace C` is nonempty if and only if `C` is nonempty. -/
lemma nonempty_iff (C : Type u) [Category.{v} C] :
    Nonempty (classifyingSpace C) ↔ Nonempty C :=
  (SSet.nonempty_toTop_iff (nerve C)).trans nerveEquiv.nonempty_congr

/-- The classifying space `classifyingSpace C` is empty if and only if `C` is empty. -/
lemma isEmpty_iff (C : Type u) [Category.{v} C] :
    IsEmpty (classifyingSpace C) ↔ IsEmpty C := by
  rw [← not_nonempty_iff, nonempty_iff, not_nonempty_iff]

/-- For `[IsDiscrete C]`, `classifyingSpace C` is isomorphic in `TopCat` to discrete `ULift.{v} C`.
-/
noncomputable def isDiscreteIso (C : Type u) [Category.{v} C] [IsDiscrete C] :
    classifyingSpace C ≅ TopCat.discrete.obj (ULift.{v} C) :=
  SSet.toTop.mapIso (nerve.isDiscreteIso C) ≪≫ SSet.toTopConstIso (ULift.{v} C)

@[simp] lemma isDiscreteIso_hom_vertex {C : Type u} [Category.{v} C] [IsDiscrete C] (X : C) :
    (isDiscreteIso C).hom (vertex X) = ULift.up X := by
  rw [isDiscreteIso, Iso.trans_hom, ConcreteCategory.comp_apply, Functor.mapIso_hom,
    vertex_eq_toTopPoint, SSet.toTop_map_toTopPoint, nerve.isDiscreteIso_hom_app,
    Equiv.apply_symm_apply, nerveEquiv_symm_obj, SSet.toTopConstIso_hom_toTopPoint]

@[simp] lemma isDiscreteIso_inv_apply {C : Type u} [Category.{v} C] [IsDiscrete C]
    (x : ULift.{v} C) : (isDiscreteIso C).inv x = vertex x.down := by
  rw [isDiscreteIso, Iso.trans_inv, Functor.mapIso_inv,
    ConcreteCategory.comp_apply (X := TopCat.discrete.obj (ULift.{v} C)) _ _ x,
    SSet.toTopConstIso_inv_apply, SSet.toTop_map_toTopPoint, nerve.isDiscreteIso_inv_app,
    ← nerveEquiv_symm_eq_const, ← vertex_eq_toTopPoint]

/-- For `[IsDiscrete C]`, `classifyingSpace C` is homeomorphic to discrete `C`. -/
noncomputable def isDiscreteHomeomorph (C : Type u) [Category.{v} C] [IsDiscrete C] :
    classifyingSpace C ≃ₜ TopCat.discrete.obj C :=
  (TopCat.homeoOfIso (isDiscreteIso C)).trans <|
    Equiv.toHomeomorphOfDiscrete (X := TopCat.discrete.obj (ULift.{v} C))
      (Y := TopCat.discrete.obj C) Equiv.ulift

@[simp] lemma isDiscreteHomeomorph_vertex {C : Type u} [Category.{v} C] [IsDiscrete C] (X : C) :
    isDiscreteHomeomorph C (vertex X) = X := by
  rw [isDiscreteHomeomorph, Homeomorph.trans_apply, TopCat.homeoOfIso_apply,
    isDiscreteIso_hom_vertex]
  -- Unfolds `Equiv.toHomeomorphOfDiscrete` and `Equiv.ulift` on `ULift.up X`.
  rfl

@[simp] lemma isDiscreteHomeomorph_symm_apply {C : Type u} [Category.{v} C] [IsDiscrete C]
    (X : TopCat.discrete.obj C) : (isDiscreteHomeomorph C).symm X = vertex (C := C) X :=
  (isDiscreteHomeomorph C).injective
    (((isDiscreteHomeomorph C).apply_symm_apply X).trans
      (isDiscreteHomeomorph_vertex (C := C) X).symm)

instance instDiscreteTopology (C : Type u) [Category.{v} C] [IsDiscrete C] :
    DiscreteTopology (classifyingSpace C) :=
  (isDiscreteHomeomorph C).isEmbedding.discreteTopology

/-- The classifying space of a discrete category with a unique object has unique point
`vertex default`. -/
noncomputable instance instUnique (C : Type u) [Category.{v} C] [Unique C] [IsDiscrete C] :
    Unique (classifyingSpace C) where
  default := vertex default
  uniq _ := (isDiscreteHomeomorph C).injective (Subsingleton.elim (α := C) _ _)

@[simp] lemma vertex_default_eq_default (C : Type u) [Category.{v} C] [Unique C] [IsDiscrete C] :
    vertex (default : C) = default := (rfl)

/-- Homeomorphism between `classifyingSpace (Discrete S)` and discrete `S`. -/
noncomputable def discreteHomeomorph (S : Type u) :
    classifyingSpace (Discrete S) ≃ₜ TopCat.discrete.obj S :=
  (isDiscreteHomeomorph (Discrete S)).trans
    (Equiv.toHomeomorphOfDiscrete (X := TopCat.discrete.obj (Discrete S))
      (Y := TopCat.discrete.obj S) discreteEquiv)

@[simp] lemma discreteHomeomorph_vertex (S : Type u) (s : S) :
    discreteHomeomorph S (vertex (Discrete.mk s)) = s := by
  rw [discreteHomeomorph, Homeomorph.trans_apply, isDiscreteHomeomorph_vertex]
  -- Unfolds `Equiv.toHomeomorphOfDiscrete` and `discreteEquiv` (`Discrete.as (Discrete.mk s) = s`).
  rfl

@[simp] lemma discreteHomeomorph_symm_apply (S : Type u) (s : TopCat.discrete.obj S) :
    (discreteHomeomorph S).symm s = vertex (Discrete.mk s) :=
  (discreteHomeomorph S).injective
    (((discreteHomeomorph S).apply_symm_apply s).trans
      (discreteHomeomorph_vertex S s).symm)

/-- A preorder order-isomorphic to `Fin (n + 1)` has classifying space homeomorphic to
`StdSimplex ℝ (Fin (n + 1))`. -/
noncomputable def preorderHomeomorphStdSimplex {n : ℕ} {α : Type u} [Preorder α]
    (e : α ≃o Fin (n + 1)) : classifyingSpace α ≃ₜ StdSimplex ℝ (Fin (n + 1)) :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso
    (SSet.stdSimplex.isoOfRepresentableBy (nerve.representableBy α e)).symm)).trans
    ⦋n⦌.toTopHomeo.{u}

@[simp] lemma preorderHomeomorphStdSimplex_toTopObjMk {n m : ℕ} {α : Type u} [Preorder α]
    (e : α ≃o Fin (n + 1)) (s : (nerve α) _⦋m⦌) (w : StdSimplex ℝ (Fin (m + 1))) :
    preorderHomeomorphStdSimplex e (SSet.toTopObjMk s w) =
      w.map fun i ↦ e ((nerve.objEquiv s).obj i) := by
  have hf : Monotone fun i : Fin (m + 1) ↦ e ((nerve.objEquiv s).obj i) :=
    fun _ _ hij ↦ e.monotone (leOfHom ((nerve.objEquiv s).map (homOfLE hij)))
  let θ : ⦋m⦌ ⟶ ⦋n⦌ := ConcreteCategory.ofHom ⟨_, hf⟩
  have hθ : (nerve.representableBy α e).homEquiv θ = s :=
    nerve.objEquiv.injective <| ComposableArrows.ext
      (fun i ↦ by
        change (nerve.objEquiv ((nerve.representableBy α e).homEquiv θ)).obj i =
          (nerve.objEquiv s).obj i
        rw [nerve.representableBy_homEquiv_obj]
        exact e.symm_apply_apply _)
      (fun _ _ ↦ Subsingleton.elim _ _)
  have hinv : (SSet.stdSimplex.isoOfRepresentableBy (nerve.representableBy α e)).inv.app (op ⦋m⦌)
      s = SSet.stdSimplex.objEquiv.{u}.symm θ := by
    simp [SSet.stdSimplex.isoOfRepresentableBy, ← hθ]
  simp [preorderHomeomorphStdSimplex, hinv, θ, OrderHom.coe_mk]

lemma preorderHomeomorphStdSimplex_symm_eq_toTopObjMk {n : ℕ} {α : Type u} [Preorder α]
    (e : α ≃o Fin (n + 1)) (w : StdSimplex ℝ (Fin (n + 1))) :
    (preorderHomeomorphStdSimplex e).symm w =
      SSet.toTopObjMk (nerve.objEquiv.symm e.symm.monotone.functor) w := by
  apply (preorderHomeomorphStdSimplex e).injective
  rw [Homeomorph.apply_symm_apply, preorderHomeomorphStdSimplex_toTopObjMk, Equiv.apply_symm_apply]
  simpa [Function.id_def] using (StdSimplex.map_id w).symm

@[simp] lemma preorderHomeomorphStdSimplex_vertex {n : ℕ} {α : Type u} [Preorder α]
    (e : α ≃o Fin (n + 1)) (a : α) :
    preorderHomeomorphStdSimplex e (vertex a) = StdSimplex.single (e a) := by
  rw [vertex_eq_toTopObjMk a (StdSimplex.single 0), preorderHomeomorphStdSimplex_toTopObjMk,
    Equiv.apply_symm_apply, StdSimplex.map_single, nerveEquiv_symm_obj]

@[simp] lemma preorderHomeomorphStdSimplex_symm_single {n : ℕ} {α : Type u} [Preorder α]
    (e : α ≃o Fin (n + 1)) (i : Fin (n + 1)) :
    (preorderHomeomorphStdSimplex e).symm (StdSimplex.single i) = vertex (e.symm i) :=
  (preorderHomeomorphStdSimplex e).injective (by simp)

/-- The classifying space of a preorder order-isomorphic to `Fin (n + 1)` is contractible. -/
lemma contractibleSpace_of_orderIso_fin {n : ℕ} {α : Type u} [Preorder α]
    (e : α ≃o Fin (n + 1)) : ContractibleSpace (classifyingSpace α) :=
  (preorderHomeomorphStdSimplex e).contractibleSpace

/-- The classifying space of any finite nonempty linear order is contractible. -/
instance (α : Type u) [LinearOrder α] [Finite α] [Nonempty α] :
    ContractibleSpace (classifyingSpace α) := by
  cases nonempty_fintype α
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := α))
  exact contractibleSpace_of_orderIso_fin (Fintype.orderIsoFinOfCardEq α hn).symm

/-- The classifying space of `Fin 2` is homeomorphic to `unitInterval`, sending `vertex 0` to `0`
and `vertex 1` to `1`. -/
noncomputable def finTwoHomeomorphI : classifyingSpace (Fin 2) ≃ₜ unitInterval :=
  (preorderHomeomorphStdSimplex (OrderIso.refl (Fin 2))).trans StdSimplex.homeomorphI

@[simp] lemma finTwoHomeomorphI_toTopObjMk {m : ℕ} (s : (nerve (Fin 2)) _⦋m⦌)
    (w : StdSimplex ℝ (Fin (m + 1))) :
    finTwoHomeomorphI (SSet.toTopObjMk s w) =
      StdSimplex.homeomorphI (w.map ((nerve.objEquiv s).obj)) := by
  simp [finTwoHomeomorphI]

@[simp] lemma finTwoHomeomorphI_vertex_zero : finTwoHomeomorphI (vertex (0 : Fin 2)) = 0 := by
  simp [finTwoHomeomorphI]

@[simp] lemma finTwoHomeomorphI_vertex_one : finTwoHomeomorphI (vertex (1 : Fin 2)) = 1 := by
  simp [finTwoHomeomorphI]

@[simp] lemma finTwoHomeomorphI_symm_zero : finTwoHomeomorphI.symm 0 = vertex (0 : Fin 2) :=
  finTwoHomeomorphI.injective (by simp)

@[simp] lemma finTwoHomeomorphI_symm_one : finTwoHomeomorphI.symm 1 = vertex (1 : Fin 2) :=
  finTwoHomeomorphI.injective (by simp)

@[simp] lemma finTwoHomeomorphI_edge_apply (f : (0 : Fin 2) ⟶ 1) (t : unitInterval) :
    finTwoHomeomorphI (edge f t) = t := by
  have hid : (ComposableArrows.mk₁ f).obj = (id : Fin 2 → Fin 2) := by funext i; fin_cases i <;> rfl
  rw [edge_apply, finTwoHomeomorphI_toTopObjMk, Equiv.apply_symm_apply, hid,
    StdSimplex.map_id, Homeomorph.apply_symm_apply]

lemma finTwoHomeomorphI_symm_apply (t : unitInterval) :
    finTwoHomeomorphI.symm t = edge (homOfLE (zero_le_one' (Fin 2))) t :=
  finTwoHomeomorphI.injective (by simp)

lemma coe_finTwoHomeomorphI_symm :
    ⇑finTwoHomeomorphI.symm = edge (homOfLE (zero_le_one' (Fin 2))) :=
  funext finTwoHomeomorphI_symm_apply

/-- Reflection of `classifyingSpace (Fin 2)` swapping `vertex 0` and `vertex 1`. -/
noncomputable def finTwoReflect : classifyingSpace (Fin 2) ⟶ classifyingSpace (Fin 2) :=
  (TopCat.isoOfHomeo
    ((finTwoHomeomorphI.trans unitInterval.symmHomeomorph).trans finTwoHomeomorphI.symm)).hom

lemma finTwoReflect_apply (p : classifyingSpace (Fin 2)) :
    finTwoReflect p = finTwoHomeomorphI.symm (unitInterval.symm (finTwoHomeomorphI p)) := by
  simp [finTwoReflect]

@[simp] lemma finTwoHomeomorphI_finTwoReflect (p : classifyingSpace (Fin 2)) :
    finTwoHomeomorphI (finTwoReflect p) = unitInterval.symm (finTwoHomeomorphI p) := by
  rw [finTwoReflect_apply, Homeomorph.apply_symm_apply]

@[simp] lemma finTwoReflect_vertex_zero : finTwoReflect (vertex (0 : Fin 2)) = vertex 1 := by
  simp [finTwoReflect_apply]

@[simp] lemma finTwoReflect_vertex_one : finTwoReflect (vertex (1 : Fin 2)) = vertex 0 := by
  simp [finTwoReflect_apply]

/-- `finTwoReflect` is not `F.classifyingSpaceMap` for any `F : Fin 2 ⥤ Fin 2`. -/
theorem not_exists_classifyingSpaceMap_eq_finTwoReflect :
    ¬ ∃ F : Fin 2 ⥤ Fin 2, F.classifyingSpaceMap = finTwoReflect := by
  rintro ⟨F, hF⟩
  have h0 : F.obj 0 = 1 :=
    vertex_inj.1 (by simpa using ConcreteCategory.congr_hom hF (vertex (0 : Fin 2)))
  have h1 : F.obj 1 = 0 :=
    vertex_inj.1 (by simpa using ConcreteCategory.congr_hom hF (vertex (1 : Fin 2)))
  have hle : F.obj 0 ≤ F.obj 1 := leOfHom (F.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)))
  rw [h0, h1] at hle
  exact absurd hle (by decide)

end Examples

end classifyingSpace

/-- The classifying space functor `Cat.{v, u} ⥤ TopCat.{max u v}` is faithful. -/
instance : classifyingSpaceFunctor.{v, u}.Faithful :=
  inferInstanceAs (nerveFunctor.{v, u} ⋙ SSet.toTop).Faithful

/-- Whenever `C` has `Y ≠ X`, `(𝟭 C).classifyingSpaceMap` differs from
`((Functor.const C).obj X).classifyingSpaceMap`. -/
lemma classifyingSpaceMap_id_ne_const {C : Type u} [Category.{v} C] {X Y : C} (hne : Y ≠ X) :
    (𝟭 C).classifyingSpaceMap ≠ ((Functor.const C).obj X).classifyingSpaceMap := fun h ↦ by
  have hy := ConcreteCategory.congr_hom h (classifyingSpace.vertex Y)
  rw [Functor.classifyingSpaceMap_vertex, Functor.classifyingSpaceMap_const, Functor.id_obj,
    TopCat.const_apply, classifyingSpace.vertex_inj] at hy
  exact hne hy

attribute [local instance] uliftCategory in
/-- The classifying space functor `Cat.{v, u} ⥤ TopCat.{max u v}` is not full in any universes
`v, u`. -/
theorem not_full_classifyingSpaceFunctor : ¬ classifyingSpaceFunctor.{v, u}.Full := by
  intro hFull
  let C₀ : Type u := ULift.{u} (ULiftHom.{v} (Fin 2))
  let toFin : C₀ ⥤ Fin 2 := _root_.CategoryTheory.ULift.downFunctor ⋙ ULiftHom.down
  let fromFin : Fin 2 ⥤ C₀ := ULiftHom.up ⋙ _root_.CategoryTheory.ULift.upFunctor
  have hTF : toFin ⋙ fromFin = 𝟭 C₀ :=
    CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ ULift.ext (Subsingleton.elim _ _))
  have hFT : fromFin ⋙ toFin = 𝟭 (Fin 2) :=
    CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _)
  let e : classifyingSpace C₀ ≃ₜ classifyingSpace (Fin 2) :=
    classifyingSpace.homeomorphOfStrictIso toFin fromFin hTF hFT
  let reflMor : classifyingSpace C₀ ⟶ classifyingSpace C₀ :=
    TopCat.ofHom ((e.symm : C(classifyingSpace (Fin 2), classifyingSpace C₀)).comp
      (classifyingSpace.finTwoReflect.hom.comp
        (e : C(classifyingSpace C₀, classifyingSpace (Fin 2)))))
  obtain ⟨G, hG⟩ := classifyingSpaceFunctor.map_surjective (X := Cat.of C₀) (Y := Cat.of C₀)
    reflMor
  refine classifyingSpace.not_exists_classifyingSpaceMap_eq_finTwoReflect
    ⟨fromFin ⋙ G.toFunctor ⋙ toFin, TopCat.hom_ext ?_⟩
  rw [← classifyingSpace.mapOfFunctor_eq_classifyingSpaceMap,
    classifyingSpace.mapOfFunctor_conj_of_strictIso toFin fromFin hTF hFT G.toFunctor,
    classifyingSpace.mapOfFunctor_eq_classifyingSpaceMap G.toFunctor,
    ← classifyingSpaceFunctor_map, hG]
  simp only [reflMor, e, TopCat.hom_ofHom, ← ContinuousMap.comp_assoc,
    Homeomorph.toContinuousMap_comp_symm, ContinuousMap.id_comp]
  rw [ContinuousMap.comp_assoc, Homeomorph.toContinuousMap_comp_symm, ContinuousMap.comp_id]

end TauCeti.CategoryTheory
