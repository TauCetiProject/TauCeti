/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Summand
public import Mathlib.Algebra.Homology.Additive
public import TauCeti.CategoryTheory.Monoidal.ProjectionFormula

/-!
# The projection formula for homological complexes

For preadditive monoidal categories whose tensors are additive in each variable, a natural
projection isomorphism `L (G X ⊗ Y) ≅ X ⊗ L Y` extends to homological complexes of any
shape with tensor signs when `G` preserves zero morphisms and `L` is additive and preserves
the coproducts along the tensor diagonals.
The comparison uses the existing tensor differential, including its Koszul sign.
Only the tensor products of the complexes involved are required to exist.

This is the projection formula for complexes used to transfer K-flatness through an exact
restriction functor with exact extension by zero. See Stacks Project, Lemmas 18.27.9
(Tag 0E8I) and 21.17.4 (Tag 0E8K). The construction uses Mathlib's tensor totalization
of Joël Riou and Kim Morrison and its coproduct comparison.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D]
  [MonoidalCategory C] [MonoidalCategory D]
  [(curriedTensor C).Additive] [∀ X : C, ((curriedTensor C).obj X).Additive]
  [(curriedTensor D).Additive] [∀ X : D, ((curriedTensor D).obj X).Additive]
  (L : D ⥤ C) (G : C ⥤ D) [L.Additive] [G.PreservesZeroMorphisms]
  (e : G.prod (𝟭 D) ⋙ tensor D ⋙ L ≅ (𝟭 C).prod L ⋙ tensor C)

variable {I : Type*} [AddMonoid I] [DecidableEq I] {c : ComplexShape I} [c.TensorSigns]

section Pair

variable (K : HomologicalComplex C c) (E : HomologicalComplex D c)
  [HasTensor ((G.mapHomologicalComplex c).obj K) E]
  [HasTensor K ((L.mapHomologicalComplex c).obj E)]
  [∀ n : I, PreservesColimit (Discrete.functor
    (fun pq : { pq : I × I // pq.1 + pq.2 = n } ↦ G.obj (K.X pq.val.1) ⊗ E.X pq.val.2)) L]

include G e in
omit [HasTensor K ((L.mapHomologicalComplex c).obj E)] [DecidableEq I] in
/-- If the source tensor product exists, a projection formula and preservation by `L` of its
diagonal coproducts give existence of the target tensor product. No chosen target tensor
instance is required. -/
lemma hasTensor_of_projectionFormula :
    HasTensor K ((L.mapHomologicalComplex c).obj E) := by
  intro n
  let f := fun pq : { pq : I × I // pq.1 + pq.2 = n } ↦
    G.obj (K.X pq.val.1) ⊗ E.X pq.val.2
  let : HasCoproduct f :=
    (inferInstance : HasTensor ((G.mapHomologicalComplex c).obj K) E) n
  let : HasCoproduct (fun pq ↦ L.obj (f pq)) :=
    HasColimit.mk ⟨_, isColimitOfHasCoproductOfPreservesColimit L f⟩
  let α : Discrete.functor (fun pq ↦ L.obj (f pq)) ≅ Discrete.functor
      (fun pq : { pq : I × I // pq.1 + pq.2 = n } ↦ K.X pq.val.1 ⊗ L.obj (E.X pq.val.2)) :=
    Discrete.natIso (fun pq ↦ e.app (K.X pq.as.val.1, E.X pq.as.val.2))
  exact hasColimit_of_iso (F := Discrete.functor (fun pq ↦ L.obj (f pq))) α.symm

/-- The degreewise projection isomorphism, obtained from the diagonal coproduct comparison. -/
private def projectionFormulaHomologicalComplexXIso (n : I) :
    L.obj ((tensorObj ((G.mapHomologicalComplex c).obj K) E).X n) ≅
      (tensorObj K ((L.mapHomologicalComplex c).obj E)).X n := by
  let f := fun pq : { pq : I × I // pq.1 + pq.2 = n } ↦
    G.obj (K.X pq.val.1) ⊗ E.X pq.val.2
  let g := fun pq : { pq : I × I // pq.1 + pq.2 = n } ↦
    K.X pq.val.1 ⊗ L.obj (E.X pq.val.2)
  let α : Discrete.functor (fun pq ↦ L.obj (f pq)) ≅ Discrete.functor g :=
    Discrete.natIso (fun pq ↦ e.app (K.X pq.as.val.1, E.X pq.as.val.2))
  letI : HasCoproduct f :=
    (inferInstance : HasTensor ((G.mapHomologicalComplex c).obj K) E) n
  letI : HasCoproduct g :=
    (inferInstance : HasTensor K ((L.mapHomologicalComplex c).obj E)) n
  exact IsColimit.coconePointsIsoOfNatIso
    (isColimitOfHasCoproductOfPreservesColimit L f) (colimit.isColimit (Discrete.functor g)) α

@[reassoc]
private lemma ι_projectionFormulaHomologicalComplexXIso_inv (p q n : I) (h : p + q = n) :
    ιTensorObj K ((L.mapHomologicalComplex c).obj E) p q n h ≫
        (L.projectionFormulaHomologicalComplexXIso G e K E n).inv =
      (e.app (K.X p, E.X q)).inv ≫
        L.map (ιTensorObj ((G.mapHomologicalComplex c).obj K) E p q n h) := by
  dsimp only [projectionFormulaHomologicalComplexXIso]
  exact IsColimit.comp_coconePointsIsoOfNatIso_inv _ _ _
    (Discrete.mk (⟨(p, q), h⟩ : { pq : I × I // pq.1 + pq.2 = n }))

private lemma projectionFormulaHomologicalComplexXIso_inv_d₁ (p q m : I) :
    mapBifunctor.d₁ K ((L.mapHomologicalComplex c).obj E) (curriedTensor C) c p q m ≫
        (L.projectionFormulaHomologicalComplexXIso G e K E m).inv =
      (e.app (K.X p, E.X q)).inv ≫
        L.map (mapBifunctor.d₁ ((G.mapHomologicalComplex c).obj K) E
          (curriedTensor D) c p q m) := by
  by_cases hp : c.Rel p (c.next p)
  · by_cases hm : c.next p + q = m
    · simp only [mapBifunctor.d₁_eq (c₂ := c) _ _ _ c hp q m hm, Units.smul_def,
        Preadditive.zsmul_comp, Preadditive.comp_zsmul, L.map_zsmul,
        curriedTensor_map_app, Category.assoc, ι_projectionFormulaHomologicalComplexXIso_inv,
        mapHomologicalComplex_obj_d, L.map_comp]
      simpa only [map_id, MonoidalCategory.tensorHom_id, comp_obj, prod_obj, id_obj,
        mapHomologicalComplex_obj_X, curriedTensor_obj_obj] using congrArg
        (fun f ↦ (ComplexShape.ε₁ c c c (p, q)).val • f)
        (projectionFormula_inv_naturality_assoc L G e (K.d p (c.next p)) (𝟙 (E.X q))
          (L.map (ιTensorObj ((G.mapHomologicalComplex c).obj K) E (c.next p) q m hm)))
    · simp [mapBifunctor.d₁_eq_zero' (c₂ := c) _ _ _ c hp q m hm]
  · simp [mapBifunctor.d₁_eq_zero _ _ _ _ p q m hp]

private lemma projectionFormulaHomologicalComplexXIso_inv_d₂ (p q m : I) :
    mapBifunctor.d₂ K ((L.mapHomologicalComplex c).obj E) (curriedTensor C) c p q m ≫
        (L.projectionFormulaHomologicalComplexXIso G e K E m).inv =
      (e.app (K.X p, E.X q)).inv ≫
        L.map (mapBifunctor.d₂ ((G.mapHomologicalComplex c).obj K) E
          (curriedTensor D) c p q m) := by
  by_cases hq : c.Rel q (c.next q)
  · by_cases hm : p + c.next q = m
    · simp only [mapBifunctor.d₂_eq (c₁ := c) _ _ _ c p hq m hm, Units.smul_def,
        Preadditive.zsmul_comp, Preadditive.comp_zsmul, L.map_zsmul,
        curriedTensor_obj_map, Category.assoc, ι_projectionFormulaHomologicalComplexXIso_inv,
        mapHomologicalComplex_obj_d, L.map_comp]
      simpa only [map_id, MonoidalCategory.id_tensorHom, comp_obj, prod_obj, id_obj,
        mapHomologicalComplex_obj_X, curriedTensor_obj_obj] using congrArg
        (fun f ↦ (ComplexShape.ε₂ c c c (p, q)).val • f)
        (projectionFormula_inv_naturality_assoc L G e (𝟙 (K.X p)) (E.d q (c.next q))
          (L.map (ιTensorObj ((G.mapHomologicalComplex c).obj K) E p (c.next q) m hm)))
    · simp [mapBifunctor.d₂_eq_zero' (c₁ := c) _ _ _ c p hq m hm]
  · simp [mapBifunctor.d₂_eq_zero _ _ _ _ p q m hq]

private lemma projectionFormulaHomologicalComplexXIso_inv_comm (n m : I) :
    (L.projectionFormulaHomologicalComplexXIso G e K E n).inv ≫
        L.map ((tensorObj ((G.mapHomologicalComplex c).obj K) E).d n m) =
      (tensorObj K ((L.mapHomologicalComplex c).obj E)).d n m ≫
        (L.projectionFormulaHomologicalComplexXIso G e K E m).inv := by
  refine mapBifunctor.hom_ext fun p q hpq ↦ ?_
  simp only [ι_projectionFormulaHomologicalComplexXIso_inv_assoc, ← L.map_comp,
    mapBifunctor.d_eq, Preadditive.comp_add, Preadditive.add_comp, L.map_add,
    mapBifunctor.ι_D₁, mapBifunctor.ι_D₂, mapBifunctor.ι_D₁_assoc, mapBifunctor.ι_D₂_assoc,
    projectionFormulaHomologicalComplexXIso_inv_d₁,
    projectionFormulaHomologicalComplexXIso_inv_d₂]

/-- A natural projection isomorphism lifts to homological complexes of any shape with tensor
signs when both categories have biadditive tensors, `G` preserves zero morphisms, and `L`
is additive and preserves the diagonal coproducts. Both tensor products must exist; the
target existence can be obtained from `hasTensor_of_projectionFormula`. -/
def projectionFormulaHomologicalComplexIso :
    (L.mapHomologicalComplex c).obj
        (tensorObj ((G.mapHomologicalComplex c).obj K) E) ≅
      tensorObj K ((L.mapHomologicalComplex c).obj E) :=
  (Hom.isoOfComponents (fun n ↦ (L.projectionFormulaHomologicalComplexXIso G e K E n).symm)
    (fun n m _ ↦ L.projectionFormulaHomologicalComplexXIso_inv_comm G e K E n m)).symm

/-- The inverse projection formula for complexes on each tensor inclusion. -/
@[reassoc (attr := simp)]
lemma ι_projectionFormulaHomologicalComplexIso_inv_f (p q n : I) (h : p + q = n) :
    ιTensorObj K ((L.mapHomologicalComplex c).obj E) p q n h ≫
        (L.projectionFormulaHomologicalComplexIso G e K E).inv.f n =
      (e.app (K.X p, E.X q)).inv ≫
        L.map (ιTensorObj ((G.mapHomologicalComplex c).obj K) E p q n h) :=
  L.ι_projectionFormulaHomologicalComplexXIso_inv G e K E p q n h

/-- On a homogeneous tensor summand the projection formula for complexes is the supplied
projection formula on the two terms. -/
@[reassoc (attr := simp)]
lemma map_ι_projectionFormulaHomologicalComplexIso_hom_f (p q n : I) (h : p + q = n) :
    L.map (ιTensorObj ((G.mapHomologicalComplex c).obj K) E p q n h) ≫
        (L.projectionFormulaHomologicalComplexIso G e K E).hom.f n =
      (e.app (K.X p, E.X q)).hom ≫
        ιTensorObj K ((L.mapHomologicalComplex c).obj E) p q n h := by
  apply (cancel_mono ((L.projectionFormulaHomologicalComplexIso G e K E).inv.f n)).1
  simp only [Category.assoc, ← comp_f, Iso.hom_inv_id, id_f,
    mapHomologicalComplex_obj_X, Category.comp_id,
    ι_projectionFormulaHomologicalComplexIso_inv_f, Iso.hom_inv_id_assoc]

variable {K' : HomologicalComplex C c} {E' : HomologicalComplex D c}
  [HasTensor ((G.mapHomologicalComplex c).obj K') E']
  [HasTensor K' ((L.mapHomologicalComplex c).obj E')]
  [∀ n : I, PreservesColimit (Discrete.functor
    (fun pq : { pq : I × I // pq.1 + pq.2 = n } ↦
      G.obj (K'.X pq.val.1) ⊗ E'.X pq.val.2)) L]

/-- The inverse projection formula for complexes is natural in both complexes. -/
@[reassoc]
lemma projectionFormulaHomologicalComplexIso_inv_naturality (f : K ⟶ K') (g : E ⟶ E') :
    tensorHom f ((L.mapHomologicalComplex c).map g) ≫
        (L.projectionFormulaHomologicalComplexIso G e K' E').inv =
      (L.projectionFormulaHomologicalComplexIso G e K E).inv ≫
        (L.mapHomologicalComplex c).map
          (tensorHom ((G.mapHomologicalComplex c).map f) g) := by
  apply Hom.ext
  funext n
  refine mapBifunctor.hom_ext fun p q hpq ↦ ?_
  have hpq : p + q = n := hpq
  simp only [comp_f, ι_tensorHom_assoc, ι_projectionFormulaHomologicalComplexIso_inv_f,
    ι_projectionFormulaHomologicalComplexIso_inv_f_assoc, mapHomologicalComplex_map_f,
    ← L.map_comp, ι_tensorHom]
  simpa only [L.map_comp, Category.assoc] using
    projectionFormula_inv_naturality_assoc L G e (f.f p) (g.f q)
      (L.map (ιTensorObj ((G.mapHomologicalComplex c).obj K') E' p q n hpq))

/-- The projection formula for complexes is natural in both complexes. -/
@[reassoc]
lemma projectionFormulaHomologicalComplexIso_hom_naturality (f : K ⟶ K') (g : E ⟶ E') :
    (L.mapHomologicalComplex c).map
        (tensorHom ((G.mapHomologicalComplex c).map f) g) ≫
        (L.projectionFormulaHomologicalComplexIso G e K' E').hom =
      (L.projectionFormulaHomologicalComplexIso G e K E).hom ≫
        tensorHom f ((L.mapHomologicalComplex c).map g) := by
  rw [← cancel_epi (L.projectionFormulaHomologicalComplexIso G e K E).inv]
  rw [← Category.assoc, ← L.projectionFormulaHomologicalComplexIso_inv_naturality G e K E f g]
  simp

end Pair

end CategoryTheory.Functor
