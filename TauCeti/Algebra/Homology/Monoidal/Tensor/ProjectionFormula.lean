/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Tensor.Differential
public import TauCeti.Algebra.Homology.Monoidal.Summand
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# The projection formula for unbounded cochain complexes

A natural projection isomorphism `L (G X ⊗ Y) ≅ X ⊗ L Y` extends to unbounded cochain
complexes when `G` preserves zero morphisms and `L` is additive and preserves the
coproducts along the tensor diagonals.
The comparison uses the existing tensor differential, including its Koszul sign.
Only the tensor products of the complexes involved are required to exist.

This is the cochain projection formula used to transfer K-flatness through an exact
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

section Pair

variable (K : CochainComplex C ℤ) (E : CochainComplex D ℤ)
  [HasTensor ((G.mapHomologicalComplex (.up ℤ)).obj K) E]
  [HasTensor K ((L.mapHomologicalComplex (.up ℤ)).obj E)]
  [∀ n : ℤ, PreservesColimit (Discrete.functor
    (fun pq : { pq : ℤ × ℤ // pq.1 + pq.2 = n } ↦ G.obj (K.X pq.val.1) ⊗ E.X pq.val.2)) L]

/-- The degreewise projection isomorphism, obtained from the diagonal coproduct comparison. -/
private def projectionFormulaCochainXIso (n : ℤ) :
    L.obj ((tensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K) E).X n) ≅
      (tensorObj K ((L.mapHomologicalComplex (.up ℤ)).obj E)).X n := by
  let B := (((curriedTensor D).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
    ((G.mapHomologicalComplex (.up ℤ)).obj K)).obj E
  let A := (((curriedTensor C).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj
    ((L.mapHomologicalComplex (.up ℤ)).obj E)
  let f := B.toGradedObject.mapObjFun (fun pq ↦ pq.1 + pq.2) n
  let g := A.toGradedObject.mapObjFun (fun pq ↦ pq.1 + pq.2) n
  let α : Discrete.functor (fun pq ↦ L.obj (f pq)) ≅ Discrete.functor g :=
    Discrete.natIso (fun pq ↦ e.app (K.X pq.as.val.1, E.X pq.as.val.2))
  letI : HasCoproduct f :=
    (inferInstance : HasTensor ((G.mapHomologicalComplex (.up ℤ)).obj K) E) n
  letI : HasCoproduct g :=
    (inferInstance : HasTensor K ((L.mapHomologicalComplex (.up ℤ)).obj E)) n
  letI : HasCoproduct (fun pq ↦ L.obj (f pq)) := hasColimit_of_iso α
  letI : PreservesColimit (Discrete.functor f) L := inferInstanceAs
    (PreservesColimit (Discrete.functor
      (fun pq : { pq : ℤ × ℤ // pq.1 + pq.2 = n } ↦
        G.obj (K.X pq.val.1) ⊗ E.X pq.val.2)) L)
  let β := PreservesCoproduct.iso L f
  let γ := HasColimit.isoOfNatIso α
  exact β ≪≫ γ

@[reassoc]
private lemma ι_projectionFormulaCochainXIso_inv (p q n : ℤ) (h : p + q = n) :
    ιTensorObj K ((L.mapHomologicalComplex (.up ℤ)).obj E) p q n h ≫
        (L.projectionFormulaCochainXIso G e K E n).inv =
      (e.app (K.X p, E.X q)).inv ≫
        L.map (ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K) E p q n h) := by
  let f := (((((curriedTensor D).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
    ((G.mapHomologicalComplex (.up ℤ)).obj K)).obj E).toGradedObject.mapObjFun
      (fun pq ↦ pq.1 + pq.2) n)
  let : HasCoproduct f :=
    (inferInstance : HasTensor ((G.mapHomologicalComplex (.up ℤ)).obj K) E) n
  let : PreservesColimit (Discrete.functor f) L := inferInstanceAs
    (PreservesColimit (Discrete.functor
      (fun pq : { pq : ℤ × ℤ // pq.1 + pq.2 = n } ↦
        G.obj (K.X pq.val.1) ⊗ E.X pq.val.2)) L)
  let : HasCoproduct (fun pq ↦ L.obj (f pq)) :=
    HasColimit.mk ⟨_, isColimitOfHasCoproductOfPreservesColimit L f⟩
  dsimp only [projectionFormulaCochainXIso]
  -- Totalization's degree object is the chosen diagonal coproduct. Rewriting this private
  -- construction crosses that implementation wrapper.
  erw [Iso.trans_inv, HasColimit.ι_isoOfNatIso_inv_assoc, PreservesCoproduct.iso_inv,
    ι_comp_sigmaComparison]
  rfl

private lemma projectionFormulaCochainXIso_inv_comm (n m : ℤ)
    (h : (ComplexShape.up ℤ).Rel n m) :
    (L.projectionFormulaCochainXIso G e K E n).inv ≫
        L.map ((tensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K) E).d n m) =
      (tensorObj K ((L.mapHomologicalComplex (.up ℤ)).obj E)).d n m ≫
        (L.projectionFormulaCochainXIso G e K E m).inv := by
  obtain rfl : m = n + 1 := h.symm
  refine mapBifunctor.hom_ext fun p q hpq ↦ ?_
  have hpq : p + q = n := hpq
  simp only [ι_projectionFormulaCochainXIso_inv_assoc, ← L.map_comp,
    ιTensorObj_d, ιTensorObj_d_assoc, L.map_add, Units.smul_def, L.map_zsmul,
    Preadditive.comp_add, Preadditive.comp_zsmul, Preadditive.add_comp,
    Preadditive.zsmul_comp, Category.assoc, ι_projectionFormulaCochainXIso_inv]
  have h₁ := e.inv.naturality (X := (K.X p, E.X q))
    (Y := (K.X (p + 1), E.X q)) (K.d p (p + 1), 𝟙 (E.X q))
  have h₂ := e.inv.naturality (X := (K.X p, E.X q))
    (Y := (K.X p, E.X (q + 1))) (𝟙 (K.X p), E.d q (q + 1))
  dsimp at h₁ h₂
  simpa only [tensorHom_id, id_tensorHom, G.map_id, L.map_id, L.map_comp,
    Category.assoc, mapHomologicalComplex_obj_X, mapHomologicalComplex_obj_d,
    Iso.app_inv] using
    congrArg₂ (· + ·)
      (congrArg (· ≫ L.map (ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K) E
        (p + 1) q (n + 1) (by omega))) h₁.symm)
      (congrArg (fun f ↦ (p.negOnePow.val : ℤ) • (f ≫
        L.map (ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K) E
          p (q + 1) (n + 1) (by omega)))) h₂.symm)

/-- An additive projection formula lifts to unbounded cochain complexes, provided `L`
preserves the coproducts on the diagonals of their tensor product. -/
def projectionFormulaCochainIso :
    (L.mapHomologicalComplex (.up ℤ)).obj
        (tensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K) E) ≅
      tensorObj K ((L.mapHomologicalComplex (.up ℤ)).obj E) :=
  (Hom.isoOfComponents (fun n ↦ (L.projectionFormulaCochainXIso G e K E n).symm)
    (fun n m h ↦ L.projectionFormulaCochainXIso_inv_comm G e K E n m h)).symm

/-- The inverse cochain projection formula on each tensor inclusion. -/
@[reassoc (attr := simp)]
lemma ι_projectionFormulaCochainIso_inv_f (p q n : ℤ) (h : p + q = n) :
    ιTensorObj K ((L.mapHomologicalComplex (.up ℤ)).obj E) p q n h ≫
        (L.projectionFormulaCochainIso G e K E).inv.f n =
      (e.app (K.X p, E.X q)).inv ≫
        L.map (ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K) E p q n h) :=
  L.ι_projectionFormulaCochainXIso_inv G e K E p q n h

/-- On a homogeneous tensor summand the cochain projection formula is the supplied
projection formula on the two terms. -/
@[reassoc (attr := simp)]
lemma map_ι_projectionFormulaCochainIso_hom_f (p q n : ℤ) (h : p + q = n) :
    L.map (ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K) E p q n h) ≫
        (L.projectionFormulaCochainIso G e K E).hom.f n =
      (e.app (K.X p, E.X q)).hom ≫
        ιTensorObj K ((L.mapHomologicalComplex (.up ℤ)).obj E) p q n h := by
  apply (cancel_mono ((L.projectionFormulaCochainIso G e K E).inv.f n)).1
  simp only [Category.assoc, ← comp_f, Iso.hom_inv_id, id_f,
    mapHomologicalComplex_obj_X, Category.comp_id,
    ι_projectionFormulaCochainIso_inv_f, Iso.hom_inv_id_assoc]

variable {K' : CochainComplex C ℤ} {E' : CochainComplex D ℤ}
  [HasTensor ((G.mapHomologicalComplex (.up ℤ)).obj K') E']
  [HasTensor K' ((L.mapHomologicalComplex (.up ℤ)).obj E')]
  [∀ n : ℤ, PreservesColimit (Discrete.functor
    (fun pq : { pq : ℤ × ℤ // pq.1 + pq.2 = n } ↦
      G.obj (K'.X pq.val.1) ⊗ E'.X pq.val.2)) L]

/-- The inverse cochain projection formula is natural in both complexes. -/
@[reassoc]
lemma projectionFormulaCochainIso_inv_naturality (f : K ⟶ K') (g : E ⟶ E') :
    tensorHom f ((L.mapHomologicalComplex (.up ℤ)).map g) ≫
        (L.projectionFormulaCochainIso G e K' E').inv =
      (L.projectionFormulaCochainIso G e K E).inv ≫
        (L.mapHomologicalComplex (.up ℤ)).map
          (tensorHom ((G.mapHomologicalComplex (.up ℤ)).map f) g) := by
  apply Hom.ext
  funext n
  refine mapBifunctor.hom_ext fun p q hpq ↦ ?_
  have hpq : p + q = n := hpq
  simp only [comp_f, ι_tensorHom_assoc, ι_projectionFormulaCochainIso_inv_f,
    ι_projectionFormulaCochainIso_inv_f_assoc, mapHomologicalComplex_map_f,
    ← L.map_comp, ι_tensorHom]
  have h := e.inv.naturality (X := (K.X p, E.X q))
    (Y := (K'.X p, E'.X q)) (f.f p, g.f q)
  simpa only [comp_obj, prod_obj, id_obj, comp_map, prod_map, id_map, tensor_map,
    L.map_comp, Category.assoc, Iso.app_inv] using
    congrArg (· ≫ L.map (ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K') E'
      p q n hpq)) h

/-- The cochain projection formula is natural in both complexes. -/
@[reassoc]
lemma projectionFormulaCochainIso_hom_naturality (f : K ⟶ K') (g : E ⟶ E') :
    (L.mapHomologicalComplex (.up ℤ)).map
        (tensorHom ((G.mapHomologicalComplex (.up ℤ)).map f) g) ≫
        (L.projectionFormulaCochainIso G e K' E').hom =
      (L.projectionFormulaCochainIso G e K E).hom ≫
        tensorHom f ((L.mapHomologicalComplex (.up ℤ)).map g) := by
  rw [← cancel_epi (L.projectionFormulaCochainIso G e K E).inv]
  rw [← Category.assoc, ← L.projectionFormulaCochainIso_inv_naturality G e K E f g]
  simp

end Pair

end CategoryTheory.Functor
