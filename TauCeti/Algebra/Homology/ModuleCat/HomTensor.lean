/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LinearYoneda
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.Flat.CategoryTheory
import TauCeti.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Tensor products and Hom-complex cohomology

For a chain complex `C` of finite projective modules, tensoring `Hom(C, N)` with a module `T`
is the same as replacing its coefficients by `T ⊗ N`. If `T` is flat, this gives a comparison
on cohomology. In particular it applies to Koszul complexes of finite projective modules.
This is the flat base-change comparison used for first Koszul cohomology in the extension
descent argument of the Stacks Project, Lemma 15.91.8 (05EG).

The termwise comparison is Mathlib's `lTensorHomEquivHomLTensor`; the cohomology comparison
uses preservation of homology by the exact functor tensoring with a flat module.
-/

public section

open CategoryTheory

universe u

namespace ChainComplex

open MonoidalCategory TensorProduct

variable {R : Type u} [CommRing R] {α : Type*} [AddRightCancelSemigroup α] [One α]
  (C : ChainComplex (ModuleCat.{u} R) α) (T N : ModuleCat.{u} R)
  [∀ i, Module.Finite R (C.X i)] [∀ i, Module.Projective R (C.X i)]

/-- Tensoring the coefficients of the Hom complex of a complex of finite projective modules
commutes with forming the Hom complex. In degree `i`, the comparison sends `t ⊗ f` to
`x ↦ t ⊗ f x`. No flatness of the tensor factor is required. -/
noncomputable def tensorLinearYonedaObjIso :
    ((tensorLeft T).mapHomologicalComplex (ComplexShape.up α)).obj (C.linearYonedaObj R N) ≅
      C.linearYonedaObj R (T ⊗ N) := by
  let e (i : α) : T ⊗[R] (C.X i ⟶ N) ≃ₗ[R] (C.X i ⟶ T ⊗ N) :=
    TensorProduct.congr (LinearEquiv.refl R T) ModuleCat.homLinearEquiv ≪≫ₗ
      lTensorHomEquivHomLTensor R (C.X i) T N ≪≫ₗ
        (ModuleCat.homLinearEquiv (M := C.X i) (N := T ⊗ N) (S := R)).symm
  refine HomologicalComplex.Hom.isoOfComponents (fun i ↦ (e i).toModuleIso) ?_
  intro i j _
  apply ModuleCat.hom_ext
  -- The terms of the mapped complex and of the Hom complex are bundled module objects.
  -- Expose their underlying linear maps so tensor extensionality can see the source.
  change (Linear.leftComp R (T ⊗ N) (C.d j i)).comp (e i).toLinearMap =
    (e j).toLinearMap.comp ((Linear.leftComp R N (C.d j i)).lTensor T)
  apply TensorProduct.ext
  ext t f x
  simp [e, TensorProduct.lTensorHomToHomLTensor, ModuleCat.homLinearEquiv,
    ModuleCat.homAddEquiv, ModuleCat.homEquiv]

/-- On pure tensors, the Hom-complex comparison is evaluation followed by tensoring. -/
@[simp]
theorem tensorLinearYonedaObjIso_hom_f_tmul (i : α) (t : T) (f : C.X i ⟶ N) :
    ModuleCat.Hom.hom (A := T ⊗ (C.linearYonedaObj R N).X i)
        ((C.tensorLinearYonedaObjIso T N).hom.f i) (t ⊗ₜ[R] f) =
      f ≫ ModuleCat.ofHom (TensorProduct.mk R T N t) := by
  apply ModuleCat.hom_ext
  ext x
  -- The component of `isoOfComponents` is the specified equivalence, behind bundled objects.
  change ((TensorProduct.congr (LinearEquiv.refl R T) ModuleCat.homLinearEquiv ≪≫ₗ
    lTensorHomEquivHomLTensor R (C.X i) T N) (t ⊗ₜ[R] f)) x = _
  simp [TensorProduct.lTensorHomToHomLTensor]
  rfl

/-- The Hom-complex tensor comparison is natural in the coefficient module. -/
theorem tensorLinearYonedaObjIso_naturality {N' : ModuleCat.{u} R} (g : N ⟶ N') :
    ((tensorLeft T).mapHomologicalComplex (ComplexShape.up α)).map
        (C.linearYonedaObjMap R g) ≫ (C.tensorLinearYonedaObjIso T N').hom =
      (C.tensorLinearYonedaObjIso T N).hom ≫ C.linearYonedaObjMap R (T ◁ g) := by
  ext i : 1
  apply ModuleCat.hom_ext
  -- The cochain objects are bundled; expose the tensor-product source for extensionality.
  change ((C.tensorLinearYonedaObjIso T N').hom.f i).hom.comp
      (((C.linearYonedaObjMap R g).f i).hom.lTensor T) =
    ((C.linearYonedaObjMap R (T ◁ g)).f i).hom.comp
      ((C.tensorLinearYonedaObjIso T N).hom.f i).hom
  apply TensorProduct.ext
  refine LinearMap.ext fun t ↦ LinearMap.ext fun (f : C.X i ⟶ N) ↦ ?_
  -- Evaluate the linear-map compositions, then use the public coefficient-map formula.
  change (C.tensorLinearYonedaObjIso T N').hom.f i
      (t ⊗ₜ[R] ((C.linearYonedaObjMap R g).f i f)) =
    (C.linearYonedaObjMap R (T ◁ g)).f i
      ((C.tensorLinearYonedaObjIso T N).hom.f i (t ⊗ₜ[R] f))
  simp only [Functor.mapHomologicalComplex_obj_X, curriedTensor_obj_obj,
    linearYonedaObjMap_f_hom_apply, tensorLinearYonedaObjIso_hom_f_tmul]
  apply ModuleCat.hom_ext (M := C.X i) (N := T ⊗ N')
  ext x
  rfl

/-- Flat tensor products commute with the cohomology of the Hom complex of a complex of
finite projective modules. The comparison is induced by `t ⊗ f ↦ (x ↦ t ⊗ f x)`. -/
noncomputable def tensorLinearYonedaHomologyIso [Module.Flat R T] (i : α) :
    T ⊗ (C.linearYonedaObj R N).homology i ≅
      (C.linearYonedaObj R (T ⊗ N)).homology i :=
  (((C.linearYonedaObj R N).sc i).mapHomologyIso (tensorLeft T)).symm ≪≫
    HomologicalComplex.homologyMapIso (C.tensorLinearYonedaObjIso T N) i

/-- The cohomology comparison takes the class of a tensored cocycle to its class after the
cochain comparison. This characterizes it without unfolding either comparison. -/
@[reassoc]
theorem tensorLinearYonedaHomologyIso_homologyπ [Module.Flat R T] (i : α) :
    (T ◁ (C.linearYonedaObj R N).homologyπ i) ≫
        (C.tensorLinearYonedaHomologyIso T N i).hom =
      (((C.linearYonedaObj R N).sc i).mapCyclesIso (tensorLeft T)).inv ≫
        HomologicalComplex.cyclesMap (C.tensorLinearYonedaObjIso T N).hom i ≫
          (C.linearYonedaObj R (T ⊗ N)).homologyπ i := by
  let S := (C.linearYonedaObj R N).sc i
  let F := tensorLeft T
  have hclass := congrArg (fun f ↦ (S.mapCyclesIso F).inv ≫ f ≫
    (S.mapHomologyIso F).inv) (S.homologyπ_comp_mapHomologyIso_hom F)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.inv_hom_id_assoc] at hclass
  -- The homology and cycles of `S.map F` are the objects of the mapped cochain complex.
  -- Paste the two squares as terms so rewriting need not unfold these bundled objects.
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ HomologicalComplex.homologyMap (C.tensorLinearYonedaObjIso T N).hom i)
      hclass.symm).trans <|
        (Category.assoc _ _ _).trans <|
          congrArg ((S.mapCyclesIso F).inv ≫ ·)
            (HomologicalComplex.homologyπ_naturality (C.tensorLinearYonedaObjIso T N).hom i)

end ChainComplex
