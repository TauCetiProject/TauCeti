/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.Basic
public import TauCeti.CategoryTheory.Monoidal.EqToHom

/-!
# Pullback of graded quasicoherent algebras

For a morphism of schemes `f : Y ⟶ X` and a nonnegatively graded quasicoherent algebra
`A = ⨁ₙ Aₙ` on `X`, the pullback `f^* A = ⨁ₙ f^* Aₙ` is a graded quasicoherent algebra on `Y`.
Its homogeneous components are the pullbacks `f^* Aₙ`, its unit is `𝒪_Y ≅ f^* 𝒪_X ⟶ f^* A₀`, and
its homogeneous multiplications are

`f^* Aᵢ ⊗ f^* Aⱼ ≅ f^* (Aᵢ ⊗ Aⱼ) ⟶ f^* Aᵢ₊ⱼ`,

where the first map inverts the tensor comparison of pullback, which is an isomorphism because
`Aᵢ` is quasicoherent (Stacks Project, Tag 03EL). This is base change of graded algebras along
`f`, the graded counterpart of `TauCeti.AlgebraicGeometry.QuasicoherentAlgebra.pullback`. It is
the algebraic side of base change for graded relative spectra, such as the linear scheme
`Spec_X (Sym F)`.

The algebra laws of `f^* A` are those of `A`, stated for its unit and homogeneous
multiplications as morphisms of quasicoherent sheaves (`GradedQuasicoherentAlgebra.one` and
`GradedQuasicoherentAlgebra.mul`), transported along the strong symmetric monoidal pullback of
quasicoherent sheaves to modules on `Y`
(`AlgebraicGeometry.Scheme.Modules.pullbackToModulesBraided`), by the transport lemmas
`CategoryTheory.GradedObject.one_mul_of_laxMonoidal`, `mul_one_of_laxMonoidal`,
`mul_assoc_of_laxMonoidal` and `mul_comm_of_laxBraided`.

Pulling back commutes with taking homogeneous components (`pullbackDegreeIso`); in particular
the degree-one component of `f^* A` is the pullback of the degree-one component of `A`.

## Main declarations

* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.pullback`: pullback of graded
  quasicoherent algebras along a morphism of schemes;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.pullback_obj_obj_X`,
  `pullback_obj_one`, `pullback_obj_mul` and `pullback_map_hom_hom_hom`: its homogeneous
  components, unit, homogeneous multiplications and action on morphisms;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.pullbackDegreeIso`: the degree-`n`
  component of `f^* A` is the pullback of the degree-`n` component of `A`, naturally in `A`.

## References

* The Stacks Project, [Tag 03EL](https://stacks.math.columbia.edu/tag/03EL) (pullback of tensor
  products).
-/

public section

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace GradedQuasicoherentAlgebra

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- Pullback of quasicoherent sheaves on `X` to modules on `Y`, a strong symmetric monoidal
functor. -/
private abbrev pullbackQ : QuasicoherentSheaf X ⥤ Y.Modules :=
  (ObjectProperty.ι _ : QuasicoherentSheaf X ⥤ X.Modules) ⋙ Scheme.Modules.pullback f

variable (A : GradedQuasicoherentAlgebra X)

/-- The pullback of the underlying module of the degree-`n` component of `A` is the pullback of
that component as a quasicoherent sheaf. -/
private def pullbackComponentIso (n : ℕ) :
    (Scheme.Modules.pullback f).obj (A.obj.X n) ≅ (pullbackQ f).obj ((degree n).obj A) :=
  eqToIso (congrArg (Scheme.Modules.pullback f).obj (degree_obj_obj A n).symm)

/-- The unit `𝒪_Y ≅ f^* 𝒪_X ⟶ f^* A₀` of the pullback of a graded quasicoherent algebra. -/
private def pullbackOne :
    𝟙_ Y.Modules ⟶ (Scheme.Modules.pullback f).obj (A.obj.X 0) :=
  ε (pullbackQ f) ≫ (pullbackQ f).map A.one ≫ (pullbackComponentIso f A 0).inv

/-- The homogeneous multiplication `f^* Aᵢ ⊗ f^* Aⱼ ≅ f^* (Aᵢ ⊗ Aⱼ) ⟶ f^* Aᵢ₊ⱼ` of the pullback of
a graded quasicoherent algebra. -/
private def pullbackMul (i j : ℕ) :
    (Scheme.Modules.pullback f).obj (A.obj.X i) ⊗ (Scheme.Modules.pullback f).obj (A.obj.X j) ⟶
      (Scheme.Modules.pullback f).obj (A.obj.X (i + j)) :=
  ((pullbackComponentIso f A i).hom ⊗ₘ (pullbackComponentIso f A j).hom) ≫
    μ (pullbackQ f) ((degree i).obj A) ((degree j).obj A) ≫ (pullbackQ f).map (A.mul i j) ≫
      (pullbackComponentIso f A (i + j)).inv

private lemma pullbackOne_def :
    pullbackOne f A = (Scheme.Modules.pullbackObjUnitIso f).inv ≫
      (Scheme.Modules.pullback f).map A.obj.toMon.one := by
  rw [pullbackOne, Scheme.Modules.pullbackToModules_ε]
  -- `pullbackQ f` acts on morphisms of quasicoherent sheaves by pullback of the underlying maps.
  exact congrArg (_ ≫ ·) (eq_of_heq ((comp_eqToHom_heq _
    (congrArg (Scheme.Modules.pullback f).obj (degree_obj_obj A 0).symm).symm).trans
      (Functor.map_heq _ rfl (degree_obj_obj A 0)
        ((heq_of_eq A.one_hom).trans (comp_eqToHom_heq _ _)))))

private lemma pullbackMul_def (i j : ℕ) :
    pullbackMul f A i j =
      inv (δ (Scheme.Modules.pullback f) (A.obj.X i) (A.obj.X j)) ≫
        (Scheme.Modules.pullback f).map (A.obj.toMon.mul i j) := by
  rw [pullbackMul, Scheme.Modules.pullbackToModules_μ]
  have := @Scheme.Modules.isIso_pullback_δ_of_isQuasicoherent _ _ f _
    ((degree j).obj A).obj ((degree i).obj A).property
  -- `pullbackQ f` acts on morphisms of quasicoherent sheaves by pullback of the underlying maps.
  exact Functor.eqToHom_conjugate_inv_δ_comp_map (C := X.Modules) _ (degree_obj_obj A i).symm
    (degree_obj_obj A j).symm (degree_obj_obj A (i + j)).symm _ _ (A.mul_hom i j)

/-- The homogeneous components `f^* Aₙ` of the pullback of a graded quasicoherent algebra. -/
private abbrev pullbackComponents : GradedObject ℕ Y.Modules :=
  fun n ↦ (Scheme.Modules.pullback f).obj (A.obj.X n)

private lemma pullbackOne_mul (n : ℕ) :
    (pullbackOne f A ▷ pullbackComponents f A n) ≫ pullbackMul f A 0 n =
      (λ_ (pullbackComponents f A n)).hom ≫
        eqToHom (congrArg (pullbackComponents f A) (zero_add n).symm) :=
  GradedObject.one_mul_of_laxMonoidal (F := pullbackQ f) (X := fun n ↦ (degree n).obj A)
    (Y := pullbackComponents f A) (e := pullbackComponentIso f A) A.mul (pullbackMul f A)
    (fun _ _ ↦ rfl) A.one (pullbackOne f A) rfl A.one_mul n

private lemma pullbackMul_one (n : ℕ) :
    (pullbackComponents f A n ◁ pullbackOne f A) ≫ pullbackMul f A n 0 =
      (ρ_ (pullbackComponents f A n)).hom ≫
        eqToHom (congrArg (pullbackComponents f A) (add_zero n).symm) :=
  GradedObject.mul_one_of_laxMonoidal (F := pullbackQ f) (X := fun n ↦ (degree n).obj A)
    (Y := pullbackComponents f A) (e := pullbackComponentIso f A) A.mul (pullbackMul f A)
    (fun _ _ ↦ rfl) A.one (pullbackOne f A) rfl A.mul_one n

private lemma pullbackMul_assoc (i j k : ℕ) :
    (pullbackMul f A i j ▷ pullbackComponents f A k) ≫ pullbackMul f A (i + j) k =
      (α_ _ _ _).hom ≫ (pullbackComponents f A i ◁ pullbackMul f A j k) ≫
        pullbackMul f A i (j + k) ≫
          eqToHom (congrArg (pullbackComponents f A) (add_assoc i j k).symm) :=
  GradedObject.mul_assoc_of_laxMonoidal (F := pullbackQ f) (X := fun n ↦ (degree n).obj A)
    (Y := pullbackComponents f A) (e := pullbackComponentIso f A) A.mul (pullbackMul f A)
    (fun _ _ ↦ rfl) A.mul_assoc i j k

private lemma pullbackMul_comm (i j : ℕ) :
    (β_ (pullbackComponents f A i) (pullbackComponents f A j)).hom ≫ pullbackMul f A j i =
      pullbackMul f A i j ≫ eqToHom (congrArg (pullbackComponents f A) (add_comm i j)) :=
  GradedObject.mul_comm_of_laxBraided (F := pullbackQ f) (X := fun n ↦ (degree n).obj A)
    (Y := pullbackComponents f A) (e := pullbackComponentIso f A) A.mul (pullbackMul f A)
    (fun _ _ ↦ rfl) A.mul_comm i j

/-- The pullback `f^* A = ⨁ₙ f^* Aₙ` of a single graded quasicoherent algebra, assembled from its
homogeneous components by `GradedQuasicoherentAlgebra.ofHomogeneous`. -/
private def pullbackObj : GradedQuasicoherentAlgebra Y :=
  ofHomogeneous (pullbackComponents f A) (pullbackOne f A) (pullbackMul f A)
    (pullbackOne_mul f A) (pullbackMul_one f A) (pullbackMul_assoc f A) (pullbackMul_comm f A)

private theorem pullbackObj_X :
    (pullbackObj f A).obj.X = fun n ↦ (Scheme.Modules.pullback f).obj (A.obj.X n) :=
  ofHomogeneous_obj_X _ _ _ _ _ _ _

private theorem one_pullbackObj :
    (pullbackObj f A).obj.toMon.one =
      pullbackOne f A ≫ eqToHom (congrFun (pullbackObj_X f A) 0).symm :=
  one_ofHomogeneous _ _ _ _ _ _ _

private theorem mul_pullbackObj (i j : ℕ) :
    (pullbackObj f A).obj.toMon.mul i j =
      (eqToHom (by rw [pullbackObj_X]) :
        (pullbackObj f A).obj.X i ⊗ (pullbackObj f A).obj.X j ⟶ _) ≫
        pullbackMul f A i j ≫ eqToHom (congrFun (pullbackObj_X f A) (i + j)).symm :=
  mul_ofHomogeneous _ _ _ _ _ _ _ i j

section Hom

variable {A} {B : GradedQuasicoherentAlgebra X}

/-- In degree `n`, the pullback of a morphism of graded quasicoherent algebras, read through
`pullbackComponentIso`, is the pullback of its degree-`n` component. -/
private lemma pullback_map_degree_map (g : A ⟶ B) (n : ℕ) :
    (Scheme.Modules.pullback f).map (g.hom.hom.hom n) =
      (pullbackComponentIso f A n).hom ≫ (pullbackQ f).map ((degree n).map g) ≫
        (pullbackComponentIso f B n).inv :=
  -- `pullbackQ f` acts on morphisms of quasicoherent sheaves by pullback of the underlying maps.
  (conj_eqToHom_iff_heq _ _ (congrArg (Scheme.Modules.pullback f).obj (degree_obj_obj A n).symm)
    (congrArg (Scheme.Modules.pullback f).obj (degree_obj_obj B n).symm)).mpr
      (Functor.map_heq _ (degree_obj_obj A n).symm (degree_obj_obj B n).symm
        ((conj_eqToHom_iff_heq _ _ (degree_obj_obj A n) (degree_obj_obj B n)).mp
          (degree_map_hom g n)).symm)

private lemma pullbackOne_map (g : A ⟶ B) :
    pullbackOne f A ≫ (Scheme.Modules.pullback f).map (g.hom.hom.hom 0) = pullbackOne f B := by
  rw [pullbackOne_def, pullbackOne_def]
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
    (((Scheme.Modules.pullback f).map_comp _ _).symm.trans
      (congrArg (Scheme.Modules.pullback f).map (Mon.one_map g.hom.hom))))

private lemma pullbackMul_map (g : A ⟶ B) (i j : ℕ) :
    ((Scheme.Modules.pullback f).map (g.hom.hom.hom i) ⊗ₘ
        (Scheme.Modules.pullback f).map (g.hom.hom.hom j)) ≫ pullbackMul f B i j =
      pullbackMul f A i j ≫ (Scheme.Modules.pullback f).map (g.hom.hom.hom (i + j)) :=
  GradedObject.map_mul_of_laxMonoidal (F := pullbackQ f) (X := fun n ↦ (degree n).obj A)
    (Y := pullbackComponents f A) (e := pullbackComponentIso f A) A.mul (pullbackMul f A)
    (fun _ _ ↦ rfl) (X' := fun n ↦ (degree n).obj B) (Y' := pullbackComponents f B)
    (e' := pullbackComponentIso f B) B.mul (pullbackMul f B) (fun _ _ ↦ rfl)
    (fun n ↦ (degree n).map g)
    (fun n ↦ (Scheme.Modules.pullback f).map (g.hom.hom.hom n))
    (pullback_map_degree_map f g)
    (GradedQuasicoherentAlgebra.map_mul g) i j

end Hom

/-- **Pullback of graded quasicoherent algebras.** For a morphism of schemes `f : Y ⟶ X`, the
pullback of a graded quasicoherent algebra `A = ⨁ₙ Aₙ` on `X` is the graded quasicoherent algebra
`f^* A = ⨁ₙ f^* Aₙ` on `Y`, with unit `𝒪_Y ≅ f^* 𝒪_X ⟶ f^* A₀` and homogeneous multiplications
`f^* Aᵢ ⊗ f^* Aⱼ ≅ f^* (Aᵢ ⊗ Aⱼ) ⟶ f^* Aᵢ₊ⱼ` (`pullback_obj_one`, `pullback_obj_mul`). A morphism
of graded algebras acts by pullback in each degree (`pullback_map_hom_hom_hom`). -/
def pullback : GradedQuasicoherentAlgebra X ⥤ GradedQuasicoherentAlgebra Y where
  obj := pullbackObj f
  map {A B} g := homMkOfEq (pullbackObj_X f A) (pullbackObj_X f B) (one_pullbackObj f A)
    (one_pullbackObj f B) (mul_pullbackObj f A) (mul_pullbackObj f B)
    (fun n ↦ (Scheme.Modules.pullback f).map (g.hom.hom.hom n)) (pullbackOne_map f g)
    (pullbackMul_map f g)
  map_id _ := homMkOfEq_id _ _ _ _ _ _ fun _ ↦ (Scheme.Modules.pullback f).map_id _
  map_comp _ _ := homMkOfEq_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fun _ ↦
    ((Scheme.Modules.pullback f).map_comp _ _).symm

/-- The degree-`n` component of the pullback `f^* A` is the pullback `f^* Aₙ` of the degree-`n`
component of `A`. -/
@[simp]
theorem pullback_obj_obj_X (A : GradedQuasicoherentAlgebra X) (n : ℕ) :
    ((pullback f).obj A).obj.X n = (Scheme.Modules.pullback f).obj (A.obj.X n) :=
  congrFun (pullbackObj_X f A) n

/-- In degree `n`, the pullback of a morphism `g` of graded quasicoherent algebras is the pullback
of the degree-`n` component of `g`, up to the identifications `pullback_obj_obj_X`. -/
@[simp]
theorem pullback_map_hom_hom_hom {A B : GradedQuasicoherentAlgebra X} (g : A ⟶ B) (n : ℕ) :
    ((pullback f).map g).hom.hom.hom n =
      eqToHom (pullback_obj_obj_X f A n) ≫ (Scheme.Modules.pullback f).map (g.hom.hom.hom n) ≫
        eqToHom (pullback_obj_obj_X f B n).symm :=
  homMkOfEq_hom_hom_hom _ _ _ _ _ _ _ _ _ n

/-- The unit of the pullback `f^* A` is the pullback of the unit of `A`, preceded by the
identification `𝒪_Y ≅ f^* 𝒪_X`, up to the identification `pullback_obj_obj_X`. -/
@[simp]
theorem pullback_obj_one (A : GradedQuasicoherentAlgebra X) :
    ((pullback f).obj A).obj.toMon.one =
      (Scheme.Modules.pullbackObjUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map A.obj.toMon.one ≫
          eqToHom (pullback_obj_obj_X f A 0).symm :=
  (one_pullbackObj f A).trans
    ((congrArg (· ≫ _) (pullbackOne_def f A)).trans (Category.assoc _ _ _))

/-- The homogeneous multiplication of the pullback `f^* A` is the pullback of that of `A`,
preceded by the inverse of the tensor comparison `f^* (Aᵢ ⊗ Aⱼ) ≅ f^* Aᵢ ⊗ f^* Aⱼ`, up to the
identifications `pullback_obj_obj_X`. -/
@[simp]
theorem pullback_obj_mul (A : GradedQuasicoherentAlgebra X) (i j : ℕ) :
    ((pullback f).obj A).obj.toMon.mul i j =
      (eqToHom (pullback_obj_obj_X f A i) ⊗ₘ eqToHom (pullback_obj_obj_X f A j)) ≫
        inv (δ (Scheme.Modules.pullback f) (A.obj.X i) (A.obj.X j)) ≫
          (Scheme.Modules.pullback f).map (A.obj.toMon.mul i j) ≫
            eqToHom (pullback_obj_obj_X f A (i + j)).symm := by
  refine (mul_pullbackObj f A i j).trans
    ((congrArg (_ ≫ · ≫ _) (pullbackMul_def f A i j)).trans ?_)
  -- Both sides start with a transport `f^* Aᵢ ⊗ f^* Aⱼ`; written as one `eqToHom`, they agree.
  simp only [tensorHom_def, eqToHom_whiskerRight, whiskerLeft_eqToHom, eqToHom_trans]
  exact congrArg (_ ≫ ·) (Category.assoc _ _ _)

/-- The degree-`n` component of the pullback `f^* A` and the pullback of the degree-`n`
component of `A` have the same underlying module `f^* Aₙ`. -/
private lemma degree_pullback_obj_obj (A : GradedQuasicoherentAlgebra X) (n : ℕ) :
    ((degree n).obj ((pullback f).obj A)).obj =
      ((QuasicoherentSheaf.pullback f).obj ((degree n).obj A)).obj :=
  ((degree_obj_obj _ n).trans (pullback_obj_obj_X f A n)).trans
    ((QuasicoherentSheaf.pullback_obj_obj f _).trans (congrArg _ (degree_obj_obj A n))).symm

/-- In degree `n`, pulling back a morphism of graded algebras and then taking its component agrees
with taking its component and then pulling back, up to the identifications of the objects. -/
private lemma degree_map_pullback_map_hom_heq {A B : GradedQuasicoherentAlgebra X} (g : A ⟶ B)
    (n : ℕ) :
    ((degree n).map ((pullback f).map g)).hom ≍
      ((QuasicoherentSheaf.pullback f).map ((degree n).map g)).hom :=
  -- Each side is a pullback of the component `g.hom.hom.hom n`, conjugated by transports.
  ((heq_of_eq (degree_map_hom _ n)).trans ((eqToHom_comp_heq _ _).trans
    (comp_eqToHom_heq _ _))).trans <|
  ((heq_of_eq (pullback_map_hom_hom_hom f g n)).trans ((eqToHom_comp_heq _ _).trans
    (comp_eqToHom_heq _ _))).trans <|
  (Functor.map_heq (Scheme.Modules.pullback f) (degree_obj_obj A n).symm
    (degree_obj_obj B n).symm ((heq_of_eq (degree_map_hom g n)).trans
      ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _))).symm).trans <|
  ((heq_of_eq (QuasicoherentSheaf.pullback_map_hom f _)).trans ((eqToHom_comp_heq _ _).trans
    (comp_eqToHom_heq _ _))).symm

/-- Taking the degree-`n` component commutes with pullback: the degree-`n` component of the
pullback `f^* A` of a graded quasicoherent algebra is the pullback of its degree-`n` component,
naturally in `A`. -/
def pullbackDegreeIso (n : ℕ) :
    pullback f ⋙ degree n ≅ degree n ⋙ QuasicoherentSheaf.pullback f :=
  NatIso.ofComponents
    (fun A ↦ ObjectProperty.isoMk _ (eqToIso (degree_pullback_obj_obj f A n)))
    (fun g ↦ ObjectProperty.hom_ext _ (eq_of_heq
      ((comp_eqToHom_heq _ (degree_pullback_obj_obj f _ n)).trans
        ((degree_map_pullback_map_hom_heq f g n).trans
          (eqToHom_comp_heq _ (degree_pullback_obj_obj f _ n)).symm))))

/-- The component of `pullbackDegreeIso` at `A` is the identification of the degree-`n` component
of `f^* A` with the pullback of the degree-`n` component of `A`. -/
@[simp]
theorem pullbackDegreeIso_hom_app_hom (n : ℕ) (A : GradedQuasicoherentAlgebra X) :
    ((pullbackDegreeIso f n).hom.app A).hom =
      eqToHom (((degree_obj_obj _ n).trans (pullback_obj_obj_X f A n)).trans
        ((QuasicoherentSheaf.pullback_obj_obj f _).trans (congrArg _ (degree_obj_obj A n))).symm) :=
  (rfl)

/-- The inverse component of `pullbackDegreeIso` at `A` is the identification of the pullback of
the degree-`n` component of `A` with the degree-`n` component of `f^* A`. -/
@[simp]
theorem pullbackDegreeIso_inv_app_hom (n : ℕ) (A : GradedQuasicoherentAlgebra X) :
    ((pullbackDegreeIso f n).inv.app A).hom =
      eqToHom (((QuasicoherentSheaf.pullback_obj_obj f _).trans
        (congrArg _ (degree_obj_obj A n))).trans
          ((degree_obj_obj _ n).trans (pullback_obj_obj_X f A n)).symm) :=
  (rfl)

end GradedQuasicoherentAlgebra

end

end AlgebraicGeometry

end TauCeti
