/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.DirectSum
public import TauCeti.AlgebraicGeometry.RelativeSpec.PullbackAlgebra
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

Pullback along the identity and along a composite are identified with the identity and with the
composite of pullbacks (`pullbackId`, `pullbackComp`), degree by degree through the corresponding
comparisons for modules.

Pullback commutes with the two ways of forgetting structure. Pulling back commutes with taking
homogeneous components (`pullbackDegreeIso`); in particular the degree-one component of `f^* A` is
the pullback of the degree-one component of `A`. The underlying direct-sum algebra of `f^* A` is
the pullback of the direct-sum algebra, `f^* (⨁ₙ Aₙ) ≅ ⨁ₙ f^* Aₙ` as quasicoherent algebras
(`pullbackToQuasicoherentAlgebraIso`), because pullback preserves direct sums. These are the
comparisons through which base change of graded relative spectra, such as linear schemes, reduces
to base change of relative spectra.

## Main declarations

* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.pullback`: pullback of graded
  quasicoherent algebras along a morphism of schemes;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.pullback_obj_obj_X`,
  `pullback_obj_one`, `pullback_obj_mul` and `pullback_map_hom_hom_hom`: its homogeneous
  components, unit, homogeneous multiplications and action on morphisms;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.pullbackId` and
  `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.pullbackComp`: its identity and
  composition isomorphisms, given in each degree by Mathlib's `Scheme.Modules.pullbackId` and
  `Scheme.Modules.pullbackComp`;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.pullbackDegreeIso`: the degree-`n`
  component of `f^* A` is the pullback of the degree-`n` component of `A`, naturally in `A`;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.pullbackToQuasicoherentAlgebraIso`: the
  isomorphism `f^* (⨁ₙ Aₙ) ≅ ⨁ₙ f^* Aₙ` of quasicoherent algebras, natural in `A`, whose inverse
  is the pullback of the inclusion of `Aₙ` on the summand `f^* Aₙ`
  (`ιTotal_pullbackToQuasicoherentAlgebraIso_inv_app`).

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §1.5 and §8.
* The Stacks Project, [Tag 01LQ](https://stacks.math.columbia.edu/tag/01LQ) (relative spectrum as
  a functor).
* The Stacks Project, [Tag 03EL](https://stacks.math.columbia.edu/tag/03EL) (pullback of tensor
  products).
-/

public section

open CategoryTheory Limits MonoidalCategory
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

section IdComp

variable {Z : Scheme.{u}}

/-- The unit of a graded algebra, in the form required by `isoMkOfEq` for the trivial
identification of its components. -/
private lemma one_eq_comp_eqToHom (P : GradedQuasicoherentAlgebra X) :
    P.obj.toMon.one = P.obj.toMon.one ≫ eqToHom (congrFun (rfl : P.obj.X = P.obj.X) 0).symm :=
  (Category.comp_id _).symm

/-- The homogeneous multiplication of a graded algebra, in the form required by `isoMkOfEq` for
the trivial identification of its components. -/
private lemma mul_eq_comp_eqToHom (P : GradedQuasicoherentAlgebra X) (i j : ℕ) :
    P.obj.toMon.mul i j = (eqToHom (by rfl) : P.obj.X i ⊗ P.obj.X j ⟶ P.obj.X i ⊗ P.obj.X j) ≫
      P.obj.toMon.mul i j ≫ eqToHom (congrFun (rfl : P.obj.X = P.obj.X) (i + j)).symm :=
  ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- `pullback_obj_one`, bracketed as required by `isoMkOfEq`. -/
private lemma pullback_obj_one_eq :
    ((pullback f).obj A).obj.toMon.one =
      ((Scheme.Modules.pullbackObjUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map A.obj.toMon.one) ≫
          eqToHom (pullback_obj_obj_X f A 0).symm := by
  rw [pullback_obj_one, Category.assoc]

/-- The homogeneous components of the pullback `f^* A`, as one family, in the form required by
`isoMkOfEq`. -/
private lemma pullback_obj_X :
    ((pullback f).obj A).obj.X = fun n ↦ (Scheme.Modules.pullback f).obj (A.obj.X n) :=
  pullbackObj_X f A

/-- `pullback_obj_mul`, with a single transport on the source, bracketed as required by
`isoMkOfEq`. -/
private lemma pullback_obj_mul_eq (i j : ℕ) :
    ((pullback f).obj A).obj.toMon.mul i j =
      (eqToHom (by rw [pullback_obj_X]) :
        ((pullback f).obj A).obj.X i ⊗ ((pullback f).obj A).obj.X j ⟶ _) ≫
        (inv (δ (Scheme.Modules.pullback f) (A.obj.X i) (A.obj.X j)) ≫
          (Scheme.Modules.pullback f).map (A.obj.toMon.mul i j)) ≫
            eqToHom (pullback_obj_obj_X f A (i + j)).symm :=
  (mul_pullbackObj f A i j).trans (congrArg (_ ≫ · ≫ _) (pullbackMul_def f A i j))

/-- The component at `P` of `pullbackId`, given degreewise by `Scheme.Modules.pullbackId`. -/
private def pullbackIdApp (P : GradedQuasicoherentAlgebra X) : (pullback (𝟙 X)).obj P ≅ P :=
  isoMkOfEq (pullback_obj_X (𝟙 X) P) rfl (pullback_obj_one_eq (𝟙 X) P)
    (one_eq_comp_eqToHom P) (pullback_obj_mul_eq (𝟙 X) P) (mul_eq_comp_eqToHom P)
    (fun n ↦ (Scheme.Modules.pullbackId X).app (P.obj.X n))
    (by
      -- Unfolding `CommMon.toMon` types the unit of `P` on the carrier `P.obj.X`.
      dsimp only [CommMon.toMon]
      rw [Iso.app_hom, Category.assoc, NatTrans.naturality, Functor.id_map,
        ← Scheme.Modules.pullbackObjUnitIso_id, Iso.inv_hom_id_assoc])
    (fun i j ↦ by
      dsimp only [CommMon.toMon]
      rw [Iso.app_hom, Iso.app_hom, Iso.app_hom, Category.assoc, NatTrans.naturality,
        Functor.id_map, ← Scheme.Modules.pullback_id_δ_assoc, IsIso.inv_hom_id_assoc])

private lemma pullbackIdApp_hom_hom_hom (P : GradedQuasicoherentAlgebra X) (n : ℕ) :
    (pullbackIdApp P).hom.hom.hom.hom n =
      eqToHom (pullback_obj_obj_X (𝟙 X) P n) ≫
        (Scheme.Modules.pullbackId X).hom.app (P.obj.X n) :=
  -- The transport on the target is along `rfl`.
  (isoMkOfEq_hom_hom_hom_hom ..).trans (congrArg _ (Category.comp_id _))

private lemma pullbackIdApp_inv_hom_hom (P : GradedQuasicoherentAlgebra X) (n : ℕ) :
    (pullbackIdApp P).inv.hom.hom.hom n =
      (Scheme.Modules.pullbackId X).inv.app (P.obj.X n) ≫
        eqToHom (pullback_obj_obj_X (𝟙 X) P n).symm :=
  -- The transport on the source is along `rfl`.
  (isoMkOfEq_inv_hom_hom_hom ..).trans (Category.id_comp _)

variable (X) in
/-- Pullback of graded quasicoherent algebras along the identity is naturally the identity. -/
def pullbackId : pullback (𝟙 X) ≅ 𝟭 (GradedQuasicoherentAlgebra X) :=
  NatIso.ofComponents pullbackIdApp fun φ ↦ hom_ext _ _ fun n ↦ by
    simp only [Functor.id_obj, Functor.id_map, ObjectProperty.FullSubcategory.comp_hom,
      CommMon.comp_hom, GradedObject.categoryOfGradedObjects_comp]
    rw [pullbackIdApp_hom_hom_hom, pullbackIdApp_hom_hom_hom, pullback_map_hom_hom_hom]
    dsimp only [CommMon.toMon]
    simp

/-- The identity comparison of graded algebra pullback is Mathlib's identity comparison of module
pullback in each degree. -/
@[simp]
theorem pullbackId_hom_app_hom_hom_hom (P : GradedQuasicoherentAlgebra X) (n : ℕ) :
    ((pullbackId X).hom.app P).hom.hom.hom n =
      eqToHom (pullback_obj_obj_X (𝟙 X) P n) ≫
        (Scheme.Modules.pullbackId X).hom.app (P.obj.X n) :=
  pullbackIdApp_hom_hom_hom P n

/-- The inverse identity comparison of graded algebra pullback is Mathlib's inverse identity
comparison of module pullback in each degree. -/
@[simp]
theorem pullbackId_inv_app_hom_hom_hom (P : GradedQuasicoherentAlgebra X) (n : ℕ) :
    ((pullbackId X).inv.app P).hom.hom.hom n =
      (Scheme.Modules.pullbackId X).inv.app (P.obj.X n) ≫
        eqToHom (pullback_obj_obj_X (𝟙 X) P n).symm :=
  pullbackIdApp_inv_hom_hom P n

/-- The component at `P` of `pullbackComp`, given degreewise by `Scheme.Modules.pullbackComp`. -/
private def pullbackCompApp (g : X ⟶ Z) (P : GradedQuasicoherentAlgebra Z) :
    (pullback f).obj ((pullback g).obj P) ≅ (pullback (f ≫ g)).obj P :=
  isoMkOfEq
    ((pullback_obj_X f ((pullback g).obj P)).trans
      (funext fun n ↦ congrArg _ (pullback_obj_obj_X g P n)))
    (pullback_obj_X (f ≫ g) P)
    (oneM := (Scheme.Modules.pullbackObjUnitIso f).inv ≫
      (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackObjUnitIso g).inv ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map P.obj.toMon.one))
    (by
      simp only [pullback_obj_one]
      -- Unfolding `CommMon.toMon` types the units on their carriers, so the transports
      -- pulled back along `f` combine.
      dsimp only [CommMon.toMon]
      simp only [Functor.map_comp, Category.assoc]
      rw [eqToHom_map, eqToHom_trans])
    (pullback_obj_one_eq (f ≫ g) P)
    (mulM := fun i j ↦ inv (δ (Scheme.Modules.pullback f) _ _) ≫
      (Scheme.Modules.pullback f).map
        (inv (δ (Scheme.Modules.pullback g) (P.obj.X i) (P.obj.X j))) ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map (P.obj.toMon.mul i j)))
    (fun i j ↦ by
      rw [pullback_obj_mul_eq, pullback_obj_mul_eq]
      -- Unfolding `CommMon.toMon` types the multiplications on their carriers, so the
      -- transports pulled back along `f` can be split off.
      dsimp only [CommMon.toMon]
      simp only [Functor.map_comp, Category.assoc]
      rw [Functor.inv_δ_comp_map_eqToHom_assoc _ (pullback_obj_obj_X g P i)
        (pullback_obj_obj_X g P j), eqToHom_trans_assoc, eqToHom_map, eqToHom_trans])
    (pullback_obj_mul_eq (f ≫ g) P)
    (fun n ↦ (Scheme.Modules.pullbackComp f g).app (P.obj.X n))
    (by
      dsimp only [CommMon.toMon]
      rw [Iso.app_hom, Category.assoc, Category.assoc, ← Functor.comp_map, NatTrans.naturality,
        Scheme.Modules.pullbackObjUnitIso_inv_comp_assoc])
    (fun i j ↦ by
      dsimp only [CommMon.toMon]
      rw [Iso.app_hom, Iso.app_hom, Iso.app_hom, Category.assoc, Category.assoc,
        ← Functor.comp_map, NatTrans.naturality,
        Scheme.Modules.inv_δ_comp_pullbackComp_hom_app_assoc])

private lemma pullbackCompApp_hom_hom_hom (g : X ⟶ Z) (P : GradedQuasicoherentAlgebra Z)
    (n : ℕ) :
    (pullbackCompApp f g P).hom.hom.hom.hom n =
      eqToHom ((pullback_obj_obj_X f _ n).trans
        (congrArg _ (pullback_obj_obj_X g P n))) ≫
        (Scheme.Modules.pullbackComp f g).hom.app (P.obj.X n) ≫
          eqToHom (pullback_obj_obj_X (f ≫ g) P n).symm :=
  isoMkOfEq_hom_hom_hom_hom ..

private lemma pullbackCompApp_inv_hom_hom (g : X ⟶ Z) (P : GradedQuasicoherentAlgebra Z)
    (n : ℕ) :
    (pullbackCompApp f g P).inv.hom.hom.hom n =
      eqToHom (pullback_obj_obj_X (f ≫ g) P n) ≫
        (Scheme.Modules.pullbackComp f g).inv.app (P.obj.X n) ≫
          eqToHom ((pullback_obj_obj_X f _ n).trans
            (congrArg _ (pullback_obj_obj_X g P n))).symm :=
  isoMkOfEq_inv_hom_hom_hom ..

/-- Pullback of graded quasicoherent algebras respects composition. -/
def pullbackComp (g : X ⟶ Z) : pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  NatIso.ofComponents (pullbackCompApp f g) fun φ ↦ hom_ext _ _ fun n ↦ by
    simp only [Functor.comp_obj, Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      CommMon.comp_hom, GradedObject.categoryOfGradedObjects_comp]
    rw [pullbackCompApp_hom_hom_hom, pullbackCompApp_hom_hom_hom, pullback_map_hom_hom_hom,
      pullback_map_hom_hom_hom, pullback_map_hom_hom_hom]
    -- As in `pullbackId`, unfold `CommMon.toMon` to cancel the transports.
    dsimp only [CommMon.toMon]
    simp only [Functor.map_comp, Category.assoc, eqToHom_trans_assoc]
    rw [eqToHom_map, eqToHom_map]
    simp [← Functor.comp_map]

/-- The composition comparison of graded algebra pullback is Mathlib's composition comparison of
module pullback in each degree. -/
@[simp]
theorem pullbackComp_hom_app_hom_hom_hom (g : X ⟶ Z) (P : GradedQuasicoherentAlgebra Z)
    (n : ℕ) :
    ((pullbackComp f g).hom.app P).hom.hom.hom n =
      eqToHom ((pullback_obj_obj_X f _ n).trans
        (congrArg _ (pullback_obj_obj_X g P n))) ≫
        (Scheme.Modules.pullbackComp f g).hom.app (P.obj.X n) ≫
          eqToHom (pullback_obj_obj_X (f ≫ g) P n).symm :=
  pullbackCompApp_hom_hom_hom f g P n

/-- The inverse composition comparison of graded algebra pullback is Mathlib's inverse
composition comparison of module pullback in each degree. -/
@[simp]
theorem pullbackComp_inv_app_hom_hom_hom (g : X ⟶ Z) (P : GradedQuasicoherentAlgebra Z)
    (n : ℕ) :
    ((pullbackComp f g).inv.app P).hom.hom.hom n =
      eqToHom (pullback_obj_obj_X (f ≫ g) P n) ≫
        (Scheme.Modules.pullbackComp f g).inv.app (P.obj.X n) ≫
          eqToHom ((pullback_obj_obj_X f _ n).trans
            (congrArg _ (pullback_obj_obj_X g P n))).symm :=
  pullbackCompApp_inv_hom_hom f g P n

end IdComp

section DirectSum

open MonObj

/-- The pullback along `f` of the inclusion of the summand `Aₙ` of `⨁ₙ Aₙ`. -/
private abbrev pullbackιTotal (n : ℕ) :
    ((pullback f).obj A).obj.X n ⟶
      (Scheme.Modules.pullback f).obj (toQuasicoherentAlgebra.obj A).obj.X :=
  eqToHom (pullback_obj_obj_X f A n) ≫ (Scheme.Modules.pullback f).map (ιTotal A n)

/-- Pullback preserves the direct sum `⨁ₙ Aₙ`: the pullbacks of its summand inclusions exhibit
`f^* (⨁ₙ Aₙ)` as a direct sum of the `f^* Aₙ`. -/
private def isColimitPullbackιTotal : IsColimit (Cofan.mk _ (pullbackιTotal f A)) :=
  (IsColimit.precomposeHomEquiv
      (Discrete.natIso fun n ↦ eqToIso (pullback_obj_obj_X f A n.as)) _).symm
    (isColimitCofanMkObjOfIsColimit (Scheme.Modules.pullback f) _ _ (isColimitιTotal A))

/-- The comparison of modules `⨁ₙ f^* Aₙ ≅ f^* (⨁ₙ Aₙ)`, given on the summand `f^* Aₙ` by the
pullback of the inclusion of `Aₙ`. -/
private def directSumPullbackIso :
    (toQuasicoherentAlgebra.obj ((pullback f).obj A)).obj.X ≅
      (Scheme.Modules.pullback f).obj (toQuasicoherentAlgebra.obj A).obj.X :=
  (isColimitιTotal ((pullback f).obj A)).coconePointUniqueUpToIso (isColimitPullbackιTotal f A)

private lemma ιTotal_directSumPullbackIso_hom (n : ℕ) :
    ιTotal ((pullback f).obj A) n ≫ (directSumPullbackIso f A).hom = pullbackιTotal f A n :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (isColimitιTotal _) (isColimitPullbackιTotal f A)
    (Discrete.mk n)

private lemma pullbackιTotal_directSumPullbackIso_inv (n : ℕ) :
    pullbackιTotal f A n ≫ (directSumPullbackIso f A).inv = ιTotal ((pullback f).obj A) n :=
  IsColimit.comp_coconePointUniqueUpToIso_inv (isColimitιTotal _) (isColimitPullbackιTotal f A)
    (Discrete.mk n)

private lemma one_directSumPullbackIso_hom :
    η[(toQuasicoherentAlgebra.obj ((pullback f).obj A)).obj.X] ≫ (directSumPullbackIso f A).hom =
      (Scheme.Modules.pullbackObjUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map η[(toQuasicoherentAlgebra.obj A).obj.X] := by
  -- The carriers of quasicoherent algebras defeat `rw` and `simp` here, so the composites are
  -- reassociated by explicit equations and the transports cancelled for abstract modules.
  have key {P T Q Q' S : Y.Modules} (u : P ⟶ T) (m : T ⟶ Q') (h : Q' = Q) (h' : Q = Q')
      (n : Q' ⟶ S) : (u ≫ m ≫ eqToHom h) ≫ (eqToHom h' ≫ n) = u ≫ m ≫ n := by
    simp
  rw [← one_ιTotal, ← one_ιTotal]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg _ (ιTotal_directSumPullbackIso_hom f A 0)).trans ?_
  refine (congrArg (· ≫ _) (pullback_obj_one f A)).trans ?_
  refine (key _ _ _ _ _).trans ?_
  exact congrArg _ ((Scheme.Modules.pullback f).map_comp _ _).symm

private lemma mul_directSumPullbackIso_hom :
    μ[(toQuasicoherentAlgebra.obj ((pullback f).obj A)).obj.X] ≫ (directSumPullbackIso f A).hom =
      ((directSumPullbackIso f A).hom ⊗ₘ (directSumPullbackIso f A).hom) ≫
        inv (δ (Scheme.Modules.pullback f)
          (toQuasicoherentAlgebra.obj A).obj.X (toQuasicoherentAlgebra.obj A).obj.X) ≫
          (Scheme.Modules.pullback f).map μ[(toQuasicoherentAlgebra.obj A).obj.X] := by
  refine toQuasicoherentAlgebra_tensor_hom_ext fun i j ↦ ?_
  -- `Mon.mul_eq`, restated on the carrier `B.obj.X`: it is stated on `B.obj.toMon.X`, which
  -- `rw` does not identify with `B.obj.X` because `CommMon.toMon` is not reducible.
  have hmul (B : GradedQuasicoherentAlgebra Y) :
      GradedObject.Monoidal.ιTensorObj B.obj.X B.obj.X i j (i + j) rfl ≫ μ[B.obj.X] (i + j) =
        B.obj.toMon.mul i j :=
    (Mon.mul_eq B.obj.toMon i j).symm
  -- The pullback of `(ιᵢ ⊗ ιⱼ) ≫ μ = mul ≫ ιᵢ₊ⱼ` through the inverse tensor comparisons, stated
  -- for abstract modules: the carriers of quasicoherent algebras defeat `rw` and `simp`.
  have key {Ai Aj Ak M : X.Modules} [Ai.IsQuasicoherent] [M.IsQuasicoherent]
      {Pi Pj Pk : Y.Modules} (hi : Pi = (Scheme.Modules.pullback f).obj Ai)
      (hj : Pj = (Scheme.Modules.pullback f).obj Aj)
      (hk : (Scheme.Modules.pullback f).obj Ak = Pk)
      (hk' : Pk = (Scheme.Modules.pullback f).obj Ak)
      (hij : Pi ⊗ Pj = (Scheme.Modules.pullback f).obj Ai ⊗ (Scheme.Modules.pullback f).obj Aj)
      (ιi : Ai ⟶ M) (ιj : Aj ⟶ M) (ιk : Ak ⟶ M) (m : Ai ⊗ Aj ⟶ Ak) (n : M ⊗ M ⟶ M)
      (h : (ιi ⊗ₘ ιj) ≫ n = m ≫ ιk) :
      (eqToHom hij ≫ (inv (δ (Scheme.Modules.pullback f) Ai Aj) ≫
          (Scheme.Modules.pullback f).map m) ≫ eqToHom hk) ≫
          eqToHom hk' ≫ (Scheme.Modules.pullback f).map ιk =
        ((eqToHom hi ≫ (Scheme.Modules.pullback f).map ιi) ⊗ₘ
          (eqToHom hj ≫ (Scheme.Modules.pullback f).map ιj)) ≫
          inv (δ (Scheme.Modules.pullback f) M M) ≫
            (Scheme.Modules.pullback f).map n := by
    subst hi hj hk
    simp only [eqToHom_refl, Category.id_comp, Category.assoc]
    rw [← Functor.map_comp, ← h, Functor.map_comp, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [IsIso.inv_comp_eq, Functor.OplaxMonoidal.δ_natural_assoc, IsIso.hom_inv_id,
      Category.comp_id]
  rw [ιTotal_tensorHom_ιTotal_mul_assoc, tensorHom_comp_tensorHom_assoc,
    ιTotal_directSumPullbackIso_hom, ιTotal_directSumPullbackIso_hom f A i,
    ιTotal_directSumPullbackIso_hom f A j, reassoc_of% hmul, pullback_obj_mul_eq]
  exact key _ _ _ _ _ _ _ _ _ _ (mul_ιTotal A i j).symm

/-- The direct-sum algebra `⨁ₙ f^* Aₙ` of the pullback is the pullback `f^* (⨁ₙ Aₙ)` of the
direct-sum algebra. -/
private def toQuasicoherentAlgebraPullbackIsoApp :
    toQuasicoherentAlgebra.obj ((pullback f).obj A) ≅
      (QuasicoherentAlgebra.pullback f).obj (toQuasicoherentAlgebra.obj A) :=
  ObjectProperty.isoMk _ (CommMon.mkIso
    (directSumPullbackIso f A ≪≫ eqToIso (QuasicoherentAlgebra.pullback_obj_X f _).symm)
    (by
      rw [QuasicoherentAlgebra.pullback_obj_one]
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) (one_directSumPullbackIso_hom f A)).trans (Category.assoc _ _ _)))
    (by
      rw [QuasicoherentAlgebra.pullback_obj_mul]
      -- As in `mul_directSumPullbackIso_hom`, cancel the carrier transports for abstract modules.
      have key {S P T Q : Y.Modules} (g : S ⟶ P) (h : P = T) (h' : T = P) (r : P ⊗ P ⟶ Q) :
          ((g ≫ eqToHom h) ⊗ₘ (g ≫ eqToHom h)) ≫ (eqToHom h' ⊗ₘ eqToHom h') ≫ r =
            (g ⊗ₘ g) ≫ r := by
        subst h
        simp
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
        (mul_directSumPullbackIso_hom f A)).trans ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans
            (key _ (QuasicoherentAlgebra.pullback_obj_X f _).symm _ _).symm)))))

private lemma ιTotal_toQuasicoherentAlgebraPullbackIsoApp_hom (n : ℕ) :
    ιTotal ((pullback f).obj A) n ≫ (toQuasicoherentAlgebraPullbackIsoApp f A).hom.hom.hom.hom =
      eqToHom (pullback_obj_obj_X f A n) ≫
        (Scheme.Modules.pullback f).map (ιTotal A n) ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X f _).symm :=
  (reassoc_of% ιTotal_directSumPullbackIso_hom f A n) _

/-- The pullback of the direct-sum algebra of a graded quasicoherent algebra is the direct-sum
algebra of its pullback: `f^* (⨁ₙ Aₙ) ≅ ⨁ₙ f^* Aₙ` as quasicoherent algebras, naturally in `A`.
Its inverse is, on the summand `f^* Aₙ`, the pullback of the inclusion of `Aₙ`
(`ιTotal_pullbackToQuasicoherentAlgebraIso_inv_app`). -/
def pullbackToQuasicoherentAlgebraIso :
    toQuasicoherentAlgebra ⋙ QuasicoherentAlgebra.pullback f ≅
      pullback f ⋙ toQuasicoherentAlgebra :=
  Iso.symm <| NatIso.ofComponents (toQuasicoherentAlgebraPullbackIsoApp f) fun {A B} φ ↦ by
    apply ObjectProperty.hom_ext
    apply CommMon.hom_ext
    refine toQuasicoherentAlgebra_hom_ext fun n ↦ ?_
    simp only [Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom, CommMon.comp_hom]
    refine ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
      (ιTotal_toQuasicoherentAlgebra_map ((pullback f).map φ) n)).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
          (ιTotal_toQuasicoherentAlgebraPullbackIsoApp_hom f B n))))).trans
      (Eq.trans ?_ ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) (ιTotal_toQuasicoherentAlgebraPullbackIsoApp_hom f A n))).symm)
    rw [pullback_map_hom_hom_hom, QuasicoherentAlgebra.pullback_map_hom_hom_hom]
    -- Cancel the carrier transports for abstract modules, as in `mul_directSumPullbackIso_hom`.
    have key {a b MA MB : X.Modules} {Sa Sb TA TB : Y.Modules} (φn : a ⟶ b) (ιA : a ⟶ MA)
        (ιB : b ⟶ MB) (ψ : MA ⟶ MB) (hψ : ιA ≫ ψ = φn ≫ ιB)
        (h₁ : Sa = (Scheme.Modules.pullback f).obj a)
        (h₂ : (Scheme.Modules.pullback f).obj b = Sb)
        (h₃ : Sb = (Scheme.Modules.pullback f).obj b)
        (h₄ : (Scheme.Modules.pullback f).obj MB = TB)
        (h₅ : Sa = (Scheme.Modules.pullback f).obj a)
        (h₆ : (Scheme.Modules.pullback f).obj MA = TA)
        (h₇ : TA = (Scheme.Modules.pullback f).obj MA)
        (h₈ : (Scheme.Modules.pullback f).obj MB = TB) :
        (eqToHom h₁ ≫ (Scheme.Modules.pullback f).map φn ≫ eqToHom h₂) ≫
            eqToHom h₃ ≫ (Scheme.Modules.pullback f).map ιB ≫ eqToHom h₄ =
          (eqToHom h₅ ≫ (Scheme.Modules.pullback f).map ιA ≫ eqToHom h₆) ≫
            eqToHom h₇ ≫ (Scheme.Modules.pullback f).map ψ ≫ eqToHom h₈ := by
      subst h₁ h₃ h₄ h₆
      simp [← Functor.map_comp, hψ]
    exact key _ _ _ _ (ιTotal_toQuasicoherentAlgebra_map φ n) _ _ _ _ _ _ _ _

/-- On the summand `f^* Aₙ`, the comparison `⨁ₙ f^* Aₙ ≅ f^* (⨁ₙ Aₙ)` is the pullback of the
inclusion of `Aₙ`. -/
@[simp, reassoc]
theorem ιTotal_pullbackToQuasicoherentAlgebraIso_inv_app (n : ℕ) :
    ιTotal ((pullback f).obj A) n ≫
        ((pullbackToQuasicoherentAlgebraIso f).inv.app A).hom.hom.hom =
      eqToHom (pullback_obj_obj_X f A n) ≫
        (Scheme.Modules.pullback f).map (ιTotal A n) ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X f _).symm :=
  ιTotal_toQuasicoherentAlgebraPullbackIsoApp_hom f A n

/-- The comparison `f^* (⨁ₙ Aₙ) ≅ ⨁ₙ f^* Aₙ` sends the pullback of the summand `Aₙ` to the
summand `f^* Aₙ`. -/
@[reassoc]
theorem pullback_map_ιTotal_pullbackToQuasicoherentAlgebraIso_hom_app (n : ℕ) :
    (Scheme.Modules.pullback f).map (ιTotal A n) ≫
        eqToHom (QuasicoherentAlgebra.pullback_obj_X f _).symm ≫
          ((pullbackToQuasicoherentAlgebraIso f).hom.app A).hom.hom.hom =
      eqToHom (pullback_obj_obj_X f A n).symm ≫ ιTotal ((pullback f).obj A) n := by
  have h : ((pullbackToQuasicoherentAlgebraIso f).hom.app A).hom.hom.hom =
      eqToHom (QuasicoherentAlgebra.pullback_obj_X f _) ≫ (directSumPullbackIso f A).inv :=
    -- The inverse of the component built from `directSumPullbackIso` and a transport.
    (rfl)
  rw [h]
  -- The carrier of the pulled-back algebra defeats `rw` here; cancel the transports directly.
  exact (congrArg (_ ≫ ·) ((eqToHom_trans_assoc _ _ _).trans
    ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _)))).trans
      ((eqToIso (pullback_obj_obj_X f A n)).eq_inv_comp.mpr
        ((Category.assoc _ _ _).symm.trans (pullbackιTotal_directSumPullbackIso_inv f A n)))

end DirectSum

end GradedQuasicoherentAlgebra

end

end AlgebraicGeometry

end TauCeti
