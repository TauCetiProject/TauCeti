/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.Basic

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

The algebra laws of `f^* A` are those of `A` transported along the strong symmetric monoidal
pullback of quasicoherent sheaves to modules on `Y`
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

variable {X Y : Scheme.{u}}

section Transport

variable (A : GradedQuasicoherentAlgebra X)

/-- The homogeneous components of a graded quasicoherent algebra, as quasicoherent sheaves. -/
private def components : GradedObject ℕ (QuasicoherentSheaf X) :=
  fun n ↦ ⟨A.obj.X n, (isGradedQuasicoherentAlgebra_iff _).mp A.property n⟩

/-- The unit of a graded quasicoherent algebra, as a morphism of quasicoherent sheaves. -/
private def oneQ : 𝟙_ (QuasicoherentSheaf X) ⟶ components A 0 :=
  ObjectProperty.homMk A.obj.toMon.one

/-- The homogeneous multiplications of a graded quasicoherent algebra, as morphisms of
quasicoherent sheaves. -/
private def mulQ (i j : ℕ) : components A i ⊗ components A j ⟶ components A (i + j) :=
  ObjectProperty.homMk (A.obj.toMon.mul i j)

/-- Transport between homogeneous components, read on underlying modules. -/
private lemma eqToHom_components_hom {i j : ℕ} (h : i = j) :
    (eqToHom (congrArg (components A) h)).hom = eqToHom (congrArg A.obj.X h) := by
  subst h
  rfl

private lemma oneQ_mulQ (n : ℕ) :
    (oneQ A ▷ components A n) ≫ mulQ A 0 n =
      (λ_ (components A n)).hom ≫ eqToHom (congrArg (components A) (zero_add n).symm) := by
  apply ObjectProperty.hom_ext
  -- Composition, whiskering and unitors of the full monoidal subcategory are those of modules.
  change (A.obj.toMon.one ▷ A.obj.X n) ≫ A.obj.toMon.mul 0 n = (λ_ (A.obj.X n)).hom ≫ _
  rw [eqToHom_components_hom A (zero_add n).symm]
  exact Mon.one_mul A.obj.toMon n

private lemma mulQ_oneQ (n : ℕ) :
    (components A n ◁ oneQ A) ≫ mulQ A n 0 =
      (ρ_ (components A n)).hom ≫ eqToHom (congrArg (components A) (add_zero n).symm) := by
  apply ObjectProperty.hom_ext
  -- As in `oneQ_mulQ`, read the full-subcategory structure maps on underlying modules.
  change (A.obj.X n ◁ A.obj.toMon.one) ≫ A.obj.toMon.mul n 0 = (ρ_ (A.obj.X n)).hom ≫ _
  rw [eqToHom_components_hom A (add_zero n).symm]
  exact Mon.mul_one A.obj.toMon n

private lemma mulQ_assoc (i j k : ℕ) :
    (mulQ A i j ▷ components A k) ≫ mulQ A (i + j) k =
      (α_ _ _ _).hom ≫ (components A i ◁ mulQ A j k) ≫ mulQ A i (j + k) ≫
        eqToHom (congrArg (components A) (add_assoc i j k).symm) := by
  apply ObjectProperty.hom_ext
  -- As in `oneQ_mulQ`, read the full-subcategory structure maps on underlying modules.
  change (A.obj.toMon.mul i j ▷ A.obj.X k) ≫ A.obj.toMon.mul (i + j) k =
    (α_ (A.obj.X i) (A.obj.X j) (A.obj.X k)).hom ≫ (A.obj.X i ◁ A.obj.toMon.mul j k) ≫
      A.obj.toMon.mul i (j + k) ≫ _
  rw [eqToHom_components_hom A (add_assoc i j k).symm]
  exact Mon.mul_assoc A.obj.toMon i j k

private lemma mulQ_comm (i j : ℕ) :
    (β_ (components A i) (components A j)).hom ≫ mulQ A j i =
      mulQ A i j ≫ eqToHom (congrArg (components A) (add_comm i j)) := by
  apply ObjectProperty.hom_ext
  -- As in `oneQ_mulQ`, read the full-subcategory structure maps on underlying modules.
  change (β_ (A.obj.X i) (A.obj.X j)).hom ≫ A.obj.toMon.mul j i = A.obj.toMon.mul i j ≫ _
  rw [eqToHom_components_hom A (add_comm i j)]
  exact CommMon.mul_comm A.obj i j

end Transport

variable (f : Y ⟶ X)

/-- Pullback of quasicoherent sheaves on `X` to modules on `Y`, a strong symmetric monoidal
functor. -/
private abbrev pullbackQ : QuasicoherentSheaf X ⥤ Y.Modules :=
  (ObjectProperty.ι _ : QuasicoherentSheaf X ⥤ X.Modules) ⋙ Scheme.Modules.pullback f

private lemma ε_pullbackQ : ε (pullbackQ f) = (Scheme.Modules.pullbackObjUnitIso f).inv :=
  (Iso.comp_hom_eq_id _).mp
    ((congrArg (ε (pullbackQ f) ≫ ·) (Scheme.Modules.pullbackToModules_η f).symm).trans
      (Functor.Monoidal.ε_η (pullbackQ f)))

variable (A : GradedQuasicoherentAlgebra X)

private lemma μ_pullbackQ_components (i j : ℕ) :
    μ (pullbackQ f) (components A i) (components A j) =
      inv (δ (Scheme.Modules.pullback f) (A.obj.X i) (A.obj.X j)) :=
  IsIso.eq_inv_of_hom_inv_id (f := δ (Scheme.Modules.pullback f) (A.obj.X i) (A.obj.X j))
    ((congrArg (· ≫ μ (pullbackQ f) (components A i) (components A j))
      (Scheme.Modules.pullbackToModules_δ f (components A i) (components A j)).symm).trans
      (Functor.Monoidal.δ_μ (pullbackQ f) (components A i) (components A j)))

/-- The unit `𝒪_Y ≅ f^* 𝒪_X ⟶ f^* A₀` of the pullback of a graded quasicoherent algebra. -/
private def pullbackOne :
    𝟙_ Y.Modules ⟶ (Scheme.Modules.pullback f).obj (A.obj.X 0) :=
  ε (pullbackQ f) ≫ (pullbackQ f).map (oneQ A)

/-- The homogeneous multiplication `f^* Aᵢ ⊗ f^* Aⱼ ≅ f^* (Aᵢ ⊗ Aⱼ) ⟶ f^* Aᵢ₊ⱼ` of the pullback of
a graded quasicoherent algebra. -/
private def pullbackMul (i j : ℕ) :
    (Scheme.Modules.pullback f).obj (A.obj.X i) ⊗ (Scheme.Modules.pullback f).obj (A.obj.X j) ⟶
      (Scheme.Modules.pullback f).obj (A.obj.X (i + j)) :=
  μ (pullbackQ f) (components A i) (components A j) ≫ (pullbackQ f).map (mulQ A i j)

private lemma pullbackMul_eq (i j : ℕ) :
    pullbackMul f A i j =
      ((Iso.refl ((Scheme.Modules.pullback f).obj (A.obj.X i))).hom ⊗ₘ
          (Iso.refl ((Scheme.Modules.pullback f).obj (A.obj.X j))).hom) ≫
        μ (pullbackQ f) (components A i) (components A j) ≫ (pullbackQ f).map (mulQ A i j) ≫
          (Iso.refl ((Scheme.Modules.pullback f).obj (A.obj.X (i + j)))).inv := by
  simp only [Iso.refl_hom, Iso.refl_inv, id_tensorHom_id, Category.id_comp]
  -- `pullbackQ f` is reducible, so the remaining identity composite is `pullbackMul f A i j`
  -- followed by the identity of its target, which `simp` does not see across the two category
  -- instances on modules.
  rfl

private lemma pullbackOne_eq :
    pullbackOne f A =
      ε (pullbackQ f) ≫ (pullbackQ f).map (oneQ A) ≫
        (Iso.refl ((Scheme.Modules.pullback f).obj (A.obj.X 0))).inv := by
  simp only [Iso.refl_inv]
  -- As in `pullbackMul_eq`, the remaining identity is that of the target of `pullbackOne f A`.
  rfl

private lemma pullbackOne_def :
    pullbackOne f A = (Scheme.Modules.pullbackObjUnitIso f).inv ≫
      (Scheme.Modules.pullback f).map A.obj.toMon.one := by
  rw [pullbackOne, ε_pullbackQ]
  -- `pullbackQ f` acts on morphisms of quasicoherent sheaves by pullback of the underlying maps.
  rfl

private lemma pullbackMul_def (i j : ℕ) :
    pullbackMul f A i j =
      inv (δ (Scheme.Modules.pullback f) (A.obj.X i) (A.obj.X j)) ≫
        (Scheme.Modules.pullback f).map (A.obj.toMon.mul i j) := by
  rw [pullbackMul, μ_pullbackQ_components]
  -- `pullbackQ f` acts on morphisms of quasicoherent sheaves by pullback of the underlying maps.
  rfl

/-- The homogeneous components `f^* Aₙ` of the pullback of a graded quasicoherent algebra. -/
private abbrev pullbackComponents : GradedObject ℕ Y.Modules :=
  fun n ↦ (Scheme.Modules.pullback f).obj (A.obj.X n)

private lemma pullbackOne_mul (n : ℕ) :
    (pullbackOne f A ▷ pullbackComponents f A n) ≫ pullbackMul f A 0 n =
      (λ_ (pullbackComponents f A n)).hom ≫
        eqToHom (congrArg (pullbackComponents f A) (zero_add n).symm) :=
  GradedObject.one_mul_of_laxMonoidal (F := pullbackQ f) (X := components A)
    (Y := pullbackComponents f A) (e := fun _ ↦ Iso.refl _) (mulQ A) (pullbackMul f A)
    (pullbackMul_eq f A) (oneQ A) (pullbackOne f A) (pullbackOne_eq f A) (oneQ_mulQ A) n

private lemma pullbackMul_one (n : ℕ) :
    (pullbackComponents f A n ◁ pullbackOne f A) ≫ pullbackMul f A n 0 =
      (ρ_ (pullbackComponents f A n)).hom ≫
        eqToHom (congrArg (pullbackComponents f A) (add_zero n).symm) :=
  GradedObject.mul_one_of_laxMonoidal (F := pullbackQ f) (X := components A)
    (Y := pullbackComponents f A) (e := fun _ ↦ Iso.refl _) (mulQ A) (pullbackMul f A)
    (pullbackMul_eq f A) (oneQ A) (pullbackOne f A) (pullbackOne_eq f A) (mulQ_oneQ A) n

private lemma pullbackMul_assoc (i j k : ℕ) :
    (pullbackMul f A i j ▷ pullbackComponents f A k) ≫ pullbackMul f A (i + j) k =
      (α_ _ _ _).hom ≫ (pullbackComponents f A i ◁ pullbackMul f A j k) ≫
        pullbackMul f A i (j + k) ≫
          eqToHom (congrArg (pullbackComponents f A) (add_assoc i j k).symm) :=
  GradedObject.mul_assoc_of_laxMonoidal (F := pullbackQ f) (X := components A)
    (Y := pullbackComponents f A) (e := fun _ ↦ Iso.refl _) (mulQ A) (pullbackMul f A)
    (pullbackMul_eq f A) (mulQ_assoc A) i j k

private lemma pullbackMul_comm (i j : ℕ) :
    (β_ (pullbackComponents f A i) (pullbackComponents f A j)).hom ≫ pullbackMul f A j i =
      pullbackMul f A i j ≫ eqToHom (congrArg (pullbackComponents f A) (add_comm i j)) :=
  GradedObject.mul_comm_of_laxBraided (F := pullbackQ f) (X := components A)
    (Y := pullbackComponents f A) (e := fun _ ↦ Iso.refl _) (mulQ A) (pullbackMul f A)
    (pullbackMul_eq f A) (mulQ_comm A) i j

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

variable {A} {B C : GradedQuasicoherentAlgebra X}

/-- The homogeneous components of a morphism of graded quasicoherent algebras, as morphisms of
quasicoherent sheaves. -/
private def homQ (g : A ⟶ B) (n : ℕ) : components A n ⟶ components B n :=
  ObjectProperty.homMk (g.hom.hom.hom n)

private lemma homQ_id (n : ℕ) : homQ (𝟙 A) n = 𝟙 (components A n) :=
  (rfl)

private lemma homQ_comp (g : A ⟶ B) (h : B ⟶ C) (n : ℕ) :
    homQ g n ≫ homQ h n = homQ (g ≫ h) n :=
  (rfl)

private lemma oneQ_homQ (g : A ⟶ B) : oneQ A ≫ homQ g 0 = oneQ B :=
  ObjectProperty.hom_ext _ (Mon.one_map g.hom.hom)

private lemma mulQ_homQ (g : A ⟶ B) (i j : ℕ) :
    (homQ g i ⊗ₘ homQ g j) ≫ mulQ B i j = mulQ A i j ≫ homQ g (i + j) :=
  ObjectProperty.hom_ext _ (Mon.map_mul g.hom.hom i j)

private lemma pullbackOne_map (g : A ⟶ B) :
    pullbackOne f A ≫ (pullbackQ f).map (homQ g 0) = pullbackOne f B :=
  (Category.assoc _ _ _).trans (congrArg (ε (pullbackQ f) ≫ ·)
    (((pullbackQ f).map_comp _ _).symm.trans (congrArg (pullbackQ f).map (oneQ_homQ g))))

private lemma pullbackMul_map (g : A ⟶ B) (i j : ℕ) :
    ((pullbackQ f).map (homQ g i) ⊗ₘ (pullbackQ f).map (homQ g j)) ≫ pullbackMul f B i j =
      pullbackMul f A i j ≫ (pullbackQ f).map (homQ g (i + j)) :=
  GradedObject.map_mul_of_laxMonoidal (F := pullbackQ f) (X := components A)
    (Y := pullbackComponents f A) (e := fun _ ↦ Iso.refl _) (mulQ A) (pullbackMul f A)
    (pullbackMul_eq f A) (X' := components B) (Y' := pullbackComponents f B)
    (e' := fun _ ↦ Iso.refl _) (mulQ B) (pullbackMul f B) (pullbackMul_eq f B) (homQ g)
    (fun n ↦ (pullbackQ f).map (homQ g n))
    (fun _ ↦ ((Category.id_comp _).trans (Category.comp_id _)).symm)
    (mulQ_homQ g) i j

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
    (fun n ↦ (pullbackQ f).map (homQ g n)) (pullbackOne_map f g) (pullbackMul_map f g)
  map_id _ := homMkOfEq_id _ _ _ _ _ _ fun n ↦
    (congrArg (pullbackQ f).map (homQ_id n)).trans ((pullbackQ f).map_id _)
  map_comp g h := homMkOfEq_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fun n ↦
    ((pullbackQ f).map_comp _ _).symm.trans (congrArg (pullbackQ f).map (homQ_comp g h n))

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
