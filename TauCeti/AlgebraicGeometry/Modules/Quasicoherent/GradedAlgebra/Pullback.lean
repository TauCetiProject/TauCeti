/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.DirectSum
public import TauCeti.AlgebraicGeometry.RelativeSpec.PullbackAlgebra
public import TauCeti.CategoryTheory.Monoidal.EqToHom

/-!
# Pullback of graded quasicoherent algebras

For a morphism of schemes `f : X ⟶ Y`, the pullback of a nonnegatively graded quasicoherent
algebra `A = (Aₙ)ₙ` on `Y` is the graded quasicoherent algebra `f^* A` on `X` whose homogeneous
components are the pullbacks `f^* Aₙ`. Its unit is `𝒪_X ≅ f^* 𝒪_Y ⟶ f^* A₀` and its homogeneous
multiplications are `f^* Aᵢ ⊗ f^* Aⱼ ≅ f^* (Aᵢ ⊗ Aⱼ) ⟶ f^* Aᵢ₊ⱼ`; the tensor comparisons are
invertible because the components are quasicoherent. The algebra laws are transported from those
of `A` along the strong symmetric monoidal pullback from quasicoherent sheaves on `Y` to modules
on `X` (`CategoryTheory.GradedObject.mul_assoc_of_laxMonoidal` and its companions). Pullback
along the identity and along a composite are identified with the identity and with the composite
of pullbacks, degree by degree through the corresponding comparisons for modules.

Pullback commutes with the two ways of forgetting structure. Its degree-`n` component is the
pullback of the degree-`n` component (`pullbackDegreeIso`). Its underlying direct-sum algebra is
the pullback of the direct-sum algebra, `f^* (⨁ₙ Aₙ) ≅ ⨁ₙ f^* Aₙ` as quasicoherent algebras
(`pullbackToQuasicoherentAlgebraIso`), because pullback preserves direct sums. These are the
comparisons through which base change of graded relative spectra, such as linear schemes, reduces
to base change of relative spectra.

## Main declarations

* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.pullback`: pullback of graded
  quasicoherent algebras along a morphism of schemes, with characteristic equations
  `pullback_obj_obj_X`, `pullback_obj_one`, `pullback_obj_mul` and `pullback_map_hom_hom_hom`;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.pullbackId` and
  `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.pullbackComp`: its identity and
  composition isomorphisms, given in each degree by Mathlib's `Scheme.Modules.pullbackId` and
  `Scheme.Modules.pullbackComp`;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.pullbackDegreeIso`: the
  homogeneous components of `f^* A` are the pullbacks of those of `A`;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.pullbackToQuasicoherentAlgebraIso`: the
  isomorphism `f^* (⨁ₙ Aₙ) ≅ ⨁ₙ f^* Aₙ` of quasicoherent algebras, natural in `A`, whose inverse
  is the pullback of the inclusion of `Aₙ` on the summand `f^* Aₙ`
  (`ιTotal_pullbackToQuasicoherentAlgebraIso_inv_app`).

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §1.5 and §8.
* The Stacks Project, [Tag 01LQ](https://stacks.math.columbia.edu/tag/01LQ) (relative spectrum as
  a functor).
-/

public section

open CategoryTheory Limits MonoidalCategory MonObj

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace GradedQuasicoherentAlgebra

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Pullback from quasicoherent sheaves on `Y` to all modules on `X`, which is strong braided
monoidal (`Scheme.Modules.pullbackToModulesBraided`). -/
private abbrev pullbackToModules : QuasicoherentSheaf Y ⥤ X.Modules :=
  (ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f

variable (A : GradedQuasicoherentAlgebra Y)

/-- The homogeneous component of `A` in degree `n`, as a quasicoherent sheaf. This is the object
of `(degree n).obj A`, restated because `degree` is not exposed and the transported algebra laws
below need its underlying module definitionally. -/
private abbrev component (n : ℕ) : QuasicoherentSheaf Y :=
  ⟨A.obj.X n, inferInstance⟩

/-- The homogeneous multiplication of `A`, as a morphism of quasicoherent sheaves. -/
private abbrev componentMul (i j : ℕ) :
    component A i ⊗ component A j ⟶ component A (i + j) :=
  ObjectProperty.homMk (A.obj.toMon.mul i j)

/-- The unit of `A`, as a morphism of quasicoherent sheaves. -/
private abbrev componentOne : 𝟙_ (QuasicoherentSheaf Y) ⟶ component A 0 :=
  ObjectProperty.homMk A.obj.toMon.one

private lemma eqToHom_component_hom {a b : ℕ} (h : a = b) :
    (eqToHom (congrArg (component A) h)).hom = eqToHom (congrArg A.obj.X h) := by
  subst h
  rfl

private lemma componentOne_mul (n : ℕ) :
    (componentOne A ▷ component A n) ≫ componentMul A 0 n =
      (λ_ (component A n)).hom ≫ eqToHom (congrArg (component A) (zero_add n).symm) := by
  apply ObjectProperty.hom_ext
  refine (A.obj.toMon.one_mul n).trans ?_
  rw [ObjectProperty.FullSubcategory.comp_hom, eqToHom_component_hom A (zero_add n).symm]
  -- The monoidal structure of quasicoherent sheaves is that of the underlying modules, so the
  -- unitors, associator, braiding and whiskerings agree with those of modules definitionally.
  rfl

private lemma componentMul_one (n : ℕ) :
    (component A n ◁ componentOne A) ≫ componentMul A n 0 =
      (ρ_ (component A n)).hom ≫ eqToHom (congrArg (component A) (add_zero n).symm) := by
  apply ObjectProperty.hom_ext
  refine (A.obj.toMon.mul_one n).trans ?_
  rw [ObjectProperty.FullSubcategory.comp_hom, eqToHom_component_hom A (add_zero n).symm]
  -- The monoidal structure of quasicoherent sheaves is that of the underlying modules, so the
  -- unitors, associator, braiding and whiskerings agree with those of modules definitionally.
  rfl

private lemma componentMul_assoc (i j k : ℕ) :
    (componentMul A i j ▷ component A k) ≫ componentMul A (i + j) k =
      (α_ _ _ _).hom ≫ (component A i ◁ componentMul A j k) ≫ componentMul A i (j + k) ≫
        eqToHom (congrArg (component A) (add_assoc i j k).symm) := by
  apply ObjectProperty.hom_ext
  refine (A.obj.toMon.mul_assoc i j k).trans ?_
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom, eqToHom_component_hom A (add_assoc i j k).symm]
  -- The monoidal structure of quasicoherent sheaves is that of the underlying modules, so the
  -- unitors, associator, braiding and whiskerings agree with those of modules definitionally.
  rfl

private lemma componentMul_comm (i j : ℕ) :
    (β_ (component A i) (component A j)).hom ≫ componentMul A j i =
      componentMul A i j ≫ eqToHom (congrArg (component A) (add_comm i j)) := by
  apply ObjectProperty.hom_ext
  refine (A.obj.mul_comm i j).trans ?_
  rw [ObjectProperty.FullSubcategory.comp_hom, eqToHom_component_hom A (add_comm i j)]
  -- The monoidal structure of quasicoherent sheaves is that of the underlying modules, so the
  -- unitors, associator, braiding and whiskerings agree with those of modules definitionally.
  rfl

/-- The unit `𝒪_X ≅ f^* 𝒪_Y ⟶ f^* A₀` of the pullback of `A`. -/
private abbrev pullbackOne : 𝟙_ X.Modules ⟶ (Scheme.Modules.pullback f).obj (A.obj.X 0) :=
  Functor.LaxMonoidal.ε (pullbackToModules f) ≫ (pullbackToModules f).map (componentOne A)

/-- The homogeneous multiplication `f^* Aᵢ ⊗ f^* Aⱼ ≅ f^* (Aᵢ ⊗ Aⱼ) ⟶ f^* Aᵢ₊ⱼ` of the pullback
of `A`. -/
private abbrev pullbackMul (i j : ℕ) :
    (Scheme.Modules.pullback f).obj (A.obj.X i) ⊗ (Scheme.Modules.pullback f).obj (A.obj.X j) ⟶
      (Scheme.Modules.pullback f).obj (A.obj.X (i + j)) :=
  Functor.LaxMonoidal.μ (pullbackToModules f) (component A i) (component A j) ≫
    (pullbackToModules f).map (componentMul A i j)

private lemma pullbackMul_eq (i j : ℕ) :
    pullbackMul f A i j =
      ((Iso.refl ((pullbackToModules f).obj (component A i))).hom ⊗ₘ
          (Iso.refl ((pullbackToModules f).obj (component A j))).hom) ≫
        Functor.LaxMonoidal.μ (pullbackToModules f) (component A i) (component A j) ≫
          (pullbackToModules f).map (componentMul A i j) ≫
            (Iso.refl ((pullbackToModules f).obj (component A (i + j)))).inv := by
  rw [Iso.refl_hom, Iso.refl_hom, Iso.refl_inv, id_tensorHom_id, Category.id_comp,
    Category.comp_id]

private lemma pullbackOne_eq :
    pullbackOne f A =
      Functor.LaxMonoidal.ε (pullbackToModules f) ≫
        (pullbackToModules f).map (componentOne A) ≫
          (Iso.refl ((pullbackToModules f).obj (component A 0))).inv := by
  rw [Iso.refl_inv, Category.comp_id]

/-- The pullback `f^* A` of a graded quasicoherent algebra `A` on `Y` along `f : X ⟶ Y`: its
homogeneous components are the pullbacks `f^* Aₙ`, with unit and homogeneous multiplications
pulled back through the monoidal comparisons of pullback. -/
private def pullbackObj : GradedQuasicoherentAlgebra X :=
  ofHomogeneous (fun n ↦ (Scheme.Modules.pullback f).obj (A.obj.X n)) (pullbackOne f A)
    (pullbackMul f A)
    (GradedObject.one_mul_of_laxMonoidal _ _ (pullbackMul_eq f A) _ _ (pullbackOne_eq f A)
      (componentOne_mul A))
    (GradedObject.mul_one_of_laxMonoidal _ _ (pullbackMul_eq f A) _ _ (pullbackOne_eq f A)
      (componentMul_one A))
    (GradedObject.mul_assoc_of_laxMonoidal _ _ (pullbackMul_eq f A) (componentMul_assoc A))
    (GradedObject.mul_comm_of_laxBraided _ _ (pullbackMul_eq f A) (componentMul_comm A))

private lemma pullbackObj_X :
    (pullbackObj f A).obj.X = fun n ↦ (Scheme.Modules.pullback f).obj (A.obj.X n) :=
  ofHomogeneous_obj_X ..

private lemma pullbackObj_one :
    (pullbackObj f A).obj.toMon.one =
      pullbackOne f A ≫ eqToHom (congrFun (pullbackObj_X f A) 0).symm :=
  one_ofHomogeneous ..

private lemma pullbackObj_mul (i j : ℕ) :
    (pullbackObj f A).obj.toMon.mul i j =
      eqToHom (by rw [CommMon.toMon_X, pullbackObj_X]) ≫ pullbackMul f A i j ≫
        eqToHom (congrFun (pullbackObj_X f A) (i + j)).symm :=
  mul_ofHomogeneous ..

variable {A} {B : GradedQuasicoherentAlgebra Y}

/-- The degree-`n` component of a graded algebra morphism, as a morphism of quasicoherent
sheaves. -/
private abbrev componentHom (φ : A ⟶ B) (n : ℕ) : component A n ⟶ component B n :=
  ObjectProperty.homMk (φ.hom.hom.hom n)

private lemma componentHom_mul (φ : A ⟶ B) (i j : ℕ) :
    (componentHom φ i ⊗ₘ componentHom φ j) ≫ componentMul B i j =
      componentMul A i j ≫ componentHom φ (i + j) :=
  ObjectProperty.hom_ext _ (Mon.map_mul φ.hom.hom i j)

private lemma pullbackOne_map (φ : A ⟶ B) :
    pullbackOne f A ≫ (Scheme.Modules.pullback f).map (φ.hom.hom.hom 0) = pullbackOne f B := by
  rw [Category.assoc]
  refine congrArg (Functor.LaxMonoidal.ε (pullbackToModules f) ≫ ·) ?_
  refine ((pullbackToModules f).map_comp (componentOne A) (componentHom φ 0)).symm.trans ?_
  exact congrArg (pullbackToModules f).map (ObjectProperty.hom_ext _ (Mon.one_map φ.hom.hom))

private lemma pullbackMul_map (φ : A ⟶ B) (i j : ℕ) :
    ((Scheme.Modules.pullback f).map (φ.hom.hom.hom i) ⊗ₘ
        (Scheme.Modules.pullback f).map (φ.hom.hom.hom j)) ≫ pullbackMul f B i j =
      pullbackMul f A i j ≫ (Scheme.Modules.pullback f).map (φ.hom.hom.hom (i + j)) := by
  refine GradedObject.map_mul_of_laxMonoidal (F := pullbackToModules f) (X := component A)
    (Y := fun n ↦ (Scheme.Modules.pullback f).obj (A.obj.X n)) (e := fun n ↦ Iso.refl _)
    (componentMul A) (pullbackMul f A) (pullbackMul_eq f A) (X' := component B)
    (Y' := fun n ↦ (Scheme.Modules.pullback f).obj (B.obj.X n)) (e' := fun n ↦ Iso.refl _)
    (componentMul B) (pullbackMul f B) (pullbackMul_eq f B) (componentHom φ)
    (fun n ↦ (Scheme.Modules.pullback f).map (φ.hom.hom.hom n)) (fun n ↦ ?_)
    (componentHom_mul φ) i j
  -- Pullback of quasicoherent sheaves to modules acts on morphisms by module pullback.
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- Pullback of graded quasicoherent algebras along a morphism of schemes `f : X ⟶ Y`. A graded
quasicoherent algebra `A` on `Y` is sent to the graded algebra with homogeneous components
`f^* Aₙ`, whose unit is `𝒪_X ≅ f^* 𝒪_Y ⟶ f^* A₀` and whose homogeneous multiplications are
`f^* Aᵢ ⊗ f^* Aⱼ ≅ f^* (Aᵢ ⊗ Aⱼ) ⟶ f^* Aᵢ₊ⱼ`; a graded algebra morphism is pulled back degree by
degree. -/
def pullback : GradedQuasicoherentAlgebra Y ⥤ GradedQuasicoherentAlgebra X where
  obj := pullbackObj f
  map {A B} φ := homMkOfEq (pullbackObj_X f A) (pullbackObj_X f B) (pullbackObj_one f A)
    (pullbackObj_one f B) (pullbackObj_mul f A) (pullbackObj_mul f B)
    (fun n ↦ (Scheme.Modules.pullback f).map (φ.hom.hom.hom n)) (pullbackOne_map f φ)
    (pullbackMul_map f φ)
  map_id A := homMkOfEq_id _ _ _ _ _ _ fun n ↦ (Scheme.Modules.pullback f).map_id (A.obj.X n)
  map_comp _ _ := homMkOfEq_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fun _ ↦
    ((Scheme.Modules.pullback f).map_comp _ _).symm

variable (A)

/-- The homogeneous components of the pullback `f^* A` are the pullbacks `f^* Aₙ` of those of
`A`. -/
@[simp]
theorem pullback_obj_obj_X :
    ((pullback f).obj A).obj.X = fun n ↦ (Scheme.Modules.pullback f).obj (A.obj.X n) :=
  pullbackObj_X f A

/-- The unit of the pullback `f^* A` is the pullback of the unit of `A`, preceded by the
identification `𝒪_X ≅ f^* 𝒪_Y`. -/
@[simp]
theorem pullback_obj_one :
    ((pullback f).obj A).obj.toMon.one =
      (Scheme.Modules.pullbackObjUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map A.obj.toMon.one ≫
          eqToHom (congrFun (pullback_obj_obj_X f A) 0).symm := by
  refine (pullbackObj_one f A).trans ?_
  have hε : Functor.LaxMonoidal.ε (pullbackToModules f) =
      (Scheme.Modules.pullbackObjUnitIso f).inv :=
    (Iso.comp_hom_eq_id _).1 (by
      rw [← Scheme.Modules.pullbackToModules_η]
      exact Functor.Monoidal.ε_η _)
  rw [pullbackOne, hε, Category.assoc]
  -- Pullback of quasicoherent sheaves to modules acts on morphisms by module pullback.
  rfl

/-- The homogeneous multiplication `f^* Aᵢ ⊗ f^* Aⱼ ⟶ f^* Aᵢ₊ⱼ` of the pullback `f^* A` is the
pullback of that of `A`, preceded by the inverse of the tensor comparison
`f^* (Aᵢ ⊗ Aⱼ) ≅ f^* Aᵢ ⊗ f^* Aⱼ`. -/
@[simp]
theorem pullback_obj_mul (i j : ℕ) :
    ((pullback f).obj A).obj.toMon.mul i j =
      eqToHom (by rw [CommMon.toMon_X, pullback_obj_obj_X]) ≫
        inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) (A.obj.X i) (A.obj.X j)) ≫
          (Scheme.Modules.pullback f).map (A.obj.toMon.mul i j) ≫
            eqToHom (congrFun (pullback_obj_obj_X f A) (i + j)).symm := by
  refine (pullbackObj_mul f A i j).trans ?_
  have hμ : Functor.LaxMonoidal.μ (pullbackToModules f) (component A i) (component A j) =
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) (A.obj.X i) (A.obj.X j)) :=
    IsIso.eq_inv_of_inv_hom_id (by
      have h := Functor.Monoidal.μ_δ (pullbackToModules f) (component A i) (component A j)
      rw [Scheme.Modules.pullbackToModules_δ] at h
      exact h)
  rw [pullbackMul, hμ, Category.assoc]
  -- Pullback of quasicoherent sheaves to modules acts on morphisms by module pullback.
  rfl

variable {A} in
/-- The pullback of a graded algebra morphism is its degreewise pullback. -/
@[simp]
theorem pullback_map_hom_hom_hom (φ : A ⟶ B) (n : ℕ) :
    ((pullback f).map φ).hom.hom.hom n =
      eqToHom (congrFun (pullback_obj_obj_X f A) n) ≫
        (Scheme.Modules.pullback f).map (φ.hom.hom.hom n) ≫
          eqToHom (congrFun (pullback_obj_obj_X f B) n).symm :=
  homMkOfEq_hom_hom_hom ..

section IdComp

variable {Z : Scheme.{u}}

/-- An isomorphism of graded quasicoherent algebras from componentwise isomorphisms between
families identified with the homogeneous components, preserving units and multiplications. -/
private def isoMkOfEq {P Q : GradedQuasicoherentAlgebra X} {M N : ℕ → X.Modules}
    (hP : P.obj.X = M) (hQ : Q.obj.X = N) {oneM : 𝟙_ X.Modules ⟶ M 0}
    {oneN : 𝟙_ X.Modules ⟶ N 0} {mulM : ∀ i j, M i ⊗ M j ⟶ M (i + j)}
    {mulN : ∀ i j, N i ⊗ N j ⟶ N (i + j)}
    (hoP : P.obj.toMon.one = oneM ≫ eqToHom (congrFun hP 0).symm)
    (hoQ : Q.obj.toMon.one = oneN ≫ eqToHom (congrFun hQ 0).symm)
    (hmP : ∀ i j, P.obj.toMon.mul i j =
      (eqToHom (by rw [hP]) : P.obj.X i ⊗ P.obj.X j ⟶ M i ⊗ M j) ≫ mulM i j ≫
        eqToHom (congrFun hP (i + j)).symm)
    (hmQ : ∀ i j, Q.obj.toMon.mul i j =
      (eqToHom (by rw [hQ]) : Q.obj.X i ⊗ Q.obj.X j ⟶ N i ⊗ N j) ≫ mulN i j ≫
        eqToHom (congrFun hQ (i + j)).symm)
    (e : ∀ n, M n ≅ N n) (one_e : oneM ≫ (e 0).hom = oneN)
    (mul_e : ∀ i j, ((e i).hom ⊗ₘ (e j).hom) ≫ mulN i j = mulM i j ≫ (e (i + j)).hom) :
    P ≅ Q where
  hom := homMkOfEq hP hQ hoP hoQ hmP hmQ (fun n ↦ (e n).hom) one_e mul_e
  inv := homMkOfEq hQ hP hoQ hoP hmQ hmP (fun n ↦ (e n).inv)
    (by rw [← one_e, Category.assoc, Iso.hom_inv_id, Category.comp_id])
    (fun i j ↦ by
      rw [Iso.eq_comp_inv, Category.assoc, ← mul_e, ← tensorIso_hom, ← tensorIso_inv,
        Iso.inv_hom_id_assoc])
  hom_inv_id := (homMkOfEq_comp hP hQ hP hoP hoQ hoP hmP hmQ hmP _ one_e mul_e _ _ _
    (fun n ↦ 𝟙 (M n)) (Category.comp_id _) (fun i j ↦ by simp)
      fun n ↦ (e n).hom_inv_id).symm.trans (homMkOfEq_id hP hoP hmP _ _ _ fun _ ↦ rfl)
  inv_hom_id := (homMkOfEq_comp hQ hP hQ hoQ hoP hoQ hmQ hmP hmQ _ _ _ _ one_e mul_e
    (fun n ↦ 𝟙 (N n)) (Category.comp_id _) (fun i j ↦ by simp)
      fun n ↦ (e n).inv_hom_id).symm.trans (homMkOfEq_id hQ hoQ hmQ _ _ _ fun _ ↦ rfl)

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
          eqToHom (congrFun (pullback_obj_obj_X f A) 0).symm := by
  rw [pullback_obj_one, Category.assoc]

/-- `pullback_obj_mul`, bracketed as required by `isoMkOfEq`. -/
private lemma pullback_obj_mul_eq (i j : ℕ) :
    ((pullback f).obj A).obj.toMon.mul i j =
      eqToHom (by rw [CommMon.toMon_X, pullback_obj_obj_X]) ≫
        (inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) (A.obj.X i) (A.obj.X j)) ≫
          (Scheme.Modules.pullback f).map (A.obj.toMon.mul i j)) ≫
            eqToHom (congrFun (pullback_obj_obj_X f A) (i + j)).symm := by
  rw [pullback_obj_mul, Category.assoc]

/-- The component at `P` of `pullbackId`, given degreewise by `Scheme.Modules.pullbackId`. -/
private def pullbackIdApp (P : GradedQuasicoherentAlgebra X) : (pullback (𝟙 X)).obj P ≅ P :=
  isoMkOfEq (pullback_obj_obj_X (𝟙 X) P) rfl (pullback_obj_one_eq (𝟙 X) P)
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
      eqToHom (congrFun (pullback_obj_obj_X (𝟙 X) P) n) ≫
        (Scheme.Modules.pullbackId X).hom.app (P.obj.X n) :=
  -- The transport on the target is along `rfl`.
  (homMkOfEq_hom_hom_hom ..).trans (congrArg _ (Category.comp_id _))

private lemma pullbackIdApp_inv_hom_hom (P : GradedQuasicoherentAlgebra X) (n : ℕ) :
    (pullbackIdApp P).inv.hom.hom.hom n =
      (Scheme.Modules.pullbackId X).inv.app (P.obj.X n) ≫
        eqToHom (congrFun (pullback_obj_obj_X (𝟙 X) P) n).symm :=
  -- The transport on the source is along `rfl`.
  (homMkOfEq_hom_hom_hom ..).trans (Category.id_comp _)

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
      eqToHom (congrFun (pullback_obj_obj_X (𝟙 X) P) n) ≫
        (Scheme.Modules.pullbackId X).hom.app (P.obj.X n) :=
  pullbackIdApp_hom_hom_hom P n

/-- The inverse identity comparison of graded algebra pullback is Mathlib's inverse identity
comparison of module pullback in each degree. -/
@[simp]
theorem pullbackId_inv_app_hom_hom_hom (P : GradedQuasicoherentAlgebra X) (n : ℕ) :
    ((pullbackId X).inv.app P).hom.hom.hom n =
      (Scheme.Modules.pullbackId X).inv.app (P.obj.X n) ≫
        eqToHom (congrFun (pullback_obj_obj_X (𝟙 X) P) n).symm :=
  pullbackIdApp_inv_hom_hom P n

/-- The component at `P` of `pullbackComp`, given degreewise by `Scheme.Modules.pullbackComp`. -/
private def pullbackCompApp (g : Y ⟶ Z) (P : GradedQuasicoherentAlgebra Z) :
    (pullback f).obj ((pullback g).obj P) ≅ (pullback (f ≫ g)).obj P :=
  isoMkOfEq
    ((pullback_obj_obj_X f _).trans
      (funext fun n ↦ congrArg _ (congrFun (pullback_obj_obj_X g P) n)))
    (pullback_obj_obj_X (f ≫ g) P)
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
    (mulM := fun i j ↦ inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) _ _) ≫
      (Scheme.Modules.pullback f).map
        (inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g) (P.obj.X i) (P.obj.X j))) ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map (P.obj.toMon.mul i j)))
    (fun i j ↦ by
      simp only [pullback_obj_mul]
      dsimp only [CommMon.toMon]
      simp only [Functor.map_comp, Category.assoc]
      rw [eqToHom_map]
      -- The remaining transport is typed through `CommMon.toMon`, so it is matched up to
      -- unfolding.
      erw [inv_δ_comp_map_eqToHom_assoc _ (congrFun (pullback_obj_obj_X g P) i)
        (congrFun (pullback_obj_obj_X g P) j), eqToHom_trans_assoc]
      rw [eqToHom_trans])
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

private lemma pullbackCompApp_hom_hom_hom (g : Y ⟶ Z) (P : GradedQuasicoherentAlgebra Z)
    (n : ℕ) :
    (pullbackCompApp f g P).hom.hom.hom.hom n =
      eqToHom ((congrFun (pullback_obj_obj_X f _) n).trans
        (congrArg _ (congrFun (pullback_obj_obj_X g P) n))) ≫
        (Scheme.Modules.pullbackComp f g).hom.app (P.obj.X n) ≫
          eqToHom (congrFun (pullback_obj_obj_X (f ≫ g) P) n).symm :=
  homMkOfEq_hom_hom_hom ..

private lemma pullbackCompApp_inv_hom_hom (g : Y ⟶ Z) (P : GradedQuasicoherentAlgebra Z)
    (n : ℕ) :
    (pullbackCompApp f g P).inv.hom.hom.hom n =
      eqToHom (congrFun (pullback_obj_obj_X (f ≫ g) P) n) ≫
        (Scheme.Modules.pullbackComp f g).inv.app (P.obj.X n) ≫
          eqToHom ((congrFun (pullback_obj_obj_X f _) n).trans
            (congrArg _ (congrFun (pullback_obj_obj_X g P) n))).symm :=
  homMkOfEq_hom_hom_hom ..

/-- Pullback of graded quasicoherent algebras respects composition. -/
def pullbackComp (g : Y ⟶ Z) : pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
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
theorem pullbackComp_hom_app_hom_hom_hom (g : Y ⟶ Z) (P : GradedQuasicoherentAlgebra Z)
    (n : ℕ) :
    ((pullbackComp f g).hom.app P).hom.hom.hom n =
      eqToHom ((congrFun (pullback_obj_obj_X f _) n).trans
        (congrArg _ (congrFun (pullback_obj_obj_X g P) n))) ≫
        (Scheme.Modules.pullbackComp f g).hom.app (P.obj.X n) ≫
          eqToHom (congrFun (pullback_obj_obj_X (f ≫ g) P) n).symm :=
  pullbackCompApp_hom_hom_hom f g P n

/-- The inverse composition comparison of graded algebra pullback is Mathlib's inverse
composition comparison of module pullback in each degree. -/
@[simp]
theorem pullbackComp_inv_app_hom_hom_hom (g : Y ⟶ Z) (P : GradedQuasicoherentAlgebra Z)
    (n : ℕ) :
    ((pullbackComp f g).inv.app P).hom.hom.hom n =
      eqToHom (congrFun (pullback_obj_obj_X (f ≫ g) P) n) ≫
        (Scheme.Modules.pullbackComp f g).inv.app (P.obj.X n) ≫
          eqToHom ((congrFun (pullback_obj_obj_X f _) n).trans
            (congrArg _ (congrFun (pullback_obj_obj_X g P) n))).symm :=
  pullbackCompApp_inv_hom_hom f g P n

end IdComp

/-- The underlying module of the degree-`n` component of `f^* A` is the pullback of the
degree-`n` component of `A`. -/
theorem degree_obj_pullback_obj_obj (n : ℕ) :
    ((degree n).obj ((pullback f).obj A)).obj =
      ((QuasicoherentSheaf.pullback f).obj ((degree n).obj A)).obj := by
  rw [degree_obj_obj, QuasicoherentSheaf.pullback_obj_obj, degree_obj_obj, pullback_obj_obj_X]

/-- The pullback of the degree-`n` component of `A` is the degree-`n` component of the pullback
`f^* A`, naturally in `A`. -/
def pullbackDegreeIso (n : ℕ) :
    degree n ⋙ QuasicoherentSheaf.pullback f ≅ pullback f ⋙ degree n :=
  Iso.symm <|
  NatIso.ofComponents (fun A ↦ ObjectProperty.isoMk _ (eqToIso (degree_obj_pullback_obj_obj f A n)))
    fun φ ↦ by
    apply ObjectProperty.hom_ext
    simp only [Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom, degree_map_hom,
      QuasicoherentSheaf.pullback_map_hom, pullback_map_hom_hom_hom, ObjectProperty.isoMk_hom,
      eqToIso.hom, ObjectProperty.homMk_hom]
    -- Cancel the transports for abstract modules: the components of graded algebras defeat `simp`.
    have key {a b a' b' : Y.Modules} {P P' Q Q' R R' : X.Modules} (φn : a' ⟶ b')
        (h₁ : P = R) (h₂ : R = (Scheme.Modules.pullback f).obj a')
        (h₃ : (Scheme.Modules.pullback f).obj b' = R') (h₄ : R' = Q) (h₅ : Q = Q')
        (h₆ : P = P') (h₇ : P' = (Scheme.Modules.pullback f).obj a)
        (h₈ : (Scheme.Modules.pullback f).obj b = Q') (h₉ : a = a') (h₁₀ : b' = b) :
        (eqToHom h₁ ≫ (eqToHom h₂ ≫ (Scheme.Modules.pullback f).map φn ≫ eqToHom h₃) ≫
            eqToHom h₄) ≫ eqToHom h₅ =
          eqToHom h₆ ≫ eqToHom h₇ ≫
            (Scheme.Modules.pullback f).map (eqToHom h₉ ≫ φn ≫ eqToHom h₁₀) ≫ eqToHom h₈ := by
      subst h₁ h₂ h₃ h₄ h₆ h₉ h₁₀
      simp
    exact key _ _ _ _ _ _ _ _ _ _ _

/-- The comparison `pullbackDegreeIso` is the identification of the underlying modules. -/
@[simp]
theorem pullbackDegreeIso_hom_app_hom (n : ℕ) :
    ((pullbackDegreeIso f n).hom.app A).hom = eqToHom (degree_obj_pullback_obj_obj f A n).symm :=
  (rfl)

/-- The inverse of `pullbackDegreeIso` is the identification of the underlying modules. -/
@[simp]
theorem pullbackDegreeIso_inv_app_hom (n : ℕ) :
    ((pullbackDegreeIso f n).inv.app A).hom = eqToHom (degree_obj_pullback_obj_obj f A n) :=
  (rfl)

section DirectSum

/-- The pullback along `f` of the inclusion of the summand `Aₙ` of `⨁ₙ Aₙ`. -/
private abbrev pullbackιTotal (n : ℕ) :
    ((pullback f).obj A).obj.X n ⟶
      (Scheme.Modules.pullback f).obj (toQuasicoherentAlgebra.obj A).obj.X :=
  eqToHom (congrFun (pullback_obj_obj_X f A) n) ≫ (Scheme.Modules.pullback f).map (ιTotal A n)

/-- Pullback preserves the direct sum `⨁ₙ Aₙ`: the pullbacks of its summand inclusions exhibit
`f^* (⨁ₙ Aₙ)` as a direct sum of the `f^* Aₙ`. -/
private def isColimitPullbackMapιTotal :
    IsColimit (Cofan.mk _ fun n ↦ (Scheme.Modules.pullback f).map (ιTotal A n) :
      Cofan fun n ↦ (Scheme.Modules.pullback f).obj (A.obj.X n)) :=
  isColimitCofanMkObjOfIsColimit (Scheme.Modules.pullback f) _ _ (isColimitιTotal A)

/-- The comparison `⨁ₙ f^* Aₙ ⟶ f^* (⨁ₙ Aₙ)` of modules, given on the summand `f^* Aₙ` by the
pullback of the inclusion of `Aₙ`. -/
private def directSumPullbackHom :
    (toQuasicoherentAlgebra.obj ((pullback f).obj A)).obj.X ⟶
      (Scheme.Modules.pullback f).obj (toQuasicoherentAlgebra.obj A).obj.X :=
  Cofan.IsColimit.desc (isColimitιTotal ((pullback f).obj A)) (pullbackιTotal f A)

private lemma ιTotal_directSumPullbackHom (n : ℕ) :
    ιTotal ((pullback f).obj A) n ≫ directSumPullbackHom f A = pullbackιTotal f A n :=
  Cofan.IsColimit.fac (isColimitιTotal ((pullback f).obj A)) (pullbackιTotal f A) n

/-- The inverse comparison `f^* (⨁ₙ Aₙ) ⟶ ⨁ₙ f^* Aₙ`. -/
private def directSumPullbackInv :
    (Scheme.Modules.pullback f).obj (toQuasicoherentAlgebra.obj A).obj.X ⟶
      (toQuasicoherentAlgebra.obj ((pullback f).obj A)).obj.X :=
  Cofan.IsColimit.desc (isColimitPullbackMapιTotal f A)
    fun n ↦ eqToHom (congrFun (pullback_obj_obj_X f A) n).symm ≫ ιTotal ((pullback f).obj A) n

private lemma pullback_map_ιTotal_directSumPullbackInv (n : ℕ) :
    (Scheme.Modules.pullback f).map (ιTotal A n) ≫ directSumPullbackInv f A =
      eqToHom (congrFun (pullback_obj_obj_X f A) n).symm ≫ ιTotal ((pullback f).obj A) n :=
  Cofan.IsColimit.fac (isColimitPullbackMapιTotal f A) _ n

/-- The comparison of modules `⨁ₙ f^* Aₙ ≅ f^* (⨁ₙ Aₙ)`. -/
private def directSumPullbackIso :
    (toQuasicoherentAlgebra.obj ((pullback f).obj A)).obj.X ≅
      (Scheme.Modules.pullback f).obj (toQuasicoherentAlgebra.obj A).obj.X where
  hom := directSumPullbackHom f A
  inv := directSumPullbackInv f A
  hom_inv_id := toQuasicoherentAlgebra_hom_ext fun n ↦ by
    rw [reassoc_of% ιTotal_directSumPullbackHom, Category.comp_id,
      pullback_map_ιTotal_directSumPullbackInv, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
  inv_hom_id := Cofan.IsColimit.hom_ext (isColimitPullbackMapιTotal f A) _ _ fun n ↦ by
    rw [cofan_mk_inj, reassoc_of% pullback_map_ιTotal_directSumPullbackInv,
      ιTotal_directSumPullbackHom, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact (Category.comp_id _).symm

private lemma one_directSumPullbackHom :
    η[(toQuasicoherentAlgebra.obj ((pullback f).obj A)).obj.X] ≫ directSumPullbackHom f A =
      (Scheme.Modules.pullbackObjUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map η[(toQuasicoherentAlgebra.obj A).obj.X] := by
  -- The carriers of quasicoherent algebras defeat `rw` and `simp` here, so the composites are
  -- reassociated by explicit equations and the transports cancelled for abstract modules.
  have key {P T Q Q' S : X.Modules} (u : P ⟶ T) (m : T ⟶ Q') (h : Q' = Q) (h' : Q = Q')
      (n : Q' ⟶ S) : (u ≫ m ≫ eqToHom h) ≫ (eqToHom h' ≫ n) = u ≫ m ≫ n := by
    simp
  rw [← one_ιTotal, ← one_ιTotal]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg _ (ιTotal_directSumPullbackHom f A 0)).trans ?_
  refine (congrArg (· ≫ _) (pullback_obj_one f A)).trans ?_
  refine (key _ _ _ _ _).trans ?_
  exact congrArg _ ((Scheme.Modules.pullback f).map_comp _ _).symm

private lemma mul_directSumPullbackHom :
    μ[(toQuasicoherentAlgebra.obj ((pullback f).obj A)).obj.X] ≫ directSumPullbackHom f A =
      (directSumPullbackHom f A ⊗ₘ directSumPullbackHom f A) ≫
        inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f)
          (toQuasicoherentAlgebra.obj A).obj.X (toQuasicoherentAlgebra.obj A).obj.X) ≫
          (Scheme.Modules.pullback f).map μ[(toQuasicoherentAlgebra.obj A).obj.X] := by
  refine toQuasicoherentAlgebra_tensor_hom_ext fun i j ↦ ?_
  -- `Mon.mul_eq`, restated on the carrier `B.obj.X`: it is stated on `B.obj.toMon.X`, which
  -- `rw` does not identify with `B.obj.X` because `CommMon.toMon` is not reducible.
  have hmul (B : GradedQuasicoherentAlgebra X) :
      GradedObject.Monoidal.ιTensorObj B.obj.X B.obj.X i j (i + j) rfl ≫ μ[B.obj.X] (i + j) =
        B.obj.toMon.mul i j :=
    (Mon.mul_eq B.obj.toMon i j).symm
  -- The pullback of `(ιᵢ ⊗ ιⱼ) ≫ μ = mul ≫ ιᵢ₊ⱼ` through the inverse tensor comparisons, stated
  -- for abstract modules: the carriers of quasicoherent algebras defeat `rw` and `simp`.
  have key {Ai Aj Ak M : Y.Modules} [Ai.IsQuasicoherent] [M.IsQuasicoherent]
      {Pi Pj Pk : X.Modules} (hi : Pi = (Scheme.Modules.pullback f).obj Ai)
      (hj : Pj = (Scheme.Modules.pullback f).obj Aj)
      (hk : (Scheme.Modules.pullback f).obj Ak = Pk)
      (hk' : Pk = (Scheme.Modules.pullback f).obj Ak)
      (hij : Pi ⊗ Pj = (Scheme.Modules.pullback f).obj Ai ⊗ (Scheme.Modules.pullback f).obj Aj)
      (ιi : Ai ⟶ M) (ιj : Aj ⟶ M) (ιk : Ak ⟶ M) (m : Ai ⊗ Aj ⟶ Ak) (n : M ⊗ M ⟶ M)
      (h : (ιi ⊗ₘ ιj) ≫ n = m ≫ ιk) :
      (eqToHom hij ≫ inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) Ai Aj) ≫
          (Scheme.Modules.pullback f).map m ≫ eqToHom hk) ≫
          eqToHom hk' ≫ (Scheme.Modules.pullback f).map ιk =
        ((eqToHom hi ≫ (Scheme.Modules.pullback f).map ιi) ⊗ₘ
          (eqToHom hj ≫ (Scheme.Modules.pullback f).map ιj)) ≫
          inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) M M) ≫
            (Scheme.Modules.pullback f).map n := by
    subst hi hj hk
    simp only [eqToHom_refl, Category.id_comp, Category.assoc]
    rw [← Functor.map_comp, ← h, Functor.map_comp, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [IsIso.inv_comp_eq, Functor.OplaxMonoidal.δ_natural_assoc, IsIso.hom_inv_id,
      Category.comp_id]
  rw [ιTotal_tensorHom_ιTotal_mul_assoc, tensorHom_comp_tensorHom_assoc,
    ιTotal_directSumPullbackHom, ιTotal_directSumPullbackHom f A i,
    ιTotal_directSumPullbackHom f A j, reassoc_of% hmul, pullback_obj_mul]
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
        ((congrArg (· ≫ _) (one_directSumPullbackHom f A)).trans (Category.assoc _ _ _)))
    (by
      rw [QuasicoherentAlgebra.pullback_obj_mul]
      -- As in `mul_directSumPullbackHom`, cancel the carrier transports for abstract modules.
      have key {S P T Q : X.Modules} (g : S ⟶ P) (h : P = T) (h' : T = P) (r : P ⊗ P ⟶ Q) :
          ((g ≫ eqToHom h) ⊗ₘ (g ≫ eqToHom h)) ≫ (eqToHom h' ⊗ₘ eqToHom h') ≫ r =
            (g ⊗ₘ g) ≫ r := by
        subst h
        simp
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
        (mul_directSumPullbackHom f A)).trans ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans
            (key _ (QuasicoherentAlgebra.pullback_obj_X f _).symm _ _).symm)))))

private lemma ιTotal_toQuasicoherentAlgebraPullbackIsoApp_hom (n : ℕ) :
    ιTotal ((pullback f).obj A) n ≫ (toQuasicoherentAlgebraPullbackIsoApp f A).hom.hom.hom.hom =
      eqToHom (congrFun (pullback_obj_obj_X f A) n) ≫
        (Scheme.Modules.pullback f).map (ιTotal A n) ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X f _).symm :=
  (reassoc_of% ιTotal_directSumPullbackHom f A n) _

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
    -- Cancel the carrier transports for abstract modules, as in `mul_directSumPullbackHom`.
    have key {a b MA MB : Y.Modules} {Sa Sb TA TB : X.Modules} (φn : a ⟶ b) (ιA : a ⟶ MA)
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
      eqToHom (congrFun (pullback_obj_obj_X f A) n) ≫
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
      eqToHom (congrFun (pullback_obj_obj_X f A) n).symm ≫ ιTotal ((pullback f).obj A) n := by
  have h : ((pullbackToQuasicoherentAlgebraIso f).hom.app A).hom.hom.hom =
      eqToHom (QuasicoherentAlgebra.pullback_obj_X f _) ≫ directSumPullbackInv f A :=
    -- The inverse of the component built from `directSumPullbackIso` and a transport.
    (rfl)
  rw [h]
  -- The carrier of the pulled-back algebra defeats `rw` here; cancel the transports directly.
  exact (congrArg (_ ≫ ·) ((eqToHom_trans_assoc _ _ _).trans
    ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _)))).trans
      (pullback_map_ιTotal_directSumPullbackInv f A n)

end DirectSum

end GradedQuasicoherentAlgebra

end

end TauCeti.AlgebraicGeometry
