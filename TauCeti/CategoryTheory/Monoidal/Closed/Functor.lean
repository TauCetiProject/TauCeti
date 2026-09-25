/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import TauCeti.CategoryTheory.Monoidal.Functor

/-!
# Internal Hom comparison for monoidal functors

A lax monoidal functor `F : C ⥤ D` has a canonical comparison morphism whenever
`A` and `F.obj A` are closed:

`F.obj (A ⟶[C] B) ⟶ (F.obj A ⟶[D] F.obj B)`.

It is the mate, under the two tensor--Hom adjunctions, of the tensorator
`F.obj A ⊗ F.obj B ⟶ F.obj (A ⊗ B)`. This file packages the comparison as a natural
transformation in `B`, characterizes it by evaluation and coevaluation, and proves its
contravariant naturality in `A`. These formulas allow closed-structure comparisons to be used
without unfolding the mates construction.

The construction generalizes Mathlib's Cartesian-closed `CategoryTheory.expComparison`; its
definition and characteristic formulas follow the mate-based development in
`Mathlib.CategoryTheory.Monoidal.Closed.Functor`.

## Main declarations

* `CategoryTheory.Functor.ihomComparison`: the internal Hom comparison of a lax monoidal
  functor;
* `CategoryTheory.Functor.ihomComparison_ev`: its characteristic equation against evaluation;
* `CategoryTheory.Functor.ihomComparison_app_eq_curry`: its componentwise curry formula;
* `CategoryTheory.Functor.ihomComparison_isIso_of_tensor_comparison`: an explicit
  compatibility criterion which turns that formula into an isomorphism;
* `CategoryTheory.Functor.ihomComparison_unit_isIso`: invertibility at the tensor unit for a
  strong monoidal functor;
* `CategoryTheory.Functor.ihomComparison_isIso_of_iso`: transport of an invertible comparison
  along an isomorphism in its source object;
* `CategoryTheory.Functor.coev_ihomComparison`: its characteristic equation against
  coevaluation;
* `CategoryTheory.Functor.ihomComparison_whiskerLeft`: its naturality in the source of the
  internal Hom.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Functor MonoidalCategory MonoidalClosed

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable (F : C ⥤ D) [F.LaxMonoidal]

/-- The canonical comparison from the image of an internal Hom to the internal Hom of the
images under a lax monoidal functor. It is natural in the target of the internal Hom. -/
def ihomComparison (A : C) [Closed A] [Closed (F.obj A)] :
    TwoSquare (ihom A) F F (ihom (F.obj A)) :=
  mateEquiv (ihom.adjunction A) (ihom.adjunction (F.obj A))
    (laxCommTensorLeft F A)

/-- Evaluation after the internal Hom comparison is the image of evaluation, preceded by the
tensorator. This equation characterizes `ihomComparison`. -/
@[reassoc (attr := simp)]
theorem ihomComparison_ev (A B : C) [Closed A] [Closed (F.obj A)] :
    F.obj A ◁ (ihomComparison F A).natTrans.app B ≫
        (ihom.ev (F.obj A)).app (F.obj B) =
      Functor.LaxMonoidal.μ F A ((ihom A).obj B) ≫ F.map ((ihom.ev A).app B) := by
  -- The mate lemma uses the square component, tensorLeft.map, and adjunction counits.
  -- Rewrite the tensorator first; the remaining terms match definitionally.
  rw [← laxCommTensorLeft_app F A ((ihom A).obj B)]
  change (tensorLeft (F.obj A)).map ((ihomComparison F A).app B) ≫
      (ihom.adjunction (F.obj A)).counit.app (F.obj B) =
    (laxCommTensorLeft F A).app ((ihom A).obj B) ≫
      F.map ((ihom.adjunction A).counit.app B)
  exact mateEquiv_counit (ihom.adjunction A) (ihom.adjunction (F.obj A))
    (laxCommTensorLeft F A) B

/-- The image of coevaluation followed by the internal Hom comparison is coevaluation followed
by the internal Hom of the tensorator. -/
@[reassoc (attr := simp)]
theorem coev_ihomComparison (A B : C) [Closed A] [Closed (F.obj A)] :
    F.map ((ihom.coev A).app B) ≫
        (ihomComparison F A).natTrans.app (A ⊗ B) =
      (ihom.coev (F.obj A)).app (F.obj B) ≫
        (ihom (F.obj A)).map (Functor.LaxMonoidal.μ F A B) := by
  -- The mate lemma uses the square component, tensorLeft.obj, and adjunction units.
  -- Rewrite the tensorator first; the remaining terms match definitionally.
  rw [← laxCommTensorLeft_app F A B]
  change F.map ((ihom.adjunction A).unit.app B) ≫
      (ihomComparison F A).app ((tensorLeft A).obj B) =
    (ihom.adjunction (F.obj A)).unit.app (F.obj ((𝟭 C).obj B)) ≫
      (ihom (F.obj A)).map ((laxCommTensorLeft F A).app ((𝟭 C).obj B))
  exact unit_mateEquiv (ihom.adjunction A) (ihom.adjunction (F.obj A))
    (laxCommTensorLeft F A) B

/-- Uncurrying the internal Hom comparison gives the tensorator followed by the image of
evaluation. -/
@[simp]
theorem uncurry_ihomComparison (A B : C) [Closed A] [Closed (F.obj A)] :
    uncurry ((ihomComparison F A).natTrans.app B) =
      Functor.LaxMonoidal.μ F A ((ihom A).obj B) ≫ F.map ((ihom.ev A).app B) := by
  rw [uncurry_eq, ihomComparison_ev]

/-- Each component of the internal Hom comparison is the curry of the tensorator followed by
the image of evaluation. -/
theorem ihomComparison_app_eq_curry (A B : C) [Closed A] [Closed (F.obj A)] :
    (ihomComparison F A).natTrans.app B =
      curry (Functor.LaxMonoidal.μ F A ((ihom A).obj B) ≫
        F.map ((ihom.ev A).app B)) := by
  rw [← uncurry_ihomComparison F A B, curry_uncurry]

/-- The internal Hom comparison is contravariantly natural in the source of the internal Hom. -/
theorem ihomComparison_whiskerLeft {A A' : C} [Closed A] [Closed A']
    [Closed (F.obj A)] [Closed (F.obj A')] (f : A' ⟶ A) :
    (ihomComparison F A).whiskerBottom (pre (F.map f)) =
      (ihomComparison F A').whiskerTop (pre f) := by
  unfold ihomComparison pre
  have vcomp₁ := mateEquiv_conjugateEquiv_vcomp
    (ihom.adjunction A) (ihom.adjunction (F.obj A)) (ihom.adjunction (F.obj A'))
    (laxCommTensorLeft F A) ((curriedTensor D).map (F.map f))
  have vcomp₂ := conjugateEquiv_mateEquiv_vcomp
    (ihom.adjunction A) (ihom.adjunction A') (ihom.adjunction (F.obj A'))
    ((curriedTensor C).map f) (laxCommTensorLeft F A')
  rw [← vcomp₁, ← vcomp₂]
  unfold TwoSquare.whiskerLeft TwoSquare.whiskerRight
  congr 1
  apply congr_arg
  ext B
  simp only [Functor.comp_obj, curriedTensor_obj_obj, NatTrans.comp_app,
    Functor.whiskerLeft_app, curriedTensor_map_app, Functor.whiskerRight_app,
    laxCommTensorLeft_app]
  rw [Functor.LaxMonoidal.μ_natural_left]


section InternalHomComparison

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- If target comparisons to a common object `T` are compatible with the image of the
source tensor comparison, then the internal Hom comparison is an isomorphism.

The hypothesis is the evaluation equation for the transported target comparison.  It is
the precise compatibility needed when a functor transports a chosen duality structure; it
is not supplied by arbitrary closed objects alone.  The common target `T` is arbitrary; the
tensor object `F.obj A ⊗ F.obj B` is the natural choice when the target comparisons are
described through the tensorator. -/
theorem ihomComparison_isIso_of_tensor_comparison
    (F : C ⥤ D) [F.LaxMonoidal] (A B : C) [Closed A] [Closed (F.obj A)] {T : D}
    (t : (ihom (F.obj A)).obj (F.obj B) ≅ T)
    (g : F.obj ((ihom A).obj B) ≅ T)
    (hcompat :
      (MonoidalCategoryStruct.whiskerLeft (F.obj A) g.hom) ≫
          (MonoidalCategoryStruct.whiskerLeft (F.obj A) t.inv) ≫
            (ihom.ev (F.obj A)).app (F.obj B) =
        Functor.LaxMonoidal.μ F A ((ihom A).obj B) ≫
          F.map ((ihom.ev A).app B)) :
    IsIso ((ihomComparison F A).natTrans.app B) := by
  let γ : F.obj ((ihom A).obj B) ≅ (ihom (F.obj A)).obj (F.obj B) :=
    g.trans t.symm
  have hγ : IsIso γ.hom := by
    dsimp [γ]
    infer_instance
  let α : F.obj ((ihom A).obj B) ⟶ (ihom (F.obj A)).obj (F.obj B) := by
    simpa only [Functor.comp_obj] using (ihomComparison F A).natTrans.app B
  have hγeq : γ.hom = MonoidalClosed.curry
      (Functor.LaxMonoidal.μ F A ((ihom A).obj B) ≫
        F.map ((ihom.ev A).app B)) := by
    have h : MonoidalClosed.uncurry γ.hom =
        MonoidalClosed.uncurry (MonoidalClosed.curry
          (Functor.LaxMonoidal.μ F A ((ihom A).obj B) ≫
            F.map ((ihom.ev A).app B))) := by
      dsimp [γ]
      rw [MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_curry]
      rw [MonoidalCategory.whiskerLeft_comp]
      simpa only [Category.assoc, Functor.id_obj] using hcompat
    exact MonoidalClosed.uncurry_injective h
  have hαeq : α = MonoidalClosed.curry
      (Functor.LaxMonoidal.μ F A ((ihom A).obj B) ≫
        F.map ((ihom.ev A).app B)) := by
    dsimp [α]
    rw [ihomComparison_app_eq_curry]
  have hα : IsIso α := by
    rw [hαeq, ← hγeq]
    exact hγ
  simpa only [α, Functor.comp_obj] using hα

/-- The mate through the two identity adjunctions is the original two-square. -/
private theorem mateEquiv_adjunction_id {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    {G H : C ⥤ D} (α : TwoSquare G (𝟭 C) (𝟭 D) H) :
    mateEquiv (Adjunction.id : (𝟭 C) ⊣ (𝟭 C))
      (Adjunction.id : (𝟭 D) ⊣ (𝟭 D)) α = α := by
  ext X
  rw [mateEquiv_apply]
  simp only [comp_obj, id_obj, NatTrans.comp_app,
    Functor.id_obj, Functor.id_map, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    rightUnitor_inv_app, associator_hom_app, associator_inv_app, leftUnitor_hom_app,
    Adjunction.id_unit, Adjunction.id_counit, Category.comp_id, Category.id_comp,
    Functor.comp_map, Functor.map_id, NatTrans.id_app]

/-- A strong monoidal functor preserves the internal-Hom comparison at the tensor unit. -/
theorem ihomComparison_unit_isIso (F : C ⥤ D) [F.Monoidal]
    [Closed (𝟙_ C)] [Closed (F.obj (𝟙_ C))] :
    IsIso (F.ihomComparison (𝟙_ C)).natTrans := by
  -- Compare the two tensor--Hom adjunctions with identity adjunctions using the
  -- left-unitors.  The remaining tensorator is a strong monoidal natural isomorphism.
  let adjC :
      CategoryTheory.MonoidalCategory.tensorLeft (C := C) (𝟙_ C) ⊣ ihom (𝟙_ C) :=
    ihom.adjunction (𝟙_ C)
  let adjD :
      CategoryTheory.MonoidalCategory.tensorLeft (C := D) (F.obj (𝟙_ C)) ⊣
        CategoryTheory.ihom (C := D) (F.obj (𝟙_ C)) :=
    ihom.adjunction (F.obj (𝟙_ C))
  let adjIC : (𝟭 C) ⊣ (𝟭 C) := Adjunction.id
  let adjID : (𝟭 D) ⊣ (𝟭 D) := Adjunction.id
  let qC : (𝟭 C) ≅ CategoryTheory.MonoidalCategory.tensorLeft (C := C) (𝟙_ C) :=
    (MonoidalCategory.leftUnitorNatIso C).symm
  let eD : (𝟙_ D : D) ≅ F.obj (𝟙_ C) := Functor.Monoidal.εIso F
  let eTL :
      CategoryTheory.MonoidalCategory.tensorLeft (C := D) (𝟙_ D) ≅
        CategoryTheory.MonoidalCategory.tensorLeft (C := D) (F.obj (𝟙_ C)) :=
    Functor.mapIso (CategoryTheory.MonoidalCategory.tensoringLeft D) eD
  let qD : (𝟭 D) ≅
      CategoryTheory.MonoidalCategory.tensorLeft (C := D) (F.obj (𝟙_ C)) :=
    (MonoidalCategory.leftUnitorNatIso D).symm.trans eTL
  let S : CategoryTheory.TwoSquare F
      (CategoryTheory.MonoidalCategory.tensorLeft (C := C) (𝟙_ C))
      (CategoryTheory.MonoidalCategory.tensorLeft (C := D) (F.obj (𝟙_ C))) F :=
    laxCommTensorLeft F (𝟙_ C)
  let S0 := S.whiskerRight (R := 𝟭 D) qD.hom
  let S1 := S0.whiskerLeft (L' := 𝟭 C) qC.symm.hom
  let m0 := mateEquiv adjIC adjID S1
  let m1 := mateEquiv adjC adjID S0
  let m2 := mateEquiv adjC adjD S
  let cC := conjugateEquiv adjIC adjC qC.symm.hom
  let cD := conjugateEquiv adjD adjID qD.hom
  have hleft := conjugateEquiv_mateEquiv_vcomp adjIC adjC adjID qC.symm.hom S0
  have hright := mateEquiv_conjugateEquiv_vcomp adjC adjD adjID S qD.hom
  have hS1 : IsIso S1.natTrans := by
    -- The whiskered square is a composite of the unitors and the tensorator.
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    dsimp [S1, S0, TwoSquare.whiskerLeft, TwoSquare.whiskerRight]
    have hqDall : IsIso qD.hom := qD.isIso_hom
    have hqD : IsIso (qD.hom.app (F.obj X)) :=
      (NatTrans.isIso_iff_isIso_app qD.hom).1 hqDall (F.obj X)
    have hS : IsIso (S.natTrans.app X) := by
      -- `S` is a `TwoSquare`; expose its stored tensorator component explicitly.
      dsimp [S]
      rw [laxCommTensorLeft_app]
      exact (Functor.Monoidal.μIso F (𝟙_ C) X).isIso_hom
    have hcomp : IsIso (qD.hom.app (F.obj X) ≫
        (S.natTrans.app X ≫ F.map (qC.inv.app X))) := by
      apply (isIso_comp_left_iff (qD.hom.app (F.obj X))
        (g := S.natTrans.app X ≫ F.map (qC.inv.app X))).2
      apply (isIso_comp_right_iff (F.map (qC.inv.app X))
        (g := S.natTrans.app X)).2
      exact hS
    simpa only [Category.assoc] using hcomp
  have hm0 : IsIso m0.natTrans := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    dsimp [m0, adjIC, adjID]
    have hX : IsIso (S1.natTrans.app X) :=
      (NatTrans.isIso_iff_isIso_app S1.natTrans).1 hS1 X
    rw [mateEquiv_adjunction_id (C := C) (D := D) (G := F) (H := F) S1]
    exact hX
  have hcC : IsIso cC := by
    dsimp [cC]
    have hq : IsIso (qC.symm.hom) := qC.symm.isIso_hom
    exact @conjugateEquiv_iso _ _ _ _ _ _ _ _ adjIC adjC (qC.symm.hom) hq
  have hcD : IsIso cD := by
    dsimp [cD]
    have hq : IsIso (qD.hom) := qD.isIso_hom
    exact @conjugateEquiv_iso _ _ _ _ _ _ _ _ adjD adjID (qD.hom) hq
  have htrace1 : IsIso (m1.whiskerTop cC).natTrans := by
    -- Conjugate the first identity mate back across the source unitor.
    rw [← hleft]
    simpa only [m0, m1, cC, S1, mateEquiv_adjunction_id] using hm0
  have hm1 : IsIso m1.natTrans := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    have hX : IsIso ((m1.whiskerTop cC).natTrans.app X) :=
      (NatTrans.isIso_iff_isIso_app (m1.whiskerTop cC).natTrans).1 htrace1 X
    dsimp [TwoSquare.whiskerTop] at hX ⊢
    have hfc : IsIso (F.map (cC.app X)) := F.map_isIso _
    exact (isIso_comp_left_iff (F.map (cC.app X))
      (g := m1.natTrans.app X)).mp hX
  have htrace2 : IsIso (m2.whiskerBottom cD).natTrans := by
    -- Conjugate the target identity mate back across the target unitor and unit map.
    rw [← hright]
    simpa only [m1, m2, cD, S0] using hm1
  have hm2 : IsIso m2.natTrans := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    have hX : IsIso ((m2.whiskerBottom cD).natTrans.app X) :=
      (NatTrans.isIso_iff_isIso_app (m2.whiskerBottom cD).natTrans).1 htrace2 X
    dsimp [TwoSquare.whiskerBottom] at hX ⊢
    have hcd : IsIso (cD.app (F.obj X)) :=
      (NatTrans.isIso_iff_isIso_app cD).1 hcD (F.obj X)
    exact (isIso_comp_right_iff (cD.app (F.obj X))
      (g := m2.natTrans.app X)).mp hX
  -- `ihomComparison` is by definition this mate of the tensorator under the two
  -- tensor--Hom adjunctions, so `m2` is the unit comparison once the local aliases
  -- are unfolded; that single unfolding is the only step identifying the two.
  simpa only [m2, adjC, adjD, S, ihomComparison] using hm2

/-- Transport invertibility of an internal-Hom comparison along an isomorphism in its source
object. -/
theorem ihomComparison_isIso_of_iso
    (F : C ⥤ D) [F.LaxMonoidal]
    {A A' : C} [Closed A] [Closed A'] [Closed (F.obj A)] [Closed (F.obj A')]
    (hA' : IsIso (F.ihomComparison A').natTrans)
    (e : A ≅ A') :
    IsIso (F.ihomComparison A).natTrans := by
  have hpre : IsIso (MonoidalClosed.pre e.hom) := by
    have hα : IsIso ((tensoringLeft C).map e.hom) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro Z
      exact MonoidalCategory.whiskerRight_isIso e.hom Z
    unfold MonoidalClosed.pre
    exact @conjugateEquiv_iso _ _ _ _ _ _ _ _ (ihom.adjunction _) (ihom.adjunction _)
      ((tensoringLeft C).map e.hom) hα
  have hpreF : IsIso (MonoidalClosed.pre (F.map e.hom)) := by
    have hα : IsIso ((tensoringLeft D).map (F.map e.hom)) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro Z
      exact MonoidalCategory.whiskerRight_isIso (F.map e.hom) Z
    unfold MonoidalClosed.pre
    exact @conjugateEquiv_iso _ _ _ _ _ _ _ _ (ihom.adjunction _) (ihom.adjunction _)
      ((tensoringLeft D).map (F.map e.hom)) hα
  -- Naturality in the source transports invertibility from `A'` to `A` across `e`.
  have hnat := ihomComparison_whiskerLeft (F := F) (A := A') (A' := A) e.hom
  have hL : IsIso ((F.ihomComparison A').whiskerBottom
      (MonoidalClosed.pre (F.map e.hom))).natTrans := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    have hp : IsIso ((MonoidalClosed.pre (F.map e.hom)).app (F.obj X)) :=
      (NatTrans.isIso_iff_isIso_app (MonoidalClosed.pre (F.map e.hom))).1 hpreF (F.obj X)
    dsimp [TwoSquare.whiskerBottom]
    exact (CategoryTheory.isIso_comp_left_iff _ _).mpr hp
  have hR : IsIso ((F.ihomComparison A).whiskerTop
      (MonoidalClosed.pre e.hom)).natTrans := by
    rw [← hnat]
    exact hL
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  have hcomp :=
    ((NatTrans.isIso_iff_isIso_app
      ((F.ihomComparison A).whiskerTop
        (MonoidalClosed.pre e.hom)).natTrans).1 hR) X
  simp only [TwoSquare.whiskerTop, Functor.whiskerRight] at hcomp
  -- The remaining whiskered comparison is invertible because its precomposition is.
  exact (CategoryTheory.isIso_comp_left_iff
    (F.map ((MonoidalClosed.pre e.hom).app X))
    ((F.ihomComparison A).natTrans.app X)).mp hcomp

end InternalHomComparison


end CategoryTheory.Functor
