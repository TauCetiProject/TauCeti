/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Colimit
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Coefficients

/-!
# Vanishing of Čech cohomology over a system of families by refinement

Let `E : J → FormalCoproduct C` be a system of families of objects of `C`, as in
`TauCeti.CategoryTheory.cechCohomology`, and let `P` be a presheaf on `C` with values in a category
`D` which has a faithful functor to abelian groups preserving zero morphisms, such as modules
(through `forget₂`) or abelian groups themselves (through the identity). The Čech cohomology of
`P` for the system is a colimit of the Čech cohomologies of the families, so it vanishes as soon as
every class of every family of the system is killed by passing to a finer family.

Forgetting the module structure commutes with forming Čech complexes, their cohomology, and
colimits, so vanishing Čech cohomology of a presheaf of modules implies vanishing Čech cohomology
of its underlying presheaf of abelian groups for any system of families.
This is how vanishing results proved for sheaves of modules, such as the vanishing of `H¹` of the
holomorphic structure sheaf on discs, reach sheaf cohomology, which is defined for sheaves of
abelian groups.

## Main results

* `TauCeti.CategoryTheory.isZero_cechCohomology_obj_of_forall_exists_homologyMap_eq_zero`: the
  Čech cohomology vanishes if every cohomology class of every family of the system is killed by
  passing to some finer member of the system.
* `TauCeti.CategoryTheory.isZero_cechCohomology_obj_comp_forget₂`: if the
  Čech cohomology of a presheaf of modules vanishes, so does that of its underlying presheaf of
  abelian groups.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w t v v' u u' w'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {J : Type t} [Preorder J] (E : J → FormalCoproduct.{w} C)
  (hE : ∀ ⦃i j : J⦄, i ≤ j → Nonempty (E j ⟶ E i)) (n : ℕ)

/-- **Vanishing by refinement.** Let `G` be a faithful functor from the coefficient category `D` to
abelian groups which preserves zero morphisms. The Čech cohomology for the system of a presheaf `P`
with values in `D` vanishes if every class in the degree `n` Čech cohomology of every family
`E j`, seen as an element through `G`, is sent to zero by the map induced by some morphism of
families `E k ⟶ E j` with `j ≤ k`. -/
theorem isZero_cechCohomology_obj_of_forall_exists_homologyMap_eq_zero {D : Type u'}
    [Category.{v'} D] [Preadditive D] [HasProducts.{w} D] [CategoryWithHomology D]
    [HasColimitsOfShape J D] (G : D ⥤ AddCommGrpCat.{w'}) [G.Faithful]
    [G.PreservesZeroMorphisms] (P : Cᵒᵖ ⥤ D)
    (h : ∀ (j : J) (z : G.obj (((cechComplexFunctor (E j).obj).obj P).homology n)),
      ∃ (k : J) (_ : j ≤ k) (φ : E k ⟶ E j),
        G.map (HomologicalComplex.homologyMap (cechComplexMap P φ) n) z = 0) :
    IsZero ((cechCohomology D E hE n).obj P) := by
  refine (IsZero.iff_id_eq_zero _).2 (cechCohomology_obj_hom_ext fun j ↦ G.map_injective ?_)
  rw [Category.comp_id, comp_zero, G.map_zero]
  ext z
  obtain ⟨k, hjk, φ, hz⟩ := h j z
  -- the structure map at `j` factors through the map to the finer family `E k`; the source of
  -- `(cechCohomologyι E hE n k).app P` is `((cechCohomologyDiagram _ E hE n).obj k).obj P`, which
  -- is the homology of the Čech complex only after unfolding `cechCohomologyDiagram_obj` and
  -- `FormalCoproduct.cech`, so the composites below are type-correct only up to that unfolding:
  -- `rw [ConcreteCategory.comp_apply]` and `simp` fail with an application type mismatch, and the
  -- steps are written as terms (`NatTrans.comp_app`, `congrArg`) that are checked up to it
  have hι : HomologicalComplex.homologyMap (cechComplexMap P φ) n ≫
      (cechCohomologyι E hE n k).app P = (cechCohomologyι E hE n j).app P := by
    rw [← cechComplexHomologyMap_app]
    exact (NatTrans.comp_app _ _ P).symm.trans <| NatTrans.congr_app
      (cechComplexHomologyMap_comp_cechCohomologyι D E hE n hjk φ) P
  rw [← hι, AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply]
  exact (ConcreteCategory.congr_hom (G.map_comp _ _) z).trans
    ((congrArg (G.map ((cechCohomologyι E hE n k).app P)).hom hz).trans (map_zero _))

section Forget

variable {J : Type w} [Preorder J] (E : J → FormalCoproduct.{w} C)
  (hE : ∀ ⦃i j : J⦄, i ≤ j → Nonempty (E j ⟶ E i)) (n : ℕ) {R : Type w} [Ring R]

/-- **Vanishing passes to the underlying abelian groups.** If the degree `n` Čech cohomology of a
presheaf of modules `P` vanishes, then so does the degree `n` Čech cohomology of the underlying
presheaf of abelian groups `P ⋙ forget₂`. -/
theorem isZero_cechCohomology_obj_comp_forget₂ (P : Cᵒᵖ ⥤ ModuleCat.{w} R)
    (h : IsZero ((cechCohomology (ModuleCat.{w} R) E hE n).obj P)) :
    IsZero ((cechCohomology AddCommGrpCat.{w} E hE n).obj
      (P ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})) := by
  let G := forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}
  let a (j : J) : G.obj (((cechComplexFunctor (E j).obj).obj P).homology n) ≅
      ((G.mapHomologicalComplex _).obj ((cechComplexFunctor (E j).obj).obj P)).homology n :=
    ((((cechComplexFunctor (E j).obj).obj P).sc n).mapHomologyIso G).symm
  have ha {j k : J} (φ : E k ⟶ E j) :
      G.map (HomologicalComplex.homologyMap (cechComplexMap P φ) n) ≫ (a k).hom =
        (a j).hom ≫ HomologicalComplex.homologyMap
          ((G.mapHomologicalComplex _).map (cechComplexMap P φ)) n :=
    ShortComplex.mapHomologyIso_inv_naturality _ G
  let e (j : J) : G.obj (((cechComplexFunctor (E j).obj).obj P).homology n) ≅
      ((cechComplexFunctor (E j).obj).obj (P ⋙ G)).homology n :=
    a j ≪≫ HomologicalComplex.homologyMapIso ((cechComplexFunctorMapIso (E j).obj G).app P) n
  have he {j k : J} (φ : E k ⟶ E j) :
      G.map (HomologicalComplex.homologyMap (cechComplexMap P φ) n) ≫ (e k).hom =
        (e j).hom ≫ HomologicalComplex.homologyMap (cechComplexMap (P ⋙ G) φ) n := by
    simp only [e, Iso.trans_hom, HomologicalComplex.homologyMapIso_hom, Iso.app_hom]
    calc
      _ = (a j).hom ≫ HomologicalComplex.homologyMap
          ((G.mapHomologicalComplex _).map (cechComplexMap P φ)) n ≫
          HomologicalComplex.homologyMap
            ((cechComplexFunctorMapIso (E k).obj G).hom.app P) n := by
        simpa only [Category.assoc] using
          ha φ =≫ HomologicalComplex.homologyMap
            ((cechComplexFunctorMapIso (E k).obj G).hom.app P) n
      _ = _ := by
        have hc := congrArg (fun g ↦ HomologicalComplex.homologyMap g n)
          (cechComplexFunctorMapIso_hom_app_comp_cechComplexMap (E k).obj G P φ)
        simpa only [HomologicalComplex.homologyMap_comp, Category.assoc] using (a j).hom ≫= hc
  let eD : (cechCohomologyDiagram (ModuleCat.{w} R) E hE n).flip.obj P ⋙ G ≅
      (cechCohomologyDiagram AddCommGrpCat.{w} E hE n).flip.obj (P ⋙ G) :=
    NatIso.ofComponents e fun {j k} f ↦ by
      have hm := NatTrans.congr_app
        (cechCohomologyDiagram_map (ModuleCat.{w} R) E hE n f (hE (leOfHom f)).some) P
      have ha := NatTrans.congr_app
        (cechCohomologyDiagram_map AddCommGrpCat.{w} E hE n f (hE (leOfHom f)).some) (P ⋙ G)
      exact ((congrArg G.map (hm.trans (cechComplexHomologyMap_app ..))) =≫ _).trans
        ((he (hE (leOfHom f)).some).trans
          (_ ≫= (ha.trans (cechComplexHomologyMap_app ..)).symm))
  exact (G.map_isZero h).of_iso
    (preservesColimitIso G _ ≪≫ HasColimit.isoOfNatIso eD).symm

end Forget

end TauCeti.CategoryTheory
