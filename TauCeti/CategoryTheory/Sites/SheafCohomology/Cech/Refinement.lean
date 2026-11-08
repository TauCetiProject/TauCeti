/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Colimit

/-!
# Vanishing of Čech cohomology over a system of families by refinement

Let `E : J → FormalCoproduct C` be a system of families of objects of `C`, as in
`TauCeti.CategoryTheory.cechCohomology`, and let `P` be a presheaf on `C` with values in a category
`D` which has a faithful functor to abelian groups preserving zero morphisms, such as modules
(through `forget₂`) or abelian groups themselves (through the identity). The Čech cohomology of
`P` for the system is a colimit of the Čech cohomologies of the families, so it vanishes as soon as
every class of every family of the system is killed by passing to a finer family.

## Main results

* `TauCeti.CategoryTheory.isZero_cechCohomology_obj_of_forall_exists_homologyMap_eq_zero`: the
  Čech cohomology vanishes if every cohomology class of every family of the system is killed by
  passing to some finer member of the system.
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

end TauCeti.CategoryTheory
