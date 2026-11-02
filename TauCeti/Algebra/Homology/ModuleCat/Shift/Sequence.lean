/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# Maps in cohomology of shifted morphisms of complexes of modules, on classes

A morphism `f : K ⟶ L⟦n⟧` of cochain complexes induces maps `K.homology a ⟶ L.homology a'` for
`n + a = a'` (`Functor.shiftMap` for the shift sequence of the cohomology functor).  For complexes
of modules, this map sends the class of a cycle `x` of `K` to the class of `f x`, read in `L` in
degree `a'` (`CochainComplex.shiftMap_homologyπ_moduleCatCyclesMk`).

## References

* M. Kashiwara, P. Schapira, *Categories and Sheaves*, Chapter 11.
-/

public section

open CategoryTheory Limits

namespace CochainComplex

variable {R : Type*} [Ring R]

/-- **The map in cohomology of a shifted morphism, on classes.** For `f : K ⟶ L⟦n⟧` and
`n + a = a'`, the induced map `K.homology a ⟶ L.homology a'` sends the class of a cycle `x` to the
class of `f x`, read in `L` in degree `a'`. -/
theorem shiftMap_homologyπ_moduleCatCyclesMk {K L : CochainComplex (ModuleCat R) ℤ} {n : ℤ}
    (f : K ⟶ L⟦n⟧) (a a' : ℤ) (h : n + a = a') (x : K.X a)
    (hx : (K.d a (a + 1)).hom x = 0) (y : L.X a')
    (hy : y = ((L.shiftFunctorObjXIso n a a' (by omega)).hom.hom ((f.f a).hom x)))
    (hy' : (L.d a' (a' + 1)).hom y = 0) :
    ((HomologicalComplex.homologyFunctor _ _ 0).shiftMap f a a' h).hom
        ((K.homologyπ a).hom (K.moduleCatCyclesMk x (a + 1) (by simp) hx)) =
      (L.homologyπ a').hom (L.moduleCatCyclesMk y (a' + 1) (by simp) hy') := by
  -- `shiftMap` is, by definition, the homology map of `f` followed by the shift isomorphism; `rw`
  -- cannot unfold the bundled `Functor.shiftMap`, so the goal is restated.
  change ((ShiftSequence.shiftIso (ModuleCat R) n a a' h).hom.app L).hom
      ((HomologicalComplex.homologyMap f a).hom
        ((K.homologyπ a).hom (K.moduleCatCyclesMk x (a + 1) (by simp) hx))) = _
  rw [HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk,
    ShiftSequence.shiftIso_hom_app]
  -- The shift isomorphism is the homology map of an isomorphism of short complexes; restate the
  -- goal as a composite so that naturality of `homologyπ` applies.
  change (((L⟦n⟧).sc a).homologyπ ≫ ShortComplex.homologyMap
    ((shiftShortComplexFunctorIso (ModuleCat R) n a a' h).hom.app L)).hom _ = _
  rw [ShortComplex.homologyπ_naturality, ModuleCat.hom_comp]
  refine congrArg (ModuleCat.Hom.hom (L.homologyπ a')) ?_
  apply L.moduleCat_iCycles_injective a'
  rw [← CochainComplex.shiftCyclesIso_hom]
  refine (congrArg (fun φ ↦ ModuleCat.Hom.hom φ _)
    (CochainComplex.shiftCyclesIso_hom_iCycles (K := L) n a a' h)).trans ?_
  rw [ModuleCat.comp_apply, HomologicalComplex.iCycles_moduleCatCyclesMk,
    HomologicalComplex.iCycles_moduleCatCyclesMk, hy]

end CochainComplex
