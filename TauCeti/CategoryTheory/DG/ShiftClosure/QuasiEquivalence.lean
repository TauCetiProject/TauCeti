/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import TauCeti.CategoryTheory.DG.QuasiEquivalence
public import TauCeti.CategoryTheory.DG.ShiftClosure.Basic

/-!
# Quasi-fully faithful DG functors on shift closures

The Hom complexes of the shift closure are shifts of those of the original DG category,
`Hom(X[r], Y[s]) ≅ Hom(X, Y)[s - r]` (`TauCeti.DGShiftClosure.dgHomComplexIso`), and the DG
functor induced by `F` acts on them by the shift of the action of `F`.  Since shifting preserves
quasi-isomorphisms, a quasi-fully faithful DG functor stays quasi-fully faithful on shift
closures.

## Main results

* `CategoryTheory.EnrichedFunctor.IsQuasiFullyFaithful.mapDGShiftClosure`: a quasi-fully faithful
  DG functor induces a quasi-fully faithful DG functor between shift closures.
-/

public section

open CategoryTheory

namespace CategoryTheory.EnrichedFunctor

open TauCeti

universe v u u₂

variable {R : Type v} [CommRing R] {C : Type u} {D : Type u₂} [DGCategory R C] [DGCategory R D]

/-- **A quasi-fully faithful DG functor is quasi-fully faithful on shift closures**: its action
on `Hom(X[r], Y[s]) = Hom(X, Y)[s - r]` is a shift of a quasi-isomorphism. -/
theorem IsQuasiFullyFaithful.mapDGShiftClosure
    {F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D} (hF : F.IsQuasiFullyFaithful) :
    F.mapDGShiftClosure.IsQuasiFullyFaithful := by
  refine (isQuasiFullyFaithful_iff_quasiIso _).2 fun X Y ↦ ?_
  refine (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk' _ _ (DGShiftClosure.dgHomComplexIso R X Y)
    (DGShiftClosure.dgHomComplexIso R (F.mapDGShiftClosure.obj X) (F.mapDGShiftClosure.obj Y))
      ?_)).2 ((CochainComplex.quasiIso_shift_iff _ _).2 (hF.quasiIso X.obj Y.obj))
  ext n f
  -- `simp only` cannot replace this chain: the objects of the right-hand composite are
  -- `F.mapDGShiftClosure.obj X`, which reducible unification does not identify with the literal
  -- shifted objects in `DGShiftClosure.dgHomComplexIso_hom_f_apply` and `dgMap_apply`.
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply, CochainComplex.shiftFunctor_map_f',
    ← dgMap_apply, ← dgMap_apply, DGShiftClosure.dgHomComplexIso_hom_f_apply,
    DGShiftClosure.dgHomComplexIso_hom_f_apply, dgMap_mapDGShiftClosure]
  exact (F.dgHomEquiv_mapDGShiftClosureHom f).symm

end CategoryTheory.EnrichedFunctor
