/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.Frobenius
public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.CategoryTheory.Exact.Stable.Basic
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Equivalence

/-!
# Stable cycles of complete resolutions

Taking cycles of a totally acyclic complex gives a Gorenstein-projective module. A chain
homotopy makes the difference of the induced cycle maps factor through a finite projective
term of the target complex. Thus cycles define an additive functor from the homotopy category
of totally acyclic complexes to the stable category of Gorenstein-projective modules.
This functor is essentially surjective in every degree: a shifted complete resolution supplies
a preimage of every Gorenstein-projective module. No full-faithfulness or triangulated
comparison for the cycle functor is asserted here.

The source is the quotient of `TauCeti.TotallyAcyclicComplex`, defined in
`TauCeti.Algebra.Homology.TotallyAcyclic.Basic`, by the
kernel of its functor to Mathlib's homotopy category. Its inclusion into that homotopy
category is full and faithful. In particular its morphisms are ordinary chain-homotopy classes,
without requiring total acyclicity to be invariant under arbitrary homotopy equivalences.

Use `A = Rᵐᵒᵖ` for right `R`-modules. The module universe may be independent of the ring
universe provided the ring is small in it; taking the universes equal includes the regular
module and its finite free powers.

## References

* R.-O. Buchweitz, *Maximal Cohen--Macaulay Modules and Tate Cohomology*, Section 4.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

namespace TauCeti

namespace TotallyAcyclicComplex

variable (A : Type u) [Ring A]

/-- Forget total acyclicity and pass to Mathlib's homotopy category. -/
abbrev toHomotopyCategory : TotallyAcyclicComplex.{v} A ⥤
    _root_.HomotopyCategory (ModuleCat.{v} A) (ComplexShape.up ℤ) :=
  ObjectProperty.ι
    (fun P : CochainComplex (ModuleCat.{v} A) ℤ ↦ P.IsTotallyAcyclic) ⋙
    _root_.HomotopyCategory.quotient _ _

/-- The ideal of null-homotopic maps between totally acyclic complexes. -/
abbrev homotopyIdeal : MorphismIdeal (TotallyAcyclicComplex.{v} A) :=
  (toHomotopyCategory A).kerIdeal

/-- Membership in the homotopy ideal means ordinary null-homotopy of the chain map. -/
theorem mem_homotopyIdeal_iff {P Q : TotallyAcyclicComplex.{v} A} (f : P ⟶ Q) :
    f ∈ (homotopyIdeal A).hom P Q ↔ Nonempty (Homotopy f.hom 0) := by
  rw [Functor.mem_kerIdeal_hom]
  exact _root_.HomotopyCategory.quotient_map_eq_zero_iff f.hom

/-- The homotopy category of totally acyclic complexes, with chain-homotopy classes as maps. -/
abbrev HomotopyCategory := (homotopyIdeal.{v} A).Quotient

/-- The additive quotient from totally acyclic complexes to their homotopy category. -/
abbrev quotient : TotallyAcyclicComplex.{v} A ⥤ HomotopyCategory.{v} A :=
  (homotopyIdeal A).quotientFunctor

/-- The full and faithful inclusion of totally acyclic homotopy classes into the ambient
homotopy category. -/
abbrev homotopyInclusion : HomotopyCategory.{v} A ⥤
    _root_.HomotopyCategory (ModuleCat.{v} A) (ComplexShape.up ℤ) :=
  (homotopyIdeal A).lift (toHomotopyCategory A) le_rfl

instance : (homotopyInclusion.{v} A).Faithful :=
  ((homotopyIdeal A).faithful_lift_iff (toHomotopyCategory A) le_rfl).mpr le_rfl

/-- The ambient inclusion sends a homotopy class to the class of its underlying chain map. -/
-- Rewrite the lift before simplifying its quotient-map argument, avoiding generic limit search.
@[simp↓ high]
theorem homotopyInclusion_map_quotient_map {P Q : TotallyAcyclicComplex.{v} A} (f : P ⟶ Q) :
    (homotopyInclusion A).map ((quotient A).map f) =
      (_root_.HomotopyCategory.quotient _ _).map f.hom :=
  CategoryTheory.Quotient.lift_map_functor_map _ _ _ _

/-- Equality in the source quotient is precisely chain homotopy. -/
theorem quotient_map_eq_iff {P Q : TotallyAcyclicComplex.{v} A} (f g : P ⟶ Q) :
    (quotient A).map f = (quotient A).map g ↔ Nonempty (Homotopy f.hom g.hom) := by
  rw [← (homotopyInclusion A).map_injective.eq_iff,
    homotopyInclusion_map_quotient_map, homotopyInclusion_map_quotient_map]
  exact CategoryTheory.Quotient.functor_map_eq_iff _ _ _

/-- Cycles in any degree, viewed as Gorenstein-projective modules. -/
abbrev cyclesFunctor (n : ℤ) : TotallyAcyclicComplex.{v} A ⥤ GorensteinProjectiveModuleCat.{v} A :=
  (IsGorensteinProjective A).lift
    (ObjectProperty.ι
      (fun P : CochainComplex (ModuleCat.{v} A) ℤ ↦ P.IsTotallyAcyclic) ⋙
      HomologicalComplex.cyclesFunctor (ModuleCat.{v} A) (ComplexShape.up ℤ) n)
    (fun P ↦ P.property.isGorensteinProjective_cycles n)

-- Instance search does not match the generic lift instance without this explicit application.
instance (n : ℤ) : (cyclesFunctor.{v} A n).Additive :=
  Functor.instAdditiveFullSubcategoryLift _ _ _

/-- The underlying module of the cycle functor is the usual module of cycles. -/
@[simp]
theorem cyclesFunctor_obj_obj (n : ℤ) (P : TotallyAcyclicComplex.{v} A) :
    ((cyclesFunctor A n).obj P).obj = P.obj.cycles n := (rfl)

/-- The underlying map of the cycle functor is Mathlib's induced map on cycles. -/
@[simp]
theorem cyclesFunctor_map_hom (n : ℤ) {P Q : TotallyAcyclicComplex.{v} A} (f : P ⟶ Q) :
    ((cyclesFunctor A n).map f).hom = cyclesMap f.hom n := (rfl)

/-- Every Gorenstein-projective module is the cycles in any prescribed degree of a shifted
complete resolution, up to isomorphism. -/
instance cyclesFunctor_essSurj (n : ℤ) : (cyclesFunctor.{v} A n).EssSurj where
  mem_essImage M := by
    obtain ⟨P, hP, ⟨e⟩⟩ := (isGorensteinProjective_iff M.obj).mp M.property
    exact ⟨⟨P⟦-n⟧, hP.shift (-n)⟩,
      ⟨ObjectProperty.isoMk _ (P.shiftCyclesIso (-n) n 0 (by simp) ≪≫ e)⟩⟩

variable [Small.{v} A]

/-- Homotopic chain maps induce equal stable cycle maps. The factorization uses the target's
finite projective term immediately preceding the chosen degree. -/
theorem stableCycles_map_eq_of_homotopy (n : ℤ) {P Q : TotallyAcyclicComplex.{v} A}
    {f g : P ⟶ Q} (h : Homotopy f.hom g.hom) :
    ((GorensteinProjectiveModuleCat.exactStructure A).projectiveStableFunctor).map
        ((cyclesFunctor A n).map f) =
      ((GorensteinProjectiveModuleCat.exactStructure A).projectiveStableFunctor).map
        ((cyclesFunctor A n).map g) := by
  rw [MorphismIdeal.quotientFunctor_map_eq_iff,
    ExactStructure.mem_projectiveStableIdeal_iff, ObjectProperty.factorsThrough_iff]
  let m := (ComplexShape.up ℤ).prev n
  have := Q.property.finite m
  have := Q.property.projective m
  let T : GorensteinProjectiveModuleCat.{v} A :=
    ⟨Q.obj.X m, isGorensteinProjective_of_projective _⟩
  refine ⟨T, (GorensteinProjectiveModuleCat.exactStructure_isProjective_iff T).mpr
    (Q.property.projective m),
    ObjectProperty.homMk (P.obj.iCycles n ≫ h.hom n m),
    ObjectProperty.homMk (Q.obj.toCycles m n), ?_⟩
  apply ObjectProperty.hom_ext
  exact h.cyclesMap_sub_eq n

/-- Stable cycles kill every null-homotopic chain map. -/
theorem homotopyIdeal_le_ker_stableCycles (n : ℤ) :
    homotopyIdeal A ≤ (cyclesFunctor A n ⋙
      (GorensteinProjectiveModuleCat.exactStructure A).projectiveStableFunctor).kerIdeal := by
  intro P Q f hf
  obtain ⟨h⟩ := (mem_homotopyIdeal_iff A f).mp hf
  rw [Functor.mem_kerIdeal_hom, Functor.comp_map]
  have h' : Homotopy f.hom (0 : P ⟶ Q).hom := h
  simpa only [Functor.map_zero] using stableCycles_map_eq_of_homotopy A n h'

/-- Cycles of complete resolutions, descended to chain-homotopy classes and stable maps. -/
abbrev stableCyclesFunctor (n : ℤ) : HomotopyCategory.{v} A ⥤
    (GorensteinProjectiveModuleCat.exactStructure A).ProjectiveStableCategory :=
  (homotopyIdeal A).lift (cyclesFunctor A n ⋙
    (GorensteinProjectiveModuleCat.exactStructure A).projectiveStableFunctor)
    (homotopyIdeal_le_ker_stableCycles A n)

/-- Stable cycles restrict along the homotopy quotient to ordinary cycles followed by the
stable quotient. -/
theorem quotient_comp_stableCyclesFunctor (n : ℤ) :
    quotient A ⋙ stableCyclesFunctor A n = cyclesFunctor A n ⋙
      (GorensteinProjectiveModuleCat.exactStructure A).projectiveStableFunctor :=
  CategoryTheory.Quotient.lift_spec _ _ (fun _ _ _ _ h ↦
    (homotopyIdeal A).map_eq_of_rel _ (homotopyIdeal_le_ker_stableCycles A n) h)

/-- On a complete resolution, stable cycles are the stable class of its cycle module. -/
@[simp]
theorem stableCyclesFunctor_obj_quotient_obj (n : ℤ) (P : TotallyAcyclicComplex.{v} A) :
    (stableCyclesFunctor A n).obj ((quotient A).obj P) =
      (GorensteinProjectiveModuleCat.exactStructure A).projectiveStableFunctor.obj
        ((cyclesFunctor A n).obj P) := (rfl)

/-- On a chain map, stable cycles are represented by its induced map on cycles. -/
-- Rewrite the lift before simplifying its quotient-map argument, avoiding generic limit search.
@[simp↓ high]
theorem stableCyclesFunctor_map_quotient_map (n : ℤ)
    {P Q : TotallyAcyclicComplex.{v} A} (f : P ⟶ Q) :
    (stableCyclesFunctor A n).map ((quotient A).map f) =
      (GorensteinProjectiveModuleCat.exactStructure A).projectiveStableFunctor.map
        ((cyclesFunctor A n).map f) :=
  CategoryTheory.Quotient.lift_map_functor_map _ _ _ _

end TotallyAcyclicComplex

end TauCeti
