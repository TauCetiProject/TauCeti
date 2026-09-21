/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.ProjectivePresentation

/-!
# Loops on a projective stable category

For an exact structure with enough projectives, choose conflations `ΩX ⟶ P(X) ⟶ X`.
Lifting a morphism `X ⟶ Y` to the projective middle terms induces a map `ΩX ⟶ ΩY`.
Different lifts induce the same map modulo morphisms factoring through projectives. This
constructs the additive loop endofunctor on the projective stable category.

Only enough projectives are needed for the construction. In a Frobenius exact category this is
the loop functor used with suspension to construct the stable triangulation; the one statement
about the chosen presentation that needs the Frobenius hypothesis, that its middle term is also
relatively injective, is recorded at the end of the file. Neither a quasi-inverse comparison nor
a triangulated structure is asserted in this file.

The API follows the suspension construction in
`TauCeti.CategoryTheory.Exact.Stable.Suspension`, but works without the Frobenius hypothesis.
It exposes the chosen presentation and its commuting squares for subsequent comparisons.

## Main definitions

* `TauCeti.ExactStructure.EnoughProjectives.loopObj`: the kernel of the chosen presentation.
* `TauCeti.ExactStructure.EnoughProjectives.loopMap`: the induced map on kernels.
* `TauCeti.ExactStructure.EnoughProjectives.stableLoop`: the additive stable loop functor.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
* Bernhard Keller, *Chain complexes and stable categories*, Manuscripta Mathematica **67**
  (1990), 379–417, Section 1.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

namespace ExactStructure.EnoughProjectives

variable {E : ExactStructure C} (hE : E.EnoughProjectives)

/-- The chosen projective middle term in the loop presentation of `X`. -/
noncomputable abbrev loopProjective (X : C) : C :=
  (hE.projectivePresentation X).P

/-- The loop object `ΩX`, the kernel term of the chosen projective presentation. -/
noncomputable abbrev loopObj (X : C) : C :=
  (hE.projectivePresentation X).K

/-- The inflation `ΩX ⟶ P(X)` in the chosen loop presentation. -/
noncomputable abbrev loopInflation (X : C) : hE.loopObj X ⟶ hE.loopProjective X :=
  (hE.projectivePresentation X).i

/-- The deflation `P(X) ⟶ X` in the chosen loop presentation. -/
noncomputable abbrev loopDeflation (X : C) : hE.loopProjective X ⟶ X :=
  (hE.projectivePresentation X).p

/-- The middle term of the chosen loop presentation is projective relative to `E`. -/
theorem isProjective_loopProjective (X : C) : E.isProjective (hE.loopProjective X) :=
  (hE.projectivePresentation X).isProjective

/-- The two maps in the chosen loop presentation compose to zero. -/
@[reassoc (attr := simp)]
theorem loopInflation_comp_loopDeflation (X : C) :
    hE.loopInflation X ≫ hE.loopDeflation X = 0 :=
  (hE.projectivePresentation X).zero

/-- The chosen loop presentation is a conflation of `E`. -/
theorem conflation_loopInflation_loopDeflation (X : C) :
    E.Conflation (ShortComplex.mk (hE.loopInflation X) (hE.loopDeflation X)
      (hE.loopInflation_comp_loopDeflation X)) :=
  (hE.projectivePresentation X).conflation

/-- The chosen lift of `f : X ⟶ Y` between the projective middle terms. -/
noncomputable abbrev loopMiddleMap {X Y : C} (f : X ⟶ Y) :
    hE.loopProjective X ⟶ hE.loopProjective Y :=
  (hE.projectivePresentation X).middleMap (hE.projectivePresentation Y) f

/-- The middle map lifts `f` along the loop deflations. -/
@[reassoc]
theorem loopMiddleMap_comp_loopDeflation {X Y : C} (f : X ⟶ Y) :
    hE.loopMiddleMap f ≫ hE.loopDeflation Y = hE.loopDeflation X ≫ f :=
  (hE.projectivePresentation X).middleMap_comp_p (hE.projectivePresentation Y) f

/-- The induced map on loop objects. Its class modulo projectives is independent of the lift. -/
noncomputable abbrev loopMap {X Y : C} (f : X ⟶ Y) : hE.loopObj X ⟶ hE.loopObj Y :=
  (hE.projectivePresentation X).kernelMap (hE.projectivePresentation Y) f

/-- The induced loop map makes the square on the inflations commute. -/
@[reassoc]
theorem loopMap_comp_loopInflation {X Y : C} (f : X ⟶ Y) :
    hE.loopMap f ≫ hE.loopInflation Y = hE.loopInflation X ≫ hE.loopMiddleMap f :=
  (hE.projectivePresentation X).kernelMap_comp_i (hE.projectivePresentation Y) f

/-- Any compatible maps between the chosen loop presentations inducing `f` give the same
morphism as `loopMap f` in the projective stable quotient. -/
theorem projectiveStableFunctor_map_loopMap_eq {X Y : C} (f : X ⟶ Y)
    (a : hE.loopProjective X ⟶ hE.loopProjective Y)
    (g : hE.loopObj X ⟶ hE.loopObj Y)
    (ha : a ≫ hE.loopDeflation Y = hE.loopDeflation X ≫ f)
    (hg : g ≫ hE.loopInflation Y = hE.loopInflation X ≫ a) :
    E.projectiveStableFunctor.map (hE.loopMap f) = E.projectiveStableFunctor.map g := by
  exact E.projectiveStableFunctor_map_kernelMap_eq
    (hE.projectivePresentation X) (hE.projectivePresentation Y) f a g ha hg

/-- Loops from the exact category to its projective stable quotient. -/
noncomputable abbrev loopToStable : C ⥤ E.ProjectiveStableCategory :=
  E.loopToStableOfPresentations hE.projectivePresentation

/-- The object formula for loops to the projective stable category. -/
theorem loopToStable_obj (X : C) :
    hE.loopToStable.obj X = E.projectiveStableFunctor.obj (hE.loopObj X) :=
  E.loopToStableOfPresentations_obj hE.projectivePresentation X

/-- The morphism formula for loops to the projective stable category. -/
theorem loopToStable_map {X Y : C} (f : X ⟶ Y) :
    hE.loopToStable.map f = eqToHom (hE.loopToStable_obj X) ≫
      E.projectiveStableFunctor.map (hE.loopMap f) ≫ eqToHom (hE.loopToStable_obj Y).symm :=
  E.loopToStableOfPresentations_map hE.projectivePresentation f

/-- Loops to the stable quotient preserve addition of morphisms. -/
noncomputable instance loopToStable_additive : (hE.loopToStable).Additive := by
  rw [loopToStable]
  infer_instance

/-- The loop object of a projective object is projective. -/
theorem isProjective_loopObj {X : C} (hX : E.isProjective X) :
    E.isProjective (hE.loopObj X) := by
  let s := E.splittingOfProjective (hE.projectivePresentation X).conflation hX
  exact E.isProjective.prop_of_retract
    ⟨hE.loopInflation X, s.r, s.f_r⟩ (hE.projectivePresentation X).isProjective

/-- Loops to the stable quotient kill every map factoring through a projective. -/
theorem loopToStable_kills_projectiveStableIdeal :
    E.projectiveStableIdeal ≤ (hE.loopToStable).kerIdeal := by
  intro X Y f hf
  rw [Functor.mem_kerIdeal_hom]
  obtain ⟨P, hP, i, p, rfl⟩ := (ObjectProperty.factorsThrough_iff E.isProjective _).mp
    ((ExactStructure.mem_projectiveStableIdeal_iff E).mp hf)
  rw [Functor.map_comp]
  have hzero : IsZero ((hE.loopToStable).obj P) :=
    hE.loopToStable_obj P ▸
      (ExactStructure.isZero_projectiveStableFunctor_obj_iff E _).mpr
        (hE.isProjective_loopObj hP)
  rw [hzero.eq_of_tgt ((hE.loopToStable).map i) 0, zero_comp]

/-- The additive loop endofunctor on the projective stable category. -/
noncomputable def stableLoop : E.ProjectiveStableCategory ⥤ E.ProjectiveStableCategory :=
  E.projectiveStableIdeal.lift hE.loopToStable hE.loopToStable_kills_projectiveStableIdeal

/-- Stable loops preserve addition of morphisms. -/
noncomputable instance stableLoop_additive : (hE.stableLoop).Additive := by
  rw [stableLoop]
  infer_instance

/-- On represented objects, the stable loop functor takes the chosen kernel. -/
@[simp]
theorem stableLoop_obj_projectiveStableFunctor_obj (X : C) :
    hE.stableLoop.obj (E.projectiveStableFunctor.obj X) =
      E.projectiveStableFunctor.obj (hE.loopObj X) := by
  simp only [stableLoop, CategoryTheory.Quotient.lift_obj_functor_obj, hE.loopToStable_obj]

/-- On represented morphisms, the stable loop functor applies the chosen kernel map. -/
@[simp]
theorem stableLoop_map_projectiveStableFunctor_map {X Y : C} (f : X ⟶ Y) :
    hE.stableLoop.map (E.projectiveStableFunctor.map f) =
      eqToHom (hE.stableLoop_obj_projectiveStableFunctor_obj X) ≫
        E.projectiveStableFunctor.map (hE.loopMap f) ≫
          eqToHom (hE.stableLoop_obj_projectiveStableFunctor_obj Y).symm :=
  (conj_eqToHom_iff_heq _ _ (hE.stableLoop_obj_projectiveStableFunctor_obj X)
    (hE.stableLoop_obj_projectiveStableFunctor_obj Y)).2
      ((conj_eqToHom_iff_heq _ _ (hE.loopToStable_obj X) (hE.loopToStable_obj Y)).1
        (hE.loopToStable_map f))

end ExactStructure.EnoughProjectives

/-! ### Loop presentations of a Frobenius exact structure -/

namespace ExactStructure.IsFrobenius

variable {E : ExactStructure C} (hE : E.IsFrobenius)

/-- The middle term of a chosen loop presentation is relatively injective. -/
theorem isInjective_loopProjective (X : C) :
    E.isInjective (hE.enoughProjectives.loopProjective X) :=
  (hE.projective_iff_injective _).mp (hE.enoughProjectives.isProjective_loopProjective X)

end ExactStructure.IsFrobenius

end TauCeti
