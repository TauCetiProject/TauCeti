/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Basic

/-!
# Loops on a projective stable category

For an exact structure with enough projectives, choose conflations `ΩX ⟶ P(X) ⟶ X`.
Lifting a morphism `X ⟶ Y` to the projective middle terms induces a map `ΩX ⟶ ΩY`.
Different lifts induce the same map modulo morphisms factoring through projectives. This
constructs the additive loop endofunctor on the projective stable category.

Only enough projectives are needed here. In a Frobenius exact category this is the loop
functor used with suspension to construct the stable triangulation. Neither a quasi-inverse
comparison nor a triangulated structure is asserted in this file.

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

/-- The chosen lift of `f : X ⟶ Y` between the projective middle terms. -/
noncomputable def loopMiddleMap {X Y : C} (f : X ⟶ Y) :
    hE.loopProjective X ⟶ hE.loopProjective Y :=
  (hE.projectivePresentation X).isProjective.factorThru
    (E.isDeflation_g (hE.projectivePresentation Y).conflation)
    (hE.loopDeflation X ≫ f)

/-- The middle map lifts `f` along the loop deflations. -/
@[reassoc (attr := simp)]
theorem loopMiddleMap_comp_loopDeflation {X Y : C} (f : X ⟶ Y) :
    hE.loopMiddleMap f ≫ hE.loopDeflation Y = hE.loopDeflation X ≫ f :=
  (hE.projectivePresentation X).isProjective.factorThru_comp
    (E.isDeflation_g (hE.projectivePresentation Y).conflation)
    (hE.loopDeflation X ≫ f)

/-- The induced map on loop objects. Its class modulo projectives is independent of the lift. -/
noncomputable def loopMap {X Y : C} (f : X ⟶ Y) : hE.loopObj X ⟶ hE.loopObj Y :=
  (E.isKernelCokernelPair _ (hE.projectivePresentation Y).conflation).lift
    (hE.loopInflation X ≫ hE.loopMiddleMap f) (by
      rw [Category.assoc, hE.loopMiddleMap_comp_loopDeflation,
        ← Category.assoc, (hE.projectivePresentation X).zero, zero_comp])

/-- The induced loop map makes the square on the inflations commute. -/
@[reassoc (attr := simp)]
theorem loopMap_comp_loopInflation {X Y : C} (f : X ⟶ Y) :
    hE.loopMap f ≫ hE.loopInflation Y = hE.loopInflation X ≫ hE.loopMiddleMap f :=
  (E.isKernelCokernelPair _ (hE.projectivePresentation Y).conflation).lift_f _ _

/-- Any compatible maps between the chosen loop presentations inducing `f` give the same
morphism as `loopMap f` in the projective stable quotient. -/
theorem projectiveStableFunctor_map_loopMap_eq {X Y : C} (f : X ⟶ Y)
    (a : hE.loopProjective X ⟶ hE.loopProjective Y)
    (g : hE.loopObj X ⟶ hE.loopObj Y)
    (ha : a ≫ hE.loopDeflation Y = hE.loopDeflation X ≫ f)
    (hg : g ≫ hE.loopInflation Y = hE.loopInflation X ≫ a) :
    E.projectiveStableFunctor.map (hE.loopMap f) = E.projectiveStableFunctor.map g := by
  rw [MorphismIdeal.quotientFunctor_map_eq_iff,
    ExactStructure.mem_projectiveStableIdeal_iff]
  let b := hE.loopMiddleMap f - a
  have hb : b ≫ hE.loopDeflation Y = 0 := by
    rw [Preadditive.sub_comp, hE.loopMiddleMap_comp_loopDeflation, ha, sub_self]
  let t := (E.isKernelCokernelPair _ (hE.projectivePresentation Y).conflation).lift b hb
  have ht : t ≫ hE.loopInflation Y = b :=
    (E.isKernelCokernelPair _ (hE.projectivePresentation Y).conflation).lift_f b hb
  have hdiff : hE.loopMap f - g = hE.loopInflation X ≫ t := by
    have := (E.isKernelCokernelPair _ (hE.projectivePresentation Y).conflation).mono_f
    rw [← cancel_mono (hE.loopInflation Y)]
    calc
      (hE.loopMap f - g) ≫ hE.loopInflation Y =
          hE.loopInflation X ≫ hE.loopMiddleMap f - hE.loopInflation X ≫ a := by
        rw [Preadditive.sub_comp, hE.loopMap_comp_loopInflation, hg]
      _ = hE.loopInflation X ≫ b := by rw [Preadditive.comp_sub]
      _ = (hE.loopInflation X ≫ t) ≫ hE.loopInflation Y := by
        rw [Category.assoc, ht]
  rw [hdiff]
  exact ObjectProperty.factorsThrough_comp E.isProjective
    (hE.projectivePresentation X).isProjective (hE.loopInflation X) t

/-- Loops from the exact category to its projective stable quotient. -/
noncomputable def loopToStable : C ⥤ E.ProjectiveStableCategory where
  obj X := E.projectiveStableFunctor.obj (hE.loopObj X)
  map f := E.projectiveStableFunctor.map (hE.loopMap f)
  map_id X := by
    simpa using hE.projectiveStableFunctor_map_loopMap_eq (f := 𝟙 X)
      (𝟙 (hE.loopProjective X)) (𝟙 (hE.loopObj X)) (by simp) (by simp)
  map_comp f g := by
    simpa using hE.projectiveStableFunctor_map_loopMap_eq (f := f ≫ g)
      (hE.loopMiddleMap f ≫ hE.loopMiddleMap g)
      (hE.loopMap f ≫ hE.loopMap g) (by simp) (by simp)

/-- The object formula for loops to the projective stable category. -/
@[simp]
theorem loopToStable_obj (X : C) :
    hE.loopToStable.obj X = E.projectiveStableFunctor.obj (hE.loopObj X) :=
  (rfl)

/-- The morphism formula for loops to the projective stable category. -/
@[simp]
theorem loopToStable_map {X Y : C} (f : X ⟶ Y) :
    hE.loopToStable.map f = eqToHom (hE.loopToStable_obj X) ≫
      E.projectiveStableFunctor.map (hE.loopMap f) ≫ eqToHom (hE.loopToStable_obj Y).symm :=
  (conj_eqToHom_iff_heq _ _ (hE.loopToStable_obj X) (hE.loopToStable_obj Y)).2 HEq.rfl

/-- Loops to the stable quotient preserve addition of morphisms. -/
noncomputable instance loopToStable_additive : (hE.loopToStable).Additive where
  map_add := by
    intro X Y f g
    rw [hE.loopToStable_map (f + g), hE.loopToStable_map f, hE.loopToStable_map g,
      ← Preadditive.comp_add, ← Preadditive.add_comp]
    rw [hE.projectiveStableFunctor_map_loopMap_eq (f := f + g)
      (hE.loopMiddleMap f + hE.loopMiddleMap g)
      (hE.loopMap f + hE.loopMap g) (by simp) (by simp)]
    simp only [Functor.map_add]

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
    (hE.stableLoop_obj_projectiveStableFunctor_obj Y)).2 HEq.rfl

end ExactStructure.EnoughProjectives

end TauCeti
