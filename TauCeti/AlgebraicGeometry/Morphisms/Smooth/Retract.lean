/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import TauCeti.AlgebraicGeometry.Morphisms.FinitePresentation
public import TauCeti.RingTheory.Smooth.Retract

/-!
# Smooth morphisms are stable under retracts

If a morphism of schemes `f : X ⟶ S` is a retract of a smooth morphism `g : Y ⟶ T` in the arrow
category, then `f` is smooth (`AlgebraicGeometry.Smooth.of_retract`, packaged as the instance
`MorphismProperty.IsStableUnderRetracts @Smooth`).

The main case is a retract over a fixed base: morphisms `i : X ⟶ Y` and `r : Y ⟶ X` with
`i ≫ r = 𝟙 X` and `r ≫ f = g`. Then `f = i ≫ g` is locally of finite presentation by
cancellation, and at each point `x` the stalk of `X` at `r (i x) = x` is a retract of the stalk
of `Y` at `i x` as an algebra over the stalk of `S`, so it is formally smooth over it. The
general case reduces to this one after base change of `g` to `S`.

A typical use: a scheme over `S` which admits a section into a smooth `S`-scheme, retracted by a
morphism over `S`, is smooth over `S`. This is how a fine moduli scheme is shown to be smooth when
it is a retract of a finite étale cover of a smooth parameter space.

## Main results

* `AlgebraicGeometry.Smooth.of_retract_of_comp_eq`: a retract of a smooth morphism over the same
  base is smooth.
* `AlgebraicGeometry.Smooth.of_retract`: a retract of a smooth morphism in the arrow category is
  smooth.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}}

/-- **A retract of a smooth morphism over the same base is smooth.** Let `g : Y ⟶ S` be smooth
and let `i : X ⟶ Y` and `r : Y ⟶ X` satisfy `i ≫ r = 𝟙 X`. Then `r ≫ f = g` forces `f` to be
smooth. -/
theorem Smooth.of_retract_of_comp_eq (f : X ⟶ S) (g : Y ⟶ S) (i : X ⟶ Y) (r : Y ⟶ X)
    (hir : i ≫ r = 𝟙 X) (hrf : r ≫ f = g) [Smooth g] : Smooth f := by
  subst hrf
  have : LocallyOfFiniteType r := locallyOfFiniteType_of_comp r f
  have : LocallyOfFinitePresentation i :=
    locallyOfFinitePresentation_of_comp i r (hfg := by rw [hir]; infer_instance)
  have hf : f = i ≫ r ≫ f := by rw [reassoc_of% hir]
  have : LocallyOfFinitePresentation f := by rw [hf]; infer_instance
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, eq_top_iff]
  rintro x -
  have hx : r (i x) = x := by rw [← Scheme.Hom.comp_apply, hir]; rfl
  -- the stalk map of a morphism equal to the identity is undone by the specialization
  have hid (φ : X ⟶ X) (hφ : φ = 𝟙 X) (h : φ x ⤳ x) :
      φ.stalkMap x ≫ X.presheaf.stalkSpecializes h = 𝟙 _ := by
    subst hφ
    exact (congrArg (· ≫ _) (Scheme.Hom.stalkMap_id X x)).trans
      ((Category.id_comp _).trans (TopCat.Presheaf.stalkSpecializes_refl _ _))
  have key : (f.stalkMap (r (i x))).hom.FormallySmooth := by
    refine RingHom.FormallySmooth.of_retract (r.stalkMap (i x)).hom
      (i.stalkMap x ≫ X.presheaf.stalkSpecializes (Inseparable.of_eq hx).specializes).hom ?_ ?_
    · rw [← CommRingCat.hom_comp, ← CommRingCat.hom_id, ← Category.assoc,
        ← Scheme.Hom.stalkMap_comp]
      exact congrArg CommRingCat.Hom.hom (hid _ hir _)
    · rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
      exact Scheme.Hom.mem_smoothLocus.mp ((r ≫ f).smoothLocus_eq_top ▸ trivial)
  exact Scheme.Hom.mem_smoothLocus.mpr (hx ▸ key)

/-- **Smooth morphisms are stable under retracts.** If `f` is a retract of a smooth morphism `g`
in the arrow category, then `f` is smooth. -/
theorem Smooth.of_retract {X S Y T : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ T} (h : RetractArrow f g)
    [Smooth g] : Smooth f := by
  have hw : h.i.left ≫ g = f ≫ h.i.right := h.i_w
  refine Smooth.of_retract_of_comp_eq f (pullback.snd g h.i.right)
    (pullback.lift h.i.left f hw) (pullback.fst g h.i.right ≫ h.r.left) (by simp) ?_
  rw [Category.assoc, h.r_w, pullback.condition_assoc, h.retract_right]
  exact Category.comp_id _

instance : MorphismProperty.IsStableUnderRetracts @Smooth where
  of_retract h _ := Smooth.of_retract h

end AlgebraicGeometry
