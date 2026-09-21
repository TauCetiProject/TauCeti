/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.Place.Basic
public import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# A place determines its center on a separated scheme

On an integral separated scheme over a field, two points with discrete valuation ring stalks
have the same associated function-field place exactly when they coincide. Equality of the
places identifies their valuation rings inside the function field. The uniqueness part of the
valuative criterion then identifies the two maps from the spectrum of this ring to the scheme,
and hence their closed-point images.

This is the injectivity step in comparing the points of a nonsingular proper curve with the
places of its function field, needed to compare divisor and principal-parts constructions.

## References

* The Stacks Project, Lemma 26.22.1 (Tag 01KZ), uniqueness in the valuative criterion.
* R. Hartshorne, *Algebraic Geometry*, Chapter I, Section 6.
-/

public section

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (.of k))] [X.IsSeparated]

/-- On a separated integral scheme, a function-field place has at most one center whose local
ring is a discrete valuation ring. -/
@[simp]
theorem toPlace_eq_iff {x y : X}
    [IsDiscreteValuationRing (X.presheaf.stalk x)]
    [IsDiscreteValuationRing (X.presheaf.stalk y)] :
    X.toPlace (k := k) x = X.toPlace (k := k) y ↔ x = y := by
  constructor
  · intro h
    -- Identify the two stalks through their common valuation subring.
    let ex := X.stalkToPlaceIntegersAlgEquiv (k := k) x
    let ey := X.stalkToPlaceIntegersAlgEquiv (k := k) y
    let e : X.presheaf.stalk y ≃+* X.presheaf.stalk x :=
      ey.toRingEquiv.trans ((RingEquiv.subringCongr
        (congrArg (fun p : Place k X.functionField ↦ p.integers.toSubring) h.symm)).trans
          ex.symm.toRingEquiv)
    have he (a : X.presheaf.stalk y) :
        algebraMap (X.presheaf.stalk x) X.functionField (e a) =
          algebraMap (X.presheaf.stalk y) X.functionField a := by
      rw [← X.coe_stalkToPlaceIntegersAlgEquiv (k := k) x,
        ← X.coe_stalkToPlaceIntegersAlgEquiv (k := k) y]
      simp only [e, ex, ey, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
        AlgEquiv.apply_symm_apply]
      exact RingEquiv.coe_subringCongr_apply _ _
    have hg (z : X) :
        Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk z) X.functionField)) ≫
          X.fromSpecStalk z = X.fromSpecStalk (genericPoint X) :=
      X.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec X).specializes trivial)
    -- Both local spectra extend the same generic-point map.
    let S : ValuativeCommSq (terminal.from X) :=
      { R := X.presheaf.stalk x
        K := X.functionField
        i₁ := X.fromSpecStalk (genericPoint X)
        i₂ := terminal.from _
        commSq := ⟨terminal.hom_ext _ _⟩ }
    have hcomp :
        Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
          (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecStalk y) =
        X.fromSpecStalk (genericPoint X) := by
      rw [← Spec.map_comp_assoc]
      have hr : CommRingCat.ofHom e.toRingHom ≫
          CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) =
          CommRingCat.ofHom (algebraMap (X.presheaf.stalk y) X.functionField) := by
        ext a
        exact he a
      rw [hr, hg]
    let l₁ : S.commSq.LiftStruct :=
      ⟨X.fromSpecStalk x, hg x, terminal.hom_ext _ _⟩
    let l₂ : S.commSq.LiftStruct :=
      ⟨Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecStalk y,
        hcomp, terminal.hom_ext _ _⟩
    have : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion _ S
    have hl : X.fromSpecStalk x =
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecStalk y :=
      congrArg CommSq.LiftStruct.l (Subsingleton.elim l₁ l₂)
    -- Equal lifts have equal closed-point images, which are the original centers.
    have : IsLocalHom e.toRingHom :=
      isLocalHom_of_leftInverse e.symm.toRingHom e.left_inv
    have hp := congrArg (fun f : Spec (X.presheaf.stalk x) ⟶ X ↦
      f (IsLocalRing.closedPoint (X.presheaf.stalk x))) hl
    calc
      x = (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecStalk y)
          (IsLocalRing.closedPoint (X.presheaf.stalk x)) :=
        Scheme.fromSpecStalk_closedPoint.symm.trans hp
      _ = X.fromSpecStalk y (Spec.map (CommRingCat.ofHom e.toRingHom)
          (IsLocalRing.closedPoint (X.presheaf.stalk x))) := Scheme.Hom.comp_apply _ _ _
      _ = y := (congrArg (X.fromSpecStalk y)
        (Spec_closedPoint (f := CommRingCat.ofHom e.toRingHom))).trans
          Scheme.fromSpecStalk_closedPoint
  · rintro rfl
    rfl

end TauCeti.AlgebraicGeometry
