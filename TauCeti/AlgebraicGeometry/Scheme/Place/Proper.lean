/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.Place.Injective
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Basic
public import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Places have unique centers on proper curves

Let `X` be a proper integral scheme of dimension at most one over a field. If the local ring at
every codimension-one point is a discrete valuation ring, then the codimension-one points of `X`
are canonically equivalent to the normalized places of its function field.

Existence is the valuative criterion for properness, applied to the valuation ring of a place.
The closed point of the resulting lift cannot map to the generic point of `X`, since that would
put the whole function field in the proper valuation ring. The dimension bound therefore makes
the image a codimension-one point. Its local ring maps into the valuation ring, which identifies
the associated normalized place. Uniqueness is the valuative criterion for separatedness.

This equivalence permits divisor and principal-parts constructions indexed by codimension-one
points of a proper curve to be reindexed by function-field places.

## Main results

* `CodimensionOnePoint.toPlace_surjective`: every place of the function field of a proper curve
  is attached to a codimension-one point;
* `CodimensionOnePoint.equivPlace`: the resulting equivalence between codimension-one points and
  places.

## References

* The Stacks Project, Lemma 29.42.1 (Tag 0BX5), the valuative criterion for properness.
* R. Hartshorne, *Algebraic Geometry*, Chapter I, Section 6.
-/

public section

open CategoryTheory CategoryTheory.Limits Order _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

namespace CodimensionOnePoint

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]

/-- Every normalized place of the function field of a proper integral curve is attached to a
codimension-one point. -/
theorem toPlace_surjective (hdim : ∀ x : X, coheight x ≤ 1) :
    Function.Surjective (fun x : CodimensionOnePoint X ↦ X.toPlace (k := k) (x : X)) := by
  intro P
  let S : ValuativeCommSq (X ↘ Spec (.of k)) :=
    { R := P.integers
      K := X.functionField
      i₁ := X.fromSpecStalk (genericPoint X)
      i₂ := Spec.map (CommRingCat.ofHom (algebraMap k P.integers))
      commSq := ⟨by
        rw [X.fromSpecStalk_genericPoint_comp_over (k := k), ← Spec.map_comp]
        congr 1⟩ }
  have hproper : IsProper (X ↘ Spec (.of k)) := inferInstance
  rw [IsProper.eq_valuativeCriterion] at hproper
  have hvc : ValuativeCriterion (X ↘ Spec (.of k)) := hproper.1.1.1
  let lifts : Unique S.commSq.LiftStruct := (hvc S).some
  obtain ⟨l, hlK, _⟩ := lifts.default
  let x : X := l (IsLocalRing.closedPoint S.R)
  have hg :
      Spec.map (CommRingCat.ofHom
          (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ X.fromSpecStalk x =
        X.fromSpecStalk (genericPoint X) :=
    X.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec X).specializes trivial)
  have hspec :
      Spec.map (Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom
          (algebraMap P.integers X.functionField)) =
        Spec.map (CommRingCat.ofHom
          (algebraMap (X.presheaf.stalk x) X.functionField)) := by
    rw [← cancel_mono (X.fromSpecStalk x), Spec.map_comp, Category.assoc]
    dsimp only [x]
    rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hlK, hg]
  have hmap :
      Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom
          (algebraMap P.integers X.functionField) =
        CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) :=
    Spec.map_injective hspec
  have hx_ne : x ≠ genericPoint X := by
    intro hx
    let e : X.presheaf.stalk x ≅ X.functionField :=
      X.presheaf.stalkCongr (.of_eq hx)
    have halg : CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x) X.functionField) = e.hom := by
      rw [RingHom.algebraMap_toAlgebra]
      rfl
    have hmap' := hmap.trans halg
    have htop : P.integers = ⊤ := by
      apply le_antisymm le_top
      intro f _
      let a : X.presheaf.stalk x := e.inv f
      have ha := congrArg (fun g : X.presheaf.stalk x →+* X.functionField ↦ g a)
        (CommRingCat.hom_ext_iff.mp hmap')
      have ha' : ((Scheme.stalkClosedPointTo l a : P.integers) : X.functionField) = f := by
        change algebraMap P.integers X.functionField (Scheme.stalkClosedPointTo l a) =
          e.hom (e.inv f) at ha
        calc
          _ = e.hom (e.inv f) := by
            simpa only [ValuationSubring.algebraMap_apply] using ha
          _ = f := Iso.inv_hom_id_apply (C := CommRingCat) e f
      rw [← ha']
      exact (Scheme.stalkClosedPointTo l a).property
    exact P.integers_ne_top htop
  have hx_pos : 0 < coheight x := by
    rw [coheight_pos]
    intro hxmax
    apply hx_ne
    exact Inseparable.eq <| inseparable_iff_specializes_and.mpr
      ⟨hxmax (genericPoint_specializes x), genericPoint_specializes x⟩
  have hx_one : coheight x = 1 :=
    le_antisymm (hdim x) (Order.one_le_iff_pos.mpr hx_pos)
  let y : CodimensionOnePoint X := ⟨x, hx_one⟩
  let _ : IsDiscreteValuationRing (X.presheaf.stalk x) := inferInstanceAs
    (IsDiscreteValuationRing (X.presheaf.stalk (y : X)))
  refine ⟨y, Place.eq_of_integers_le ?_⟩
  intro f hf
  obtain ⟨a, rfl⟩ := (X.mem_toPlace_integers_iff_exists_stalk (k := k) x _).mp hf
  have ha := congrArg (fun g : X.presheaf.stalk x →+* X.functionField ↦ g a)
    (CommRingCat.hom_ext_iff.mp hmap)
  have ha' : ((Scheme.stalkClosedPointTo l a : P.integers) : X.functionField) =
      algebraMap (X.presheaf.stalk x) X.functionField a := by
    change algebraMap P.integers X.functionField (Scheme.stalkClosedPointTo l a) =
      algebraMap (X.presheaf.stalk x) X.functionField a at ha
    simpa only [ValuationSubring.algebraMap_apply] using ha
  rw [← ha']
  exact (Scheme.stalkClosedPointTo l a).property

/-- The codimension-one points of a proper integral curve are canonically equivalent to the
normalized places of its function field. -/
def equivPlace (hdim : ∀ x : X, coheight x ≤ 1) :
    CodimensionOnePoint X ≃ Place k X.functionField :=
  letI : X.IsSeparated := by
    constructor
    rw [← terminal.comp_from (X ↘ Spec (.of k))]
    infer_instance
  Equiv.ofBijective (fun x ↦ X.toPlace (k := k) (x : X))
    ⟨(fun x y h ↦ Subtype.ext (toPlace_eq_iff.mp h)), toPlace_surjective hdim⟩

/-- The point-to-place equivalence is induced by `Scheme.toPlace`. -/
@[simp]
theorem equivPlace_apply (hdim : ∀ x : X, coheight x ≤ 1) (x : CodimensionOnePoint X) :
    equivPlace (k := k) hdim x = X.toPlace (k := k) (x : X) := by
  unfold equivPlace
  exact Equiv.ofBijective_apply _ _ _

end CodimensionOnePoint

end

end TauCeti.AlgebraicGeometry
