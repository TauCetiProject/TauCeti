/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.Place.Injective
public import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Places have unique centers on proper curves

Let `X` be an integral scheme of dimension at most one over a field whose structure morphism
satisfies the existence part of the valuative criterion, a proper curve for instance. If the
local ring at every codimension-one point is a discrete valuation ring, then every normalized
place of the function field of `X` is attached to a codimension-one point; if `X` is moreover
separated, the codimension-one points are canonically equivalent to those places.

Existence is the valuative criterion, applied to the valuation ring of a place. The closed point
of the resulting lift cannot map to the generic point of `X`, since that would put the whole
function field in the valuation ring. The dimension bound therefore makes the image a
codimension-one point. Its local ring maps into the valuation ring, which identifies the
associated normalized place. Injectivity is `CodimensionOnePoint.toPlace_injective`, which rests
on the uniqueness part of the valuative criterion.

This equivalence permits divisor and principal-parts constructions indexed by codimension-one
points of a proper curve to be reindexed by function-field places.

## Main results

* `CodimensionOnePoint.toPlace_surjective`: every place of the function field of such a curve is
  attached to a codimension-one point;
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

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (.of k))]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]

/-- Every normalized place of the function field of an integral curve over `k` is attached to a
codimension-one point, as soon as the structure morphism satisfies the existence part of the
valuative criterion. A proper curve is the motivating instance. -/
theorem toPlace_surjective (hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)))
    (hdim : ∀ x : X, coheight x ≤ 1) :
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
  obtain ⟨l, hlK, -⟩ := (hex S).exists_lift.some
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
  -- The lift factors the inclusion of the stalk at `x` into the function field through the
  -- valuation ring of `P`; this is the only consequence of `hmap` used below.
  have hmem (a : X.presheaf.stalk x) :
      algebraMap (X.presheaf.stalk x) X.functionField a ∈ P.integers := by
    have ha : algebraMap P.integers X.functionField (Scheme.stalkClosedPointTo l a) =
        algebraMap (X.presheaf.stalk x) X.functionField a := by
      simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
        CommRingCat.hom_ofHom] using
        congrArg (fun g : X.presheaf.stalk x →+* X.functionField ↦ g a)
          (CommRingCat.hom_ext_iff.mp hmap)
    rw [← ha, ValuationSubring.algebraMap_apply]
    exact (Scheme.stalkClosedPointTo l a).property
  have hx_ne : x ≠ genericPoint X := by
    intro hx
    -- At the generic point the stalk is the whole function field, so `hmem` would make the
    -- valuation ring of `P` everything.
    let e : X.presheaf.stalk x ≅ X.functionField := X.presheaf.stalkCongr (.of_eq hx)
    have halg (b : X.presheaf.stalk x) :
        algebraMap (X.presheaf.stalk x) X.functionField b = e.hom b := by
      rw [RingHom.algebraMap_toAlgebra]
      simp [e]
    refine P.integers_ne_top (le_antisymm le_top fun f _ ↦ ?_)
    have h := hmem (e.inv f)
    rwa [halg, Iso.inv_hom_id_apply (C := CommRingCat) e f] at h
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
  exact hmem a

/-- The codimension-one points of a separated integral curve over `k` whose structure morphism
satisfies the existence part of the valuative criterion, a proper curve for instance, are
canonically equivalent to the normalized places of its function field. -/
def equivPlace [X.IsSeparated] (hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)))
    (hdim : ∀ x : X, coheight x ≤ 1) :
    CodimensionOnePoint X ≃ Place k X.functionField :=
  Equiv.ofBijective (fun x ↦ X.toPlace (k := k) (x : X))
    ⟨toPlace_injective, toPlace_surjective hex hdim⟩

/-- The point-to-place equivalence is induced by `Scheme.toPlace`. -/
@[simp]
theorem equivPlace_apply [X.IsSeparated]
    (hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)))
    (hdim : ∀ x : X, coheight x ≤ 1) (x : CodimensionOnePoint X) :
    equivPlace (k := k) hex hdim x = X.toPlace (k := k) (x : X) :=
  Equiv.ofBijective_apply _ _ _

end CodimensionOnePoint

end

end TauCeti.AlgebraicGeometry
