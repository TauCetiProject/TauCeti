/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Affine fppf lifting

An affine, surjective, flat morphism locally of finite presentation admits lifts of every
affine-valued point after one faithfully flat, finitely presented extension of its value
ring. The extension is the coordinate ring of the pullback of the point. This works even
when the target scheme is nonaffine and the value ring is nonreduced.

This lifting statement makes geometric fppf covers usable in comparisons of functors of
points, for example when realizing a homogeneous quotient as a projective orbit.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5, quotient sheaves.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- Every affine-valued point of the target of an affine fppf cover lifts after a
faithfully flat, finitely presented extension of the value ring. -/
theorem exists_faithfullyFlat_lift {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] [Flat f] [Surjective f] [LocallyOfFinitePresentation f]
    {A : CommRingCat.{u}} (y : Spec A ⟶ Y) :
    ∃ (B : CommRingCat.{u}) (φ : A ⟶ B) (z : Spec B ⟶ X),
      φ.hom.FaithfullyFlat ∧ φ.hom.FinitePresentation ∧ z ≫ f = Spec.map φ ≫ y := by
  let P := pullback f y
  let p : P ⟶ Spec A := pullback.snd f y
  let e : P ≅ Spec Γ(P, ⊤) := P.isoSpec
  let q : Spec Γ(P, ⊤) ⟶ Spec A := e.inv ≫ p
  let φ : A ⟶ Γ(P, ⊤) := Spec.preimage q
  have hφ : Spec.map φ = q := Spec.map_preimage q
  have : Flat q := inferInstance
  have : Surjective q := inferInstance
  have : LocallyOfFinitePresentation q := inferInstance
  refine ⟨Γ(P, ⊤), φ, e.inv ≫ pullback.fst f y, ?_, ?_, ?_⟩
  · apply (flat_and_surjective_SpecMap_iff φ).mp
    rw [hφ]
    exact ⟨inferInstance, inferInstance⟩
  · apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp
    rw [hφ]
    infer_instance
  · rw [hφ, Category.assoc, pullback.condition]
    exact (Category.assoc _ _ _).symm

end AlgebraicGeometry.Scheme.Hom
