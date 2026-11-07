/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Fppf lifting of affine-valued points

A quasi-compact, surjective, flat morphism locally of finite presentation admits lifts of
every affine-valued point after one faithfully flat, finitely presented extension of its value
ring. The extension is the coordinate ring of a finite disjoint union of affine opens covering
the pullback of the point. This works even when the target scheme is nonaffine and the value
ring is nonreduced.

This lifting statement makes geometric fppf covers usable in comparisons of functors of
points, for example when realizing a homogeneous quotient as a projective orbit.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5, quotient sheaves.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- Every affine-valued point of the target of a quasi-compact fppf cover lifts after a
faithfully flat, finitely presented extension of the value ring. -/
theorem exists_faithfullyFlat_lift {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [Flat f] [Surjective f] [LocallyOfFinitePresentation f]
    {A : CommRingCat.{u}} (y : Spec A ⟶ Y) :
    ∃ (B : CommRingCat.{u}) (φ : A ⟶ B) (z : Spec B ⟶ X),
      φ.hom.FaithfullyFlat ∧ φ.hom.FinitePresentation ∧ z ≫ f = Spec.map φ ≫ y := by
  let 𝒰 := (pullback f y).affineCover.finiteSubcover
  let p : ∐ 𝒰.X ⟶ pullback f y := Sigma.desc 𝒰.f
  -- instance search does not find the source-locality of `LocallyOfFinitePresentation`
  have : IsZariskiLocalAtSource @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.FinitePresentation)
  have : LocallyOfFinitePresentation p :=
    IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((∐ 𝒰.X).isoSpec.inv ≫ p ≫ pullback.snd f y)
  refine ⟨Γ(∐ 𝒰.X, ⊤), φ, (∐ 𝒰.X).isoSpec.inv ≫ p ≫ pullback.fst f y, ?_, ?_, ?_⟩
  · exact (flat_and_surjective_SpecMap_iff φ).mp (hφ ▸ ⟨inferInstance, inferInstance⟩)
  · exact (LocallyOfFinitePresentation.SpecMap_iff φ).mp (hφ ▸ inferInstance)
  · simp [hφ, pullback.condition]

end AlgebraicGeometry.Scheme.Hom
