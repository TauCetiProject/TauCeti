/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Fppf lifting of affine-valued points

A surjective, flat morphism locally of finite presentation admits lifts of every affine-valued
point after one faithfully flat, finitely presented extension of its value ring. Such a morphism
is open, so finitely many affine opens of the pullback of the point have images covering the
affine source of the point. The extension is the coordinate ring of their disjoint union. This
works even when the target scheme is nonaffine and the value ring is nonreduced.

This lifting statement makes geometric fppf covers usable in comparisons of functors of
points, for example when realizing a homogeneous quotient as a projective orbit.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5, quotient sheaves.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- Every affine-valued point of the target of an fppf cover lifts after a faithfully flat,
finitely presented extension of the value ring. -/
theorem exists_faithfullyFlat_lift {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] [LocallyOfFinitePresentation f]
    {A : CommRingCat.{u}} (y : Spec A ⟶ Y) :
    ∃ (B : CommRingCat.{u}) (φ : A ⟶ B) (z : Spec B ⟶ X),
      φ.hom.FaithfullyFlat ∧ φ.hom.FinitePresentation ∧ z ≫ f = Spec.map φ ≫ y := by
  -- The base change of `f` along `y` is flat and locally of finite presentation, hence open, so
  -- the images of finitely many affine opens of `pullback f y` cover the compact `Spec A`.
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : (pullback f y).affineOpens ↦ pullback.snd f y '' (U.1 : Set (pullback f y).carrier))
    (fun U ↦ (pullback.snd f y).isOpenMap _ U.1.2) fun a _ ↦ by
      obtain ⟨x, rfl⟩ := (pullback.snd f y).surjective a
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        (pullback f y).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, x, hxU, rfl⟩
  have (U : t) : IsAffine U.1.1 := U.1.2
  let p : ∐ (fun U : t ↦ (U.1.1 : Scheme)) ⟶ pullback f y := Sigma.desc fun U ↦ U.1.1.ι
  -- instance search does not find the source-locality of `LocallyOfFinitePresentation`
  have : IsZariskiLocalAtSource @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.FinitePresentation)
  have : LocallyOfFinitePresentation p :=
    IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  have : Surjective (p ≫ pullback.snd f y) := ⟨fun a ↦ by
    obtain ⟨U, hU, x, hx, rfl⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ a))
    obtain ⟨x, rfl⟩ : x ∈ Set.range U.1.ι := by rwa [Scheme.Opens.range_ι]
    refine ⟨Sigma.ι (fun U : t ↦ (U.1.1 : Scheme)) ⟨U, hU⟩ x, ?_⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc_assoc, Scheme.Hom.comp_apply]⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((∐ fun U : t ↦ (U.1.1 : Scheme)).isoSpec.inv ≫ p ≫
    pullback.snd f y)
  refine ⟨_, φ, (∐ fun U : t ↦ (U.1.1 : Scheme)).isoSpec.inv ≫ p ≫ pullback.fst f y, ?_, ?_, ?_⟩
  · exact (flat_and_surjective_SpecMap_iff φ).mp (hφ ▸ ⟨inferInstance, inferInstance⟩)
  · exact (LocallyOfFinitePresentation.SpecMap_iff φ).mp (hφ ▸ inferInstance)
  · simp [hφ, pullback.condition]

end AlgebraicGeometry.Scheme.Hom
