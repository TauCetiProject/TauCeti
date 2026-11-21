/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.QuasiCompact
public import TauCeti.AlgebraicGeometry.Morphisms.Separated
public import TauCeti.AlgebraicGeometry.Scheme.LocallyDirected
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Separated gluing along a common open

Let `i : U ⟶ X` and `j : U ⟶ Y` be open immersions over `S`. The pushout glues `X` and `Y`
along exactly `U`. If both pieces are separated over `S`, their gluing is separated over `S`
if and only if `U ⟶ X ×_S Y` is a closed immersion. Local finite type and quasi-compactness
pass from the two structure maps to the glued structure map, so separated schemes of finite
type can be glued whenever their overlap is closed in their fibre product.

This criterion is used to glue modifications after arranging a closed overlap. No density,
Noetherian, or quasi-compactness hypothesis on the base is needed here.

## References

* The Stacks Project, Lemma 38.33.1, in *Nagata compactification* (Tag 0F3U).
* The Stacks Project, Section 26.14, *Gluing schemes* (Tag 01JA).
-/

public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable {U X Y S : Scheme.{u}} (i : U ⟶ X) (j : U ⟶ Y)
  [IsOpenImmersion i] [IsOpenImmersion j] (f : X ⟶ S) (g : Y ⟶ S)
  (h : i ≫ f = j ≫ g)

/-- For open immersions `i : U ⟶ X`, `j : U ⟶ Y` over `S` with `f`, `g` separated,
the glued morphism `pushout.desc f g h` is separated if and only if
`pullback.lift i j h : U ⟶ X ×_S Y` is a closed immersion. -/
theorem IsSeparated.pushout_desc_iff [IsSeparated f] [IsSeparated g] :
    IsSeparated (pushout.desc f g h) ↔ IsClosedImmersion (pullback.lift i j h) := by
  let p := pushout.desc f g h
  -- Identify the overlap with the intersection of the charts in the glued scheme.
  have he : (Scheme.isPullback_pushout_of_isOpenImmersion i j).isoPullback.hom ≫
      pullback.mapDesc (pushout.inl i j) (pushout.inr i j) p =
        pullback.lift i j h ≫ (pullback.congrHom (pushout.inl_desc f g h)
          (pushout.inr_desc f g h)).inv := by
    ext <;> simp [p]
  have hclosed : IsClosedImmersion (pullback.lift i j h) ↔
      IsClosedImmersion (pullback.mapDesc (pushout.inl i j) (pushout.inr i j) p) := by
    rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion
      _ (pullback.congrHom (pushout.inl_desc f g h) (pushout.inr_desc f g h)).inv,
      ← he, MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion]
  constructor
  · intro hp
    have : IsSeparated p := hp
    exact hclosed.mpr (MorphismProperty.of_isPullback
      (pullback_map_diagonal_isPullback (pushout.inl i j) (pushout.inr i j) p)
      (inferInstance : IsClosedImmersion (pullback.diagonal p)))
  · intro hc
    have hc' := hclosed.mp hc
    let 𝒰 := Scheme.pushoutOpenCover i j
    have hfalse : 𝒰.f false ≫ p = f := pushout.inl_desc f g h
    have htrue : 𝒰.f true ≫ p = g := pushout.inr_desc f g h
    have : ∀ b, IsSeparated (𝒰.f b ≫ p) := by
      rintro (_ | _)
      · exact hfalse.symm ▸ (inferInstance : IsSeparated f)
      · exact htrue.symm ▸ (inferInstance : IsSeparated g)
    refine IsSeparated.of_openCover p 𝒰 ?_
    rintro (_ | _) (_ | _) hne
    · exact (hne rfl).elim
    · exact hc'
    · -- Reversing the two charts conjugates the overlap map by the two product symmetries.
      have he' : (pullbackSymmetry (pushout.inl i j) (pushout.inr i j)).hom ≫
          pullback.mapDesc (pushout.inr i j) (pushout.inl i j) p =
            pullback.mapDesc (pushout.inl i j) (pushout.inr i j) p ≫
              (pullbackSymmetry _ _).hom := by
        ext <;> simp
      have : IsClosedImmersion (pullback.mapDesc (pushout.inr i j) (pushout.inl i j) p) := by
        rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
          (pullbackSymmetry (pushout.inl i j) (pushout.inr i j)).hom, he']
        infer_instance
      exact this
    · exact (hne rfl).elim

/-- A property local at the source passes to a morphism glued from two open pieces. -/
theorem IsZariskiLocalAtSource.pushout_desc {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtSource P] (hf : P f) (hg : P g) : P (pushout.desc f g h) := by
  refine IsZariskiLocalAtSource.of_openCover (P := P)
    (f := pushout.desc f g h) (Scheme.pushoutOpenCover i j) ?_
  rintro (_ | _)
  · exact (pushout.inl_desc f g h).symm ▸ hf
  · exact (pushout.inr_desc f g h).symm ▸ hg

/-- Local finite type passes to the morphism glued from two open pieces. -/
theorem LocallyOfFiniteType.pushout_desc [LocallyOfFiniteType f] [LocallyOfFiniteType g] :
    LocallyOfFiniteType (pushout.desc f g h) := by
  -- Instance search does not find this source-local instance through `HasRingHomProperty`.
  let : IsZariskiLocalAtSource @LocallyOfFiniteType :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  exact IsZariskiLocalAtSource.pushout_desc i j f g h inferInstance inferInstance

/-- Quasi-compactness passes to the morphism glued from two open pieces. -/
theorem QuasiCompact.pushout_desc [QuasiCompact f] [QuasiCompact g] :
    QuasiCompact (pushout.desc f g h) := by
  let 𝒰 := Scheme.pushoutOpenCover i j
  refine QuasiCompact.of_openCover (pushout.desc f g h) 𝒰 ?_
  rintro (_ | _)
  · exact (pushout.inl_desc f g h).symm ▸ (inferInstance : QuasiCompact f)
  · exact (pushout.inr_desc f g h).symm ▸ (inferInstance : QuasiCompact g)

end AlgebraicGeometry
