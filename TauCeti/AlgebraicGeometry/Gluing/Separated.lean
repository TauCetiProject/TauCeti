/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

/-- Gluing separated schemes along an open gives a separated scheme precisely when the
overlap is a closed subscheme of the product over the base. -/
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
    let 𝒰 : (pushout i j).OpenCover := Scheme.Cover.mkOfCovers Bool
      (fun b ↦ if b then Y else X)
      (fun b ↦ match b with | false => pushout.inl i j | true => pushout.inr i j)
      (fun z ↦ by
        rcases (Set.ext_iff.mp (Scheme.range_pushout_inl_union_range_pushout_inr i j) z).mpr
          trivial with ⟨x, rfl⟩ | ⟨y, rfl⟩
        exacts [⟨false, x, rfl⟩, ⟨true, y, rfl⟩])
      (fun b ↦ by cases b <;> infer_instance)
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

/-- Local finite type passes to the morphism glued from two open pieces. -/
theorem LocallyOfFiniteType.pushout_desc [LocallyOfFiniteType f] [LocallyOfFiniteType g] :
    LocallyOfFiniteType (pushout.desc f g h) := by
  let : IsZariskiLocalAtSource @LocallyOfFiniteType :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (f := pushout.desc f g h) (Scheme.IsLocallyDirected.openCover (span i j)) ?_
  rintro (_ | _ | _)
  · -- The apex inclusion factors through the left chart.
    have he : colimit.ι (span i j) WalkingSpan.zero ≫ pushout.desc f g h = i ≫ f := by
      rw [← colimit.w (span i j) (WalkingSpan.Hom.fst), Category.assoc, pushout.inl_desc]
      rfl
    exact he.symm ▸ (inferInstance : LocallyOfFiniteType (i ≫ f))
  · exact (pushout.inl_desc f g h).symm ▸ (inferInstance : LocallyOfFiniteType f)
  · exact (pushout.inr_desc f g h).symm ▸ (inferInstance : LocallyOfFiniteType g)

/-- Quasi-compactness passes to the morphism glued from two open pieces. In particular the
gluing of two finite-type morphisms is finite type, with no condition on the base. -/
theorem QuasiCompact.pushout_desc [QuasiCompact f] [QuasiCompact g] :
    QuasiCompact (pushout.desc f g h) := by
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro V hV
  have he : (pushout.desc f g h) ⁻¹' (V : Set S) =
      (pushout.inl i j) '' (f ⁻¹' (V : Set S)) ∪
        (pushout.inr i j) '' (g ⁻¹' (V : Set S)) := by
    ext z
    constructor
    · intro hz
      rcases (Set.ext_iff.mp (Scheme.range_pushout_inl_union_range_pushout_inr i j) z).mpr
          trivial with ⟨x, rfl⟩ | ⟨y, rfl⟩
      · exact Or.inl ⟨x, by simpa [← Scheme.Hom.comp_apply] using hz, rfl⟩
      · exact Or.inr ⟨y, by simpa [← Scheme.Hom.comp_apply] using hz, rfl⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
      · simpa [← Scheme.Hom.comp_apply] using hx
      · simpa [← Scheme.Hom.comp_apply] using hy
  simp only [Scheme.Hom.coe_preimage]
  rw [he]
  exact ((QuasiCompact.isCompact_preimage (f := f) V V.isOpen hV.isCompact).image
    (pushout.inl i j).continuous).union
      ((QuasiCompact.isCompact_preimage (f := g) V V.isOpen hV.isCompact).image
        (pushout.inr i j).continuous)

end AlgebraicGeometry
