/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.SplitEpi
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Base change of a section of a scheme morphism

A section of `f : X ⟶ S` induces a section on each base change `T ×_S X`. The projection
formulas and naturality in `T` follow from pullback of split epimorphisms and symmetry of
pullbacks.
-/

public section

open CategoryTheory Limits

namespace TauCeti
namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S) (x₀ : S ⟶ X) (hx₀ : x₀ ≫ f = 𝟙 S)

/-- The base change `x₀_T : T ⟶ T ×_S X` of a section `x₀` of `f : X ⟶ S` to a scheme `T` over
`S`. -/
def baseChangeSection (T : Over S) : T.left ⟶ pullback T.hom f :=
  ((⟨x₀, hx₀⟩ : SplitEpi f).pullback T.hom).section_ ≫
    (pullbackSymmetry f T.hom).hom

/-- The base-changed section is a section of the projection `T ×_S X ⟶ T`. -/
@[reassoc (attr := simp)]
lemma baseChangeSection_fst (T : Over S) :
    baseChangeSection f x₀ hx₀ T ≫ pullback.fst T.hom f = 𝟙 T.left :=
  by simp [baseChangeSection, Category.assoc]

/-- The base-changed section followed by the projection to `X` is `T ⟶ S ⟶ X`. -/
@[reassoc (attr := simp)]
lemma baseChangeSection_snd (T : Over S) :
    baseChangeSection f x₀ hx₀ T ≫ pullback.snd T.hom f = T.hom ≫ x₀ :=
  by simp [baseChangeSection, Category.assoc]

/-- The base-changed sections are compatible with the morphisms `T' ×_S X ⟶ T ×_S X` induced by
morphisms `T' ⟶ T` over `S`. -/
@[reassoc]
lemma baseChangeSection_comp_pullback_map {T' T : Over S} (φ : T' ⟶ T) :
    baseChangeSection f x₀ hx₀ T' ≫
        ((Over.pullback f).map φ).left =
      φ.left ≫ baseChangeSection f x₀ hx₀ T := by
  let h : SplitEpi f := ⟨x₀, hx₀⟩
  have hcomm : (pullbackSymmetry f T'.hom).hom ≫ ((Over.pullback f).map φ).left =
      pullback.map f T'.hom f T.hom (𝟙 X) φ.left (𝟙 S) (by simp)
        (by simp [Over.w φ]) ≫ (pullbackSymmetry f T.hom).hom := by
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left]
      rw [pullback.map]
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullbackSymmetry_hom_comp_fst]
      rw [← Category.assoc, pullbackSymmetry_hom_comp_fst]
    · simp only [Over.pullback_map_left]
      rw [pullback.map]
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullbackSymmetry_hom_comp_snd]
      simp
  have hsection : (h.pullback T'.hom).section_ ≫
      pullback.map f T'.hom f T.hom (𝟙 X) φ.left (𝟙 S) (by simp)
        (by simp [Over.w φ]) = φ.left ≫ (h.pullback T.hom).section_ := by
    exact h.pullback_section_map_of_eq T.hom T'.hom φ.left (Over.w φ)
  simp only [baseChangeSection, hcomm, Category.assoc]
  exact congrArg (· ≫ (pullbackSymmetry f T.hom).hom) hsection

end

end AlgebraicGeometry
end TauCeti
