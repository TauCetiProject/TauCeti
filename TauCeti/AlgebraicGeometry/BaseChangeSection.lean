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

More generally, a `T`-point `x : T ⟶ X` of `X` over `S` has a graph `T ⟶ T ×_S X`, a section of
the projection `T ×_S X ⟶ T` (`graphSection`). Graphs commute with base change along morphisms
`T' ⟶ T` over `S`, and form pullback squares with the induced morphisms
`T' ×_S X ⟶ T ×_S X` (`isPullback_graphSection`). The base change of a section `x₀` of `f` is
the graph of the `T`-point `T ⟶ S ⟶ X` (`graphSection_basePoint`).
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

variable {f}

/-- The **graph** `T ⟶ T ×_S X` of a `T`-point `x : T ⟶ X` of `X` over `S`: the section of the
projection `T ×_S X ⟶ T` whose second component is `x`. -/
def graphSection {T : Over S} (x : T ⟶ Over.mk f) : T.left ⟶ pullback T.hom f :=
  pullback.lift (𝟙 T.left) x.left (by simpa using (Over.w x).symm)

/-- The graph of a `T`-point is a section of the projection `T ×_S X ⟶ T`. -/
@[reassoc (attr := simp)]
lemma graphSection_fst {T : Over S} (x : T ⟶ Over.mk f) :
    graphSection x ≫ pullback.fst T.hom f = 𝟙 T.left :=
  pullback.lift_fst _ _ _

/-- The second component of the graph of a `T`-point `x` is `x` itself. -/
@[reassoc (attr := simp)]
lemma graphSection_snd {T : Over S} (x : T ⟶ Over.mk f) :
    graphSection x ≫ pullback.snd T.hom f = x.left :=
  pullback.lift_snd _ _ _

/-- Graphs commute with base change: the graph of `φ ≫ x` followed by the induced morphism
`T' ×_S X ⟶ T ×_S X` is `φ` followed by the graph of `x`. -/
@[reassoc]
lemma graphSection_comp_pullback_map {T' T : Over S} (φ : T' ⟶ T) (x : T ⟶ Over.mk f) :
    graphSection (φ ≫ x) ≫ ((Over.pullback f).map φ).left = φ.left ≫ graphSection x := by
  apply pullback.hom_ext <;> simp

/-- The graph of a `T`-point `x` and the graph of its base change `φ ≫ x` along `φ : T' ⟶ T` form
a pullback square with the induced morphism `T' ×_S X ⟶ T ×_S X`. -/
lemma isPullback_graphSection {T' T : Over S} (φ : T' ⟶ T) (x : T ⟶ Over.mk f) :
    IsPullback (graphSection (φ ≫ x)) φ.left ((Over.pullback f).map φ).left
      (graphSection x) := by
  -- The square formed by `T' ×_S X ⟶ T ×_S X` and the two projections is a pullback square;
  -- pasting with it gives a square whose horizontal composites are identities.
  have h : IsPullback ((Over.pullback f).map φ).left (pullback.fst T'.hom f)
      (pullback.fst T.hom f) φ.left := by
    refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback T.hom f).flip
    simpa using (IsPullback.of_hasPullback T'.hom f).flip
  refine IsPullback.of_right ?_ (graphSection_comp_pullback_map φ x) h.flip
  rw [graphSection_fst, graphSection_fst]
  exact IsPullback.id_horiz φ.left

variable {x₀}

/-- The `T`-point `T ⟶ S ⟶ X` of `X` over `S` given by a section `x₀` of `f`. -/
def basePoint (T : Over S) : T ⟶ Over.mk f :=
  Over.homMk (T.hom ≫ x₀) (by simp [hx₀])

/-- The underlying morphism of the base point is `T ⟶ S ⟶ X`. -/
@[simp]
lemma basePoint_left (T : Over S) : (basePoint hx₀ T).left = T.hom ≫ x₀ :=
  (rfl)

/-- The base points are compatible with morphisms over `S`. -/
@[reassoc (attr := simp)]
lemma comp_basePoint {T' T : Over S} (φ : T' ⟶ T) : φ ≫ basePoint hx₀ T = basePoint hx₀ T' := by
  ext
  simp [Over.w_assoc φ]

/-- The graph of the base point is the base change `x₀_T : T ⟶ T ×_S X` of the section `x₀`. -/
@[simp]
lemma graphSection_basePoint (T : Over S) :
    graphSection (basePoint hx₀ T) = baseChangeSection f x₀ hx₀ T := by
  apply pullback.hom_ext <;> simp

end

end AlgebraicGeometry
end TauCeti
