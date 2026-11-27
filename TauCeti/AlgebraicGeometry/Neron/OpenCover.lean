/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.AlgebraicGeometry.Neron.BaseChange

/-!
# The Néron mapping property is local on the base

Let `j : η ⟶ S` be a morphism of schemes and `𝒰` an open cover of `S`, and let
`j' i : η' i ⟶ 𝒰.X i` be the base change of `j` to the `i`-th member of `𝒰`. If, for every `i`,
the restriction `X ×_S 𝒰.X i` of an `S`-scheme `X` has the mapping property relative to `j' i`,
then `X` has the mapping property relative to `j`. This holds for every class `P` of test
morphisms which is stable under base change and under precomposition with open immersions, in
particular for smooth test morphisms. Since smooth base change restricts the Néron mapping
property to open subschemes of the base, the Néron mapping property of `X` is equivalent to that
of all its restrictions to the members of an open cover.

This is how the Néron mapping property of a model glued from local pieces is verified: over a
Dedekind scheme, Néron models over the local rings at the finitely many closed points of bad
reduction and an abelian scheme over a dense open subscheme are spread out to an open cover of
the base and glued, and the glued scheme has the mapping property because each of its
restrictions does.

## Main results

* `TauCeti.AlgebraicGeometry.Neron.MappingProperty.of_openCover`: the mapping property for a
  class of test morphisms stable under base change and under precomposition with open immersions
  holds as soon as it holds on the members of an open cover of the base.
* `TauCeti.AlgebraicGeometry.Neron.neronMappingProperty_iff_of_openCover`: the Néron mapping
  property holds exactly when it holds on every member of an open cover of the base.

## References

* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 21, Springer, 1990, §1.2, Definition 1, and §1.4, Proposition 1.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Neron

universe v u

variable {η S : Scheme.{u}} {j : η ⟶ S} {𝒰 : S.OpenCover.{v}} {η' : 𝒰.I₀ → Scheme.{u}}
  {j' : ∀ i, η' i ⟶ 𝒰.X i} {g' : ∀ i, η' i ⟶ η}

/-- The pullback of an open cover `𝒰` of `S` along `f : T ⟶ S`, as an open cover of `T` indexed
by `𝒰.I₀` itself. This is Mathlib's `Scheme.Cover.pullback₁` with its members exposed reducibly,
so that a member of `𝒰` and the corresponding member of the pullback share their index without
unfolding `pullback₁`. -/
private abbrev pullbackCover (𝒰 : S.OpenCover.{v}) {T : Scheme.{u}} (f : T ⟶ S) :
    T.OpenCover.{v} where
  I₀ := 𝒰.I₀
  X i := pullback f (𝒰.f i)
  f i := pullback.fst f (𝒰.f i)
  mem₀ := (𝒰.pullback₁ f).mem₀

/-- Two `S`-morphisms out of an `S`-scheme `Y` agree once they agree on the restrictions
`Y ×_S 𝒰.X i ⟶ Y` of `Y` to the members of an open cover of `S`. -/
private theorem hom_ext_of_counit (𝒰 : S.OpenCover.{v}) {Y T : Over S} {f₁ f₂ : Y ⟶ T}
    (h : ∀ i, (Over.mapPullbackAdj (𝒰.f i)).counit.app Y ≫ f₁ =
      (Over.mapPullbackAdj (𝒰.f i)).counit.app Y ≫ f₂) : f₁ = f₂ := by
  ext1
  exact Scheme.Cover.hom_ext (pullbackCover 𝒰 Y.hom) _ _ fun i ↦ by simpa using congr($(h i).left)

/-- Two `η`-morphisms out of the base change `Y ×_S η` of an `S`-scheme `Y` along `j` agree once
they agree on the base changes along `j` of the restrictions of `Y` to the members of an open
cover of `S`. -/
private theorem pullback_hom_ext_of_counit (𝒰 : S.OpenCover.{v}) (j : η ⟶ S) {Y : Over S}
    {T : Over η} {φ₁ φ₂ : (Over.pullback j).obj Y ⟶ T}
    (h : ∀ i, (Over.pullback j).map ((Over.mapPullbackAdj (𝒰.f i)).counit.app Y) ≫ φ₁ =
      (Over.pullback j).map ((Over.mapPullbackAdj (𝒰.f i)).counit.app Y) ≫ φ₂) : φ₁ = φ₂ := by
  let 𝒱 := pullbackCover 𝒰 Y.hom
  let 𝒲 := pullbackCover 𝒱 (pullback.fst Y.hom j)
  ext1
  refine Scheme.Cover.hom_ext 𝒲 _ _ fun i ↦ ?_
  -- The `i`-th member of `𝒲` factors through the base change of the `i`-th restriction of `Y`.
  obtain ⟨m, hm⟩ : ∃ m, m ≫
      ((Over.pullback j).map ((Over.mapPullbackAdj (𝒰.f i)).counit.app Y)).left = 𝒲.f i :=
    ⟨pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ pullback.snd Y.hom j) (by
      dsimp
      rw [Category.assoc, ← pullback.condition, ← pullback.condition]
      exact (pullback.condition_assoc (f := pullback.fst Y.hom j) (g := 𝒱.f i) Y.hom).symm), by
      apply pullback.hom_ext <;> simp [𝒲, 𝒱, pullback.condition]⟩
  rw [← hm, Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, h i]

namespace MappingProperty

variable {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
  [P.RespectsLeft @IsOpenImmersion]

/-- Let `Y` be an `S`-scheme with structure morphism in `P`, and suppose that restriction along
`j` is injective on `S`-morphisms into `X` from every `P`-scheme over the member `𝒰.X i` of an
open cover of `S`. Then extensions to `Y ×_S 𝒰.X i` and to `Y ×_S 𝒰.X k` of the restrictions of
one morphism `φ : Y ×_S η ⟶ X ×_S η` agree on the overlap of the two restrictions of `Y`. -/
private theorem pullback_fst_comp_left_eq_pullback_snd_comp_left {X Y : Over S} (hY : P Y.hom)
    {i k : 𝒰.I₀} (hinj : ∀ Z : Over (𝒰.X i), P Z.hom →
      Function.Injective ((Over.pullback j).map : ((Over.map (𝒰.f i)).obj Z ⟶ X) → _))
    {φ : (Over.pullback j).obj Y ⟶ (Over.pullback j).obj X}
    {ψi : (Over.map (𝒰.f i)).obj ((Over.pullback (𝒰.f i)).obj Y) ⟶ X}
    {ψk : (Over.map (𝒰.f k)).obj ((Over.pullback (𝒰.f k)).obj Y) ⟶ X}
    (hψi : (Over.pullback j).map ψi =
      (Over.pullback j).map ((Over.mapPullbackAdj (𝒰.f i)).counit.app Y) ≫ φ)
    (hψk : (Over.pullback j).map ψk =
      (Over.pullback j).map ((Over.mapPullbackAdj (𝒰.f k)).counit.app Y) ≫ φ) :
    pullback.fst ((pullbackCover 𝒰 Y.hom).f i) ((pullbackCover 𝒰 Y.hom).f k) ≫ ψi.left =
      pullback.snd ((pullbackCover 𝒰 Y.hom).f i) ((pullbackCover 𝒰 Y.hom).f k) ≫ ψk.left := by
  let 𝒱 := pullbackCover 𝒰 Y.hom
  -- The overlap, as a `P`-scheme over `𝒰.X i`, with its two maps to the restrictions of `Y`.
  let W : Over (𝒰.X i) :=
    Over.mk (pullback.fst (𝒱.f i) (𝒱.f k) ≫ ((Over.pullback (𝒰.f i)).obj Y).hom)
  have hW : P W.hom := MorphismProperty.RespectsLeft.precomp (Q := @IsOpenImmersion) _
    (MorphismProperty.pullback_fst _ _ (𝒱.map_prop k)) _ (P.pullback_snd _ _ hY)
  let α : (Over.map (𝒰.f i)).obj W ⟶ (Over.map (𝒰.f i)).obj ((Over.pullback (𝒰.f i)).obj Y) :=
    Over.homMk (pullback.fst (𝒱.f i) (𝒱.f k))
  let β : (Over.map (𝒰.f i)).obj W ⟶ (Over.map (𝒰.f k)).obj ((Over.pullback (𝒰.f k)).obj Y) :=
    Over.homMk (pullback.snd (𝒱.f i) (𝒱.f k)) (by
      dsimp [W]
      rw [Category.assoc, ← pullback.condition, ← pullback.condition]
      exact (pullback.condition_assoc (f := 𝒱.f i) (g := 𝒱.f k) Y.hom).symm)
  have hαβ : α ≫ (Over.mapPullbackAdj (𝒰.f i)).counit.app Y =
      β ≫ (Over.mapPullbackAdj (𝒰.f k)).counit.app Y := by
    ext1
    simpa [α, β] using pullback.condition
  -- Both composites extend the same morphism from the base change of the overlap.
  have : α ≫ ψi = β ≫ ψk := by
    refine hinj W hW ?_
    simp only [Functor.map_comp, hψi, hψk, ← Functor.map_comp_assoc, hαβ]
  exact congr($(this).left)

/-- The mapping property for a class `P` of test morphisms which is stable under base change and
under precomposition with open immersions holds for `X` as soon as it holds for the restrictions
`X ×_S 𝒰.X i` of `X` to the members of an open cover `𝒰` of `S`, relative to the base changes
`j' i` of `j` (Bosch–Lütkebohmert–Raynaud, *Néron Models*, §1.4, Proposition 1). -/
theorem of_openCover (sq : ∀ i, IsPullback (j' i) (g' i) (𝒰.f i) j) {X : Over S}
    (h : ∀ i, MappingProperty P (j' i) ((Over.pullback (𝒰.f i)).obj X)) :
    MappingProperty P j X where
  bijective Y hY := by
    -- Restriction along `j` is bijective for every test object over a member of the cover.
    have hloc (i : 𝒰.I₀) (Z : Over (𝒰.X i)) (hZ : P Z.hom) :=
      (bijective_pullback_map_iff_of_isPullback (sq i) X Z).1 ((h i).bijective Z hZ)
    have hY' (i : 𝒰.I₀) : P ((Over.pullback (𝒰.f i)).obj Y).hom := P.pullback_snd _ _ hY
    refine ⟨fun f₁ f₂ hf ↦ hom_ext_of_counit 𝒰 fun i ↦ (hloc i _ (hY' i)).1 ?_, fun φ ↦ ?_⟩
    · simp only [Functor.map_comp, hf]
    -- Extend `φ` on each restriction of `Y`, and glue the extensions.
    choose ψ hψ using fun i ↦ (hloc i _ (hY' i)).2
      ((Over.pullback j).map ((Over.mapPullbackAdj (𝒰.f i)).counit.app Y) ≫ φ)
    let 𝒱 := pullbackCover 𝒰 Y.hom
    have compat (i k : 𝒰.I₀) := pullback_fst_comp_left_eq_pullback_snd_comp_left hY
      (fun Z hZ ↦ (hloc i Z hZ).1) (hψ i) (hψ k)
    let G : Y ⟶ X := Over.homMk (Scheme.Cover.glueMorphisms 𝒱 (fun i ↦ (ψ i).left) compat)
      (Scheme.Cover.hom_ext 𝒱 _ _ fun i ↦ by
        rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms 𝒱 _ compat i]
        exact (Over.w (ψ i)).trans pullback.condition.symm)
    have hG (i : 𝒰.I₀) : (Over.mapPullbackAdj (𝒰.f i)).counit.app Y ≫ G = ψ i := by
      ext1
      simp only [Over.comp_left, Over.mapPullbackAdj_counit_app, Over.homMk_left, G]
      exact Scheme.Cover.ι_glueMorphisms 𝒱 _ compat i
    exact ⟨G, pullback_hom_ext_of_counit 𝒰 j fun i ↦ by rw [← Functor.map_comp, hG, hψ i]⟩

end MappingProperty

/-- The Néron mapping property is local on the base: an `S`-scheme `X` has the Néron mapping
property relative to `j` exactly when, for every member `𝒰.X i` of an open cover of `S`, its
restriction `X ×_S 𝒰.X i` has the Néron mapping property relative to the base change `j' i` of
`j`. -/
theorem neronMappingProperty_iff_of_openCover (sq : ∀ i, IsPullback (j' i) (g' i) (𝒰.f i) j)
    {X : Over S} :
    NeronMappingProperty j X ↔
      ∀ i, NeronMappingProperty (j' i) ((Over.pullback (𝒰.f i)).obj X) := by
  -- Instance search does not find `RespectsLeft` from Mathlib's `Respects` instance for
  -- `@Smooth`, whose implicit binders differ from those of `MorphismProperty`.
  have : MorphismProperty.RespectsLeft @Smooth @IsOpenImmersion :=
    MorphismProperty.Respects.toRespectsLeft
  exact ⟨fun h i ↦ h.pullback (sq i), MappingProperty.of_openCover sq⟩

end TauCeti.AlgebraicGeometry.Neron
