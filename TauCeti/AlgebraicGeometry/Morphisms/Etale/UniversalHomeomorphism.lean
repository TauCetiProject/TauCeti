/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import TauCeti.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Universal homeomorphisms lift against étale morphisms

Let `g : U' ⟶ U` be a universal homeomorphism and `p : W ⟶ V` an étale morphism. Every
commutative square from `g` to `p` has a unique diagonal filler: universal homeomorphisms have the
unique left lifting property with respect to étale morphisms. Uniqueness holds because `g` is
surjective and `p` is unramified (`AlgebraicGeometry.ext_of_surjective_of_formallyUnramified`).
For existence, a section `σ : U' ⟶ W` of `p` over `g` has open image: its graph is a section of
the étale base change `W ×_U U' ⟶ U'`, hence an open immersion, and `W ×_U U' ⟶ W` is a
homeomorphism. The open subscheme `O ⊆ W` cut out by this image is étale, surjective and
universally injective over `U`, hence isomorphic to `U`, and its inverse is the lift.

Consequently, for a universal homeomorphism `f : X ⟶ Y`, base change along `f` is bijective on
morphisms of `Y`-schemes into an étale `Y`-scheme. The resulting full faithfulness of base change
on small étale sites is in `TauCeti.AlgebraicGeometry.Sites.Etale.TopologicalInvariance`.

## Main results

* `TauCeti.AlgebraicGeometry.IsUniversalHomeomorphism.hasLiftingProperty_of_etale`:
  universal homeomorphisms have the left lifting property with respect to étale morphisms.
* `TauCeti.AlgebraicGeometry.IsUniversalHomeomorphism.overPullback_map_bijective`: base change
  along a universal homeomorphism is bijective on morphisms into an étale scheme.

## References

* The Stacks Project, [Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ), topological
  invariance of the small étale site.
-/

public section

open CategoryTheory Limits MorphismProperty

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {U U' V W : Scheme.{u}}

/-- A morphism `σ : U' ⟶ W` over a universal homeomorphism `g : U' ⟶ U` into an étale `U`-scheme
`W` extends to a section of `W ⟶ U`. This is the case `V = U` of
`IsUniversalHomeomorphism.hasLiftingProperty_of_etale`. -/
private theorem exists_section_of_isUniversalHomeomorphism (p : W ⟶ U) [Etale p] (g : U' ⟶ U)
    [IsUniversalHomeomorphism g] (σ : U' ⟶ W) (hσ : σ ≫ p = g) :
    ∃ s : U ⟶ W, s ≫ p = 𝟙 U ∧ g ≫ s = σ := by
  -- the graph of `σ` is a section of the étale base change of `p`, so an open immersion
  let σ' : U' ⟶ pullback p g := pullback.lift σ (𝟙 U') (by simp [hσ])
  have hσ'snd : σ' ≫ pullback.snd p g = 𝟙 U' := pullback.lift_snd _ _ _
  have : IsSplitMono σ' := ⟨⟨⟨pullback.snd p g, hσ'snd⟩⟩⟩
  have : Etale (σ' ≫ pullback.snd p g) := by rw [hσ'snd]; infer_instance
  have : Etale σ' := Etale.of_comp σ' (pullback.snd p g)
  have : IsOpenImmersion σ' := IsOpenImmersion.of_etale_of_universallyInjective σ'
  -- the image of `σ` is open, as `pullback p g ⟶ W` is a homeomorphism
  have hσfst : σ' ≫ pullback.fst p g = σ := pullback.lift_fst _ _ _
  have hopen : IsOpen (Set.range σ) := by
    rw [← hσfst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact (IsUniversalHomeomorphism.isHomeomorph (pullback.fst p g)).isOpenMap _
      σ'.isOpenEmbedding.isOpen_range
  -- the open subscheme `O` cut out by the image of `σ` is isomorphic to `U`
  let O : W.Opens := ⟨Set.range σ, hopen⟩
  let σO : U' ⟶ O := IsOpenImmersion.lift O.ι σ (by simp [O])
  have hσO : σO ≫ O.ι = σ := IsOpenImmersion.lift_fac _ _ _
  have : Surjective σO := by
    refine ⟨fun x ↦ ?_⟩
    have hx : O.ι x ∈ Set.range O.ι := ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, O.ι.isOpenEmbedding.injective (by rw [← Scheme.Hom.comp_apply, hσO, hy])⟩
  have hq : σO ≫ O.ι ≫ p = g := by rw [reassoc_of% hσO, hσ]
  have : Surjective (σO ≫ O.ι ≫ p) := by rw [hq]; infer_instance
  have : Surjective (O.ι ≫ p) := Surjective.of_comp σO _
  have : UniversallyInjective (σO ≫ O.ι ≫ p) := by rw [hq]; infer_instance
  have : UniversallyInjective (O.ι ≫ p) := UniversallyInjective.of_comp_surjective σO _
  have : IsIso (O.ι ≫ p) := isIso_of_etale_of_universallyInjective_of_surjective _
  refine ⟨inv (O.ι ≫ p) ≫ O.ι, by simp, ?_⟩
  rw [← hσO, ← hq]
  simp

/-- **Universal homeomorphisms lift against étale morphisms.** Every commutative square from a
universal homeomorphism to an étale morphism has a diagonal filler. The filler is unique by
`AlgebraicGeometry.ext_of_surjective_of_formallyUnramified`. -/
instance IsUniversalHomeomorphism.hasLiftingProperty_of_etale (g : U' ⟶ U)
    [IsUniversalHomeomorphism g] (p : W ⟶ V) [Etale p] : HasLiftingProperty g p where
  sq_hasLift {σ t} sq := by
    obtain ⟨s, hs, hgs⟩ := exists_section_of_isUniversalHomeomorphism (pullback.snd p t) g
      (pullback.lift σ g sq.w) (pullback.lift_snd _ _ _)
    refine .mk' ⟨s ≫ pullback.fst p t, ?_, ?_⟩
    · rw [reassoc_of% hgs, pullback.lift_fst]
    · rw [Category.assoc, pullback.condition, reassoc_of% hs]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsUniversalHomeomorphism f]

/-- Base change along a universal homeomorphism `f : X ⟶ Y` is bijective on morphisms of schemes
over `Y` whose target is étale over `Y`. -/
theorem IsUniversalHomeomorphism.overPullback_map_bijective {A B : Over Y} [Etale B.hom] :
    Function.Bijective ((Over.pullback f).map : (A ⟶ B) → _) := by
  refine ⟨fun a b h ↦ ?_, fun c ↦ ?_⟩
  · ext1
    refine ext_of_surjective_of_formallyUnramified B.hom (by simp) (pullback.fst A.hom f) ?_
    simpa using congrArg (fun k ↦ k.left ≫ pullback.fst B.hom f) h
  · have hc : c.left ≫ pullback.snd B.hom f = pullback.snd A.hom f := by simpa using Over.w c
    have sq : CommSq (c.left ≫ pullback.fst B.hom f) (pullback.fst A.hom f) B.hom A.hom :=
      ⟨by simp [pullback.condition, reassoc_of% hc]⟩
    refine ⟨Over.homMk sq.lift sq.fac_right, ?_⟩
    ext1
    apply pullback.hom_ext <;> simp [hc]

end TauCeti.AlgebraicGeometry
