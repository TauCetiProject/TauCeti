/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.Injective
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality
import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Basic

/-!
# Schematic density and separated targets

Morphisms over a base into a separated scheme are determined by their restriction along a
scheme-theoretically dominant morphism. Unlike the corresponding statement for topologically
dominant morphisms, this requires no reducedness hypothesis on the source. In particular, it
applies to flat models with a possibly nonreduced generic fibre.

The equalizer argument extends Mathlib's
`AlgebraicGeometry.ext_of_isDominant_of_isSeparated`, by Christian Merten and Andrew Yang:
schematic density makes the closed equalizer the entire source as a scheme, not just as a space.

The file also gives criteria for scheme-theoretic dominance. A morphism to an affine scheme is
scheme-theoretically dominant exactly when it is injective on global sections
(`AlgebraicGeometry.isSchemeTheoreticallyDominant_iff_appTop_injective`); in particular, `Spec` of
a ring homomorphism is scheme-theoretically dominant exactly when the homomorphism is injective
(`AlgebraicGeometry.isSchemeTheoreticallyDominant_SpecMap_iff`). A morphism is scheme-theoretically
dominant if its base change to each member of an open cover of the target is
(`AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_openCover`), and a quasi-compact
scheme-theoretically dominant morphism stays so after corestriction along an open immersion
containing its image
(`AlgebraicGeometry.IsOpenImmersion.isSchemeTheoreticallyDominant_lift`). The scheme-theoretic
image of a scheme-theoretically dominant morphism is its whole target
(`AlgebraicGeometry.IsSchemeTheoreticallyDominant.isIso_imageι`).

A flat surjective morphism is scheme-theoretically dominant
(`AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_flat_of_surjective`), and so are all its base
changes (`AlgebraicGeometry.IsSchemeTheoreticallyDominant.universally_of_flat_of_surjective`). The
proof is stalkwise: a flat local homomorphism of stalks is faithfully flat, and extension of ideals
along a faithfully flat ring map is injective.

For a commutative square whose side `p` is scheme-theoretically dominant, factorization through a
closed subscheme can be checked after precomposition with `p`
(`AlgebraicGeometry.Scheme.IdealSheafData.comap_le_ker_iff_of_isSchemeTheoreticallyDominant`). In
particular an ideal sheaf vanishes exactly when its inverse image along a scheme-theoretically
dominant morphism does
(`AlgebraicGeometry.Scheme.IdealSheafData.comap_eq_bot_iff_of_isSchemeTheoreticallyDominant`).
If moreover every base change of `g` is scheme-theoretically dominant, then taking inverse images
along `g` reflects inclusion of ideal sheaves
(`comap_le_comap_iff_of_universally_isSchemeTheoreticallyDominant` in the namespace
`AlgebraicGeometry.Scheme.IdealSheafData`), so it is injective. This is how equalities of closed
subschemes descend along flat surjective morphisms, see
`TauCeti.AlgebraicGeometry.IdealSheaf.FaithfullyFlat`.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

universe u

variable {W X Y S : Scheme.{u}}

/-- If a composite is scheme-theoretically dominant, so is its second factor. -/
theorem _root_.AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_comp
    (f : W ⟶ X) (g : X ⟶ Y) [IsSchemeTheoreticallyDominant (f ≫ g)] :
    IsSchemeTheoreticallyDominant g := by
  constructor
  exact eq_bot_iff.mpr ((Scheme.Hom.le_ker_comp f g).trans (f ≫ g).ker_eq_bot.le)

/-- Precomposition with a scheme-theoretically dominant morphism does not change the kernel. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant
    (f : W ⟶ X) [IsSchemeTheoreticallyDominant f] (g : X ⟶ Y) : (f ≫ g).ker = g.ker := by
  rw [Scheme.Hom.ker_comp, f.ker_eq_bot, Scheme.IdealSheafData.map_bot]

/-- The scheme-theoretic image of a scheme-theoretically dominant morphism is the whole target. -/
instance _root_.AlgebraicGeometry.IsSchemeTheoreticallyDominant.isIso_imageι (f : X ⟶ Y)
    [IsSchemeTheoreticallyDominant f] : IsIso f.imageι :=
  IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
    ((Scheme.IdealSheafData.ker_subschemeι _).trans f.ker_eq_bot)

/-- Two morphisms into a separated scheme over a base agree if they agree after precomposition
with a scheme-theoretically dominant morphism. The source need not be reduced. -/
theorem ext_of_isSchemeTheoreticallyDominant
    (ι : W ⟶ X) [IsSchemeTheoreticallyDominant ι] {f g : X ⟶ Y}
    (s : Y ⟶ S) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (hι : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over S := Over.mk (f ≫ s)
  let Y' : Over S := Over.mk s
  let W' : Over S := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  let ι' : W' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := inferInstanceAs (IsSeparated s)
  have hι' : ι' ≫ f' = ι' ≫ g' := by
    apply Over.OverMorphism.ext
    simpa only [Over.comp_left, ι', f', g', Over.homMk_left] using hι
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    apply le_antisymm _ bot_le
    calc
      (equalizer.ι f' g').left.ker ≤
          ((equalizer.lift ι' hι').left ≫ (equalizer.ι f' g').left).ker :=
        Scheme.Hom.le_ker_comp _ _
      _ = ι.ker := by
        rw [← Over.comp_left, equalizer.lift_ι]
        simp only [ι', Over.homMk_left]
      _ = ⊥ := ι.ker_eq_bot
  have : IsIso (equalizer.ι f' g').left :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  rw [← cancel_epi (equalizer.ι f' g').left]
  simpa only [Over.comp_left, f', g', Over.homMk_left] using
    congrArg Over.Hom.left (equalizer.condition f' g')

end TauCeti

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- A morphism `f : X ⟶ Y` to an affine scheme is scheme-theoretically dominant exactly when it
is injective on global sections. -/
theorem isSchemeTheoreticallyDominant_iff_appTop_injective (f : X ⟶ Y) [IsAffine Y] :
    IsSchemeTheoreticallyDominant f ↔ Function.Injective f.appTop := by
  -- an ideal sheaf on an affine scheme is trivial exactly when its ideal of global sections is
  rw [isSchemeTheoreticallyDominant_iff, Scheme.ker_of_isAffine,
    ← Scheme.IdealSheafData.equivOfIsAffine_symm_apply, map_eq_bot_iff,
    RingHom.injective_iff_ker_eq_bot]

/-- `Spec` of a ring homomorphism `φ` is scheme-theoretically dominant exactly when `φ` is
injective. -/
@[simp]
theorem isSchemeTheoreticallyDominant_SpecMap_iff {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    IsSchemeTheoreticallyDominant (Spec.map φ) ↔ Function.Injective φ.hom := by
  -- on global sections, `Spec.map φ` is `φ`, up to the isomorphisms `Scheme.ΓSpecIso`
  rw [isSchemeTheoreticallyDominant_iff_appTop_injective,
    RingHom.injective_respectsIso.arrow_mk_iso_iff (arrowIsoΓSpecOfIsAffine φ)]

/-- A morphism `f : X ⟶ Y` is scheme-theoretically dominant if its base change to each member of
an open cover of `Y` is scheme-theoretically dominant. -/
theorem IsSchemeTheoreticallyDominant.of_openCover {f : X ⟶ Y} (𝒰 : Y.OpenCover)
    (h : ∀ i, IsSchemeTheoreticallyDominant (𝒰.pullbackHom f i)) :
    IsSchemeTheoreticallyDominant f := by
  -- the kernels of the members of an open cover of `Y` have trivial intersection, so it suffices
  -- that each of them contains the kernel of `f`
  rw [isSchemeTheoreticallyDominant_iff, eq_bot_iff, ← Scheme.Hom.ker_eq_bot_of_isIso (𝟙 Y)]
  refine (Scheme.Hom.le_ker_iff_of_openCover (𝟙 Y) _ 𝒰).2 fun i ↦ ?_
  -- the base change of `f` to a member of the cover has trivial kernel, so following it by the
  -- member gives a morphism with the kernel of the member, and this morphism factors through `f`
  rw [Category.comp_id, ← Scheme.IdealSheafData.map_bot (𝒰.f i), ← (h i).ker_eq_bot,
    Scheme.IdealSheafData.map_ker, 𝒰.pullbackHom_map]
  exact Scheme.Hom.le_ker_comp _ _

/-- A quasi-compact scheme-theoretically dominant morphism stays scheme-theoretically dominant
after corestriction along an open immersion containing its image. -/
instance IsOpenImmersion.isSchemeTheoreticallyDominant_lift {W V Z : Scheme.{u}} (v : V ⟶ Z)
    [IsOpenImmersion v] (u : W ⟶ Z) [IsSchemeTheoreticallyDominant u] [QuasiCompact u]
    (H : Set.range u ⊆ Set.range v) :
    IsSchemeTheoreticallyDominant (IsOpenImmersion.lift v u H) :=
  IsSchemeTheoreticallyDominant.of_isPullback (IsOpenImmersion.isPullback_lift_id u v H).flip

/-- **Factorization through a closed subscheme descends along scheme-theoretically dominant
morphisms.** For a commutative square `φ' ≫ g = p ≫ φ` with `p` scheme-theoretically dominant,
`φ'` factors through the inverse image of `V(D)` along `g` exactly when `φ` factors through
`V(D)`. -/
theorem Scheme.IdealSheafData.comap_le_ker_iff_of_isSchemeTheoreticallyDominant
    {X' Y' : Scheme.{u}} (D : Y.IdealSheafData) {g : Y' ⟶ Y} (p : X' ⟶ X)
    [IsSchemeTheoreticallyDominant p] {φ' : X' ⟶ Y'} {φ : X ⟶ Y} (w : φ' ≫ g = p ≫ φ) :
    D.comap g ≤ φ'.ker ↔ D ≤ φ.ker := by
  rw [← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_ker, w,
    p.ker_comp_of_isSchemeTheoreticallyDominant]

/-- **A closed subscheme is everything as soon as its inverse image along a scheme-theoretically
dominant morphism is.** For `g` scheme-theoretically dominant, `I.comap g = ⊥` exactly when
`I = ⊥`. -/
@[simp]
theorem Scheme.IdealSheafData.comap_eq_bot_iff_of_isSchemeTheoreticallyDominant (g : X ⟶ Y)
    [IsSchemeTheoreticallyDominant g] {I : Y.IdealSheafData} : I.comap g = ⊥ ↔ I = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ comap_bot g⟩
  rw [← le_bot_iff, ← g.ker_eq_bot, ← map_bot, le_map_iff_comap_le, h]

/-- **Inverse images along a universally scheme-theoretically dominant morphism reflect
inclusion.** If every base change of `g : X ⟶ Y` is scheme-theoretically dominant, then
`I.comap g ≤ J.comap g` exactly when `I ≤ J`. -/
theorem Scheme.IdealSheafData.comap_le_comap_iff_of_universally_isSchemeTheoreticallyDominant
    (g : X ⟶ Y) (hg : MorphismProperty.universally @IsSchemeTheoreticallyDominant g)
    {I J : Y.IdealSheafData} : I.comap g ≤ J.comap g ↔ I ≤ J := by
  refine ⟨fun h ↦ ?_, fun h ↦ comap_mono g h⟩
  -- The base change of `g` to `V(J)` is scheme-theoretically dominant, and its composite with `g`
  -- factors through `V(J.comap g)`, hence through `V(I.comap g)`.
  have hJ := IsPullback.of_hasPullback g J.subschemeι
  have : IsSchemeTheoreticallyDominant (pullback.snd g J.subschemeι) := hg _ _ _ hJ.flip
  have := (comap_le_ker_iff_of_isSchemeTheoreticallyDominant I _ pullback.condition).mp
    (by rwa [ker_eq_comap_of_isPullback J.subschemeι hJ, ker_subschemeι])
  rwa [ker_subschemeι] at this

/-- **Inverse images along a universally scheme-theoretically dominant morphism are injective.**
If every base change of `g` is scheme-theoretically dominant, then two ideal sheaves with the same
inverse image along `g` are equal. -/
theorem Scheme.IdealSheafData.comap_injective_of_universally_isSchemeTheoreticallyDominant
    (g : X ⟶ Y) (hg : MorphismProperty.universally @IsSchemeTheoreticallyDominant g) :
    Function.Injective (comap · g) := fun _ _ h ↦
  le_antisymm ((comap_le_comap_iff_of_universally_isSchemeTheoreticallyDominant g hg).mp h.le)
    ((comap_le_comap_iff_of_universally_isSchemeTheoreticallyDominant g hg).mp h.ge)

/-- **A flat surjective morphism is scheme-theoretically dominant**: its scheme-theoretic image is
the whole target. -/
instance IsSchemeTheoreticallyDominant.of_flat_of_surjective (f : X ⟶ Y) [Flat f]
    [Surjective f] : IsSchemeTheoreticallyDominant f where
  ker_eq_bot := by
    -- `f.ker` and `⊥` have the same inverse image along `f`, and at each point the extension of
    -- stalk ideals along the faithfully flat stalk map of `f` is injective.
    refine le_bot_iff.mp (Scheme.IdealSheafData.le_iff_forall_stalkIdeal_le.mpr fun x ↦ ?_)
    obtain ⟨y, rfl⟩ := f.surjective x
    let _ := (f.stalkMap y).hom.toAlgebra
    have : Module.FaithfullyFlat (Y.presheaf.stalk (f y)) (X.presheaf.stalk y) :=
      f.faithfullyFlat_stalkMap y (Flat.stalkMap f y)
    have hy := congr(Scheme.IdealSheafData.stalkIdeal
      $(f.comap_ker_self.trans (Scheme.IdealSheafData.comap_bot f).symm) y)
    rw [Scheme.IdealSheafData.stalkIdeal_comap, Scheme.IdealSheafData.stalkIdeal_comap] at hy
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := X.presheaf.stalk y) (f.ker.stalkIdeal _),
      ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := X.presheaf.stalk y)
        ((⊥ : Y.IdealSheafData).stalkIdeal (f y))]
    exact Ideal.comap_mono hy.le

/-- **Flat surjective morphisms are universally scheme-theoretically dominant**, since flatness and
surjectivity are stable under base change. -/
theorem IsSchemeTheoreticallyDominant.universally_of_flat_of_surjective (f : X ⟶ Y) [Flat f]
    [Surjective f] : MorphismProperty.universally @IsSchemeTheoreticallyDominant f :=
  fun _ _ _ _ f' (h : IsPullback f' _ _ f) ↦
    have : Flat f' := MorphismProperty.of_isPullback h.flip ‹_›
    have : Surjective f' := MorphismProperty.of_isPullback h.flip ‹_›
    inferInstance

end AlgebraicGeometry
