/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Finite.Colimits
public import Mathlib.AlgebraicGeometry.LimitsOver
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Finite limits, finite coproducts, summands and epimorphisms of finite étale schemes

The category `FiniteEtaleScheme S` of finite étale schemes over a scheme `S` has a terminal
object, fibre products and finite coproducts, all computed in `Over S`. Every monomorphism in it
is the inclusion of a direct summand: its underlying morphism of schemes is an open and closed
immersion, and the open complement of its image is again finite étale over `S`. These are the
axioms (G1) and (G3), and the finite-coproduct half of (G2), of a Galois category in the sense of
Lenstra, as they appear in Mathlib's `CategoryTheory.PreGaloisCategory`. Quotients by finite groups,
the remaining half of (G2), are not treated here.

## Main results

* `TauCeti.FiniteEtaleScheme.isOpenImmersion_hom_left`,
  `TauCeti.FiniteEtaleScheme.isClosedImmersion_hom_left`: the underlying morphism of a
  monomorphism of finite étale schemes is an open and closed immersion.
* `TauCeti.FiniteEtaleScheme.exists_isColimit_binaryCofanMk_of_mono`: every monomorphism of
  finite étale schemes is the first inclusion of a binary coproduct.
* `TauCeti.FiniteEtaleScheme.epi_iff_surjective`: a morphism of finite étale schemes is an
  epimorphism if and only if its underlying morphism of schemes is surjective.
* The category `FiniteEtaleScheme S` is finitary extensive: finite coproducts are disjoint and
  stable under pullback.
* The category `FiniteEtaleScheme S` is closed in `Over S` under binary products, so it inherits
  the cartesian monoidal structure of `Over S` (Mathlib's
  `CartesianMonoidalCategory.fullSubcategory`), with the fibre product over `S` as tensor product.

The limit and colimit instances are deduced from Mathlib's closure results for
`MorphismProperty.overObj` and from Mathlib's description of coproducts of schemes by disjoint
open covers, `AlgebraicGeometry.nonempty_isColimit_binaryCofanMk_of_isCompl`. Openness of
monomorphisms uses `AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono`. Surjective morphisms are
epimorphisms because they are faithfully flat (`AlgebraicGeometry.Flat.epi_of_flat_of_surjective`);
conversely the image of an epimorphism is a direct summand whose complement must be empty.

## References

* H. W. Lenstra, *Galois theory for schemes*, Definition 3.1 and Section 5.
* The Stacks Project, Section 58.5 (tag 0BL8), *Finite étale covers of schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti

namespace FiniteEtaleScheme

variable {S : Scheme.{u}}

-- Mathlib's `inf` instances for `IsMultiplicative` and `IsStableUnderBaseChange` are passed
-- explicitly: instance search cannot unify the classes `@IsFinite` and `@Etale` with a
-- `MorphismProperty Scheme` metavariable, as their types agree only after unfolding
-- `MorphismProperty`.
instance : (finiteEtaleSchemeProperty S).IsClosedUnderLimitsOfShape (Discrete PEmpty.{1}) := by
  rw [finiteEtaleSchemeProperty_eq_overObj]
  exact @Over.closedUnderLimitsOfShape_discrete_empty _ _ _ _
    MorphismProperty.IsMultiplicative.inf.toContainsIdentities
    (@MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ _ .inf)

instance : (finiteEtaleSchemeProperty S).IsClosedUnderLimitsOfShape WalkingCospan := by
  rw [finiteEtaleSchemeProperty_eq_overObj]
  exact @Over.closedUnderLimitsOfShape_pullback _ _ _ _ _
    MorphismProperty.IsMultiplicative.inf.toIsStableUnderComposition .inf _

/-- A scheme over `S` isomorphic to a finite étale one is finite étale. -/
instance : (finiteEtaleSchemeProperty S).IsClosedUnderIsomorphisms := by
  have : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).RespectsIso :=
    @MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ _ .inf
  rw [finiteEtaleSchemeProperty_eq_overObj]
  infer_instance

/-- Binary products of finite étale schemes over `S` are finite étale: in `Over S` the product is
the fibre product over the terminal object `S`. -/
instance : (finiteEtaleSchemeProperty S).IsClosedUnderLimitsOfShape (Discrete WalkingPair) := by
  refine .mk' ?_
  rintro _ ⟨F, hF⟩
  have ht : finiteEtaleSchemeProperty S (⊤_ Over S) :=
    (finiteEtaleSchemeProperty S).prop_limit _ fun j ↦ j.as.elim
  refine (finiteEtaleSchemeProperty S).prop_of_iso
    ((HasLimit.isoOfNatIso (diagramIsoPair F)) ≪≫ prodIsoPullback _ _).symm
    ((finiteEtaleSchemeProperty S).prop_limit _ ?_)
  rintro (_ | ⟨_ | _⟩)
  exacts [ht, hF _, hF _]

/-- Finite étale schemes over `S` have all finite limits, computed in `Over S`: the terminal
object is `S` itself and fibre products are fibre products of schemes. -/
instance : HasFiniteLimits (FiniteEtaleScheme S) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

instance : (finiteEtaleSchemeProperty S).IsClosedUnderColimitsOfShape (Discrete PEmpty.{1}) where
  colimitsOfShape_le X hX := by
    obtain ⟨t⟩ := (ObjectProperty.colimitsOfShape_isEmpty_iff _ _ _).mp hX
    have : IsEmpty X.left := isInitial_iff_isEmpty.mp ⟨t.isInitialObj (Over.forget S) X⟩
    exact (finiteEtaleSchemeProperty_iff X).mpr ⟨inferInstance, inferInstance⟩

instance : (finiteEtaleSchemeProperty S).IsClosedUnderColimitsOfShape (Discrete WalkingPair) where
  colimitsOfShape_le X hX := by
    -- Finiteness and étaleness are treated separately: binary coproducts of finite morphisms are
    -- finite, and étaleness is local on the source.
    have hfin : ObjectProperty.IsClosedUnderColimitsOfShape
        (MorphismProperty.overObj @IsFinite (X := S)) (Discrete WalkingPair) :=
      IsFinite.isClosedUnderColimitsOfShape_walkingPair (𝟭 Scheme.{u}) S
    have het : ObjectProperty.IsClosedUnderColimitsOfShape
        (MorphismProperty.overObj @Etale (X := S)) (Discrete WalkingPair) :=
      have : IsZariskiLocalAtSource @Etale.{u} := HasRingHomProperty.instIsZariskiLocalAtSource
      IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete (𝟭 Scheme.{u}) S
    exact (finiteEtaleSchemeProperty_iff X).mpr ⟨hfin.colimitsOfShape_le X
        (ObjectProperty.colimitsOfShape_monotone _
          (fun X h ↦ ((finiteEtaleSchemeProperty_iff X).mp h).1) _ hX),
      het.colimitsOfShape_le X (ObjectProperty.colimitsOfShape_monotone _
          (fun X h ↦ ((finiteEtaleSchemeProperty_iff X).mp h).2) _ hX)⟩

/-- Finite étale schemes over `S` are closed under finite coproducts in `Over S`: the empty
scheme and disjoint unions of finite étale schemes are finite étale. -/
instance : (finiteEtaleSchemeProperty S).IsClosedUnderFiniteCoproducts :=
  .mk'

/-- The inclusion of finite étale schemes over `S` into `Over S` preserves finite limits. -/
instance : PreservesFiniteLimits (finiteEtaleSchemeProperty S).ι :=
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

/-- The braiding of the cartesian monoidal structure on finite étale schemes over `S`, whose
tensor product is the fibre product over `S`. -/
noncomputable instance : BraidedCategory (FiniteEtaleScheme S) := .ofCartesianMonoidalCategory

/-- The inclusion of finite étale schemes over `S` into `Over S` preserves finite coproducts. -/
instance : PreservesFiniteCoproducts (finiteEtaleSchemeProperty S).ι :=
  ⟨fun _ ↦ inferInstance⟩

/-- The category of finite étale schemes over `S` is finitary extensive: finite coproducts are
disjoint and stable under pullback, since both are computed in the extensive category of
schemes. -/
instance : FinitaryExtensive (FiniteEtaleScheme S) :=
  finitaryExtensive_of_preserves_and_reflects ((finiteEtaleSchemeProperty S).ι ⋙ Over.forget S)

variable {X Y : FiniteEtaleScheme S}

/-- The underlying morphism of schemes of a monomorphism of finite étale schemes is a
monomorphism. -/
instance mono_hom_left (i : X ⟶ Y) [Mono i] : Mono i.hom.left := by
  have : Mono ((finiteEtaleSchemeProperty S).ι.map i) := (finiteEtaleSchemeProperty S).ι.map_mono i
  exact Over.mono_left_of_mono ((finiteEtaleSchemeProperty S).ι.map i)

/-- The underlying morphism of schemes of a monomorphism of finite étale schemes is an open
immersion. -/
instance isOpenImmersion_hom_left (i : X ⟶ Y) [Mono i] : IsOpenImmersion i.hom.left :=
  IsOpenImmersion.of_flat_of_mono _

/-- The underlying morphism of schemes of a monomorphism of finite étale schemes is a closed
immersion. -/
instance isClosedImmersion_hom_left (i : X ⟶ Y) [Mono i] : IsClosedImmersion i.hom.left :=
  IsClosedImmersion.of_isPreimmersion _ i.hom.left.isClosedMap.isClosed_range

/-- Every monomorphism `i : X ⟶ Y` of finite étale schemes over `S` is the inclusion of a direct
summand: there is a finite étale `Z` over `S` with a morphism `u : Z ⟶ Y` exhibiting `Y` as the
coproduct of `X` and `Z`. Here `Z` is the open complement of the image of `i`. -/
theorem exists_isColimit_binaryCofanMk_of_mono (i : X ⟶ Y) [Mono i] :
    ∃ (Z : FiniteEtaleScheme S) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u)) := by
  let U : Y.obj.left.Opens :=
    ⟨(Set.range i.hom.left)ᶜ, i.hom.left.isClosedMap.isClosed_range.isOpen_compl⟩
  have : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact i.hom.left.isOpenEmbedding.isOpen_range.isClosed_compl)
  let Z : FiniteEtaleScheme S :=
    ⟨Over.mk (U.ι ≫ Y.obj.hom), (finiteEtaleSchemeProperty_iff _).mpr
      ⟨inferInstanceAs (IsFinite (U.ι ≫ Y.obj.hom)), inferInstanceAs (Etale (U.ι ≫ Y.obj.hom))⟩⟩
  let u : Z ⟶ Y := ObjectProperty.homMk (Over.homMk U.ι rfl)
  have hU : IsCompl i.hom.left.opensRange U.ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι]
    constructor
    · rw [disjoint_iff, ← SetLike.coe_set_eq]
      simp [U]
    · rw [codisjoint_iff, ← SetLike.coe_set_eq]
      simp [U]
  obtain ⟨h⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl i.hom.left U.ι hU
  exact ⟨Z, u, ⟨isColimitOfReflects ((finiteEtaleSchemeProperty S).ι ⋙ Over.forget S)
    ((isColimitMapCoconeBinaryCofanEquiv _ _ _).symm h)⟩⟩

/-- A morphism of finite étale schemes whose underlying morphism of schemes is surjective is an
epimorphism. -/
theorem epi_of_surjective (g : X ⟶ Y) [Surjective g.hom.left] : Epi g := by
  have : Epi g.hom.left := Flat.epi_of_flat_of_surjective _
  have : Epi ((finiteEtaleSchemeProperty S).ι.map g) := Over.epi_of_epi_left (hk := this) _
  exact (finiteEtaleSchemeProperty S).ι.epi_of_epi_map this

/-- The underlying morphism of schemes of an epimorphism of finite étale schemes is
surjective. -/
instance surjective_hom_left (g : X ⟶ Y) [Epi g] : Surjective g.hom.left := by
  -- The image `W` of `g` is open and closed, hence a direct summand `Y = W ⨿ Z`. As `g` factors
  -- through `W`, the two inclusions `Y ⟶ Y ⨿ Y` agree on `Z`, so `Z` is initial by disjointness
  -- of coproducts, and `W` is all of `Y`.
  let W : Y.obj.left.Opens := ⟨_, g.hom.left.isOpenMap.isOpen_range⟩
  have : IsClosedImmersion W.ι := .of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact g.hom.left.isClosedMap.isClosed_range)
  let W' : FiniteEtaleScheme S :=
    ⟨Over.mk (W.ι ≫ Y.obj.hom), (finiteEtaleSchemeProperty_iff _).mpr
      ⟨inferInstanceAs (IsFinite (W.ι ≫ Y.obj.hom)), inferInstanceAs (Etale (W.ι ≫ Y.obj.hom))⟩⟩
  let w : W' ⟶ Y := ObjectProperty.homMk (Over.homMk W.ι rfl)
  have : Mono ((finiteEtaleSchemeProperty S).ι.map w) :=
    Over.mono_of_mono_left (hk := inferInstanceAs (Mono W.ι)) _
  have : Mono w := (finiteEtaleSchemeProperty S).ι.mono_of_mono_map this
  obtain ⟨Z, u, ⟨hc⟩⟩ := exists_isColimit_binaryCofanMk_of_mono w
  -- The factorization `g = g' ≫ w`.
  let g' : X ⟶ W' := ObjectProperty.homMk (Over.homMk
    (IsOpenImmersion.lift W.ι g.hom.left (by rw [Scheme.Opens.range_ι]; rfl)) (by simp [W']))
  have hg : g' ≫ w = g :=
    ObjectProperty.hom_ext _ (Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _))
  have hw : w ≫ hc.desc (BinaryCofan.mk (w ≫ coprod.inl) (u ≫ coprod.inr)) = w ≫ coprod.inl :=
    hc.fac _ ⟨.left⟩
  have hu : u ≫ coprod.inl = u ≫ coprod.inr := by
    have : (coprod.inl : Y ⟶ Y ⨿ Y) =
        hc.desc (BinaryCofan.mk (w ≫ coprod.inl) (u ≫ coprod.inr)) := by
      rw [← cancel_epi g, ← hg, Category.assoc, Category.assoc, hw]
    rw [this]
    exact hc.fac _ ⟨.right⟩
  -- `u` factors through the initial pullback of the two coproduct inclusions.
  obtain ⟨t, -, -⟩ :=
    (FinitaryExtensive.isPullback_initial_to_binaryCofan (coprodIsCoprod Y Y)).exists_lift u u hu
  have : IsIso t := initialIsInitial.isIso_to t
  have : IsIso w :=
    (BinaryCofan.isColimit_iff_isIso_inl (initialIsInitial.ofIso (asIso t).symm) _).mp ⟨hc⟩
  have : IsIso W.ι :=
    inferInstanceAs (IsIso (((finiteEtaleSchemeProperty S).ι ⋙ Over.forget S).map w))
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨⟨z, hz⟩, rfl⟩ := W.ι.surjective y
  rw [Scheme.Opens.ι_apply]
  exact hz

/-- A morphism of finite étale schemes is an epimorphism if and only if its underlying morphism
of schemes is surjective. -/
theorem epi_iff_surjective (g : X ⟶ Y) : Epi g ↔ Surjective g.hom.left :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ epi_of_surjective g⟩

end FiniteEtaleScheme

end TauCeti
