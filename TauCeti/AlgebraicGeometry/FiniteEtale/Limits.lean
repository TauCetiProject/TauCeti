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
# Finite limits, finite coproducts and summands of finite étale schemes

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

The limit and colimit instances are deduced from Mathlib's closure results for
`MorphismProperty.overObj` and from Mathlib's description of coproducts of schemes by disjoint
open covers, `AlgebraicGeometry.nonempty_isColimit_binaryCofanMk_of_isCompl`. Openness of
monomorphisms uses `AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono`.

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

/-- The inclusion of finite étale schemes over `S` into `Over S` preserves finite coproducts. -/
instance : PreservesFiniteCoproducts (finiteEtaleSchemeProperty S).ι :=
  ⟨fun _ ↦ inferInstance⟩

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

end FiniteEtaleScheme

end TauCeti
