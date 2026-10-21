/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.Counit
public import TauCeti.AlgebraicGeometry.RelativeSpec.Equalizer
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.DescentDatum

/-!
# The descended scheme of a descent datum on an affine morphism

Let `p : S' ⟶ S` be an affine morphism of schemes and `D` a descent datum relative to `p`, in the
sense of `TauCeti.DescentDatum p X`, on a scheme `X ⟶ S'` affine over `S'`. Write
`π = X.hom ≫ p : X ⟶ S`, an affine morphism. The datum gives two morphisms over `S`
from `S' ×_S X` to `X`: the action `(s, x) ↦ s · x` and the second projection `(s, x) ↦ x`. On
functions, these are two morphisms of quasi-coherent `𝒪_S`-algebras `π_* 𝒪_X ⟶ (π')_* 𝒪_{S' ×_S X}`,
and this file defines the *descended scheme* `D.descended` as the relative spectrum over `S` of
their equalizer (`CommMon.relativeSpecEqualizer`). Over an affine open `U` of `S` it is the
spectrum of the functions on `π⁻¹ U` which are invariant under the descent datum
(`CommMon.isPullback_relativeSpecEqualizerCover`); this is the global form of the invariant
subalgebra `TauCeti.Algebra.DescentDatum.descended` used over an affine base.

The quotient map `D.toDescended : X ⟶ D.descended` lies over `S` and is invariant under the
action (`DescentDatum.act_toDescended`). Consequently it induces a morphism of descent data
`D.toBaseChangeDescended : Hom D (baseChange p D.descended)` from `D` to the canonical descent
datum on `D.descended ×_S S'`. Faithfully flat descent for affine morphisms asserts that this
comparison is an isomorphism when `p` is flat, so that `D` is then effective with descended
scheme `D.descended`; this file constructs the comparison.

## Main declarations

* `TauCeti.DescentDatum.actAlgebraMap D` and `TauCeti.DescentDatum.sndAlgebraMap p X`: pullback
  of functions along the action and along the second projection;
* `TauCeti.DescentDatum.descended D`: the descended scheme, affine over `S`, identified with the
  relative spectrum of the equalizer by `TauCeti.DescentDatum.descended_left` and
  `TauCeti.DescentDatum.descended_hom`;
* `TauCeti.DescentDatum.toDescended D`: the quotient map `X ⟶ D.descended` over `S`, with
  `TauCeti.DescentDatum.relativeSpecFunctionsToScheme_toDescended` and
  `TauCeti.DescentDatum.act_toDescended`;
* `TauCeti.DescentDatum.toBaseChangeDescended D`: the comparison morphism of descent data from `D`
  to the canonical descent datum on the base change of `D.descended`.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII,
  Théorème 2.1.
* The Stacks Project, Chapter *Descent*, Section *Descent data for schemes over schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

namespace DescentDatum

universe u

noncomputable section

variable {S S' : Scheme.{u}} {p : S' ⟶ S} [IsAffineHom p] {X : Over S'} [IsAffineHom X.hom]
  (D : DescentDatum p X)

omit [IsAffineHom X.hom] in
/-- The structure morphism `S' ×_S X ⟶ S` is affine. -/
instance isAffineHom_pullback_snd_comp :
    IsAffineHom (pullback.snd p (X.hom ≫ p) ≫ X.hom ≫ p) :=
  have : IsAffineHom (pullback.snd p (X.hom ≫ p)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  inferInstance

/-- Pullback of functions along the action of `D`, as a morphism of function algebras over `S`. -/
abbrev actAlgebraMap :
    (X.hom ≫ p).pushforwardStructureAlgebra ⟶
      (pullback.snd p (X.hom ≫ p) ≫ X.hom ≫ p).pushforwardStructureAlgebra :=
  Scheme.Hom.pushforwardStructureAlgebraMap D.act D.act_comp_hom_comp

variable (p X) in
/-- Pullback of functions along the second projection `S' ×_S X ⟶ X`, as a morphism of function
algebras over `S`. -/
abbrev sndAlgebraMap :
    (X.hom ≫ p).pushforwardStructureAlgebra ⟶
      (pullback.snd p (X.hom ≫ p) ≫ X.hom ≫ p).pushforwardStructureAlgebra :=
  Scheme.Hom.pushforwardStructureAlgebraMap (pullback.snd p (X.hom ≫ p)) rfl

/-- The scheme descended from a descent datum `D` on an affine morphism `X ⟶ S'`: the relative
spectrum over `S` of the functions on `X` whose pullbacks along the action and along the second
projection `S' ×_S X ⟶ X` agree. -/
-- Implicitly reducible, so that morphisms into `D.descended.left` unify with morphisms into the
-- relative spectrum of the equalizer, and the equalizer lemmas rewrite them.
@[expose, implicit_reducible]
def descended : Over S :=
  Over.mk (CommMon.relativeSpecEqualizerToBase D.actAlgebraMap (sndAlgebraMap p X))

/-- The underlying scheme of the descended scheme is the relative spectrum of the equalizer of
`D.actAlgebraMap` and `sndAlgebraMap p X`. -/
theorem descended_left :
    D.descended.left = CommMon.relativeSpecEqualizer D.actAlgebraMap (sndAlgebraMap p X) :=
  (rfl)

/-- The structure morphism of the descended scheme is that of the relative spectrum of the
equalizer. -/
theorem descended_hom :
    D.descended.hom = CommMon.relativeSpecEqualizerToBase D.actAlgebraMap (sndAlgebraMap p X) :=
  (rfl)

/-- The descended scheme is affine over `S`. -/
instance isAffineHom_descended_hom : IsAffineHom D.descended.hom := by
  rw [descended_hom]
  infer_instance

/-- The quotient map from `X` to the scheme descended from `D`. -/
def toDescended : X.left ⟶ D.descended.left :=
  inv (X.hom ≫ p).relativeSpecFunctionsToScheme ≫
    CommMon.relativeSpecEqualizerπ D.actAlgebraMap (sndAlgebraMap p X)

/-- Through the identification of `X` with the relative spectrum of its functions over `S`, the
quotient map is `CommMon.relativeSpecEqualizerπ`. -/
@[reassoc]
theorem relativeSpecFunctionsToScheme_toDescended :
    (X.hom ≫ p).relativeSpecFunctionsToScheme ≫ D.toDescended =
      CommMon.relativeSpecEqualizerπ D.actAlgebraMap (sndAlgebraMap p X) := by
  rw [toDescended, IsIso.hom_inv_id_assoc]

/-- The quotient map lies over `S`. -/
@[reassoc (attr := simp)]
theorem toDescended_hom : D.toDescended ≫ D.descended.hom = X.hom ≫ p := by
  rw [← cancel_epi (X.hom ≫ p).relativeSpecFunctionsToScheme,
    relativeSpecFunctionsToScheme_toDescended_assoc, descended_hom,
    CommMon.relativeSpecEqualizerπ_relativeSpecEqualizerToBase,
    Scheme.Hom.relativeSpecFunctionsToScheme_comp]

/-- The quotient map is invariant under the descent datum: `s · x` and `x` have the same image. -/
@[reassoc]
theorem act_toDescended :
    D.act ≫ D.toDescended = pullback.snd p (X.hom ≫ p) ≫ D.toDescended := by
  -- Both maps are, through the identifications of affine schemes over `S` with the relative
  -- spectra of their function algebras, the relative spectra of the two algebra maps, which
  -- `CommMon.relativeSpecEqualizerπ` coequalizes.
  rw [toDescended,
    Scheme.Hom.inv_relativeSpecFunctionsToScheme_naturality_assoc D.act D.act_comp_hom_comp,
    Scheme.Hom.inv_relativeSpecFunctionsToScheme_naturality_assoc _ rfl,
    CommMon.relativeSpecMap_relativeSpecEqualizerπ]

/-- The comparison morphism from `D` to the canonical descent datum on the base change
`D.descended ×_S S'` of the descended scheme, `x ↦ (D.toDescended x, X.hom x)`. When it is an
isomorphism, the descent datum `D` is effective with descended scheme `D.descended`. -/
def toBaseChangeDescended : Hom D (baseChange p D.descended) where
  hom := Over.homMk (pullback.lift D.toDescended X.hom D.toDescended_hom) (pullback.lift_snd _ _ _)
  map_act := by
    apply pullback.hom_ext
    · simp [act_toDescended]
    · simp

/-- The first component of the comparison morphism is the quotient map. -/
@[reassoc (attr := simp)]
theorem toBaseChangeDescended_hom_left_fst :
    D.toBaseChangeDescended.hom.left ≫ pullback.fst D.descended.hom p = D.toDescended :=
  pullback.lift_fst _ _ _

/-- The second component of the comparison morphism is the structure morphism `X ⟶ S'`. -/
@[reassoc (attr := simp)]
theorem toBaseChangeDescended_hom_left_snd :
    D.toBaseChangeDescended.hom.left ≫ pullback.snd D.descended.hom p = X.hom :=
  pullback.lift_snd _ _ _

end

end DescentDatum

end TauCeti
