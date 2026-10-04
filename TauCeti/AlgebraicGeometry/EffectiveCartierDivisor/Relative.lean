/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Relative effective Cartier divisors

An effective Cartier divisor on `X` relative to `S` is an effective Cartier divisor whose
closed subscheme is flat over `S`. This file records the base-change ideal and identifies its
closed subscheme with the expected fibre product. Consequently, the relative flatness condition
is preserved by arbitrary base change.

The remaining part of arbitrary-base-change stability is local algebra: a local equation must
stay a nonzerodivisor. That calculation uses the quotient-flatness criterion developed in
`TauCeti.RingTheory.Flat.QuotientRegular`.

## Main results

* `Scheme.IdealSheafData.IsRelativeEffectiveCartier`: an effective Cartier divisor flat over
  the base.
* `Scheme.IdealSheafData.relativeBaseChangeSubschemeIso`: the closed subscheme cut out by the
  pulled-back ideal is the base change of the original closed subscheme.
* `Scheme.IdealSheafData.IsRelativeEffectiveCartier.flat_relativeBaseChange`: relative
  flatness is preserved by arbitrary base change.
* `Scheme.IdealSheafData.IsRelativeEffectiveCartier.relativeBaseChange_of_flat`: a relative
  effective Cartier divisor remains one after a flat base change.

## References

* Stacks Project, *Divisors*, Relative effective Cartier divisors.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {S T X : Scheme.{u}}

/-- An effective Cartier divisor relative to `S` is an effective Cartier divisor whose closed
subscheme is flat over `S`. -/
def IsRelativeEffectiveCartier (I : X.IdealSheafData) (f : X ⟶ S) : Prop :=
  I.IsEffectiveCartier ∧ Flat (I.subschemeι ≫ f)

/-- A relative effective Cartier divisor is an effective Cartier divisor on its ambient scheme. -/
theorem IsRelativeEffectiveCartier.isEffectiveCartier {I : X.IdealSheafData} {f : X ⟶ S}
    (hI : I.IsRelativeEffectiveCartier f) : I.IsEffectiveCartier :=
  hI.1

/-- The closed subscheme of a relative effective Cartier divisor is flat over the base. -/
theorem IsRelativeEffectiveCartier.flat {I : X.IdealSheafData} {f : X ⟶ S}
    (hI : I.IsRelativeEffectiveCartier f) : Flat (I.subschemeι ≫ f) :=
  hI.2

/-- The closed subscheme cut out by the base-changed ideal is the fibre product of the original
closed subscheme with the new base. -/
noncomputable def relativeBaseChangeSubschemeIso (I : X.IdealSheafData) (f : X ⟶ S)
    (g : T ⟶ S) :
    (I.comap (pullback.fst f g)).subscheme ≅ pullback (I.subschemeι ≫ f) g :=
  I.comapIso (pullback.fst f g) ≪≫
    pullbackSymmetry (pullback.fst f g) I.subschemeι ≪≫
      pullbackRightPullbackFstIso f g I.subschemeι

/-- Under `relativeBaseChangeSubschemeIso`, the structure morphism to the new base is the
restriction of the fibre-product projection. -/
@[reassoc]
theorem relativeBaseChangeSubschemeIso_hom_snd (I : X.IdealSheafData) (f : X ⟶ S)
    (g : T ⟶ S) :
    (I.relativeBaseChangeSubschemeIso f g).hom ≫ pullback.snd (I.subschemeι ≫ f) g =
      (I.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g := by
  simp [relativeBaseChangeSubschemeIso, Category.assoc]

/-- The relative flatness half of the effective Cartier condition is preserved by arbitrary
base change. No flatness assumption on the new base is needed. -/
theorem IsRelativeEffectiveCartier.flat_relativeBaseChange {I : X.IdealSheafData}
    {f : X ⟶ S} (hI : I.IsRelativeEffectiveCartier f) (g : T ⟶ S) :
    Flat ((I.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g) := by
  let _ : Flat (I.subschemeι ≫ f) := hI.flat
  rw [← relativeBaseChangeSubschemeIso_hom_snd]
  infer_instance

/-- Once the original divisor is relative, its arbitrary base change is relative if and only if
the pulled-back ideal is an effective Cartier divisor. Relative flatness is automatic. -/
theorem IsRelativeEffectiveCartier.relativeBaseChange_iff {I : X.IdealSheafData}
    {f : X ⟶ S} (hI : I.IsRelativeEffectiveCartier f) (g : T ⟶ S) :
    (I.comap (pullback.fst f g)).IsRelativeEffectiveCartier (pullback.snd f g) ↔
      (I.comap (pullback.fst f g)).IsEffectiveCartier := by
  constructor
  · exact IsRelativeEffectiveCartier.isEffectiveCartier
  · exact fun h ↦ ⟨h, hI.flat_relativeBaseChange g⟩

/-- A relative effective Cartier divisor remains a relative effective Cartier divisor after a
flat base change. Arbitrary base change requires the stronger local-algebra argument that uses
flatness of the divisor rather than flatness of the base-change morphism. -/
theorem IsRelativeEffectiveCartier.relativeBaseChange_of_flat {I : X.IdealSheafData}
    {f : X ⟶ S} (hI : I.IsRelativeEffectiveCartier f) (g : T ⟶ S) [Flat g] :
    (I.comap (pullback.fst f g)).IsRelativeEffectiveCartier (pullback.snd f g) := by
  rw [hI.relativeBaseChange_iff]
  exact hI.isEffectiveCartier.comap (pullback.fst f g)

end AlgebraicGeometry.Scheme.IdealSheafData
