/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

import TauCeti.AlgebraicGeometry.Morphisms.FiniteType.Basic
import TauCeti.AlgebraicGeometry.Normalization.Finite
import TauCeti.RingTheory.IntegralClosure.DiscreteValuationRing

/-!
# Finiteness of normalization over a discrete valuation ring

Over an arbitrary discrete valuation ring `R` with fraction field `K` (not assumed Japanese or
excellent), if `X` is locally of finite type over `Spec R` and its generic fibre `C` is smooth of
relative dimension `1` over `Spec K`, then the normalization of `X` in `C` is finite over `X`
(`TauCeti.AlgebraicGeometry.isFinite_fromNormalization_of_isPullback`, Stacks Lemma 55.8.3 / 0C2U).

## Main results

* `TauCeti.AlgebraicGeometry.isFinite_fromNormalization_of_isPullback`: for a scheme `X` locally of
  finite type over a discrete valuation ring `R` whose generic fibre `C` is smooth of relative
  dimension `1` over `Frac(R)`, the normalization of `X` in `C` is finite over `X`.

## References

* [Stacks Project, Lemma 55.8.3](https://stacks.math.columbia.edu/tag/0C2U), finiteness of
  normalization for smooth curve models over discrete valuation rings.
-/

public section

open CategoryTheory AlgebraicGeometry Limits

namespace TauCeti.AlgebraicGeometry

universe u

/-- **Finiteness of normalization in a smooth generic fibre of relative dimension one.** Let `R` be
a discrete valuation ring with fraction field `K`, let `X` be a scheme locally of finite type over
`Spec R`, and let `C` be its generic fibre over `Spec K`, with projection `g : C ⟶ X`. If `C` is
smooth of relative dimension `1` over `Spec K`, then the normalization of `X` in `C` along `g` is
finite over `X`. No excellence or Japanese hypothesis on `R` and no flatness hypothesis on `X` are
needed. -/
@[stacks 0C2U]
theorem isFinite_fromNormalization_of_isPullback
    {R K : Type u} [CommRing R] [IsDomain R] [_root_.IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X C : Scheme.{u}} {toBase : X ⟶ Spec (.of R)} [LocallyOfFiniteType toBase]
    {toK : C ⟶ Spec (.of K)} [SmoothOfRelativeDimension 1 toK] {g : C ⟶ X}
    (H : IsPullback g toK toBase (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    haveI : IsAffineHom g := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
    IsFinite g.fromNormalization := by
  have : IsAffineHom g := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  refine g.isFinite_fromNormalization_iff.mpr fun U hU ↦ ?_
  have hV : IsAffineOpen (g ⁻¹ᵁ U) := hU.preimage g
  refine with_finiteType_algebraIsPushout_of_isPullback H hU fun _ hS hXY ↦ ?_
  have hsm : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (toK.appLE ⊤ (g ⁻¹ᵁ U) le_top).hom :=
    HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension 1)
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1))
      (f := toK) ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨g ⁻¹ᵁ U, hV⟩ le_top
  have hloc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap K Γ(C, g ⁻¹ᵁ U)) := by
    rw [hS, CommRingCat.hom_comp]
    exact (RingHom.locally_respectsIso
      (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1))).right _
      (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv hsm
  open TauCeti.IsDiscreteValuationRing in
  exact hXY ▸ finite_integralClosure_of_locally_isStandardSmoothOfRelativeDimension_one
    (R := R) (K := K) hloc

end TauCeti.AlgebraicGeometry
