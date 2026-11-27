/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.RingTheory.Ideal.AffineBlowup.RegularPair
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import TauCeti.RingTheory.Localization.Tower
import TauCeti.RingTheory.RegularLocalRing.DimensionTwo
import TauCeti.RingTheory.RegularLocalRing.Locus
import TauCeti.RingTheory.RegularLocalRing.OfQuotient
import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension

/-!
# Regularity of the affine blowup algebra of a regular pair

Let `a, g` be a weakly regular sequence on a Noetherian ring `R`, and let `S` be a localization
of `R` away from `a`. The affine blowup algebra `R[g/a] = R[(a, g)/a] ⊆ S`, the coordinate ring of
the chart `D₊(a t)` of the blowup `Proj R[(a, g)t]` of `Spec R` along `V(a, g)`, is a regular ring
as soon as `S` and `R ⧸ (a, g)` are:

* away from `a`, the chart is `S` itself, since `R[g/a]` is an intermediate ring of `S`;
* along `a`, the element `a` is a nonzerodivisor of `R[g/a]` and, through the presentation
  `R[X] ⧸ (aX - g) ≅ R[g/a]` of `Ideal.adjoinRootEquivAffineBlowup`, the quotient
  `R[g/a] ⧸ (a) ≅ R[X] ⧸ (aX - g, a) = R[X] ⧸ (a, g)` is the polynomial ring `(R ⧸ (a, g))[X]`
  (`Ideal.affineBlowupQuotEquivPolynomial`), which is regular; regularity then lifts along the
  nonzerodivisor `a` (`TauCeti.IsRegularLocalRing.localization_of_isRegularRing_quotient`).

The main instance is the blowup of a two-dimensional regular local ring `A` at its closed point.
If `x, y` generate the maximal ideal `𝔪` of `A`, then `x, y` is a regular sequence, `A_x` is
regular and `A ⧸ 𝔪` is a field, so the chart `A[𝔪/x]` is a regular ring
(`TauCeti.IsRegularLocalRing.isRegular_of_span_pair_eq_maximalIdeal`). The charts of `x` and
of `y` cover the blowup of `Spec A` at its closed point, so this blowup is a regular scheme; this is
the local computation behind the regularity of the blowup of a regular two-dimensional scheme at a
closed point, in `TauCeti/AlgebraicGeometry/Blowup/Regular.lean`.

## Main results

* `RingTheory.Sequence.IsWeaklyRegular.isRegularRing_affineBlowup`: for a weakly regular pair
  `a, g` on a Noetherian ring with `R_a` and `R ⧸ (a, g)` regular, the affine blowup algebra
  `R[(a, g)/a]` is a regular ring.
* `TauCeti.IsRegularLocalRing.isRegularRing_affineBlowup_maximalIdeal`: for a regular local ring
  `A` of dimension two and an element `x` of a pair generating its maximal ideal `𝔪`, the affine
  blowup algebra `A[𝔪/x]` is a regular ring.

## References

* The Stacks Project, Lemma 10.106.7 (00NU), for lifting regularity along a nonzerodivisor, and
  Lemma 10.106.3 (00NQ), for regular systems of parameters as regular sequences.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford University Press, 2002, Section 8.1
  (blowing up), where blowups of regular schemes along regular centres are shown to be regular.
-/

public section

open Polynomial RingTheory.Sequence IsLocalRing

namespace RingTheory.Sequence.IsWeaklyRegular

variable {R : Type*} [CommRing R] {a g : R}

variable (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away a S]

/-- **The chart of a blowup along a regular pair is regular when its two pieces are.** Let `a, g` be
a weakly regular pair on a Noetherian ring `R`, and let `S` be a localization of `R` away from `a`.
If `S` and `R ⧸ (a, g)` are regular rings, then so is the affine blowup algebra
`R[(a, g)/a] ⊆ S`, the coordinate ring of the chart `D₊(a t)` of the blowup of `Spec R` along
`V(a, g)`. -/
theorem isRegularRing_affineBlowup [IsNoetherianRing R] (hag : IsWeaklyRegular R [a, g])
    [IsRegularRing S] [IsRegularRing (R ⧸ Ideal.span {a, g})] :
    IsRegularRing ((Ideal.span {a, g}).affineBlowup a S) := by
  set T := (Ideal.span {a, g}).affineBlowup a S
  have : IsNoetherianRing T :=
    isNoetherianRing_of_ringEquiv _ (Ideal.adjoinRootEquivAffineBlowup S hag).toRingEquiv
  -- `T ⧸ (a) ≅ (R ⧸ (a, g))[X]` is regular.
  have : IsRegularRing (T ⧸ Ideal.span {algebraMap R T a}) :=
    .of_ringEquiv (Ideal.affineBlowupQuotEquivPolynomial S hag).symm
  have : IsLocalization.Away (algebraMap R T a) S := by
    rw [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
    exact IsLocalization.isLocalization_algebraMapSubmonoid_of_injective (Submonoid.powers a)
      Subtype.val_injective
  rw [← TauCeti.Excellence.regularLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  intro p
  by_cases hp : algebraMap R T a ∈ p.asIdeal
  · -- Along `a`, regularity lifts from the regular quotient `T ⧸ (a)`.
    have ha := (Ideal.isRegular_algebraMap_affineBlowup (I := Ideal.span {a, g}) (a := a)
      (S := S)).mem_nonZeroDivisors
    exact TauCeti.Excellence.mem_regularLocus.mpr <|
      TauCeti.IsRegularLocalRing.localization_of_isRegularRing_quotient ha p.asIdeal hp
  · -- Away from `a`, the prime `p` comes from the regular localization `S` of `T`.
    obtain ⟨q, rfl⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap T S)) := by
      rw [PrimeSpectrum.localization_away_comap_range S (algebraMap R T a),
        SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
      exact hp
    rw [← Set.mem_preimage, (Submonoid.powers (algebraMap R T a)).preimage_comap_regularLocus,
      TauCeti.Excellence.regularLocus_eq_univ]
    trivial

end RingTheory.Sequence.IsWeaklyRegular

namespace TauCeti.IsRegularLocalRing

variable {A : Type*} [CommRing A] [IsRegularLocalRing A]

/-- **Blowing up the closed point of a regular surface: the charts are regular.** Let `A` be a
regular local ring of dimension two whose maximal ideal `𝔪` is generated by `x` and `y`, and let
`S` be a localization of `A` away from `x`. Then the affine blowup algebra `A[𝔪/x] ⊆ S`, the
coordinate ring of the chart `D₊(x t)` of the blowup of `Spec A` at its closed point, is a regular
ring. -/
theorem isRegularRing_affineBlowup_maximalIdeal (hdim : ringKrullDim A = 2) {x y : A}
    (hxy : Ideal.span {x, y} = maximalIdeal A) (S : Type*) [CommRing S] [Algebra A S]
    [IsLocalization.Away x S] : IsRegularRing ((maximalIdeal A).affineBlowup x S) := by
  have hreg : IsRegular A [x, y] := isRegular_of_span_pair_eq_maximalIdeal hdim hxy
  have : IsRegularRing S := IsRegularRing.of_isLocalization (Submonoid.powers x) S
  have : IsRegularRing (A ⧸ Ideal.span {x, y}) := by
    rw [hxy]
    let := Ideal.Quotient.field (maximalIdeal A)
    infer_instance
  rw [← hxy]
  exact hreg.toIsWeaklyRegular.isRegularRing_affineBlowup S

end TauCeti.IsRegularLocalRing
