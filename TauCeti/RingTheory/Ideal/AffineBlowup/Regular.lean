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
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay
import TauCeti.RingTheory.RegularLocalRing.DimensionTwo
import TauCeti.RingTheory.RegularLocalRing.Locus
import TauCeti.RingTheory.RegularLocalRing.OfQuotient
import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension

/-!
# Regularity of the affine blowup algebra of a regular pair

Let `a, g` be a weakly regular sequence on a Noetherian ring `R`, and let `S` be a localization
of `R` away from `a`. The affine blowup algebra `R[g/a] = R[(a, g)/a] ⊆ S`, the chart `D₊(a)` of
the blowup of `Spec R` along `V(a, g)`, is a regular ring as soon as `S` and `R ⧸ (a, g)` are:

* away from `a`, the chart is `S` itself, since `R[g/a]` is an intermediate ring of `S`;
* along `a`, the element `a` is a nonzerodivisor of `R[g/a]` and the quotient
  `R[g/a] ⧸ (a) ≅ R[X] ⧸ (aX - g, a) = R[X] ⧸ (a, g)` is the polynomial ring `(R ⧸ (a, g))[X]`,
  which is regular; regularity then lifts along the nonzerodivisor `a`.

The main instance is the blowup of a two-dimensional regular local ring `A` at its closed point.
If `x, y` generate the maximal ideal `𝔪` of `A`, then `x, y` is a regular sequence, `A_x` is
regular and `A ⧸ 𝔪` is a field, so the chart `A[𝔪/x]` is a regular ring. The charts of `x` and
of `y` cover the blowup of `Spec A` at its closed point, so this blowup is a regular scheme; this is
the local computation behind the regularity of the blowup of a regular two-dimensional scheme at a
closed point, in `TauCeti/AlgebraicGeometry/Blowup/Regular.lean`.

## Main results

* `RingTheory.Sequence.IsWeaklyRegular.isRegularRing_affineBlowup`: for a weakly regular sequence
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

/-- The quotient of the affine blowup algebra `R[(a, g)/a]` by `a` is a regular ring when
`R ⧸ (a, g)` is: it is the polynomial ring `(R ⧸ (a, g))[X]`. -/
private theorem isRegularRing_affineBlowup_quotient (hag : IsWeaklyRegular R [a, g])
    [IsRegularRing (R ⧸ Ideal.span {a, g})] :
    IsRegularRing ((Ideal.span {a, g}).affineBlowup a S ⧸
      Ideal.span {algebraMap R ((Ideal.span {a, g}).affineBlowup a S) a}) := by
  let I := Ideal.span {a}
  -- `R[X] ⧸ (aX - g, a) = (R ⧸ (a))[X] ⧸ (g)`, since modulo `a` the relation `aX - g` is `-g`.
  have hmap : I.map (AdjoinRoot.of (C a * X - C g)) =
      Ideal.span {AdjoinRoot.of (C a * X - C g) a} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hrel : Ideal.span {(C a * X - C g).map (Ideal.Quotient.mk I)} =
      (Ideal.span {Ideal.Quotient.mk I g}).map C := by
    rw [Ideal.map_span, Set.image_singleton, Polynomial.map_sub, Polynomial.map_mul, map_C, map_C,
      map_X, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a), map_zero,
      zero_mul, zero_sub, Ideal.span_singleton_neg]
  let e₀ : AdjoinRoot (C a * X - C g) ⧸ Ideal.span {AdjoinRoot.of (C a * X - C g) a} ≃+*
      ((R ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I g})[X] :=
    (Ideal.quotEquivOfEq hmap.symm).trans
      ((AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot I _).trans
        ((Ideal.quotEquivOfEq hrel).trans (Ideal.polynomialQuotientEquivQuotientPolynomial _).symm))
  let e := Ideal.adjoinRootEquivAffineBlowup S hag
  -- `(R ⧸ (a)) ⧸ (g) = R ⧸ (a, g)`
  have : IsRegularRing ((R ⧸ Ideal.span {a}) ⧸
      Ideal.span {Ideal.Quotient.mk (Ideal.span {a}) g}) := by
    have h₁ : Ideal.span {Ideal.Quotient.mk (Ideal.span {a}) g} =
        (Ideal.span {g}).map (Ideal.Quotient.mk (Ideal.span {a})) := by
      rw [Ideal.map_span, Set.image_singleton]
    have h₂ : Ideal.span {a} ⊔ Ideal.span {g} = Ideal.span {a, g} := by
      rw [← Ideal.span_insert]
    exact .of_ringEquiv ((Ideal.quotEquivOfEq h₁).trans
      ((DoubleQuot.quotQuotEquivQuotSup (Ideal.span {a}) (Ideal.span {g})).trans
        (Ideal.quotEquivOfEq h₂))).symm
  have hspan : Ideal.span {algebraMap R ((Ideal.span {a, g}).affineBlowup a S) a} =
      (Ideal.span {AdjoinRoot.of (C a * X - C g) a}).map e := by
    rw [Ideal.map_span, Set.image_singleton, ← AdjoinRoot.algebraMap_eq, AlgEquiv.commutes]
  exact IsRegularRing.of_ringEquiv
    (R := ((R ⧸ Ideal.span {a}) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {a}) g})[X])
    ((Ideal.quotientEquiv _ _ e.toRingEquiv hspan).symm.trans e₀).symm

/-- **The chart of a blowup along a regular pair is regular.** Let `a, g` be a weakly regular
sequence on a Noetherian ring `R`, and let `S` be a localization of `R` away from `a`. If `S` and
`R ⧸ (a, g)` are regular rings, then so is the affine blowup algebra `R[(a, g)/a] ⊆ S`, the chart
`D₊(a)` of the blowup of `Spec R` along `V(a, g)`. -/
theorem isRegularRing_affineBlowup [IsNoetherianRing R] (hag : IsWeaklyRegular R [a, g])
    [IsRegularRing S] [IsRegularRing (R ⧸ Ideal.span {a, g})] :
    IsRegularRing ((Ideal.span {a, g}).affineBlowup a S) := by
  set T := (Ideal.span {a, g}).affineBlowup a S
  have : IsNoetherianRing T :=
    isNoetherianRing_of_ringEquiv _ (Ideal.adjoinRootEquivAffineBlowup S hag).toRingEquiv
  have := isRegularRing_affineBlowup_quotient S hag
  let M := Algebra.algebraMapSubmonoid T (Submonoid.powers a)
  have : IsLocalization M S := IsLocalization.isLocalization_algebraMapSubmonoid_of_injective
    (Submonoid.powers a) Subtype.val_injective
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
      rw [PrimeSpectrum.localization_comap_range S M, Set.mem_ofPred_eq, Set.disjoint_left]
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩ hn
      exact hp (p.isPrime.mem_of_pow_mem n (by simpa using hn))
    rw [← Set.mem_preimage, M.preimage_comap_regularLocus,
      TauCeti.Excellence.regularLocus_eq_univ]
    trivial

end RingTheory.Sequence.IsWeaklyRegular

namespace TauCeti.IsRegularLocalRing

variable {A : Type*} [CommRing A] [IsRegularLocalRing A]

/-- **Blowing up the closed point of a regular surface: the charts are regular.** Let `A` be a
regular local ring of dimension two whose maximal ideal `𝔪` is generated by `x` and `y`, and let
`S` be a localization of `A` away from `x`. Then the affine blowup algebra `A[𝔪/x] ⊆ S`, the
chart `D₊(x)` of the blowup of `Spec A` at its closed point, is a regular ring. -/
theorem isRegularRing_affineBlowup_maximalIdeal (hdim : ringKrullDim A = 2) {x y : A}
    (hxy : Ideal.span {x, y} = maximalIdeal A) (S : Type*) [CommRing S] [Algebra A S]
    [IsLocalization.Away x S] : IsRegularRing ((maximalIdeal A).affineBlowup x S) := by
  -- A pair generating the maximal ideal of a two-dimensional regular local ring is regular.
  have hreg : IsRegular A [x, y] := isRegular_of_ofList_eq_maximalIdeal
    (by simpa [Ideal.ofList_cons, Ideal.ofList_singleton, ← Ideal.span_insert] using hxy)
    (by simp [spanFinrank_maximalIdeal_eq_two hdim])
  have : IsRegularRing S := IsRegularRing.of_isLocalization (Submonoid.powers x) S
  have : IsRegularRing (A ⧸ Ideal.span {x, y}) := by
    rw [hxy]
    let := Ideal.Quotient.field (maximalIdeal A)
    infer_instance
  rw [← hxy]
  exact hreg.toIsWeaklyRegular.isRegularRing_affineBlowup S

end TauCeti.IsRegularLocalRing
