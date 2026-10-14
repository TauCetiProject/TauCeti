/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Valuation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Localization.Integral
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.XSubT
public import TauCeti.RingTheory.AdjoinRoot.Factors
public import TauCeti.RingTheory.DedekindDomain.PrimesAbove
import Mathlib.Tactic.LinearCombination
import TauCeti.RingTheory.DedekindDomain.SelmerGroup
import TauCeti.RingTheory.Valuation.RootMonic

/-!
# The bad primes of a Weierstrass curve, and the arithmetic away from them

Let `W : y² = f(x) = x³ + a₂x² + a₄x + a₆` be an elliptic curve in characteristic `≠ 2` normal
form over a field `K`, and let `R` be a Dedekind domain with fraction field `K`. The **bad
primes** of `W` over `R` are the primes dividing `2` or the discriminant `Δ`, together with those
occurring in a denominator of `a₂`, `a₄` or `a₆`. There are finitely many of them, and away from
them the Weierstrass equation is as well behaved as it can be.

The arithmetic of Step 6 of the weak Mordell–Weil theorem needs less than goodness. At a prime `w`
of the ring of integers of a field factor `K[X] ⧸ (p)` of the étale algebra, it needs `a₂`, `a₄`
and `a₆` to be integral at the prime of `R` under `w`, which makes the root `θ` of `f` integral at
`w`, and it needs the derivative `f' θ = 3θ² + 2a₂θ + a₄` to be a `w`-unit. The latter holds as
soon as the discriminant `disc f` of the cubic is a unit at the prime under `w`: evaluating at `θ`
the Bézout identity between `f` and `f'` exhibits `disc f` as `f' θ` times an explicit quadratic
in `θ`, and both factors are integral (`Valuation.map_cubic_deriv_eq_one`). Since
`Δ = 16 · disc f`, this holds at every good prime, but also at a prime above `2` at which `f` has
separable reduction.

The lemmas here take exactly these hypotheses at the prime under `w`. They combine into
`even_valuationOfNeZero_sub_root`: at such a prime the valuation of `x - θ` is **even**, for
`(x, y)` any point of `W` with `f x ≠ 0`. That is the arithmetic content of Step 6 with all the
group theory stripped away; `TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.SelmerGroupA`
puts the group theory back and reads it as membership in a Selmer group.

## Main definitions

* `WeierstrassCurve.Affine.badPrimes`: the set `S` of bad primes of `W` over `R`.
* `WeierstrassCurve.Affine.ringOfIntegersFactor`: the integral closure of `R` in the field factor
  `K[X] ⧸ (p)`, a Dedekind domain with fraction field `K[X] ⧸ (p)`.

## Main results

* `WeierstrassCurve.Affine.finite_badPrimes`: there are only finitely many bad primes.
* `WeierstrassCurve.Affine.valuation_discr_f_eq_one_of_notMem_badPrimes`: at a good prime,
  `disc f` is a unit.
* `WeierstrassCurve.Affine.valuation_root_le_one`: if `a₂`, `a₄`, `a₆` are integral at the prime
  under `w`, the root `θ` is integral at `w`.
* `WeierstrassCurve.Affine.valuation_deriv_root_le_one`: then `f' θ` is integral at `w` too.
* `WeierstrassCurve.Affine.valuation_deriv_root_eq_one`: if moreover `disc f` is a unit there,
  `f' θ` is a `w`-unit.
* `WeierstrassCurve.Affine.valuation_cofactor_eq_one`: if `f' θ` is a `w`-unit, `x` is integral
  and `x - θ` is not a unit, then the cofactor of `x - θ` in the Weierstrass equation is a unit.
* `WeierstrassCurve.Affine.valuation_projFactor_torsion_eq_one`: at a root `x` of `f` with `f' x`
  a unit, the component of the corrected `2`-torsion representative `x - T + fCofactor x` is a
  unit.
* `WeierstrassCurve.Affine.even_valuationOfNeZero_sub_root`: if `f' θ` is a `w`-unit, the
  valuation of `x - θ` is even. This is the arithmetic core of Step 6.

## Implementation notes

The `Valuation` lemmas about the monic cubic `t³ + at² + bt + c` used to live here as `private`
plumbing, on the grounds that this file and its sequel were their only consumers. The two public
statements now sit with the general statements they specialize, in
`TauCeti.RingTheory.Valuation.RootMonic`, and are used from here as `Valuation` dot notation; one
of them, `map_cubic_eq_of_one_lt`, has since gained a consumer outside `MordellWeil/`. The
coefficient helper they share stays `private` there.
The `Core` section still lives in this file rather than in `SelmerGroupA` because it is the last
consumer of the `RingOfIntegers` estimates above.

## Provenance

Adapted, with the author's proofs, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeakMordellWeil.lean`, sections `BadPrimes`, `RingOfIntegers` and `Core` (the
source's `Cubic` section is now in `TauCeti.RingTheory.Valuation.RootMonic`). The
source carries its own `HeightOneSpectrum.below`; at our Mathlib pin that map is
`HeightOneSpectrum.under`, which is used here instead. The source is written against Lean
`v4.32.0`; this is a forward port.

The per-prime hypotheses (integral `a₂`, `a₄`, `a₆` and a unit `disc f`, or a unit `f' θ`, resp.
`f' x`, at the prime under `w`, in place of `w` not lying above a bad prime) and the Bézout
identity with `disc f` rather than `Δ` on the right follow the later revision `3bfe124` of the
same project, same file and sections.
-/

public section

open Polynomial

namespace WeierstrassCurve.Affine

open IsDedekindDomain

-- Step 6 needs neither `DecidableEq K` nor the group structure on points, so the variables are
-- declared afresh rather than inherited from the `x - T` map.
variable {K : Type*} [Field K] (W : Affine K)

/- Notation local to this file and its sequel: for a monic irreducible factor `p` of `f`,
`𝕃 p` is the field factor `K[X] ⧸ (p)` of `W.A`, `ι p : K →+* 𝕃 p` is the canonical embedding,
and `θ p` is the image of the root `T` of `f` in `𝕃 p`. -/
local notation:max "𝕃" p:max => AdjoinRoot (p : K[X])
local notation:max "ι" p:max => algebraMap K (AdjoinRoot (p : K[X]))
local notation:max "θ" p:max => AdjoinRoot.root (p : K[X])

/-- The set of **bad primes** of `R`: those dividing `2` or the discriminant of `W`, and those
occurring in a denominator of `a₂`, `a₄` or `a₆` (the latter three are the supports of the
coefficients in the sense of `IsDedekindDomain.HeightOneSpectrum.Support`). Away from these, the
`x - T` map lands in the `2`-Selmer group. -/
def badPrimes (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] :
    Set (HeightOneSpectrum R) :=
  {v | v.valuation K 2 ≠ 1} ∪ {v | v.valuation K W.Δ ≠ 1} ∪ HeightOneSpectrum.Support R W.a₂ ∪
    HeightOneSpectrum.Support R W.a₄ ∪ HeightOneSpectrum.Support R W.a₆

/-- There are only finitely many bad primes: `2` and `W.Δ` are nonzero, and the support of any
element of `K` is finite. -/
lemma finite_badPrimes (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K]
    [IsFractionRing R K] [W.IsElliptic] [W.IsCharNeTwoNF] : (W.badPrimes R).Finite :=
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two W)
  ((((HeightOneSpectrum.finite_setOfPred_valuation_ne_one h2).union
    (HeightOneSpectrum.finite_setOfPred_valuation_ne_one W.isUnit_Δ.ne_zero)).union
      (HeightOneSpectrum.Support.finite R W.a₂)).union
        (HeightOneSpectrum.Support.finite R W.a₄)).union
          (HeightOneSpectrum.Support.finite R W.a₆)

section BadPrimes

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  {v : HeightOneSpectrum R}

/-- **Membership in `badPrimes`, as an arithmetic condition.** A prime is bad exactly when `2` or
`Δ` fails to be a unit there, or one of `a₂`, `a₄`, `a₆` fails to be integral there.

This is the characteristic lemma for `badPrimes`: the five projections below are read off from it,
and it is what a consumer should use rather than unfolding the nested unions in the definition. -/
@[simp]
lemma mem_badPrimes_iff :
    v ∈ W.badPrimes R ↔
      v.valuation K 2 ≠ 1 ∨ v.valuation K W.Δ ≠ 1 ∨ 1 < v.valuation K W.a₂ ∨
        1 < v.valuation K W.a₄ ∨ 1 < v.valuation K W.a₆ := by
  simp only [badPrimes, Set.mem_union, Set.mem_ofPred_eq, HeightOneSpectrum.Support]
  tauto

/-- The five good-prime conditions, packaged: at a prime that is not bad, `2` and `Δ` are units
and `a₂`, `a₄`, `a₆` are integral. -/
lemma notMem_badPrimes_iff :
    v ∉ W.badPrimes R ↔
      v.valuation K 2 = 1 ∧ v.valuation K W.Δ = 1 ∧ v.valuation K W.a₂ ≤ 1 ∧
        v.valuation K W.a₄ ≤ 1 ∧ v.valuation K W.a₆ ≤ 1 := by
  rw [W.mem_badPrimes_iff R]
  push Not
  rfl

/-- At a good prime, `a₂` is integral: a prime where it is not lies in its support, hence is
bad. -/
lemma valuation_a₂_le_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.a₂ ≤ 1 :=
  ((W.notMem_badPrimes_iff R).mp hv).2.2.1

/-- At a good prime, `a₄` is integral. -/
lemma valuation_a₄_le_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.a₄ ≤ 1 :=
  ((W.notMem_badPrimes_iff R).mp hv).2.2.2.1

/-- At a good prime, `a₆` is integral. -/
lemma valuation_a₆_le_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.a₆ ≤ 1 :=
  ((W.notMem_badPrimes_iff R).mp hv).2.2.2.2

/-- At a good prime, the discriminant is a unit. This is the half of `badPrimes` that makes the
reduction of `W` nonsingular there. -/
lemma valuation_Δ_eq_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.Δ = 1 :=
  ((W.notMem_badPrimes_iff R).mp hv).2.1

/-- At a good prime, `2` is a unit: the `2`-component of `badPrimes`, read off like the other
four. -/
lemma valuation_two_eq_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K 2 = 1 :=
  ((W.notMem_badPrimes_iff R).mp hv).1

/-- At a good prime, the discriminant of the cubic `f` is a unit, since `Δ = 16 · disc f` and both
`Δ` and `2` are units there. This is the form in which Step 6 consumes the goodness of a prime. -/
lemma valuation_discr_f_eq_one_of_notMem_badPrimes [W.IsCharNeTwoNF] (hv : v ∉ W.badPrimes R) :
    v.valuation K W.f.discr = 1 := by
  have h16 : v.valuation K 16 = 1 := by
    rw [show (16 : K) = 2 ^ 4 by norm_num, map_pow,
      W.valuation_two_eq_one_of_notMem_badPrimes R hv, one_pow]
  have hΔ := W.valuation_Δ_eq_one_of_notMem_badPrimes R hv
  rwa [W.Δ_eq_sixteen_mul_discr_f, map_mul, h16, one_mul] at hΔ

end BadPrimes

section RingOfIntegers

variable (R : Type*) [CommRing R] [Algebra R K]

/-- The ring of integers of the field factor `K[X] ⧸ (p)` over `R`. -/
noncomputable abbrev ringOfIntegersFactor (p : W.f.Factors) : Type _ :=
  integralClosure R (𝕃 p)

section

variable [IsDomain R] [IsFractionRing R K]

/-- A field factor is the fraction field of its ring of integers over any domain `R` with
fraction field `K`. The finite extension need not be separable. -/
instance isFractionRing_ringOfIntegersFactor (p : W.f.Factors) :
    IsFractionRing (W.ringOfIntegersFactor R p) (𝕃 p) :=
  IsIntegralClosure.isFractionRing_of_finite_extension R K (𝕃 p) _

/-- The ring of integers of a field factor is torsion-free over `R`, as `R` embeds into it. -/
instance instIsTorsionFreeRingOfIntegersFactor (p : W.f.Factors) :
    Module.IsTorsionFree R (W.ringOfIntegersFactor R p) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  have hinj : Function.Injective (algebraMap R (𝕃 p)) := by
    rw [IsScalarTower.algebraMap_eq R K (𝕃 p)]
    exact (ι p).injective.comp (IsFractionRing.injective R K)
  exact fun a b hab ↦ hinj (congrArg Subtype.val hab)

end

variable [IsDedekindDomain R] [IsFractionRing R K]

/-- The ring of integers of a field factor is a Dedekind domain: it is the integral closure of
`R` in a finite separable extension of the fraction field `K`. -/
instance isDedekindDomain_ringOfIntegersFactor [W.IsElliptic] [W.IsCharNeTwoNF]
    (p : W.f.Factors) : IsDedekindDomain (W.ringOfIntegersFactor R p) :=
  have := AdjoinRoot.isSeparable_of_separable (separable_f W) p
  IsIntegralClosure.isDedekindDomain R K (𝕃 p) _

/-- The `w`-adic valuation of an element of `K` is the valuation at the prime of `R` under `w`,
raised to the ramification index. -/
lemma valuation_algebraMap_eq [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor R p)) (z : K) :
    (HeightOneSpectrum.under R w).valuation K z ^
        ((HeightOneSpectrum.under R w).asIdeal.ramificationIdx' w.asIdeal) =
      w.valuation (𝕃 p) (ι p z) := by
  -- Mathlib's `valuation_liesOver` states the exponent as `w.asIdeal.ramificationIdx R`, which
  -- `ramificationIdx'_eq_ramificationIdx` identifies with the `ramificationIdx'` used here.
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ w.asIdeal
    (HeightOneSpectrum.under R w).ne_bot]
  exact HeightOneSpectrum.valuation_liesOver _ _ _ z

/-- If `z` is integral at the prime under `w`, then it is integral at `w`. -/
lemma valuation_algebraMap_le_one [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor R p)) {z : K}
    (hz : (HeightOneSpectrum.under R w).valuation K z ≤ 1) :
    w.valuation (𝕃 p) (ι p z) ≤ 1 := by
  rw [← W.valuation_algebraMap_eq R p w z]
  simpa using pow_le_pow_left' hz _

/-- `θ` satisfies the Weierstrass cubic in the field factor `K[X] ⧸ (p)`. -/
lemma root_cubic_eq_zero (p : W.f.Factors) :
    θ p ^ 3 + ι p W.a₂ * θ p ^ 2 + ι p W.a₄ * θ p + ι p W.a₆ = 0 := by
  have hz : AdjoinRoot.mk (p : K[X]) W.f = 0 := AdjoinRoot.mk_eq_zero.mpr p.dvd
  simpa [f, AdjoinRoot.algebraMap_eq] using hz

/-- The cofactor `f / (X - x)`, computed in the field factor `K[X] ⧸ (p)`. -/
lemma mk_fCofactor_eq (p : W.f.Factors) (x : K) :
    AdjoinRoot.mk (p : K[X]) (W.fCofactor x) =
      θ p ^ 2 + (ι p x + ι p W.a₂) * θ p + (ι p x ^ 2 + ι p W.a₂ * ι p x + ι p W.a₄) := by
  simp only [fCofactor, map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    ← AdjoinRoot.algebraMap_eq]

variable [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
  {w : HeightOneSpectrum (W.ringOfIntegersFactor R p)}
  (ha₂ : (HeightOneSpectrum.under R w).valuation K W.a₂ ≤ 1)
  (ha₄ : (HeightOneSpectrum.under R w).valuation K W.a₄ ≤ 1)
  (ha₆ : (HeightOneSpectrum.under R w).valuation K W.a₆ ≤ 1)

include ha₂ ha₄ ha₆

/-- If `a₂`, `a₄` and `a₆` are integral at the prime under `w`, then the root `θ` is integral at
`w`: it satisfies the monic cubic `f`, whose coefficients are integral at `w`. -/
lemma valuation_root_le_one : w.valuation (𝕃 p) (θ p) ≤ 1 :=
  Valuation.le_one_of_root_cubic _ (W.valuation_algebraMap_le_one R p w ha₂)
    (W.valuation_algebraMap_le_one R p w ha₄) (W.valuation_algebraMap_le_one R p w ha₆)
    (W.root_cubic_eq_zero p)

omit ha₂ ha₄ ha₆ in
/-- An element of `K` with trivial valuation at the prime under `w` has trivial valuation
at `w`. -/
lemma valuation_algebraMap_eq_one {z : K}
    (hz : (HeightOneSpectrum.under R w).valuation K z = 1) :
    w.valuation (𝕃 p) (ι p z) = 1 := by
  rw [← W.valuation_algebraMap_eq R p w z, hz, one_pow]

/-- If `a₂`, `a₄` and `a₆` are integral at the prime under `w`, then so is
`f' θ = 3θ² + 2a₂θ + a₄`: it is a polynomial in `θ` and the coefficients. -/
lemma valuation_deriv_root_le_one :
    w.valuation (𝕃 p) (3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄) ≤ 1 := by
  have h₂ := W.valuation_algebraMap_le_one R p w ha₂
  have h₄ := W.valuation_algebraMap_le_one R p w ha₄
  have hθ := W.valuation_root_le_one R p ha₂ ha₄ ha₆
  have h₃ : (3 : 𝕃 p) ∈ (w.valuation (𝕃 p)).integer := ofNat_mem _ 3
  have h₂' : (2 : 𝕃 p) ∈ (w.valuation (𝕃 p)).integer := ofNat_mem _ 2
  exact add_mem (add_mem (mul_mem h₃ (pow_mem hθ 2)) (mul_mem (mul_mem h₂' h₂) hθ)) h₄

/-- If `a₂`, `a₄` and `a₆` are integral and `disc f` is a unit at the prime under `w`, then
`f' θ = 3θ² + 2a₂θ + a₄` is a unit at `w` (`Valuation.map_cubic_deriv_eq_one`). The hypothesis is
on `disc f` rather than on `Δ = 16 · disc f`, so this applies at primes above `2` as well. -/
lemma valuation_deriv_root_eq_one
    (hd : (HeightOneSpectrum.under R w).valuation K W.f.discr = 1) :
    w.valuation (𝕃 p) (3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄) = 1 := by
  refine Valuation.map_cubic_deriv_eq_one _ (W.valuation_algebraMap_le_one R p w ha₂)
    (W.valuation_algebraMap_le_one R p w ha₄) (W.valuation_algebraMap_le_one R p w ha₆)
    (W.root_cubic_eq_zero p) ?_
  have h := W.valuation_algebraMap_eq_one R p hd
  rw [W.discr_f] at h
  simpa only [map_sub, map_add, map_mul, map_pow, map_ofNat] using h

/-- If `a₂`, `a₄` and `a₆` are integral at the prime under `w` and `f' θ = 3θ² + 2a₂θ + a₄` is a
`w`-unit, if `x` is `w`-integral and `x - θ` is not a `w`-unit, then the cofactor
`θ² + (x + a₂)θ + (x² + a₂x + a₄)` is a `w`-unit: it differs from `f' θ` by the multiple
`(x - θ)(x + 2θ + a₂)` of `x - θ`.

Stated in the shape `mk_fCofactor_eq` produces, so that it applies to the image of `fCofactor x`
in the field factor without reshaping. -/
lemma valuation_cofactor_eq_one {x : K}
    (hderiv : w.valuation (𝕃 p) (3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄) = 1)
    (hx : w.valuation (𝕃 p) (ι p x) ≤ 1)
    (hlt : w.valuation (𝕃 p) (ι p x - θ p) < 1) :
    w.valuation (𝕃 p) (θ p ^ 2 + (ι p x + ι p W.a₂) * θ p
      + (ι p x ^ 2 + ι p W.a₂ * ι p x + ι p W.a₄)) = 1 := by
  set L := 𝕃 p
  set ν := w.valuation L
  set t := θ p
  set s := algebraMap K L x
  set A₂ := algebraMap K L W.a₂
  set A := algebraMap K L W.a₄
  have hA₂ : ν A₂ ≤ 1 := W.valuation_algebraMap_le_one R p w ha₂
  have ht : ν t ≤ 1 := W.valuation_root_le_one R p ha₂ ha₄ ha₆
  have h2t : s + 2 * t + A₂ ∈ ν.integer :=
    add_mem (add_mem hx (mul_mem (ofNat_mem _ 2) ht)) hA₂
  have hlt' : ν ((s - t) * (s + 2 * t + A₂)) < ν (3 * t ^ 2 + 2 * A₂ * t + A) := by
    rw [hderiv, map_mul]
    exact (mul_le_of_le_one_right' h2t).trans_lt hlt
  rw [show t ^ 2 + (s + A₂) * t + (s ^ 2 + A₂ * s + A)
      = (s - t) * (s + 2 * t + A₂) + (3 * t ^ 2 + 2 * A₂ * t + A) by ring,
    ν.map_add_eq_of_lt_right hlt', hderiv]

/-- If `x` is a root of `f`, if `a₂`, `a₄` and `a₆` are integral at the prime under `w` and
`f' x = 3x² + 2a₂x + a₄` is a unit there, then the `p`-component of the `x - T` representative is
a unit at `w`.

Both `x` and `θ` are roots of `f`, so `x - θ` times the cofactor is `0` and, `L` being a field,
one of the two factors vanishes. If `x = θ` the component is `f' x`; if the cofactor vanishes the
component is `x - θ`, and `f' x = (x - θ)(2x + θ + a₂)`. Either way it is a unit. -/
lemma valuation_projFactor_torsion_eq_one {x : K} (hx : W.f.eval x = 0)
    (hdx : (HeightOneSpectrum.under R w).valuation K (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 1) :
    w.valuation (𝕃 p) (ι p x - θ p + AdjoinRoot.mk (p : K[X]) (W.fCofactor x)) = 1 := by
  rw [W.mk_fCofactor_eq p x]
  set L := 𝕃 p
  set ν := w.valuation L
  set t := θ p
  set s := algebraMap K L x with hsdef
  set A₂ := algebraMap K L W.a₂ with hA₂def
  set A := algebraMap K L W.a₄ with hAdef
  set B := algebraMap K L W.a₆ with hBdef
  have hA₂ : ν A₂ ≤ 1 := W.valuation_algebraMap_le_one R p w ha₂
  have hA : ν A ≤ 1 := W.valuation_algebraMap_le_one R p w ha₄
  have hB : ν B ≤ 1 := W.valuation_algebraMap_le_one R p w ha₆
  have ht : ν t ≤ 1 := W.valuation_root_le_one R p ha₂ ha₄ ha₆
  have hderiv : ν (3 * s ^ 2 + 2 * A₂ * s + A) = 1 := by
    simpa only [map_add, map_mul, map_pow, map_ofNat] using
      W.valuation_algebraMap_eq_one R p (w := w) hdx
  -- `x` is a root of the cubic too, hence integral at `w`
  have hs : s ^ 3 + A₂ * s ^ 2 + A * s + B = 0 := by
    rw [hsdef, hA₂def, hAdef, hBdef, ← W.map_eval_f, hx, map_zero]
  have hs1 : ν s ≤ 1 := ν.le_one_of_root_cubic hA₂ hA hB hs
  have hprod : (s - t) * (t ^ 2 + (s + A₂) * t + (s ^ 2 + A₂ * s + A)) = 0 := by
    linear_combination hs - W.root_cubic_eq_zero p
  rcases mul_eq_zero.mp hprod with h0 | h0
  · -- `x = θ`: the component is `f' x`
    rw [h0, zero_add, show t ^ 2 + (s + A₂) * t + (s ^ 2 + A₂ * s + A)
        = 3 * s ^ 2 + 2 * A₂ * s + A by linear_combination -(t + 2 * s + A₂) * h0, hderiv]
  · -- the cofactor vanishes: the component is `x - θ`, and `f' x = (x - θ)(2x + θ + a₂)`
    rw [h0, add_zero]
    have hst : s - t ∈ ν.integer := sub_mem hs1 ht
    have h2t : 2 * s + t + A₂ ∈ ν.integer :=
      add_mem (add_mem (mul_mem (ofNat_mem _ 2) hs1) ht) hA₂
    refine ν.eq_one_of_mul_eq_one hst h2t ?_
    rw [show (s - t) * (2 * s + t + A₂) = 3 * s ^ 2 + 2 * A₂ * s + A by linear_combination -h0,
      hderiv]

end RingOfIntegers

section Core

variable [W.IsElliptic] [W.IsCharNeTwoNF]
  (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  (p : W.f.Factors)
  {x y : K} (h : W.Equation x y) (hx : W.f.eval x ≠ 0)
  (u : (AdjoinRoot (p : K[X]))ˣ)
  (hu : (u : AdjoinRoot (p : K[X])) =
    algebraMap K (AdjoinRoot (p : K[X])) x - AdjoinRoot.root (p : K[X]))
  (w : HeightOneSpectrum (W.ringOfIntegersFactor R p))
  (ha₂ : (HeightOneSpectrum.under R w).valuation K W.a₂ ≤ 1)
  (ha₄ : (HeightOneSpectrum.under R w).valuation K W.a₄ ≤ 1)
  (ha₆ : (HeightOneSpectrum.under R w).valuation K W.a₆ ≤ 1)
  -- `f' θ` is a `w`-unit; the local notation for `θ` is not available in a `variable` command
  (hderiv : w.valuation (AdjoinRoot (p : K[X]))
    (3 * AdjoinRoot.root (p : K[X]) ^ 2
      + 2 * algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * AdjoinRoot.root (p : K[X])
      + algebraMap K (AdjoinRoot (p : K[X])) W.a₄) = 1)

include h hx hu ha₂ ha₄ ha₆

/-- Non-integral case: `x` has a pole at the prime of `R` under `w`.

The coefficients `a₂`, `a₄`, `a₆` and the root `θ` are `w`-integral, so `1 < ν x` makes the
leading term of the cubic dominate: `ν (f x) = ν x ³`, hence `ν y ² = ν x ³`. Also `ν θ ≤ 1 < ν x`
gives `ν (x - θ) = ν x`. Therefore `ν (x - θ) = ν (y / x) ²` is an even power. -/
private lemma even_valuationOfNeZero_sub_root_of_one_lt
    (hx' : 1 < w.valuation (𝕃 p) (ι p x)) :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
  set L := 𝕃 p
  set ν := w.valuation L
  have hx0 : algebraMap K L x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hx'
    exact absurd hx' (by simp)
  have hx0' : ν (algebraMap K L x) ≠ 0 := ν.ne_zero_iff.mpr hx0
  have hy0 : algebraMap K L y ≠ 0 := (_root_.map_ne_zero _).mpr (W.y_ne_zero_of_eval_f_ne_zero h hx)
  -- the Weierstrass equation, transported to `L`
  have heq : (algebraMap K L y) ^ 2 = algebraMap K L x ^ 3 +
      algebraMap K L W.a₂ * algebraMap K L x ^ 2 +
      algebraMap K L W.a₄ * algebraMap K L x + algebraMap K L W.a₆ := by
    rw [← W.map_eval_f, (equation_iff_eval_f_eq_sq W x y).mp h, map_pow]
  have hval : ν (algebraMap K L y) ^ 2 = ν (algebraMap K L x) ^ 3 := by
    rw [← map_pow, heq,
      ν.map_cubic_eq_of_one_lt (W.valuation_algebraMap_le_one R p w ha₂)
      (W.valuation_algebraMap_le_one R p w ha₄) (W.valuation_algebraMap_le_one R p w ha₆) hx']
  -- `ν (x - θ) = ν x`, since `θ` is integral and `x` is not
  have hu' : ν (u : L) = ν (algebraMap K L x) := by
    rw [hu]
    exact Valuation.map_sub_eq_of_lt_left _ ((W.valuation_root_le_one R p ha₂ ha₄ ha₆).trans_lt hx')
  have hkey : ν (u : L) = ν ((Units.mk0 _ (div_ne_zero hy0 hx0) : Lˣ) : L) ^ 2 := by
    rw [hu', Units.val_mk0, map_div₀, div_pow, hval, eq_div_iff (pow_ne_zero 2 hx0'), mul_comm]
    exact (pow_succ _ 2).symm
  simpa using w.dvd_toAdd_valuationOfNeZero hkey

include hderiv in
/-- Integral case: `x` is integral at the prime of `R` under `w`.

Over `L` the Weierstrass equation factors as `y ² = (x - θ) * c` with cofactor
`c = x ² + θ x + θ ² + a₂ (x + θ) + a₄`. If `x - θ` is a `w`-unit there is nothing to do.
Otherwise `ν (x - θ) < 1`, and since `c = (x - θ) * (x + 2 θ + a₂) + f' θ` with `f' θ` a `w`-unit,
the cofactor is a `w`-unit. Hence `ν (x - θ) = ν y ²` is an even power. -/
private lemma even_valuationOfNeZero_sub_root_of_le_one
    (hx' : w.valuation (𝕃 p) (ι p x) ≤ 1) :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
  set L := 𝕃 p
  set ν := w.valuation L
  set t := θ p
  set A₂ := algebraMap K L W.a₂ with hA₂def
  set A := algebraMap K L W.a₄ with hAdef
  have ht : ν t ≤ 1 := W.valuation_root_le_one R p ha₂ ha₄ ha₆
  -- `y ² = (x - θ) * (x ² + θ x + θ ² + a₂ (x + θ) + a₄)` over `L`
  have heqL : (algebraMap K L y) ^ 2 = algebraMap K L x ^ 3 + A₂ * algebraMap K L x ^ 2 +
      A * algebraMap K L x + algebraMap K L W.a₆ := by
    rw [hA₂def, hAdef, ← W.map_eval_f, (equation_iff_eval_f_eq_sq W x y).mp h, map_pow]
  have hfac : (u : L) * (t ^ 2 + (algebraMap K L x + A₂) * t
        + (algebraMap K L x ^ 2 + A₂ * algebraMap K L x + A)) =
      (algebraMap K L y) ^ 2 := by
    rw [hu]
    linear_combination -W.root_cubic_eq_zero p - heqL
  have hu1 : ν (u : L) ≤ 1 := by rw [hu]; exact ν.map_sub_le hx' ht
  by_cases hlt : ν (u : L) = 1
  · -- `x - θ` is a unit, so its valuation is trivially even
    have hkey : ν (u : L) = ν ((1 : Lˣ) : L) ^ 2 := by rw [Units.val_one, map_one, one_pow, hlt]
    simpa using w.dvd_toAdd_valuationOfNeZero hkey
  -- otherwise `w` divides `x - θ`, and then it cannot divide the cofactor
  replace hlt : ν (u : L) < 1 := lt_of_le_of_ne hu1 hlt
  rw [hu] at hlt
  have hcof : ν (t ^ 2 + (algebraMap K L x + A₂) * t
      + (algebraMap K L x ^ 2 + A₂ * algebraMap K L x + A)) = 1 :=
    W.valuation_cofactor_eq_one R p ha₂ ha₄ ha₆ hderiv hx' hlt
  have hy0 : algebraMap K L y ≠ 0 := (_root_.map_ne_zero _).mpr (W.y_ne_zero_of_eval_f_ne_zero h hx)
  have hkey : ν (u : L) = ν ((Units.mk0 _ hy0 : Lˣ) : L) ^ 2 := by
    rw [Units.val_mk0, ← map_pow, ← hfac, map_mul, hcof, mul_one]
  simpa using w.dvd_toAdd_valuationOfNeZero hkey

include hderiv in
/-- The arithmetic core of Step 6, generic case, with all the group theory stripped away: for
`(x, y)` on `W` with `f x ≠ 0`, and `w` a prime of the ring of integers of the field factor
`K[X] ⧸ (p)` such that `a₂`, `a₄` and `a₆` are integral at the prime under `w` and `f' θ` is a
`w`-unit, the `w`-adic valuation of `x - θ` is even. By `valuation_deriv_root_eq_one`, the last
condition holds when `disc f` is a unit at the prime under `w`.

The proof splits on whether `x` has a pole at the prime of `R` under `w`. -/
lemma even_valuationOfNeZero_sub_root :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
  by_cases hx' : 1 < w.valuation (𝕃 p) (ι p x)
  · exact W.even_valuationOfNeZero_sub_root_of_one_lt R p h hx u hu w ha₂ ha₄ ha₆ hx'
  · exact W.even_valuationOfNeZero_sub_root_of_le_one R p h hx u hu w ha₂ ha₄ ha₆ hderiv
      (not_lt.mp hx')

end Core

end WeierstrassCurve.Affine

end
