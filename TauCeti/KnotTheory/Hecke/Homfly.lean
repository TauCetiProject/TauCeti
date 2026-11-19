/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Hecke.Ocneanu
public import TauCeti.KnotTheory.Homfly.Alexander
public import TauCeti.RingTheory.Localization.Away.Basic
import TauCeti.Algebra.Polynomial.Laurent.Regular
import Mathlib.Tactic.LinearCombination

/-!
# Comparison between Hecke Markov braid traces and the HOMFLY polynomial

This file connects the normalized universal Hecke braid trace `MarkovBraid.heckeTrace` and its
Ocneanu-trace specialization to `MarkovBraid.reducedHomfly`, and establishes regularity across both
apparent zero-factor loci before evaluating specializations there:

1. **Two-variable HOMFLY comparison (`MarkovBraid.eval₂_reducedHomfly_eq_heckeTrace`)**: whenever
   `u = q - q⁻¹` is a unit and `(C, l, z)` satisfies both Markov normalization equations for a
   Markov trace `τ`, evaluating `β.reducedHomfly K` at `(l⁻¹, u)` equals `β.heckeTrace τ C l`.
2. **Regularity across `l⁻¹ - l = 0` (`C = 0`, Alexander specialization)**: in
   `heckeUniversalRing K` (inverting `(q - q⁻¹)(a - a⁻¹)`), the normalized Ocneanu trace equals the
   image under `heckeAlexanderInclusion K` (injective over any commutative ring `K`) of the regular
   element `MarkovBraid.heckeAlexanderRegular K` in `heckeAlexanderRegularRing K` (inverting
   `q - q⁻¹` alone); lifting at `a = ±1` specializes cleanly, and `a = 1`, `q = s⁻¹` recovers
   `MarkovBraid.normalizedBurauAlexander s`.
3. **Regularity across `q - q⁻¹ = 0` (`q = ±1`, classical specialization)**: when
   `l₀⁻¹ - l₀ = C₀ * (T 1 - T (-1))` in `LaurentPolynomial K`, the generic HOMFLY specialization in
   `Localization.Away (C₀ * (T 1 - T (-1)))` equals the image under `heckeZeroFactorLift C₀`
   (injective over any commutative ring `K`) of `heckeTrace` over `Localization.Away C₀`, lifting
   to any `q` with `eval₂ φ q C₀` invertible (including `q = ±1`).

## Main definitions

* `TauCeti.heckeDeltaQ`, `TauCeti.heckeDeltaA`, `TauCeti.heckeAlexanderRegularRing`,
  `TauCeti.heckeUniversalRing`, `TauCeti.heckeAlexanderInclusion`, `TauCeti.heckeDeltaQUnit`,
  `TauCeti.heckeUniversalQ`, `TauCeti.heckeUniversalA`, `TauCeti.heckeUniversalC`,
  `TauCeti.heckeUniversalZ`, and `TauCeti.MarkovBraid.heckeAlexanderRegular`.
* `TauCeti.heckeZeroFactorLift`, `TauCeti.heckeZeroFactorZ`, and `TauCeti.heckeZeroFactorDeltaUnit`.

## Main results

* `TauCeti.MarkovBraid.eval₂_reducedHomfly_eq_heckeTrace` and
  `TauCeti.heckeBraidInvariant_eq_eval₂_reducedHomfly`.
* `TauCeti.heckeAlexanderInclusion_injective`,
  `TauCeti.MarkovBraid.heckeAlexanderInclusion_heckeAlexanderRegular`,
  `TauCeti.MarkovBraid.lift_heckeAlexanderRegular_eq_eval₂_reducedHomfly`, and
  `TauCeti.MarkovBraid.lift_heckeAlexanderRegular_eq_normalizedBurauAlexander`.
* `TauCeti.heckeZeroFactorLift_injective`,
  `TauCeti.MarkovBraid.heckeZeroFactorLift_heckeTrace_eq_eval₂_reducedHomfly`, and
  `TauCeti.MarkovBraid.lift_heckeTrace_heckeZeroFactorZ_eq_heckeTrace`.

## References

* P. Freyd, D. Yetter, J. Hoste, W. B. R. Lickorish, K. Millett, and A. Ocneanu, *A new polynomial
  invariant of knots and links*, Bull. Amer. Math. Soc. 12 (1985), 239–246.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*, Ann. of
  Math. 126 (1987), 335–388, Sections 5–9.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapters 8 and 15.
-/

public noncomputable section

namespace TauCeti

open BraidGroup KnotTheory LaurentPolynomial
open InfiniteTypeAHeckeAlgebra (IsMarkovTrace ocneanuTrace isMarkovTrace_ocneanuTrace)

/-! ### Comparison with the two-variable HOMFLY polynomial -/

section HomflyComparison

variable {K R : Type*} [Field K] [CommRing R]

/-- Under `C * l * z = 1` and `C * l⁻¹ * (z - u) = 1` for `u : Rˣ`, evaluating `homflyUnknot K` at
`(l⁻¹, u)` gives the unlink factor `C`. -/
theorem KnotTheory.eval₂_homflyUnknot_of_heckeNormalization (φ : K →+* R) {u l : Rˣ} {C z : R}
    (hpos : C * (l : R) * z = 1) (hneg : C * (↑l⁻¹ : R) * (z - (u : R)) = 1) :
    eval₂ (eval₂ φ u) l⁻¹ (homflyUnknot K) = C := by
  have hCu := mul_eq_val_inv_sub_of_heckeNormalization hpos hneg
  have heval : eval₂ (eval₂ φ u) l⁻¹ (homflyUnknot K) = ((↑l⁻¹ : R) - l) * ↑u⁻¹ := by
    simp [homflyUnknot_def, map_mul, map_sub]
  rw [heval, ← hCu, mul_assoc, Units.mul_inv, mul_one]

namespace MarkovBraid

/-- **Comparison between `reducedHomfly` and `heckeTrace`.** Whenever `u = q - q⁻¹` is a unit in `R`
and `(C, l, z)` solves both Markov normalization equations for a Markov trace `τ`, evaluating
`β.reducedHomfly K` at outer variable `l⁻¹` and inner variable `u` recovers `β.heckeTrace τ C l`. -/
theorem eval₂_reducedHomfly_eq_heckeTrace (φ : K →+* R) {q u l : Rˣ} {C z : R}
    {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R} (hτ : IsMarkovTrace z τ)
    (hu : (u : R) = (q : R) - ↑q⁻¹) (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1) (β : MarkovBraid) :
    eval₂ (eval₂ φ u) l⁻¹ (β.reducedHomfly K) = β.heckeTrace τ C l := by
  set e : LaurentPolynomial (LaurentPolynomial K) →+* R := eval₂ (eval₂ φ u) l⁻¹
  have heU : e (homflyUnknot K) = C :=
    KnotTheory.eval₂_homflyUnknot_of_heckeNormalization φ hpos (hu.symm ▸ hneg)
  have heq := eq_heckeTrace_of_skein hτ hpos hneg (F := fun γ ↦ e (γ.reducedHomfly K))
    (fun _ _ h ↦ congrArg e (h.reducedHomfly_eq K))
    (fun n c i ↦ by
      simpa only [e, one_mul, map_sub, map_mul, eval₂_T, zpow_one, zpow_neg_one, inv_inv, eval₂_C,
        hu] using congrArg e (reducedHomfly_skein K (1 : BraidGroup (n + 1)) c i))
    (fun n b ↦ by rw [reducedHomfly_strandIncl, map_mul, heU]) (by simp [e])
  exact congrFun heq β

/-- Evaluating the unreduced HOMFLY polynomial `β.homfly K` at `(l⁻¹, q - q⁻¹)` gives
`C * β.heckeTrace τ C l`. -/
theorem eval₂_homfly_eq_mul_heckeTrace (φ : K →+* R) {q u l : Rˣ} {C z : R}
    {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R} (hτ : IsMarkovTrace z τ)
    (hu : (u : R) = (q : R) - ↑q⁻¹) (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1) (β : MarkovBraid) :
    eval₂ (eval₂ φ u) l⁻¹ (β.homfly K) = C * β.heckeTrace τ C l := by
  rw [← homflyUnknot_mul_reducedHomfly, map_mul,
    KnotTheory.eval₂_homflyUnknot_of_heckeNormalization φ hpos (hu.symm ▸ hneg),
    β.eval₂_reducedHomfly_eq_heckeTrace φ hτ hu hpos hneg]

/-- Canonical specialization of `eval₂_reducedHomfly_eq_heckeTrace` to `ocneanuTrace R q z`. -/
theorem eval₂_reducedHomfly_eq_heckeTrace_ocneanuTrace (φ : K →+* R) {q u l : Rˣ} {C z : R}
    (hu : (u : R) = (q : R) - ↑q⁻¹) (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1) (β : MarkovBraid) :
    eval₂ (eval₂ φ u) l⁻¹ (β.reducedHomfly K) = β.heckeTrace (ocneanuTrace R q z) C l :=
  β.eval₂_reducedHomfly_eq_heckeTrace φ (isMarkovTrace_ocneanuTrace z) hu hpos hneg

end MarkovBraid

/-- On `Quot MarkovEquiv`, `heckeBraidInvariant` equals the descended specialization of
`reducedHomfly K` whenever `u = q - q⁻¹` is a unit. -/
theorem heckeBraidInvariant_eq_eval₂_reducedHomfly (φ : K →+* R) {q u l : Rˣ} {C z : R}
    {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R} (hτ : IsMarkovTrace z τ)
    (hu : (u : R) = (q : R) - ↑q⁻¹) (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1) (x : Quot MarkovEquiv) :
    heckeBraidInvariant hτ C l hpos hneg x =
      Quot.lift (fun β : MarkovBraid ↦ eval₂ (eval₂ φ u) l⁻¹ (β.reducedHomfly K))
        (fun _ _ h ↦ congrArg _ (h.reducedHomfly_eq K)) x := by
  rcases Quot.exists_rep x with ⟨β, rfl⟩
  rw [heckeBraidInvariant_mk]
  exact (β.eval₂_reducedHomfly_eq_heckeTrace φ hτ hu hpos hneg).symm

end HomflyComparison

/-! ### Regularity and evaluation across zero-factor specializations -/

section ZeroFactorRegularity

/-! #### 1. Regularity across `l⁻¹ - l = 0` (`C = 0`, Alexander specialization) -/

section AlexanderRegularity

section CommRing

variable (K : Type*) [CommRing K]

/-- The inner Hecke skein factor `q - q⁻¹` inside `K[q, q⁻¹][a, a⁻¹]`. -/
def heckeDeltaQ : LaurentPolynomial (LaurentPolynomial K) := C (T 1 - T (-1))

/-- Defining formula for `heckeDeltaQ K`. -/
theorem heckeDeltaQ_def : heckeDeltaQ K = C (T 1 - T (-1)) := (rfl)

/-- Evaluating `heckeDeltaQ K` along `f` at `a` gives `f (T 1 - T (-1))`. -/
@[simp]
theorem eval₂_heckeDeltaQ {R : Type*} [CommRing R] (f : LaurentPolynomial K →+* R) (a : Rˣ) :
    eval₂ f a (heckeDeltaQ K) = f (T 1 - T (-1)) := by
  simp [heckeDeltaQ_def]

/-- The outer writhe factor `a - a⁻¹ = l⁻¹ - l` inside `K[q, q⁻¹][a, a⁻¹]`. -/
def heckeDeltaA : LaurentPolynomial (LaurentPolynomial K) := T 1 - T (-1)

/-- Defining formula for `heckeDeltaA K`. -/
theorem heckeDeltaA_def : heckeDeltaA K = T 1 - T (-1) := (rfl)

/-- Evaluating `heckeDeltaA K` along `f` at `a` gives `a - a⁻¹`. -/
@[simp]
theorem eval₂_heckeDeltaA {R : Type*} [CommRing R] (f : LaurentPolynomial K →+* R) (a : Rˣ) :
    eval₂ f a (heckeDeltaA K) = (a : R) - ↑a⁻¹ := by
  simp [heckeDeltaA_def, map_sub]

/-- Over a nontrivial commutative ring `K`, `heckeDeltaQ K` is nonzero. -/
@[simp]
theorem heckeDeltaQ_ne_zero [Nontrivial K] : heckeDeltaQ K ≠ 0 := fun h ↦
  have hc : (T 1 - T (-1) : LaurentPolynomial K) = 0 := by
    simpa using congrArg (eval₂ (RingHom.id (LaurentPolynomial K)) 1) h
  T_sub_T_ne_zero (by decide) hc

/-- Over a nontrivial commutative ring `K`, `heckeDeltaA K` is nonzero. -/
@[simp]
theorem heckeDeltaA_ne_zero [Nontrivial K] : heckeDeltaA K ≠ 0 :=
  T_sub_T_ne_zero (by decide)

/-- The localization `K[q, q⁻¹][a, a⁻¹][(q - q⁻¹)⁻¹]`, regular at `a = ±1` (`C = 0`). -/
abbrev heckeAlexanderRegularRing : Type _ := Localization.Away (heckeDeltaQ K)

/-- The universal localization `K[q, q⁻¹][a, a⁻¹][((q - q⁻¹)(a - a⁻¹))⁻¹]`. -/
abbrev heckeUniversalRing : Type _ := Localization.Away (heckeDeltaQ K * heckeDeltaA K)

/-- Canonical localization map from `heckeAlexanderRegularRing K` into `heckeUniversalRing K`. -/
def heckeAlexanderInclusion : heckeAlexanderRegularRing K →+* heckeUniversalRing K :=
  IsLocalization.Away.awayToAwayRight (heckeDeltaQ K) (heckeDeltaA K)

/-- Defining formula for `heckeAlexanderInclusion K`. -/
theorem heckeAlexanderInclusion_def :
    heckeAlexanderInclusion K =
      IsLocalization.Away.awayToAwayRight (heckeDeltaQ K) (heckeDeltaA K) := (rfl)

/-- `heckeAlexanderInclusion K` commutes with `algebraMap` from `K[q, q⁻¹][a, a⁻¹]`. -/
@[simp]
theorem heckeAlexanderInclusion_algebraMap (x : LaurentPolynomial (LaurentPolynomial K)) :
    heckeAlexanderInclusion K
        (algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeAlexanderRegularRing K) x) =
      algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeUniversalRing K) x :=
  IsLocalization.Away.awayToAwayRight_eq (heckeDeltaQ K) (heckeDeltaA K) x

/-- Over every commutative ring `K`, `heckeAlexanderInclusion K` is injective, ensuring uniqueness
of regular extensions across `a - a⁻¹ = 0`. -/
theorem heckeAlexanderInclusion_injective :
    Function.Injective (heckeAlexanderInclusion K) :=
  IsLocalization.Away.awayToAwayRight_injective (heckeDeltaQ K) (heckeDeltaA K)
    (by rw [heckeDeltaA_def]; exact isRegular_T_sub_T (by decide))

/-- The unit `q - q⁻¹` inside `heckeAlexanderRegularRing K`. -/
def heckeDeltaQUnit : (heckeAlexanderRegularRing K)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := heckeAlexanderRegularRing K) (heckeDeltaQ K)).unit

/-- Coercing `heckeDeltaQUnit K` gives `algebraMap _ _ (heckeDeltaQ K)`. -/
@[simp]
theorem val_heckeDeltaQUnit :
    (heckeDeltaQUnit K : heckeAlexanderRegularRing K) =
      algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeAlexanderRegularRing K)
        (heckeDeltaQ K) := IsUnit.unit_spec _

/-- The inverse of `heckeDeltaQUnit K` is `IsLocalization.Away.invSelf (heckeDeltaQ K)`. -/
@[simp]
theorem val_inv_heckeDeltaQUnit :
    (↑(heckeDeltaQUnit K)⁻¹ : heckeAlexanderRegularRing K) =
      IsLocalization.Away.invSelf (heckeDeltaQ K) := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [val_heckeDeltaQUnit]
  exact IsLocalization.Away.mul_invSelf (heckeDeltaQ K)

/-- The generic Hecke parameter `q` as a unit in `heckeUniversalRing K`. -/
def heckeUniversalQ : (heckeUniversalRing K)ˣ :=
  Units.map ((algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeUniversalRing K)).comp
    C).toMonoidHom (genericUnit K)

/-- Coercing `heckeUniversalQ K` gives the image of `C (T 1)`. -/
@[simp]
theorem val_heckeUniversalQ :
    (heckeUniversalQ K : heckeUniversalRing K) =
      algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeUniversalRing K) (C (T 1)) := by
  simp [heckeUniversalQ]

/-- The inverse of `heckeUniversalQ K` coerces to the image of `C (T (-1))`. -/
@[simp]
theorem val_inv_heckeUniversalQ :
    (↑(heckeUniversalQ K)⁻¹ : heckeUniversalRing K) =
      algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeUniversalRing K) (C (T (-1))) := by
  simp [heckeUniversalQ]

/-- Mapping `heckeDeltaQUnit K` into `heckeUniversalRing K` gives
`heckeUniversalQ K - (heckeUniversalQ K)⁻¹`. -/
theorem val_map_heckeAlexanderInclusion_heckeDeltaQUnit :
    (↑(Units.map (heckeAlexanderInclusion K).toMonoidHom (heckeDeltaQUnit K)) :
        heckeUniversalRing K) =
      (heckeUniversalQ K : heckeUniversalRing K) - ↑(heckeUniversalQ K)⁻¹ := by
  simp [heckeDeltaQ_def]

/-- The generic outer HOMFLY variable `a = l⁻¹` as a unit in `heckeUniversalRing K`. -/
def heckeUniversalA : (heckeUniversalRing K)ˣ :=
  Units.map (algebraMap (LaurentPolynomial (LaurentPolynomial K))
    (heckeUniversalRing K)).toMonoidHom (genericUnit (LaurentPolynomial K))

/-- Coercing `heckeUniversalA K` gives the image of `T 1`. -/
@[simp]
theorem val_heckeUniversalA :
    (heckeUniversalA K : heckeUniversalRing K) =
      algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeUniversalRing K) (T 1) := by
  simp [heckeUniversalA]

/-- The inverse of `heckeUniversalA K` coerces to the image of `T (-1)`. -/
@[simp]
theorem val_inv_heckeUniversalA :
    (↑(heckeUniversalA K)⁻¹ : heckeUniversalRing K) =
      algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeUniversalRing K) (T (-1)) := by
  simp [heckeUniversalA]

/-- The generic unlink factor `C = (a - a⁻¹) * (q - q⁻¹)⁻¹` in `heckeUniversalRing K`. -/
def heckeUniversalC : heckeUniversalRing K :=
  algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeUniversalRing K) (heckeDeltaA K) *
    ↑((Units.map (heckeAlexanderInclusion K).toMonoidHom (heckeDeltaQUnit K))⁻¹)

/-- Defining formula for `heckeUniversalC K`. -/
theorem heckeUniversalC_def :
    heckeUniversalC K =
      algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeUniversalRing K) (heckeDeltaA K) *
        ↑((Units.map (heckeAlexanderInclusion K).toMonoidHom (heckeDeltaQUnit K))⁻¹) := (rfl)

/-- The generic Ocneanu parameter `z = (a - a⁻¹)⁻¹ * (q - q⁻¹) * a` in `heckeUniversalRing K`. -/
def heckeUniversalZ : heckeUniversalRing K :=
  (algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeUniversalRing K) (heckeDeltaQ K) *
      IsLocalization.Away.invSelf (heckeDeltaQ K * heckeDeltaA K)) *
    ↑(Units.map (heckeAlexanderInclusion K).toMonoidHom (heckeDeltaQUnit K)) *
    (heckeUniversalA K : heckeUniversalRing K)

/-- Defining formula for `heckeUniversalZ K`. -/
theorem heckeUniversalZ_def :
    heckeUniversalZ K =
      (algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeUniversalRing K) (heckeDeltaQ K) *
          IsLocalization.Away.invSelf (heckeDeltaQ K * heckeDeltaA K)) *
        ↑(Units.map (heckeAlexanderInclusion K).toMonoidHom (heckeDeltaQUnit K)) *
        (heckeUniversalA K : heckeUniversalRing K) := (rfl)

/-- The generic parameters `(heckeUniversalC K, (heckeUniversalA K)⁻¹, heckeUniversalZ K)` satisfy
both Markov normalization equations in `heckeUniversalRing K`. -/
theorem heckeUniversalNormalization :
    heckeUniversalC K * ↑((heckeUniversalA K)⁻¹ : (heckeUniversalRing K)ˣ) *
        heckeUniversalZ K = 1 ∧
      heckeUniversalC K * ↑(((heckeUniversalA K)⁻¹ : (heckeUniversalRing K)ˣ)⁻¹) *
        (heckeUniversalZ K -
          ((heckeUniversalQ K : heckeUniversalRing K) - ↑(heckeUniversalQ K)⁻¹)) = 1 := by
  set ι := algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeUniversalRing K)
  set u_u := Units.map (heckeAlexanderInclusion K).toMonoidHom (heckeDeltaQUnit K)
  set invΔa := ι (heckeDeltaQ K) * IsLocalization.Away.invSelf (heckeDeltaQ K * heckeDeltaA K)
  have hΔa_inv : invΔa * ι (heckeDeltaA K) = 1 := by
    rw [show invΔa * ι (heckeDeltaA K) = ι (heckeDeltaQ K * heckeDeltaA K) *
      IsLocalization.Away.invSelf (heckeDeltaQ K * heckeDeltaA K) by simp [invΔa, map_mul]; ring]
    exact IsLocalization.Away.mul_invSelf _
  exact heckeNormalization_of_mul_eq_val_inv_sub (c := invΔa * ↑u_u)
    (by
      rw [heckeUniversalC_def]
      linear_combination (u_u : heckeUniversalRing K) * ↑u_u⁻¹ * hΔa_inv + u_u.mul_inv)
    (by
      rw [inv_inv, ← val_map_heckeAlexanderInclusion_heckeDeltaQUnit K, heckeUniversalC_def]
      have ha_sub : (heckeUniversalA K : heckeUniversalRing K) - ↑(heckeUniversalA K)⁻¹ =
          ι (heckeDeltaA K) := by simp [ι, heckeDeltaA_def]
      linear_combination ι (heckeDeltaA K) * u_u.inv_mul - ha_sub)
    (by rw [inv_inv]; rfl)

/-- When `u = q - q⁻¹` is a unit in `R`, any evaluation map `q ↦ q`, `a ↦ a` sends `heckeDeltaQ K`
to a unit in `R`. -/
theorem isUnit_eval₂_heckeDeltaQ {R : Type*} [CommRing R] (φ : K →+* R) {q u : Rˣ} (a : Rˣ)
    (hu : (u : R) = (q : R) - ↑q⁻¹) : IsUnit (eval₂ (eval₂ φ q) a (heckeDeltaQ K)) := by
  simp [← hu]

end CommRing

section Field

variable (K : Type*) [Field K]

/-- The regular two-variable element in `heckeAlexanderRegularRing K` extending the universal
normalized Hecke trace across `a - a⁻¹ = 0` (`l = ±1`, `C = 0`). -/
def MarkovBraid.heckeAlexanderRegular (β : MarkovBraid) : heckeAlexanderRegularRing K :=
  eval₂ (eval₂ (algebraMap K (heckeAlexanderRegularRing K)) (heckeDeltaQUnit K))
    (Units.map (algebraMap (LaurentPolynomial (LaurentPolynomial K))
      (heckeAlexanderRegularRing K)).toMonoidHom (genericUnit (LaurentPolynomial K)))
    (β.reducedHomfly K)

/-- Defining formula for `MarkovBraid.heckeAlexanderRegular K β`. -/
theorem MarkovBraid.heckeAlexanderRegular_def (β : MarkovBraid) :
    β.heckeAlexanderRegular K =
      eval₂ (eval₂ (algebraMap K (heckeAlexanderRegularRing K)) (heckeDeltaQUnit K))
        (Units.map (algebraMap (LaurentPolynomial (LaurentPolynomial K))
          (heckeAlexanderRegularRing K)).toMonoidHom (genericUnit (LaurentPolynomial K)))
        (β.reducedHomfly K) := (rfl)

/-- Markov-equivalent braids have the same regular element `heckeAlexanderRegular K`. -/
theorem MarkovEquiv.heckeAlexanderRegular_eq {β γ : MarkovBraid} (h : MarkovEquiv β γ) :
    β.heckeAlexanderRegular K = γ.heckeAlexanderRegular K := by
  rw [MarkovBraid.heckeAlexanderRegular_def, MarkovBraid.heckeAlexanderRegular_def,
    h.reducedHomfly_eq K]

/-- On the unlink `⟨n, 1⟩`, `heckeAlexanderRegular K` evaluates to
`((a - a⁻¹) * (q - q⁻¹)⁻¹) ^ n`. -/
@[simp]
theorem MarkovBraid.heckeAlexanderRegular_one (n : ℕ) :
    heckeAlexanderRegular K ⟨n, 1⟩ =
      (algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeAlexanderRegularRing K)
          (heckeDeltaA K) *
        IsLocalization.Away.invSelf (heckeDeltaQ K)) ^ n := by
  simp [MarkovBraid.heckeAlexanderRegular_def, homflyUnknot_def, heckeDeltaA_def, map_sub]

/-- Adding an uncrossed strand multiplies `heckeAlexanderRegular K` by
`(a - a⁻¹) * (q - q⁻¹)⁻¹`. -/
@[simp]
theorem MarkovBraid.heckeAlexanderRegular_strandIncl {n : ℕ} (b : BraidGroup (n + 1)) :
    heckeAlexanderRegular K ⟨n + 1, BraidGroup.strandIncl b⟩ =
      (algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeAlexanderRegularRing K)
          (heckeDeltaA K) *
        IsLocalization.Away.invSelf (heckeDeltaQ K)) *
        heckeAlexanderRegular K ⟨n, b⟩ := by
  simp [MarkovBraid.heckeAlexanderRegular_def, homflyUnknot_def, heckeDeltaA_def, map_sub]

/-- `heckeAlexanderRegular K` satisfies the oriented HOMFLY skein relation in every braid
context. -/
theorem MarkovBraid.heckeAlexanderRegular_skein {n : ℕ} (b c : BraidGroup (n + 1)) (i : Fin n) :
    algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeAlexanderRegularRing K) (T 1) *
        heckeAlexanderRegular K ⟨n, b * BraidGroup.sigma (n := n + 1) i * c⟩ -
      algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeAlexanderRegularRing K) (T (-1)) *
        heckeAlexanderRegular K ⟨n, b * (BraidGroup.sigma (n := n + 1) i)⁻¹ * c⟩ =
      algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeAlexanderRegularRing K)
          (heckeDeltaQ K) *
        heckeAlexanderRegular K ⟨n, b * c⟩ := by
  have hs := congrArg
    (eval₂ (eval₂ (algebraMap K (heckeAlexanderRegularRing K)) (heckeDeltaQUnit K))
      (Units.map (algebraMap (LaurentPolynomial (LaurentPolynomial K))
        (heckeAlexanderRegularRing K)).toMonoidHom (genericUnit (LaurentPolynomial K))))
    (reducedHomfly_skein K b c i)
  simp only [map_sub, map_mul, eval₂_T, zpow_one, zpow_neg_one, eval₂_C] at hs
  simp only [MarkovBraid.heckeAlexanderRegular_def]
  simpa using hs

/-- Transporting `β.heckeAlexanderRegular K` along any ring homomorphism out of
`heckeAlexanderRegularRing K` pushes both Laurent evaluation variables through `f`. -/
theorem MarkovBraid.map_heckeAlexanderRegular {R : Type*} [CommRing R]
    (f : heckeAlexanderRegularRing K →+* R) (β : MarkovBraid) :
    f (β.heckeAlexanderRegular K) =
      eval₂ (eval₂ (f.comp (algebraMap K (heckeAlexanderRegularRing K)))
          (Units.map f.toMonoidHom (heckeDeltaQUnit K)))
        (Units.map (f.comp (algebraMap (LaurentPolynomial (LaurentPolynomial K))
          (heckeAlexanderRegularRing K))).toMonoidHom (genericUnit (LaurentPolynomial K)))
        (β.reducedHomfly K) := by
  rw [MarkovBraid.heckeAlexanderRegular_def, hom_eval₂]
  congr 2
  refine RingHom.ext fun p ↦ ?_
  simp only [RingHom.comp_apply, hom_eval₂, RingHom.toMonoidHom_eq_coe]

/-- **Regularity of the universal normalized Hecke trace across `l⁻¹ - l = 0` (`C = 0`).** Inside
`heckeUniversalRing K`, the normalized Ocneanu braid trace with generic parameters equals the image
under `heckeAlexanderInclusion K` of `β.heckeAlexanderRegular K`. -/
theorem MarkovBraid.heckeAlexanderInclusion_heckeAlexanderRegular (β : MarkovBraid) :
    heckeAlexanderInclusion K (β.heckeAlexanderRegular K) =
      β.heckeTrace (ocneanuTrace (heckeUniversalRing K) (heckeUniversalQ K) (heckeUniversalZ K))
        (heckeUniversalC K) (heckeUniversalA K)⁻¹ := by
  obtain ⟨hpos, hneg⟩ := heckeUniversalNormalization K
  have hK : (heckeAlexanderInclusion K).comp (algebraMap K (heckeAlexanderRegularRing K)) =
      algebraMap K (heckeUniversalRing K) := by
    ext x
    simp [IsScalarTower.algebraMap_apply K (LaurentPolynomial (LaurentPolynomial K))
      (heckeAlexanderRegularRing K), IsScalarTower.algebraMap_apply K
      (LaurentPolynomial (LaurentPolynomial K)) (heckeUniversalRing K)]
  have hA : Units.map ((heckeAlexanderInclusion K).comp
        (algebraMap (LaurentPolynomial (LaurentPolynomial K))
          (heckeAlexanderRegularRing K))).toMonoidHom (genericUnit (LaurentPolynomial K)) =
      ((heckeUniversalA K)⁻¹)⁻¹ := by ext; simp [inv_inv, val_heckeUniversalA]
  rw [β.map_heckeAlexanderRegular K (heckeAlexanderInclusion K), hK, hA]
  exact β.eval₂_reducedHomfly_eq_heckeTrace_ocneanuTrace _
    (val_map_heckeAlexanderInclusion_heckeDeltaQUnit K) hpos hneg

/-- **General evaluation of `MarkovBraid.heckeAlexanderRegular`.** For `φ : K →+* R`, outer unit
`a : Rˣ` (including `a = ±1`), and `u = q - q⁻¹`, lifting `β.heckeAlexanderRegular K` along
`IsLocalization.Away.lift (heckeDeltaQ K)` evaluates `β.reducedHomfly K` at `(a, u)`. -/
theorem MarkovBraid.lift_heckeAlexanderRegular_eq_eval₂_reducedHomfly {R : Type*} [CommRing R]
    (φ : K →+* R) (q a u : Rˣ) (hu : (u : R) = (q : R) - ↑q⁻¹) (β : MarkovBraid) :
    IsLocalization.Away.lift (heckeDeltaQ K) (isUnit_eval₂_heckeDeltaQ K φ a hu)
        (β.heckeAlexanderRegular K) =
      eval₂ (eval₂ φ u) a (β.reducedHomfly K) := by
  set g : LaurentPolynomial (LaurentPolynomial K) →+* R := eval₂ (eval₂ φ q) a
  set L : heckeAlexanderRegularRing K →+* R :=
    IsLocalization.Away.lift (heckeDeltaQ K) (isUnit_eval₂_heckeDeltaQ K φ a hu)
  have hcomp : L.comp
      (algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeAlexanderRegularRing K)) = g :=
    IsLocalization.Away.lift_comp _ _
  have hK : L.comp (algebraMap K (heckeAlexanderRegularRing K)) = φ := by
    rw [IsScalarTower.algebraMap_eq K (LaurentPolynomial (LaurentPolynomial K))
      (heckeAlexanderRegularRing K), ← RingHom.comp_assoc, hcomp]
    ext x
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply K (LaurentPolynomial K)
      (LaurentPolynomial (LaurentPolynomial K)) x, ← C_eq_algebraMap, ← C_eq_algebraMap]
    simp [g]
  have hu_eq : Units.map L.toMonoidHom (heckeDeltaQUnit K) = u := by
    ext; simp [L, hu]
  have ha_eq : Units.map g.toMonoidHom (genericUnit (LaurentPolynomial K)) = a := by ext; simp [g]
  rw [β.map_heckeAlexanderRegular K L, hcomp, hK, hu_eq, ha_eq]

/-- **Evaluation of the regular extension at `l = 1` (`C = 0`, Alexander specialization).** Given
`φ : K →+* R` and `s : Rˣ` with `s⁻¹ - s` invertible (`q = s⁻¹`, `a = 1`), lifting
`β.heckeAlexanderRegular K` recovers `β.normalizedBurauAlexander s`. -/
theorem MarkovBraid.lift_heckeAlexanderRegular_eq_normalizedBurauAlexander {R : Type*}
    [CommRing R] (φ : K →+* R) (s : Rˣ)
    (hg : IsUnit (eval₂ (eval₂ φ s⁻¹) 1 (heckeDeltaQ K))) (β : MarkovBraid) :
    IsLocalization.Away.lift (heckeDeltaQ K) hg (β.heckeAlexanderRegular K) =
      β.normalizedBurauAlexander s := by
  have hu : (hg.unit : R) = ((s⁻¹ : Rˣ) : R) - (s : R) := by
    simp [IsUnit.unit_spec]
  exact (β.lift_heckeAlexanderRegular_eq_eval₂_reducedHomfly K φ s⁻¹ 1 hg.unit hu).trans
    (β.eval₂_reducedHomfly_eq_normalizedBurauAlexander φ s hg.unit hu)

end Field

end AlexanderRegularity

/-! #### 2. Regularity across `q - q⁻¹ = 0` (`q = ±1`, classical specialization) -/

section ClassicalRegularity

section CommRing

variable {K : Type*} [CommRing K]

/-- Canonical localization map from `Localization.Away C₀` into
`Localization.Away (C₀ * (T 1 - T (-1)))`. -/
def heckeZeroFactorLift (C₀ : LaurentPolynomial K) :
    Localization.Away C₀ →+* Localization.Away (C₀ * (T 1 - T (-1))) :=
  IsLocalization.Away.awayToAwayRight C₀ (T 1 - T (-1))

/-- Defining formula for `heckeZeroFactorLift C₀`. -/
theorem heckeZeroFactorLift_def (C₀ : LaurentPolynomial K) :
    heckeZeroFactorLift C₀ = IsLocalization.Away.awayToAwayRight C₀ (T 1 - T (-1)) := (rfl)

/-- `heckeZeroFactorLift C₀` commutes with `algebraMap` from `LaurentPolynomial K`. -/
@[simp]
theorem heckeZeroFactorLift_algebraMap (C₀ a : LaurentPolynomial K) :
    heckeZeroFactorLift C₀ (algebraMap (LaurentPolynomial K) (Localization.Away C₀) a) =
      algebraMap (LaurentPolynomial K) (Localization.Away (C₀ * (T 1 - T (-1)))) a :=
  IsLocalization.Away.awayToAwayRight_eq C₀ (T 1 - T (-1)) a

/-- Over every commutative ring `K` and for every `C₀ : LaurentPolynomial K`,
`heckeZeroFactorLift C₀` is injective, ensuring uniqueness of regular extensions across
`q - q⁻¹ = 0`. -/
theorem heckeZeroFactorLift_injective (C₀ : LaurentPolynomial K) :
    Function.Injective (heckeZeroFactorLift C₀) :=
  IsLocalization.Away.awayToAwayRight_injective C₀ (T 1 - T (-1))
    (isRegular_T_sub_T (by decide))

/-- The regular Ocneanu trace parameter `C₀⁻¹ * l₀⁻¹` inside `Localization.Away C₀`. -/
def heckeZeroFactorZ (C₀ : LaurentPolynomial K) (l₀ : (LaurentPolynomial K)ˣ) :
    Localization.Away C₀ :=
  IsLocalization.Away.invSelf (S := Localization.Away C₀) C₀ *
    algebraMap (LaurentPolynomial K) (Localization.Away C₀) (↑l₀⁻¹ : LaurentPolynomial K)

/-- Defining formula for `heckeZeroFactorZ C₀ l₀`. -/
theorem heckeZeroFactorZ_def (C₀ : LaurentPolynomial K) (l₀ : (LaurentPolynomial K)ˣ) :
    heckeZeroFactorZ C₀ l₀ =
      IsLocalization.Away.invSelf (S := Localization.Away C₀) C₀ *
        algebraMap (LaurentPolynomial K) (Localization.Away C₀) (↑l₀⁻¹ : LaurentPolynomial K) :=
  (rfl)

/-- The unit `T 1 - T (-1) = q - q⁻¹` inside `Localization.Away (C₀ * (T 1 - T (-1)))`. -/
def heckeZeroFactorDeltaUnit (C₀ : LaurentPolynomial K) :
    (Localization.Away (C₀ * (T 1 - T (-1))))ˣ :=
  (IsLocalization.Away.isUnit_of_dvd (S := Localization.Away (C₀ * (T 1 - T (-1))))
    (C₀ * (T 1 - T (-1))) (dvd_mul_left _ _)).unit

/-- Coercing `heckeZeroFactorDeltaUnit C₀` gives the image of `T 1 - T (-1)`. -/
@[simp]
theorem val_heckeZeroFactorDeltaUnit (C₀ : LaurentPolynomial K) :
    (heckeZeroFactorDeltaUnit C₀ : Localization.Away (C₀ * (T 1 - T (-1)))) =
      algebraMap (LaurentPolynomial K) (Localization.Away (C₀ * (T 1 - T (-1))))
        (T 1 - T (-1)) := IsUnit.unit_spec _

/-- The inverse of `heckeZeroFactorDeltaUnit C₀` is
`algebraMap _ _ C₀ * invSelf (C₀ * (T 1 - T (-1)))`. -/
@[simp]
theorem val_inv_heckeZeroFactorDeltaUnit (C₀ : LaurentPolynomial K) :
    (↑(heckeZeroFactorDeltaUnit C₀)⁻¹ : Localization.Away (C₀ * (T 1 - T (-1)))) =
      algebraMap (LaurentPolynomial K) (Localization.Away (C₀ * (T 1 - T (-1)))) C₀ *
        IsLocalization.Away.invSelf (C₀ * (T 1 - T (-1))) := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [val_heckeZeroFactorDeltaUnit, ← mul_assoc, ← map_mul, mul_comm _ C₀]
  exact IsLocalization.Away.mul_invSelf (C₀ * (T 1 - T (-1)))

/-- In `Localization.Away C₀`, any `l₀ : (LaurentPolynomial K)ˣ` satisfying
`l₀⁻¹ - l₀ = C₀ * (T 1 - T (-1))` solves both Markov normalization equations with
`z = heckeZeroFactorZ C₀ l₀`. -/
theorem heckeZeroFactorNormalization {C₀ : LaurentPolynomial K} {l₀ : (LaurentPolynomial K)ˣ}
    (hl₀ : (↑l₀⁻¹ : LaurentPolynomial K) - (l₀ : LaurentPolynomial K) = C₀ * (T 1 - T (-1))) :
    algebraMap (LaurentPolynomial K) (Localization.Away C₀) C₀ *
        ↑(Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom l₀) *
        heckeZeroFactorZ C₀ l₀ = 1 ∧
      algebraMap (LaurentPolynomial K) (Localization.Away C₀) C₀ *
        ↑((Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom l₀)⁻¹) *
        (heckeZeroFactorZ C₀ l₀ -
          (↑(Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom
              (genericUnit K)) -
            ↑(Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom
              (genericUnit K))⁻¹)) = 1 :=
  heckeNormalization_of_mul_eq_val_inv_sub
    (by rw [mul_comm]; exact IsLocalization.Away.mul_invSelf C₀)
    (by simpa [map_sub, map_mul] using
      congrArg (algebraMap (LaurentPolynomial K) (Localization.Away C₀)) hl₀.symm)
    (by simp [heckeZeroFactorZ_def])

/-- **Transport of the `(C₀, l₀)` Ocneanu `heckeTrace` out of `Localization.Away C₀`.** For any
`φ : K →+* R`, `q : Rˣ`, and inverse `c` of `eval₂ φ q C₀`, lifting the `(C₀, l₀)` Ocneanu
`heckeTrace` from `Localization.Away C₀` via `IsLocalization.Away.lift C₀` produces the normalized
Ocneanu braid trace at `q` (including at `q = ±1`). When `l₀⁻¹ - l₀ = C₀ * (T 1 - T (-1))`, this
evaluates the unique regular extension of `reducedHomfly` across `q - q⁻¹ = 0`. -/
theorem MarkovBraid.lift_heckeTrace_heckeZeroFactorZ_eq_heckeTrace {R : Type*} [CommRing R]
    {C₀ : LaurentPolynomial K} (l₀ : (LaurentPolynomial K)ˣ) (φ : K →+* R) (q : Rˣ) {c : R}
    (hc : c * eval₂ φ q C₀ = 1) (β : MarkovBraid) :
    IsLocalization.Away.lift C₀ (IsUnit.of_mul_eq_one_right c hc)
        (β.heckeTrace (ocneanuTrace (Localization.Away C₀)
            (Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom
              (genericUnit K)) (heckeZeroFactorZ C₀ l₀))
          (algebraMap (LaurentPolynomial K) (Localization.Away C₀) C₀)
          (Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom l₀)) =
      β.heckeTrace (ocneanuTrace R q (c * eval₂ φ q (↑l₀⁻¹ : LaurentPolynomial K)))
        (eval₂ φ q C₀) (Units.map (eval₂ φ q).toMonoidHom l₀) := by
  let hunit : IsUnit (eval₂ φ q C₀) := IsUnit.of_mul_eq_one_right c hc
  have hLC : IsLocalization.Away.lift C₀ hunit
      (algebraMap (LaurentPolynomial K) (Localization.Away C₀) C₀) = eval₂ φ q C₀ :=
    IsLocalization.Away.lift_eq C₀ hunit C₀
  have hLc : IsLocalization.Away.lift C₀ hunit
      (IsLocalization.Away.invSelf (S := Localization.Away C₀) C₀) = c := by
    rw [IsLocalization.Away.lift, IsLocalization.Away.invSelf, IsLocalization.lift_mk'_spec,
      map_one, mul_comm, hc]
  have hq_eq : Units.map (IsLocalization.Away.lift C₀ hunit).toMonoidHom
      (Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom
        (genericUnit K)) = q := by ext; simp
  have hl_eq : Units.map (IsLocalization.Away.lift C₀ hunit).toMonoidHom
      (Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom l₀) =
        Units.map (eval₂ φ q).toMonoidHom l₀ := by ext; simp
  have hLz : IsLocalization.Away.lift C₀ hunit (heckeZeroFactorZ C₀ l₀) =
      c * eval₂ φ q (↑l₀⁻¹ : LaurentPolynomial K) := by
    rw [heckeZeroFactorZ_def, map_mul, hLc, IsLocalization.Away.lift_eq]
  rw [β.map_heckeTrace_ocneanuTrace (IsLocalization.Away.lift C₀ hunit), hLC, hLz, hq_eq, hl_eq]

end CommRing

section Field

variable {K : Type*} [Field K]

/-- **Regularity across `q - q⁻¹ = 0` (`q = ±1`).** Whenever `l₀⁻¹ - l₀ = C₀ * (T 1 - T (-1))` in
`LaurentPolynomial K` (uniquely determined in `Localization.Away C₀` by
`heckeZeroFactorLift_injective C₀`), the generic HOMFLY specialization in
`Localization.Away (C₀ * (T 1 - T (-1)))` equals the image under `heckeZeroFactorLift C₀` of the
regular normalized Ocneanu trace in `Localization.Away C₀`. -/
theorem MarkovBraid.heckeZeroFactorLift_heckeTrace_eq_eval₂_reducedHomfly
    {C₀ : LaurentPolynomial K} {l₀ : (LaurentPolynomial K)ˣ}
    (hl₀ : (↑l₀⁻¹ : LaurentPolynomial K) - (l₀ : LaurentPolynomial K) = C₀ * (T 1 - T (-1)))
    (β : MarkovBraid) :
    heckeZeroFactorLift C₀
        (β.heckeTrace (ocneanuTrace (Localization.Away C₀)
            (Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom
              (genericUnit K)) (heckeZeroFactorZ C₀ l₀))
          (algebraMap (LaurentPolynomial K) (Localization.Away C₀) C₀)
          (Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom l₀)) =
      eval₂ (eval₂ (algebraMap K (Localization.Away (C₀ * (T 1 - T (-1)))))
          (heckeZeroFactorDeltaUnit C₀))
        (Units.map (algebraMap (LaurentPolynomial K)
          (Localization.Away (C₀ * (T 1 - T (-1))))).toMonoidHom l₀)⁻¹
        (β.reducedHomfly K) := by
  obtain ⟨hpos₀, hneg₀⟩ := heckeZeroFactorNormalization hl₀
  set q₀ := Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom
    (genericUnit K)
  set l_S₀ := Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom l₀
  have hpos : heckeZeroFactorLift C₀
        (algebraMap (LaurentPolynomial K) (Localization.Away C₀) C₀) *
      ↑(Units.map (heckeZeroFactorLift C₀).toMonoidHom l_S₀) *
      heckeZeroFactorLift C₀ (heckeZeroFactorZ C₀ l₀) = 1 := by
    simpa using congrArg (heckeZeroFactorLift C₀) hpos₀
  have hneg : heckeZeroFactorLift C₀
        (algebraMap (LaurentPolynomial K) (Localization.Away C₀) C₀) *
      ↑((Units.map (heckeZeroFactorLift C₀).toMonoidHom l_S₀)⁻¹) *
      (heckeZeroFactorLift C₀ (heckeZeroFactorZ C₀ l₀) -
        (↑(Units.map (heckeZeroFactorLift C₀).toMonoidHom q₀) -
          ↑(Units.map (heckeZeroFactorLift C₀).toMonoidHom q₀)⁻¹)) = 1 := by
    simpa using congrArg (heckeZeroFactorLift C₀) hneg₀
  have hu : (heckeZeroFactorDeltaUnit C₀ : Localization.Away (C₀ * (T 1 - T (-1)))) =
      ↑(Units.map (heckeZeroFactorLift C₀).toMonoidHom q₀) -
        ↑(Units.map (heckeZeroFactorLift C₀).toMonoidHom q₀)⁻¹ := by simp [q₀, map_sub]
  have hl_eq : Units.map (heckeZeroFactorLift C₀).toMonoidHom l_S₀ =
      Units.map (algebraMap (LaurentPolynomial K)
        (Localization.Away (C₀ * (T 1 - T (-1))))).toMonoidHom l₀ := by ext; simp [l_S₀]
  rw [β.map_heckeTrace_ocneanuTrace (heckeZeroFactorLift C₀),
    ← β.eval₂_reducedHomfly_eq_heckeTrace_ocneanuTrace
      (algebraMap K (Localization.Away (C₀ * (T 1 - T (-1))))) hu hpos hneg, hl_eq]

end Field

end ClassicalRegularity

end ZeroFactorRegularity

end TauCeti
