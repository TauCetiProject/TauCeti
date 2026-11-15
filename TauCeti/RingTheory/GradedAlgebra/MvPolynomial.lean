/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Generator
public import TauCeti.RingTheory.GradedAlgebra.Localization.Away

/-!
# Homogeneous unit degrees and shift classes for weighted polynomial rings

Give `MvPolynomial σ R` its weighted grading `weightedHomogeneousSubmodule R w` for weights
`w : σ → ι` in an additive commutative group `ι`. Geometrically, for `ι = ℤ`, this is the
coordinate ring of the weighted affine space `𝔸(w)` with `𝔾_m` acting on the `i`-th coordinate by
weight `w i`, and `Localization.Away f` for a weighted homogeneous polynomial `f` is the
`𝔾_m`-invariant open subscheme `D(f) ⊆ 𝔸(w)`.

Over any nontrivial commutative semiring `R`, the constant-term homomorphism sends units of
`MvPolynomial σ R` to units of `R`, so every homogeneous unit has degree `0`
(`TauCeti.homogeneousUnitDegrees_weighted`) and the shift class group of `MvPolynomial σ R` is `ι`
(`TauCeti.shiftClassGroupWeightedEquiv`).

When `MvPolynomial σ R` is a domain (for instance when `R` is an integral domain, or a cancellative
domain semiring such as `ℕ`) and `f = ∏ j ∈ s, p j` is a finite product of weighted homogeneous
primes `p j` of weights `d j`, inverting `f` produces homogeneous unit degrees
`AddSubgroup.closure (d '' s)` (`TauCeti.homogeneousUnitDegrees_away_prod_prime`). For `ι = ℤ`,
this subgroup is `AddSubgroup.zmultiples (s.gcd d)`, identifying the shift class group of `D(f)`
with `ZMod (s.gcd d).natAbs` (`TauCeti.shiftClassGroupAwayProdPrimeEquiv`), and with
`ZMod e.natAbs` when `f` is a single weighted homogeneous prime of weight `e`
(`TauCeti.shiftClassGroupAwayPrimeEquiv`) or a positive power of one
(`TauCeti.shiftClassGroupAwayPrimePowEquiv`).

## Main definitions

* `TauCeti.shiftClassGroupWeightedEquiv`: `ShiftClassGroup (weightedHomogeneousSubmodule R w) ≃+ ι`.
* `TauCeti.shiftClassGroupAwayProdPrimeEquiv`: for `f = ∏ j ∈ s, p j` a product of weighted
  homogeneous primes of `ℤ`-weights `d j`, `ShiftClassGroup` of `Localization.Away f` is
  `ZMod (s.gcd d).natAbs`.
* `TauCeti.shiftClassGroupAwayPrimeEquiv`, `TauCeti.shiftClassGroupAwayPrimePowEquiv`, and
  `TauCeti.shiftClassGroupAwayMulPrimeEquiv`: the single-prime, prime-power, and two-prime
  specializations `ZMod e.natAbs` and `ZMod (e₁.gcd e₂)`.

## Main results

* `TauCeti.homogeneousUnitDegrees_weighted`: over any nontrivial commutative semiring,
  `homogeneousUnitDegrees (weightedHomogeneousSubmodule R w) = ⊥`.
* `TauCeti.homogeneousUnitDegrees_away_prod_prime`, `TauCeti.homogeneousUnitDegrees_away_prime`,
  `TauCeti.homogeneousUnitDegrees_away_prime_pow`, and
  `TauCeti.homogeneousUnitDegrees_away_mul_prime`: homogeneous unit degrees of `Localization.Away f`
  for products and powers of weighted homogeneous primes, together with coordinate-variable
  specializations (`homogeneousUnitDegrees_away_X`, `homogeneousUnitDegrees_away_X_pow`,
  `homogeneousUnitDegrees_away_X_mul_X`).
* `TauCeti.exists_linearEquiv_away_prime_iff` and
  `TauCeti.exists_linearEquiv_shift_away_weighted`: classification of shifts and compatible
  `ℤ`-gradings on `D(f) ⊆ 𝔸(w)`.
-/

public section

namespace TauCeti

open _root_.MvPolynomial TauCeti.GradedAlgebra

attribute [local instance] _root_.MvPolynomial.WeightedHomogeneousSubmodule.gradedMonoid
  _root_.MvPolynomial.weightedGradedAlgebra

section Nontrivial

variable (R : Type*) [CommSemiring R] [Nontrivial R] {σ ι : Type*} [AddCommGroup ι] (w : σ → ι)

/-- Over any nontrivial commutative semiring `R` (even with nilpotents or zero or negative weights),
every homogeneous unit of `MvPolynomial σ R` has weighted degree `0`: `constantCoeff` maps a unit
to a unit of `R`, hence its constant term is nonzero of weight `0`. Over a subsingleton ring,
`homogeneousUnitDegrees_eq_top_of_subsingleton` gives `⊤` instead. -/
@[simp]
theorem homogeneousUnitDegrees_weighted :
    homogeneousUnitDegrees (weightedHomogeneousSubmodule R w) = ⊥ := by
  rw [eq_bot_iff, homogeneousUnitDegrees_le_iff]
  intro u d hu
  rw [AddSubgroup.mem_bot]
  have hc : (u : MvPolynomial σ R).coeff 0 ≠ 0 := by
    rw [← constantCoeff_eq]
    exact (u.isUnit.map constantCoeff).ne_zero
  exact ((mem_weightedHomogeneousSubmodule R w d _).mp hu hc).symm.trans (map_zero _)

/-- The shift class group of `MvPolynomial σ R` with weights `w : σ → ι` over a nontrivial
commutative semiring `R` is canonically `ι`: distinct shifts are never graded-isomorphic. -/
noncomputable def shiftClassGroupWeightedEquiv :
    ShiftClassGroup (weightedHomogeneousSubmodule R w) ≃+ ι :=
  (QuotientAddGroup.quotientAddEquivOfEq (homogeneousUnitDegrees_weighted R w)).trans
    QuotientAddGroup.quotientBot

@[simp]
theorem shiftClassGroupWeightedEquiv_mk (d : ι) :
    shiftClassGroupWeightedEquiv R w d = d :=
  (rfl)

end Nontrivial

section AwayDomain

variable {R σ ι : Type*} [CommSemiring R] [IsCancelAdd R] [IsDomain R]
  [AddCommGroup ι] {w : σ → ι} {f : MvPolynomial σ R} {e : ι}

/-- Inverting a finite product `f = ∏ j ∈ s, p j` of weighted homogeneous primes
`p j ∈ weightedHomogeneousSubmodule R w (d j)` in `MvPolynomial σ R` produces homogeneous unit
degrees generated by `{d j | j ∈ s}`. -/
theorem homogeneousUnitDegrees_away_prod_prime (hf : f ∈ weightedHomogeneousSubmodule R w e)
    {J : Type*} (s : Finset J) {p : J → MvPolynomial σ R} {d : J → ι} (hprod : ∏ j ∈ s, p j = f)
    (hp : ∀ j ∈ s, Prime (p j))
    (hd : ∀ j ∈ s, p j ∈ weightedHomogeneousSubmodule R w (d j)) :
    homogeneousUnitDegrees (awayGrading (weightedHomogeneousSubmodule R w) hf) =
      AddSubgroup.closure (d '' (s : Set J)) := by
  classical
  rw [homogeneousUnitDegrees_awayGrading_prod_prime s hprod hp hd,
    homogeneousUnitDegrees_weighted, bot_sup_eq]

/-- Inverting a positive power `f = q ^ n` (`n ≠ 0`) of a weighted homogeneous prime `q` of weight
`d` produces homogeneous unit degrees `AddSubgroup.zmultiples d` (the degree of `q`, not `n • d`,
since `q` itself becomes a unit). -/
theorem homogeneousUnitDegrees_away_prime_pow (hf : f ∈ weightedHomogeneousSubmodule R w e)
    {q : MvPolynomial σ R} {d : ι} {n : ℕ} (hn : n ≠ 0) (hpow : q ^ n = f) (hq : Prime q)
    (hd : q ∈ weightedHomogeneousSubmodule R w d) :
    homogeneousUnitDegrees (awayGrading (weightedHomogeneousSubmodule R w) hf) =
      AddSubgroup.zmultiples d := by
  classical
  rw [homogeneousUnitDegrees_awayGrading_prime_pow hn hpow hq hd,
    homogeneousUnitDegrees_weighted, bot_sup_eq]

/-- Inverting a weighted homogeneous prime `f` of weight `e` in `MvPolynomial σ R` produces
homogeneous unit degrees `AddSubgroup.zmultiples e`. -/
theorem homogeneousUnitDegrees_away_prime (hf : f ∈ weightedHomogeneousSubmodule R w e)
    (hf_prime : Prime f) :
    homogeneousUnitDegrees (awayGrading (weightedHomogeneousSubmodule R w) hf) =
      AddSubgroup.zmultiples e := by
  classical
  rw [homogeneousUnitDegrees_awayGrading_prime hf_prime,
    homogeneousUnitDegrees_weighted, bot_sup_eq]

/-- Inverting the product `f = p₁ * p₂` of two weighted homogeneous primes of weights `e₁` and `e₂`
produces homogeneous unit degrees `zmultiples e₁ ⊔ zmultiples e₂`. -/
theorem homogeneousUnitDegrees_away_mul_prime (hf : f ∈ weightedHomogeneousSubmodule R w e)
    {p₁ p₂ : MvPolynomial σ R} {e₁ e₂ : ι} (hmul : p₁ * p₂ = f)
    (hp₁ : Prime p₁) (hp₂ : Prime p₂)
    (h₁ : p₁ ∈ weightedHomogeneousSubmodule R w e₁)
    (h₂ : p₂ ∈ weightedHomogeneousSubmodule R w e₂) :
    homogeneousUnitDegrees (awayGrading (weightedHomogeneousSubmodule R w) hf) =
      AddSubgroup.zmultiples e₁ ⊔ AddSubgroup.zmultiples e₂ := by
  classical
  rw [homogeneousUnitDegrees_awayGrading_mul_prime hmul hp₁ hp₂ h₁ h₂,
    homogeneousUnitDegrees_weighted, bot_sup_eq]

end AwayDomain

section AwayX

variable {R σ ι : Type*} [CommRing R] [IsDomain R]
  [AddCommGroup ι] {w : σ → ι} {e : ι}

/-- Inverting a coordinate variable `X i` of weight `w i` gives homogeneous unit degrees
`AddSubgroup.zmultiples (w i)`. -/
theorem homogeneousUnitDegrees_away_X {i : σ}
    (hf : (X i : MvPolynomial σ R) ∈ weightedHomogeneousSubmodule R w e) :
    homogeneousUnitDegrees (awayGrading (weightedHomogeneousSubmodule R w) hf) =
      AddSubgroup.zmultiples (w i) :=
  homogeneousUnitDegrees_away_prime_pow hf one_ne_zero (pow_one _) prime_X
    (isWeightedHomogeneous_X R w i)

/-- Inverting a positive power `X i ^ n` (`n ≠ 0`) of a coordinate variable gives homogeneous unit
degrees `AddSubgroup.zmultiples (w i)`. -/
theorem homogeneousUnitDegrees_away_X_pow {i : σ} {n : ℕ} (hn : n ≠ 0)
    (hf : (X i ^ n : MvPolynomial σ R) ∈ weightedHomogeneousSubmodule R w e) :
    homogeneousUnitDegrees (awayGrading (weightedHomogeneousSubmodule R w) hf) =
      AddSubgroup.zmultiples (w i) :=
  homogeneousUnitDegrees_away_prime_pow hf hn rfl prime_X (isWeightedHomogeneous_X R w i)

/-- Inverting the product `X i * X j` of two coordinate variables (even when `i = j`) gives
homogeneous unit degrees `zmultiples (w i) ⊔ zmultiples (w j)`. -/
theorem homogeneousUnitDegrees_away_X_mul_X {i j : σ}
    (hf : (X i * X j : MvPolynomial σ R) ∈ weightedHomogeneousSubmodule R w e) :
    homogeneousUnitDegrees (awayGrading (weightedHomogeneousSubmodule R w) hf) =
      AddSubgroup.zmultiples (w i) ⊔ AddSubgroup.zmultiples (w j) :=
  homogeneousUnitDegrees_away_mul_prime hf rfl prime_X prime_X
    (isWeightedHomogeneous_X R w i) (isWeightedHomogeneous_X R w j)

end AwayX

section IntGrading

variable {R σ : Type*} [CommSemiring R] [IsCancelAdd R] [IsDomain R]
  {w : σ → ℤ} {f : MvPolynomial σ R} {e : ℤ}

/-- For `ℤ`-weights `w : σ → ℤ`, inverting a finite product `f = ∏ j ∈ s, p j` of weighted
homogeneous primes of weights `d j` produces homogeneous unit degrees `zmultiples (s.gcd d)`. -/
theorem homogeneousUnitDegrees_away_prod_prime_int (hf : f ∈ weightedHomogeneousSubmodule R w e)
    {J : Type*} (s : Finset J) {p : J → MvPolynomial σ R} {d : J → ℤ} (hprod : ∏ j ∈ s, p j = f)
    (hp : ∀ j ∈ s, Prime (p j))
    (hd : ∀ j ∈ s, p j ∈ weightedHomogeneousSubmodule R w (d j)) :
    homogeneousUnitDegrees (awayGrading (weightedHomogeneousSubmodule R w) hf) =
      AddSubgroup.zmultiples (s.gcd d) := by
  rw [homogeneousUnitDegrees_away_prod_prime hf s hprod hp hd, ← Finset.coe_image,
    Int.closure_eq_zmultiples_finsetGcd, ← Finset.gcd_eq_gcd_image]

/-- For `ℤ`-weights `w : σ → ℤ`, inverting `f = p₁ * p₂` for weighted homogeneous primes of weights
`e₁` and `e₂` produces homogeneous unit degrees `zmultiples (e₁.gcd e₂ : ℤ)`. -/
theorem homogeneousUnitDegrees_away_mul_prime_int (hf : f ∈ weightedHomogeneousSubmodule R w e)
    {p₁ p₂ : MvPolynomial σ R} {e₁ e₂ : ℤ} (hmul : p₁ * p₂ = f)
    (hp₁ : Prime p₁) (hp₂ : Prime p₂)
    (h₁ : p₁ ∈ weightedHomogeneousSubmodule R w e₁)
    (h₂ : p₂ ∈ weightedHomogeneousSubmodule R w e₂) :
    homogeneousUnitDegrees (awayGrading (weightedHomogeneousSubmodule R w) hf) =
      AddSubgroup.zmultiples (e₁.gcd e₂ : ℤ) := by
  rw [homogeneousUnitDegrees_away_mul_prime hf hmul hp₁ hp₂ h₁ h₂, Int.zmultiples_sup]

/-- For `f = ∏ j ∈ s, p j` a finite product of weighted homogeneous primes of `ℤ`-weights `d j`,
the shift class group of `Localization.Away f` is `ZMod (s.gcd d).natAbs`. -/
noncomputable def shiftClassGroupAwayProdPrimeEquiv (hf : f ∈ weightedHomogeneousSubmodule R w e)
    {J : Type*} (s : Finset J) {p : J → MvPolynomial σ R} {d : J → ℤ} (hprod : ∏ j ∈ s, p j = f)
    (hp : ∀ j ∈ s, Prime (p j))
    (hd : ∀ j ∈ s, p j ∈ weightedHomogeneousSubmodule R w (d j)) :
    ShiftClassGroup (awayGrading (weightedHomogeneousSubmodule R w) hf) ≃+
      ZMod (s.gcd d).natAbs :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (homogeneousUnitDegrees_away_prod_prime_int hf s hprod hp hd)).trans
    (Int.quotientZMultiplesEquivZMod (s.gcd d))

@[simp]
theorem shiftClassGroupAwayProdPrimeEquiv_mk (hf : f ∈ weightedHomogeneousSubmodule R w e)
    {J : Type*} (s : Finset J) {p : J → MvPolynomial σ R} {d : J → ℤ} (hprod : ∏ j ∈ s, p j = f)
    (hp : ∀ j ∈ s, Prime (p j))
    (hd : ∀ j ∈ s, p j ∈ weightedHomogeneousSubmodule R w (d j)) (k : ℤ) :
    shiftClassGroupAwayProdPrimeEquiv hf s hprod hp hd k = k :=
  (rfl)

/-- For a weighted homogeneous prime `f` of `ℤ`-weight `e`, the shift class group of
`Localization.Away f` is `ZMod e.natAbs`: shifts on `D(f) ⊆ 𝔸(w)` are classified modulo `|e|`. -/
noncomputable def shiftClassGroupAwayPrimeEquiv (hf : f ∈ weightedHomogeneousSubmodule R w e)
    (hf_prime : Prime f) :
    ShiftClassGroup (awayGrading (weightedHomogeneousSubmodule R w) hf) ≃+ ZMod e.natAbs :=
  (QuotientAddGroup.quotientAddEquivOfEq (homogeneousUnitDegrees_away_prime hf hf_prime)).trans
    (Int.quotientZMultiplesEquivZMod e)

@[simp]
theorem shiftClassGroupAwayPrimeEquiv_mk (hf : f ∈ weightedHomogeneousSubmodule R w e)
    (hf_prime : Prime f) (k : ℤ) :
    shiftClassGroupAwayPrimeEquiv hf hf_prime k = k :=
  (rfl)

/-- For a positive power `f = q ^ n` (`n ≠ 0`) of a weighted homogeneous prime `q` of `ℤ`-weight
`d`, the shift class group of `Localization.Away f` is `ZMod d.natAbs`. -/
noncomputable def shiftClassGroupAwayPrimePowEquiv (hf : f ∈ weightedHomogeneousSubmodule R w e)
    {q : MvPolynomial σ R} {d : ℤ} {n : ℕ} (hn : n ≠ 0) (hpow : q ^ n = f) (hq : Prime q)
    (hd : q ∈ weightedHomogeneousSubmodule R w d) :
    ShiftClassGroup (awayGrading (weightedHomogeneousSubmodule R w) hf) ≃+ ZMod d.natAbs :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (homogeneousUnitDegrees_away_prime_pow hf hn hpow hq hd)).trans
    (Int.quotientZMultiplesEquivZMod d)

@[simp]
theorem shiftClassGroupAwayPrimePowEquiv_mk (hf : f ∈ weightedHomogeneousSubmodule R w e)
    {q : MvPolynomial σ R} {d : ℤ} {n : ℕ} (hn : n ≠ 0) (hpow : q ^ n = f) (hq : Prime q)
    (hd : q ∈ weightedHomogeneousSubmodule R w d) (k : ℤ) :
    shiftClassGroupAwayPrimePowEquiv hf hn hpow hq hd k = k :=
  (rfl)

/-- For `f = p₁ * p₂` a product of two weighted homogeneous primes of `ℤ`-weights `e₁` and `e₂`,
the shift class group of `Localization.Away f` is `ZMod (e₁.gcd e₂)`. -/
noncomputable def shiftClassGroupAwayMulPrimeEquiv (hf : f ∈ weightedHomogeneousSubmodule R w e)
    {p₁ p₂ : MvPolynomial σ R} {e₁ e₂ : ℤ} (hmul : p₁ * p₂ = f)
    (hp₁ : Prime p₁) (hp₂ : Prime p₂)
    (h₁ : p₁ ∈ weightedHomogeneousSubmodule R w e₁)
    (h₂ : p₂ ∈ weightedHomogeneousSubmodule R w e₂) :
    ShiftClassGroup (awayGrading (weightedHomogeneousSubmodule R w) hf) ≃+ ZMod (e₁.gcd e₂) :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (homogeneousUnitDegrees_away_mul_prime_int hf hmul hp₁ hp₂ h₁ h₂)).trans
    (Int.quotientZMultiplesNatEquivZMod (e₁.gcd e₂))

@[simp]
theorem shiftClassGroupAwayMulPrimeEquiv_mk (hf : f ∈ weightedHomogeneousSubmodule R w e)
    {p₁ p₂ : MvPolynomial σ R} {e₁ e₂ : ℤ} (hmul : p₁ * p₂ = f)
    (hp₁ : Prime p₁) (hp₂ : Prime p₂)
    (h₁ : p₁ ∈ weightedHomogeneousSubmodule R w e₁)
    (h₂ : p₂ ∈ weightedHomogeneousSubmodule R w e₂) (k : ℤ) :
    shiftClassGroupAwayMulPrimeEquiv hf hmul hp₁ hp₂ h₁ h₂ k = k :=
  (rfl)

/-- Two shifts `d₁` and `d₂` of `Localization.Away f`, for a weighted homogeneous prime `f` of
`ℤ`-weight `e`, are graded-isomorphic if and only if `d₁` and `d₂` have the same image in
`ZMod e.natAbs`. -/
theorem exists_linearEquiv_away_prime_iff (hf : f ∈ weightedHomogeneousSubmodule R w e)
    (hf_prime : Prime f) {d₁ d₂ : ℤ} :
    (∃ φ : Localization.Away f ≃ₗ[Localization.Away f] Localization.Away f,
        ∀ n x, φ x ∈ awayGrading (weightedHomogeneousSubmodule R w) hf (n + d₂) ↔
          x ∈ awayGrading (weightedHomogeneousSubmodule R w) hf (n + d₁)) ↔
      (d₁ : ZMod e.natAbs) = (d₂ : ZMod e.natAbs) := by
  rw [← ShiftClassGroup.mk_eq_mk_iff,
    ← (shiftClassGroupAwayPrimeEquiv hf hf_prime).injective.eq_iff,
    shiftClassGroupAwayPrimeEquiv_mk, shiftClassGroupAwayPrimeEquiv_mk]

end IntGrading

section ConnectedShift

variable {R σ τ : Type*} [CommRing R] [NoZeroDivisors R] {w : σ → ℤ}
  {f : MvPolynomial σ R} {e : ℤ}

/-- Over a commutative ring `R` without zero divisors, for any weighted homogeneous polynomial
`f ∈ weightedHomogeneousSubmodule R w e` (including `f = 0`, where `Localization.Away f` is the zero
ring), `Localization.Away f` has preconnected prime spectrum, so every compatible `ℤ`-grading `ℳ` of
`Localization.Away f` is graded-isomorphic to a shift of
`awayGrading (weightedHomogeneousSubmodule R w) hf`. -/
theorem exists_linearEquiv_shift_away_weighted (hf : f ∈ weightedHomogeneousSubmodule R w e)
    [SetLike τ (Localization.Away f)] [AddSubmonoidClass τ (Localization.Away f)]
    (ℳ : ℤ → τ) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (awayGrading (weightedHomogeneousSubmodule R w) hf) ℳ] :
    ∃ d : ℤ, ∃ φ : Localization.Away f ≃ₗ[Localization.Away f] Localization.Away f,
      ∀ n x, φ x ∈ ℳ n ↔ x ∈ awayGrading (weightedHomogeneousSubmodule R w) hf (n + d) := by
  have : PreconnectedSpace (PrimeSpectrum (Localization.Away f)) := by
    by_cases hf0 : f = 0
    · have : Subsingleton (Localization.Away f) :=
        IsLocalization.subsingleton (M := .powers f) ⟨1, by simp [hf0]⟩
      infer_instance
    · have : Nontrivial (MvPolynomial σ R) := ⟨⟨f, 0, hf0⟩⟩
      have : IsDomain (MvPolynomial σ R) := NoZeroDivisors.to_isDomain _
      have : IsDomain (Localization.Away f) := Localization.Away.isDomain hf0
      infer_instance
  exact exists_linearEquiv_shift_of_connected
    (awayGrading (weightedHomogeneousSubmodule R w) hf) ℳ

end ConnectedShift

end TauCeti
