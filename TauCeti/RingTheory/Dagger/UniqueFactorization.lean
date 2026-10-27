/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Noetherian
public import TauCeti.RingTheory.Dagger.Preparation
public import TauCeti.RingTheory.MvPowerSeries.NonZeroDivisors
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain

/-!
# Monsky–Washnitzer algebras are unique factorisation domains

Over a complete ultrametric normed field `K`, the Monsky–Washnitzer algebra `K⟨X⟩†` in finitely
many variables is a unique factorisation domain.

Write `W = K⟨X⟩†` and `W' = K⟨X, Y⟩†`, with `Y = X none`. Evaluating polynomials at `Y` along
`washnitzerAlgebra.optionC` is the ring map `washnitzerAlgebra.polynomialToOption : W[Y] → W'`.
Let `ω ∈ W[Y]` be monic of degree `s` and distinguished of degree `s` in `Y`. Uniqueness of
overconvergent Weierstrass division shows that `ω` divides a polynomial in `W[Y]` as soon as it
divides it in `W'`, and existence of division shows that every series in `W'` is congruent
modulo `ω` to a polynomial. Hence `ω` is prime in `W[Y]` iff it is prime in `W'`.

Factoriality follows by induction on the number of variables. Since `W'` is a noetherian domain,
it suffices that every irreducible `f ∈ W'` is prime. A triangular automorphism makes `f`
distinguished in `Y` with a unit coefficient in the distinguished degree, and overconvergent
Weierstrass preparation writes it as a unit multiple of a monic polynomial `ω ∈ W[Y]`. The
divisibility comparison shows that `ω` is irreducible in `W[Y]`, hence prime, since `W[Y]` is a
unique factorisation domain by induction and Gauss's lemma. So `ω` and `f` are prime in `W'`.

## Main definitions

* `TauCeti.Dagger.washnitzerAlgebra.polynomialToOption`: the evaluation `W[Y] → W'` at `Y`.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.polynomialToOption_dvd_iff`: divisibility by a distinguished
  monic polynomial is the same in `W[Y]` and in `W'`.
* `TauCeti.Dagger.washnitzerAlgebra.exists_mul_add_polynomialToOption_eq`: every series in `W'`
  is congruent to a polynomial of smaller degree modulo a distinguished monic polynomial.
* `TauCeti.Dagger.washnitzerAlgebra.irreducible_of_irreducible_polynomialToOption` and
  `TauCeti.Dagger.washnitzerAlgebra.prime_polynomialToOption_iff`: irreducibility and primality
  of a distinguished monic polynomial pass from `W'` to `W[Y]`, and primality back.
* `TauCeti.Dagger.washnitzerAlgebra.uniqueFactorizationMonoid`: `K⟨X⟩†` is a unique factorisation
  domain for finitely many variables.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.4 (1).
* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §5.2.6,
  Theorem 1 (the same statement for Tate algebras).

The argument follows `TauCeti.MvPowerSeries.uniqueFactorizationMonoid` in
`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniqueFactorization` and the divisibility
comparison `TauCeti.PowerSeries.IsDistinguished.polynomialToRestricted_dvd_iff`, with
overconvergent Weierstrass division and preparation in place of their fixed-radius counterparts.
-/

public section

namespace TauCeti.Dagger.washnitzerAlgebra

open _root_.MvPowerSeries

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "W" => washnitzerAlgebra σ K
local notation "W'" => washnitzerAlgebra (Option σ) K
local notation "Tate" => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

section Polynomial

variable {s : ℕ} {ω : Polynomial (washnitzerAlgebra σ K)}

/-- Divisibility of polynomials by a distinguished monic polynomial `ω` is unchanged on passing
to `K⟨X, Y⟩†`. The assertion uses uniqueness of overconvergent division, but not completeness. -/
theorem polynomialToOption_dvd_iff
    (hω : PowerSeries.IsDistinguished 1 s (ω.map (toTate σ K).toRingHom : PowerSeries Tate))
    (hm : ω.IsMonicOfDegree s) (p : Polynomial W) :
    polynomialToOption ω ∣ polynomialToOption p ↔ ω ∣ p := by
  refine ⟨fun ⟨a, ha⟩ ↦ ?_, fun h ↦ map_dvd _ h⟩
  have hg : PowerSeries.IsDistinguished 1 s
      (Huber.restrictedOptionEquiv (toTate _ K (polynomialToOption ω)) : PowerSeries Tate) := by
    rwa [restrictedOptionEquiv_toTate_polynomialToOption]
  have hdeg : (p %ₘ ω).degree < (s : WithBot ℕ) := by
    simpa [Polynomial.degree_eq_natDegree hm.ne_zero, hm.natDegree_eq] using
      Polynomial.degree_modByMonic_lt p hm.monic
  -- Compare `p = a * ω` in `W'` with the polynomial division `p = (p /ₘ ω) * ω + p %ₘ ω`.
  have heq : optionSeries a * optionSeries (polynomialToOption ω) + ((0 : Polynomial W) :
      PowerSeries W) = optionSeries (polynomialToOption (p /ₘ ω)) *
        optionSeries (polynomialToOption ω) + ((p %ₘ ω : Polynomial W) : PowerSeries W) := by
    simpa [ha, mul_comm, add_comm] using congrArg (fun x ↦ optionSeries (polynomialToOption x))
      (Polynomial.modByMonic_add_div p ω).symm
  have hzero := (eq_and_eq_of_mul_add_eq_mul_add_of_isDistinguished hg
    (by simp [Polynomial.degree_zero]) hdeg heq).2
  exact (Polynomial.modByMonic_eq_zero_iff_dvd hm.monic).mp hzero.symm

/-- A distinguished monic polynomial which is irreducible in `K⟨X, Y⟩†` is irreducible in
`K⟨X⟩†[Y]`. -/
theorem irreducible_of_irreducible_polynomialToOption
    (hω : PowerSeries.IsDistinguished 1 s (ω.map (toTate σ K).toRingHom : PowerSeries Tate))
    (hm : ω.IsMonicOfDegree s) (h : Irreducible (polynomialToOption ω)) : Irreducible ω := by
  -- If the image of a factor `a` of `ω = a * b` is a unit, then `ω` divides `b` after passing
  -- to `K⟨X, Y⟩†`, hence as polynomials; cancelling `b` shows that `a` is a unit.
  have key (a b : Polynomial W) (hab : ω = a * b) (ha : IsUnit (polynomialToOption a)) :
      IsUnit a := by
    have hb : b ≠ 0 := right_ne_zero_of_mul (hab ▸ hm.ne_zero)
    obtain ⟨d, hd⟩ := (polynomialToOption_dvd_iff hω hm b).mp <| by
      rw [hab, map_mul]
      exact ha.mul_left_dvd.mpr dvd_rfl
    rw [hab] at hd
    refine IsUnit.of_mul_eq_one d (mul_left_cancel₀ hb ?_)
    rw [mul_one, ← mul_assoc, mul_comm b a]
    exact hd.symm
  refine ⟨fun hu ↦ h.not_isUnit (hu.map _), fun a b hab ↦ ?_⟩
  rcases h.isUnit_or_isUnit (by rw [hab, map_mul]) with ha | hb
  · exact Or.inl (key a b hab ha)
  · exact Or.inr (key b a (hab.trans (mul_comm a b)) hb)

variable [CompleteSpace K]

/-- Every overconvergent series is congruent modulo a distinguished monic polynomial `ω` to a
polynomial in `Y` of degree less than that of `ω`, with coefficients in `K⟨X⟩†`. -/
theorem exists_mul_add_polynomialToOption_eq
    (hω : PowerSeries.IsDistinguished 1 s (ω.map (toTate σ K).toRingHom : PowerSeries Tate))
    (hm : ω.IsMonicOfDegree s) (f : W') :
    ∃ (q : W') (r : Polynomial W), r.degree < (s : WithBot ℕ) ∧
      q * polynomialToOption ω + polynomialToOption r = f := by
  have hg : PowerSeries.IsDistinguished 1 s
      (Huber.restrictedOptionEquiv (toTate _ K (polynomialToOption ω)) : PowerSeries Tate) := by
    rwa [restrictedOptionEquiv_toTate_polynomialToOption]
  have hu : IsUnit (PowerSeries.coeff s
      (Huber.restrictedOptionEquiv (toTate _ K (polynomialToOption ω)) : PowerSeries Tate)) := by
    simp [restrictedOptionEquiv_toTate_polynomialToOption, Polynomial.coeff_coe,
      ← hm.natDegree_eq, hm.monic.coeff_natDegree]
  obtain ⟨q, r, hr, hqr⟩ := exists_mul_add_eq_of_isDistinguished hg hu f
  exact ⟨q, r, hr, optionSeries_injective (by simpa using hqr)⟩

/-- A distinguished monic polynomial is prime in `K⟨X⟩†[Y]` iff it is prime in `K⟨X, Y⟩†`. -/
theorem prime_polynomialToOption_iff
    (hω : PowerSeries.IsDistinguished 1 s (ω.map (toTate σ K).toRingHom : PowerSeries Tate))
    (hm : ω.IsMonicOfDegree s) : Prime (polynomialToOption ω) ↔ Prime ω := by
  have hdvd := polynomialToOption_dvd_iff hω hm
  refine ⟨fun h ↦ ⟨fun h0 ↦ h.ne_zero (by simp [h0]), fun hu ↦ h.not_isUnit (hu.map _),
    fun a b hab ↦ ?_⟩, fun h ↦ ⟨fun h0 ↦ h.ne_zero (polynomialToOption_injective (by simp [h0])),
    fun hu ↦ h.not_isUnit ?_, fun a b hab ↦ ?_⟩⟩
  · simpa only [← hdvd] using
      h.dvd_or_dvd (by simpa only [map_mul] using map_dvd polynomialToOption hab)
  · -- A unit `polynomialToOption ω` divides `polynomialToOption 1`, so `ω` divides `1`.
    exact isUnit_of_dvd_one ((hdvd 1).mp (by simpa using hu.dvd))
  · -- Reduce `a` and `b` to polynomial remainders modulo `ω`.
    obtain ⟨qa, ra, -, rfl⟩ := exists_mul_add_polynomialToOption_eq hω hm a
    obtain ⟨qb, rb, -, rfl⟩ := exists_mul_add_polynomialToOption_eq hω hm b
    have hr : ω ∣ ra * rb := by
      rw [← hdvd, map_mul]
      have hexp : (qa * polynomialToOption ω + polynomialToOption ra) *
          (qb * polynomialToOption ω + polynomialToOption rb) = polynomialToOption ω *
            (qa * qb * polynomialToOption ω + qa * polynomialToOption rb +
              qb * polynomialToOption ra) + polynomialToOption ra * polynomialToOption rb := by
        ring
      rw [hexp] at hab
      exact (dvd_add_right (dvd_mul_right _ _)).mp hab
    rcases h.dvd_or_dvd hr with ha | hb
    · exact Or.inl ((dvd_add_right (dvd_mul_left _ qa)).mpr ((hdvd ra).mpr ha))
    · exact Or.inr ((dvd_add_right (dvd_mul_left _ qb)).mpr ((hdvd rb).mpr hb))

end Polynomial

section UniqueFactorization

variable [CompleteSpace K]

/-- The inductive step: if `K⟨X⟩†` is a unique factorisation domain, so is `K⟨X, Y⟩†`. -/
private theorem uniqueFactorizationMonoid_option [Finite σ] [UniqueFactorizationMonoid W] :
    UniqueFactorizationMonoid W' := by
  refine { irreducible_iff_prime := fun {f} ↦ ⟨fun hf ↦ ?_, Prime.irreducible⟩ }
  -- Make `f` distinguished in `Y`, and pass to its image `g` under the automorphism.
  obtain ⟨α, hα, s, hd, hu⟩ := exists_triangularEquiv_isDistinguished_isUnit f hf.ne_zero
  let e := triangularEquiv (R := K) α hα
  rw [← MulEquiv.prime_iff e.toMulEquiv]
  rw [← MulEquiv.irreducible_iff e.toMulEquiv] at hf
  set g : W' := e f
  -- Weierstrass preparation: `g = u * ω(Y)` with `u` a unit and `ω` monic.
  obtain ⟨u, ω, hu', hm, hmul⟩ := exists_isUnit_isMonicOfDegree_mul_eq hd hu
  have hω : PowerSeries.IsDistinguished 1 s (ω.map (toTate σ K).toRingHom : PowerSeries Tate) :=
    (hmul ▸ hd).of_isUnit_mul one_pos
      ((hu'.map (toTate _ K)).map Huber.restrictedOptionEquiv.toRingHom)
  have hg : u * polynomialToOption ω = g := by
    apply toTate_injective
    apply Huber.restrictedOptionEquiv.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subring.coe_mul, restrictedOptionEquiv_toTate_polynomialToOption, hmul]
  have hassoc : Associated (polynomialToOption ω) g := by
    rw [← hg, mul_comm]
    exact associated_mul_unit_right _ _ hu'
  have hirr := hassoc.symm.irreducible hf
  -- `ω` is irreducible, hence prime, in the unique factorisation domain `K⟨X⟩†[Y]`.
  have hωp : Prime ω := UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (irreducible_of_irreducible_polynomialToOption hω hm hirr)
  -- So `ω(Y)`, hence `g`, is prime in `K⟨X, Y⟩†`.
  exact hassoc.prime ((prime_polynomialToOption_iff hω hm).mpr hωp)

/-- **Monsky–Washnitzer algebras are unique factorisation domains.** Over a complete ultrametric
normed field `K`, the algebra `K⟨X⟩†` of overconvergent power series in finitely many variables
is a unique factorisation domain. -/
instance uniqueFactorizationMonoid [Finite σ] : UniqueFactorizationMonoid W :=
  Finite.induction_empty_option
    (P := fun σ ↦ ∀ [Finite σ], UniqueFactorizationMonoid (washnitzerAlgebra σ K))
    (fun {α β} e h _ ↦
      have : Finite α := .of_equiv β e.symm
      (renameAlgEquiv (R := K) e).toMulEquiv.uniqueFactorizationMonoid h)
    ((RingEquiv.ofBijective (algebraMap K (washnitzerAlgebra PEmpty K))
      ⟨(algebraMap K _).injective, algebraMap_surjective⟩).toMulEquiv.uniqueFactorizationMonoid
        inferInstance)
    (fun {_} _ h _ ↦
      have := h
      uniqueFactorizationMonoid_option) σ

end UniqueFactorization

end TauCeti.Dagger.washnitzerAlgebra
