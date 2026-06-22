/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.AlgebraicGeometry.WeilDivisor.Principal
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# The order system of a Dedekind domain

The abstract `OrderSystem` of `TauCeti.AlgebraicGeometry.WeilDivisor.Principal` packages the
order-of-vanishing data needed to build principal divisors and the divisor class group. This
file supplies the roadmap's intended *concrete* instance of that data: a Dedekind domain `R`
with fraction field `K`. Its height-one spectrum `HeightOneSpectrum R` is the set of
codimension-one points of `Spec R` (an affine model of a curve, or the ring of integers of a
number field), and the `v`-adic valuation gives each point an order-of-vanishing homomorphism
on the multiplicative group `Kˣ` of nonzero rational functions.

Concretely we build:

* `adicOrd R K v : Additive Kˣ →+ ℤ`, the order of vanishing `ord_v(f) = -log v(f)` of a
  nonzero rational function `f` at the height-one prime `v` (the sign makes a uniformizer have
  order `+1`, i.e. a simple zero);
* `OrderSystem.ofDedekindDomain R K : OrderSystem (HeightOneSpectrum R) (Additive Kˣ)`, whose
  finiteness condition is exactly the statement that a nonzero rational function has zeros and
  poles at only finitely many primes;
* `DivisorClassGroup R K`, the resulting Weil divisor class group `Cl(Spec R)`;
* the sanity check that the principal divisor of a nonzero *integral* element is effective
  (an element of `R` has no poles).

The roadmap explicitly anticipates this instantiation: "Instantiate `G` with `Additive Kˣ`
for the multiplicative group of a function field `K`: then `ord x` is the order of vanishing
`ord_x(f)`". This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A ("Divisors on
a curve: Weil divisors `⊕_x ℤ`", "principal divisors", "`Cl(X)`"), grounding the abstract
order-system API in Mathlib's Dedekind-domain adic valuations.

We do *not* claim the weighted-degree-zero property here: for a general Dedekind domain (e.g.
`ℤ`) there is no product formula, so a principal divisor need not have degree zero. That holds
only for proper curves over a field (and number fields with the archimedean places included),
and is later geometric input.

This reuses Mathlib's `IsDedekindDomain.HeightOneSpectrum.valuation`, the `WithZero.log`
logarithm on `ℤᵐ⁰`, and `IsDedekindDomain.HeightOneSpectrum.Support.finite` (finiteness of the
support of a rational function); no external mathematics is vendored.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The order of vanishing `ord_v(f) = -log v(f)` of a nonzero rational function `f : Kˣ` at a
height-one prime `v` of a Dedekind domain `R`, as a homomorphism `Additive Kˣ →+ ℤ`. The sign
is chosen so that a uniformizer at `v` has order `+1` (a simple zero) and a pole has negative
order. -/
noncomputable def adicOrd (v : HeightOneSpectrum R) : Additive Kˣ →+ ℤ :=
  AddMonoidHom.mk' (fun u => -WithZero.log (v.valuation K ((Additive.toMul u : Kˣ) : K)))
    fun u₁ u₂ => by
      have h₁ : v.valuation K ((Additive.toMul u₁ : Kˣ) : K) ≠ 0 :=
        (v.valuation K).ne_zero_iff.mpr (Units.ne_zero _)
      have h₂ : v.valuation K ((Additive.toMul u₂ : Kˣ) : K) ≠ 0 :=
        (v.valuation K).ne_zero_iff.mpr (Units.ne_zero _)
      simp only [toMul_add, Units.val_mul, map_mul, WithZero.log_mul h₁ h₂]
      ring

variable {R K}

@[simp]
lemma adicOrd_apply (v : HeightOneSpectrum R) (u : Additive Kˣ) :
    adicOrd R K v u = -WithZero.log (v.valuation K ((Additive.toMul u : Kˣ) : K)) :=
  rfl

@[simp]
lemma adicOrd_ofMul (v : HeightOneSpectrum R) (u : Kˣ) :
    adicOrd R K v (Additive.ofMul u) = -WithZero.log (v.valuation K (u : K)) :=
  rfl

/-- The order `ord_v(f)` is nonnegative exactly when `f` is integral at `v`, i.e. has
valuation at most one. -/
lemma adicOrd_nonneg_iff (v : HeightOneSpectrum R) (u : Additive Kˣ) :
    0 ≤ adicOrd R K v u ↔ v.valuation K ((Additive.toMul u : Kˣ) : K) ≤ 1 := by
  have hu : v.valuation K ((Additive.toMul u : Kˣ) : K) ≠ 0 :=
    (v.valuation K).ne_zero_iff.mpr (Units.ne_zero _)
  rw [adicOrd_apply, neg_nonneg, ← WithZero.log_one (M := ℤ),
    WithZero.log_le_log hu one_ne_zero]

variable (R K)

/-- The order system of a Dedekind domain `R` with fraction field `K`: its points are the
height-one primes `v` of `R`, the group is the multiplicative group `Kˣ` of nonzero rational
functions, and the order at `v` is the `v`-adic order of vanishing. The finiteness condition is
exactly the statement that a nonzero rational function has zeros and poles at only finitely many
primes. -/
noncomputable def OrderSystem.ofDedekindDomain :
    OrderSystem (HeightOneSpectrum R) (Additive Kˣ) where
  ord v := adicOrd R K v
  finite_support u := by
    set k : K := ((Additive.toMul u : Kˣ) : K) with hk
    have hk0 : k ≠ 0 := Units.ne_zero _
    refine Set.Finite.subset
      ((HeightOneSpectrum.Support.finite (R := R) (K := K) k).union
        (HeightOneSpectrum.Support.finite (R := R) (K := K) k⁻¹)) ?_
    intro v hv
    have hlog : WithZero.log (v.valuation K k) ≠ 0 := by
      simpa [adicOrd_apply, ← hk, neg_ne_zero] using hv
    have hval : v.valuation K k ≠ 0 := (v.valuation K).ne_zero_iff.mpr hk0
    have hne_one : v.valuation K k ≠ 1 := fun h => hlog (by rw [h, WithZero.log_one])
    rcases lt_or_gt_of_ne hne_one with hlt | hgt
    · refine Or.inr ?_
      change 1 < v.valuation K k⁻¹
      rw [map_inv₀]
      exact (one_lt_inv₀ (WithZero.pos_iff_ne_zero.mpr hval)).mpr hlt
    · exact Or.inl hgt

@[simp]
lemma OrderSystem.ofDedekindDomain_ord (v : HeightOneSpectrum R) :
    (OrderSystem.ofDedekindDomain R K).ord v = adicOrd R K v :=
  rfl

/-- The coefficient of the principal divisor of `f : Kˣ` at a height-one prime `v` is the
`v`-adic order of vanishing `-log v(f)`. -/
lemma coeff_principalDivisor_ofDedekindDomain (u : Additive Kˣ) (v : HeightOneSpectrum R) :
    coeff ((OrderSystem.ofDedekindDomain R K).principalDivisor u) v =
      -WithZero.log (v.valuation K ((Additive.toMul u : Kˣ) : K)) := by
  rw [OrderSystem.coeff_principalDivisor, OrderSystem.ofDedekindDomain_ord, adicOrd_apply]

/-- The divisor class group `Cl(Spec R)` of a Dedekind domain, as the Weil divisor class group
of its order system. -/
noncomputable abbrev DivisorClassGroup : Type _ :=
  (OrderSystem.ofDedekindDomain R K).ClassGroup

variable {R K}

/-- An integral element `r : R`, `r ≠ 0`, as a nonzero rational function. -/
noncomputable def algebraMapUnit {r : R} (hr : r ≠ 0) : Kˣ :=
  Units.mk0 (algebraMap R K r) (by rwa [ne_eq, IsFractionRing.to_map_eq_zero_iff])

omit [IsDedekindDomain R] in
@[simp]
lemma algebraMapUnit_val {r : R} (hr : r ≠ 0) :
    (algebraMapUnit (K := K) hr : K) = algebraMap R K r :=
  rfl

/-- The principal divisor of a nonzero *integral* element is effective: an element of `R` has
no poles, only zeros. This is the divisor-of-functions sanity check that rules out a vacuous
order system. -/
lemma principalDivisor_isEffective_of_integral {r : R} (hr : r ≠ 0) :
    IsEffective ((OrderSystem.ofDedekindDomain R K).principalDivisor
      (Additive.ofMul (algebraMapUnit (K := K) hr))) := by
  rw [isEffective_iff]
  intro v
  rw [OrderSystem.coeff_principalDivisor, OrderSystem.ofDedekindDomain_ord, adicOrd_nonneg_iff]
  simp only [toMul_ofMul, algebraMapUnit_val]
  exact v.valuation_le_one r

/-- The divisor of a nonzero integral element `r : R` has a strictly positive coefficient (a
genuine zero) at `v` exactly when `r` lies in the prime `v`. Its support is therefore the set
of primes dividing `r`. -/
lemma coeff_principalDivisor_pos_iff_mem {r : R} (hr : r ≠ 0) (v : HeightOneSpectrum R) :
    0 < coeff ((OrderSystem.ofDedekindDomain R K).principalDivisor
      (Additive.ofMul (algebraMapUnit (K := K) hr))) v ↔ r ∈ v.asIdeal := by
  have hu : v.valuation K (algebraMap R K r) ≠ 0 :=
    (v.valuation K).ne_zero_iff.mpr (by rwa [ne_eq, IsFractionRing.to_map_eq_zero_iff])
  rw [coeff_principalDivisor_ofDedekindDomain]
  simp only [toMul_ofMul, algebraMapUnit_val]
  rw [neg_pos, ← WithZero.log_one (M := ℤ), WithZero.log_lt_log hu one_ne_zero,
    v.valuation_lt_one_iff_mem]

end WeilDivisor

end AlgebraicGeometry

end TauCeti
