/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Coupling.NormalForm
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.RingTheory.Ideal.Quotient.Basic
import TauCeti.RingTheory.MvPowerSeries.Dvd

/-!
# Couplings from a resolution of the identity

In characteristic `p`, the Frobenius powers of a linear form are sums of powers of individual
variables. If the powered coefficients are those of the dual frame at the partner coordinates,
the resolution of the identity contracts the resulting sum to the coupling. Reduction modulo
a divisor of `p` gives the corresponding congruence of integral power series, including the
higher Frobenius powers that occur in the exponent of a product of theta functions.

The congruence comes from `New.Parameters.piPrimeInt_dvd_sum_linearSeries_sub_coupling` in
`grh/src/New/Derivatives/FormalGroup/ThetaProducts.lean` of lsernau/grh-lean at `72fead1`.
-/

public section

namespace MvPowerSeries

variable {Φ c : Type*} [Fintype Φ] [Fintype c]

/-- A coefficient map preserves the coupling for each partner rule and exponent. -/
@[simp]
theorem map_coupling {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (p : ℕ) (pr : ℕ → Φ → Φ) (e : ℕ) :
    map (σ := Φ × c) f (coupling p pr e) = coupling p pr e := by
  simp [coupling_def]

variable {ι : Type*} [Fintype ι] [DecidableEq (Φ × c)]

/-- In exponential characteristic `p`, a weighted resolution of the identity whose dual
coefficients are Frobenius partners turns the weighted sum of powers of the linear forms into a
coupling power. Here `a` consists of coefficients of the forms, `b` of the dual vectors, and `m`
of their multiplicities. -/
theorem sum_natCast_mul_linearForm_pow_eq_coupling_pow {R : Type*} [CommRing R] {p : ℕ}
    [ExpChar R p] {pr : ℕ → Φ → Φ} {e : ℕ} (j : ℕ)
    {a b : ι → Φ × c → R} {m : ι → ℕ}
    (hres : ∀ x y, ∑ i, (m i : R) * b i x * a i y = if x = y then 1 else 0)
    (hpartner : ∀ i x, a i x ^ p ^ e = b i (pr e x.1, x.2)) :
    ∑ i, (m i : MvPowerSeries (Φ × c) R) *
        ((∑ x, C (a i x) * X x) ^ p ^ e * (∑ x, C (a i x) * X x)) ^ p ^ j =
      coupling p pr e ^ p ^ j := by
  let : ExpChar (MvPowerSeries (Φ × c) R) p := expChar_of_injective_ringHom C_injective p
  let L (i : ι) : MvPowerSeries (Φ × c) R := ∑ y, C (a i y) * X y
  have resolve (x : Φ × c) : ∑ i, C ((m i : R) * b i x) * L i = X x := by
    simp only [L, Finset.mul_sum, ← mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, ← map_sum, hres, apply_ite C, map_one, map_zero, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have partner (i : ι) : L i ^ p ^ e = ∑ x, C (b i (pr e x.1, x.2)) * X x ^ p ^ e := by
    simp only [L, sum_pow_char_pow p e, mul_pow, ← map_pow, hpartner]
  have h : ∑ i, (m i : MvPowerSeries (Φ × c) R) * (L i ^ p ^ e * L i) = coupling p pr e := by
    simp only [partner, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm, coupling_def]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [← resolve (pr e x.1, x.2), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_natCast]
    ac_rfl
  have hpow := congrArg (iterateFrobenius (MvPowerSeries (Φ × c) R) p j) h
  rw [map_sum, iterateFrobenius_def] at hpow
  rw [← hpow]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_natCast, iterateFrobenius_def]

/-- A weighted resolution with Frobenius partners modulo a divisor `π` of `p` gives the
coupling congruence modulo `π` in every coefficient. The identity only needs to be resolved
modulo `π`; no reduction modulo the maximal ideal is used. -/
theorem C_dvd_sum_sub_coupling_pow {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime)
    {π : R} (hπ : π ∣ (p : R)) {pr : ℕ → Φ → Φ} {e : ℕ} (j : ℕ)
    {a b : ι → Φ × c → R} {m : ι → ℕ}
    (hres : ∀ x y, π ∣ (∑ i, (m i : R) * b i x * a i y) - (if x = y then 1 else 0))
    (hpartner : ∀ i x, π ∣ a i x ^ p ^ e - b i (pr e x.1, x.2)) :
    C π ∣ (∑ i, (m i : MvPowerSeries (Φ × c) R) *
      ((∑ x, C (a i x) * X x) ^ p ^ e * (∑ x, C (a i x) * X x)) ^ p ^ j) -
        coupling p pr e ^ p ^ j := by
  by_cases hunit : IsUnit π
  · exact (hunit.map C).dvd
  let I : Ideal R := Ideal.span {π}
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hI : I ≠ ⊤ := fun h ↦ hunit (Ideal.span_singleton_eq_top.mp h)
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hp₀ : (p : R ⧸ I) = 0 := by
    rw [← map_natCast q, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.mpr hπ
  let : CharP (R ⧸ I) p := (CharP.charP_iff_prime_eq_zero hp).mpr hp₀
  let : Fact p.Prime := ⟨hp⟩
  have hqres (x y : Φ × c) :
      ∑ i, (m i : R ⧸ I) * q (b i x) * q (a i y) = if x = y then 1 else 0 := by
    have h := Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (hres x y))
    simpa [q, apply_ite] using h
  have hqpartner (i : ι) (x : Φ × c) :
      q (a i x) ^ p ^ e = q (b i (pr e x.1, x.2)) := by
    have h := Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (hpartner i x))
    simpa [q] using h
  rw [C_dvd_iff_dvd_coeff]
  intro d
  refine Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp (?_ : q _ = 0))
  rw [← coeff_map]
  simp only [map_sub, map_sum, map_mul, map_pow, map_natCast, map_C, map_X, map_coupling,
    sum_natCast_mul_linearForm_pow_eq_coupling_pow j hqres hqpartner, sub_self, map_zero]

end MvPowerSeries
