/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import TauCeti.NumberTheory.QuadraticForm.Global.CohomologicalSymbol
import TauCeti.NumberTheory.LocalField.QuadraticForm.OddResidue.Padic
import TauCeti.NumberTheory.LocalField.QuadraticForm.PadicTwo
import TauCeti.NumberTheory.QuadraticForm.Global.ArchimedeanSymbol
import TauCeti.NumberTheory.QuadraticForm.Global.HilbertSymbol

/-!
# Quadratic reciprocity from Hilbert reciprocity

Hilbert's reciprocity law over `ℚ` says that for `a, b ∈ ℚˣ` the cohomological Hilbert invariants
`inv_v((a) ∪ (b)) ∈ ZMod 2` sum to zero over all places `v` of `ℚ`. This file evaluates that sum
when `a = p` and `b = q` are distinct odd primes, and so identifies Hilbert reciprocity for `p`
and `q` with the quadratic reciprocity law.

Through `TauCeti.finprod_hilbertSymbol_mul_prod_hilbertSymbol_eq_hilbertSign` the sign of the sum
is the product of the norm-equation Hilbert symbols `(p, q)_v`, and each factor is explicit:

* at the real place, `(p, q)_∞ = 1`, as `p` and `q` are positive;
* at a prime `ℓ ∉ {2, p, q}`, both `p` and `q` are `ℓ`-adic units and `(p, q)_ℓ = 1`;
* at `p`, `(p, q)_p = (q / p)`, and at `q`, `(p, q)_q = (p / q)`, the Legendre symbols;
* at `2`, `(p, q)_2 = (-1) ^ ((p - 1)/2 · (q - 1)/2)`, by Serre's dyadic formula.

The finite places of `ℚ` are read in `ℚ_ℓ` through `TauCeti.hilbertSymbol_unitAtFinitePlace_rat`.
Hence the sum vanishes exactly when `(p / q) (q / p) = (-1) ^ ((p - 1)/2 · (q - 1)/2)`. Read from
left to right this derives quadratic reciprocity from Hilbert reciprocity; read from right to left
with Mathlib's `legendreSym.quadratic_reciprocity`, it checks the normalization of the
cohomological invariants at `2`, `p` and `q` against the classical symbols.

## Main results

* `coe_finprod_hilbertSymbol_unitAtFinitePlace_eq_legendreSym`: the product of the Hilbert
  symbols `(p, q)_v` over the finite places.
* `coe_hilbertSign_sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt`: the sign
  of the sum of the cohomological Hilbert invariants of `p` and `q`.
* `sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt_eq_zero_iff`: Hilbert
  reciprocity for `p` and `q` is equivalent to quadratic reciprocity for `p` and `q`.

All declarations are in the namespace `TauCeti.ClassFieldTheory`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.2, Theorem 1 (the local symbols) and
  §2.2, proof of Theorem 3 (their product for two odd primes).
-/

public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Rat.HeightOneSpectrum

namespace TauCeti.ClassFieldTheory

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {a b : ℚˣ}

/-- The Hilbert symbol over `ℚ_ℓ` of two global units that are the primes `p` and `q`. -/
private theorem hilbertSymbol_units_map_eq_natCast (ℓ : Nat.Primes) (ha : (a : ℚ) = p)
    (hb : (b : ℚ) = q) :
    hilbertSymbol (Units.map (algebraMap ℚ ℚ_[ℓ]).toMonoidHom a)
        (Units.map (algebraMap ℚ ℚ_[ℓ]).toMonoidHom b) =
      hilbertSymbol (Units.mk0 (p : ℚ_[ℓ]) (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))
        (Units.mk0 (q : ℚ_[ℓ]) (Nat.cast_ne_zero.2 (Fact.out : q.Prime).ne_zero)) := by
  congr 1 <;> ext <;> simp [ha, hb]

/-- **The finite part of the Hilbert product formula for two odd primes.** For distinct odd
primes `p` and `q`, the product over the finite places `v` of `ℚ` of the Hilbert symbols
`(p, q)_v` is `(-1) ^ ((p - 1)/2 · (q - 1)/2) · (q / p) · (p / q)`: the place `2` contributes the
sign, the places `p` and `q` the two Legendre symbols, and every other place `1`. -/
theorem coe_finprod_hilbertSymbol_unitAtFinitePlace_eq_legendreSym (hp : p ≠ 2) (hq : q ≠ 2)
    (hpq : p ≠ q) (ha : (a : ℚ) = p) (hb : (b : ℚ) = q) :
    ((∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) : ℤˣ) : ℤ) =
      (-1) ^ (p / 2 * (q / 2)) * legendreSym p q * legendreSym q p := by
  have hpp : p.Prime := Fact.out
  have hqp : q.Prime := Fact.out
  have hpq' : ¬ p ∣ q := fun h ↦ hpq ((Nat.prime_dvd_prime_iff_eq hpp hqp).1 h)
  have hqp' : ¬ q ∣ p := fun h ↦ hpq ((Nat.prime_dvd_prime_iff_eq hqp hpp).1 h).symm
  let P₂ : Nat.Primes := ⟨2, Nat.prime_two⟩
  let Pp : Nat.Primes := ⟨p, hpp⟩
  let Pq : Nat.Primes := ⟨q, hqp⟩
  rw [← finprod_comp_equiv (primesEquiv (R := 𝓞 ℚ)).symm,
    finprod_congr fun ℓ ↦ (hilbertSymbol_unitAtFinitePlace_rat ℓ a b).trans
      (hilbertSymbol_units_map_eq_natCast ℓ ha hb),
    finprod_eq_prod_of_mulSupport_subset (s := {P₂, Pp, Pq}) _ fun ℓ hℓ ↦ ?_]
  · have hne {x y : Nat.Primes} (h : (x : ℕ) ≠ y) : x ≠ y := fun e ↦ h (congrArg _ e)
    have h2p : P₂ ∉ ({Pp, Pq} : Finset Nat.Primes) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hne (Ne.symm hp), hne (Ne.symm hq)⟩
    rw [Finset.prod_insert h2p, Finset.prod_insert (Finset.notMem_singleton.2 (hne hpq)),
      Finset.prod_singleton, Units.val_mul, Units.val_mul, mul_assoc]
    -- The three factors: the dyadic sign and the two Legendre symbols.
    have hP := Padic.hilbertSymbol_intCast_self_eq_legendreSym hp (n := q)
      (Int.natCast_dvd_natCast.not.2 hpq')
    have hQ := Padic.hilbertSymbol_intCast_self_eq_legendreSym hq (n := p)
      (Int.natCast_dvd_natCast.not.2 hqp')
    simp only [Int.cast_natCast] at hP hQ
    rw [hilbertSymbol_comm] at hP
    congr 1
    · exact congrArg Units.val (hilbertSymbol_natCast_natCast_padicTwo (hpp.odd_of_ne_two hp)
        (hqp.odd_of_ne_two hq)) |>.trans (by simp)
    · exact congrArg₂ (· * ·) hP hQ
  · -- At every other prime both `p` and `q` are units and the symbol is `1`.
    by_contra hmem
    apply hℓ
    have hℓ2 : (ℓ : ℕ) ≠ 2 := fun h ↦ hmem (by simp [show ℓ = P₂ from Subtype.ext h])
    have hℓp : ¬ (ℓ : ℕ) ∣ p := fun h ↦ hmem (by
      simp [show ℓ = Pp from Subtype.ext ((Nat.prime_dvd_prime_iff_eq ℓ.2 hpp).1 h)])
    have hℓq : ¬ (ℓ : ℕ) ∣ q := fun h ↦ hmem (by
      simp [show ℓ = Pq from Subtype.ext ((Nat.prime_dvd_prime_iff_eq ℓ.2 hqp).1 h)])
    simpa only [Int.cast_natCast] using Padic.hilbertSymbol_intCast_intCast_eq_one hℓ2 (m := p)
      (n := q) (Int.natCast_dvd_natCast.not.2 hℓp) (Int.natCast_dvd_natCast.not.2 hℓq)

/-- **The Hilbert reciprocity sum of two odd primes.** For distinct odd primes `p` and `q`, the sign
of the sum over all places of `ℚ` of the cohomological Hilbert invariants of `p` and `q` is
`(-1) ^ ((p - 1)/2 · (q - 1)/2) · (q / p) · (p / q)`. The real place contributes nothing, as `p`
and `q` are positive. -/
theorem coe_hilbertSign_sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) (ha : (a : ℚ) = p) (hb : (b : ℚ) = q) :
    ((hilbertSign ((∑ v ∈ finiteHilbertSupport ℚ a b, finiteHilbertInvariantAt ℚ v a b) +
        ∑ w : InfinitePlace ℚ, infiniteHilbertInvariantAt ℚ w a b) : ℤˣ) : ℤ) =
      (-1) ^ (p / 2 * (q / 2)) * legendreSym p q * legendreSym q p := by
  rw [← finprod_hilbertSymbol_mul_prod_hilbertSymbol_eq_hilbertSign, Units.val_mul,
    coe_finprod_hilbertSymbol_unitAtFinitePlace_eq_legendreSym hp hq hpq ha hb,
    Finset.prod_eq_one fun w _ ↦ (hilbertSymbol_unitAtRealPlace_eq_one_iff w a b).2
      (Or.inl (by simpa [ha] using (Fact.out : p.Prime).pos)), Units.val_one, mul_one]

/-- **Quadratic reciprocity is Hilbert reciprocity for two odd primes.** For distinct odd primes
`p` and `q`, the cohomological Hilbert invariants of `p` and `q` sum to zero over the places of
`ℚ` exactly when `(p / q) (q / p) = (-1) ^ ((p - 1)/2 · (q - 1)/2)`. So Hilbert's reciprocity law
`∑_v inv_v((p) ∪ (q)) = 0` gives the quadratic reciprocity law, its dyadic factor being the sign. -/
theorem sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt_eq_zero_iff
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) (ha : (a : ℚ) = p) (hb : (b : ℚ) = q) :
    (∑ v ∈ finiteHilbertSupport ℚ a b, finiteHilbertInvariantAt ℚ v a b) +
        ∑ w : InfinitePlace ℚ, infiniteHilbertInvariantAt ℚ w a b = 0 ↔
      legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2)) := by
  rw [← hilbertSign_eq_one_iff, Units.ext_iff,
    coe_hilbertSign_sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt hp hq hpq ha
      hb, Units.val_one]
  have hs : ((-1 : ℤ) ^ (p / 2 * (q / 2))) * (-1) ^ (p / 2 * (q / 2)) = 1 := by
    rw [← mul_pow]
    simp
  constructor <;> intro h
  · linear_combination (-1 : ℤ) ^ (p / 2 * (q / 2)) * h -
      legendreSym p q * legendreSym q p * hs
  · linear_combination (-1 : ℤ) ^ (p / 2 * (q / 2)) * h + hs

end TauCeti.ClassFieldTheory
