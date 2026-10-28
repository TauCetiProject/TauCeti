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
and `q` with the quadratic reciprocity law; and when `a` is `-1` or `2` and `b = p` is an odd
prime, identifying Hilbert reciprocity with the two supplementary laws.

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

The two supplementary laws come from the same sum for `a = -1` and for `a = 2`, with `b = p` an odd
prime. Only the places `2` and `p` contribute: `(a, p)_p = (a / p)`, the real place contributes
nothing as `p` is positive, and at `2` Serre's formula gives `(-1, p)_2 = χ₄(p)` and
`(2, p)_2 = χ₈(p)`. So Hilbert reciprocity for `-1` and `p` is the first supplementary law
`(-1 / p) = χ₄(p) = (-1) ^ ((p - 1)/2)`, and for `2` and `p` it is the second supplementary law
`(2 / p) = χ₈(p) = (-1) ^ ((p² - 1)/8)`, in the forms of Mathlib's `legendreSym.at_neg_one` and
`legendreSym.at_two`.

## Main results

* `coe_finprod_hilbertSymbol_unitAtFinitePlace_eq_legendreSym`: the product of the Hilbert
  symbols `(p, q)_v` over the finite places.
* `coe_hilbertSign_sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt`: the sign
  of the sum of the cohomological Hilbert invariants of `p` and `q`.
* `sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt_eq_zero_iff`: Hilbert
  reciprocity for `p` and `q` is equivalent to quadratic reciprocity for `p` and `q`.
* `coe_finprod_hilbertSymbol_unitAtFinitePlace_eq_mul_legendreSym`: the product of the Hilbert
  symbols `(m, p)_v` over the finite places, for an integer `m` divisible by no odd prime.
* `coe_hilbertSign_sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt_eq_mul`: the
  sign `(m, p)_2 · (m / p)` of the sum of the cohomological Hilbert invariants of such `m` and `p`.
* `sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt_eq_zero_iff_neg_one` and
  `sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt_eq_zero_iff_two`: Hilbert
  reciprocity for `-1` and `p`, respectively for `2` and `p`, is equivalent to the first,
  respectively the second, supplementary law for `p`.

All declarations are in the namespace `TauCeti.ClassFieldTheory`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.2, Theorem 1 (the local symbols) and
  §2.2, proof of Theorem 3 (their product for two odd primes, and for `-1` or `2` and an odd
  prime).
-/

public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Rat.HeightOneSpectrum

namespace TauCeti.ClassFieldTheory

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {a b : ℚˣ}

/-- The Hilbert symbol over `ℚ_ℓ` of two global units, through prescribed values in `ℚ_ℓ`. -/
private theorem hilbertSymbol_units_map_eq (ℓ : ℕ) [Fact ℓ.Prime] {x y : ℚ_[ℓ]ˣ}
    (ha : ((a : ℚ) : ℚ_[ℓ]) = x) (hb : ((b : ℚ) : ℚ_[ℓ]) = y) :
    hilbertSymbol (Units.map (algebraMap ℚ ℚ_[ℓ]).toMonoidHom a)
        (Units.map (algebraMap ℚ ℚ_[ℓ]).toMonoidHom b) = hilbertSymbol x y := by
  congr 1 <;> ext <;> simpa

/-- The product over the finite places of `ℚ` of the Hilbert symbols of two integers `m` and `n`
is the product of their Hilbert symbols over `ℚ_ℓ` for `ℓ` in any finite set `S` of primes
containing `2` and every prime dividing `m` or `n`: at an odd prime dividing neither, both are
units and the symbol is `1`. -/
private theorem finprod_hilbertSymbol_unitAtFinitePlace_eq_prod {m n : ℤ} (S : Finset Nat.Primes)
    (hS : ∀ ℓ : Nat.Primes, ℓ ∉ S → (ℓ : ℕ) ≠ 2 ∧ ¬ (ℓ : ℤ) ∣ m ∧ ¬ (ℓ : ℤ) ∣ n)
    (ha : (a : ℚ) = m) (hb : (b : ℚ) = n) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) =
      ∏ ℓ ∈ S, hilbertSymbol (Units.map (algebraMap ℚ ℚ_[ℓ]).toMonoidHom a)
        (Units.map (algebraMap ℚ ℚ_[ℓ]).toMonoidHom b) := by
  rw [← finprod_comp_equiv (primesEquiv (R := 𝓞 ℚ)).symm,
    finprod_congr fun ℓ ↦ hilbertSymbol_unitAtFinitePlace_rat ℓ a b,
    finprod_eq_prod_of_mulSupport_subset _ fun ℓ hℓ ↦ ?_]
  by_contra hmem
  obtain ⟨hℓ2, hℓm, hℓn⟩ := hS ℓ hmem
  exact hℓ ((hilbertSymbol_units_map_eq ℓ (by simp [ha]) (by simp [hb])).trans
    (Padic.hilbertSymbol_intCast_intCast_eq_one hℓ2 hℓm hℓn))

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
  rw [finprod_hilbertSymbol_unitAtFinitePlace_eq_prod (m := p) (n := q) {P₂, Pp, Pq}
    (fun ℓ hmem ↦ ?_) (by simp [ha]) (by simp [hb])]
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
    rw [hilbertSymbol_comm] at hP
    congr 1
    · exact congrArg Units.val ((hilbertSymbol_units_map_eq P₂ (by simp [ha]) (by simp [hb])).trans
        (hilbertSymbol_natCast_natCast_padicTwo (hpp.odd_of_ne_two hp)
          (hqp.odd_of_ne_two hq))) |>.trans (by simp)
    · exact congrArg₂ (· * ·)
        (congrArg Units.val (hilbertSymbol_units_map_eq Pp (by simp [ha]) (by simp [hb]))
          |>.trans hP)
        (congrArg Units.val (hilbertSymbol_units_map_eq Pq (by simp [ha]) (by simp [hb]))
          |>.trans hQ)
  · -- At every other prime both `p` and `q` are units.
    have hℓ2 : (ℓ : ℕ) ≠ 2 := fun h ↦ hmem (by simp [show ℓ = P₂ from Subtype.ext h])
    have hℓp : ¬ (ℓ : ℕ) ∣ p := fun h ↦ hmem (by
      simp [show ℓ = Pp from Subtype.ext ((Nat.prime_dvd_prime_iff_eq ℓ.2 hpp).1 h)])
    have hℓq : ¬ (ℓ : ℕ) ∣ q := fun h ↦ hmem (by
      simp [show ℓ = Pq from Subtype.ext ((Nat.prime_dvd_prime_iff_eq ℓ.2 hqp).1 h)])
    exact ⟨hℓ2, Int.natCast_dvd_natCast.not.2 hℓp, Int.natCast_dvd_natCast.not.2 hℓq⟩

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

/-- Reading the sign `s · y` of a Hilbert reciprocity sum, with `s * s = 1`, as the equation
`y = s`: this turns the evaluated sign of the sum into a reciprocity law. -/
private theorem sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt_eq_zero_iff_of
    {s y : ℤ} (hs : s * s = 1)
    (h : ((hilbertSign ((∑ v ∈ finiteHilbertSupport ℚ a b, finiteHilbertInvariantAt ℚ v a b) +
        ∑ w : InfinitePlace ℚ, infiniteHilbertInvariantAt ℚ w a b) : ℤˣ) : ℤ) = s * y) :
    (∑ v ∈ finiteHilbertSupport ℚ a b, finiteHilbertInvariantAt ℚ v a b) +
        ∑ w : InfinitePlace ℚ, infiniteHilbertInvariantAt ℚ w a b = 0 ↔ y = s := by
  rw [← hilbertSign_eq_one_iff, Units.ext_iff, h, Units.val_one]
  constructor <;> intro h
  · linear_combination s * h - y * hs
  · linear_combination s * h + hs

/-- **Quadratic reciprocity is Hilbert reciprocity for two odd primes.** For distinct odd primes
`p` and `q`, the cohomological Hilbert invariants of `p` and `q` sum to zero over the places of
`ℚ` exactly when `(p / q) (q / p) = (-1) ^ ((p - 1)/2 · (q - 1)/2)`. So Hilbert's reciprocity law
`∑_v inv_v((p) ∪ (q)) = 0` gives the quadratic reciprocity law, its dyadic factor being the sign. -/
theorem sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt_eq_zero_iff
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) (ha : (a : ℚ) = p) (hb : (b : ℚ) = q) :
    (∑ v ∈ finiteHilbertSupport ℚ a b, finiteHilbertInvariantAt ℚ v a b) +
        ∑ w : InfinitePlace ℚ, infiniteHilbertInvariantAt ℚ w a b = 0 ↔
      legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2)) := by
  refine sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt_eq_zero_iff_of
    (by rw [← mul_pow]; simp) ?_
  rw [coe_hilbertSign_sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt hp hq hpq ha
    hb]
  ring

/-! ### The supplementary laws -/

/-- **The finite part of the Hilbert product formula for an odd prime and a power of `2` up to
sign.** Let `p` be an odd prime and `m` an integer divisible by no odd prime. Then the product over
the finite places `v` of `ℚ` of the Hilbert symbols `(m, p)_v` is `(m, p)_2 · (m / p)`: the place
`p` contributes the Legendre symbol, and every place other than `2` and `p` contributes `1`. -/
theorem coe_finprod_hilbertSymbol_unitAtFinitePlace_eq_mul_legendreSym (hp : p ≠ 2) {m : ℤ}
    (hm : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ¬ (ℓ : ℤ) ∣ m) (ha : (a : ℚ) = m) (hb : (b : ℚ) = p) :
    ((∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) : ℤˣ) : ℤ) =
      (hilbertSymbol (Units.map (algebraMap ℚ ℚ_[2]).toMonoidHom a)
          (Units.map (algebraMap ℚ ℚ_[2]).toMonoidHom b) : ℤ) * legendreSym p m := by
  have hpp : p.Prime := Fact.out
  have hpm : ¬ (p : ℤ) ∣ m := hm p hpp hp
  let P₂ : Nat.Primes := ⟨2, Nat.prime_two⟩
  let Pp : Nat.Primes := ⟨p, hpp⟩
  have h2p : P₂ ≠ Pp := fun h ↦ hp (congrArg Subtype.val h).symm
  rw [finprod_hilbertSymbol_unitAtFinitePlace_eq_prod (m := m) (n := p) {P₂, Pp}
    (fun ℓ hmem ↦ ?_) ha (by simp [hb]), Finset.prod_pair h2p, Units.val_mul]
  · -- The place `p` contributes the Legendre symbol `(m / p)`.
    exact congrArg _ (congrArg Units.val (hilbertSymbol_units_map_eq p (by simp [ha])
      (by simp [hb])) |>.trans (Padic.hilbertSymbol_intCast_self_eq_legendreSym hp hpm))
  · -- At every other prime both `m` and `p` are units.
    have hℓ2 : (ℓ : ℕ) ≠ 2 := fun h ↦ hmem (by simp [show ℓ = P₂ from Subtype.ext h])
    have hℓp : ¬ (ℓ : ℕ) ∣ p := fun h ↦ hmem (by
      simp [show ℓ = Pp from Subtype.ext ((Nat.prime_dvd_prime_iff_eq ℓ.2 hpp).1 h)])
    exact ⟨hℓ2, hm ℓ ℓ.2 hℓ2, Int.natCast_dvd_natCast.not.2 hℓp⟩

/-- **The Hilbert reciprocity sum of an odd prime and a power of `2` up to sign.** Let `p` be an
odd prime and `m` an integer divisible by no odd prime. Then the sign of the sum over all places of
`ℚ` of the cohomological Hilbert invariants of `m` and `p` is `(m, p)_2 · (m / p)`. The real place
contributes nothing, as `p` is positive. -/
theorem coe_hilbertSign_sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt_eq_mul
    (hp : p ≠ 2) {m : ℤ} (hm : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ¬ (ℓ : ℤ) ∣ m) (ha : (a : ℚ) = m)
    (hb : (b : ℚ) = p) :
    ((hilbertSign ((∑ v ∈ finiteHilbertSupport ℚ a b, finiteHilbertInvariantAt ℚ v a b) +
        ∑ w : InfinitePlace ℚ, infiniteHilbertInvariantAt ℚ w a b) : ℤˣ) : ℤ) =
      (hilbertSymbol (Units.map (algebraMap ℚ ℚ_[2]).toMonoidHom a)
          (Units.map (algebraMap ℚ ℚ_[2]).toMonoidHom b) : ℤ) * legendreSym p m := by
  rw [← finprod_hilbertSymbol_mul_prod_hilbertSymbol_eq_hilbertSign, Units.val_mul,
    coe_finprod_hilbertSymbol_unitAtFinitePlace_eq_mul_legendreSym hp hm ha hb,
    Finset.prod_eq_one fun w _ ↦ (hilbertSymbol_unitAtRealPlace_eq_one_iff w a b).2
      (Or.inr (by simpa [hb] using (Fact.out : p.Prime).pos)), Units.val_one, mul_one]

/-- **The Hilbert reciprocity sum of `-1` and an odd prime.** For an odd prime `p`, the sign of the
sum over all places of `ℚ` of the cohomological Hilbert invariants of `-1` and `p` is
`χ₄(p) · (-1 / p)`. The real place contributes nothing, as `p` is positive, and the place `2`
contributes `(-1, p)_2 = χ₄(p)`. -/
theorem coe_hilbertSign_sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt_neg_one
    (hp : p ≠ 2) (ha : (a : ℚ) = -1) (hb : (b : ℚ) = p) :
    ((hilbertSign ((∑ v ∈ finiteHilbertSupport ℚ a b, finiteHilbertInvariantAt ℚ v a b) +
        ∑ w : InfinitePlace ℚ, infiniteHilbertInvariantAt ℚ w a b) : ℤˣ) : ℤ) =
      ZMod.χ₄ p * legendreSym p (-1) := by
  have hm : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ¬ (ℓ : ℤ) ∣ -1 := fun ℓ hℓ _ h ↦
    hℓ.one_lt.ne' (Nat.dvd_one.1 (Int.natCast_dvd_natCast.1 (dvd_neg.1 h)))
  rw [coe_hilbertSign_sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt_eq_mul hp hm
    (by simpa using ha) hb, congrArg Units.val (hilbertSymbol_units_map_eq 2 (by simp [ha])
      (by simp [hb])) |>.trans (coe_hilbertSymbol_neg_one_natCast_padicTwo
        ((Fact.out : p.Prime).odd_of_ne_two hp))]

/-- **The first supplementary law is Hilbert reciprocity for `-1` and an odd prime.** For an odd
prime `p`, the cohomological Hilbert invariants of `-1` and `p` sum to zero over the places of `ℚ`
exactly when `(-1 / p) = χ₄(p)`, that is `(-1 / p) = (-1) ^ ((p - 1)/2)`. -/
theorem sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt_eq_zero_iff_neg_one
    (hp : p ≠ 2) (ha : (a : ℚ) = -1) (hb : (b : ℚ) = p) :
    (∑ v ∈ finiteHilbertSupport ℚ a b, finiteHilbertInvariantAt ℚ v a b) +
        ∑ w : InfinitePlace ℚ, infiniteHilbertInvariantAt ℚ w a b = 0 ↔
      legendreSym p (-1) = ZMod.χ₄ p := by
  have hodd := Nat.odd_iff.1 ((Fact.out : p.Prime).odd_of_ne_two hp)
  have hs : ZMod.χ₄ p * ZMod.χ₄ p = 1 := by
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    split_ifs <;> omega
  exact sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt_eq_zero_iff_of hs
    (coe_hilbertSign_sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt_neg_one hp ha
      hb)

/-- **The Hilbert reciprocity sum of `2` and an odd prime.** For an odd prime `p`, the sign of the
sum over all places of `ℚ` of the cohomological Hilbert invariants of `2` and `p` is
`χ₈(p) · (2 / p)`. The real place contributes nothing, as `p` is positive, and the place `2`
contributes `(2, p)_2 = χ₈(p)`. -/
theorem coe_hilbertSign_sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt_two
    (hp : p ≠ 2) (ha : (a : ℚ) = 2) (hb : (b : ℚ) = p) :
    ((hilbertSign ((∑ v ∈ finiteHilbertSupport ℚ a b, finiteHilbertInvariantAt ℚ v a b) +
        ∑ w : InfinitePlace ℚ, infiniteHilbertInvariantAt ℚ w a b) : ℤˣ) : ℤ) =
      ZMod.χ₈ p * legendreSym p 2 := by
  have hm : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ¬ (ℓ : ℤ) ∣ 2 := fun ℓ hℓ hℓ2 h ↦
    hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (Int.natCast_dvd_natCast.1 h))
  rw [coe_hilbertSign_sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt_eq_mul hp hm
    (by simpa using ha) hb, congrArg Units.val (hilbertSymbol_units_map_eq 2 (by simp [ha])
      (by simp [hb])) |>.trans (coe_hilbertSymbol_two_natCast_padicTwo
        ((Fact.out : p.Prime).odd_of_ne_two hp))]

/-- **The second supplementary law is Hilbert reciprocity for `2` and an odd prime.** For an odd
prime `p`, the cohomological Hilbert invariants of `2` and `p` sum to zero over the places of `ℚ`
exactly when `(2 / p) = χ₈(p)`, that is `(2 / p) = (-1) ^ ((p² - 1)/8)`. -/
theorem sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt_eq_zero_iff_two
    (hp : p ≠ 2) (ha : (a : ℚ) = 2) (hb : (b : ℚ) = p) :
    (∑ v ∈ finiteHilbertSupport ℚ a b, finiteHilbertInvariantAt ℚ v a b) +
        ∑ w : InfinitePlace ℚ, infiniteHilbertInvariantAt ℚ w a b = 0 ↔
      legendreSym p 2 = ZMod.χ₈ p := by
  have hodd := Nat.odd_iff.1 ((Fact.out : p.Prime).odd_of_ne_two hp)
  have hs : ZMod.χ₈ p * ZMod.χ₈ p = 1 := by
    rw [ZMod.χ₈_nat_eq_if_mod_eight]
    split_ifs <;> omega
  exact sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt_eq_zero_iff_of hs
    (coe_hilbertSign_sum_finiteHilbertInvariantAt_add_sum_infiniteHilbertInvariantAt_two hp ha hb)

end TauCeti.ClassFieldTheory
