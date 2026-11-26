/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.DedekindPsi
import TauCeti.Data.Nat.GCD
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Simproc.Divisors
import Mathlib.Tactic.Simproc.Factors

/-!
# Orbit arithmetic of symplectic cyclic actions on K3 surfaces

Let the cyclic group `C_n` act faithfully and symplectically on a K3 surface `X`, with `n`
invertible in the (algebraically closed) ground field. Every point with nontrivial stabilizer is
isolated, and for a divisor `m > 1` of `n` let `a m` be the number of orbits whose stabilizer has
order `m`; such an orbit has `n / m` points. The quotient `X / C_n` has an `A_{m-1}` singularity at
the image of each such orbit, and its minimal resolution is again a K3 surface. Comparing Euler
characteristics (`e(X) = 24`, a free orbit counts `n` times, an `A_{m-1}` resolution contributes
`m`) gives Nikulin's orbit identity `24 (n - 1) = ∑_{m ∣ n} a m * (n / m) * (m ^ 2 - 1)`.
Applying it to the subgroup of order `d`, which acts on a point with stabilizer of order `m` with
stabilizer of order `gcd (m, d)`, gives the relation
`24 (d - 1) = ∑_{m ∣ n} (n / m) * a m * (gcd (m, d) ^ 2 - 1)` for every divisor `d` of `n`.

This file develops the purely arithmetic consequences of these relations:

* the number of points fixed by the subgroup of order `d > 1` is the value at `d` of the rational
  Mathieu function `ε d = 24 / ψ d = 24 / (d * ∏_{p ∣ d} (1 + 1 / p))`, with `ψ` the Dedekind ψ
  function, the character of the Mathieu permutation representation at an element of order `d`;
* if the exceptional root lattice `⨁_{m ∣ n} A_{m-1} ^ (a m)` has rank at most `21`, as it must
  inside the Picard lattice of the resolution, then `n ∈ {1, 2, 3, 4, 5, 6, 7, 8, 11, 14, 15}`;
* for `n = 11, 14, 15` the orbit counts are forced, the root lattices are `2 A₁₀`,
  `A₁₃ ⊕ A₆ ⊕ A₁` and `A₁₄ ⊕ A₄ ⊕ A₂`, and they have rank `20`; in particular a rank bound of `19`,
  as in characteristic zero, leaves `n ≤ 8`.

The relations are inverted along the divisor lattice using Jordan's totient function `J₂`,
through `gcd (m, d) ^ 2 = ∑_{e ∣ gcd (m, d)} J₂ e` and `J₂ e * ε e = 24 * φ e`, the latter
from `J₂ = ψ * φ`.

## Main definitions

* `TauCeti.mathieuFunction`: the rational Mathieu function `ε = 24 / ψ`.
* `TauCeti.IsK3CyclicOrbitData n a`: the orbit relations above, for all divisors `d` of `n`.
* `TauCeti.cyclicFixedPointCount n a d`: the number `∑_{d ∣ m ∣ n} (n / m) * a m` of points
  fixed by the subgroup of order `d`.
* `TauCeti.cyclicRootRank n a`: the rank `∑_{m ∣ n} a m * (m - 1)` of the exceptional root
  lattice of the resolved quotient.

## Main results

* `TauCeti.IsK3CyclicOrbitData.cyclicFixedPointCount_eq_mathieuFunction`: the fixed-point count
  of the subgroup of order `d > 1` is `ε d`.
* `TauCeti.IsK3CyclicOrbitData.mem_candidates`: the list of possible orders under the rank bound
  `21`.
* `TauCeti.IsK3CyclicOrbitData.cyclicRootRank_eq_twenty`: the root rank is `20` for orders
  `11`, `14` and `15`.
* `TauCeti.IsK3CyclicOrbitData.le_eight`: under the rank bound `19`, `n ≤ 8`.

## References

* V. V. Nikulin, *Finite automorphism groups of Kähler K3 surfaces*, Trans. Moscow Math. Soc.
  38 (1980), §5.
* I. Dolgachev and J. Keum, *Finite groups of symplectic automorphisms of K3 surfaces in positive
  characteristic*, Ann. of Math. 169 (2009), Lemma 3.1–3.2 and Theorem 3.3.
* S. Mukai, *Finite groups of automorphisms of K3 surfaces and the Mathieu group*, Invent. Math.
  94 (1988), (0.1) and Proposition 1.4.
-/

public section

open Finset ArithmeticFunction

namespace TauCeti

/-! ### The rational Mathieu function -/

/-- The rational Mathieu function `ε n = 24 / ψ n = 24 / (n * ∏_{p ∣ n} (1 + 1 / p))`, where `ψ` is
the Dedekind ψ function `ArithmeticFunction.dedekindPsi` and the product runs over the primes
dividing `n`. As observed by Mukai, when `M₂₃` has an element of order `n`, `ε n` is the number of
letters that element fixes in the action of `M₂₃` on `24` letters, and when a K3 surface has a tame
symplectic automorphism of order `n`, `ε n` is its number of fixed points. Its value at `0` is `0`,
by the convention `x / 0 = 0`. -/
def mathieuFunction (n : ℕ) : ℚ :=
  24 / dedekindPsi n

theorem mathieuFunction_def (n : ℕ) : mathieuFunction n = 24 / dedekindPsi n := (rfl)

/-- `ε n` as `24 / (n * ∏_{p ∣ n} (1 + 1 / p))`, with the prime factors of `n` written as
`n.primeFactorsList.toFinset`: the evaluation step for concrete values of `ε`. On a numeral `n`,
the `Nat.primeFactorsList_ofNat` simproc factors `n.primeFactorsList`, so
`norm_num [mathieuFunction_eq_primeFactorsList]` computes `ε n`. There is no such simproc for
`n.primeFactors`, so the Euler product `dedekindPsi_eq_prod` alone does not suffice. -/
theorem mathieuFunction_eq_primeFactorsList (n : ℕ) :
    mathieuFunction n = 24 / (n * ∏ p ∈ n.primeFactorsList.toFinset, (1 + (p : ℚ)⁻¹)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [mathieuFunction_def]
  rw [Nat.toFinset_factors, mathieuFunction_def, dedekindPsi_eq_prod hn]

@[simp]
theorem mathieuFunction_zero : mathieuFunction 0 = 0 := by
  simp [mathieuFunction_def]

@[simp]
theorem mathieuFunction_one : mathieuFunction 1 = 24 := by
  simp [mathieuFunction_def]

/-- The value of `ε` at a prime power: `ε (p ^ k) = 24 / (p ^ (k - 1) * (p + 1))` for `k ≠ 0`. -/
theorem mathieuFunction_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    mathieuFunction (p ^ k) = 24 / ((p : ℚ) ^ (k - 1) * (p + 1)) := by
  simp [mathieuFunction_def, dedekindPsi_apply_prime_pow hp hk]

/-- The value of `ε` at a prime: `ε p = 24 / (p + 1)`. -/
@[simp]
theorem mathieuFunction_prime {p : ℕ} (hp : p.Prime) : mathieuFunction p = 24 / (p + 1) := by
  simpa using mathieuFunction_prime_pow hp one_ne_zero

/-- `ε` is multiplicative up to the factor `24`: `ε (m * n) = ε m * ε n / 24` for coprime `m`
and `n`. -/
theorem mathieuFunction_mul {m n : ℕ} (h : m.Coprime n) :
    mathieuFunction (m * n) = mathieuFunction m * mathieuFunction n / 24 := by
  rw [mathieuFunction_def, mathieuFunction_def, mathieuFunction_def,
    isMultiplicative_dedekindPsi.map_mul_of_coprime h, Int.cast_mul]
  rcases eq_or_ne (dedekindPsi m : ℚ) 0 with hm | hm
  · simp [hm]
  rcases eq_or_ne (dedekindPsi n : ℚ) 0 with hn | hn
  · simp [hn]
  field_simp

/-- `ε` is `24` times Euler's totient over Jordan's totient `J₂`: `ε n * J₂ n = 24 * φ n`. -/
theorem mathieuFunction_mul_jordanTotient (n : ℕ) :
    mathieuFunction n * jordanTotient 2 n = 24 * n.totient := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hψ : (dedekindPsi n : ℚ) ≠ 0 := Int.cast_ne_zero.2 (dedekindPsi_pos hn).ne'
  rw [mathieuFunction_def, ← dedekindPsi_mul_totient, Int.cast_mul, Int.cast_natCast]
  field_simp

/-! ### Orbit relations -/

/-- The orbit relations of a faithful tame symplectic action of the cyclic group of order `n` on a
K3 surface, in terms of the number `a m` of orbits with stabilizer of order `m`: for every divisor
`d` of `n`, `∑_{m ∣ n} (n / m) * a m * (gcd (m, d) ^ 2 - 1) = 24 * (d - 1)`. This is the Euler
characteristic identity for the resolved quotient by the subgroup of order `d`. The value `a 1`
(the free orbits, which are infinite in number) does not enter. -/
def IsK3CyclicOrbitData (n : ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ d ∈ n.divisors, ∑ m ∈ n.divisors, n / m * a m * (m.gcd d ^ 2 - 1) = 24 * (d - 1)

theorem isK3CyclicOrbitData_iff {n : ℕ} {a : ℕ → ℕ} :
    IsK3CyclicOrbitData n a ↔
      ∀ d ∈ n.divisors, ∑ m ∈ n.divisors, n / m * a m * (m.gcd d ^ 2 - 1) = 24 * (d - 1) :=
  Iff.rfl

/-- The number `∑_{d ∣ m ∣ n} (n / m) * a m` of points fixed by the subgroup of order `d` of the
cyclic group of order `n`, when `a m` orbits have stabilizer of order `m`. -/
def cyclicFixedPointCount (n : ℕ) (a : ℕ → ℕ) (d : ℕ) : ℕ :=
  ∑ m ∈ n.divisors with d ∣ m, n / m * a m

theorem cyclicFixedPointCount_def (n : ℕ) (a : ℕ → ℕ) (d : ℕ) :
    cyclicFixedPointCount n a d = ∑ m ∈ n.divisors with d ∣ m, n / m * a m := (rfl)

/-- The rank `∑_{m ∣ n} a m * (m - 1)` of the exceptional root lattice `⨁_{m ∣ n} A_{m-1} ^ (a m)`
of the minimal resolution of the quotient by the cyclic group of order `n`, when `a m` orbits have
stabilizer of order `m`. -/
def cyclicRootRank (n : ℕ) (a : ℕ → ℕ) : ℕ :=
  ∑ m ∈ n.divisors, a m * (m - 1)

theorem cyclicRootRank_def (n : ℕ) (a : ℕ → ℕ) :
    cyclicRootRank n a = ∑ m ∈ n.divisors, a m * (m - 1) := (rfl)

/-- The orbit identity of the full group: `∑_{m ∣ n} a m * (n / m) * (m ^ 2 - 1) = 24 * (n - 1)`. -/
theorem IsK3CyclicOrbitData.sum_eq_mul_sub_one {n : ℕ} {a : ℕ → ℕ}
    (h : IsK3CyclicOrbitData n a) :
    ∑ m ∈ n.divisors, a m * (n / m) * (m ^ 2 - 1) = 24 * (n - 1) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [← isK3CyclicOrbitData_iff.1 h n (Nat.mem_divisors_self n hn)]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [Nat.gcd_eq_left (Nat.dvd_of_mem_divisors hm), mul_comm (a m)]

/-- The orbit counts of the subgroup of order `d` of the cyclic group of order `n`: a point with
stabilizer of order `m` has stabilizer of order `gcd (m, d)` in the subgroup, and an orbit of the
whole group with stabilizer of order `m` splits into `n / lcm (m, d)` orbits of the subgroup. -/
def cyclicSubgroupOrbitCount (n : ℕ) (a : ℕ → ℕ) (d e : ℕ) : ℕ :=
  ∑ m ∈ n.divisors with m.gcd d = e, n / m.lcm d * a m

theorem cyclicSubgroupOrbitCount_def (n : ℕ) (a : ℕ → ℕ) (d e : ℕ) :
    cyclicSubgroupOrbitCount n a d e = ∑ m ∈ n.divisors with m.gcd d = e, n / m.lcm d * a m :=
  (rfl)

/-- The orbit relations pass to subgroups: the orbit counts of the subgroup of order `d` satisfy
the orbit relations of the cyclic group of order `d`. -/
theorem IsK3CyclicOrbitData.restrict {n : ℕ} {a : ℕ → ℕ}
    (h : IsK3CyclicOrbitData n a) (hn : n ≠ 0) {d : ℕ} (hd : d ∣ n) :
    IsK3CyclicOrbitData d (cyclicSubgroupOrbitCount n a d) := by
  refine isK3CyclicOrbitData_iff.2 fun d' hd' ↦ ?_
  have hd0 : d ≠ 0 := (Nat.mem_divisors.1 hd').2
  calc ∑ e ∈ d.divisors, d / e * cyclicSubgroupOrbitCount n a d e * (e.gcd d' ^ 2 - 1)
      = ∑ e ∈ d.divisors, ∑ m ∈ n.divisors with m.gcd d = e,
          n / m * a m * (m.gcd d' ^ 2 - 1) := by
        refine Finset.sum_congr rfl fun e _ ↦ ?_
        rw [cyclicSubgroupOrbitCount_def, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun m hm ↦ ?_
        obtain ⟨hmn, rfl⟩ := Finset.mem_filter.1 hm
        rw [Nat.gcd_assoc, Nat.gcd_eq_right (Nat.dvd_of_mem_divisors hd'),
          ← Nat.div_gcd_mul_div_lcm (Nat.dvd_of_mem_divisors hmn) hd]
        ring
    _ = ∑ m ∈ n.divisors, n / m * a m * (m.gcd d' ^ 2 - 1) :=
        Finset.sum_fiberwise_of_maps_to
          (fun m _ ↦ Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right m d, hd0⟩) _
    _ = 24 * (d' - 1) := isK3CyclicOrbitData_iff.1 h d'
        (Nat.mem_divisors.2 ⟨(Nat.dvd_of_mem_divisors hd').trans hd, hn⟩)

/-- The fixed-point counts of the subgroup of order `d`, computed from its orbit counts
`cyclicSubgroupOrbitCount n a d`, agree with those of the whole group: for `e ∣ d`, the subgroup of
order `e` fixes the same points either way. -/
theorem cyclicFixedPointCount_cyclicSubgroupOrbitCount {n : ℕ} (a : ℕ → ℕ) {d e : ℕ}
    (hd : d ∣ n) (he : e ∣ d) :
    cyclicFixedPointCount d (cyclicSubgroupOrbitCount n a d) e = cyclicFixedPointCount n a e := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [cyclicFixedPointCount_def, cyclicSubgroupOrbitCount_def]
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hn hd
  rw [cyclicFixedPointCount_def, cyclicFixedPointCount_def, Finset.sum_filter, Finset.sum_filter]
  calc ∑ f ∈ d.divisors, (if e ∣ f then d / f * cyclicSubgroupOrbitCount n a d f else 0)
      = ∑ f ∈ d.divisors, ∑ m ∈ n.divisors with m.gcd d = f,
          if e ∣ m then n / m * a m else 0 := by
        refine Finset.sum_congr rfl fun f _ ↦ ?_
        rw [cyclicSubgroupOrbitCount_def, Finset.mul_sum]
        -- `e ∣ gcd (m, d) ↔ e ∣ m`, since `e ∣ d`
        split_ifs with hef
        · refine Finset.sum_congr rfl fun m hm ↦ ?_
          obtain ⟨hmn, rfl⟩ := Finset.mem_filter.1 hm
          rw [ite_eq_left (hef.trans (Nat.gcd_dvd_left m d)), ← mul_assoc,
            Nat.div_gcd_mul_div_lcm (Nat.dvd_of_mem_divisors hmn) hd]
        · refine (Finset.sum_eq_zero fun m hm ↦ ?_).symm
          obtain ⟨-, rfl⟩ := Finset.mem_filter.1 hm
          exact ite_eq_right fun hem ↦ hef (Nat.dvd_gcd hem he)
    _ = ∑ m ∈ n.divisors, if e ∣ m then n / m * a m else 0 :=
        Finset.sum_fiberwise_of_maps_to
          (fun m _ ↦ Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right m d, hd0⟩) _

/-- A single orbit type contributes to the root rank. -/
theorem le_cyclicRootRank {n m : ℕ} (a : ℕ → ℕ) (hm : m ∈ n.divisors) :
    a m * (m - 1) ≤ cyclicRootRank n a :=
  Finset.single_le_sum (f := fun m ↦ a m * (m - 1)) (fun _ _ ↦ Nat.zero_le _) hm

/-- The points fixed by the subgroup of order `d` are those fixed by its overgroup of order
`d * q`, together with the points with stabilizer divisible by `d` but not by `d * q`. -/
private theorem cyclicFixedPointCount_eq_add (n : ℕ) (a : ℕ → ℕ) (d q : ℕ) :
    cyclicFixedPointCount n a d = cyclicFixedPointCount n a (d * q) +
      ∑ m ∈ n.divisors with d ∣ m ∧ ¬ d * q ∣ m, n / m * a m := by
  rw [cyclicFixedPointCount_def, cyclicFixedPointCount_def, ← Finset.sum_filter_add_sum_filter_not
    (n.divisors.filter (d ∣ ·)) (d * q ∣ ·), Finset.filter_filter, Finset.filter_filter]
  congr 2
  exact Finset.filter_congr fun m _ ↦
    ⟨fun h ↦ h.2, fun h ↦ ⟨Nat.dvd_trans (Nat.dvd_mul_right d q) h, h⟩⟩

/-- A subgroup fixes at least as many points as any of its overgroups. -/
theorem cyclicFixedPointCount_mul_le (n : ℕ) (a : ℕ → ℕ) (d q : ℕ) :
    cyclicFixedPointCount n a (d * q) ≤ cyclicFixedPointCount n a d :=
  (cyclicFixedPointCount_eq_add n a d q) ▸ Nat.le_add_right _ _

/-- For a prime `q` with `d * q ∣ n`, the difference of the fixed-point counts of the subgroups of
orders `d` and `d * q` is divisible by `q`: the points fixed by the subgroup of order `d` but not
by that of order `d * q` lie in orbits of the subgroup of order `d * q` of length divisible by
`q`. -/
theorem prime_dvd_cyclicFixedPointCount_sub {n d q : ℕ} (a : ℕ → ℕ) (hq : q.Prime)
    (hdq : d * q ∣ n) :
    q ∣ cyclicFixedPointCount n a d - cyclicFixedPointCount n a (d * q) := by
  rw [cyclicFixedPointCount_eq_add n a d q, Nat.add_sub_cancel_left]
  refine Finset.dvd_sum fun m hm ↦ Dvd.dvd.mul_right ?_ _
  rw [Finset.mem_filter] at hm
  obtain ⟨hmn, hdm, hdqm⟩ := hm
  obtain ⟨t, rfl⟩ := hdm
  have hm0 : d * t ≠ 0 := (Nat.pos_of_mem_divisors hmn).ne'
  replace hmn := Nat.mem_divisors.1 hmn
  -- if `q` did not divide `n / m`, then `d * q ∣ n = m * (n / m)` would force `d * q ∣ m`
  by_contra hqs
  apply hdqm
  have hqts : q ∣ t * (n / (d * t)) := by
    have hd0 : d ≠ 0 := left_ne_zero_of_mul hm0
    have := hdq
    rw [← Nat.mul_div_cancel' hmn.1, mul_assoc] at this
    exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hd0) this
  exact Nat.mul_dvd_mul_left d ((hq.dvd_mul.1 hqts).resolve_right hqs)

/-! ### Fixed-point counts -/

/-- The orbit relation at a divisor `d`, summed against `J₂` over the divisors of `d`. -/
private theorem IsK3CyclicOrbitData.sum_jordanTotient_mul {n : ℕ} {a : ℕ → ℕ}
    (h : IsK3CyclicOrbitData n a) {d : ℕ} (hd : d ∈ n.divisors) :
    ∑ e ∈ d.divisors, (jordanTotient 2 e * cyclicFixedPointCount n a e - 24 * e.totient) =
      cyclicFixedPointCount n a 1 - 24 := by
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  have hrel := isK3CyclicOrbitData_iff.1 h d hd
  have hcast : ∑ m ∈ n.divisors, ((n / m * a m : ℕ) : ℤ) * (((m.gcd d : ℕ) : ℤ) ^ 2 - 1) =
      24 * ((d : ℤ) - 1) := by
    have hle : ∀ m ∈ n.divisors, 1 ≤ m.gcd d ^ 2 := fun m _ ↦
      Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (Nat.gcd_ne_zero_right hd0))
    have := congrArg (fun x : ℕ ↦ (x : ℤ)) hrel
    simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] at this
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hd0), Nat.cast_one] at this
    rw [← this]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    rw [Nat.cast_sub (hle m hm)]
    push_cast
    ring
  have hexpand : ∑ m ∈ n.divisors, ((n / m * a m : ℕ) : ℤ) * ((m.gcd d : ℕ) : ℤ) ^ 2 =
      ∑ e ∈ d.divisors, jordanTotient 2 e * cyclicFixedPointCount n a e := by
    simp only [gcd_pow_eq_sum_jordanTotient 2 _ hd0, cyclicFixedPointCount_def, Nat.cast_sum,
      Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ ↦ Finset.sum_congr rfl fun m _ ↦ ?_
    split_ifs <;> ring
  have hone : (cyclicFixedPointCount n a 1 : ℤ) = ∑ m ∈ n.divisors, ((n / m * a m : ℕ) : ℤ) := by
    simp [cyclicFixedPointCount_def]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Nat.cast_sum, Nat.sum_totient, ← hexpand, hone]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib] at hcast
  linear_combination hcast

/-- The fixed-point counts determined by the orbit relations: for every divisor `d > 1` of `n`,
`J₂ d * F d = 24 * φ d`, where `F d` is the number of points fixed by the subgroup of order `d`. -/
theorem IsK3CyclicOrbitData.jordanTotient_mul_cyclicFixedPointCount {n : ℕ} {a : ℕ → ℕ}
    (h : IsK3CyclicOrbitData n a) {d : ℕ} (hd : d ∈ n.divisors) (hd1 : 1 < d) :
    jordanTotient 2 d * cyclicFixedPointCount n a d = 24 * d.totient := by
  -- Möbius inversion: `D e := J₂ e * F e - 24 * φ e` has the same sums over the divisors of each
  -- divisor of `n` as the function supported at `1` with value `D 1`, so it vanishes at every
  -- divisor `e > 1` of `n`, by strong induction on `e`.
  suffices jordanTotient 2 d * cyclicFixedPointCount n a d - 24 * d.totient = 0 from
    sub_eq_zero.1 this
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  have hsum := h.sum_jordanTotient_mul hd
  rw [← Nat.cons_self_properDivisors hd0, Finset.sum_cons,
    Finset.sum_eq_single_of_mem 1 (Nat.one_mem_properDivisors_iff_one_lt.2 hd1)] at hsum
  · simp only [jordanTotient_apply_one, Nat.totient_one, Nat.cast_one] at hsum
    linarith
  · intro e he he1
    obtain ⟨hed, hlt⟩ := Nat.mem_properDivisors.1 he
    have he0 : e ≠ 0 := by rintro rfl; exact hd0 (Nat.eq_zero_of_zero_dvd hed)
    exact ih e hlt (Nat.mem_divisors.2 ⟨hed.trans (Nat.dvd_of_mem_divisors hd),
      (Nat.mem_divisors.1 hd).2⟩) (by omega)

/-- The number of points fixed by the subgroup of order `d > 1` is the Mathieu function `ε d`. -/
theorem IsK3CyclicOrbitData.cyclicFixedPointCount_eq_mathieuFunction {n : ℕ} {a : ℕ → ℕ}
    (h : IsK3CyclicOrbitData n a) {d : ℕ} (hd : d ∈ n.divisors) (hd1 : 1 < d) :
    (cyclicFixedPointCount n a d : ℚ) = mathieuFunction d := by
  have hJ : (jordanTotient 2 d : ℚ) ≠ 0 :=
    Int.cast_ne_zero.2 (jordanTotient_pos two_ne_zero (by omega)).ne'
  have h1 := mathieuFunction_mul_jordanTotient d
  have h2 : (jordanTotient 2 d : ℚ) * cyclicFixedPointCount n a d = 24 * d.totient := by
    exact_mod_cast h.jordanTotient_mul_cyclicFixedPointCount hd hd1
  refine mul_left_cancel₀ hJ ?_
  rw [h2, ← h1, mul_comm]

/-- A fixed-point count is determined by an integral value of the Mathieu function. -/
private theorem IsK3CyclicOrbitData.cyclicFixedPointCount_eq {n : ℕ} {a : ℕ → ℕ}
    (h : IsK3CyclicOrbitData n a) (hn : n ≠ 0) {d k : ℕ} (hdn : d ∣ n) (hd1 : 1 < d)
    (hk : mathieuFunction d = k) : cyclicFixedPointCount n a d = k := by
  have := h.cyclicFixedPointCount_eq_mathieuFunction (Nat.mem_divisors.2 ⟨hdn, hn⟩) hd1
  exact_mod_cast this.trans hk

/-! ### The possible orders -/

/-- A natural number whose prime factors lie in `{2, 3, 5, 7, 11}` and which is divisible by none
of `9, 12, 16, 10, 21, 22, 25, 28, 33, 35, 49, 55, 77, 121` is one of
`1, 2, 3, 4, 5, 6, 7, 8, 11, 14, 15`. -/
private theorem mem_candidates_of_not_dvd {n : ℕ} (hn : n ≠ 0)
    (hp : ∀ p, p.Prime → p ∣ n → p ∈ ({2, 3, 5, 7, 11} : Finset ℕ))
    (hb : ∀ d ∈ ({9, 12, 16, 10, 21, 22, 25, 28, 33, 35, 49, 55, 77, 121} : Finset ℕ), ¬ d ∣ n) :
    n ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 11, 14, 15} : Finset ℕ) := by
  -- strong induction: remove one prime factor `p` and run through the finitely many products
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases eq_or_ne n 1 with rfl | hn1
  · decide
  obtain ⟨p, hpp, m, rfl⟩ := Nat.exists_prime_and_dvd hn1
  have hm0 : m ≠ 0 := right_ne_zero_of_mul hn
  have hm := ih m (lt_mul_left (Nat.pos_of_ne_zero hm0) hpp.one_lt) hm0
    (fun q hq hqm ↦ hp q hq (Dvd.dvd.mul_left hqm p))
    (fun d hd hdm ↦ hb d hd (Dvd.dvd.mul_left hdm p))
  have hp' := hp p hpp (dvd_mul_right p m)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm hp'
  revert hb
  rcases hp' with rfl | rfl | rfl | rfl | rfl <;>
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A prime dividing the order of the cyclic group is `2`, `3`, `5`, `7` or `11`, under the root
rank bound `21`: `ε p = 24 / (p + 1)` must be integral, and `p = 23` would need rank `22`. -/
private theorem IsK3CyclicOrbitData.prime_mem {n : ℕ} {a : ℕ → ℕ} (h : IsK3CyclicOrbitData n a)
    (hn : n ≠ 0) (hrank : cyclicRootRank n a ≤ 21) {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    p ∈ ({2, 3, 5, 7, 11} : Finset ℕ) := by
  have hk := h.cyclicFixedPointCount_eq_mathieuFunction (Nat.mem_divisors.2 ⟨hpn, hn⟩) hp.one_lt
  set k := cyclicFixedPointCount n a p
  have h24 : (p + 1) * k = 24 := by
    rw [mathieuFunction_prime hp, eq_div_iff (by positivity)] at hk
    exact_mod_cast (mul_comm _ _).trans hk
  have h23 : p ≠ 23 := by
    rintro rfl
    obtain ⟨m, hm, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (show k ≠ 0 by omega)
    rw [Finset.mem_filter] at hm
    have ham : 1 ≤ a m := Nat.one_le_iff_ne_zero.2 (right_ne_zero_of_mul hm0)
    have h23m : 23 ≤ m := Nat.le_of_dvd (Nat.pos_of_mem_divisors hm.1) hm.2
    have := le_cyclicRootRank a hm.1
    have : 1 * (m - 1) ≤ a m * (m - 1) := Nat.mul_le_mul_right _ ham
    omega
  have hle : p ≤ 23 := by
    have := Nat.le_of_dvd (by norm_num) (Dvd.intro k h24)
    omega
  interval_cases p <;> first | decide | omega | (exfalso; norm_num at hp)

/-- Orbit divisibility excludes a divisor `d * q` of `n` when the integral values `k = ε d` and
`l = ε (d * q)` have difference not divisible by the prime `q`. -/
private theorem IsK3CyclicOrbitData.not_dvd_of_not_dvd_sub {n : ℕ} {a : ℕ → ℕ}
    (h : IsK3CyclicOrbitData n a) (hn : n ≠ 0) {d q k l : ℕ} (hq : q.Prime) (hd1 : 1 < d)
    (hk : mathieuFunction d = k) (hl : mathieuFunction (d * q) = l) (hkl : ¬ q ∣ k - l) :
    ¬ d * q ∣ n := fun hdq ↦ by
  have hd := h.cyclicFixedPointCount_eq hn ((Nat.dvd_mul_right d q).trans hdq) hd1 hk
  have hdq' := h.cyclicFixedPointCount_eq hn hdq (one_lt_mul_of_lt_of_le hd1 hq.one_le) hl
  exact hkl (hd ▸ hdq' ▸ prime_dvd_cyclicFixedPointCount_sub a hq hdq)

/-- A divisor `d > 1` of `n` has integral `ε d`, so `d` does not divide `n` when `ε d = k / l` with
`l` not dividing `k`. -/
private theorem IsK3CyclicOrbitData.not_dvd_of_mathieuFunction_eq_div {n : ℕ} {a : ℕ → ℕ}
    (h : IsK3CyclicOrbitData n a) (hn : n ≠ 0) {d k l : ℕ} (hd1 : 1 < d) (hl : l ≠ 0)
    (hkl : mathieuFunction d = k / l) (hlk : ¬ l ∣ k) : ¬ d ∣ n := fun hdn ↦ by
  have hF := h.cyclicFixedPointCount_eq_mathieuFunction (Nat.mem_divisors.2 ⟨hdn, hn⟩) hd1
  rw [hkl, eq_div_iff (Nat.cast_ne_zero.2 hl)] at hF
  exact hlk ⟨cyclicFixedPointCount n a d, by rw [mul_comm]; exact_mod_cast hF.symm⟩

/-- The orders `10, 21, 22, 25, 28, 33, 35, 49, 55, 77, 121` have nonintegral `ε`, so none of them
divides the order of the cyclic group. -/
private theorem IsK3CyclicOrbitData.not_dvd_of_mem {n : ℕ} {a : ℕ → ℕ}
    (h : IsK3CyclicOrbitData n a) (hn : n ≠ 0) {d : ℕ}
    (hd : d ∈ ({10, 21, 22, 25, 28, 33, 35, 49, 55, 77, 121} : Finset ℕ)) : ¬ d ∣ n := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.not_dvd_of_mathieuFunction_eq_div hn (k := 4) (l := 3) (by norm_num) (by norm_num)
      (by norm_num [mathieuFunction_eq_primeFactorsList]) (by norm_num)
  · exact h.not_dvd_of_mathieuFunction_eq_div hn (k := 3) (l := 4) (by norm_num) (by norm_num)
      (by norm_num [mathieuFunction_eq_primeFactorsList]) (by norm_num)
  · exact h.not_dvd_of_mathieuFunction_eq_div hn (k := 2) (l := 3) (by norm_num) (by norm_num)
      (by norm_num [mathieuFunction_eq_primeFactorsList]) (by norm_num)
  · exact h.not_dvd_of_mathieuFunction_eq_div hn (k := 4) (l := 5) (by norm_num) (by norm_num)
      (by norm_num [mathieuFunction_eq_primeFactorsList]) (by norm_num)
  · exact h.not_dvd_of_mathieuFunction_eq_div hn (k := 1) (l := 2) (by norm_num) (by norm_num)
      (by norm_num [mathieuFunction_eq_primeFactorsList]) (by norm_num)
  · exact h.not_dvd_of_mathieuFunction_eq_div hn (k := 1) (l := 2) (by norm_num) (by norm_num)
      (by norm_num [mathieuFunction_eq_primeFactorsList]) (by norm_num)
  · exact h.not_dvd_of_mathieuFunction_eq_div hn (k := 1) (l := 2) (by norm_num) (by norm_num)
      (by norm_num [mathieuFunction_eq_primeFactorsList]) (by norm_num)
  · exact h.not_dvd_of_mathieuFunction_eq_div hn (k := 3) (l := 7) (by norm_num) (by norm_num)
      (by norm_num [mathieuFunction_eq_primeFactorsList]) (by norm_num)
  · exact h.not_dvd_of_mathieuFunction_eq_div hn (k := 1) (l := 3) (by norm_num) (by norm_num)
      (by norm_num [mathieuFunction_eq_primeFactorsList]) (by norm_num)
  · exact h.not_dvd_of_mathieuFunction_eq_div hn (k := 1) (l := 4) (by norm_num) (by norm_num)
      (by norm_num [mathieuFunction_eq_primeFactorsList]) (by norm_num)
  · exact h.not_dvd_of_mathieuFunction_eq_div hn (k := 2) (l := 11) (by norm_num) (by norm_num)
      (by norm_num [mathieuFunction_eq_primeFactorsList]) (by norm_num)

/-- **The possible orders of a symplectic cyclic action.** If the orbit relations hold for the
cyclic group of order `n ≠ 0` and the exceptional root lattice of the resolved quotient has rank at
most `21` (it is a negative definite sublattice of a Picard lattice of rank at most `22` and
signature `(1, ρ - 1)`), then `n` is one of `1, 2, 3, 4, 5, 6, 7, 8, 11, 14, 15`. -/
theorem IsK3CyclicOrbitData.mem_candidates {n : ℕ} {a : ℕ → ℕ} (h : IsK3CyclicOrbitData n a)
    (hn : n ≠ 0) (hrank : cyclicRootRank n a ≤ 21) :
    n ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 11, 14, 15} : Finset ℕ) := by
  refine mem_candidates_of_not_dvd hn (fun p hp hpn ↦ h.prime_mem hn hrank hp hpn)
    (fun d hd hdn ↦ ?_)
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert] at hd
  rcases hd with rfl | rfl | rfl | hd
  -- orders `9`, `12` and `16`: orbit divisibility over the subgroups of orders `3`, `6` and `8`
  · exact h.not_dvd_of_not_dvd_sub hn Nat.prime_three (d := 3) (k := 6) (l := 2) (by norm_num)
      (by norm_num)
      (by norm_num [mathieuFunction_eq_primeFactorsList]) (by norm_num) hdn
  · exact h.not_dvd_of_not_dvd_sub hn Nat.prime_two (d := 6) (k := 2) (l := 1) (by norm_num)
      (by norm_num [mathieuFunction_eq_primeFactorsList])
      (by norm_num [mathieuFunction_eq_primeFactorsList]) (by norm_num) hdn
  · exact h.not_dvd_of_not_dvd_sub hn Nat.prime_two (d := 8) (k := 2) (l := 1) (by norm_num)
      (by norm_num [mathieuFunction_eq_primeFactorsList])
      (by norm_num [mathieuFunction_eq_primeFactorsList]) (by norm_num) hdn
  -- the remaining orders have nonintegral `ε`
  · exact h.not_dvd_of_mem hn hd hdn

/-- The orbit counts of a symplectic action of order `11`: two orbits of fixed points. -/
theorem IsK3CyclicOrbitData.orbitCounts_eleven {a : ℕ → ℕ} (h : IsK3CyclicOrbitData 11 a) :
    a 11 = 2 := by
  have h11 := h.cyclicFixedPointCount_eq (by norm_num) (dvd_refl 11) (by norm_num) (k := 2)
    (by norm_num [mathieuFunction_eq_primeFactorsList])
  simp only [cyclicFixedPointCount_def, Nat.divisors_ofNat] at h11
  simpa [Finset.filter_insert, Finset.filter_singleton] using h11

/-- The orbit counts of a symplectic action of order `14`: one orbit each with stabilizer of order
`2`, `7` and `14`. -/
theorem IsK3CyclicOrbitData.orbitCounts_fourteen {a : ℕ → ℕ} (h : IsK3CyclicOrbitData 14 a) :
    a 2 = 1 ∧ a 7 = 1 ∧ a 14 = 1 := by
  have h2 := h.cyclicFixedPointCount_eq (by norm_num) (by norm_num : 2 ∣ 14) (by norm_num) (k := 8)
    (by norm_num [mathieuFunction_eq_primeFactorsList])
  have h7 := h.cyclicFixedPointCount_eq (by norm_num) (by norm_num : 7 ∣ 14) (by norm_num) (k := 3)
    (by norm_num [mathieuFunction_eq_primeFactorsList])
  have h14 := h.cyclicFixedPointCount_eq (by norm_num) (dvd_refl 14) (by norm_num) (k := 1)
    (by norm_num [mathieuFunction_eq_primeFactorsList])
  simp only [cyclicFixedPointCount_def, Nat.divisors_ofNat] at h2 h7 h14
  simp [Finset.filter_insert, Finset.filter_singleton] at h2 h7 h14
  omega

/-- The orbit counts of a symplectic action of order `15`: one orbit each with stabilizer of order
`3`, `5` and `15`. -/
theorem IsK3CyclicOrbitData.orbitCounts_fifteen {a : ℕ → ℕ} (h : IsK3CyclicOrbitData 15 a) :
    a 3 = 1 ∧ a 5 = 1 ∧ a 15 = 1 := by
  have h3 := h.cyclicFixedPointCount_eq (by norm_num) (by norm_num : 3 ∣ 15) (by norm_num) (k := 6)
    (by norm_num [mathieuFunction_eq_primeFactorsList])
  have h5 := h.cyclicFixedPointCount_eq (by norm_num) (by norm_num : 5 ∣ 15) (by norm_num) (k := 4)
    (by norm_num [mathieuFunction_eq_primeFactorsList])
  have h15 := h.cyclicFixedPointCount_eq (by norm_num) (dvd_refl 15) (by norm_num) (k := 1)
    (by norm_num [mathieuFunction_eq_primeFactorsList])
  simp only [cyclicFixedPointCount_def, Nat.divisors_ofNat] at h3 h5 h15
  simp [Finset.filter_insert, Finset.filter_singleton] at h3 h5 h15
  omega

/-- For the orders `11`, `14` and `15` the exceptional root lattices `2 A₁₀`, `A₁₃ ⊕ A₆ ⊕ A₁` and
`A₁₄ ⊕ A₄ ⊕ A₂` of the resolved quotient have rank `20`. -/
theorem IsK3CyclicOrbitData.cyclicRootRank_eq_twenty {n : ℕ} {a : ℕ → ℕ}
    (h : IsK3CyclicOrbitData n a) (hn : n = 11 ∨ n = 14 ∨ n = 15) : cyclicRootRank n a = 20 := by
  rcases hn with rfl | rfl | rfl
  · simp only [cyclicRootRank_def, Nat.divisors_ofNat]
    simp [h.orbitCounts_eleven]
  · obtain ⟨h2, h7, h14⟩ := h.orbitCounts_fourteen
    simp only [cyclicRootRank_def, Nat.divisors_ofNat]
    simp [h2, h7, h14]
  · obtain ⟨h3, h5, h15⟩ := h.orbitCounts_fifteen
    simp only [cyclicRootRank_def, Nat.divisors_ofNat]
    simp [h3, h5, h15]

/-- Under the rank bound `19` on the exceptional root lattice, as in characteristic zero, where the
Picard rank is at most `20`, the order of a symplectic cyclic action is at most `8`. -/
theorem IsK3CyclicOrbitData.le_eight {n : ℕ} {a : ℕ → ℕ} (h : IsK3CyclicOrbitData n a)
    (hn : n ≠ 0) (hrank : cyclicRootRank n a ≤ 19) : n ≤ 8 := by
  have hmem := h.mem_candidates hn (by omega)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h11 | h14 | h15
  any_goals norm_num
  all_goals
    have := h.cyclicRootRank_eq_twenty (by omega)
    omega

/-! ### Examples -/

/-- A symplectic involution: eight fixed points, `24 * (2 - 1) = 8 * 3`. -/
example : IsK3CyclicOrbitData 2 (fun m ↦ if m = 2 then 8 else 0) := by
  simp only [isK3CyclicOrbitData_iff, Nat.divisors_ofNat]
  decide

/-- Order `4`: four orbits with stabilizer of order `4` and two with stabilizer of order `2`;
`72 = 4 * 15 + 2 * 2 * 3`, and the square fixes `4 + 2 * 2 = 8` points. -/
example : IsK3CyclicOrbitData 4 (fun m ↦ if m = 4 then 4 else if m = 2 then 2 else 0) := by
  simp only [isK3CyclicOrbitData_iff, Nat.divisors_ofNat]
  decide

/-- Order `14` survives the orbit relations: `21 + 96 + 195 = 312 = 24 * 13`. -/
example : IsK3CyclicOrbitData 14 (fun m ↦ if m = 2 ∨ m = 7 ∨ m = 14 then 1 else 0) := by
  simp only [isK3CyclicOrbitData_iff, Nat.divisors_ofNat]
  decide

end TauCeti
