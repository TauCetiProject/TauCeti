/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Cyclotomic.GaussSum
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# A multiquadratic field lies in a cyclotomic field

This file proves the explicit Kronecker–Weber theorem for multiquadratic fields: the field
generated over `ℚ` by square roots of rational numbers `d₁, …, dₙ` is contained in a cyclotomic
field. Concretely, inside any field `L` of characteristic zero holding a primitive `N`-th root of
unity `ζ` with `0 < N`, every square root of an integer `m` with `4 |m| ∣ N` already lies in
`ℚ(ζ)`.

The engine is the prime case: a square root of a prime `p` is assembled from a root of unity of
order `4p`. For odd `p` the quadratic Gauss sum supplies a square root of the prime discriminant
`p* = ±p` (`exists_mem_sq_eq_oddPrimeDiscriminant`), and the fourth root of unity corrects its sign
when `p ≡ 3 (mod 4)`; for `p = 2` the eighth root of unity supplies `√2` directly
(`exists_mem_sq_eq_two`). Multiplying square roots along a prime factorization reaches every
positive integer, the fourth root of unity reaches the negative ones, and clearing denominators
reaches every rational number. Since the two square roots of an element differ by a sign, *every*
square root of such an `m` lies in the field, not just the constructed one. A zero radicand is
excluded automatically: `4 · 0 ∣ N` forces `N = 0`.

Taking `L = ℂ` makes the statement unconditional: with `N = 4 ∏ᵢ |num dᵢ · den dᵢ|` one may use
`ζ = exp (2 π i / N)`, so `ℚ(√d₁, …, √dₙ) ⊆ ℚ(ζ_N)` for any choice of square roots. The target
`ℚ(ζ_N)` is the `N`-th cyclotomic field: `IsPrimitiveRoot.adjoin_isCyclotomicExtension` identifies
it as a cyclotomic extension of `ℚ`.

This is the multiquadratic case of the Kronecker–Weber theorem, which it makes explicit: the
cyclotomic field is named, not merely asserted to exist. The general theorem, for every abelian
extension of `ℚ`, is not proved here. For the classical account see K. Ireland and M. Rosen, *A
Classical Introduction to Modern Number Theory*, Chapter 6.

## Main results

* `TauCeti.Multiquadratic.mem_of_sq_eq_intCast`: every square root of an integer `m` lies in an
  intermediate field holding a primitive `N`-th root of unity, provided `0 < N` and `4 |m| ∣ N`.
* `TauCeti.Multiquadratic.mem_of_sq_eq_ratCast`: the same for a rational number.
* `TauCeti.Multiquadratic.adjoin_range_le_of_sq_eq_ratCast`: a multiquadratic field with rational
  radicands is contained in any such intermediate field.
* `TauCeti.Multiquadratic.adjoin_range_le_adjoin_exp`: over `ℂ`, `ℚ(√d₁, …, √dₙ) ⊆ ℚ(ζ_N)` for the
  root of unity `ζ_N = exp (2 π i / N)` and the order `N = 4 ∏ᵢ |num dᵢ · den dᵢ|`.
* `TauCeti.Multiquadratic.exists_isCyclotomicExtension_adjoin_range_le`: every multiquadratic field
  with rational radicands lies in a cyclotomic field.
-/

public section

open IntermediateField

namespace TauCeti.Multiquadratic

variable {L : Type*} [Field L] [CharZero L] {F : IntermediateField ℚ L} {ζ : L} {N : ℕ}

/-- **A root of unity of order `4p` carries a square root of the prime `p`.** For an odd prime the
Gauss sum gives a square root of `p* = ±p`, and a primitive fourth root of unity repairs the sign;
for `p = 2` a primitive eighth root of unity gives `√2`. -/
theorem exists_mem_sq_eq_prime (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) (hmem : ζ ∈ F) {p : ℕ}
    (hp : p.Prime) (hdvd : 4 * p ∣ N) :
    ∃ x ∈ F, x ^ 2 = (p : L) := by
  rcases eq_or_ne p 2 with rfl | hp2
  · have h8 : 8 ∣ N := by norm_num at hdvd; exact hdvd
    obtain ⟨x, hxF, hx⟩ := exists_mem_sq_eq_two (hζ.pow hN (Nat.div_mul_cancel h8).symm)
      (pow_mem hmem _)
    exact ⟨x, hxF, by rw [hx]; norm_num⟩
  · have hpN : p ∣ N := (dvd_mul_left p 4).trans hdvd
    have h4N : 4 ∣ N := (dvd_mul_right 4 p).trans hdvd
    obtain ⟨w, hwF, hw⟩ := exists_mem_sq_eq_oddPrimeDiscriminant hp hp2
      (hζ.pow hN (Nat.div_mul_cancel hpN).symm) (pow_mem hmem _)
    by_cases hp4 : p % 4 = 1
    · rw [oddPrimeDiscriminant_of_mod_four_eq_one hp4] at hw
      exact ⟨w, hwF, by rw [hw]; push_cast; ring⟩
    · rw [oddPrimeDiscriminant_of_mod_four_ne_one hp4] at hw
      obtain ⟨i, hiF, hi⟩ := exists_mem_sq_eq_neg_one (hζ.pow hN (Nat.div_mul_cancel h4N).symm)
        (pow_mem hmem _)
      refine ⟨i * w, mul_mem hiF hwF, ?_⟩
      rw [mul_pow, hi, hw]
      push_cast
      ring

/-- **A root of unity of order divisible by `4n` carries a square root of `n`.** The square roots
of the prime factors of `n` multiply together. -/
theorem exists_mem_sq_eq_natCast (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) (hmem : ζ ∈ F) {n : ℕ}
    (hdvd : 4 * n ∣ N) :
    ∃ x ∈ F, x ^ 2 = (n : L) := by
  induction n using induction_on_primes with
  | zero => simp only [Nat.mul_zero, zero_dvd_iff] at hdvd; omega
  | one => exact ⟨1, one_mem F, by norm_num⟩
  | prime_mul p n hp ih =>
    obtain ⟨y, hyF, hy⟩ := ih ((mul_dvd_mul_left 4 ⟨p, mul_comm p n⟩).trans hdvd)
    obtain ⟨z, hzF, hz⟩ := exists_mem_sq_eq_prime hN hζ hmem hp
      ((mul_dvd_mul_left 4 (Dvd.intro n rfl)).trans hdvd)
    refine ⟨y * z, mul_mem hyF hzF, ?_⟩
    rw [mul_pow, hy, hz]
    push_cast
    ring

/-- **A root of unity of order divisible by `4 |m| ` carries a square root of the integer `m`.**
A primitive fourth root of unity turns the square root of `|m|` into one of `m`. -/
theorem exists_mem_sq_eq_intCast (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) (hmem : ζ ∈ F) {m : ℤ}
    (hdvd : 4 * m.natAbs ∣ N) :
    ∃ x ∈ F, x ^ 2 = (m : L) := by
  obtain ⟨x, hxF, hx⟩ := exists_mem_sq_eq_natCast hN hζ hmem hdvd
  rcases m.natAbs_eq with hm' | hm'
  · have hcast : ((m : L)) = ((m.natAbs : ℕ) : L) := by rw [hm']; simp
    exact ⟨x, hxF, by rw [hx, hcast]⟩
  · have h4N : 4 ∣ N := (dvd_mul_right 4 m.natAbs).trans hdvd
    obtain ⟨i, hiF, hi⟩ := exists_mem_sq_eq_neg_one (hζ.pow hN (Nat.div_mul_cancel h4N).symm)
      (pow_mem hmem _)
    have hcast : ((m : L)) = -((m.natAbs : ℕ) : L) := by
      rw [hm']
      simp
    refine ⟨i * x, mul_mem hiF hxF, ?_⟩
    rw [mul_pow, hi, hx, hcast]
    ring

/-- **Every square root of an integer lies in a field of roots of unity of matching order.** If the
intermediate field `F` contains a primitive `N`-th root of unity of positive order `N` and
`4 |m| ∣ N`, then both square roots of the integer `m` lie in `F`: the constructed one does, and
the two differ by a sign. -/
theorem mem_of_sq_eq_intCast (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) (hmem : ζ ∈ F) {m : ℤ}
    (hdvd : 4 * m.natAbs ∣ N) {x : L} (hx : x ^ 2 = (m : L)) : x ∈ F := by
  obtain ⟨y, hyF, hy⟩ := exists_mem_sq_eq_intCast hN hζ hmem hdvd
  rcases eq_or_eq_neg_of_sq_eq_sq x y (hx.trans hy.symm) with h | h
  · exact h ▸ hyF
  · exact h ▸ neg_mem hyF

/-- **Every square root of a rational number lies in a field of roots of unity of matching
order.** Clearing the denominator of `q` turns it into the integer `q.num * q.den`, whose square
class it shares. -/
theorem mem_of_sq_eq_ratCast (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) (hmem : ζ ∈ F) {q : ℚ}
    (hdvd : 4 * (q.num * q.den).natAbs ∣ N) {x : L} (hx : x ^ 2 = (q : L)) : x ∈ F := by
  have hden : ((q.den : L)) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have hq' : (q : L) * q.den = ((q.num : ℤ) : L) := by
    exact_mod_cast congrArg (fun t : ℚ => (t : L)) q.mul_den_eq_num
  have hxd : (x * q.den) ^ 2 = ((q.num * q.den : ℤ) : L) :=
    calc (x * q.den) ^ 2 = x ^ 2 * q.den * q.den := by ring
      _ = (q : L) * q.den * q.den := by rw [hx]
      _ = ((q.num : ℤ) : L) * q.den := by rw [hq']
      _ = ((q.num * q.den : ℤ) : L) := by push_cast; ring
  have hmemxd : x * q.den ∈ F := mem_of_sq_eq_intCast hN hζ hmem hdvd hxd
  have hxeq : x = (x * q.den) / (q.den : L) := by field_simp
  rw [hxeq]
  exact div_mem hmemxd (IntermediateField.natCast_mem F _)

/-- **A multiquadratic field lies in any field of roots of unity of matching order.** If the
intermediate field `F` of `L / ℚ` contains a primitive `N`-th root of unity of positive order `N`
and, for each radicand `d i`, the order `N` is divisible by `4 |num (d i) · den (d i)|`, then every
field generated over `ℚ` by square roots `r i` of the `d i` is contained in `F`. -/
theorem adjoin_range_le_of_sq_eq_ratCast {ι : Type*} (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N)
    (hmem : ζ ∈ F) {d : ι → ℚ} {r : ι → L} (hr : ∀ i, r i ^ 2 = (d i : L))
    (hdvd : ∀ i, 4 * ((d i).num * (d i).den).natAbs ∣ N) :
    adjoin ℚ (Set.range r) ≤ F := by
  rw [adjoin_le_iff]
  rintro x ⟨i, rfl⟩
  exact mem_of_sq_eq_ratCast hN hζ hmem (hdvd i) (hr i)

/-- **A multiquadratic field with integer radicands lies in any field of roots of unity of matching
order.** The integer analogue of `adjoin_range_le_of_sq_eq_ratCast`: the divisibility condition
reads `4 |d i| ∣ N`. -/
theorem adjoin_range_le_of_sq_eq_intCast {ι : Type*} (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N)
    (hmem : ζ ∈ F) {d : ι → ℤ} {r : ι → L} (hr : ∀ i, r i ^ 2 = (d i : L))
    (hdvd : ∀ i, 4 * (d i).natAbs ∣ N) :
    adjoin ℚ (Set.range r) ≤ F := by
  rw [adjoin_le_iff]
  rintro x ⟨i, rfl⟩
  exact mem_of_sq_eq_intCast hN hζ hmem (hdvd i) (hr i)

/-- **A multiquadratic field with integer radicands lies in the cyclotomic field `ℚ(ζ_N)`.** The
`F = ℚ(ζ)` case of `adjoin_range_le_of_sq_eq_intCast`. -/
theorem adjoin_range_le_adjoin_of_sq_eq_intCast {ι : Type*} (hN : 0 < N)
    (hζ : IsPrimitiveRoot ζ N) {d : ι → ℤ} {r : ι → L} (hr : ∀ i, r i ^ 2 = (d i : L))
    (hdvd : ∀ i, 4 * (d i).natAbs ∣ N) :
    adjoin ℚ (Set.range r) ≤ adjoin ℚ {ζ} :=
  adjoin_range_le_of_sq_eq_intCast hN hζ (mem_adjoin_simple_self ℚ ζ) hr hdvd

/-! ### Over `ℂ` no root of unity need be assumed -/

/-- **A multiquadratic field lies in the explicitly named cyclotomic field.** For a finite family
of nonzero rational radicands `d i` and any choice of complex square roots `r i`, the field
`ℚ(√d₁, …, √dₙ)` is contained in `ℚ(exp (2 π i / N))` for `N = 4 ∏ᵢ |num (dᵢ) · den (dᵢ)|`. -/
theorem adjoin_range_le_adjoin_exp {ι : Type*} [Fintype ι] {d : ι → ℚ} {r : ι → ℂ}
    (hd : ∀ i, d i ≠ 0) (hr : ∀ i, r i ^ 2 = (d i : ℂ)) :
    adjoin ℚ (Set.range r) ≤ adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I /
      ((4 * ∏ i, ((d i).num * (d i).den).natAbs : ℕ) : ℂ))} := by
  have hprod : 0 < ∏ i, ((d i).num * (d i).den).natAbs :=
    Finset.prod_pos fun i _ => Int.natAbs_pos.mpr
      (mul_ne_zero (Rat.num_ne_zero.mpr (hd i)) (by exact_mod_cast (d i).den_nz))
  have hpos : 0 < 4 * ∏ i, ((d i).num * (d i).den).natAbs := by omega
  exact adjoin_range_le_of_sq_eq_ratCast hpos (Complex.isPrimitiveRoot_exp _ hpos.ne')
    (mem_adjoin_simple_self ℚ _) hr
    fun i => Nat.mul_dvd_mul_left 4 (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))

/-- **Every multiquadratic field lies in a cyclotomic field.** For a finite family of rational
radicands `d i` and any choice of complex square roots `r i`, the field `ℚ(√d₁, …, √dₙ)` is
contained in a cyclotomic extension of `ℚ`. The order and the field are named explicitly in
`adjoin_range_le_adjoin_exp`, from which this existential form is deduced after discarding the
zero radicands, whose square roots are `0`.

This is the explicit Kronecker–Weber theorem for multiquadratic fields. -/
theorem exists_isCyclotomicExtension_adjoin_range_le {ι : Type*} [Finite ι] {d : ι → ℚ}
    {r : ι → ℂ} (hr : ∀ i, r i ^ 2 = (d i : ℂ)) :
    ∃ N : ℕ, 0 < N ∧ ∃ G : IntermediateField ℚ ℂ,
      IsCyclotomicExtension {N} ℚ G ∧ adjoin ℚ (Set.range r) ≤ G := by
  classical
  obtain ⟨N, hpos, hle⟩ : ∃ N : ℕ, 0 < N ∧ adjoin ℚ (Set.range r) ≤
      adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))} := by
    have : Fintype {i : ι // d i ≠ 0} := Fintype.ofFinite _
    have hprod : 0 < ∏ i : {i : ι // d i ≠ 0}, ((d i.1).num * (d i.1).den).natAbs :=
      Finset.prod_pos fun i _ => Int.natAbs_pos.mpr
        (mul_ne_zero (Rat.num_ne_zero.mpr i.2) (by exact_mod_cast (d i.1).den_nz))
    refine ⟨_, ?_, le_trans ?_
      (adjoin_range_le_adjoin_exp (fun i : {i : ι // d i ≠ 0} => i.2) fun i => hr i.1)⟩
    · omega
    · rw [adjoin_le_iff]
      rintro x ⟨i, rfl⟩
      by_cases hi : d i = 0
      · have hr0 : r i = 0 := by
          have h := hr i
          rw [hi, Rat.cast_zero] at h
          exact sq_eq_zero_iff.mp h
        exact hr0 ▸ zero_mem _
      · exact subset_adjoin ℚ _ ⟨⟨i, hi⟩, rfl⟩
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))) N :=
    Complex.isPrimitiveRoot_exp N hpos.ne'
  have : NeZero N := ⟨hpos.ne'⟩
  exact ⟨N, hpos, _, (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
    (F := adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))}) (hζ := hζ)).mpr rfl, hle⟩

/-- **Worked example: `ℚ(√2, √3) ⊆ ℚ(ζ₂₄)`.** A biquadratic field lies in the `24`-th cyclotomic
field, for either choice of the two square roots. The order `24` is what the construction uses:
`√2` is built from an eighth root of unity and `√3` from a twelfth. -/
theorem adjoin_pair_le_adjoin_of_sq_eq_two_of_sq_eq_three {ζ x y : ℂ} (hζ : IsPrimitiveRoot ζ 24)
    (hx : x ^ 2 = 2) (hy : y ^ 2 = 3) :
    adjoin ℚ {x, y} ≤ adjoin ℚ {ζ} := by
  have hmem : ∀ {m : ℤ} {z : ℂ}, 4 * m.natAbs ∣ 24 → z ^ 2 = (m : ℂ) →
      z ∈ adjoin ℚ {ζ} := fun hdvd hz =>
    mem_of_sq_eq_intCast (by norm_num) hζ (mem_adjoin_simple_self ℚ ζ) hdvd hz
  rw [adjoin_le_iff]
  rintro z (rfl | rfl)
  · exact hmem (m := 2) (by norm_num) (by rw [hx]; norm_num)
  · exact hmem (m := 3) (by norm_num) (by rw [hy]; norm_num)

end TauCeti.Multiquadratic
