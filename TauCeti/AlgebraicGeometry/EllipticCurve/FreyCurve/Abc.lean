/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FreyCurve.Conductor
public import TauCeti.AlgebraicGeometry.EllipticCurve.Szpiro
public import TauCeti.NumberTheory.AbcConjecture
import Mathlib.RingTheory.Radical.NatInt
import TauCeti.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.Radical.Ideal

/-!
# Szpiro's conjecture implies the abc conjecture with exponent `3 / 2`

Let `a + b = c` be coprime integers. The Frey curve `y² = x (x - a) (x + b)` has discriminant
`16 (a b c)²`, and away from `2` its reduction is good or multiplicative, bad exactly at the primes
dividing `a b c`. So its minimal discriminant is about `(a b c)²` and its conductor about
`rad (a b c)`, and Szpiro's conjecture `|Δ_min| ≪_ε N ^ (6 + ε)` gives
`(a b c)² ≪_ε rad (a b c) ^ (6 + ε)`. As the largest of `|a|`, `|b|`, `|c|` is the sum of the other
two, its square is at most `2 |a b c|`, and this is the abc conjecture with exponent `3 / 2`:
`max (|a|, |b|, |c|) ≪_ε rad (a b c) ^ (3 / 2 + ε)`. The exponent `3 / 2` is the one this argument
gives; it is not claimed to be optimal.

Only the prime `2` needs care. Exactly one of `a`, `b`, `c` is even.

* If `16` divides it, the triple can be reordered and its signs changed so that the Frey curve is
  semistable, with minimal discriminant `(a b c)² / 2⁸` and algorithmic conductor dividing
  `rad (a b c)` (`TauCeti.isSemistable_freyCurve`, `TauCeti.minimalDiscriminantIdeal_freyCurve`).
* Otherwise the Frey equation is globally minimal, with minimal discriminant `16 (a b c)²`
  (`TauCeti.minimalDiscriminantIdeal_freyCurve_of_not_dvd`). Its reduction at `2` may be additive,
  but its algorithmic conductor still divides `2¹¹ rad (a b c)`
  (`TauCeti.algorithmicConductor_freyCurve_dvd`).

Either way some elliptic curve over `ℚ` has `(a b c)² ≤ 2⁸ |Δ_min|` and `N ≤ 2¹¹ rad (a b c)`,
which is all that Szpiro's conjecture needs.

The conjectures are stated against the algorithmic conductor of Tate's algorithm, as in
`TauCeti/AlgebraicGeometry/EllipticCurve/Szpiro.lean`, and neither is proved here.

## Main results

* `TauCeti.AlgorithmicSzpiroConjecture.exists_sq_le`: under Szpiro's conjecture,
  `(A B (A + B))² ≪_ε rad (A B (A + B)) ^ (6 + ε)` for all coprime `A` and `B` with
  `A B (A + B) ≠ 0`.
* `TauCeti.AlgorithmicSzpiroConjecture.abcConjectureWithExponent`: Szpiro's conjecture implies the
  abc conjecture with exponent `3 / 2`.

## References

* J. Oesterlé, *Nouvelles approches du « théorème » de Fermat*, Séminaire Bourbaki 694 (1988),
  Astérisque 161–162 (1988), 165–186.
* G. Frey, *Links between stable elliptic curves and certain Diophantine equations*, Ann. Univ.
  Sarav. Ser. Math. 1 (1986), 1–40.
-/

public section

namespace TauCeti

open WeierstrassCurve UniqueFactorizationMonoid

/-! ### Szpiro's conjecture for all Frey curves -/

/-- A coprime pair `A`, `B` with `16 ∣ A B (A + B)` can be replaced by a coprime pair `A'`, `B'`
with `A' ≡ -1 (mod 4)`, `16 ∣ B'` and `A' B' (A' + B') = A B (A + B)`. The new pair is the old one
reordered, with signs changed. -/
private theorem exists_pair_of_sixteen_dvd {A B : ℤ} (hAB : IsCoprime A B)
    (h16 : 16 ∣ A * B * (A + B)) :
    ∃ A' B' : ℤ, IsCoprime A' B' ∧ 4 ∣ A' + 1 ∧ 16 ∣ B' ∧
      A' * B' * (A' + B') = A * B * (A + B) := by
  -- for a coprime pair `X`, `Y` with `16 ∣ Y`, take `(X, Y)` or `(-(X + Y), Y)`
  have key {X Y : ℤ} (hXY : IsCoprime X Y) (hY : 16 ∣ Y) :
      ∃ A' B' : ℤ, IsCoprime A' B' ∧ 4 ∣ A' + 1 ∧ 16 ∣ B' ∧
        A' * B' * (A' + B') = X * Y * (X + Y) := by
    have hX : ¬ 2 ∣ X := fun h2 ↦ Int.prime_two.not_dvd_one
      (hXY.isUnit_of_dvd' h2 (dvd_trans ⟨8, by norm_num⟩ hY)).dvd
    by_cases h4 : 4 ∣ X + 1
    · exact ⟨X, Y, hXY, h4, hY, rfl⟩
    · exact ⟨-(X + Y), Y, by simpa using (hXY.add_mul_left_left 1).neg_left, by omega, hY,
        by ring⟩
  -- an odd integer is coprime to `16`
  have hodd {x : ℤ} (hx : ¬ 2 ∣ x) : IsCoprime (16 : ℤ) x := by
    obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
    exact (show IsCoprime (2 : ℤ) (2 * k + 1) from ⟨-k, 1, by ring⟩).pow_left (m := 4)
  have hnot : ¬ (2 ∣ A ∧ 2 ∣ B) := fun ⟨hA, hB⟩ ↦
    Int.prime_two.not_dvd_one (hAB.isUnit_of_dvd' hA hB).dvd
  by_cases hB : 2 ∣ B
  · -- `B` is even, so `16 ∣ B`
    have hA : ¬ 2 ∣ A := fun hA ↦ hnot ⟨hA, hB⟩
    have : 16 ∣ B := (hodd (x := A * (A + B)) (by
      rw [Int.prime_two.dvd_mul]; omega)).dvd_of_dvd_mul_left (by convert h16 using 1; ring)
    exact key hAB this
  by_cases hA : 2 ∣ A
  · -- `A` is even, so `16 ∣ A`
    have : 16 ∣ A := (hodd (x := B * (A + B)) (by
      rw [Int.prime_two.dvd_mul]; omega)).dvd_of_dvd_mul_left (by convert h16 using 1; ring)
    obtain ⟨A', B', h₁, h₂, h₃, h₄⟩ := key hAB.symm this
    exact ⟨A', B', h₁, h₂, h₃, by rw [h₄]; ring⟩
  · -- `A` and `B` are odd, so `16 ∣ A + B`
    have : 16 ∣ -(A + B) := dvd_neg.2 ((hodd (x := A * B) (by
      rw [Int.prime_two.dvd_mul]; omega)).dvd_of_dvd_mul_left h16)
    have hcop : IsCoprime A (-(A + B)) := by
      have := (hAB.add_mul_left_right 1).neg_right
      rwa [mul_one, add_comm] at this
    obtain ⟨A', B', h₁, h₂, h₃, h₄⟩ := key hcop this
    exact ⟨A', B', h₁, h₂, h₃, by rw [h₄]; ring⟩

/-- The Frey curve of a coprime pair with `16 ∣ B` and `A ≡ -1 (mod 4)` has
`|Δ_min| = (A B (A + B))² / 2⁸` and algorithmic conductor dividing `rad (A B (A + B))`. -/
private theorem natAbs_sq_eq_and_absNorm_algorithmicConductor_le {A B : ℤ}
    (hAB : IsCoprime A B) (hA : 4 ∣ A + 1) (hB : 16 ∣ B) (hP : A * B * (A + B) ≠ 0)
    [((freyCurve A B).baseChange ℚ).IsElliptic] :
    (A * B * (A + B)).natAbs ^ 2 =
        2 ^ 8 * Ideal.absNorm (minimalDiscriminantIdeal ℤ ((freyCurve A B).baseChange ℚ)) ∧
      Ideal.absNorm (algorithmicConductor ℤ ((freyCurve A B).baseChange ℚ)) ≤
        radical (A * B * (A + B)).natAbs := by
  obtain ⟨d, hd⟩ : (2 : ℤ) ^ 8 ∣ (A * B * (A + B)) ^ 2 := by
    rw [show (2 : ℤ) ^ 8 = 16 ^ 2 by norm_num]
    exact pow_dvd_pow_of_dvd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hB A) _) 2
  have hD := minimalDiscriminantIdeal_freyCurve (F := ℚ) hA hB hAB (d := d) (by rw [← hd]; ring)
  refine ⟨?_, ?_⟩
  · rw [hD, Int.absNorm_span_singleton, ← Int.natAbs_pow, hd, Int.natAbs_mul]
    norm_num
  -- `(d) ∣ (A B (A + B))²`, so the conductor `rad (d)` divides `rad (A B (A + B))`
  have hd₂ : Ideal.span {d} ∣ Ideal.span {A * B * (A + B)} ^ 2 := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_dvd_span_singleton_iff_dvd]
    exact ⟨2 ^ 8, by rw [hd]; ring⟩
  have hN : algorithmicConductor ℤ ((freyCurve A B).baseChange ℚ) ∣
      Ideal.span {radical (A * B * (A + B))} := by
    rw [(isSemistable_iff_algorithmicConductor_eq_radical _).1
      (isSemistable_freyCurve (F := ℚ) hA hB hAB), hD, ← radical_span_singleton]
    exact (radical_dvd_radical hd₂ (pow_ne_zero 2 (by simpa using hP))).trans
      (radical_pow _ two_ne_zero).dvd
  have := Int.absNorm_le_natAbs_of_dvd_span_singleton radical_ne_zero hN
  rwa [← Int.radical_natAbs_eq_radical, Int.natAbs_natCast] at this

/-- **Some Frey curve of a coprime triple has small conductor against its discriminant.** For
coprime integers `A` and `B` with `A B (A + B) ≠ 0` there is an elliptic curve `E` over `ℚ`, the
Frey curve of `A`, `B` and `-(A + B)` in a suitable order and with suitable signs, with
`(A B (A + B))² ≤ 2⁸ |Δ_min|` and algorithmic conductor of norm at most `2¹¹ rad (A B (A + B))`.
If `16 ∣ A B (A + B)` the curve can be chosen semistable; otherwise the Frey equation of `A` and
`B` is globally minimal (`TauCeti.minimalDiscriminantIdeal_freyCurve_of_not_dvd`,
`TauCeti.algorithmicConductor_freyCurve_dvd`). -/
theorem exists_natAbs_sq_le_absNorm_minimalDiscriminantIdeal {A B : ℤ} (hAB : IsCoprime A B)
    (hP : A * B * (A + B) ≠ 0) :
    ∃ (E : WeierstrassCurve ℚ) (_ : E.IsElliptic),
      (A * B * (A + B)).natAbs ^ 2 ≤ 2 ^ 8 * Ideal.absNorm (minimalDiscriminantIdeal ℤ E) ∧
        Ideal.absNorm (algorithmicConductor ℤ E) ≤ 2 ^ 11 * radical (A * B * (A + B)).natAbs := by
  by_cases h16 : 16 ∣ A * B * (A + B)
  · -- the semistable case: `|Δ_min| = (A B (A + B))² / 2⁸` and `N ∣ rad (A B (A + B))`
    obtain ⟨A', B', hAB', hA', hB', hprod⟩ := exists_pair_of_sixteen_dvd hAB h16
    have := isElliptic_baseChange_freyCurve (A := A') (B := B') (hprod ▸ hP)
    obtain ⟨hD, hN⟩ := natAbs_sq_eq_and_absNorm_algorithmicConductor_le hAB' hA' hB' (hprod ▸ hP)
    rw [hprod] at hD hN
    exact ⟨_, this, hD.le, hN.trans (Nat.le_mul_of_pos_left _ (by norm_num))⟩
  · -- the minimal case: `|Δ_min| = 16 (A B (A + B))²` and `N ∣ 2¹¹ rad (A B (A + B))`
    have := isElliptic_baseChange_freyCurve hP
    refine ⟨_, this, ?_, ?_⟩
    · rw [minimalDiscriminantIdeal_freyCurve_of_not_dvd hAB h16, Int.absNorm_span_singleton]
      generalize A * B * (A + B) = P
      rw [Int.natAbs_mul, Int.natAbs_pow]
      calc P.natAbs ^ 2 ≤ 2 ^ 8 * 16 * P.natAbs ^ 2 := Nat.le_mul_of_pos_left _ (by norm_num)
        _ = _ := by norm_num; ring
    · have := Int.absNorm_le_natAbs_of_dvd_span_singleton (by simp)
        (algorithmicConductor_freyCurve_dvd hAB h16)
      rwa [Int.natAbs_mul, ← Int.radical_natAbs_eq_radical, Int.natAbs_natCast] at this

/-- **Szpiro's conjecture for Frey curves.** Under `TauCeti.AlgorithmicSzpiroConjecture`, for every
`ε > 0` there is a constant `C` such that `(A B (A + B))² ≤ C rad (A B (A + B)) ^ (6 + ε)` for all
coprime integers `A` and `B` with `A B (A + B) ≠ 0`. This applies Szpiro's conjecture to the curve
of `TauCeti.exists_natAbs_sq_le_absNorm_minimalDiscriminantIdeal`. -/
theorem AlgorithmicSzpiroConjecture.exists_sq_le (h : AlgorithmicSzpiroConjecture) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, ∀ A B : ℤ, IsCoprime A B → A * B * (A + B) ≠ 0 →
      ((A * B * (A + B) : ℤ) : ℝ) ^ 2 ≤
        C * ((radical (A * B * (A + B)).natAbs : ℕ) : ℝ) ^ (6 + ε) := by
  obtain ⟨C, hC⟩ := algorithmicSzpiroConjecture_iff.1 h ε hε
  refine ⟨2 ^ 8 * max C 0 * (2 ^ 11 : ℝ) ^ (6 + ε), fun A B hAB hP ↦ ?_⟩
  obtain ⟨E, _, hD, hN⟩ := exists_natAbs_sq_le_absNorm_minimalDiscriminantIdeal hAB hP
  have h6 : 0 ≤ 6 + ε := by linarith
  have hD' : ((A * B * (A + B) : ℤ) : ℝ) ^ 2 ≤
      2 ^ 8 * (Ideal.absNorm (minimalDiscriminantIdeal ℤ E) : ℝ) := by
    rw [← sq_abs, ← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast hD
  have hN' : (Ideal.absNorm (algorithmicConductor ℤ E) : ℝ) ≤
      2 ^ 11 * ((radical (A * B * (A + B)).natAbs : ℕ) : ℝ) := by
    exact_mod_cast hN
  calc ((A * B * (A + B) : ℤ) : ℝ) ^ 2
      ≤ 2 ^ 8 * (max C 0 * (Ideal.absNorm (algorithmicConductor ℤ E) : ℝ) ^ (6 + ε)) :=
        hD'.trans (by gcongr; exact (hC E).trans (by gcongr; exact le_max_left C 0))
    _ ≤ 2 ^ 8 * (max C 0 * (2 ^ 11 * ((radical (A * B * (A + B)).natAbs : ℕ) : ℝ)) ^ (6 + ε)) := by
        gcongr
    _ = 2 ^ 8 * max C 0 * (2 ^ 11 : ℝ) ^ (6 + ε) *
        ((radical (A * B * (A + B)).natAbs : ℕ) : ℝ) ^ (6 + ε) := by
        rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)]
        ring

/-- **Szpiro's conjecture implies the abc conjecture with exponent `3 / 2`**: under
`TauCeti.AlgorithmicSzpiroConjecture`, for every `ε > 0` there is a constant `C` with
`max (|a|, |b|, |c|) ≤ C rad (a b c) ^ (3 / 2 + ε)` for all coprime `a + b = c`. For coprime
positive integers `a + b = c`, Szpiro's bound for Frey curves gives
`(a b c)² ≪_ε rad (a b c) ^ (6 + 4 ε)` (`TauCeti.AlgorithmicSzpiroConjecture.exists_sq_le`), and
`c² ≤ 2 a b c` because `a + b ≤ 2 a b`. -/
theorem AlgorithmicSzpiroConjecture.abcConjectureWithExponent (h : AlgorithmicSzpiroConjecture) :
    AbcConjectureWithExponent (3 / 2) := by
  refine (abcConjectureWithExponent_iff_nat _ (by norm_num)).2 fun ε hε ↦ ?_
  obtain ⟨K, hK⟩ := h.exists_sq_le (ε := 4 * ε) (by positivity)
  set C : ℝ := (4 * max K 0) ^ (1 / 4 : ℝ)
  refine ⟨C, fun a b c ha hb hab habc ↦ ?_⟩
  set R : ℝ := ((radical (a * b * c) : ℕ) : ℝ)
  have hR : 0 ≤ R := Nat.cast_nonneg _
  -- Szpiro's bound for the Frey curve of `a` and `b`: `(a b c)² ≤ K R ^ (6 + 4 ε)`
  have hK' : (((a * b * c : ℕ) : ℤ) : ℝ) ^ 2 ≤ K * R ^ (6 + 4 * ε) := by
    have := hK a b (Nat.Coprime.isCoprime hab) (by positivity)
    rwa [← Nat.cast_add, habc, ← Nat.cast_mul, ← Nat.cast_mul, Int.natAbs_natCast] at this
  -- `c² ≤ 2 a b c`, since `c = a + b ≤ 2 a b`
  have hc : (c : ℝ) ^ 2 ≤ 2 * (((a * b * c : ℕ) : ℤ) : ℝ) := by
    have : c ^ 2 ≤ 2 * (a * b * c) := by
      calc c ^ 2 = c * (a + b) := by rw [habc, sq]
        _ ≤ c * (2 * a * b) := Nat.mul_le_mul_left c (by nlinarith)
        _ = 2 * (a * b * c) := by ring
    exact_mod_cast this
  -- so `c⁴ ≤ 4 (a b c)² ≤ 4 K R ^ (6 + 4 ε) ≤ (C R ^ (3 / 2 + ε))⁴`
  have hC4 : C ^ 4 = 4 * max K 0 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hR4 : (R ^ (3 / 2 + ε)) ^ 4 = R ^ (6 + 4 * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR]
    congr 1
    push_cast
    ring
  refine (pow_le_pow_iff_left₀ (Nat.cast_nonneg c) (by positivity) (by norm_num : 4 ≠ 0)).1 ?_
  rw [mul_pow, hC4, hR4]
  calc (c : ℝ) ^ 4 = ((c : ℝ) ^ 2) ^ 2 := by ring
    _ ≤ (2 * (((a * b * c : ℕ) : ℤ) : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hc 2
    _ = 4 * (((a * b * c : ℕ) : ℤ) : ℝ) ^ 2 := by ring
    _ ≤ 4 * (K * R ^ (6 + 4 * ε)) := by gcongr
    _ ≤ 4 * max K 0 * R ^ (6 + 4 * ε) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (by gcongr; exact le_max_left K 0)
        (Real.rpow_nonneg hR _)

end TauCeti

end
