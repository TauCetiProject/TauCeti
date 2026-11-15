/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Data.Nat.DvdSequence
public import Mathlib.RingTheory.Ideal.Operations
public import TauCeti.NumberTheory.LucasSequence.Basic
import TauCeti.Algebra.GCDMonoid.Basic
import TauCeti.RingTheory.Ideal.Operations

/-!
# Divisibility, coprimality, and strong divisibility of Lucas sequences

Every Lucas sequence of the first kind `lucasU P Q` over a commutative ring `R` is a divisibility
sequence (`TauCeti.isDvdSequence_lucasU`), with no coprimality or nonvanishing hypothesis on `P`
and `Q`: if `m ∣ n`, then `lucasU P Q m ∣ lucasU P Q n` via the explicit quotient
`lucasU (lucasV P Q m) (Q ^ m) (n / m)` from `TauCeti.lucasU_mul`.

When `IsCoprime P Q`, consecutive terms `lucasU P Q (n + 1)` and `lucasU P Q n` are coprime and
`lucasU P Q (n + 1)` is coprime to `Q` (`TauCeti.isCoprime_lucasU_succ_lucasU`,
`TauCeti.isCoprime_lucasU_succ_left`); conversely, either family of coprimality assertions
forces `IsCoprime P Q`. Combining those coprimality laws with the addition formula
`TauCeti.lucasU_add_add_one` runs the Euclidean algorithm on ideal spans, proving the ring-level
strong divisibility law
`Ideal.span {lucasU P Q m, lucasU P Q n} = Ideal.span {lucasU P Q (m.gcd n)}`
(`TauCeti.span_pair_lucasU`) in every commutative ring.

In any commutative ring with a `NormalizedGCDMonoid` structure, running the corresponding GCD
reduction under the weaker hypothesis `IsRelPrime P Q` gives
`GCDMonoid.gcd (lucasU P Q m) (lucasU P Q n) = normalize (lucasU P Q (m.gcd n))`
(`TauCeti.gcd_lucasU_eq_normalize`), and over `ℤ` gives the headline theorem
`Int.gcd (lucasU P Q m) (lucasU P Q n) = (lucasU P Q (Nat.gcd m n)).natAbs`
(`TauCeti.gcd_lucasU`), together with the sharp characterization
`Nat.IsStrongDvdSequence (fun n ↦ (lucasU P Q n).natAbs) ↔ IsCoprime P Q`
(`TauCeti.isStrongDvdSequence_natAbs_lucasU_iff`).

## Main results

* `TauCeti.lucasU_dvd_of_dvd`, `TauCeti.isDvdSequence_lucasU`: `lucasU P Q` is a divisibility
  sequence over every commutative ring.
* `TauCeti.isCoprime_lucasU_succ_left`, `TauCeti.forall_isCoprime_lucasU_succ_left_iff`:
  `lucasU P Q (n + 1)` is coprime to `Q` for all `n` if and only if `IsCoprime P Q`.
* `TauCeti.isCoprime_lucasU_succ_lucasU`, `TauCeti.forall_isCoprime_lucasU_succ_lucasU_iff`:
  consecutive terms of `lucasU P Q` are coprime for all `n` if and only if `IsCoprime P Q`.
* `TauCeti.span_pair_lucasU`: for coprime `P` and `Q` in any commutative ring,
  `Ideal.span {lucasU P Q m, lucasU P Q n} = Ideal.span {lucasU P Q (m.gcd n)}`.
* `TauCeti.isCoprime_lucasU_of_coprime`: if `IsCoprime P Q` and `m.Coprime n`, then
  `IsCoprime (lucasU P Q m) (lucasU P Q n)`.
* `TauCeti.gcd_lucasU_eq_normalize`: for relatively prime `P` and `Q` in any commutative
  `NormalizedGCDMonoid`,
  `GCDMonoid.gcd (lucasU P Q m) (lucasU P Q n) = normalize (lucasU P Q (m.gcd n))`.
* `TauCeti.gcd_lucasU`: for coprime `P Q : ℤ`,
  `Int.gcd (lucasU P Q m) (lucasU P Q n) = (lucasU P Q (Nat.gcd m n)).natAbs`.
* `TauCeti.isStrongDvdSequence_natAbs_lucasU_iff`: `n ↦ (lucasU P Q n).natAbs` is a strong
  divisibility sequence if and only if `IsCoprime P Q`.

## References

* R. D. Carmichael, *On the numerical factors of the arithmetic forms αⁿ ± βⁿ*, Annals of
  Mathematics (2) **15** (1913), 30–48, Section 2, Theorems I, IV, and VI.
* P. Bala, *Divisibility sequences from strong divisibility sequences*, OEIS A238600 note (2014),
  Section 2, Proposition 2.2, and Appendix, Propositions A2 and A3.
-/

public section

namespace TauCeti

section CommRing

variable {R : Type*} [CommRing R]

/-! ### Divisibility sequence property -/

/-- `lucasU P Q m` divides `lucasU P Q (m * n)` in every commutative ring, with no hypothesis on
`P` or `Q`. -/
theorem lucasU_dvd_lucasU_mul (P Q : R) (m n : ℕ) :
    lucasU P Q m ∣ lucasU P Q (m * n) :=
  ⟨lucasU (lucasV P Q m) (Q ^ m) n, lucasU_mul P Q m n⟩

/-- If `m ∣ n`, then `lucasU P Q m ∣ lucasU P Q n` in every commutative ring. -/
theorem lucasU_dvd_of_dvd (P Q : R) {m n : ℕ} (h : m ∣ n) :
    lucasU P Q m ∣ lucasU P Q n := by
  obtain ⟨k, rfl⟩ := h
  exact lucasU_dvd_lucasU_mul P Q m k

/-- **Every Lucas sequence of the first kind is a divisibility sequence.** -/
theorem isDvdSequence_lucasU (P Q : R) : IsDvdSequence (lucasU P Q) :=
  fun _ _ h ↦ lucasU_dvd_of_dvd P Q h

/-! ### Coprimality of terms and parameters -/

/-- If `IsCoprime P Q`, then `lucasU P Q (n + 1)` is coprime to `Q` for every `n`. -/
theorem isCoprime_lucasU_succ_left {P Q : R} (h : IsCoprime P Q) (n : ℕ) :
    IsCoprime (lucasU P Q (n + 1)) Q := by
  induction n with
  | zero => simp [isCoprime_one_left]
  | succ n ih =>
    rw [lucasU_add_two, IsCoprime.sub_mul_left_left_iff]
    exact h.mul_left ih

/-- Every positive-index term `lucasU P Q (n + 1)` is coprime to `Q` if and only if
`IsCoprime P Q`. -/
theorem forall_isCoprime_lucasU_succ_left_iff {P Q : R} :
    (∀ n, IsCoprime (lucasU P Q (n + 1)) Q) ↔ IsCoprime P Q :=
  ⟨fun h ↦ by simpa [lucasU_two] using h 1, isCoprime_lucasU_succ_left⟩

/-- If `IsCoprime P Q`, then consecutive terms `lucasU P Q (n + 1)` and `lucasU P Q n` are
coprime for every `n`. -/
theorem isCoprime_lucasU_succ_lucasU {P Q : R} (h : IsCoprime P Q) (n : ℕ) :
    IsCoprime (lucasU P Q (n + 1)) (lucasU P Q n) := by
  induction n with
  | zero => simp [isCoprime_one_left]
  | succ n ih =>
    rw [lucasU_add_two, IsCoprime.mul_sub_right_left_iff]
    exact (isCoprime_lucasU_succ_left h n).symm.mul_left ih.symm

/-- Consecutive terms of `lucasU P Q` are coprime for all `n` if and only if `IsCoprime P Q`. -/
theorem forall_isCoprime_lucasU_succ_lucasU_iff {P Q : R} :
    (∀ n, IsCoprime (lucasU P Q (n + 1)) (lucasU P Q n)) ↔ IsCoprime P Q := by
  refine ⟨fun h ↦ ?_, isCoprime_lucasU_succ_lucasU⟩
  have h2 := h 2
  rw [lucasU_three, lucasU_two, sq, IsCoprime.mul_sub_right_left_iff, isCoprime_comm] at h2
  exact h2

/-! ### Euclidean reduction and strong divisibility of ideal spans -/

/-- Shifting one index by `m` leaves the ideal generated by `lucasU P Q m` and `lucasU P Q k`
unchanged when `IsCoprime P Q`. -/
theorem span_pair_lucasU_add {P Q : R} (h : IsCoprime P Q) (m k : ℕ) :
    Ideal.span {lucasU P Q m, lucasU P Q (m + k)} =
      Ideal.span {lucasU P Q m, lucasU P Q k} := by
  cases m with
  | zero => simp
  | succ m =>
    have hadd : m + 1 + k = k + m + 1 := by omega
    have hsub : lucasU P Q (m + 1 + k) =
        -(Q * lucasU P Q m * lucasU P Q k - lucasU P Q (k + 1) * lucasU P Q (m + 1)) := by
      rw [hadd, lucasU_add_add_one]
      ring
    have hcop : IsCoprime (lucasU P Q (m + 1)) (Q * lucasU P Q m) :=
      (isCoprime_lucasU_succ_left h m).mul_right (isCoprime_lucasU_succ_lucasU h m)
    rw [hsub, Ideal.span_pair_neg, Ideal.span_pair_sub_mul_left,
      Ideal.span_pair_mul_left_right_of_isCoprime hcop]

/-- Adding a multiple of `m` to the second index leaves the ideal generated by `lucasU P Q m` and
`lucasU P Q r` unchanged when `IsCoprime P Q`. -/
theorem span_pair_lucasU_mul_add {P Q : R} (h : IsCoprime P Q) (m q r : ℕ) :
    Ideal.span {lucasU P Q m, lucasU P Q (m * q + r)} =
      Ideal.span {lucasU P Q m, lucasU P Q r} := by
  induction q generalizing r with
  | zero => simp
  | succ q ih =>
    have hmr : m * (q + 1) + r = m * q + (m + r) := by ring
    rw [hmr, ih, span_pair_lucasU_add h]

/-- **Ideal-span strong divisibility for `lucasU`**: in any commutative ring, if `IsCoprime P Q`,
the ideal generated by `lucasU P Q m` and `lucasU P Q n` is the principal ideal generated by
`lucasU P Q (m.gcd n)`. -/
theorem span_pair_lucasU {P Q : R} (h : IsCoprime P Q) (m n : ℕ) :
    Ideal.span {lucasU P Q m, lucasU P Q n} = Ideal.span {lucasU P Q (m.gcd n)} := by
  induction m, n using Nat.gcd.induction with
  | H0 n => simp
  | H1 m n _ ih =>
    calc
      Ideal.span {lucasU P Q m, lucasU P Q n}
        = Ideal.span {lucasU P Q m, lucasU P Q (m * (n / m) + n % m)} := by
          rw [Nat.div_add_mod]
      _ = Ideal.span {lucasU P Q (n % m), lucasU P Q m} := by
          rw [span_pair_lucasU_mul_add h, Set.pair_comm]
      _ = Ideal.span {lucasU P Q (m.gcd n)} := by
          rw [ih, ← Nat.gcd_rec]

/-- If `IsCoprime P Q` and `m.Coprime n`, then `lucasU P Q m` and `lucasU P Q n` are coprime in
`R`. -/
theorem isCoprime_lucasU_of_coprime {P Q : R} (h : IsCoprime P Q) {m n : ℕ} (hmn : m.Coprime n) :
    IsCoprime (lucasU P Q m) (lucasU P Q n) := by
  rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq, ← Ideal.span_insert,
    span_pair_lucasU h, hmn.gcd_eq_one, lucasU_one, Ideal.span_singleton_one]

/-! ### Strong divisibility in normalized GCD monoids -/

private theorem isRelPrime_lucasU_succ_left [DecompositionMonoid R] {P Q : R}
    (h : IsRelPrime P Q) (n : ℕ) : IsRelPrime (lucasU P Q (n + 1)) Q := by
  induction n with
  | zero => simp [isRelPrime_one_left]
  | succ n ih =>
    rw [lucasU_add_two, IsRelPrime.sub_mul_left_left_iff]
    exact h.mul_left ih

private theorem isRelPrime_lucasU_succ_lucasU [DecompositionMonoid R] {P Q : R}
    (h : IsRelPrime P Q) (n : ℕ) : IsRelPrime (lucasU P Q (n + 1)) (lucasU P Q n) := by
  induction n with
  | zero => simp [isRelPrime_one_left]
  | succ n ih =>
    rw [lucasU_add_two, IsRelPrime.mul_sub_right_left_iff]
    exact (isRelPrime_lucasU_succ_left h n).symm.mul_left ih.symm

private theorem gcd_lucasU_add [NormalizedGCDMonoid R] {P Q : R}
    (h : IsRelPrime P Q) (m k : ℕ) :
    GCDMonoid.gcd (lucasU P Q m) (lucasU P Q (m + k)) =
      GCDMonoid.gcd (lucasU P Q m) (lucasU P Q k) := by
  cases m with
  | zero => rw [zero_add]
  | succ m =>
    have hadd : m + 1 + k = k + m + 1 := by omega
    have hdvd : lucasU P Q (m + 1) ∣
        lucasU P Q (m + 1 + k) - -(Q * lucasU P Q m * lucasU P Q k) :=
      ⟨lucasU P Q (k + 1), by rw [hadd, lucasU_add_add_one]; ring⟩
    have hrel : IsRelPrime (lucasU P Q (m + 1)) (Q * lucasU P Q m) :=
      (isRelPrime_lucasU_succ_left h m).mul_right (isRelPrime_lucasU_succ_lucasU h m)
    rw [gcd_eq_of_dvd_sub_right hdvd, gcd_neg, hrel.gcd_mul_left_cancel_right]

private theorem gcd_lucasU_mul_add [NormalizedGCDMonoid R] {P Q : R}
    (h : IsRelPrime P Q) (m q r : ℕ) :
    GCDMonoid.gcd (lucasU P Q m) (lucasU P Q (m * q + r)) =
      GCDMonoid.gcd (lucasU P Q m) (lucasU P Q r) := by
  induction q generalizing r with
  | zero => simp
  | succ q ih =>
    have hmr : m * (q + 1) + r = m * q + (m + r) := by ring
    rw [hmr, ih, gcd_lucasU_add h]

/-- **Strong divisibility of `lucasU` in a commutative `NormalizedGCDMonoid`**: if
`IsRelPrime P Q`, then `gcd (U_m, U_n) = normalize U_{gcd(m, n)}`. -/
theorem gcd_lucasU_eq_normalize [NormalizedGCDMonoid R] {P Q : R} (h : IsRelPrime P Q) (m n : ℕ) :
    GCDMonoid.gcd (lucasU P Q m) (lucasU P Q n) = normalize (lucasU P Q (m.gcd n)) := by
  induction m, n using Nat.gcd.induction with
  | H0 n => simp
  | H1 m n _ ih =>
    calc
      GCDMonoid.gcd (lucasU P Q m) (lucasU P Q n)
        = GCDMonoid.gcd (lucasU P Q m) (lucasU P Q (m * (n / m) + n % m)) := by
          rw [Nat.div_add_mod]
      _ = GCDMonoid.gcd (lucasU P Q (n % m)) (lucasU P Q m) := by
          rw [gcd_lucasU_mul_add h, gcd_comm]
      _ = normalize (lucasU P Q (m.gcd n)) := by
          rw [ih, ← Nat.gcd_rec]

end CommRing

section Int

/-- Every integer Lucas sequence of the first kind gives a natural divisibility sequence after
taking `Int.natAbs`. -/
theorem isDvdSequence_natAbs_lucasU (P Q : ℤ) :
    IsDvdSequence fun n ↦ (lucasU P Q n).natAbs :=
  fun _ _ h ↦ Int.natAbs_dvd_natAbs.mpr (lucasU_dvd_of_dvd P Q h)

/-- **Strong divisibility of integer Lucas sequences**: for coprime `P Q : ℤ` and all `m n : ℕ`,
`Int.gcd (lucasU P Q m) (lucasU P Q n) = (lucasU P Q (Nat.gcd m n)).natAbs`. -/
theorem gcd_lucasU {P Q : ℤ} (h : IsCoprime P Q) (m n : ℕ) :
    Int.gcd (lucasU P Q m) (lucasU P Q n) = (lucasU P Q (Nat.gcd m n)).natAbs := by
  apply Nat.cast_injective (R := ℤ)
  rw [Int.coe_gcd, gcd_lucasU_eq_normalize h.isRelPrime, ← Int.abs_eq_normalize, Int.natCast_natAbs]

/-- For coprime `P Q : ℤ`, `n ↦ (lucasU P Q n).natAbs` is a strong divisibility sequence on `ℕ`. -/
theorem isStrongDvdSequence_natAbs_lucasU {P Q : ℤ} (h : IsCoprime P Q) :
    Nat.IsStrongDvdSequence fun n ↦ (lucasU P Q n).natAbs := by
  intro m n
  rw [← Int.gcd_eq_natAbs, gcd_lucasU h]

/-- **Sharp characterization of strong divisibility for integer Lucas sequences**:
`n ↦ (lucasU P Q n).natAbs` is a strong divisibility sequence if and only if `IsCoprime P Q`. -/
theorem isStrongDvdSequence_natAbs_lucasU_iff {P Q : ℤ} :
    (Nat.IsStrongDvdSequence fun n ↦ (lucasU P Q n).natAbs) ↔ IsCoprime P Q := by
  refine ⟨fun h ↦ ?_, isStrongDvdSequence_natAbs_lucasU⟩
  have h32 : Int.gcd (lucasU P Q 3) (lucasU P Q 2) = 1 := by
    simpa [Int.gcd_eq_natAbs] using h 3 2
  have hcop : IsCoprime (lucasU P Q 3) (lucasU P Q 2) := Int.isCoprime_iff_gcd_eq_one.mpr h32
  rwa [lucasU_three, lucasU_two, sq, IsCoprime.mul_sub_right_left_iff, isCoprime_comm] at hcop

/-- Degenerate root-of-unity check: at `(1, 1)` (sixth roots of unity), `lucasU 1 1 3 = 0` and
`lucasU 1 1 6 = 0`, and strong divisibility holds with `gcd(0, 0) = 0`. -/
example : Int.gcd (lucasU 1 1 3) (lucasU 1 1 6) = (lucasU (1 : ℤ) 1 (Nat.gcd 3 6)).natAbs :=
  gcd_lucasU isCoprime_one_left 3 6

/-- Coprimality is genuinely necessary: at `P = Q = 2`, `lucasU 2 2 2 = 2` and
`lucasU 2 2 3 = 2`, so `Int.gcd (lucasU 2 2 2) (lucasU 2 2 3) = 2 ≠ 1 = |lucasU 2 2 1|`. -/
example : Int.gcd (lucasU 2 2 2) (lucasU 2 2 3) ≠ (lucasU (2 : ℤ) 2 (Nat.gcd 2 3)).natAbs := by
  norm_num [lucasU_two, lucasU_three]

end Int

end TauCeti
