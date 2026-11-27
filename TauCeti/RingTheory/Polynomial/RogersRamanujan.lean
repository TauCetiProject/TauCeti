/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import TauCeti.RingTheory.Polynomial.GaussianBinomial
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.LinearCombination

/-!
# Schur's polynomial identities

Schur's polynomial identities are finite versions of the Rogers–Ramanujan identities. With
`[n k]_t` the Gaussian binomial coefficient, extended by `0` to negative lower indices, they read
```
∑_{j ≥ 0} t^(j²) [n-j j]_t = ∑_{h ∈ ℤ} (-1)^h t^(h(5h+1)/2) [n ⌊(n-5h)/2⌋]_t,
∑_{j ≥ 0} t^(j²+j) [n-j j]_t = ∑_{h ∈ ℤ} (-1)^h t^(h(5h+3)/2) [n+1 ⌊(n-5h)/2⌋]_t,
```
for every `n` and every element `t` of a commutative ring. Both sides are finite sums: the terms
with `j > n`, or with a lower index outside `[0, n]` (respectively `[0, n + 1]`), vanish. Since the
Gaussian binomial coefficients are values of polynomials with natural coefficients, the identities
are identities of integral polynomials, evaluated at `t`. As `n → ∞`, each `[n-j j]` tends to
`1 / ((1 - t) ⋯ (1 - t^j))` coefficientwise, and the right-hand sides tend to theta series that
the Jacobi triple product turns into the products of the Rogers–Ramanujan identities.

Writing `D n` and `E n` for the two left sums, both satisfy Fibonacci-type recurrences
`D (n + 2) = D (n + 1) + t^(n+1) D n` and `E (n + 2) = E (n + 1) + t^(n+2) E n`, with
`D 0 = D 1 = E 0 = E 1 = 1`. We prove the identities by showing that the alternating sums satisfy
the same recurrences and initial values. For an alternating sum, the recurrence follows from the
two successor recursions of the Gaussian coefficients: the defect of the term of index `h` is the
difference of two consecutive values of one sequence, so the defects telescope over `ℤ`.

## Main definitions

* `TauCeti.rogersRamanujanSum t n`, `TauCeti.rogersRamanujanSumTwo t n`: the sums
  `∑_{j ≤ n} t^(j²) [n-j j]_t` and `∑_{j ≤ n} t^(j²+j) [n-j j]_t`.
* `TauCeti.schurAlternatingSum t n`, `TauCeti.schurAlternatingSumTwo t n`: Schur's alternating sums
  `∑ᶠ h : ℤ, (-1)^|h| t^(h(5h+1)/2) [n ⌊(n-5h)/2⌋]_t` and
  `∑ᶠ h : ℤ, (-1)^|h| t^(h(5h+3)/2) [n+1 ⌊(n-5h)/2⌋]_t`.

## Main results

* `TauCeti.rogersRamanujanSum_add_two`, `TauCeti.rogersRamanujanSumTwo_add_two`,
  `TauCeti.schurAlternatingSum_add_two`, `TauCeti.schurAlternatingSumTwo_add_two`: the recurrences.
* `TauCeti.rogersRamanujanSum_eq_schurAlternatingSum`,
  `TauCeti.rogersRamanujanSumTwo_eq_schurAlternatingSumTwo`: **Schur's polynomial identities**.

## References

* I. Schur, *Ein Beitrag zur additiven Zahlentheorie und zur Theorie der Kettenbrüche*,
  Sitzungsberichte der Preussischen Akademie der Wissenschaften (1917), 302–321.
* S. O. Warnaar, *Partial-sum analogues of the Rogers–Ramanujan identities*, arXiv:math/0108193,
  equations (1.3) and (1.4).
-/

public section

open Finset Function

namespace TauCeti

section Semiring

variable {R : Type*} [Semiring R]

/-- The sum `∑_{j ≤ n} t^(j²) [n-j j]_t`, the left side of the first of Schur's polynomial
identities. It is a finite form of `∑_{j ≥ 0} t^(j²) / ((1 - t) ⋯ (1 - t^j))`. -/
noncomputable def rogersRamanujanSum (t : R) (n : ℕ) : R :=
  ∑ j ∈ range (n + 1), t ^ (j ^ 2) * gaussianBinomial t (n - j) j

/-- The sum `∑_{j ≤ n} t^(j²+j) [n-j j]_t`, the left side of the second of Schur's polynomial
identities. It is a finite form of `∑_{j ≥ 0} t^(j²+j) / ((1 - t) ⋯ (1 - t^j))`. -/
noncomputable def rogersRamanujanSumTwo (t : R) (n : ℕ) : R :=
  ∑ j ∈ range (n + 1), t ^ (j ^ 2 + j) * gaussianBinomial t (n - j) j

/-- The recurrence shared by both left sums: with weights `t^(j² + a j)` the sums
`∑_{j ≤ n} t^(j² + a j) [n-j j]_t` satisfy `F (n + 2) = F (n + 1) + t^(n+1+a) F n`. -/
private theorem sum_pow_mul_gaussianBinomial_add_two (t : R) (a n : ℕ) :
    ∑ j ∈ range (n + 3), t ^ (j ^ 2 + a * j) * gaussianBinomial t (n + 2 - j) j =
      ∑ j ∈ range (n + 2), t ^ (j ^ 2 + a * j) * gaussianBinomial t (n + 1 - j) j +
        t ^ (n + 1 + a) *
          ∑ j ∈ range (n + 1), t ^ (j ^ 2 + a * j) * gaussianBinomial t (n - j) j := by
  -- Split each term with `j = i + 1 ≥ 1` by the mirrored successor recursion.
  have hterm (i : ℕ) (hi : i ∈ range (n + 1)) :
      t ^ ((i + 1) ^ 2 + a * (i + 1)) * gaussianBinomial t (n + 2 - (i + 1)) (i + 1) =
        t ^ ((i + 1) ^ 2 + a * (i + 1)) * gaussianBinomial t (n + 1 - (i + 1)) (i + 1) +
          t ^ (n + 1 + a) * (t ^ (i ^ 2 + a * i) * gaussianBinomial t (n - i) i) := by
    have hi := mem_range.1 hi
    rw [show n + 2 - (i + 1) = n - i + 1 by omega, show n + 1 - (i + 1) = n - i by omega,
      gaussianBinomial_succ_succ', mul_add, add_comm, ← mul_assoc, ← mul_assoc, ← pow_add,
      ← pow_add]
    rcases le_or_gt i (n - i) with hle | hlt
    · obtain ⟨d, rfl⟩ : ∃ d, n = i + i + d := ⟨n - i - i, by omega⟩
      rw [show i + i + d - i - i = d by omega,
        show (i + 1) ^ 2 + a * (i + 1) + d = i + i + d + 1 + a + (i ^ 2 + a * i) by ring]
    · rw [gaussianBinomial_eq_zero_of_lt t hlt, mul_zero, mul_zero]
  rw [sum_range_succ' _ (n + 2), sum_range_succ _ (n + 1), sum_range_succ' _ (n + 1), mul_sum,
    sum_congr rfl hterm, sum_add_distrib]
  simp
  abel

/-- `∑_{j ≤ 0} t^(j²) [0-j j]_t = 1`. -/
@[simp]
theorem rogersRamanujanSum_zero (t : R) : rogersRamanujanSum t 0 = 1 := by
  simp [rogersRamanujanSum]

/-- `∑_{j ≤ 1} t^(j²) [1-j j]_t = 1`. -/
@[simp]
theorem rogersRamanujanSum_one (t : R) : rogersRamanujanSum t 1 = 1 := by
  simp [rogersRamanujanSum, sum_range_succ]

/-- The recurrence `D (n + 2) = D (n + 1) + t^(n+1) D n` of the first left sum. -/
theorem rogersRamanujanSum_add_two (t : R) (n : ℕ) :
    rogersRamanujanSum t (n + 2) =
      rogersRamanujanSum t (n + 1) + t ^ (n + 1) * rogersRamanujanSum t n := by
  simpa [rogersRamanujanSum] using sum_pow_mul_gaussianBinomial_add_two t 0 n

/-- `∑_{j ≤ 0} t^(j²+j) [0-j j]_t = 1`. -/
@[simp]
theorem rogersRamanujanSumTwo_zero (t : R) : rogersRamanujanSumTwo t 0 = 1 := by
  simp [rogersRamanujanSumTwo]

/-- `∑_{j ≤ 1} t^(j²+j) [1-j j]_t = 1`. -/
@[simp]
theorem rogersRamanujanSumTwo_one (t : R) : rogersRamanujanSumTwo t 1 = 1 := by
  simp [rogersRamanujanSumTwo, sum_range_succ]

/-- The recurrence `E (n + 2) = E (n + 1) + t^(n+2) E n` of the second left sum. -/
theorem rogersRamanujanSumTwo_add_two (t : R) (n : ℕ) :
    rogersRamanujanSumTwo t (n + 2) =
      rogersRamanujanSumTwo t (n + 1) + t ^ (n + 2) * rogersRamanujanSumTwo t n := by
  simpa [rogersRamanujanSumTwo] using sum_pow_mul_gaussianBinomial_add_two t 1 n

end Semiring

section CommRing

variable {R : Type*} [CommRing R]

/-- Schur's alternating sum `∑_{h ∈ ℤ} (-1)^h t^(h(5h+1)/2) [n ⌊(n-5h)/2⌋]_t`, the right side of
the first of Schur's polynomial identities. Only the finitely many `h` with
`0 ≤ ⌊(n-5h)/2⌋ ≤ n` contribute. -/
noncomputable def schurAlternatingSum (t : R) (n : ℕ) : R :=
  ∑ᶠ h : ℤ, (-1) ^ h.natAbs * t ^ (h * (5 * h + 1) / 2).toNat *
    gaussianBinomialInt t n (((n : ℤ) - 5 * h) / 2)

/-- Schur's alternating sum `∑_{h ∈ ℤ} (-1)^h t^(h(5h+3)/2) [n+1 ⌊(n-5h)/2⌋]_t`, the right side of
the second of Schur's polynomial identities. Only the finitely many `h` with
`0 ≤ ⌊(n-5h)/2⌋ ≤ n + 1` contribute. -/
noncomputable def schurAlternatingSumTwo (t : R) (n : ℕ) : R :=
  ∑ᶠ h : ℤ, (-1) ^ h.natAbs * t ^ (h * (5 * h + 3) / 2).toNat *
    gaussianBinomialInt t (n + 1) (((n : ℤ) - 5 * h) / 2)

/-- A function on `ℤ` vanishing wherever `[m ⌊(N-5h)/2⌋]_t` does has finite support. -/
private theorem hasFiniteSupport_of_gaussianBinomialInt (t : R) (m : ℕ) (N : ℤ) {f : ℤ → R}
    (hf : ∀ h, gaussianBinomialInt t m ((N - 5 * h) / 2) = 0 → f h = 0) : HasFiniteSupport f := by
  refine (Set.finite_Icc (-(N.natAbs + 2 * m + 1 : ℤ)) N.natAbs).subset fun h hh ↦ ?_
  have h₀ : 0 ≤ (N - 5 * h) / 2 := by
    by_contra hc
    exact hh (hf h (gaussianBinomialInt_of_neg t m (not_le.1 hc)))
  have h₁ : (N - 5 * h) / 2 ≤ m := by
    by_contra hc
    exact hh (hf h (gaussianBinomialInt_eq_zero_of_lt t (not_le.1 hc)))
  rw [Set.mem_Icc]
  omega

/-- Two powers of `t` agree in front of `[m k]_t` once their exponents agree for `0 ≤ k ≤ m`. -/
private theorem pow_mul_gaussianBinomialInt_congr (t : R) {m : ℕ} {k : ℤ} {x y : ℕ}
    (hxy : 0 ≤ k → k ≤ m → x = y) :
    t ^ x * gaussianBinomialInt t m k = t ^ y * gaussianBinomialInt t m k := by
  rcases lt_or_ge k 0 with hk | hk
  · rw [gaussianBinomialInt_of_neg t m hk, mul_zero, mul_zero]
  rcases le_or_gt k m with hkm | hkm
  · rw [hxy hk hkm]
  · rw [gaussianBinomialInt_eq_zero_of_lt t hkm, mul_zero, mul_zero]

/-- The sign `(-1)^|h|` changes from `h` to `h + 1`. -/
private theorem neg_one_pow_natAbs_add_one (h : ℤ) :
    (-1 : R) ^ (h + 1).natAbs = -(-1) ^ h.natAbs := by
  rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := h.natAbs)]
  rcases Nat.mod_two_eq_zero_or_one h.natAbs with h₀ | h₁
  · rw [h₀, show (h + 1).natAbs % 2 = 1 by omega]
    simp
  · rw [h₁, show (h + 1).natAbs % 2 = 0 by omega]
    simp

/-- The common shape `∑ᶠ h, (-1)^|h| t^(e h) [n+a ⌊(n-5h)/2⌋]_t` of Schur's two alternating sums,
for an exponent function `e`. -/
private noncomputable def altSum (t : R) (a : ℕ) (e : ℤ → ℕ) (n : ℕ) : R :=
  ∑ᶠ h : ℤ, (-1) ^ h.natAbs * t ^ e h * gaussianBinomialInt t (n + a) (((n : ℤ) - 5 * h) / 2)

/-- The sequence whose consecutive differences are the defects of the recurrence of `altSum`: it
is supported on the `h` with `n - 5h` even. -/
private noncomputable def altSumDefect (t : R) (a : ℕ) (e : ℤ → ℕ) (n : ℕ) (h : ℤ) : R :=
  (if ((n : ℤ) - 5 * h) % 2 = 0 then
      (-1) ^ h.natAbs * t ^ e h * t ^ (((n : ℤ) + 2 - 5 * h) / 2).toNat else 0) *
    gaussianBinomialInt t (n + a) (((n : ℤ) + 2 - 5 * h) / 2)

/-- The defect of the recurrence `F (n + 2) = F (n + 1) + t^(n+1+a) F n` at the term of index `h`
of `altSum` is a difference of consecutive values of `altSumDefect`. -/
private theorem altSum_term_sub (t : R) (a : ℕ) (e : ℤ → ℕ)
    (he : ∀ h, (e (h + 1) : ℤ) = e h + 5 * h + 3 + a) (n : ℕ) (h : ℤ) :
    (-1) ^ h.natAbs * t ^ e h *
        gaussianBinomialInt t (n + 2 + a) ((((n + 2 : ℕ) : ℤ) - 5 * h) / 2) -
      (-1) ^ h.natAbs * t ^ e h *
        gaussianBinomialInt t (n + 1 + a) ((((n + 1 : ℕ) : ℤ) - 5 * h) / 2) -
      t ^ (n + 1 + a) *
        ((-1) ^ h.natAbs * t ^ e h * gaussianBinomialInt t (n + a) (((n : ℤ) - 5 * h) / 2)) =
    altSumDefect t a e n h - altSumDefect t a e n (h + 1) := by
  set k := ((n : ℤ) + 2 - 5 * h) / 2 with hk
  rw [show n + 2 + a = n + a + 1 + 1 by omega, show n + 1 + a = n + a + 1 by omega]
  push_cast
  rcases Int.emod_two_eq_zero_or_one ((n : ℤ) - 5 * h) with hpar | hpar
  · -- `n - 5h = 2k - 2`: only `altSumDefect t a e n h` is nonzero.
    have hb : altSumDefect t a e n h =
        (-1) ^ h.natAbs * t ^ e h * t ^ k.toNat * gaussianBinomialInt t (n + a) k := by
      rw [altSumDefect, ite_eq_left hpar]
    have hb₁ : altSumDefect t a e n (h + 1) = 0 := by
      rw [altSumDefect, ite_eq_right (by omega), zero_mul]
    rw [← hk, show ((n : ℤ) + 1 - 5 * h) / 2 = k - 1 by omega,
      show ((n : ℤ) - 5 * h) / 2 = k - 1 by omega, hb, hb₁,
      gaussianBinomialInt_succ t (n + a + 1) k, gaussianBinomialInt_succ' t (n + a) k]
    have key : t ^ k.toNat * (t ^ ((↑(n + a) : ℤ) + 1 - k).toNat *
        gaussianBinomialInt t (n + a) (k - 1)) =
        t ^ (n + 1 + a) * gaussianBinomialInt t (n + a) (k - 1) := by
      rw [← mul_assoc, ← pow_add]
      exact pow_mul_gaussianBinomialInt_congr t fun _ _ ↦ by omega
    linear_combination ((-1) ^ h.natAbs * t ^ e h) * key
  · -- `n - 5h = 2k - 1`: only `altSumDefect t a e n (h + 1)` is nonzero.
    have hb : altSumDefect t a e n h = 0 := by
      rw [altSumDefect, ite_eq_right (by omega), zero_mul]
    have hb₁ : altSumDefect t a e n (h + 1) = (-1) ^ (h + 1).natAbs * t ^ e (h + 1) *
        t ^ (k - 2).toNat * gaussianBinomialInt t (n + a) (k - 2) := by
      rw [altSumDefect, ite_eq_left (by omega),
        show ((n : ℤ) + 2 - 5 * (h + 1)) / 2 = k - 2 by omega]
    rw [← hk, show ((n : ℤ) + 1 - 5 * h) / 2 = k by omega,
      show ((n : ℤ) - 5 * h) / 2 = k - 1 by omega, hb, hb₁, neg_one_pow_natAbs_add_one,
      gaussianBinomialInt_succ' t (n + a + 1) k, gaussianBinomialInt_succ t (n + a) (k - 1),
      show k - 1 - 1 = k - 2 by ring]
    have key₁ : t ^ ((↑(n + a + 1) : ℤ) + 1 - k).toNat * (t ^ (k - 1).toNat *
        gaussianBinomialInt t (n + a) (k - 1)) =
        t ^ (n + 1 + a) * gaussianBinomialInt t (n + a) (k - 1) := by
      rw [← mul_assoc, ← pow_add]
      exact pow_mul_gaussianBinomialInt_congr t fun _ _ ↦ by omega
    have key₂ : t ^ e h * (t ^ ((↑(n + a + 1) : ℤ) + 1 - k).toNat *
        gaussianBinomialInt t (n + a) (k - 2)) =
        t ^ e (h + 1) * (t ^ (k - 2).toNat * gaussianBinomialInt t (n + a) (k - 2)) := by
      rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
      have := he h
      exact pow_mul_gaussianBinomialInt_congr t fun _ _ ↦ by omega
    linear_combination (-1) ^ h.natAbs * key₂ + ((-1) ^ h.natAbs * t ^ e h) * key₁

/-- The recurrence `F (n + 2) = F (n + 1) + t^(n+1+a) F n` of `altSum`, for an exponent function
`e` with `e (h + 1) = e h + 5h + 3 + a`, as for `e h = h (5h + 1) / 2 + a h`. -/
private theorem altSum_add_two (t : R) (a : ℕ) (e : ℤ → ℕ)
    (he : ∀ h, (e (h + 1) : ℤ) = e h + 5 * h + 3 + a) (n : ℕ) :
    altSum t a e (n + 2) = altSum t a e (n + 1) + t ^ (n + 1 + a) * altSum t a e n := by
  have hfin (m : ℕ) (N : ℤ) (c : ℤ → R) :
      HasFiniteSupport fun h ↦ c h * gaussianBinomialInt t m ((N - 5 * h) / 2) :=
    hasFiniteSupport_of_gaussianBinomialInt t m N fun h h₀ ↦ by rw [h₀, mul_zero]
  have hD : HasFiniteSupport (altSumDefect t a e n) :=
    hasFiniteSupport_of_gaussianBinomialInt t (n + a) (n + 2) fun h h₀ ↦ by
      rw [altSumDefect, h₀, mul_zero]
  have hsum := finsum_congr (altSum_term_sub t a e he n)
  have hshift := finsum_comp_equiv (Equiv.addRight (1 : ℤ)) (f := altSumDefect t a e n)
  simp only [Equiv.coe_addRight] at hshift
  rw [finsum_sub_distrib hD (hD.fun_comp_of_injective (add_left_injective 1)), hshift, sub_self,
    finsum_sub_distrib, finsum_sub_distrib, ← mul_finsum'] at hsum
  · rw [altSum, altSum, altSum]
    linear_combination hsum
  all_goals first
    | exact hfin _ _ _
    | exact (hfin _ _ _).fun_sub (hfin _ _ _)
    | exact HasFiniteSupport.fun_mul_right _ (hfin _ _ _)

/-- For odd `c` with `0 ≤ c ≤ 5`, `e h = h (5h + c) / 2` is a natural number with
`e (h + 1) = e h + 5h + (c + 5) / 2`: these are the consecutive differences needed by
`altSum_add_two`. -/
private theorem toNat_ediv_two_succ {c d : ℤ} (hc : 0 ≤ c) (hc' : c ≤ 5) (hd : c + 5 = 2 * d)
    (h : ℤ) : (((h + 1) * (5 * (h + 1) + c) / 2).toNat : ℤ) =
      (h * (5 * h + c) / 2).toNat + 5 * h + d := by
  have hnonneg (x : ℤ) : 0 ≤ x * (5 * x + c) := by
    rcases le_or_gt 0 x with hx | hx
    · exact mul_nonneg hx (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos hx.le (by omega)
  have heven (x : ℤ) : x * (5 * x + c) % 2 = 0 := by
    rcases Int.emod_two_eq_zero_or_one x with hx | hx <;>
      simp [Int.mul_emod, Int.add_emod, hx, show c % 2 = 1 by omega]
  have h₀ := hnonneg h
  have h₁ := hnonneg (h + 1)
  have h₂ := heven h
  have h₃ := heven (h + 1)
  have hexp : (h + 1) * (5 * (h + 1) + c) = h * (5 * h + c) + 2 * (5 * h) + (c + 5) := by ring
  rw [Int.toNat_of_nonneg (Int.ediv_nonneg h₁ (by norm_num)),
    Int.toNat_of_nonneg (Int.ediv_nonneg h₀ (by norm_num)), hexp]
  omega

/-- `schurAlternatingSum` is `altSum` with `a = 0` and `e h = h(5h+1)/2`. -/
private theorem schurAlternatingSum_eq_altSum (t : R) (n : ℕ) :
    schurAlternatingSum t n = altSum t 0 (fun h ↦ (h * (5 * h + 1) / 2).toNat) n := by
  simp [schurAlternatingSum, altSum]

/-- `schurAlternatingSumTwo` is `altSum` with `a = 1` and `e h = h(5h+3)/2`. -/
private theorem schurAlternatingSumTwo_eq_altSum (t : R) (n : ℕ) :
    schurAlternatingSumTwo t n = altSum t 1 (fun h ↦ (h * (5 * h + 3) / 2).toNat) n := by
  simp [schurAlternatingSumTwo, altSum]

/-- The recurrence `S (n + 2) = S (n + 1) + t^(n+1) S n` of the first alternating sum. -/
theorem schurAlternatingSum_add_two (t : R) (n : ℕ) :
    schurAlternatingSum t (n + 2) =
      schurAlternatingSum t (n + 1) + t ^ (n + 1) * schurAlternatingSum t n := by
  simp only [schurAlternatingSum_eq_altSum]
  exact altSum_add_two t 0 _ (fun h ↦ by
    simpa using toNat_ediv_two_succ (d := 3) (by norm_num) (by norm_num) (by norm_num) h) n

/-- The recurrence `S (n + 2) = S (n + 1) + t^(n+2) S n` of the second alternating sum. -/
theorem schurAlternatingSumTwo_add_two (t : R) (n : ℕ) :
    schurAlternatingSumTwo t (n + 2) =
      schurAlternatingSumTwo t (n + 1) + t ^ (n + 2) * schurAlternatingSumTwo t n := by
  simp only [schurAlternatingSumTwo_eq_altSum]
  exact altSum_add_two t 1 _ (fun h ↦ by
    simpa [add_assoc] using
      toNat_ediv_two_succ (d := 4) (by norm_num) (by norm_num) (by norm_num) h) n

/-- The first alternating sum at `n = 0` is `1`: only `h = 0` contributes. -/
@[simp]
theorem schurAlternatingSum_zero (t : R) : schurAlternatingSum t 0 = 1 := by
  rw [schurAlternatingSum, finsum_eq_single _ 0 fun h hh ↦ by
    rcases lt_or_gt_of_ne hh with hlt | hgt
    · rw [gaussianBinomialInt_eq_zero_of_lt t (by omega), mul_zero]
    · rw [gaussianBinomialInt_of_neg t 0 (by omega), mul_zero]]
  simp

/-- The first alternating sum at `n = 1` is `1`: only `h = 0` contributes. -/
@[simp]
theorem schurAlternatingSum_one (t : R) : schurAlternatingSum t 1 = 1 := by
  rw [schurAlternatingSum, finsum_eq_single _ 0 fun h hh ↦ by
    rcases lt_or_gt_of_ne hh with hlt | hgt
    · rw [gaussianBinomialInt_eq_zero_of_lt t (by omega), mul_zero]
    · rw [gaussianBinomialInt_of_neg t 1 (by omega), mul_zero]]
  simp

/-- The second alternating sum at `n = 0` is `1`: only `h = 0` contributes. -/
@[simp]
theorem schurAlternatingSumTwo_zero (t : R) : schurAlternatingSumTwo t 0 = 1 := by
  rw [schurAlternatingSumTwo, finsum_eq_single _ 0 fun h hh ↦ by
    rcases lt_or_gt_of_ne hh with hlt | hgt
    · rw [gaussianBinomialInt_eq_zero_of_lt t (by omega), mul_zero]
    · rw [gaussianBinomialInt_of_neg t _ (by omega), mul_zero]]
  simp

/-- The second alternating sum at `n = 1` is `1`: only `h = 0` contributes. -/
@[simp]
theorem schurAlternatingSumTwo_one (t : R) : schurAlternatingSumTwo t 1 = 1 := by
  rw [schurAlternatingSumTwo, finsum_eq_single _ 0 fun h hh ↦ by
    rcases lt_or_gt_of_ne hh with hlt | hgt
    · rw [gaussianBinomialInt_eq_zero_of_lt t (by omega), mul_zero]
    · rw [gaussianBinomialInt_of_neg t _ (by omega), mul_zero]]
  simp

/-- **Schur's first polynomial identity**:
`∑_{j ≤ n} t^(j²) [n-j j]_t = ∑_{h ∈ ℤ} (-1)^h t^(h(5h+1)/2) [n ⌊(n-5h)/2⌋]_t`. -/
theorem rogersRamanujanSum_eq_schurAlternatingSum (t : R) (n : ℕ) :
    rogersRamanujanSum t n = schurAlternatingSum t n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih₀ ih₁ => rw [rogersRamanujanSum_add_two, schurAlternatingSum_add_two, ih₀, ih₁]

/-- **Schur's second polynomial identity**:
`∑_{j ≤ n} t^(j²+j) [n-j j]_t = ∑_{h ∈ ℤ} (-1)^h t^(h(5h+3)/2) [n+1 ⌊(n-5h)/2⌋]_t`. -/
theorem rogersRamanujanSumTwo_eq_schurAlternatingSumTwo (t : R) (n : ℕ) :
    rogersRamanujanSumTwo t n = schurAlternatingSumTwo t n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih₀ ih₁ => rw [rogersRamanujanSumTwo_add_two, schurAlternatingSumTwo_add_two, ih₀, ih₁]

end CommRing

end TauCeti
