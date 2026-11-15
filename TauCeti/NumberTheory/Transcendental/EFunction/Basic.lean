/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AlgebraicClosure
public import TauCeti.NumberTheory.Height.House
public import TauCeti.NumberTheory.Transcendental.EFunction.Series
public import TauCeti.RingTheory.Algebraic.Denominator
public import TauCeti.RingTheory.PowerSeries.DFinite.Algebraic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Siegel's E-functions

Following Beukers and Fischler–Rivoal (the geometric-growth refinement of Siegel's 1929
definition), an analytic function

  `eFun a z = ∑' n, aₙ * zⁿ / n!`

is an *E-function* (`TauCeti.IsEFunction a`) when its normalized coefficient sequence `a : ℕ → ℂ`
satisfies four arithmetic-differential conditions:

1. Every `aₙ` is algebraic over `ℚ`.
2. The formal series `ePowerSeries a = ∑ (aₙ / n!) Xⁿ` is D-finite over `algebraicClosure ℚ ℂ`.
3. There exists `C > 0` such that every Galois conjugate of `aₙ` has modulus at most `C ^ (n + 1)`
   (equivalently, `TauCeti.house (aₙ) ≤ C ^ (n + 1)`).
4. There exist `D > 0` and positive integers `dₙ ≤ D ^ (n + 1)` such that `dₙ * aₘ` is an
   algebraic integer for all `m ≤ n`.

All coefficients of an E-function lie in a single number field
(`TauCeti.IsEFunction.exists_numberField`), `eFun a` is an entire analytic function on `ℂ`, and the
class of E-functions is closed under sums, differences, algebraic scalar multiples, Hurwitz
products (analytic multiplication), forward shifts (analytic differentiation), algebraic rescaling
`z ↦ α z`, and coefficientwise ring endomorphisms of `ℂ` (Galois conjugation).

When `a` has rational coefficients and `eFun a 1 = 0`, dividing `eFun a z` by `1 - z` produces an
E-function with coefficients `divOneSubSeq a n = n! * ∑ k ≤ n, aₖ / k!`
(`TauCeti.IsEFunction.divOneSubSeq`); the identity `eFun a 1 = 0` rewrites the partial sum as minus
the convergent tail `-∑' m, a_{n + 1 + m} / (n + 1 + m)!`, supplying the geometric bound on `bₙ`.

## Main definitions

* `TauCeti.IsEFunction a`: the E-function predicate on a coefficient sequence `a : ℕ → ℂ`.
* `TauCeti.divOneSubSeq a`: the coefficient sequence `n ↦ n! * ∑ k ≤ n, aₖ / k!` of the quotient
  by `1 - z`.
* `TauCeti.expSqSeq`: the normalized E-coefficient sequence of `exp (z ^ 2)`, equal to
  `(2k)! / k!` at `n = 2k` and `0` at odd `n`.

## Main results

* `TauCeti.IsEFunction.exists_numberField`: all coefficients of an E-function lie in a common
  number field.
* `TauCeti.IsEFunction.add`, `TauCeti.IsEFunction.hurwitzMul`, `TauCeti.IsEFunction.shift`,
  `TauCeti.IsEFunction.rescale`, `TauCeti.IsEFunction.comp_ringHom`: closure of E-functions.
* `TauCeti.IsEFunction.divOneSubSeq`, `TauCeti.IsEFunction.one_sub_mul_eFun_divOneSubSeq`: quotient
  by `1 - z` for rational E-coefficients vanishing at `1`.
* `TauCeti.isEFunction_const_one`, `TauCeti.isEFunction_sub_one`,
  `TauCeti.not_isEFunction_factorial`, `TauCeti.not_isEFunction_expSqSeq`: concrete examples and
  non-examples (`exp z` and `(z - 1) exp z` are E-functions; `1 / (1 - z)` and `exp (z ^ 2)` are
  not).

## References

* C. L. Siegel, *Über einige Anwendungen diophantischer Approximationen*, Abh. Preuß. Akad. Wiss.,
  Phys.-Math. Kl. 1929, Nr. 1.
* F. Beukers, *A refined version of the Siegel–Shidlovskii theorem*, Ann. of Math. (2) **163**
  (2006), 369–379, §1–2, Corollary 2.2.
* F. Beukers, *E-functions and G-functions*, lecture notes, Arizona Winter School, 2008, §3.1–3.4,
  Proposition 3.2.1, Corollary 3.4.2.
* S. Fischler and T. Rivoal, *Arithmetic theory of E-operators*, J. Éc. polytech. Math. **3**
  (2016), 31–65, Definition 1.
-/

public section

open Filter Polynomial
open scoped ENNReal NNReal PowerSeries Topology

namespace TauCeti

/-! ### Siegel's E-functions -/

/-- A sequence `a : ℕ → ℂ` defines an *E-function* `eFun a` when its terms are algebraic over `ℚ`,
`ePowerSeries a` is D-finite over `algebraicClosure ℚ ℂ`, the Galois conjugates of `aₙ` are
bounded by `C ^ (n + 1)`, and positive integers `dₙ ≤ D ^ (n + 1)` clear the denominators of
`a₀, …, aₙ` simultaneously. -/
structure IsEFunction (a : ℕ → ℂ) : Prop where
  isAlgebraic : ∀ n, IsAlgebraic ℚ (a n)
  isDFinite : PowerSeries.IsDFinite (algebraicClosure ℚ ℂ) (ePowerSeries a)
  size_le : ∃ C : ℝ, 0 < C ∧ ∀ n, ∀ z ∈ (minpoly ℚ (a n)).aroots ℂ, ‖z‖ ≤ C ^ (n + 1)
  den_le : ∃ D : ℝ, 0 < D ∧ ∃ d : ℕ → ℕ,
    ∀ n, 1 ≤ d n ∧ (d n : ℝ) ≤ D ^ (n + 1) ∧ ∀ m ≤ n, IsIntegral ℤ ((d n : ℂ) * a m)

namespace IsEFunction

/-- The house of the coefficients of an E-function grows at most geometrically. -/
theorem exists_house_le {a : ℕ → ℂ} (ha : IsEFunction a) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, house (a n) ≤ C ^ (n + 1) := by
  obtain ⟨C, hC, hsize⟩ := ha.size_le
  refine ⟨C, hC, fun n ↦ (house_le_iff (by positivity)).mpr fun z hz ↦ ?_⟩
  exact hsize n z (Polynomial.mem_aroots'.mpr (Polynomial.mem_rootSet'.mp hz))

/-- Construct `IsEFunction a` using a geometric bound on `TauCeti.house (a n)`. -/
theorem of_house_le {a : ℕ → ℂ} (halg : ∀ n, IsAlgebraic ℚ (a n))
    (hdf : PowerSeries.IsDFinite (algebraicClosure ℚ ℂ) (ePowerSeries a))
    (hhouse : ∃ C : ℝ, 0 < C ∧ ∀ n, house (a n) ≤ C ^ (n + 1))
    (hden : ∃ D : ℝ, 0 < D ∧ ∃ d : ℕ → ℕ,
      ∀ n, 1 ≤ d n ∧ (d n : ℝ) ≤ D ^ (n + 1) ∧ ∀ m ≤ n, IsIntegral ℤ ((d n : ℂ) * a m)) :
    IsEFunction a := by
  refine ⟨halg, hdf, ?_, hden⟩
  obtain ⟨C, hC, hC'⟩ := hhouse
  refine ⟨C, hC, fun n z hz ↦ (norm_le_house_of_mem_rootSet ?_).trans (hC' n)⟩
  exact Polynomial.mem_rootSet'.mpr (Polynomial.mem_aroots'.mp hz)

/-- The complex moduli `‖a n‖` of an E-function grow at most geometrically. -/
theorem exists_norm_le {a : ℕ → ℂ} (ha : IsEFunction a) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, ‖a n‖ ≤ C ^ (n + 1) := by
  obtain ⟨C, hC, hh⟩ := ha.exists_house_le
  exact ⟨C, hC, fun n ↦ (norm_le_house (ha.isAlgebraic n)).trans (hh n)⟩

/-- All coefficients of an E-function lie in a single number field inside `ℂ`. -/
theorem exists_numberField {a : ℕ → ℂ} (ha : IsEFunction a) :
    ∃ (K : IntermediateField ℚ ℂ) (_ : NumberField K), ∀ n, a n ∈ K := by
  simpa using
    ((isDFinite_ePowerSeries_iff (k := algebraicClosure ℚ ℂ) a).mp ha.isDFinite).exists_numberField
      (by simpa using ha.isAlgebraic)

/-- The formal series `ePowerSeries a` of an E-function has infinite convergence radius. -/
theorem radius_ePowerSeries {a : ℕ → ℂ} (ha : IsEFunction a) :
    (ePowerSeries a).radius = ⊤ := by
  obtain ⟨_, _, hnorm⟩ := ha.exists_norm_le
  exact radius_ePowerSeries_of_norm_le hnorm

/-- The formal series `ePowerSeries a` of an E-function is entire. -/
theorem isEntire_ePowerSeries {a : ℕ → ℂ} (ha : IsEFunction a) :
    (ePowerSeries a).IsEntire :=
  PowerSeries.radius_eq_top_iff.mp ha.radius_ePowerSeries

/-- The series `∑ aₙ zⁿ / n!` of an E-function is summable at every `z : ℂ`. -/
theorem summable_eFun_term {a : ℕ → ℂ} (ha : IsEFunction a) (z : ℂ) :
    Summable fun n : ℕ ↦ a n * z ^ n / n.factorial := by
  obtain ⟨_, _, hnorm⟩ := ha.exists_norm_le
  exact summable_eFun_term_of_norm_le hnorm z

/-- The series `∑ aₙ zⁿ / n!` of an E-function converges to `eFun a z` at every `z : ℂ`. -/
theorem hasSum_eFun {a : ℕ → ℂ} (ha : IsEFunction a) (z : ℂ) :
    HasSum (fun n : ℕ ↦ a n * z ^ n / n.factorial) (eFun a z) := by
  obtain ⟨_, _, hnorm⟩ := ha.exists_norm_le
  exact hasSum_eFun_of_norm_le hnorm z

/-- An E-function is represented by its formal Taylor series on the open ball of radius `⊤`. -/
theorem hasFPowerSeriesOnBall_eFun {a : ℕ → ℂ} (ha : IsEFunction a) :
    HasFPowerSeriesOnBall (eFun a)
      (FormalMultilinearSeries.ofScalars ℂ fun n ↦ a n / n.factorial) 0 ⊤ := by
  obtain ⟨_, _, hnorm⟩ := ha.exists_norm_le
  exact hasFPowerSeriesOnBall_eFun_of_norm_le hnorm

/-- For an E-function `a`, `eFun a` is analytic on all of `ℂ`. -/
theorem analyticOnNhd_eFun {a : ℕ → ℂ} (ha : IsEFunction a) :
    AnalyticOnNhd ℂ (eFun a) Set.univ := by
  obtain ⟨_, _, hnorm⟩ := ha.exists_norm_le
  exact analyticOnNhd_eFun_of_norm_le hnorm

/-- For an E-function `a`, `eFun a` is entire (differentiable everywhere on `ℂ`). -/
theorem differentiable_eFun {a : ℕ → ℂ} (ha : IsEFunction a) :
    Differentiable ℂ (eFun a) := by
  obtain ⟨_, _, hnorm⟩ := ha.exists_norm_le
  exact differentiable_eFun_of_norm_le hnorm

/-- Complex differentiation of `eFun a` shifts the coefficients of an E-function by `1`. -/
theorem deriv_eFun {a : ℕ → ℂ} (ha : IsEFunction a) :
    deriv (eFun a) = eFun fun n ↦ a (n + 1) := by
  obtain ⟨_, _, hnorm⟩ := ha.exists_norm_le
  exact deriv_eFun_of_norm_le hnorm

/-- The `m`-th derivative at `0` of `eFun a` is `a m`. -/
theorem iteratedDeriv_eFun_eval_zero {a : ℕ → ℂ} (ha : IsEFunction a) (m : ℕ) :
    iteratedDeriv m (eFun a) 0 = a m := by
  obtain ⟨_, _, hnorm⟩ := ha.exists_norm_le
  rw [iteratedDeriv_eFun_of_norm_le hnorm m, eFun_eval_zero, zero_add]

/-- For two E-functions `a` and `b`, `eFun (a + b) z = eFun a z + eFun b z`. -/
theorem eFun_add {a b : ℕ → ℂ} (ha : IsEFunction a) (hb : IsEFunction b) (z : ℂ) :
    eFun (a + b) z = eFun a z + eFun b z := by
  obtain ⟨_, _, hna⟩ := ha.exists_norm_le
  obtain ⟨_, _, hnb⟩ := hb.exists_norm_le
  exact eFun_add_of_norm_le hna hnb z

/-- For two E-functions `a` and `b`, `eFun (hurwitzMul a b) z = eFun a z * eFun b z`. -/
theorem eFun_hurwitzMul {a b : ℕ → ℂ} (ha : IsEFunction a) (hb : IsEFunction b) (z : ℂ) :
    eFun (hurwitzMul a b) z = eFun a z * eFun b z := by
  obtain ⟨_, _, hna⟩ := ha.exists_norm_le
  obtain ⟨_, _, hnb⟩ := hb.exists_norm_le
  exact eFun_hurwitzMul_of_norm_le hna hnb z

end IsEFunction

/-! ### Closure properties and basic examples of E-functions -/

/-- The zero sequence is an E-function. -/
@[simp]
theorem isEFunction_zero : IsEFunction 0 :=
  IsEFunction.of_house_le
    (fun _ ↦ isAlgebraic_zero)
    (by simp)
    ⟨1, one_pos, fun _ ↦ by simp⟩
    ⟨1, one_pos, fun _ ↦ 1, fun _ ↦ ⟨le_rfl, by simp, fun _ _ ↦ by simp [isIntegral_zero]⟩⟩

/-- Any sequence supported at a single index `k` with an algebraic value `c` is an E-function. -/
theorem isEFunction_single (k : ℕ) {c : ℂ} (hc : IsAlgebraic ℚ c) :
    IsEFunction (Pi.single k c) := by
  refine IsEFunction.of_house_le ?_ ?_ ?_ ?_
  · intro n
    by_cases hnk : n = k
    · subst hnk; simpa using hc
    · simp [Pi.single_eq_of_ne hnk, isAlgebraic_zero]
  · rw [ePowerSeries_single]
    have hX : (PowerSeries.X ^ k : ℂ⟦X⟧) = ((Polynomial.X ^ k : ℂ[X]) : ℂ⟦X⟧) := by simp
    rw [hX]
    exact (PowerSeries.isDFinite_polynomial (algebraicClosure ℚ ℂ) _).smul _
  · refine ⟨max 1 (house c), by positivity, fun n ↦ ?_⟩
    by_cases hnk : n = k
    · subst hnk
      simpa using (le_max_right 1 (house c)).trans
        (le_self_pow₀ (le_max_left 1 (house c)) (Nat.succ_ne_zero n))
    · simp only [Pi.single_eq_of_ne hnk, house_zero]
      positivity
  · set q := Algebra.natDenominator c
    have hq0 : 1 ≤ q :=
      Nat.one_le_iff_ne_zero.mpr (Algebra.natDenominator_ne_zero_of_isAlgebraic_rat hc)
    have hqint : IsIntegral ℤ ((q : ℂ) * c) := by
      simpa [q, nsmul_eq_mul] using Algebra.isIntegral_natDenominator_smul c
    refine ⟨q, by positivity, fun _ ↦ q, fun n ↦ ⟨hq0, ?_, fun m _ ↦ ?_⟩⟩
    · exact_mod_cast Nat.le_self_pow (Nat.succ_ne_zero n) q
    · by_cases hmk : m = k
      · subst hmk; simpa using hqint
      · simp [Pi.single_eq_of_ne hmk, isIntegral_zero]

/-- A constant algebraic term at index `0` defines an E-function. -/
theorem isEFunction_single_zero {c : ℂ} (hc : IsAlgebraic ℚ c) :
    IsEFunction (Pi.single 0 c) :=
  isEFunction_single 0 hc

/-- The constant-one sequence (representing `Complex.exp`) is an E-function. -/
@[simp]
theorem isEFunction_const_one : IsEFunction (fun _ ↦ 1) :=
  IsEFunction.of_house_le
    (fun _ ↦ isAlgebraic_one)
    (by simp)
    ⟨1, one_pos, fun _ ↦ by simp⟩
    ⟨1, one_pos, fun _ ↦ 1, fun _ ↦ ⟨le_rfl, by simp, fun _ _ ↦ by simp [isIntegral_one]⟩⟩

namespace IsEFunction

/-- Negation preserves E-functions. -/
protected theorem neg {a : ℕ → ℂ} (ha : IsEFunction a) : IsEFunction (-a) := by
  obtain ⟨C, hC, hh⟩ := ha.exists_house_le
  obtain ⟨D, hD, d, hd⟩ := ha.den_le
  refine of_house_le (fun n ↦ (ha.isAlgebraic n).neg)
    (by rw [ePowerSeries_neg]; exact ha.isDFinite.neg)
    ⟨C, hC, fun n ↦ by simpa using hh n⟩
    ⟨D, hD, d, fun n ↦ ⟨(hd n).1, (hd n).2.1, fun m hm ↦ ?_⟩⟩
  simpa [mul_neg] using ((hd n).2.2 m hm).neg

/-- Sums of E-functions are E-functions. -/
protected theorem add {a b : ℕ → ℂ} (ha : IsEFunction a) (hb : IsEFunction b) :
    IsEFunction (a + b) := by
  obtain ⟨C₁, hC₁, hha⟩ := ha.exists_house_le
  obtain ⟨C₂, hC₂, hhb⟩ := hb.exists_house_le
  obtain ⟨D₁, hD₁, d₁, hd₁⟩ := ha.den_le
  obtain ⟨D₂, hD₂, d₂, hd₂⟩ := hb.den_le
  have halg (n : ℕ) : IsAlgebraic ℚ (a n + b n) := by
    rw [← mem_algebraicClosure_iff]
    exact add_mem (mem_algebraicClosure_iff.mpr (ha.isAlgebraic n))
      (mem_algebraicClosure_iff.mpr (hb.isAlgebraic n))
  refine of_house_le halg (by rw [ePowerSeries_add]; exact ha.isDFinite.add hb.isDFinite) ?_ ?_
  · refine ⟨2 * max C₁ C₂, by positivity, fun n ↦ ?_⟩
    calc house (a n + b n)
        ≤ house (a n) + house (b n) := house_add_le (ha.isAlgebraic n) (hb.isAlgebraic n)
      _ ≤ max C₁ C₂ ^ (n + 1) + max C₁ C₂ ^ (n + 1) :=
          add_le_add ((hha n).trans (by gcongr; exact le_max_left _ _))
            ((hhb n).trans (by gcongr; exact le_max_right _ _))
      _ = 2 * max C₁ C₂ ^ (n + 1) := by ring
      _ ≤ (2 * max C₁ C₂) ^ (n + 1) := by
          rw [mul_pow]
          gcongr
          exact le_self_pow₀ (by norm_num) (Nat.succ_ne_zero n)
  · refine ⟨D₁ * D₂, mul_pos hD₁ hD₂, fun n ↦ d₁ n * d₂ n, fun n ↦ ?_⟩
    refine ⟨Nat.mul_le_mul (hd₁ n).1 (hd₂ n).1, ?_, fun m hm ↦ ?_⟩
    · rw [Nat.cast_mul, mul_pow]
      exact mul_le_mul (hd₁ n).2.1 (hd₂ n).2.1 (Nat.cast_nonneg _) (by positivity)
    · simp only [Pi.add_apply]
      have h1 : ((d₁ n * d₂ n : ℕ) : ℂ) * (a m + b m) =
          (d₂ n : ℂ) * ((d₁ n : ℂ) * a m) + (d₁ n : ℂ) * ((d₂ n : ℂ) * b m) := by
        push_cast; ring
      rw [h1]
      exact ((isIntegral_natCast _).mul ((hd₁ n).2.2 m hm)).add
        ((isIntegral_natCast _).mul ((hd₂ n).2.2 m hm))

/-- Differences of E-functions are E-functions. -/
protected theorem sub {a b : ℕ → ℂ} (ha : IsEFunction a) (hb : IsEFunction b) :
    IsEFunction (a - b) := by
  simpa [sub_eq_add_neg] using ha.add hb.neg

/-- Multiplying an E-function by an algebraic scalar gives an E-function. -/
protected theorem smul {c : ℂ} (hc : IsAlgebraic ℚ c) {a : ℕ → ℂ} (ha : IsEFunction a) :
    IsEFunction (c • a) := by
  obtain ⟨C, hC, hha⟩ := ha.exists_house_le
  obtain ⟨D, hD, d, hd⟩ := ha.den_le
  set q := Algebra.natDenominator c
  have hq1 : 1 ≤ q :=
    Nat.one_le_iff_ne_zero.mpr (Algebra.natDenominator_ne_zero_of_isAlgebraic_rat hc)
  have hqint : IsIntegral ℤ ((q : ℂ) * c) := by
    simpa [q, nsmul_eq_mul] using Algebra.isIntegral_natDenominator_smul c
  have halg (n : ℕ) : IsAlgebraic ℚ (c * a n) := by
    rw [← mem_algebraicClosure_iff]
    exact mul_mem (mem_algebraicClosure_iff.mpr hc)
      (mem_algebraicClosure_iff.mpr (ha.isAlgebraic n))
  refine of_house_le halg (by rw [ePowerSeries_smul]; exact ha.isDFinite.smul c) ?_ ?_
  · set B := max 1 (house c) * C
    refine ⟨B, by positivity, fun n ↦ ?_⟩
    have hc_le : house c ≤ max 1 (house c) ^ (n + 1) :=
      (le_max_right 1 (house c)).trans
        (le_self_pow₀ (le_max_left 1 (house c)) (Nat.succ_ne_zero n))
    calc house (c * a n)
        ≤ house c * house (a n) := house_mul_le hc (ha.isAlgebraic n)
      _ ≤ max 1 (house c) ^ (n + 1) * C ^ (n + 1) :=
          mul_le_mul hc_le (hha n) (house_nonneg _) (by positivity)
      _ = B ^ (n + 1) := by rw [← mul_pow]
  · refine ⟨q * D, by positivity, fun n ↦ q * d n, fun n ↦ ?_⟩
    refine ⟨Nat.mul_le_mul hq1 (hd n).1, ?_, fun m hm ↦ ?_⟩
    · rw [Nat.cast_mul, mul_pow]
      exact mul_le_mul (by exact_mod_cast Nat.le_self_pow (Nat.succ_ne_zero n) q)
        (hd n).2.1 (Nat.cast_nonneg _) (by positivity)
    · simp only [Pi.smul_apply, smul_eq_mul]
      have hmul : ((q * d n : ℕ) : ℂ) * (c * a m) = ((q : ℂ) * c) * ((d n : ℂ) * a m) := by
        push_cast; ring
      rw [hmul]
      exact hqint.mul ((hd n).2.2 m hm)

private theorem house_hurwitzMul_le {a b : ℕ → ℂ} {C₁ C₂ : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (halg_a : ∀ n, IsAlgebraic ℚ (a n)) (halg_b : ∀ n, IsAlgebraic ℚ (b n))
    (hha : ∀ n, house (a n) ≤ C₁ ^ (n + 1)) (hhb : ∀ n, house (b n) ≤ C₂ ^ (n + 1)) (n : ℕ) :
    house (TauCeti.hurwitzMul a b n) ≤ (2 * max 1 (max C₁ C₂) ^ 2) ^ (n + 1) := by
  set B := max 1 (max C₁ C₂)
  have hB1 : 1 ≤ B := le_max_left _ _
  have hC₁B : C₁ ≤ B := (le_max_left C₁ C₂).trans (le_max_right _ _)
  have hC₂B : C₂ ≤ B := (le_max_right C₁ C₂).trans (le_max_right _ _)
  have hterm_alg (k : ℕ) : IsAlgebraic ℚ ((n.choose k : ℂ) * (a k * b (n - k))) := by
    rw [← mem_algebraicClosure_iff]
    exact mul_mem (natCast_mem _ _)
      (mul_mem (mem_algebraicClosure_iff.mpr (halg_a k))
        (mem_algebraicClosure_iff.mpr (halg_b (n - k))))
  rw [hurwitzMul_def]
  have hnsmul : (∑ k ∈ Finset.range (n + 1), n.choose k • (a k * b (n - k))) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (a k * b (n - k)) :=
    Finset.sum_congr rfl fun _ _ ↦ nsmul_eq_mul _ _
  rw [hnsmul]
  calc house (∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (a k * b (n - k)))
      ≤ ∑ k ∈ Finset.range (n + 1), house ((n.choose k : ℂ) * (a k * b (n - k))) :=
        house_sum_le _ fun k _ ↦ hterm_alg k
    _ ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * B ^ (n + 2) := by
        refine Finset.sum_le_sum fun k hk ↦ ?_
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hexp : k + 1 + (n - k + 1) = n + 2 := by omega
        have hab : IsAlgebraic ℚ (a k * b (n - k)) := by
          rw [← mem_algebraicClosure_iff]
          exact mul_mem (mem_algebraicClosure_iff.mpr (halg_a k))
            (mem_algebraicClosure_iff.mpr (halg_b (n - k)))
        have hak : house (a k) ≤ B ^ (k + 1) :=
          (hha k).trans (pow_le_pow_left₀ hC₁.le hC₁B _)
        have hbk : house (b (n - k)) ≤ B ^ (n - k + 1) :=
          (hhb (n - k)).trans (pow_le_pow_left₀ hC₂.le hC₂B _)
        calc house ((n.choose k : ℂ) * (a k * b (n - k)))
            ≤ house (n.choose k : ℂ) * (house (a k) * house (b (n - k))) :=
              (house_mul_le (isAlgebraic_natCast _) hab).trans
                (mul_le_mul_of_nonneg_left
                  (house_mul_le (halg_a k) (halg_b (n - k))) (house_nonneg _))
          _ ≤ (n.choose k : ℝ) * (B ^ (k + 1) * B ^ (n - k + 1)) := by
              rw [house_natCast]
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul hak hbk (house_nonneg _) (by positivity)) (Nat.cast_nonneg _)
          _ = (n.choose k : ℝ) * B ^ (n + 2) := by rw [← pow_add, hexp]
    _ = 2 ^ n * B ^ (n + 2) := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ (2 * B ^ 2) ^ (n + 1) := by
        rw [mul_pow, ← pow_mul]
        exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n))
          (pow_le_pow_right₀ hB1 (by omega)) (by positivity) (by positivity)

/-- **Products of E-functions are E-functions.** The Hurwitz convolution of two E-functions is an
E-function. -/
protected theorem hurwitzMul {a b : ℕ → ℂ} (ha : IsEFunction a) (hb : IsEFunction b) :
    IsEFunction (TauCeti.hurwitzMul a b) := by
  obtain ⟨C₁, hC₁, hha⟩ := ha.exists_house_le
  obtain ⟨C₂, hC₂, hhb⟩ := hb.exists_house_le
  obtain ⟨D₁, hD₁, d₁, hd₁⟩ := ha.den_le
  obtain ⟨D₂, hD₂, d₂, hd₂⟩ := hb.den_le
  have halg (n : ℕ) : IsAlgebraic ℚ (TauCeti.hurwitzMul a b n) := by
    rw [hurwitzMul_def, ← mem_algebraicClosure_iff]
    refine sum_mem fun k _ ↦ ?_
    rw [nsmul_eq_mul]
    exact mul_mem (natCast_mem _ _)
      (mul_mem (mem_algebraicClosure_iff.mpr (ha.isAlgebraic k))
        (mem_algebraicClosure_iff.mpr (hb.isAlgebraic (n - k))))
  refine of_house_le halg (by rw [ePowerSeries_hurwitzMul]; exact ha.isDFinite.mul hb.isDFinite)
    ⟨2 * max 1 (max C₁ C₂) ^ 2, by positivity,
      house_hurwitzMul_le hC₁ hC₂ ha.isAlgebraic hb.isAlgebraic hha hhb⟩ ?_
  refine ⟨D₁ * D₂, mul_pos hD₁ hD₂, fun n ↦ d₁ n * d₂ n, fun n ↦ ?_⟩
  refine ⟨Nat.mul_le_mul (hd₁ n).1 (hd₂ n).1, ?_, fun m hm ↦ ?_⟩
  · rw [Nat.cast_mul, mul_pow]
    exact mul_le_mul (hd₁ n).2.1 (hd₂ n).2.1 (Nat.cast_nonneg _) (by positivity)
  · rw [hurwitzMul_def, Finset.mul_sum, ← mem_integralClosure_iff]
    refine sum_mem fun k hk ↦ ?_
    rw [mem_integralClosure_iff]
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1 : ((d₁ n * d₂ n : ℕ) : ℂ) * (m.choose k • (a k * b (m - k))) =
        (m.choose k : ℂ) * (((d₁ n : ℂ) * a k) * ((d₂ n : ℂ) * b (m - k))) := by
      rw [nsmul_eq_mul]; push_cast; ring
    rw [h1]
    exact (isIntegral_natCast _).mul (((hd₁ n).2.2 k (hkm.trans hm)).mul
      ((hd₂ n).2.2 (m - k) ((Nat.sub_le m k).trans hm)))

/-- **Derivatives of E-functions are E-functions.** Shifting the coefficient sequence by `1`
preserves `IsEFunction`. -/
protected theorem shift {a : ℕ → ℂ} (ha : IsEFunction a) :
    IsEFunction fun n ↦ a (n + 1) := by
  obtain ⟨C, hC, hha⟩ := ha.exists_house_le
  obtain ⟨D, hD, d, hd⟩ := ha.den_le
  refine of_house_le (fun n ↦ ha.isAlgebraic (n + 1))
    (by rw [← derivative_ePowerSeries]; exact ha.isDFinite.derivative) ?_ ?_
  · refine ⟨max 1 C ^ 2, by positivity, fun n ↦ (hha (n + 1)).trans ?_⟩
    calc C ^ (n + 2) ≤ max 1 C ^ (n + 2) := by gcongr; exact le_max_right 1 C
      _ ≤ max 1 C ^ (2 * (n + 1)) := pow_le_pow_right₀ (le_max_left 1 C) (by omega)
      _ = (max 1 C ^ 2) ^ (n + 1) := by rw [pow_mul]
  · refine ⟨max 1 D ^ 2, by positivity, fun n ↦ d (n + 1), fun n ↦ ⟨(hd (n + 1)).1, ?_, ?_⟩⟩
    · refine ((hd (n + 1)).2.1).trans ?_
      calc D ^ (n + 2) ≤ max 1 D ^ (n + 2) := by gcongr; exact le_max_right 1 D
        _ ≤ max 1 D ^ (2 * (n + 1)) := pow_le_pow_right₀ (le_max_left 1 D) (by omega)
        _ = (max 1 D ^ 2) ^ (n + 1) := by rw [pow_mul]
    · exact fun m hm ↦ (hd (n + 1)).2.2 (m + 1) (Nat.succ_le_succ hm)

/-- Rescaling the variable by an algebraic number `α` (`aₙ ↦ αⁿ aₙ`) preserves `IsEFunction`. -/
protected theorem rescale {α : ℂ} (hα : IsAlgebraic ℚ α) {a : ℕ → ℂ} (ha : IsEFunction a) :
    IsEFunction fun n ↦ α ^ n * a n := by
  obtain ⟨C, hC, hha⟩ := ha.exists_house_le
  obtain ⟨D, hD, d, hd⟩ := ha.den_le
  let α₀ : algebraicClosure ℚ ℂ := ⟨α, mem_algebraicClosure_iff.mpr hα⟩
  have halg (n : ℕ) : IsAlgebraic ℚ (α ^ n * a n) := by
    rw [← mem_algebraicClosure_iff]
    exact mul_mem (pow_mem α₀.2 n) (mem_algebraicClosure_iff.mpr (ha.isAlgebraic n))
  refine of_house_le halg
    (by rw [← rescale_ePowerSeries]; exact ha.isDFinite.rescale α₀) ?_ ?_
  · set B := max 1 (house α) * C
    refine ⟨B, by positivity, fun n ↦ ?_⟩
    have hαn : IsAlgebraic ℚ (α ^ n) := mem_algebraicClosure_iff.mp (pow_mem α₀.2 n)
    have hα_le : house α ^ n ≤ max 1 (house α) ^ (n + 1) :=
      (pow_le_pow_left₀ (house_nonneg α) (le_max_right 1 (house α)) n).trans
        (pow_le_pow_right₀ (le_max_left 1 (house α)) (Nat.le_succ n))
    calc house (α ^ n * a n)
        ≤ house (α ^ n) * house (a n) := house_mul_le hαn (ha.isAlgebraic n)
      _ = house α ^ n * house (a n) := by rw [house_pow]
      _ ≤ max 1 (house α) ^ (n + 1) * C ^ (n + 1) :=
          mul_le_mul hα_le (hha n) (house_nonneg _) (by positivity)
      _ = B ^ (n + 1) := by rw [← mul_pow]
  · set q := Algebra.natDenominator α
    have hq1 : 1 ≤ q :=
      Nat.one_le_iff_ne_zero.mpr (Algebra.natDenominator_ne_zero_of_isAlgebraic_rat hα)
    have hqint : IsIntegral ℤ ((q : ℂ) * α) := by
      simpa [q, nsmul_eq_mul] using Algebra.isIntegral_natDenominator_smul α
    refine ⟨q * D, by positivity, fun n ↦ q ^ n * d n, fun n ↦ ?_⟩
    refine ⟨Nat.mul_le_mul (Nat.one_le_pow n q hq1) (hd n).1, ?_, fun m hm ↦ ?_⟩
    · rw [Nat.cast_mul, Nat.cast_pow, mul_pow]
      exact mul_le_mul (pow_le_pow_right₀ (by exact_mod_cast hq1) (Nat.le_succ n))
        (hd n).2.1 (Nat.cast_nonneg _) (by positivity)
    · have hsplit : ((q ^ n * d n : ℕ) : ℂ) * (α ^ m * a m) =
          (q : ℂ) ^ (n - m) * ((q : ℂ) * α) ^ m * ((d n : ℂ) * a m) := by
        have hqn : (q : ℂ) ^ n = (q : ℂ) ^ (n - m) * (q : ℂ) ^ m := by
          rw [← pow_add, Nat.sub_add_cancel hm]
        push_cast
        rw [hqn, mul_pow]
        ring
      rw [hsplit]
      exact (((isIntegral_natCast q).pow _).mul (hqint.pow m)).mul ((hd n).2.2 m hm)

/-- **Galois conjugation of E-functions.** Applying any ring endomorphism `σ : ℂ →+* ℂ`
coefficientwise to an E-function gives an E-function. -/
protected theorem comp_ringHom {a : ℕ → ℂ} (ha : IsEFunction a) (σ : ℂ →+* ℂ) :
    IsEFunction (σ ∘ a) := by
  obtain ⟨C, hC, hha⟩ := ha.exists_house_le
  obtain ⟨D, hD, d, hd⟩ := ha.den_le
  let σ₀ : algebraicClosure ℚ ℂ →+* algebraicClosure ℚ ℂ :=
    { toFun := fun x ↦ ⟨σ x, (map_mem_algebraicClosure_iff σ.toRatAlgHom).mpr x.2⟩
      map_one' := Subtype.ext σ.map_one
      map_mul' := fun x y ↦ Subtype.ext (σ.map_mul x y)
      map_zero' := Subtype.ext σ.map_zero
      map_add' := fun x y ↦ Subtype.ext (σ.map_add x y) }
  have halg (n : ℕ) : IsAlgebraic ℚ (σ (a n)) :=
    mem_algebraicClosure_iff.mp
      ((map_mem_algebraicClosure_iff σ.toRatAlgHom).mpr
        (mem_algebraicClosure_iff.mpr (ha.isAlgebraic n)))
  refine of_house_le halg
    (by rw [← map_ePowerSeries]; exact ha.isDFinite.map σ₀ σ fun _ ↦ rfl)
    ⟨C, hC, fun n ↦ by simpa [Function.comp_apply] using hha n⟩
    ⟨D, hD, d, fun n ↦ ⟨(hd n).1, (hd n).2.1, fun m hm ↦ ?_⟩⟩
  have himg : (d n : ℂ) * σ (a m) = σ ((d n : ℂ) * a m) := by simp
  rw [Function.comp_apply, himg]
  exact ((hd n).2.2 m hm).map σ.toIntAlgHom

end IsEFunction

/-- The sequence `n ↦ α ^ n` (representing `z ↦ exp (α z)`) is an E-function for algebraic `α`. -/
theorem isEFunction_pow {α : ℂ} (hα : IsAlgebraic ℚ α) : IsEFunction (α ^ ·) := by
  simpa using isEFunction_const_one.rescale hα

/-! ### Division by `1 - z` for rational E-coefficients vanishing at `1` -/

/-- Given `a : ℕ → ℂ`, the normalized coefficient sequence
`divOneSubSeq a n = n! * ∑ k ∈ Finset.range (n + 1), a k / k!` of `(1 - X)⁻¹ * ePowerSeries a`. -/
noncomputable def divOneSubSeq (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  n.factorial * ∑ k ∈ Finset.range (n + 1), a k / k.factorial

/-- Unfolding `divOneSubSeq`. -/
theorem divOneSubSeq_def (a : ℕ → ℂ) (n : ℕ) :
    divOneSubSeq a n = n.factorial * ∑ k ∈ Finset.range (n + 1), a k / k.factorial :=
  (rfl)

/-- At `n = 0`, `divOneSubSeq a 0 = a 0`. -/
@[simp]
theorem divOneSubSeq_zero (a : ℕ → ℂ) : divOneSubSeq a 0 = a 0 := by
  simp [divOneSubSeq_def]

/-- `divOneSubSeq` maps the zero sequence to `0`. -/
@[simp]
theorem divOneSubSeq_zero_seq : divOneSubSeq 0 = 0 := by
  ext n
  simp [divOneSubSeq_def]

/-- Formal identity `(1 - X) * ePowerSeries (divOneSubSeq a) = ePowerSeries a`. -/
@[simp]
theorem one_sub_X_mul_ePowerSeries_divOneSubSeq (a : ℕ → ℂ) :
    (1 - PowerSeries.X) * ePowerSeries (divOneSubSeq a) = ePowerSeries a := by
  have hcoeff (n : ℕ) :
      PowerSeries.coeff n (ePowerSeries (divOneSubSeq a)) =
        ∑ k ∈ Finset.range (n + 1), a k / k.factorial := by
    rw [coeff_ePowerSeries, divOneSubSeq_def,
      mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))]
  ext n
  cases n with
  | zero => simp [sub_mul]
  | succ n =>
    rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul, hcoeff, hcoeff,
      Finset.sum_range_succ, add_sub_cancel_left, coeff_ePowerSeries]

private theorem norm_divOneSubSeq_le {a : ℕ → ℂ} {C : ℝ} (hC : 0 < C)
    (hnorm : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) (hz : eFun a 1 = 0) (n : ℕ) :
    ‖divOneSubSeq a n‖ ≤ (max 1 C ^ 2 * Real.exp C) ^ (n + 1) := by
  have hsum1 : Summable fun k : ℕ ↦ a k / k.factorial := by
    simpa using summable_eFun_term_of_norm_le hnorm 1
  have hz0 : (∑' k : ℕ, a k / k.factorial) = 0 := by simpa [eFun_def] using hz
  have hsplit := hsum1.sum_add_tsum_nat_add (n + 1)
  rw [hz0] at hsplit
  have htail := eq_neg_of_add_eq_zero_left hsplit
  have hterm_le (m : ℕ) :
      ‖(n.factorial : ℂ) * (a (m + (n + 1)) / (m + (n + 1)).factorial)‖ ≤
        C ^ (n + 2) * (C ^ m / m.factorial) := by
    have hfac_le : n.factorial * m.factorial ≤ (m + (n + 1)).factorial :=
      calc n.factorial * m.factorial
          ≤ (n + 1).factorial * m.factorial :=
            Nat.mul_le_mul_right _ (Nat.factorial_le (Nat.le_succ n))
        _ = 1 * (m.factorial * (n + 1).factorial) := by ring
        _ ≤ (m + (n + 1)).choose (n + 1) * (m.factorial * (n + 1).factorial) :=
            Nat.mul_le_mul_right _ (Nat.choose_pos (Nat.le_add_left (n + 1) m))
        _ = (m + (n + 1)).factorial := by
            rw [← mul_assoc, Nat.add_choose_mul_factorial_mul_factorial]
    have hexp : m + (n + 1) + 1 = (n + 2) + m := by omega
    have hnf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hmf : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
    calc (n.factorial : ℝ) * (‖a (m + (n + 1))‖ / (m + (n + 1)).factorial)
        ≤ (n.factorial : ℝ) * (C ^ (m + (n + 1) + 1) / (n.factorial * m.factorial)) := by
          gcongr
          · exact hnorm _
          · exact_mod_cast hfac_le
      _ = C ^ (n + 2) * (C ^ m / m.factorial) := by
          rw [hexp, pow_add]
          field_simp
  have hdom : Summable fun m : ℕ ↦ C ^ (n + 2) * (C ^ m / m.factorial) :=
    (Real.summable_pow_div_factorial C).mul_left (C ^ (n + 2))
  have hsub : Summable fun m : ℕ ↦
      ‖(n.factorial : ℂ) * (a (m + (n + 1)) / (m + (n + 1)).factorial)‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm_le hdom
  have hnorm_tail : ‖divOneSubSeq a n‖ ≤ C ^ (n + 2) * Real.exp C := by
    rw [divOneSubSeq_def, htail, mul_neg, norm_neg, ← tsum_mul_left]
    exact (norm_tsum_le_tsum_norm hsub).trans ((Summable.tsum_le_tsum hterm_le hsub hdom).trans
      (by rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]))
  refine hnorm_tail.trans ?_
  rw [mul_pow]
  exact mul_le_mul
    (calc C ^ (n + 2) ≤ max 1 C ^ (n + 2) := by gcongr; exact le_max_right 1 C
      _ ≤ max 1 C ^ (2 * (n + 1)) := pow_le_pow_right₀ (le_max_left 1 C) (by omega)
      _ = (max 1 C ^ 2) ^ (n + 1) := by rw [pow_mul])
    (le_self_pow₀ (Real.one_le_exp hC.le) (Nat.succ_ne_zero n))
    (Real.exp_pos C).le (by positivity)

/-- **Quotient by `1 - z` at a zero.** If `a` is an E-function with rational coefficients and
`eFun a 1 = 0`, then `divOneSubSeq a` is an E-function. -/
protected theorem IsEFunction.divOneSubSeq {a : ℕ → ℂ} (ha : IsEFunction a)
    (hrat : ∀ n, ∃ q : ℚ, a n = q) (hz : eFun a 1 = 0) :
    IsEFunction (divOneSubSeq a) := by
  choose q hq using hrat
  have hbq (n : ℕ) : divOneSubSeq a n =
      ((n.factorial * ∑ k ∈ Finset.range (n + 1), q k / k.factorial : ℚ) : ℂ) := by
    rw [divOneSubSeq_def]; push_cast
    congr 1; exact Finset.sum_congr rfl fun k _ ↦ by rw [hq k]
  obtain ⟨C, hC, hnorm⟩ := ha.exists_norm_le
  obtain ⟨D, hD, d, hd⟩ := ha.den_le
  refine IsEFunction.of_house_le
    (fun n ↦ by rw [hbq n, ← eq_ratCast (algebraMap ℚ ℂ)]; exact isAlgebraic_algebraMap _)
    ((PowerSeries.isDFinite_one_sub_X_mul_iff (k := algebraicClosure ℚ ℂ)).mp
      (by rw [one_sub_X_mul_ePowerSeries_divOneSubSeq]; exact ha.isDFinite))
    ⟨max 1 C ^ 2 * Real.exp C, by positivity, fun n ↦ ?_⟩ ?_
  · rw [hbq n, house_ratCast, ← Complex.norm_ratCast, ← hbq n]
    exact norm_divOneSubSeq_le hC hnorm hz n
  · refine ⟨D, hD, d, fun n ↦ ⟨(hd n).1, (hd n).2.1, fun m hm ↦ ?_⟩⟩
    rw [divOneSubSeq_def, ← mul_assoc, mul_comm (d n : ℂ), mul_assoc, Finset.mul_sum,
      Finset.mul_sum, ← mem_integralClosure_iff]
    refine sum_mem fun k hk ↦ ?_
    rw [mem_integralClosure_iff]
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    obtain ⟨u, hu⟩ := Nat.factorial_dvd_factorial hkm
    have hkf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hdiv : (m.factorial : ℂ) * ((d n : ℂ) * (a k / k.factorial)) =
        (u : ℂ) * ((d n : ℂ) * a k) := by
      rw [hu, Nat.cast_mul]
      field_simp
    rw [hdiv]
    exact (isIntegral_natCast u).mul ((hd n).2.2 k (hkm.trans hm))

/-- Analytic quotient identity `(1 - z) * eFun (divOneSubSeq a) z = eFun a z`. -/
theorem IsEFunction.one_sub_mul_eFun_divOneSubSeq {a : ℕ → ℂ} (ha : IsEFunction a)
    (hrat : ∀ n, ∃ q : ℚ, a n = q) (hz : eFun a 1 = 0) (z : ℂ) :
    (1 - z) * eFun (divOneSubSeq a) z = eFun a z := by
  have hb : IsEFunction (divOneSubSeq a) := ha.divOneSubSeq hrat hz
  let p : ℕ → ℂ := Pi.single 0 1 - Pi.single 1 1
  have hp : IsEFunction p := (isEFunction_single_zero isAlgebraic_one).sub
    (isEFunction_single 1 isAlgebraic_one)
  have hp_ps : ePowerSeries p = 1 - PowerSeries.X := by
    simp [p, ePowerSeries_single 1 (1 : ℂ)]
  have hmul_seq : hurwitzMul p (divOneSubSeq a) = a := by
    apply ePowerSeries_injective
    rw [ePowerSeries_hurwitzMul, hp_ps, one_sub_X_mul_ePowerSeries_divOneSubSeq]
  have hp_eval : eFun p z = 1 - z := by
    have hadd : eFun p z = eFun (Pi.single 0 1) z + eFun (-Pi.single 1 1) z :=
      (isEFunction_single_zero isAlgebraic_one).eFun_add
        (isEFunction_single 1 isAlgebraic_one).neg z
    simpa [sub_eq_add_neg] using hadd
  rw [← hp_eval, ← hp.eFun_hurwitzMul hb z, hmul_seq]

/-! ### Concrete examples and non-examples -/

private theorem sub_one_eq_hurwitzMul :
    (fun n : ℕ ↦ (n : ℂ) - 1) = hurwitzMul (Pi.single 1 1 - Pi.single 0 1) (fun _ ↦ 1) := by
  ext n
  rw [hurwitzMul_sub_left]
  cases n with
  | zero => simp [hurwitzMul_single_left]
  | succ n => simp [hurwitzMul_single_left]

/-- The sequence `n ↦ (n : ℂ) - 1` evaluates under `eFun` to `(z - 1) * Complex.exp z`. -/
theorem eFun_sub_one (z : ℂ) :
    eFun (fun n ↦ (n : ℂ) - 1) z = (z - 1) * Complex.exp z := by
  have hp1 : IsEFunction (Pi.single 1 1 - Pi.single 0 1) :=
    (isEFunction_single 1 isAlgebraic_one).sub (isEFunction_single_zero isAlgebraic_one)
  have hp1_eval : eFun (Pi.single 1 1 - Pi.single 0 1) z = z - 1 := by
    have h := (isEFunction_single 1 isAlgebraic_one).eFun_add
      (isEFunction_single_zero isAlgebraic_one).neg z
    simpa [sub_eq_add_neg] using h
  rw [sub_one_eq_hurwitzMul, hp1.eFun_hurwitzMul isEFunction_const_one z, hp1_eval, eFun_const_one]

/-- The sequence `n ↦ (n : ℂ) - 1` (representing `(z - 1) * exp z`) is an E-function. -/
theorem isEFunction_sub_one : IsEFunction fun n ↦ (n : ℂ) - 1 := by
  rw [sub_one_eq_hurwitzMul]
  exact ((isEFunction_single 1 isAlgebraic_one).sub
    (isEFunction_single_zero isAlgebraic_one)).hurwitzMul isEFunction_const_one

/-- The factorial sequence `n ↦ (n! : ℂ)` (the normalized E-coefficients of `1 / (1 - z)`) is not an
E-function. -/
theorem not_isEFunction_factorial : ¬IsEFunction fun n ↦ (n.factorial : ℂ) := by
  intro ha
  obtain ⟨C, hC, hnorm⟩ := ha.exists_norm_le
  have hlim := (Real.summable_pow_div_factorial C).tendsto_atTop_zero
  have hge : ∀ n : ℕ, C⁻¹ ≤ C ^ n / n.factorial := by
    intro n
    have h1 : (n.factorial : ℝ) ≤ C ^ (n + 1) := by simpa using hnorm n
    have hnf : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
    rw [inv_eq_one_div, div_le_div_iff₀ hC hnf]
    simpa [pow_succ] using h1
  have hle0 : C⁻¹ ≤ 0 := ge_of_tendsto' hlim hge
  linarith [inv_pos.mpr hC]

/-- The normalized E-coefficient sequence of `exp (z ^ 2)`: `(2k)! / k!` at `n = 2k` and `0` at odd
`n`. -/
noncomputable def expSqSeq (n : ℕ) : ℂ :=
  if Even n then (n.factorial : ℂ) / (n / 2).factorial else 0

/-- At `n = 0`, `expSqSeq 0 = 1`. -/
@[simp]
theorem expSqSeq_zero : expSqSeq 0 = 1 := by
  simp [expSqSeq]

/-- At even indices `2 * k`, `expSqSeq (2 * k) = (2 * k)! / k!`. -/
@[simp]
theorem expSqSeq_two_mul (k : ℕ) :
    expSqSeq (2 * k) = ((2 * k).factorial : ℂ) / k.factorial := by
  simp [expSqSeq]

/-- At odd indices `2 * k + 1`, `expSqSeq (2 * k + 1) = 0`. -/
@[simp]
theorem expSqSeq_two_mul_add_one (k : ℕ) : expSqSeq (2 * k + 1) = 0 := by
  have hne : ¬Even (2 * k + 1) := by simp
  simp [expSqSeq, hne]

/-- `eFun expSqSeq z` evaluates to `Complex.exp (z ^ 2)`. -/
theorem eFun_expSqSeq (z : ℂ) : eFun expSqSeq z = Complex.exp (z ^ 2) := by
  have heven (k : ℕ) :
      expSqSeq (2 * k) * z ^ (2 * k) / (2 * k).factorial = (z ^ 2) ^ k / k.factorial := by
    have hf : ((2 * k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [expSqSeq_two_mul, div_mul_eq_mul_div, div_right_comm, mul_div_cancel_left₀ _ hf, pow_mul]
  have hsum_even : Summable fun k : ℕ ↦
      expSqSeq (2 * k) * z ^ (2 * k) / (2 * k).factorial := by
    simp_rw [heven]
    exact Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖z ^ 2‖) fun k ↦ by simp
  have hsum_odd : Summable fun k : ℕ ↦
      expSqSeq (2 * k + 1) * z ^ (2 * k + 1) / (2 * k + 1).factorial := by
    simp only [expSqSeq_two_mul_add_one, zero_mul, zero_div]
    exact summable_zero
  rw [eFun_def, ← tsum_even_add_odd hsum_even hsum_odd]
  simp_rw [heven, expSqSeq_two_mul_add_one, zero_mul, zero_div, tsum_zero, add_zero]
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]

/-- The normalized E-coefficient sequence `expSqSeq` of `exp (z ^ 2)` is not an E-function. -/
theorem not_isEFunction_expSqSeq : ¬IsEFunction expSqSeq := by
  intro ha
  obtain ⟨C, _, hnorm⟩ := ha.exists_norm_le
  set B : ℝ := max 1 C ^ 3
  obtain ⟨m, hm⟩ := exists_nat_gt B
  set k : ℕ := m + 1
  have hk : B < k := hm.trans (by exact_mod_cast Nat.lt_succ_self m)
  have h2k : ((k + 1 : ℕ) : ℝ) ^ k ≤ ‖expSqSeq (2 * k)‖ := by
    have hle : k.factorial * (k + 1) ^ k ≤ (2 * k).factorial := by
      simpa [two_mul] using @Nat.factorial_mul_pow_le_factorial k k
    obtain ⟨q, hq⟩ := Nat.factorial_dvd_factorial (Nat.le_mul_of_pos_left k two_pos)
    have hkq : (k + 1) ^ k ≤ q := Nat.le_of_mul_le_mul_left (hle.trans_eq hq) (Nat.factorial_pos k)
    have hval : expSqSeq (2 * k) = (q : ℂ) := by
      have hkf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
      rw [expSqSeq_two_mul, hq, Nat.cast_mul, mul_div_cancel_left₀ _ hkf]
    rw [hval, Complex.norm_natCast]
    exact_mod_cast hkq
  have hupper : ‖expSqSeq (2 * k)‖ ≤ B ^ k := by
    refine (hnorm (2 * k)).trans ?_
    calc C ^ (2 * k + 1)
        ≤ max 1 C ^ (2 * k + 1) :=
          pow_le_pow_left₀ (by simpa using (norm_nonneg _).trans (hnorm 0)) (le_max_right 1 C) _
      _ ≤ max 1 C ^ (3 * k) := pow_le_pow_right₀ (le_max_left 1 C) (by omega)
      _ = B ^ k := by rw [pow_mul]
  have hlt : B ^ k < ((k + 1 : ℕ) : ℝ) ^ k :=
    pow_lt_pow_left₀ (hk.trans (by exact_mod_cast Nat.lt_succ_self k))
      (by positivity) (Nat.succ_ne_zero m)
  linarith

end TauCeti
