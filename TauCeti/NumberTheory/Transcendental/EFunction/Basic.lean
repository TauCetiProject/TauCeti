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
public import TauCeti.RingTheory.PowerSeries.DFinite.Borel
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import TauCeti.Algebra.Order.GroupWithZero.Pow
import TauCeti.FieldTheory.Normal.Closure
import TauCeti.FieldTheory.Normal.Embeddings

/-!
# Siegel's E-functions

Siegel introduced E-functions in 1929 to generalize the Lindemann–Weierstrass theorem and prove
the transcendence and algebraic independence over `algebraicClosure ℚ ℂ` of values at algebraic
points of entire solutions to linear differential equations with rational function coefficients
over `algebraicClosure ℚ ℂ` — including exponential, Bessel, and confluent hypergeometric
functions (the Siegel–Shidlovskii theorem and its refinements by André and Beukers).

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
(`TauCeti.IsEFunction.exists_numberField`) and hence in a single finite Galois number field over
`ℚ` (`TauCeti.IsEFunction.exists_isGalois_numberField`), `eFun a` is an entire analytic function on
`ℂ`, and the class of E-functions is closed under sums, differences, algebraic scalar multiples,
binary and finite Hurwitz products (analytic multiplication), forward shifts (analytic
differentiation), algebraic rescaling `z ↦ α z`, coefficientwise ring endomorphisms of `ℂ`,
intrinsic Galois conjugation by `Gal(algebraicClosure ℚ ℂ/ℚ)`, and `ℚ`-embeddings of algebraic
coefficient fields.

When an E-function `a` vanishes at `1` (`eFun a 1 = 0`), the general quotient sequence
`divOneSubSeq a` defined in `TauCeti.NumberTheory.Transcendental.EFunction.Series` satisfies the
analytic quotient identity `(1 - z) * eFun (divOneSubSeq a) z = eFun a z`
(`TauCeti.IsEFunction.one_sub_mul_eFun_divOneSubSeq`). When `a` also has rational coefficients,
`divOneSubSeq a` is itself an E-function (`TauCeti.IsEFunction.divOneSubSeq`). For an arbitrary
nonzero E-function `a`, forming the Hurwitz product of all Galois conjugates over a finite Galois
coefficient field produces a nonzero rational-coefficient E-function multiple
(`TauCeti.IsEFunction.fold_hurwitzMul_gal`, `TauCeti.exists_rat_fold_hurwitzMul_gal`,
`TauCeti.IsEFunction.exists_rat_isEFunction_hurwitzMul`). When `eFun a 1 = 0`, the
`(1 - z)`-quotient of this Galois-conjugate product is again an E-function
(`TauCeti.IsEFunction.divOneSubSeq_fold_hurwitzMul_gal`); combined with algebraic rescaling
(`TauCeti.IsEFunction.rescale`), this reduces vanishing at nonzero algebraic zeros to the
rational-coefficient base case at `1` in Beukers's proof of the refined Siegel–Shidlovskii theorem.

## Main definitions

* `TauCeti.IsEFunction a`: the E-function predicate on a coefficient sequence `a : ℕ → ℂ`.

## Main results

* `TauCeti.IsEFunction.exists_numberField`, `TauCeti.IsEFunction.exists_isGalois_numberField`: all
  coefficients of an E-function lie in a common (finite Galois) number field.
* `TauCeti.IsEFunction.add`, `TauCeti.IsEFunction.sub`, `TauCeti.IsEFunction.hurwitzMul`,
  `TauCeti.IsEFunction.fold_hurwitzMul`, `TauCeti.IsEFunction.shift`,
  `TauCeti.IsEFunction.comp_add_right`, `TauCeti.IsEFunction.rescale`,
  `TauCeti.IsEFunction.comp_ringHom`, `TauCeti.IsEFunction.galoisConj`,
  `TauCeti.IsEFunction.comp_algHom`: closure of E-functions.
* `TauCeti.IsEFunction.one_sub_mul_eFun_divOneSubSeq`, `TauCeti.IsEFunction.divOneSubSeq`,
  `TauCeti.IsEFunction.fold_hurwitzMul_gal`, `TauCeti.exists_rat_fold_hurwitzMul_gal`,
  `TauCeti.IsEFunction.divOneSubSeq_fold_hurwitzMul_gal`,
  `TauCeti.IsEFunction.exists_rat_isEFunction_hurwitzMul`: quotient by `1 - z` at `1` and
  rational-coefficient Galois-conjugate Hurwitz products.
* `TauCeti.isEFunction_const_one`, `TauCeti.isEFunction_natCast_sub_one`,
  `TauCeti.not_isEFunction_factorial`, `TauCeti.not_exists_isEFunction_eFun_eq_exp_sq`: concrete
  examples and non-examples (`exp z` and `(z - 1) exp z` are E-functions; `1 / (1 - z)` and
  `exp (z ^ 2)` are not).

## References

* C. L. Siegel, *Über einige Anwendungen diophantischer Approximationen*, Abh. Preuß. Akad. Wiss.,
  Phys.-Math. Kl. 1929, Nr. 1.
* F. Beukers, *A refined version of the Siegel–Shidlovskii theorem*, Ann. of Math. (2) **163**
  (2006), 369–379, §1–2, Corollary 2.2, Lemma 2.4, Theorem 2.5.
* F. Beukers, *E-functions and G-functions*, lecture notes, Arizona Winter School, 2008, §3.1–3.4,
  Proposition 3.2.1, Corollary 3.4.2.
* S. Fischler and T. Rivoal, *On Siegel's problem for E-functions*, Math. Z. **301** (2022),
  1429–1453 (arXiv:1910.06817), Definition 1.
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
  /-- Every normalized Taylor coefficient `aₙ` is algebraic over `ℚ`. -/
  isAlgebraic : ∀ n, IsAlgebraic ℚ (a n)
  /-- The factorial-divided formal power series `ePowerSeries a = ∑ (aₙ / n!) Xⁿ` satisfies a
  nonzero linear differential equation with polynomial coefficients over
  `algebraicClosure ℚ ℂ`. -/
  isDFinite : PowerSeries.IsDFinite (algebraicClosure ℚ ℂ) (ePowerSeries a)
  /-- Geometric house bound: every complex root of `minpoly ℚ (aₙ)` has modulus at most
  `C ^ (n + 1)` for a uniform constant `C > 0` (using exponent `n + 1` so `n = 0` is included
  without an extra multiplicative factor). -/
  size_le : ∃ C : ℝ, 0 < C ∧ ∀ n, ∀ z ∈ (minpoly ℚ (a n)).aroots ℂ, ‖z‖ ≤ C ^ (n + 1)
  /-- Geometric common-denominator bound: positive integers `dₙ ≤ D ^ (n + 1)` make `dₙ * aₘ`
  an algebraic integer simultaneously for all `m ≤ n`. -/
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

/-- All coefficients of an E-function lie in a single finite Galois number field inside `ℂ`. -/
theorem exists_isGalois_numberField {a : ℕ → ℂ} (ha : IsEFunction a) :
    ∃ (L : IntermediateField ℚ ℂ) (_ : NumberField L) (_ : IsGalois ℚ L), ∀ n, a n ∈ L := by
  obtain ⟨K, _, hK⟩ := ha.exists_numberField
  let L : IntermediateField ℚ ℂ := IntermediateField.normalClosure ℚ K ℂ
  exact ⟨L, {}, inferInstance, fun n ↦ IntermediateField.le_normalClosure K (hK n)⟩

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

/-- For an E-function `a`, `eFun a` has complex derivative `eFun (fun n ↦ a (n + 1)) z` at every
`z : ℂ`. -/
theorem hasDerivAt_eFun {a : ℕ → ℂ} (ha : IsEFunction a) (z : ℂ) :
    HasDerivAt (eFun a) (eFun (fun n ↦ a (n + 1)) z) z := by
  obtain ⟨_, _, hnorm⟩ := ha.exists_norm_le
  exact hasDerivAt_eFun_of_norm_le hnorm z

/-- Complex differentiation of `eFun a` shifts the coefficients of an E-function by `1`. -/
theorem deriv_eFun {a : ℕ → ℂ} (ha : IsEFunction a) :
    deriv (eFun a) = eFun fun n ↦ a (n + 1) := by
  obtain ⟨_, _, hnorm⟩ := ha.exists_norm_le
  exact deriv_eFun_of_norm_le hnorm

/-- The `m`-th complex derivative of `eFun a` shifts the coefficients of an E-function by `m`. -/
theorem iteratedDeriv_eFun {a : ℕ → ℂ} (ha : IsEFunction a) (m : ℕ) :
    iteratedDeriv m (eFun a) = eFun fun n ↦ a (n + m) := by
  obtain ⟨_, _, hnorm⟩ := ha.exists_norm_le
  exact iteratedDeriv_eFun_of_norm_le hnorm m

/-- Applying the `m`-th derivative of `eFun a` at `0` recovers `a m`. -/
theorem iteratedDeriv_eFun_apply_zero {a : ℕ → ℂ} (ha : IsEFunction a) (m : ℕ) :
    iteratedDeriv m (eFun a) 0 = a m := by
  rw [ha.iteratedDeriv_eFun m, eFun_apply_zero, zero_add]

/-- For two E-functions `a` and `b`, `eFun (a + b) z = eFun a z + eFun b z`. -/
theorem eFun_add {a b : ℕ → ℂ} (ha : IsEFunction a) (hb : IsEFunction b) (z : ℂ) :
    eFun (a + b) z = eFun a z + eFun b z := by
  obtain ⟨_, _, hna⟩ := ha.exists_norm_le
  obtain ⟨_, _, hnb⟩ := hb.exists_norm_le
  exact eFun_add_of_norm_le hna hnb z

/-- For two E-functions `a` and `b`, `eFun (a - b) z = eFun a z - eFun b z`. -/
theorem eFun_sub {a b : ℕ → ℂ} (ha : IsEFunction a) (hb : IsEFunction b) (z : ℂ) :
    eFun (a - b) z = eFun a z - eFun b z := by
  obtain ⟨_, _, hna⟩ := ha.exists_norm_le
  obtain ⟨_, _, hnb⟩ := hb.exists_norm_le
  exact eFun_sub_of_norm_le hna hnb z

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
  refine of_house_le (fun n ↦ (ha.isAlgebraic n).add (hb.isAlgebraic n))
    (by rw [ePowerSeries_add]; exact ha.isDFinite.add hb.isDFinite) ?_ ?_
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
  refine of_house_le (fun n ↦ hc.mul (ha.isAlgebraic n))
    (by rw [ePowerSeries_smul]; exact ha.isDFinite.smul c) ?_ ?_
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
  have hterm_alg (k : ℕ) : IsAlgebraic ℚ ((n.choose k : ℂ) * (a k * b (n - k))) :=
    (isAlgebraic_natCast _).mul ((halg_a k).mul (halg_b (n - k)))
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
        have hab : IsAlgebraic ℚ (a k * b (n - k)) := (halg_a k).mul (halg_b (n - k))
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
    refine sum_mem fun k _ ↦ mem_algebraicClosure_iff.mpr ?_
    exact ((ha.isAlgebraic k).mul (hb.isAlgebraic (n - k))).nsmul _
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

/-- Finite Hurwitz products of E-functions are E-functions. -/
theorem fold_hurwitzMul {ι : Type*} (s : Finset ι) {f : ι → ℕ → ℂ}
    (hf : ∀ i ∈ s, IsEFunction (f i)) :
    IsEFunction (s.fold TauCeti.hurwitzMul (Pi.single 0 1) f) := by
  induction s using Finset.cons_induction with
  | empty => simpa using isEFunction_single_zero isAlgebraic_one
  | cons i s hi ih =>
    rw [Finset.fold_cons hi]
    exact (hf i (Finset.mem_cons_self i s)).hurwitzMul
      (ih fun j hj ↦ hf j (Finset.mem_cons_of_mem hj))

/-- Evaluating `eFun` on a finite Hurwitz product of E-functions gives the pointwise product of
their `eFun` evaluations. -/
theorem eFun_fold_hurwitzMul {ι : Type*} (s : Finset ι) {f : ι → ℕ → ℂ}
    (hf : ∀ i ∈ s, IsEFunction (f i)) (z : ℂ) :
    eFun (s.fold TauCeti.hurwitzMul (Pi.single 0 1) f) z = ∏ i ∈ s, eFun (f i) z := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    have hs : ∀ j ∈ s, IsEFunction (f j) := fun j hj ↦ hf j (Finset.mem_cons_of_mem hj)
    rw [Finset.fold_cons hi, Finset.prod_cons,
      (hf i (Finset.mem_cons_self i s)).eFun_hurwitzMul (fold_hurwitzMul s hs) z, ih hs]

/-- **Derivatives of E-functions are E-functions.** Shifting the coefficient sequence by `1`
preserves `IsEFunction`. -/
protected theorem shift {a : ℕ → ℂ} (ha : IsEFunction a) :
    IsEFunction fun n ↦ a (n + 1) := by
  obtain ⟨C, hC, hha⟩ := ha.exists_house_le
  obtain ⟨D, hD, d, hd⟩ := ha.den_le
  refine of_house_le (fun n ↦ ha.isAlgebraic (n + 1))
    (by rw [← derivative_ePowerSeries]; exact ha.isDFinite.derivative) ?_ ?_
  · exact ⟨max 1 C ^ 2, by positivity,
      fun n ↦ (hha (n + 1)).trans (pow_le_max_one_pow_pow hC.le (by omega))⟩
  · refine ⟨max 1 D ^ 2, by positivity, fun n ↦ d (n + 1), fun n ↦ ⟨(hd (n + 1)).1, ?_, ?_⟩⟩
    · exact ((hd (n + 1)).2.1).trans (pow_le_max_one_pow_pow hD.le (by omega))
    · exact fun m hm ↦ (hd (n + 1)).2.2 (m + 1) (Nat.succ_le_succ hm)

/-- **Iterated derivatives of E-functions are E-functions.** Shifting the coefficient sequence by
`m` preserves `IsEFunction`. -/
protected theorem comp_add_right {a : ℕ → ℂ} (ha : IsEFunction a) (m : ℕ) :
    IsEFunction fun n ↦ a (n + m) := by
  induction m generalizing a with
  | zero => simpa using ha
  | succ m ih =>
    simpa only [Nat.add_assoc, Nat.add_comm 1 m] using ih ha.shift

/-- Rescaling the variable by an algebraic number `α` (`aₙ ↦ αⁿ aₙ`) preserves `IsEFunction`. -/
protected theorem rescale {α : ℂ} (hα : IsAlgebraic ℚ α) {a : ℕ → ℂ} (ha : IsEFunction a) :
    IsEFunction fun n ↦ α ^ n * a n := by
  obtain ⟨C, hC, hha⟩ := ha.exists_house_le
  obtain ⟨D, hD, d, hd⟩ := ha.den_le
  let α₀ : algebraicClosure ℚ ℂ := ⟨α, mem_algebraicClosure_iff.mpr hα⟩
  refine of_house_le (fun n ↦ (hα.pow n).mul (ha.isAlgebraic n))
    (by rw [← rescale_ePowerSeries]; exact ha.isDFinite.rescale α₀) ?_ ?_
  · set B := max 1 (house α) * C
    refine ⟨B, by positivity, fun n ↦ ?_⟩
    have hα_le : house α ^ n ≤ max 1 (house α) ^ (n + 1) :=
      pow_le_max_one_pow (house_nonneg α) (Nat.le_succ n)
    calc house (α ^ n * a n)
        ≤ house (α ^ n) * house (a n) := house_mul_le (hα.pow n) (ha.isAlgebraic n)
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
    { toFun := fun x ↦ ⟨σ x, (map_mem_algebraicClosure_iff σ.toRatAlgHom).mpr x.property⟩
      map_one' := Subtype.ext σ.map_one
      map_mul' := fun x y ↦ Subtype.ext (σ.map_mul x y)
      map_zero' := Subtype.ext σ.map_zero
      map_add' := fun x y ↦ Subtype.ext (σ.map_add x y) }
  refine of_house_le (fun n ↦ (ha.isAlgebraic n).algHom σ.toRatAlgHom)
    (by rw [← map_ePowerSeries]; exact ha.isDFinite.map σ₀ σ fun _ ↦ rfl)
    ⟨C, hC, fun n ↦ by simpa [Function.comp_apply] using hha n⟩
    ⟨D, hD, d, fun n ↦ ⟨(hd n).1, (hd n).2.1, fun m hm ↦ ?_⟩⟩
  have himg : (d n : ℂ) * σ (a m) = σ ((d n : ℂ) * a m) := by simp
  rw [Function.comp_apply, himg]
  exact ((hd n).2.2 m hm).map σ.toIntAlgHom

/-- **Intrinsic Galois conjugation of E-functions.** Any Galois automorphism
`τ ∈ Gal(algebraicClosure ℚ ℂ/ℚ)` acts directly on the algebraic coefficients of an E-function `a`
(without extending `τ` to an endomorphism of `ℂ`) and produces an E-function. -/
protected theorem galoisConj {a : ℕ → ℂ} (ha : IsEFunction a)
    (τ : Gal(algebraicClosure ℚ ℂ/ℚ)) :
    IsEFunction fun n ↦
      (τ ⟨a n, mem_algebraicClosure_iff.mpr (ha.isAlgebraic n)⟩ : ℂ) := by
  obtain ⟨C, hC, hha⟩ := ha.exists_house_le
  obtain ⟨D, hD, d, hd⟩ := ha.den_le
  set a₀ : ℕ → algebraicClosure ℚ ℂ := fun n ↦
    ⟨a n, mem_algebraicClosure_iff.mpr (ha.isAlgebraic n)⟩
  set ι : algebraicClosure ℚ ℂ →+* ℂ := algebraMap (algebraicClosure ℚ ℂ) ℂ
  have hι_a₀ : ι ∘ a₀ = a := by
    ext n; simp [ι, a₀, IntermediateField.algebraMap_apply]
  have hdf₀ : PowerSeries.IsDFinite (algebraicClosure ℚ ℂ) (ePowerSeries a₀) := by
    refine (PowerSeries.isDFinite_map_iff (RingEquiv.refl (algebraicClosure ℚ ℂ)) ι.injective
      (fun _ ↦ by simp [ι, IntermediateField.algebraMap_apply])).mp ?_
    rw [map_ePowerSeries, hι_a₀]
    exact ha.isDFinite
  refine of_house_le
    (fun n ↦ mem_algebraicClosure_iff.mp (τ (a₀ n)).property)
    (?_)
    ⟨C, hC, fun n ↦ ?_⟩
    ⟨D, hD, d, fun n ↦ ?_⟩
  · have hcomp : (fun n ↦ (τ (a₀ n) : ℂ)) = (ι.comp τ.toRingHom) ∘ a₀ := by
      ext n; simp [ι, IntermediateField.algebraMap_apply]
    rw [hcomp, ← map_ePowerSeries]
    exact hdf₀.map τ.toRingHom (ι.comp τ.toRingHom)
      fun _ ↦ by simp [ι, IntermediateField.algebraMap_apply]
  · calc house (ι (τ (a₀ n)))
        = house (τ.toRingHom (a₀ n)) := house_map ι _
      _ = house (a₀ n) := house_map τ.toRingHom (a₀ n)
      _ = house (ι (a₀ n)) := (house_map ι (a₀ n)).symm
      _ ≤ C ^ (n + 1) := hha n
  · obtain ⟨hd1, hd_le, hd_int⟩ := hd n
    refine ⟨hd1, hd_le, fun m hm ↦ ?_⟩
    have hint₀ : IsIntegral ℤ ((d n : algebraicClosure ℚ ℂ) * a₀ m) := by
      rw [← isIntegral_algHom_iff ι.toIntAlgHom ι.injective]
      simpa [ι, a₀, IntermediateField.algebraMap_apply] using hd_int m hm
    have hint_τ : IsIntegral ℤ (τ ((d n : algebraicClosure ℚ ℂ) * a₀ m)) :=
      hint₀.map (τ.toAlgHom.restrictScalars ℤ)
    simpa only [map_mul, map_natCast, RingHom.toIntAlgHom_apply, ι, a₀,
      IntermediateField.algebraMap_apply] using hint_τ.map ι.toIntAlgHom

/-- If `a : ℕ → K` takes values in an algebraic extension `K / ℚ` embedded in `ℂ` and
`algebraMap K ℂ ∘ a` is an E-function, then `φ ∘ a` is an E-function for every `ℚ`-embedding
`φ : K →ₐ[ℚ] ℂ`. -/
protected theorem comp_algHom {K : Type*} [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    [Algebra K ℂ] [IsScalarTower ℚ K ℂ] {a : ℕ → K}
    (ha : IsEFunction (algebraMap K ℂ ∘ a)) (φ : K →ₐ[ℚ] ℂ) :
    IsEFunction (φ ∘ a) := by
  have hι (x : K) : IsScalarTower.toAlgHom ℚ K ℂ x ∈ (algebraicClosure ℚ ℂ).toSubalgebra :=
    mem_algebraicClosure_iff.mpr
      ((Algebra.IsAlgebraic.isAlgebraic x).algHom (IsScalarTower.toAlgHom ℚ K ℂ))
  have hφ (x : K) : φ x ∈ (algebraicClosure ℚ ℂ).toSubalgebra :=
    mem_algebraicClosure_iff.mpr ((Algebra.IsAlgebraic.isAlgebraic x).algHom φ)
  let ι₀ : K →ₐ[ℚ] algebraicClosure ℚ ℂ :=
    (IsScalarTower.toAlgHom ℚ K ℂ).codRestrict (algebraicClosure ℚ ℂ).toSubalgebra hι
  let φ₀ : K →ₐ[ℚ] algebraicClosure ℚ ℂ :=
    φ.codRestrict (algebraicClosure ℚ ℂ).toSubalgebra hφ
  obtain ⟨τ, hτ₀⟩ := MulAction.exists_smul_eq Gal(algebraicClosure ℚ ℂ/ℚ) ι₀ φ₀
  have hτ : (fun n ↦ (τ ⟨(algebraMap K ℂ ∘ a) n,
        mem_algebraicClosure_iff.mpr (ha.isAlgebraic n)⟩ : ℂ)) = φ ∘ a := by
    ext n
    have hsub : (⟨(algebraMap K ℂ ∘ a) n, mem_algebraicClosure_iff.mpr (ha.isAlgebraic n)⟩ :
        algebraicClosure ℚ ℂ) = ι₀ (a n) :=
      Subtype.ext (AlgHom.coe_codRestrict (IsScalarTower.toAlgHom ℚ K ℂ)
        (algebraicClosure ℚ ℂ).toSubalgebra hι (a n)).symm
    rw [hsub, ← AlgEquiv.smul_algHom_apply, hτ₀]
    exact AlgHom.coe_codRestrict φ (algebraicClosure ℚ ℂ).toSubalgebra hφ (a n)
  exact hτ ▸ ha.galoisConj τ

end IsEFunction

/-- The sequence `n ↦ α ^ n` (representing `z ↦ exp (α z)`) is an E-function for algebraic `α`. -/
theorem isEFunction_pow {α : ℂ} (hα : IsAlgebraic ℚ α) : IsEFunction (α ^ ·) := by
  simpa using isEFunction_const_one.rescale hα

/-! ### Division by `1 - z` at a zero at `1` -/

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
  obtain ⟨C, _, hnorm⟩ := ha.exists_norm_le
  obtain ⟨D, hD, d, hd⟩ := ha.den_le
  refine IsEFunction.of_house_le
    (fun n ↦ by rw [hbq n, ← eq_ratCast (algebraMap ℚ ℂ)]; exact isAlgebraic_algebraMap _)
    ((PowerSeries.isDFinite_one_sub_X_mul_iff (k := algebraicClosure ℚ ℂ)).mp
      (by rw [one_sub_X_mul_ePowerSeries_divOneSubSeq]; exact ha.isDFinite))
    ⟨max 1 C ^ 2 * Real.exp C, by positivity, fun n ↦ ?_⟩ ?_
  · rw [hbq n, house_ratCast, ← Complex.norm_ratCast, ← hbq n]
    exact norm_divOneSubSeq_le hnorm hz n
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

/-- For an E-function `a` vanishing at `1` (`eFun a 1 = 0`), the quotient sequence `divOneSubSeq a`
satisfies `(1 - z) * eFun (divOneSubSeq a) z = eFun a z` for all `z : ℂ`. -/
theorem IsEFunction.one_sub_mul_eFun_divOneSubSeq {a : ℕ → ℂ} (ha : IsEFunction a)
    (hz : eFun a 1 = 0) (z : ℂ) :
    (1 - z) * eFun (divOneSubSeq a) z = eFun a z := by
  obtain ⟨_, _, hnorm⟩ := ha.exists_norm_le
  exact one_sub_mul_eFun_divOneSubSeq_of_norm_le hnorm hz z

/-! ### Galois-conjugate Hurwitz products -/

/-- For a finite Galois extension `K / ℚ` embedded in `ℂ`, every coefficient of the Galois-orbit
Hurwitz product of `a : ℕ → K` is rational. -/
theorem exists_rat_fold_hurwitzMul_gal {K : Type*} [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K] [Algebra K ℂ] [IsScalarTower ℚ K ℂ]
    (a : ℕ → K) (n : ℕ) :
    ∃ q : ℚ,
      (Finset.univ : Finset Gal(K/ℚ)).fold hurwitzMul (Pi.single 0 1)
        (fun σ ↦ algebraMap K ℂ ∘ (σ • a)) n = q := by
  obtain ⟨q, hq⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := ℚ) (E := K) _).mpr fun τ ↦
    congrFun (smul_fold_hurwitzMul_univ τ a) n
  refine ⟨q, ?_⟩
  rw [← congrFun (comp_fold_hurwitzMul (algebraMap K ℂ) Finset.univ fun σ : Gal(K/ℚ) ↦ σ • a) n,
    Function.comp_apply, ← hq, ← IsScalarTower.algebraMap_apply ℚ K ℂ, eq_ratCast]

namespace IsEFunction

/-- **Galois-conjugate Hurwitz product of an E-function.** For a finite Galois extension `K / ℚ`
embedded in `ℂ` and `a : ℕ → K` defining an E-function, the Hurwitz product of all `Gal(K/ℚ)`
conjugates of `a` is an E-function. -/
theorem fold_hurwitzMul_gal {K : Type*} [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K] [Algebra K ℂ] [IsScalarTower ℚ K ℂ]
    {a : ℕ → K} (ha : IsEFunction (algebraMap K ℂ ∘ a)) :
    IsEFunction ((Finset.univ : Finset Gal(K/ℚ)).fold TauCeti.hurwitzMul (Pi.single 0 1)
      fun σ ↦ algebraMap K ℂ ∘ (σ • a)) :=
  fold_hurwitzMul Finset.univ fun σ _ ↦
    ha.comp_algHom ((IsScalarTower.toAlgHom ℚ K ℂ).comp σ.toAlgHom)

/-- Evaluating `eFun` on the Galois-conjugate Hurwitz product over `Gal(K/ℚ)` gives the product of
the `eFun` evaluations of all conjugates. -/
theorem eFun_fold_hurwitzMul_gal {K : Type*} [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K] [Algebra K ℂ] [IsScalarTower ℚ K ℂ]
    {a : ℕ → K} (ha : IsEFunction (algebraMap K ℂ ∘ a)) (z : ℂ) :
    eFun ((Finset.univ : Finset Gal(K/ℚ)).fold TauCeti.hurwitzMul (Pi.single 0 1)
      fun σ ↦ algebraMap K ℂ ∘ (σ • a)) z =
      ∏ σ : Gal(K/ℚ), eFun (algebraMap K ℂ ∘ (σ • a)) z :=
  eFun_fold_hurwitzMul Finset.univ
    (fun σ _ ↦ ha.comp_algHom ((IsScalarTower.toAlgHom ℚ K ℂ).comp σ.toAlgHom)) z

/-- When an E-function `algebraMap K ℂ ∘ a` over a finite Galois extension `K / ℚ` vanishes at `1`,
the `(1 - z)`-quotient `divOneSubSeq` of its Galois-conjugate Hurwitz product is an E-function. -/
theorem divOneSubSeq_fold_hurwitzMul_gal {K : Type*} [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K] [Algebra K ℂ] [IsScalarTower ℚ K ℂ]
    {a : ℕ → K} (ha : IsEFunction (algebraMap K ℂ ∘ a))
    (hz : eFun (algebraMap K ℂ ∘ a) 1 = 0) :
    IsEFunction (TauCeti.divOneSubSeq
      ((Finset.univ : Finset Gal(K/ℚ)).fold TauCeti.hurwitzMul (Pi.single 0 1)
        fun σ ↦ algebraMap K ℂ ∘ (σ • a))) := by
  refine ha.fold_hurwitzMul_gal.divOneSubSeq (exists_rat_fold_hurwitzMul_gal a) ?_
  rw [ha.eFun_fold_hurwitzMul_gal 1]
  exact Finset.prod_eq_zero (Finset.mem_univ (1 : Gal(K/ℚ))) (by simpa using hz)

/-- **Nonzero rational-coefficient Galois-conjugate multiple of an E-function.** Every nonzero
E-function `a` admits an E-function cofactor `c` (the Hurwitz product of the nontrivial Galois
conjugates of `a` over a finite Galois coefficient field) such that `hurwitzMul a c` is a nonzero
E-function with rational coefficients. -/
theorem exists_rat_isEFunction_hurwitzMul {a : ℕ → ℂ} (ha : IsEFunction a) (ha0 : a ≠ 0) :
    ∃ c : ℕ → ℂ, IsEFunction c ∧ IsEFunction (TauCeti.hurwitzMul a c) ∧
      TauCeti.hurwitzMul a c ≠ 0 ∧ ∀ n, ∃ q : ℚ, TauCeti.hurwitzMul a c n = q := by
  classical
  obtain ⟨L, _, _, hL⟩ := ha.exists_isGalois_numberField
  let a₀ : ℕ → L := fun n ↦ ⟨a n, hL n⟩
  have ha₀_eq : algebraMap L ℂ ∘ a₀ = a := by
    ext n; simp [a₀, IntermediateField.algebraMap_apply]
  have ha₀ : IsEFunction (algebraMap L ℂ ∘ a₀) := ha₀_eq.symm ▸ ha
  have ha₀_ne : a₀ ≠ 0 := fun h0 ↦ ha0 (by simp [← ha₀_eq, h0])
  let g : Gal(L/ℚ) → ℕ → ℂ := fun σ ↦ algebraMap L ℂ ∘ (σ • a₀)
  let b : ℕ → ℂ := (Finset.univ : Finset Gal(L/ℚ)).fold TauCeti.hurwitzMul (Pi.single 0 1) g
  let c : ℕ → ℂ :=
    ((Finset.univ : Finset Gal(L/ℚ)).erase 1).fold TauCeti.hurwitzMul (Pi.single 0 1) g
  have hbc : b = TauCeti.hurwitzMul a c := by
    have hg1 : g 1 = a := by simp [g, one_smul, ha₀_eq]
    calc b = (insert (1 : Gal(L/ℚ)) (Finset.univ.erase 1)).fold
              TauCeti.hurwitzMul (Pi.single 0 1) g := by
            rw [Finset.insert_erase (Finset.mem_univ _)]
      _ = TauCeti.hurwitzMul (g 1) c := Finset.fold_insert (Finset.notMem_erase _ _)
      _ = TauCeti.hurwitzMul a c := by rw [hg1]
  have hb_ne : b ≠ 0 := by
    intro hb0
    have hb_map : b = algebraMap L ℂ ∘
        (Finset.univ : Finset Gal(L/ℚ)).fold TauCeti.hurwitzMul (Pi.single 0 1)
          (fun σ ↦ σ • a₀) :=
      (comp_fold_hurwitzMul (algebraMap L ℂ) Finset.univ fun σ : Gal(L/ℚ) ↦ σ • a₀).symm
    have hfold0 : ((Finset.univ : Finset Gal(L/ℚ)).fold TauCeti.hurwitzMul (Pi.single 0 1)
        fun σ ↦ σ • a₀) = 0 :=
      funext fun n ↦ (algebraMap L ℂ).injective (by simpa [hb_map] using congrFun hb0 n)
    exact ha₀_ne (fold_hurwitzMul_smul_univ_eq_zero_iff.mp hfold0)
  refine ⟨c,
    fold_hurwitzMul _ fun σ _ ↦ ha₀.comp_algHom ((IsScalarTower.toAlgHom ℚ L ℂ).comp σ.toAlgHom),
    hbc ▸ ha₀.fold_hurwitzMul_gal, hbc ▸ hb_ne, hbc ▸ exists_rat_fold_hurwitzMul_gal a₀⟩

end IsEFunction

/-! ### Concrete examples and non-examples -/

private theorem natCast_sub_one_eq_hurwitzMul :
    (fun n : ℕ ↦ (n : ℂ) - 1) = hurwitzMul (Pi.single 1 1 - Pi.single 0 1) (fun _ ↦ 1) := by
  ext n
  rw [hurwitzMul_sub_left]
  cases n with
  | zero => simp
  | succ n => simp [hurwitzMul_single_left]

/-- The sequence `n ↦ (n : ℂ) - 1` evaluates under `eFun` to `(z - 1) * Complex.exp z`. -/
theorem eFun_natCast_sub_one (z : ℂ) :
    eFun (fun n ↦ (n : ℂ) - 1) z = (z - 1) * Complex.exp z := by
  have hp1 : IsEFunction (Pi.single 1 (1 : ℂ) - Pi.single 0 1) :=
    (isEFunction_single 1 isAlgebraic_one).sub (isEFunction_single_zero isAlgebraic_one)
  have hp1_eval : eFun (Pi.single 1 (1 : ℂ) - Pi.single 0 1) z = z - 1 := by
    simpa using (isEFunction_single 1 isAlgebraic_one).eFun_sub
      (isEFunction_single_zero isAlgebraic_one) z
  rw [natCast_sub_one_eq_hurwitzMul, hp1.eFun_hurwitzMul isEFunction_const_one z, hp1_eval,
    eFun_const_one]

/-- The sequence `n ↦ (n : ℂ) - 1` (representing `(z - 1) * exp z`) is an E-function. -/
theorem isEFunction_natCast_sub_one : IsEFunction fun n ↦ (n : ℂ) - 1 := by
  rw [natCast_sub_one_eq_hurwitzMul]
  exact ((isEFunction_single 1 isAlgebraic_one).sub
    (isEFunction_single_zero isAlgebraic_one)).hurwitzMul isEFunction_const_one

/-- The factorial sequence `n ↦ (n! : ℂ)` (the normalized E-coefficients of `1 / (1 - z)`) is not an
E-function. -/
theorem not_isEFunction_factorial : ¬IsEFunction fun n ↦ (n.factorial : ℂ) := by
  intro ha
  obtain ⟨C, _, hnorm⟩ := ha.exists_norm_le
  obtain ⟨n, hn⟩ := (FloorSemiring.eventually_mul_pow_lt_factorial_sub C C 0).exists
  exact hn.not_ge (by simpa [pow_succ'] using hnorm n)

private noncomputable def expSqSeq (n : ℕ) : ℂ :=
  if Even n then (n.factorial : ℂ) / (n / 2).factorial else 0

private theorem expSqSeq_two_mul (k : ℕ) :
    expSqSeq (2 * k) = ((2 * k).factorial : ℂ) / k.factorial := by
  simp [expSqSeq]

private theorem expSqSeq_two_mul_add_one (k : ℕ) : expSqSeq (2 * k + 1) = 0 := by
  have hne : ¬Even (2 * k + 1) := by simp
  simp [expSqSeq, hne]

private theorem eFun_expSqSeq (z : ℂ) : eFun expSqSeq z = Complex.exp (z ^ 2) := by
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

private theorem isEntire_ePowerSeries_expSqSeq : (ePowerSeries expSqSeq).IsEntire := by
  refine PowerSeries.radius_eq_top_iff.mp (ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_)
  have hsum : Summable fun k : ℕ ↦ ((r : ℝ) ^ 2) ^ k / k.factorial :=
    Real.summable_pow_div_factorial ((r : ℝ) ^ 2)
  obtain ⟨B, hB⟩ := hsum.tendsto_atTop_zero.bddAbove_range
  refine PowerSeries.le_radius_of_bound (max 0 B) fun n ↦ ?_
  by_cases hn : Even n
  · obtain ⟨k, rfl⟩ := hn
    have h2k : k + k = 2 * k := (two_mul k).symm
    have hf : ((2 * k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hmem : ((r : ℝ) ^ 2) ^ k / k.factorial ∈
        Set.range (fun m : ℕ ↦ ((r : ℝ) ^ 2) ^ m / m.factorial) := ⟨k, rfl⟩
    rw [h2k, coeff_ePowerSeries, expSqSeq_two_mul, div_right_comm, div_self hf, norm_div,
      norm_one, Complex.norm_natCast, pow_mul, one_div_mul_eq_div]
    exact (hB hmem).trans (le_max_right 0 B)
  · simp [coeff_ePowerSeries, expSqSeq, hn]

private theorem not_isEFunction_expSqSeq : ¬IsEFunction expSqSeq := by
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
  have hupper : ‖expSqSeq (2 * k)‖ ≤ B ^ k :=
    (hnorm (2 * k)).trans <| pow_le_max_one_pow_pow
      (by simpa using (norm_nonneg _).trans (hnorm 0)) (by omega)
  have hlt : B ^ k < ((k + 1 : ℕ) : ℝ) ^ k :=
    pow_lt_pow_left₀ (hk.trans (by exact_mod_cast Nat.lt_succ_self k))
      (by positivity) (Nat.succ_ne_zero m)
  linarith

/-- The entire D-finite function `z ↦ Complex.exp (z ^ 2)` is not represented by any E-function
`eFun a`: its normalized Taylor coefficients at even indices `2k` equal `(2k)! / k!`, which grow
faster than geometric powers. -/
theorem not_exists_isEFunction_eFun_eq_exp_sq :
    ¬∃ a : ℕ → ℂ, IsEFunction a ∧ ∀ z : ℂ, eFun a z = Complex.exp (z ^ 2) := by
  rintro ⟨a, ha, heq⟩
  have hfreq : ∃ᶠ z in 𝓝 (0 : ℂ), z ∈ nonZeroDivisors ℂ :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)).frequently <|
      (Eventually.of_forall fun n : ℕ ↦
        mem_nonZeroDivisors_of_ne_zero (one_div_ne_zero (Nat.cast_add_one_ne_zero n))).frequently
  have hps : ePowerSeries a = ePowerSeries expSqSeq :=
    ha.isEntire_ePowerSeries.eq_of_forall_evalAt_eq isEntire_ePowerSeries_expSqSeq hfreq fun z ↦ by
      rw [← eFun_eq_evalAt_ePowerSeries, ← eFun_eq_evalAt_ePowerSeries, heq z, eFun_expSqSeq]
  exact not_isEFunction_expSqSeq (ePowerSeries_injective hps ▸ ha)

end TauCeti
