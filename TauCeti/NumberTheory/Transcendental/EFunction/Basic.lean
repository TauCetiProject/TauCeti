/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AlgebraicClosure
public import TauCeti.NumberTheory.Height.House
public import TauCeti.NumberTheory.Transcendental.EFunction.Series
public import TauCeti.RingTheory.PowerSeries.DFinite.Basic

import TauCeti.NumberTheory.NumberField.AdjoinPair

/-!
# Siegel's E-functions and G-functions

Siegel introduced *E-functions* and *G-functions* in 1929 to generalize the Hermite–Lindemann
theorem to solutions of linear differential equations with polynomial coefficients. In the
geometric growth normalization of Shidlovskii, André, Beukers, and Fischler–Rivoal, both notions
impose the same arithmetic conditions on a complex coefficient sequence `a : ℕ → ℂ`:

1. Every `a n` is algebraic over `ℚ`.
2. Its formal generating series satisfies a nonzero linear differential equation over
   `(algebraicClosure ℚ ℂ)[X]`: `ePowerSeries a = ∑ₙ (aₙ / n!) Xⁿ` is D-finite over
   `algebraicClosure ℚ ℂ` for an **E-function**, while the ordinary series
   `PowerSeries.mk a = ∑ₙ aₙ Xⁿ` is D-finite over `algebraicClosure ℚ ℂ` for a **G-function**.
3. The complex conjugates of `a n` grow at most geometrically: `|σ(a n)| ≤ C ^ (n + 1)`.
4. Common positive integer denominators `d n` clearing `a 0, …, a n` into algebraic integers grow
   at most geometrically: `1 ≤ d n ≤ D ^ (n + 1)`.

Because D-finiteness is equivalent to a polynomial recurrence on the coefficients
(`PowerSeries.isDFinite_iff_pRecursive`), multiplying or dividing a polynomial recurrence by rising
factorial factors identifies D-finiteness of `PowerSeries.mk a` with D-finiteness of
`ePowerSeries a` (`TauCeti.isDFinite_mk_iff_isDFinite_ePowerSeries`). Consequently, the formal
Borel transform gives an exact equivalence `IsGFunction a ↔ IsEFunction a`
(`TauCeti.isGFunction_iff_isEFunction`). Moreover, any algebraic P-recursive sequence is generated
past the natural roots of its leading recurrence polynomial by finitely many algebraic numbers, so
all coefficients of an E-function or G-function lie in a single number field
(`TauCeti.IsEFunction.exists_numberField`, `TauCeti.IsGFunction.exists_numberField`).

Analytically, the geometric bound on conjugates makes `ePowerSeries a` entire, so `eFun a` is an
entire function on `ℂ` whose Taylor derivatives at `0` are the `a k`, while `PowerSeries.mk a` has
positive radius of convergence.

## Main definitions

* `TauCeti.IsEFunction`: Siegel's E-functions `∑ₙ aₙ zⁿ / n!` in geometric normalization.
* `TauCeti.IsGFunction`: Siegel's G-functions `∑ₙ aₙ zⁿ` in geometric normalization.

## Main results

* `TauCeti.isDFinite_mk_iff_isDFinite_ePowerSeries`: `PowerSeries.mk a` is D-finite over `k` if
  and only if `ePowerSeries a` is D-finite over `k`.
* `TauCeti.isGFunction_iff_isEFunction`: formal Borel transform equivalence between G-functions
  and E-functions.
* `TauCeti.exists_numberField_of_isDFinite_mk`, `TauCeti.IsEFunction.exists_numberField`,
  `TauCeti.IsGFunction.exists_numberField`: all coefficients lie in a single number field.
* `TauCeti.IsEFunction.isEntire_ePowerSeries`, `TauCeti.IsEFunction.differentiable_eFun`,
  `TauCeti.IsEFunction.hasSum_eFun`: `eFun a` is entire and represented everywhere by its series.
* `TauCeti.IsGFunction.radius_pos`, `TauCeti.IsGFunction.exists_pos_summable`: a G-function has
  positive radius of convergence.

## References

* C. L. Siegel, *Über einige Anwendungen diophantischer Approximationen*, Abh. Preuß. Akad. Wiss.
  Phys.-Math. Kl. **1929**, no. 1.
* F. Beukers, *A refined version of the Siegel–Shidlovskii theorem*, Ann. of Math. (2) **163**
  (2006), 369–379.
* F. Beukers, *E-functions and G-functions*, lecture notes, Arizona Winter School, 2008, §3.1, §4.1.
* S. Fischler and T. Rivoal, *Arithmetic theory of E-operators*, J. Éc. polytech. Math. **3**
  (2016), 31–65, §1.
-/

public section

open Finset Polynomial PowerSeries
open scoped ENNReal NNReal

namespace TauCeti

/-! ### Definitions of E-functions and G-functions -/

/-- Siegel's *E-functions* (in the geometric normalization of Shidlovskii, André, and Beukers):
sequences `a : ℕ → ℂ` of algebraic numbers whose factorial-divided formal series `ePowerSeries a`
is D-finite over `algebraicClosure ℚ ℂ` and whose conjugates and common denominators grow at most
geometrically. -/
structure IsEFunction (a : ℕ → ℂ) : Prop where
  /-- Every coefficient `a n` is algebraic over `ℚ`. -/
  isAlgebraic : ∀ n, IsAlgebraic ℚ (a n)
  /-- The factorial-divided series `∑ₙ (aₙ / n!) Xⁿ` is D-finite over `algebraicClosure ℚ ℂ`. -/
  isDFinite : PowerSeries.IsDFinite (algebraicClosure ℚ ℂ) (ePowerSeries a)
  /-- All complex conjugates of `a n` are bounded in modulus by `C ^ (n + 1)`. -/
  size_le : ∃ C : ℝ, 0 < C ∧ ∀ n, ∀ z ∈ (minpoly ℚ (a n)).aroots ℂ, ‖z‖ ≤ C ^ (n + 1)
  /-- Common positive integer denominators `d n` clearing `a 0, …, a n` into algebraic integers
  satisfy `d n ≤ D ^ (n + 1)`. -/
  den_le : ∃ D : ℝ, 0 < D ∧ ∃ d : ℕ → ℕ, ∀ n, 1 ≤ d n ∧ (d n : ℝ) ≤ D ^ (n + 1) ∧
    ∀ m ≤ n, IsIntegral ℤ ((d n : ℂ) * a m)

/-- Siegel's *G-functions*: sequences `a : ℕ → ℂ` of algebraic numbers whose ordinary generating
series `PowerSeries.mk a = ∑ₙ aₙ Xⁿ` is D-finite over `algebraicClosure ℚ ℂ`, with the same
geometric conjugate and common-denominator bounds as `IsEFunction`. -/
structure IsGFunction (a : ℕ → ℂ) : Prop where
  /-- Every coefficient `a n` is algebraic over `ℚ`. -/
  isAlgebraic : ∀ n, IsAlgebraic ℚ (a n)
  /-- The ordinary power series `∑ₙ aₙ Xⁿ` is D-finite over `algebraicClosure ℚ ℂ`. -/
  isDFinite : PowerSeries.IsDFinite (algebraicClosure ℚ ℂ) (PowerSeries.mk a)
  /-- All complex conjugates of `a n` are bounded in modulus by `C ^ (n + 1)`. -/
  size_le : ∃ C : ℝ, 0 < C ∧ ∀ n, ∀ z ∈ (minpoly ℚ (a n)).aroots ℂ, ‖z‖ ≤ C ^ (n + 1)
  /-- Common positive integer denominators `d n` clearing `a 0, …, a n` into algebraic integers
  satisfy `d n ≤ D ^ (n + 1)`. -/
  den_le : ∃ D : ℝ, 0 < D ∧ ∃ d : ℕ → ℕ, ∀ n, 1 ≤ d n ∧ (d n : ℝ) ≤ D ^ (n + 1) ∧
    ∀ m ≤ n, IsIntegral ℤ ((d n : ℂ) * a m)

/-- Construct an `IsEFunction` from a geometric bound on `TauCeti.house`. -/
theorem IsEFunction.of_house_le {a : ℕ → ℂ} (halg : ∀ n, IsAlgebraic ℚ (a n))
    (hdf : PowerSeries.IsDFinite (algebraicClosure ℚ ℂ) (ePowerSeries a))
    (hsize : ∃ C : ℝ, 0 < C ∧ ∀ n, house (a n) ≤ C ^ (n + 1))
    (hden : ∃ D : ℝ, 0 < D ∧ ∃ d : ℕ → ℕ, ∀ n, 1 ≤ d n ∧ (d n : ℝ) ≤ D ^ (n + 1) ∧
      ∀ m ≤ n, IsIntegral ℤ ((d n : ℂ) * a m)) :
    IsEFunction a where
  isAlgebraic := halg
  isDFinite := hdf
  size_le := by
    obtain ⟨C, hC, hh⟩ := hsize
    exact ⟨C, hC, fun n ↦ (house_le_iff_forall_mem_aroots (by positivity)).mp (hh n)⟩
  den_le := hden

/-- Construct an `IsGFunction` from a geometric bound on `TauCeti.house`. -/
theorem IsGFunction.of_house_le {a : ℕ → ℂ} (halg : ∀ n, IsAlgebraic ℚ (a n))
    (hdf : PowerSeries.IsDFinite (algebraicClosure ℚ ℂ) (PowerSeries.mk a))
    (hsize : ∃ C : ℝ, 0 < C ∧ ∀ n, house (a n) ≤ C ^ (n + 1))
    (hden : ∃ D : ℝ, 0 < D ∧ ∃ d : ℕ → ℕ, ∀ n, 1 ≤ d n ∧ (d n : ℝ) ≤ D ^ (n + 1) ∧
      ∀ m ≤ n, IsIntegral ℤ ((d n : ℂ) * a m)) :
    IsGFunction a where
  isAlgebraic := halg
  isDFinite := hdf
  size_le := by
    obtain ⟨C, hC, hh⟩ := hsize
    exact ⟨C, hC, fun n ↦ (house_le_iff_forall_mem_aroots (by positivity)).mp (hh n)⟩
  den_le := hden

/-! ### Formal Borel transform between `PowerSeries.mk` and `ePowerSeries` -/

section BorelTransform

/-- Evaluating the shifted rising Pochhammer polynomial `(ascPochhammer k d).taylor (m + 1)` at `n`
and multiplying by `(n + m)!` produces `(n + m + d)!`. -/
private theorem factorial_mul_eval_taylor_ascPochhammer {k K : Type*} [CommSemiring k]
    [CommSemiring K] [Algebra k K] (n m d : ℕ) :
    ((n + m).factorial : K) *
      algebraMap k K ((Polynomial.taylor ((m + 1 : ℕ) : k) (ascPochhammer k d)).eval (n : k)) =
      ((n + m + d).factorial : K) := by
  rw [Polynomial.taylor_eval, ← Polynomial.eval_map_apply, ascPochhammer_map]
  simpa only [map_add, map_natCast, map_one, Nat.cast_add, Nat.cast_one, add_assoc] using
    factorial_mul_ascPochhammer K (n + m) d

/-- **Borel transform for D-finite series.** Over any field `k` inside a characteristic-zero field
`K`, the ordinary series `PowerSeries.mk a = ∑ₙ aₙ Xⁿ` is D-finite over `k` if and only if the
factorial-divided series `ePowerSeries a = ∑ₙ (aₙ / n!) Xⁿ` is D-finite over `k`. -/
theorem isDFinite_mk_iff_isDFinite_ePowerSeries {k K : Type*} [Field k] [Field K] [CharZero K]
    [Algebra k K] {a : ℕ → K} :
    PowerSeries.IsDFinite k (PowerSeries.mk a) ↔ PowerSeries.IsDFinite k (ePowerSeries a) := by
  constructor
  · intro hf
    obtain ⟨r, p, hp, hrec⟩ := PowerSeries.isDFinite_iff_pRecursive.mp hf
    have hne : Polynomial.taylor (1 : k) (ascPochhammer k r) ≠ 0 :=
      (Polynomial.taylor_eq_zero _ _).not.mpr (monic_ascPochhammer k r).ne_zero
    refine PowerSeries.isDFinite_iff_pRecursive.mpr
      ⟨r, fun i ↦ p i * Polynomial.taylor (1 : k) (ascPochhammer k i), mul_ne_zero hp hne,
        fun n ↦ ?_⟩
    refine mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)) ?_
    rw [mul_zero, mul_sum, ← hrec n]
    refine sum_congr rfl fun i _ ↦ ?_
    have hni : ((n + (i : ℕ)).factorial : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hprod := factorial_mul_eval_taylor_ascPochhammer (k := k) (K := K) n 0 i
    simp only [zero_add, add_zero, Nat.cast_one] at hprod
    rw [Algebra.smul_def, Algebra.smul_def, coeff_ePowerSeries, coeff_mk, Polynomial.eval_mul,
      map_mul, ← mul_assoc, mul_left_comm (n.factorial : K), hprod, mul_assoc,
      mul_div_cancel₀ _ hni]
  · intro hf
    obtain ⟨r, q, hq, hrec⟩ := PowerSeries.isDFinite_iff_pRecursive.mp hf
    refine PowerSeries.isDFinite_iff_pRecursive.mpr
      ⟨r, fun i ↦ q i * Polynomial.taylor ((i + 1 : ℕ) : k) (ascPochhammer k (r - i)),
        by simpa using hq, fun n ↦ ?_⟩
    rw [show (0 : K) = ((n + r).factorial : K) * ∑ i : Fin (r + 1),
        (q i).eval (n : k) • coeff (n + i) (ePowerSeries a) by rw [hrec n, mul_zero], mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    have hi : (i : ℕ) ≤ r := Nat.lt_succ_iff.mp i.isLt
    have hni : ((n + (i : ℕ)).factorial : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hprod := factorial_mul_eval_taylor_ascPochhammer (k := k) (K := K) n i (r - i)
    rw [Nat.add_assoc, Nat.add_sub_of_le hi] at hprod
    rw [Algebra.smul_def, Algebra.smul_def, coeff_mk, coeff_ePowerSeries, Polynomial.eval_mul,
      map_mul, ← hprod]
    conv_lhs => rw [← mul_div_cancel₀ (a (n + i)) hni]
    ring

/-- **Borel transform equivalence.** A complex sequence `a` defines a G-function if and only if it
defines an E-function. -/
theorem isGFunction_iff_isEFunction {a : ℕ → ℂ} : IsGFunction a ↔ IsEFunction a :=
  ⟨fun h ↦ ⟨h.isAlgebraic, isDFinite_mk_iff_isDFinite_ePowerSeries.mp h.isDFinite,
      h.size_le, h.den_le⟩,
    fun h ↦ ⟨h.isAlgebraic, isDFinite_mk_iff_isDFinite_ePowerSeries.mpr h.isDFinite,
      h.size_le, h.den_le⟩⟩

end BorelTransform

/-! ### Coefficients lie in a single number field -/

section NumberField

/-- If all coefficients of `p : k[X]` map into an intermediate field `K`, then so does `p.eval ↑n`
for every `n : ℕ`. -/
private theorem eval_natCast_mem_of_coeff_mem {Q k F : Type*} [Field Q] [Field k] [Field F]
    [Algebra Q F] [Algebra k F] (K : IntermediateField Q F) (p : k[X])
    (hp : ∀ j : Fin (p.natDegree + 1), algebraMap k F (p.coeff j) ∈ K) (n : ℕ) :
    algebraMap k F (p.eval (n : k)) ∈ K := by
  rw [Polynomial.eval_eq_sum_range, map_sum]
  refine K.sum_mem fun j hj ↦ ?_
  simpa only [map_mul, map_pow, map_natCast] using
    K.mul_mem (hp ⟨j, mem_range.mp hj⟩) (pow_mem (K.natCast_mem n) j)

/-- If a sequence `a : ℕ → F` of `ℚ`-algebraic elements in a characteristic-zero field has a
generating series `PowerSeries.mk a` that is D-finite over `algebraicClosure ℚ F`, then all
coefficients `a n` belong to a single intermediate number field `K` of `F / ℚ`. -/
theorem exists_numberField_of_isDFinite_mk {F : Type*} [Field F] [CharZero F] {a : ℕ → F}
    (halg : ∀ n, IsAlgebraic ℚ (a n))
    (hdf : PowerSeries.IsDFinite (algebraicClosure ℚ F) (PowerSeries.mk a)) :
    ∃ (K : IntermediateField ℚ F) (_ : NumberField K), ∀ n, a n ∈ K := by
  obtain ⟨r, q, hq, hrec⟩ := PowerSeries.isDFinite_iff_pRecursive.mp hdf
  have : CharZero (algebraicClosure ℚ F) :=
    (algebraMap (algebraicClosure ℚ F) F).charZero
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, (q (Fin.last r)).eval (n : algebraicClosure ℚ F) ≠ 0 :=
    Filter.eventually_atTop.mp (Nat.cofinite_eq_atTop ▸
      Nat.cast_injective.tendsto_cofinite.eventually
        (Polynomial.eventually_eval_ne_zero_cofinite hq))
  -- Collect the initial terms `a 0, …, a (N + r - 1)` and all coefficients of `q 0, …, q r`.
  let ι := Fin (N + r) ⊕ Σ i : Fin (r + 1), Fin ((q i).natDegree + 1)
  let gen : ι → F := Sum.elim (fun m ↦ a m) (fun ij ↦ ((q ij.1).coeff ij.2 : F))
  have hgen_alg : ∀ x : ι, IsAlgebraic ℚ (gen x) := by
    rintro (m | ⟨i, j⟩)
    · exact halg m
    · exact mem_algebraicClosure_iff.mp ((q i).coeff j).2
  obtain ⟨K, hK, y, hy⟩ := exists_numberField_comp hgen_alg
  have hmem_gen : ∀ x : ι, gen x ∈ K := fun x ↦ by
    rw [← congrFun hy x]
    exact (y x).2
  have heval_mem : ∀ (i : Fin (r + 1)) (n : ℕ),
      algebraMap (algebraicClosure ℚ F) F ((q i).eval (n : algebraicClosure ℚ F)) ∈ K :=
    fun i ↦ eval_natCast_mem_of_coeff_mem K (q i) fun j ↦ hmem_gen (Sum.inr ⟨i, j⟩)
  refine ⟨K, hK, fun m ↦ ?_⟩
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    by_cases hm : m < N + r
    · exact hmem_gen (Sum.inl ⟨m, hm⟩)
    · set n := m - r
      have hmr : n + r = m := by omega
      have hnN : N ≤ n := by omega
      have hstep : ∑ i : Fin (r + 1),
          algebraMap (algebraicClosure ℚ F) F ((q i).eval (n : algebraicClosure ℚ F)) *
            a (n + i) = 0 := by
        simpa only [Algebra.smul_def, coeff_mk] using hrec n
      rw [Fin.sum_univ_castSucc, Fin.val_last, hmr] at hstep
      set c := algebraMap (algebraicClosure ℚ F) F
        ((q (Fin.last r)).eval (n : algebraicClosure ℚ F))
      have hne : c ≠ 0 := (_root_.map_ne_zero _).mpr (hN n hnN)
      have hcm : c * a m = -∑ i : Fin r, algebraMap (algebraicClosure ℚ F) F
          ((q i.castSucc).eval (n : algebraicClosure ℚ F)) * a (n + i.castSucc) := by
        linear_combination hstep
      have hsol : a m = -c⁻¹ * ∑ i : Fin r, algebraMap (algebraicClosure ℚ F) F
          ((q i.castSucc).eval (n : algebraicClosure ℚ F)) * a (n + i.castSucc) := by
        rw [← inv_mul_cancel_left₀ hne (a m), hcm, mul_neg, neg_mul]
      rw [hsol]
      refine K.mul_mem (K.neg_mem (K.inv_mem (heval_mem _ n))) (K.sum_mem fun i _ ↦ ?_)
      have hilt : n + (i.castSucc : ℕ) < m := by
        rw [Fin.val_castSucc]
        have := i.isLt
        omega
      exact K.mul_mem (heval_mem _ n) (ih _ hilt)

/-- All coefficients of a G-function lie in a single number field inside `ℂ`. -/
theorem IsGFunction.exists_numberField {a : ℕ → ℂ} (ha : IsGFunction a) :
    ∃ (K : IntermediateField ℚ ℂ) (_ : NumberField K), ∀ n, a n ∈ K :=
  exists_numberField_of_isDFinite_mk ha.isAlgebraic ha.isDFinite

/-- All coefficients of an E-function lie in a single number field inside `ℂ`. -/
theorem IsEFunction.exists_numberField {a : ℕ → ℂ} (ha : IsEFunction a) :
    ∃ (K : IntermediateField ℚ ℂ) (_ : NumberField K), ∀ n, a n ∈ K :=
  (isGFunction_iff_isEFunction.mpr ha).exists_numberField

end NumberField

/-! ### Analytic consequences for E-functions and G-functions -/

namespace IsEFunction

variable {a : ℕ → ℂ}

/-- The houses of the coefficients of an E-function grow at most geometrically. -/
theorem exists_house_le (ha : IsEFunction a) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, house (a n) ≤ C ^ (n + 1) := by
  obtain ⟨C, hC, hsize⟩ := ha.size_le
  exact ⟨C, hC, fun n ↦ (house_le_iff_forall_mem_aroots (by positivity)).mpr (hsize n)⟩

/-- The moduli `‖a n‖` of an E-function grow at most geometrically. -/
theorem exists_norm_le (ha : IsEFunction a) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, ‖a n‖ ≤ C ^ (n + 1) := by
  obtain ⟨C, hC, hh⟩ := ha.exists_house_le
  exact ⟨C, hC, fun n ↦ (norm_le_house (ha.isAlgebraic n)).trans (hh n)⟩

/-- The formal factorial-divided series `ePowerSeries a` of an E-function is entire. -/
theorem isEntire_ePowerSeries (ha : IsEFunction a) : (ePowerSeries a).IsEntire := by
  obtain ⟨_, _, hnorm⟩ := ha.exists_norm_le
  exact isEntire_ePowerSeries_of_norm_le hnorm

/-- The formal radius of `ePowerSeries a` for an E-function is `⊤`. -/
theorem radius_ePowerSeries (ha : IsEFunction a) : (ePowerSeries a).radius = ⊤ :=
  radius_eq_top_iff.mpr ha.isEntire_ePowerSeries

/-- For an E-function `a` and every `z : ℂ`, `∑ₙ aₙ zⁿ / n!` converges to `eFun a z`. -/
theorem hasSum_eFun (ha : IsEFunction a) (z : ℂ) :
    HasSum (fun n ↦ a n * z ^ n / n.factorial) (eFun a z) :=
  TauCeti.hasSum_eFun ha.isEntire_ePowerSeries z

/-- For an E-function `a` and every `z : ℂ`, `fun n ↦ a n * z ^ n / n!` is summable. -/
theorem summable_eFun (ha : IsEFunction a) (z : ℂ) :
    Summable fun n ↦ a n * z ^ n / n.factorial :=
  TauCeti.summable_eFun ha.isEntire_ePowerSeries z

/-- `eFun a` has formal power series `∑ₙ (aₙ / n!) zⁿ` of infinite radius at `0`. -/
theorem hasFPowerSeriesOnBall_eFun (ha : IsEFunction a) :
    HasFPowerSeriesOnBall (eFun a)
      (FormalMultilinearSeries.ofScalars ℂ fun k ↦ a k / k.factorial) 0 ⊤ :=
  TauCeti.hasFPowerSeriesOnBall_eFun ha.isEntire_ePowerSeries

/-- For an E-function `a`, `eFun a` is analytic on all of `ℂ`. -/
theorem analyticOnNhd_eFun (ha : IsEFunction a) : AnalyticOnNhd ℂ (eFun a) Set.univ :=
  TauCeti.analyticOnNhd_eFun ha.isEntire_ePowerSeries

/-- For an E-function `a`, `eFun a` is an entire (everywhere complex-differentiable) function. -/
theorem differentiable_eFun (ha : IsEFunction a) : Differentiable ℂ (eFun a) :=
  TauCeti.differentiable_eFun ha.isEntire_ePowerSeries

/-- Shifting the coefficients of an E-function differentiates `eFun a`. -/
theorem deriv_eFun (ha : IsEFunction a) : deriv (eFun a) = eFun fun n ↦ a (n + 1) :=
  TauCeti.deriv_eFun ha.isEntire_ePowerSeries

/-- Iterated derivatives of `eFun a` for an E-function shift the coefficients by `k`. -/
theorem iteratedDeriv_eFun (ha : IsEFunction a) (k : ℕ) :
    iteratedDeriv k (eFun a) = eFun fun n ↦ a (n + k) :=
  TauCeti.iteratedDeriv_eFun ha.isEntire_ePowerSeries k

/-- The `k`-th derivative of `eFun a` at `0` is `a k`. -/
theorem iteratedDeriv_eFun_zero (ha : IsEFunction a) (k : ℕ) :
    iteratedDeriv k (eFun a) 0 = a k :=
  TauCeti.iteratedDeriv_eFun_zero ha.isEntire_ePowerSeries k

end IsEFunction

namespace IsGFunction

variable {a : ℕ → ℂ}

/-- The houses of the coefficients of a G-function grow at most geometrically. -/
theorem exists_house_le (ha : IsGFunction a) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, house (a n) ≤ C ^ (n + 1) :=
  (isGFunction_iff_isEFunction.mp ha).exists_house_le

/-- The moduli `‖a n‖` of a G-function grow at most geometrically. -/
theorem exists_norm_le (ha : IsGFunction a) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, ‖a n‖ ≤ C ^ (n + 1) :=
  (isGFunction_iff_isEFunction.mp ha).exists_norm_le

/-- **Positive radius of convergence of a G-function.** For every G-function `a`, the ordinary
series `PowerSeries.mk a` has positive radius of convergence. -/
theorem radius_pos (ha : IsGFunction a) : 0 < (PowerSeries.mk a).radius := by
  obtain ⟨C, hC, hnorm⟩ := ha.exists_norm_le
  set r : ℝ≥0 := ⟨C⁻¹, inv_nonneg.mpr hC.le⟩
  have hr : (0 : ℝ≥0∞) < r := by
    exact_mod_cast inv_pos.mpr hC
  refine hr.trans_le (PowerSeries.le_radius_of_bound C (r := r) fun n ↦ ?_)
  rw [coeff_mk, show (r : ℝ) = C⁻¹ from rfl]
  calc ‖a n‖ * (C⁻¹) ^ n ≤ C ^ (n + 1) * (C⁻¹) ^ n := by
        gcongr
        exact hnorm n
    _ = C * (C * C⁻¹) ^ n := by rw [pow_succ', mul_pow, mul_assoc]
    _ = C := by rw [mul_inv_cancel₀ hC.ne', one_pow, mul_one]

/-- A G-function converges absolutely on an open disc of positive radius around `0`. -/
theorem exists_pos_summable (ha : IsGFunction a) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r → Summable fun n ↦ a n * z ^ n := by
  obtain ⟨C, hC, hnorm⟩ := ha.exists_norm_le
  refine ⟨C⁻¹, inv_pos.mpr hC, fun z hz ↦ Summable.of_norm ?_⟩
  have hratio : 0 ≤ C * ‖z‖ := by positivity
  have hlt : C * ‖z‖ < 1 := by
    calc C * ‖z‖ < C * C⁻¹ := mul_lt_mul_of_pos_left hz hC
      _ = 1 := mul_inv_cancel₀ hC.ne'
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    ((summable_geometric_of_lt_one hratio hlt).mul_left C)
  rw [norm_mul, norm_pow]
  calc ‖a n‖ * ‖z‖ ^ n ≤ C ^ (n + 1) * ‖z‖ ^ n := by gcongr; exact hnorm n
    _ = C * (C * ‖z‖) ^ n := by rw [pow_succ', mul_pow, mul_assoc]

/-- `PowerSeries.mk a` defines an analytic function on the open ball of radius
`(PowerSeries.mk a).radius` around `0`. -/
theorem hasFPowerSeriesOnBall (ha : IsGFunction a) :
    HasFPowerSeriesOnBall (fun z ↦ ∑' n, a n * z ^ n)
      (FormalMultilinearSeries.ofScalars ℂ a) 0 (PowerSeries.mk a).radius := by
  have hrad : (PowerSeries.mk a).radius = (FormalMultilinearSeries.ofScalars ℂ a).radius := by
    simpa only [coeff_mk] using PowerSeries.radius_eq_radius_ofScalars ℂ (PowerSeries.mk a)
  rw [hrad]
  have hp := (FormalMultilinearSeries.ofScalars ℂ a).hasFPowerSeriesOnBall (hrad ▸ ha.radius_pos)
  convert hp using 1
  ext z
  simp [FormalMultilinearSeries.sum, smul_eq_mul, mul_comm]

end IsGFunction

end TauCeti
