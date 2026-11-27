/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Cyclotomic.Completion.FactorialExpansion

/-!
# Factorial series in the full cyclotomic completion

For an arbitrary sequence of polynomials `b_n ∈ R[q]`, the factorial series `∑_{n ≥ 0} b_n P_n`,
`P_n = (1 - q) ⋯ (1 - q ^ n)`, converges in the full cyclotomic completion
`R[q]^{ℕ_{>0}} = CycloCompletion R {n | 0 < n}`, the classical Habiro ring of `R`. No growth
condition on the coefficients is needed: every index divides `P_n` for all large `n`, so modulo any
index only finitely many terms survive. Modulo `P_N` the sum is the finite sum `∑_{n < N} b_n P_n`.

Every element is the factorial series of its normalized factorial digits, but unrestricted
coefficient sequences are not unique: `(1 - q) P_0 - P_1 = 0`. Only for coefficients with
`deg b_n ≤ n` are the coefficients the digits of the sum.

The standard example is Kontsevich's element `F = ∑_{n ≥ 0} P_n`, all of whose normalized
factorial digits are one.

## Main definitions

* `TauCeti.CycloCompletion.factorialSeries b`: the factorial series `∑_{n ≥ 0} b_n P_n`.
* `TauCeti.CycloCompletion.kontsevich R`: Kontsevich's element `F = ∑_{n ≥ 0} P_n`.

## Main results

* `TauCeti.CycloCompletion.hasSum_factorialSeries`: the series is unconditionally summable, with
  sum `factorialSeries b`.
* `TauCeti.CycloCompletion.proj_factorialIndex_factorialSeries`: modulo `P_N` the sum is
  `∑_{n < N} b_n P_n`, and `TauCeti.CycloCompletion.eq_factorialSeries_iff` characterizes the sum
  by these residues.
* `TauCeti.CycloCompletion.factorialSeries_add`, `TauCeti.CycloCompletion.factorialSeries_smul`,
  `TauCeti.CycloCompletion.fromPoly_mul_factorialSeries`,
  `TauCeti.CycloCompletion.map_factorialSeries`: additivity, scalar and polynomial multiplication,
  and coefficient change.
* `TauCeti.CycloCompletion.factorialDigit_factorialSeries`,
  `TauCeti.CycloCompletion.factorialSeries_factorialDigit`: reconstruction from bounded-degree
  digits and from the digits of an element.
* `TauCeti.CycloCompletion.factorialDigit_kontsevich`: every digit of `F` is one.

## References

* K. Habiro, *Cyclotomic completions of polynomial rings*, Publ. Res. Inst. Math. Sci. **40**
  (2004), 1127–1146, §1.
* K. Habiro, *Cyclotomic completions of polynomial rings*, arXiv:math/0209324v1, §1, (2).
-/

public section

open Filter Finset Polynomial
open scoped Topology

namespace TauCeti

variable {R : Type*} [CommRing R] {R' : Type*} [CommRing R']

namespace CycloCompletion

open PolyFamilyLimit

/-- The factorial terms `b_n P_n` of any polynomial sequence are summable in the full completion:
modulo each index only finitely many of them are nonzero. -/
theorem summable_fromPoly_mul_factorialPoly (b : ℕ → R[X]) :
    Summable fun n ↦ fromPoly R {n | 0 < n} (b n * factorialPoly R n) := by
  refine summable_iff_forall_eventually_proj_eq_zero.mpr fun f ↦ ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_dvd_factorialIndex f] with n hn
  rw [proj_fromPoly, AdjoinRoot.mk_eq_zero]
  exact (hn.trans (factorialIndex_dvd_iff.mpr dvd_rfl)).mul_left _

/-- The factorial series `∑_{n ≥ 0} b_n P_n` of an arbitrary polynomial sequence `b`, in the full
cyclotomic completion. -/
noncomputable def factorialSeries (b : ℕ → R[X]) : CycloCompletion R {n | 0 < n} :=
  ∑' n, fromPoly R {n | 0 < n} (b n * factorialPoly R n)

/-- The factorial terms `b_n P_n` sum to the factorial series. -/
theorem hasSum_factorialSeries (b : ℕ → R[X]) :
    HasSum (fun n ↦ fromPoly R {n | 0 < n} (b n * factorialPoly R n)) (factorialSeries b) :=
  (summable_fromPoly_mul_factorialPoly b).hasSum

/-- The polynomial partial sums `∑_{n < N} b_n P_n` converge to the factorial series. -/
theorem tendsto_fromPoly_sum_factorialSeries (b : ℕ → R[X]) :
    Tendsto (fun N ↦ fromPoly R {n | 0 < n} (∑ n ∈ range N, b n * factorialPoly R n)) atTop
      (𝓝 (factorialSeries b)) := by
  simpa only [map_sum] using (hasSum_factorialSeries b).tendsto_sum_nat

/-- Modulo each index, the partial sums `∑_{n < N} b_n P_n` eventually agree with the factorial
series. -/
theorem eventually_mk_sum_eq_proj_factorialSeries (b : ℕ → R[X]) (f : cycloIndex R {n | 0 < n}) :
    ∀ᶠ N in atTop, AdjoinRoot.mk (f : R[X]) (∑ n ∈ range N, b n * factorialPoly R n) =
      proj f (factorialSeries b) := by
  have h := (tendsto_sub_nhds_zero_iff.mpr (tendsto_fromPoly_sum_factorialSeries b))
  filter_upwards [(hasBasis_nhds_zero R _).tendsto_right_iff.mp h f trivial] with N hN
  rwa [SetLike.mem_coe, RingHom.mem_ker, map_sub, proj_fromPoly, sub_eq_zero] at hN

/-- **Finite projections of a factorial series.** Modulo `P_N`, the factorial series
`∑_{n ≥ 0} b_n P_n` is the finite sum `∑_{n < N} b_n P_n`. -/
theorem proj_factorialIndex_factorialSeries (b : ℕ → R[X]) (N : ℕ) :
    proj (factorialIndex R N) (factorialSeries b) =
      AdjoinRoot.mk _ (∑ n ∈ range N, b n * factorialPoly R n) := by
  obtain ⟨M, hM, hNM⟩ :=
    ((eventually_mk_sum_eq_proj_factorialSeries b _).and (eventually_ge_atTop N)).exists
  rw [← hM, ← sum_range_add_sum_Ico _ hNM, map_add, add_eq_left, map_sum]
  refine sum_eq_zero fun n hn ↦ AdjoinRoot.mk_eq_zero.mpr ?_
  exact (factorialIndex_dvd_iff.mpr (factorialPoly_dvd_factorialPoly (mem_Ico.mp hn).1)).mul_left _

/-- An element of the full completion is the factorial series `∑_{n ≥ 0} b_n P_n` exactly when it
agrees with `∑_{n < N} b_n P_n` modulo every `P_N`. -/
theorem eq_factorialSeries_iff {x : CycloCompletion R {n | 0 < n}} {b : ℕ → R[X]} :
    x = factorialSeries b ↔ ∀ N, proj (factorialIndex R N) x =
      AdjoinRoot.mk _ (∑ n ∈ range N, b n * factorialPoly R n) := by
  refine ⟨fun h N ↦ h ▸ proj_factorialIndex_factorialSeries b N, fun h ↦ ?_⟩
  exact ext_factorialIndex fun N ↦ by rw [h, proj_factorialIndex_factorialSeries]

/-- A factorial series with finitely many nonzero coefficients is the polynomial
`∑_{n < N} b_n P_n`. -/
theorem factorialSeries_eq_fromPoly_sum {b : ℕ → R[X]} {N : ℕ} (hb : ∀ n, N ≤ n → b n = 0) :
    factorialSeries b = fromPoly R {n | 0 < n} (∑ n ∈ range N, b n * factorialPoly R n) := by
  rw [factorialSeries, map_sum,
    tsum_eq_sum (s := range N) fun n hn ↦ by rw [hb n (by simpa using hn), zero_mul, map_zero]]

/-- The factorial series with zero coefficients is zero. -/
@[simp]
theorem factorialSeries_zero : factorialSeries (0 : ℕ → R[X]) = 0 := by
  simp [factorialSeries]

/-- Factorial series are additive in their coefficients. -/
@[simp]
theorem factorialSeries_add (b c : ℕ → R[X]) :
    factorialSeries (b + c) = factorialSeries b + factorialSeries c := by
  simp only [factorialSeries, Pi.add_apply, add_mul, map_add]
  exact (summable_fromPoly_mul_factorialPoly b).tsum_add (summable_fromPoly_mul_factorialPoly c)

/-- Factorial series commute with scalar multiplication of the coefficients. -/
@[simp]
theorem factorialSeries_smul (r : R) (b : ℕ → R[X]) :
    factorialSeries (r • b) = r • factorialSeries b := by
  simp only [factorialSeries, Pi.smul_apply, smul_mul_assoc, map_smul]
  exact (summable_fromPoly_mul_factorialPoly b).tsum_const_smul r

/-- Factorial series commute with negation of the coefficients. -/
@[simp]
theorem factorialSeries_neg (b : ℕ → R[X]) : factorialSeries (-b) = -factorialSeries b := by
  simpa using factorialSeries_smul (-1 : R) b

/-- Factorial series commute with subtraction of the coefficients. -/
@[simp]
theorem factorialSeries_sub (b c : ℕ → R[X]) :
    factorialSeries (b - c) = factorialSeries b - factorialSeries c := by
  simp [sub_eq_add_neg]

/-- Multiplying a factorial series by a polynomial multiplies each coefficient. -/
theorem fromPoly_mul_factorialSeries (p : R[X]) (b : ℕ → R[X]) :
    fromPoly R {n | 0 < n} p * factorialSeries b = factorialSeries fun n ↦ p * b n := by
  rw [factorialSeries, factorialSeries, ← (summable_fromPoly_mul_factorialPoly b).tsum_mul_left]
  simp only [mul_assoc, map_mul]

/-- Coefficient change maps a factorial series to the factorial series of the mapped
coefficients. -/
@[simp]
theorem map_factorialSeries (φ : R →+* R') (b : ℕ → R[X]) :
    map φ {n | 0 < n} (factorialSeries b) = factorialSeries fun n ↦ (b n).map φ := by
  refine (((hasSum_factorialSeries b).map (map φ {n | 0 < n}) (continuous_map φ _)).congr_fun
    fun n ↦ ?_).tsum_eq.symm
  simp [map_fromPoly, map_factorialPoly]

/-- **Reconstruction from digits.** For coefficients with `deg a_n ≤ n`, the normalized factorial
digits of the factorial series `∑_{n ≥ 0} a_n P_n` are the coefficients `a_n`. -/
theorem factorialDigit_factorialSeries {a : ℕ → R[X]} (ha : ∀ n, (a n).degree ≤ n) :
    (factorialSeries a).factorialDigit = a :=
  factorialDigit_eq_of_eventually ha fun _ ↦ eventually_mk_sum_eq_proj_factorialSeries a _

/-- Every element of the full completion is the factorial series of its normalized factorial
digits. -/
@[simp]
theorem factorialSeries_factorialDigit (x : CycloCompletion R {n | 0 < n}) :
    factorialSeries x.factorialDigit = x :=
  (eq_factorialSeries_iff.mpr (proj_factorialIndex x)).symm

section Kontsevich

variable (R)

/-- Kontsevich's element `F = ∑_{n ≥ 0} P_n = ∑_{n ≥ 0} (q; q)_n` of the full cyclotomic
completion: the factorial series all of whose coefficients are one. -/
noncomputable def kontsevich : CycloCompletion R {n | 0 < n} :=
  factorialSeries fun _ ↦ 1

/-- Kontsevich's element is the factorial series with all coefficients one. -/
theorem kontsevich_def : kontsevich R = factorialSeries fun _ ↦ 1 :=
  (rfl)

/-- Every normalized factorial digit of Kontsevich's element `F = ∑_{n ≥ 0} P_n` is one. -/
@[simp]
theorem factorialDigit_kontsevich (n : ℕ) : (kontsevich R).factorialDigit n = 1 := by
  rw [kontsevich_def,
    factorialDigit_factorialSeries fun _ ↦ degree_one_le.trans Nat.WithBot.coe_nonneg]

end Kontsevich

end CycloCompletion

/-! ### Reference values -/

open CycloCompletion PolyFamilyLimit

/-- A coefficient sequence supported at zero sums to the polynomial it carries. -/
example (p : R[X]) : factorialSeries (Pi.single 0 p) = fromPoly R {n | 0 < n} p := by
  rw [factorialSeries_eq_fromPoly_sum (N := 1) fun n hn ↦ by simp [Pi.single_apply]; omega]
  simp

/-- The unrestricted sequence `(1 - q, -1, 0, 0, …)` sums to zero, since `(1 - q) P_0 = P_1`:
factorial-series coefficients are not unique without the degree bound. -/
example : factorialSeries (fun n ↦ if n = 0 then 1 - X else if n = 1 then -1 else 0 : ℕ → R[X]) =
    0 := by
  rw [factorialSeries_eq_fromPoly_sum (N := 2) fun n hn ↦ by
    simp [show n ≠ 0 by omega, show n ≠ 1 by omega]]
  simp [sum_range_succ]

/-- Kontsevich's element is `2 - q` modulo `P_2`. -/
example : proj (factorialIndex R 2) (kontsevich R) = AdjoinRoot.mk _ (2 - X) := by
  rw [kontsevich_def, proj_factorialIndex_factorialSeries]
  congr 1
  simp [sum_range_succ]
  ring

end TauCeti
