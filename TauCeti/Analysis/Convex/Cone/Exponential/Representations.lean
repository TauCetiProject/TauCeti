/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.Analysis.Convex.Cone.Exponential.Basic
import Mathlib.Tactic.NormNum
import TauCeti.Analysis.SpecialFunctions.Log.ScaledExp
import TauCeti.Analysis.SpecialFunctions.Log.Softplus

/-!
# Elementary exponential-cone representations

We build the standard elementary conic representations over the closed real exponential cone
`TauCeti.ExponentialCone.cone`:

* Unit-scale exponential and logarithmic sections (`mem_cone_one_iff`, `le_log_iff_mem_cone`) and
  the strictly positive-scale logarithmic perspective (`le_mul_log_div_iff_mem_cone`), retaining
  strict positivity hypotheses on logarithm arguments so no junk value of `Real.log` at zero is
  used.
* The distinct-auxiliary softplus system `TauCeti.ExponentialCone.SoftplusSystem` representing
  `y * log (1 + exp (x / y)) ≤ t` for `0 < y`, its unit-scale specialization, its literal closed
  zero face `0 ≤ t ∧ x ≤ t` at `y = 0`, infeasibility at `y < 0`, and the corresponding logistic
  negative-log-sigmoid cost representations.
* Finite nonnegative-weight exponential lifting (`sum_mul_exp_le_iff_exists_mem_cone`) over any
  `Finset`, allowing zero weights and empty index sets.
* Scalar and finitely weighted process rows with time factors `t i > 0` and nonnegatively scaled
  exponential lifting (`mul_exp_le_iff_exists_mem_cone`; the companion logarithmic linearization
  is `Real.mul_exp_le_iff_log_add_le_log`).

## Main definitions and results

* `TauCeti.ExponentialCone.mem_cone_one_iff`, `TauCeti.ExponentialCone.le_log_iff_mem_cone`,
  `TauCeti.ExponentialCone.le_mul_log_div_iff_mem_cone`: exponential and logarithmic sections and
  perspective.
* `TauCeti.ExponentialCone.SoftplusSystem`: two-cone auxiliary system for the softplus
  perspective and its zero face.
* `TauCeti.ExponentialCone.mul_log_one_add_exp_div_le_iff_softplusSystem`,
  `TauCeti.ExponentialCone.log_one_add_exp_le_iff_softplusSystem`,
  `TauCeti.ExponentialCone.softplusSystem_zero_iff`,
  `TauCeti.ExponentialCone.not_softplusSystem_of_neg`: softplus and logistic cost
  representations.
* `TauCeti.ExponentialCone.sum_mul_exp_le_iff_exists_mem_cone`: finite nonnegative-weight
  exponential lifting.
* `TauCeti.ExponentialCone.mem_cone_mul_add_one_iff`,
  `TauCeti.ExponentialCone.sum_mul_exp_div_sub_one_le_iff_exists_mem_cone`,
  `TauCeti.ExponentialCone.mul_exp_le_iff_exists_mem_cone`: process rows and scaled exponential
  lifting.

## References

* MOSEK, *Modeling Cookbook* 3.4.0, Sections 5.1–5.2 and 7.1.1.
* D. E. Bernal Neira, *Modern Computational Approaches to Nonlinear Discrete Optimization and
  Applications in Process Systems Engineering*, Carnegie Mellon University doctoral thesis,
  May 2021, Chapter 8, Table 8.1 and (8.16)–(8.17), (8.32)–(8.35).
* D. E. Bernal Neira and I. E. Grossmann, *Convex mixed-integer nonlinear programs derived from
  generalized disjunctive programming using cones*, Computational Optimization and Applications
  88 (2024), 251–312, Table 1 and (9)–(10), (12).
* The distinct-auxiliary softplus system and the statement family follow the interface lineage
  in D. E. Bernal Neira's `complete-retained-library`
  (commit `59c355eb14ed1eff9664736428ca02b4543200b8`, Apache-2.0,
  `Chapter08ExponentialRows.lean` and `Chapter08ExponentialControls.lean`); all Lean proofs here
  are written from scratch against `TauCeti.ExponentialCone.cone`.
-/

public section

namespace TauCeti.ExponentialCone

/-! ### Exponential and logarithmic sections and perspectives -/

/-- The unit-scale slice of `cone` is the epigraph of `Real.exp`. -/
@[simp]
theorem mem_cone_one_iff {u w : ℝ} : (u, 1, w) ∈ cone ↔ Real.exp w ≤ u := by
  simpa using mem_cone_iff_of_pos (u := u) (v := 1) (w := w) zero_lt_one

/-- For strictly positive `x` and `y`, the logarithmic perspective hypograph `t ≤ y * log (x / y)`
is equivalent to `(x, y, t) ∈ cone`. Both strict positivity hypotheses are retained so that
`x / y` lies in the positive domain of `Real.log` without relying on totalized values at zero. -/
theorem le_mul_log_div_iff_mem_cone {x y t : ℝ} (hx : 0 < x) (hy : 0 < y) :
    t ≤ y * Real.log (x / y) ↔ (x, y, t) ∈ cone := by
  rw [mem_cone_iff_of_pos hy, ← div_le_iff₀' hy, Real.le_log_iff_exp_le (div_pos hx hy),
    le_div_iff₀' hy]

/-- For strictly positive `x`, the logarithm hypograph `t ≤ log x` is equivalent to
`(x, 1, t) ∈ cone`. -/
theorem le_log_iff_mem_cone {x t : ℝ} (hx : 0 < x) :
    t ≤ Real.log x ↔ (x, 1, t) ∈ cone := by
  simpa using le_mul_log_div_iff_mem_cone (t := t) hx zero_lt_one

/-! ### Softplus system, perspectives, and logistic cost -/

/-- Two-cone auxiliary system representing the epigraph of the softplus perspective
`y * log (1 + exp (x / y)) ≤ t` at positive scale `y > 0`, together with its closed zero face
`0 ≤ t ∧ x ≤ t` at `y = 0`. -/
def SoftplusSystem (x t y : ℝ) : Prop :=
  ∃ u v : ℝ, u + v ≤ y ∧ (u, y, x - t) ∈ cone ∧ (v, y, -t) ∈ cone

/-- Definitional expansion of `SoftplusSystem`. -/
theorem softplusSystem_iff {x t y : ℝ} :
    SoftplusSystem x t y ↔
      ∃ u v : ℝ, u + v ≤ y ∧ (u, y, x - t) ∈ cone ∧ (v, y, -t) ∈ cone := (Iff.rfl)

/-- For strictly positive scale `y`, the softplus perspective epigraph
`y * log (1 + exp (x / y)) ≤ t` is represented by `SoftplusSystem x t y`. -/
theorem mul_log_one_add_exp_div_le_iff_softplusSystem {x t y : ℝ} (hy : 0 < y) :
    y * Real.log (1 + Real.exp (x / y)) ≤ t ↔ SoftplusSystem x t y := by
  rw [← le_div_iff₀' hy, Real.log_one_add_exp_le_iff, ← sub_div, ← neg_div, softplusSystem_iff]
  constructor
  · intro h
    refine ⟨y * Real.exp ((x - t) / y), y * Real.exp (-t / y), ?_,
      (mem_cone_iff_of_pos hy).mpr le_rfl, (mem_cone_iff_of_pos hy).mpr le_rfl⟩
    simpa [mul_add] using mul_le_mul_of_nonneg_left h hy.le
  · rintro ⟨u, v, huv, hu, hv⟩
    have hsum : y * (Real.exp ((x - t) / y) + Real.exp (-t / y)) ≤ y * 1 := by
      rw [mul_add, mul_one]
      exact (add_le_add ((mem_cone_iff_of_pos hy).mp hu)
        ((mem_cone_iff_of_pos hy).mp hv)).trans huv
    exact (mul_le_mul_iff_right₀ hy).mp hsum

/-- The scalar softplus epigraph `log (1 + exp x) ≤ t` is represented by `SoftplusSystem x t 1`. -/
theorem log_one_add_exp_le_iff_softplusSystem {x t : ℝ} :
    Real.log (1 + Real.exp x) ≤ t ↔ SoftplusSystem x t 1 := by
  simpa using mul_log_one_add_exp_div_le_iff_softplusSystem (x := x) (t := t) zero_lt_one

/-- At zero scale, `SoftplusSystem x t 0` reduces to the literal closed face `0 ≤ t ∧ x ≤ t`. -/
@[simp]
theorem softplusSystem_zero_iff {x t : ℝ} :
    SoftplusSystem x t 0 ↔ 0 ≤ t ∧ x ≤ t := by
  simp only [softplusSystem_iff, mem_cone_zero_iff, sub_nonpos, neg_nonpos]
  exact ⟨fun ⟨_, _, _, hu, hv⟩ ↦ ⟨hv.2, hu.2⟩,
    fun ⟨ht, hxt⟩ ↦ ⟨0, 0, by simp, ⟨le_rfl, hxt⟩, ⟨le_rfl, ht⟩⟩⟩

/-- At any strictly negative scale, `SoftplusSystem` is infeasible. -/
theorem not_softplusSystem_of_neg {x t y : ℝ} (hy : y < 0) : ¬ SoftplusSystem x t y := by
  rintro ⟨_, _, _, hu, _⟩
  exact notMem_cone_of_neg hy hu

/-- For strictly positive scale `y`, the scaled logistic cost `-y * log (1 / (1 + exp (-s / y)))`
has epigraph represented by `SoftplusSystem (-s) t y`. -/
theorem neg_mul_log_one_div_one_add_exp_neg_div_le_iff_softplusSystem {s t y : ℝ} (hy : 0 < y) :
    -y * Real.log (1 / (1 + Real.exp (-s / y))) ≤ t ↔ SoftplusSystem (-s) t y := by
  rw [one_div, Real.log_inv, neg_mul_neg]
  exact mul_log_one_add_exp_div_le_iff_softplusSystem hy

/-- The scalar logistic cost `-log (1 / (1 + exp (-s)))` has epigraph represented by
`SoftplusSystem (-s) t 1`. -/
theorem neg_log_one_div_one_add_exp_neg_le_iff_softplusSystem {s t : ℝ} :
    -Real.log (1 / (1 + Real.exp (-s))) ≤ t ↔ SoftplusSystem (-s) t 1 := by
  simpa using
    neg_mul_log_one_div_one_add_exp_neg_div_le_iff_softplusSystem (s := s) (t := t) zero_lt_one

/-! ### Finite nonnegative-weight exponential lifting -/

/-- A finite nonnegative-weight sum of exponentials is bounded by `L` if and only if each
exponential can be lifted to an auxiliary variable in the unit-scale exponential cone satisfying
the corresponding linear sum bound. Both zero weights and empty index sets are permitted. -/
theorem sum_mul_exp_le_iff_exists_mem_cone {ι : Type*} {I : Finset ι}
    {d s : ι → ℝ} {L : ℝ} (hd : ∀ i ∈ I, 0 ≤ d i) :
    (∑ i ∈ I, d i * Real.exp (s i)) ≤ L ↔
      ∃ u : ι → ℝ, (∑ i ∈ I, d i * u i) ≤ L ∧ ∀ i ∈ I, (u i, 1, s i) ∈ cone := by
  constructor
  · intro h
    exact ⟨fun i ↦ Real.exp (s i), h, fun _ _ ↦ mem_cone_one_iff.mpr le_rfl⟩
  · rintro ⟨u, hsum, hcone⟩
    refine (Finset.sum_le_sum fun i hi ↦ ?_).trans hsum
    exact mul_le_mul_of_nonneg_left (mem_cone_one_iff.mp (hcone i hi)) (hd i hi)

/-! ### Process rows and scaled exponential inequalities -/

/-- For strictly positive time factor `t`, the process-row membership `(t * (u + 1), t, x) ∈ cone`
is equivalent to `exp (x / t) - 1 ≤ u`, with no sign restriction on `u` or `x`. -/
theorem mem_cone_mul_add_one_iff {u x t : ℝ} (ht : 0 < t) :
    (t * (u + 1), t, x) ∈ cone ↔ Real.exp (x / t) - 1 ≤ u := by
  rw [mem_cone_iff_of_pos ht, mul_le_mul_iff_right₀ ht, sub_le_iff_le_add]

/-- A finite nonnegative-weight sum of process terms `d i * (exp (x i / t i) - 1)` with strictly
positive time factors `t i` is bounded by `L` if and only if it admits auxiliary variables `u`
with `(t i * (u i + 1), t i, x i) ∈ cone`. -/
theorem sum_mul_exp_div_sub_one_le_iff_exists_mem_cone {ι : Type*} {I : Finset ι}
    {d t x : ι → ℝ} {L : ℝ} (hd : ∀ i ∈ I, 0 ≤ d i) (ht : ∀ i ∈ I, 0 < t i) :
    (∑ i ∈ I, d i * (Real.exp (x i / t i) - 1)) ≤ L ↔
      ∃ u : ι → ℝ, (∑ i ∈ I, d i * u i) ≤ L ∧
        ∀ i ∈ I, (t i * (u i + 1), t i, x i) ∈ cone := by
  have hshift :
      (∑ i ∈ I, d i * (Real.exp (x i / t i) - 1)) ≤ L ↔
        (∑ i ∈ I, d i * Real.exp (x i / t i)) ≤ L + ∑ i ∈ I, d i := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, sub_le_iff_le_add]
  rw [hshift, sum_mul_exp_le_iff_exists_mem_cone hd]
  constructor
  · rintro ⟨v, hsum, hcone⟩
    refine ⟨fun i ↦ v i - 1, ?_, fun i hi ↦ (mem_cone_mul_add_one_iff (ht i hi)).mpr
      (sub_le_sub_right (mem_cone_one_iff.mp (hcone i hi)) 1)⟩
    simpa only [mul_sub, mul_one, Finset.sum_sub_distrib, sub_le_iff_le_add] using hsum
  · rintro ⟨u, hsum, hcone⟩
    refine ⟨fun i ↦ u i + 1, ?_, fun i hi ↦ mem_cone_one_iff.mpr
      (sub_le_iff_le_add.mp ((mem_cone_mul_add_one_iff (ht i hi)).mp (hcone i hi)))⟩
    simpa only [mul_add, mul_one, Finset.sum_add_distrib] using add_le_add hsum le_rfl

/-- For nonnegative `a`, the scaled exponential inequality `a * exp s ≤ R` is equivalent to the
existence of an auxiliary `v` with `a * v ≤ R` and `(v, 1, s) ∈ cone`. -/
theorem mul_exp_le_iff_exists_mem_cone {a s R : ℝ} (ha : 0 ≤ a) :
    a * Real.exp s ≤ R ↔ ∃ v : ℝ, a * v ≤ R ∧ (v, 1, s) ∈ cone := by
  constructor
  · intro h
    exact ⟨Real.exp s, h, mem_cone_one_iff.mpr le_rfl⟩
  · rintro ⟨v, hv, hcone⟩
    exact (mul_le_mul_of_nonneg_left (mem_cone_one_iff.mp hcone) ha).trans hv

/-! ### Examples -/

example : SoftplusSystem (Real.log 3) (Real.log 4) 1 := by
  refine ⟨3 / 4, 1 / 4, by norm_num, ?_, ?_⟩
  · rw [mem_cone_one_iff, Real.exp_sub, Real.exp_log (by norm_num), Real.exp_log (by norm_num)]
  · rw [mem_cone_one_iff, Real.exp_neg, Real.exp_log (by norm_num), one_div]

example : ¬ SoftplusSystem 0 0 1 := by
  rw [← log_one_add_exp_le_iff_softplusSystem, Real.exp_zero]
  exact not_le.mpr (Real.log_pos (by norm_num))

example : SoftplusSystem 2 2 0 := by
  simp

example : ¬ SoftplusSystem 2 1 0 := by
  simp

example : ¬ SoftplusSystem 0 0 (-1) :=
  not_softplusSystem_of_neg (by norm_num)

example : -Real.log (1 / (1 + Real.exp (-(-Real.log 3)))) ≤ Real.log 4 := by
  rw [neg_log_one_div_one_add_exp_neg_le_iff_softplusSystem, neg_neg]
  refine ⟨3 / 4, 1 / 4, by norm_num, ?_, ?_⟩
  · rw [mem_cone_one_iff, Real.exp_sub, Real.exp_log (by norm_num), Real.exp_log (by norm_num)]
  · rw [mem_cone_one_iff, Real.exp_neg, Real.exp_log (by norm_num), one_div]

example {n : ℕ} (a x : Fin n → ℝ) (b t : ℝ) :
    Real.log (1 + Real.exp ((∑ j, a j * x j) + b)) ≤ t ↔
      SoftplusSystem ((∑ j, a j * x j) + b) t 1 :=
  log_one_add_exp_le_iff_softplusSystem

example (d s : Fin 0 → ℝ) :
    ∃ u : Fin 0 → ℝ, (∑ i ∈ (∅ : Finset (Fin 0)), d i * u i) ≤ 0 ∧
      ∀ i ∈ (∅ : Finset (Fin 0)), (u i, 1, s i) ∈ cone := by
  rw [← sum_mul_exp_le_iff_exists_mem_cone (s := s) (by simp)]
  simp

example (d s : Fin 0 → ℝ) :
    ¬ ∃ u : Fin 0 → ℝ, (∑ i ∈ (∅ : Finset (Fin 0)), d i * u i) ≤ -1 ∧
      ∀ i ∈ (∅ : Finset (Fin 0)), (u i, 1, s i) ∈ cone := by
  rw [← sum_mul_exp_le_iff_exists_mem_cone (s := s) (by simp)]
  norm_num

example {n : ℕ} (d t x s : Fin n → ℝ) (hd : ∀ j, 0 ≤ d j) (ht : ∀ j, 0 < t j) :
    (∑ j, d j * (Real.exp (x j / t j) - 1)) - (∑ j, s j * x j) ≤ 0 ↔
      ∃ u : Fin n → ℝ, (∑ j, d j * u j) - (∑ j, s j * x j) ≤ 0 ∧
        ∀ j, (t j * (u j + 1), t j, x j) ∈ cone := by
  simpa only [sub_nonpos, Finset.mem_univ, forall_true_left] using
    sum_mul_exp_div_sub_one_le_iff_exists_mem_cone (I := Finset.univ) (d := d) (t := t)
      (x := x) (L := ∑ j, s j * x j) (fun j _ ↦ hd j) (fun j _ ↦ ht j)

example {n : ℕ} (q x : Fin n → ℝ) {a : ℝ} (ha : 0 < a) (b c z : ℝ) :
    a * Real.exp (∑ j, q j * x j) ≤ b * z + c ↔
      ∃ v : ℝ, a * v ≤ b * z + c ∧ (v, 1, ∑ j, q j * x j) ∈ cone :=
  mul_exp_le_iff_exists_mem_cone ha.le

example {n : ℕ} (q x : Fin n → ℝ) {a : ℝ} (ha : 0 < a) (b c z : ℝ) :
    a * Real.exp (∑ j, q j * x j) ≤ b * z + c ↔
      0 < b * z + c ∧ Real.log a + (∑ j, q j * x j) ≤ Real.log (b * z + c) :=
  Real.mul_exp_le_iff_log_add_le_log ha

example : ¬ (1 * Real.exp 0 ≤ (0 : ℝ)) := by
  rw [Real.mul_exp_le_iff_log_add_le_log zero_lt_one]
  simp

example : (1 * ((Real.exp (-1) - 1) + 1), 1, -1) ∈ cone :=
  (mem_cone_mul_add_one_iff zero_lt_one).mpr (by simp)

end TauCeti.ExponentialCone
