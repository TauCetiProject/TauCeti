/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import TauCeti.Analysis.CStarAlgebra.Schatten
public import TauCeti.Analysis.CStarAlgebra.SquareFunction
public import TauCeti.Analysis.Normed.Module.RademacherSum.Basic
public import TauCeti.Analysis.Normed.Module.RademacherSum.Moment

import TauCeti.Algebra.Group.Pi.Lemmas
import TauCeti.Analysis.CStarAlgebra.Khintchine.Dual
import TauCeti.Analysis.Normed.Module.HahnBanach.Basic

/-!
# The `p = 1` noncommutative Khintchine inequality for matrices

For a finite family `a : ι → CStarMatrix m m ℂ`, the Rademacher `Lᵖ` sum gauge and the infimal
row/column sum gauge are
`randomSumGauge p a = (|2^ι|⁻¹ ∑_ε ‖∑_k (±1)_{ε_k} a_k‖_{S^p}^p)^(1/p)` and
`rowColumnSumGauge p a = inf_{a = b + c} (‖columnSquare b‖_{S^p} + ‖rowSquare c‖_{S^p})`.

At `p = 1`, Lust-Piquard and Pisier proved uniform equivalence of these norms, and Haagerup–Musat /
Pisier established the explicit universal lower constant `(√3)⁻¹` (with upper constant `1`). We
prove this by combining:
1. Rectangular Schatten realization of `columnSquare`/`rowSquare` and infimal convolution `⊓`
   (`rowColumnSumSeminorm`).
2. Column/row trace-pairing duality from `TauCeti.Analysis.CStarAlgebra.Schatten` lifted to
   `rowColumnSumGauge 1`.
3. `Seminorm.exists_dual_apply_eq_and_norm_le`, `CStarMatrix.existsUnique_sum_trace_mul_eq`, and
   `TauCeti.exists_rademacherCoeff_eq_and_norm_le` for `(√3)⁻¹`, plus sign-cube Bessel duality for
   `1`.

## Main declarations

* `TauCeti.randomSumGauge`, `TauCeti.randomSumGauge_eq_rademacherMoment`,
  `TauCeti.rowColumnSumGauge`, `TauCeti.rowColumnSumSeminorm`,
  `TauCeti.rowColumnSumGauge_extend_zero`, `TauCeti.rowColumnSumGauge_single`
* `TauCeti.norm_sum_trace_mul_le_rowColumnSumGauge_one`,
  `TauCeti.exists_norm_square_le_one_and_sum_trace_mul_eq_rowColumnSumGauge_one`
* `TauCeti.isGreatest_rowColumnSumGauge_one`, `TauCeti.rowColumnSumGauge_one_eq_sSup`,
  `TauCeti.sum_trace_rademacherCoeff_mul`, `TauCeti.isGreatest_randomSumGauge_one`,
  `TauCeti.randomSumGauge_one_eq_sSup`
* `TauCeti.randomSumGauge_one_le_matrixLpGauge_columnSquare`,
  `TauCeti.randomSumGauge_one_le_matrixLpGauge_rowSquare`
* `TauCeti.matrix_khintchine_one`

## References

* F. Lust-Piquard and G. Pisier, *Non commutative Khintchine and Paley inequalities*,
  Ark. Mat. 29 (1991), 241–260.
* U. Haagerup and M. Musat, *On the best constants in noncommutative Khintchine-type
  inequalities*, J. Funct. Anal. 250 (2007), 588–624, Theorem 2.11.
* G. Pisier, *Grothendieck's theorem, past and present*, Bull. Amer. Math. Soc. 49 (2012),
  Theorem 9.1.
-/

public section

noncomputable section

open scoped BigOperators ComplexOrder ComplexStarModule InnerProductSpace NNReal ENNReal

namespace TauCeti

/-! ### The Rademacher `Lᵖ` sum gauge -/

section RandomSumGauge

variable {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m]

/-- The Rademacher `Lᵖ` sum gauge `(𝔼_ε ‖∑_k (±1)_{ε_k} a_k‖_p^p)^(1/p)` over `ι → Bool`. -/
def randomSumGauge (p : ℝ≥0) (a : ι → CStarMatrix m m ℂ) : ℝ :=
  ((∑ ε : ι → Bool, matrixLpGauge p (∑ k, (if ε k then (1 : ℂ) else -1) • a k) ^ (p : ℝ)) /
    (Fintype.card (ι → Bool) : ℝ)) ^ (1 / (p : ℝ))

/-- Unfolding definition of `randomSumGauge`. -/
theorem randomSumGauge_def (p : ℝ≥0) (a : ι → CStarMatrix m m ℂ) :
    randomSumGauge p a = ((∑ ε : ι → Bool,
      matrixLpGauge p (∑ k, (if ε k then (1 : ℂ) else -1) • a k) ^ (p : ℝ)) /
      (Fintype.card (ι → Bool) : ℝ)) ^ (1 / (p : ℝ)) := (rfl)

/-- `randomSumGauge` is nonnegative. -/
theorem randomSumGauge_nonneg (p : ℝ≥0) (a : ι → CStarMatrix m m ℂ) : 0 ≤ randomSumGauge p a :=
  Real.rpow_nonneg (div_nonneg (Finset.sum_nonneg fun _ _ =>
    Real.rpow_nonneg (matrixLpGauge_nonneg p _) _) (Nat.cast_nonneg _)) _

/-- `randomSumGauge p a` equals `(𝔼 ε : ι → ℤˣ, matrixLpGauge p (∑ k, ε k • a k) ^ p)^(1/p)`. -/
theorem randomSumGauge_eq_expect_units (p : ℝ≥0) (a : ι → CStarMatrix m m ℂ) :
    randomSumGauge p a =
      (𝔼 ε : ι → ℤˣ, matrixLpGauge p (∑ k, ε k • a k) ^ (p : ℝ)) ^ (1 / (p : ℝ)) := by
  let e : (ι → Bool) ≃ (ι → ℤˣ) := Equiv.piCongrRight fun _ =>
    ⟨fun b => if b then 1 else -1, fun u => decide (u = 1), fun b => by cases b <;> decide,
      fun u => by rcases Int.units_eq_one_or u with rfl | rfl <;> decide⟩
  rw [randomSumGauge_def, Fintype.card_congr e, Finset.expect_eq_sum_div_card, Finset.card_univ,
    Fintype.sum_equiv e _ (fun ε : ι → ℤˣ => matrixLpGauge p (∑ k, ε k • a k) ^ (p : ℝ)) fun ε => by
      congr 2; exact Finset.sum_congr rfl fun k _ => by
        cases h : ε k <;> simp [h, e, Units.smul_def]]

/-- At exponent `0`, `randomSumGauge 0 a` evaluates to `1` through `1 / 0 = 0` and `r ^ 0 = 1`. -/
@[simp] theorem randomSumGauge_zero_left (a : ι → CStarMatrix m m ℂ) : randomSumGauge 0 a = 1 := by
  simp [randomSumGauge_eq_expect_units]

/-- At `p = 1`, `randomSumGauge 1 a = 𝔼 ε : ι → ℤˣ, matrixLpGauge 1 (∑ k, ε k • a k)`. -/
theorem randomSumGauge_one_eq_expect_units (a : ι → CStarMatrix m m ℂ) :
    randomSumGauge 1 a = 𝔼 ε : ι → ℤˣ, matrixLpGauge 1 (∑ k, ε k • a k) := by
  simpa using randomSumGauge_eq_expect_units 1 a

/-- For `1 ≤ p`, `randomSumGauge p` agrees with `rademacherMoment` in the seminormed additive
group induced by `matrixLpSeminorm`. -/
theorem randomSumGauge_eq_rademacherMoment {p : ℝ≥0} (hp : 1 ≤ p) (a : ι → CStarMatrix m m ℂ) :
    randomSumGauge p a =
      @rademacherMoment ι (CStarMatrix m m ℂ) _ _
        (matrixLpSeminorm m p hp).toSeminormedAddCommGroup (p : ℝ) a := by
  let : SeminormedAddCommGroup (CStarMatrix m m ℂ) :=
    (matrixLpSeminorm m p hp).toSeminormedAddCommGroup
  rw [randomSumGauge_eq_expect_units, rademacherMoment_def]
  exact congrArg (· ^ (1 / (p : ℝ))) <| Finset.expect_congr rfl fun _ _ =>
    congrArg (· ^ (p : ℝ)) <| by
      rw [(matrixLpSeminorm m p hp).norm_toSeminormedAddCommGroup, matrixLpSeminorm_apply]

/-- At `0`, `randomSumGauge p` vanishes for `0 < p`. -/
@[simp] theorem randomSumGauge_zero {p : ℝ≥0} (hp : 0 < p) :
    randomSumGauge p (0 : ι → CStarMatrix m m ℂ) = 0 := by
  have hp' : (p : ℝ) ≠ 0 := (NNReal.coe_pos.mpr hp).ne'
  simp [randomSumGauge_eq_expect_units, matrixLpGauge_zero hp, Real.zero_rpow hp',
    Real.zero_rpow (inv_ne_zero hp')]

/-- For `0 < p`, `randomSumGauge p a = 0` if and only if `a = 0`. -/
@[simp] theorem randomSumGauge_eq_zero_iff {p : ℝ≥0} (hp : 0 < p) {a : ι → CStarMatrix m m ℂ} :
    randomSumGauge p a = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ randomSumGauge_zero hp⟩
  have hp' : (0 : ℝ) < (p : ℝ) := NNReal.coe_pos.mpr hp
  have hnn : 0 ≤ 𝔼 ε : ι → ℤˣ, matrixLpGauge p (∑ k, ε k • a k) ^ (p : ℝ) :=
    Finset.expect_nonneg fun _ _ => Real.rpow_nonneg (matrixLpGauge_nonneg p _) _
  have hsum : ∑ ε : ι → ℤˣ, matrixLpGauge p (∑ k, ε k • a k) ^ (p : ℝ) = 0 := by
    have hpow := congrArg (· ^ (p : ℝ)) h
    rw [randomSumGauge_eq_expect_units, one_div, Real.rpow_inv_rpow hnn hp'.ne',
      Real.zero_rpow hp'.ne', Finset.expect_eq_sum_div_card, Finset.card_univ,
      div_eq_zero_iff] at hpow
    exact hpow.resolve_right (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hall (ε : ι → ℤˣ) : ∑ k, ε k • a k = 0 := (matrixLpGauge_eq_zero_iff hp).mp <|
    (Real.rpow_eq_zero (matrixLpGauge_nonneg p _) hp'.ne').mp <|
      (Finset.sum_eq_zero_iff_of_nonneg fun _ _ =>
        Real.rpow_nonneg (matrixLpGauge_nonneg p _) _).mp hsum ε (Finset.mem_univ ε)
  funext i
  rw [← congrFun (rademacherCoeff_sum_units_smul (𝕜 := ℝ) a) i]
  simp [rademacherCoeff_apply, hall]

/-- `randomSumGauge` is invariant under entrywise `star`. -/
@[simp] theorem randomSumGauge_star (p : ℝ≥0) (a : ι → CStarMatrix m m ℂ) :
    randomSumGauge p (fun k => star (a k)) = randomSumGauge p a := by
  rw [randomSumGauge_eq_expect_units, randomSumGauge_eq_expect_units]; congr 1
  refine Finset.expect_congr rfl fun ε _ => ?_
  rw [← matrixLpGauge_star p (∑ k, ε k • a k), star_sum]; congr 2
  exact Finset.sum_congr rfl fun k _ => by rw [Units.smul_def, Units.smul_def, star_zsmul]

/-- `randomSumGauge` is invariant under negation. -/
@[simp] theorem randomSumGauge_neg (p : ℝ≥0) (a : ι → CStarMatrix m m ℂ) :
    randomSumGauge p (-a) = randomSumGauge p a := by
  simp only [randomSumGauge_eq_expect_units, Pi.neg_apply, smul_neg, Finset.sum_neg_distrib,
    matrixLpGauge_neg]

/-- For `0 < p`, `randomSumGauge p` is absolutely homogeneous over `ℂ`. -/
theorem randomSumGauge_smul {p : ℝ≥0} (hp : 0 < p) (c : ℂ) (a : ι → CStarMatrix m m ℂ) :
    randomSumGauge p (c • a) = ‖c‖ * randomSumGauge p a := by
  have hp' : (0 : ℝ) < (p : ℝ) := NNReal.coe_pos.mpr hp
  have hsum (ε : ι → ℤˣ) : (∑ k, ε k • (c • a) k) = c • ∑ k, ε k • a k := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by
      rw [Pi.smul_apply, Units.smul_def, Units.smul_def, smul_comm]
  rw [randomSumGauge_eq_expect_units, randomSumGauge_eq_expect_units]
  simp_rw [hsum, matrixLpGauge_smul hp, Real.mul_rpow (norm_nonneg c) (matrixLpGauge_nonneg p _)]
  rw [← Finset.mul_expect, Real.mul_rpow (Real.rpow_nonneg (norm_nonneg c) _)
      (Finset.expect_nonneg fun _ _ => Real.rpow_nonneg (matrixLpGauge_nonneg p _) _),
    one_div, Real.rpow_rpow_inv (norm_nonneg c) hp'.ne']

/-- Reindexing a family along an equivalence preserves `randomSumGauge`. -/
theorem randomSumGauge_comp_equiv {κ : Type*} [Fintype κ] [DecidableEq κ] (e : κ ≃ ι)
    (p : ℝ≥0) (a : ι → CStarMatrix m m ℂ) : randomSumGauge p (a ∘ e) = randomSumGauge p a := by
  rw [randomSumGauge_eq_expect_units, randomSumGauge_eq_expect_units,
    expect_sum_units_smul_comp_equiv e (fun x : CStarMatrix m m ℂ => matrixLpGauge p x ^ (p : ℝ)) a]

/-- Flipping signs by `δ : ι → ℤˣ` preserves `randomSumGauge`. -/
@[simp] theorem randomSumGauge_units_smul (δ : ι → ℤˣ) (p : ℝ≥0) (a : ι → CStarMatrix m m ℂ) :
    randomSumGauge p (fun k => δ k • a k) = randomSumGauge p a := by
  rw [randomSumGauge_eq_expect_units, randomSumGauge_eq_expect_units,
    expect_sum_units_smul_units_smul δ (fun x : CStarMatrix m m ℂ => matrixLpGauge p x ^ (p : ℝ)) a]

/-- Padding a family with zeros preserves `randomSumGauge`. -/
@[simp] theorem randomSumGauge_sumElim_zero {κ : Type*} [Fintype κ] [DecidableEq κ] (p : ℝ≥0)
    (a : ι → CStarMatrix m m ℂ) :
    randomSumGauge p (Sum.elim a (0 : κ → CStarMatrix m m ℂ)) = randomSumGauge p a := by
  rw [randomSumGauge_eq_expect_units, randomSumGauge_eq_expect_units,
    expect_sum_units_smul_sumElim_zero (κ := κ)
      (fun x : CStarMatrix m m ℂ => matrixLpGauge p x ^ (p : ℝ)) a]

/-- Extending a family by zero along an injection preserves `randomSumGauge`. -/
theorem randomSumGauge_extend_zero {κ : Type*} [Fintype κ] [DecidableEq κ] {f : κ → ι}
    (hf : Function.Injective f) (p : ℝ≥0) (a : κ → CStarMatrix m m ℂ) :
    randomSumGauge p (Function.extend f a 0) = randomSumGauge p a := by
  rw [randomSumGauge_eq_expect_units, randomSumGauge_eq_expect_units,
    expect_sum_units_smul_extend_zero hf
      (fun x : CStarMatrix m m ℂ => matrixLpGauge p x ^ (p : ℝ)) a]

/-- On a single-element index type, `randomSumGauge p a` equals `matrixLpGauge p (a default)`. -/
@[simp] theorem randomSumGauge_unique [Unique ι] (p : ℝ≥0) (a : ι → CStarMatrix m m ℂ) :
    randomSumGauge p a = matrixLpGauge p (a default) := by
  by_cases hp : p = 0
  · subst hp; simp
  · have hp' : (p : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hp
    rw [randomSumGauge_eq_expect_units,
      expect_sum_units_smul_unique (g := fun x : CStarMatrix m m ℂ => matrixLpGauge p x ^ (p : ℝ))
        (fun x => by rw [matrixLpGauge_neg]),
      ← Real.rpow_mul (matrixLpGauge_nonneg p _), mul_one_div_cancel hp', Real.rpow_one]

/-- The `randomSumGauge p` of a single-entry family `Pi.single i x` equals `matrixLpGauge p x`. -/
@[simp] theorem randomSumGauge_single (p : ℝ≥0) (i : ι) (x : CStarMatrix m m ℂ) :
    randomSumGauge p (Pi.single i x) = matrixLpGauge p x := by
  rw [← Function.extend_const_eq_single (fun _ : Unit => i) x,
    randomSumGauge_extend_zero (Function.injective_of_subsingleton _) p,
    randomSumGauge_unique]

/-- Triangle inequality for `randomSumGauge p` when `1 ≤ p`. -/
theorem randomSumGauge_add_le {p : ℝ≥0} (hp : 1 ≤ p) (a b : ι → CStarMatrix m m ℂ) :
    randomSumGauge p (a + b) ≤ randomSumGauge p a + randomSumGauge p b := by
  simp only [randomSumGauge_eq_rademacherMoment hp]
  exact @rademacherMoment_add_le ι (CStarMatrix m m ℂ) _ _
    (matrixLpSeminorm m p hp).toSeminormedAddCommGroup (p : ℝ) (by exact_mod_cast hp) a b

end RandomSumGauge

/-! ### The row/column sum gauge and seminorm -/

section RowColumnSumGauge

variable {ι m : Type*} [Fintype ι] [Fintype m]

/-- The infimal row/column `Lᵖ` sum gauge
`inf {matrixLpGauge p (columnSquare b) + matrixLpGauge p (rowSquare c) | a = b + c}`. -/
def rowColumnSumGauge (p : ℝ≥0) (a : ι → CStarMatrix m m ℂ) : ℝ :=
  sInf {r : ℝ | ∃ b c : ι → CStarMatrix m m ℂ, a = b + c ∧
    r = matrixLpGauge p (columnSquare b) + matrixLpGauge p (rowSquare c)}

/-- Unfolding definition of `rowColumnSumGauge`. -/
theorem rowColumnSumGauge_def (p : ℝ≥0) (a : ι → CStarMatrix m m ℂ) :
    rowColumnSumGauge p a = sInf {r : ℝ | ∃ b c : ι → CStarMatrix m m ℂ, a = b + c ∧
      r = matrixLpGauge p (columnSquare b) + matrixLpGauge p (rowSquare c)} := (rfl)

/-- At exponent `0`, `rowColumnSumGauge 0 a` evaluates to `2` because both `L⁰` gauges equal `1`.
-/
@[simp] theorem rowColumnSumGauge_zero_left (a : ι → CStarMatrix m m ℂ) :
    rowColumnSumGauge 0 a = 2 := by
  have hset : {r : ℝ | ∃ b c : ι → CStarMatrix m m ℂ, a = b + c ∧
      r = matrixLpGauge 0 (columnSquare b) + matrixLpGauge 0 (rowSquare c)} = {2} := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, matrixLpGauge_zero_left]
    constructor
    · rintro ⟨_, _, _, rfl⟩; norm_num
    · rintro rfl; exact ⟨a, 0, (add_zero a).symm, by norm_num⟩
  rw [rowColumnSumGauge_def, hset, csInf_singleton]

/-- `rowColumnSumGauge` is nonnegative. -/
theorem rowColumnSumGauge_nonneg (p : ℝ≥0) (a : ι → CStarMatrix m m ℂ) :
    0 ≤ rowColumnSumGauge p a :=
  Real.sInf_nonneg fun _ ⟨_, _, _, h⟩ =>
    h ▸ add_nonneg (matrixLpGauge_nonneg p _) (matrixLpGauge_nonneg p _)

/-- Any decomposition `a = b + c` bounds `rowColumnSumGauge p a` above. -/
theorem rowColumnSumGauge_le_of_eq_add (p : ℝ≥0) {a b c : ι → CStarMatrix m m ℂ} (h : a = b + c) :
    rowColumnSumGauge p a ≤ matrixLpGauge p (columnSquare b) + matrixLpGauge p (rowSquare c) :=
  csInf_le ⟨0, fun _ ⟨_, _, _, hr⟩ =>
    hr ▸ add_nonneg (matrixLpGauge_nonneg p _) (matrixLpGauge_nonneg p _)⟩ ⟨b, c, h, rfl⟩

/-- Universal lower-bound property for `rowColumnSumGauge`. -/
theorem le_rowColumnSumGauge {p : ℝ≥0} {a : ι → CStarMatrix m m ℂ} {r : ℝ}
    (h : ∀ b c : ι → CStarMatrix m m ℂ, a = b + c →
      r ≤ matrixLpGauge p (columnSquare b) + matrixLpGauge p (rowSquare c)) :
    r ≤ rowColumnSumGauge p a :=
  le_csInf ⟨_, a, 0, (add_zero a).symm, rfl⟩ fun _ ⟨b, c, hbc, hr⟩ => hr ▸ h b c hbc

/-- Characterization of lower bounds on `rowColumnSumGauge p a`. -/
theorem le_rowColumnSumGauge_iff {p : ℝ≥0} {a : ι → CStarMatrix m m ℂ} {r : ℝ} :
    r ≤ rowColumnSumGauge p a ↔ ∀ b c : ι → CStarMatrix m m ℂ, a = b + c →
      r ≤ matrixLpGauge p (columnSquare b) + matrixLpGauge p (rowSquare c) :=
  ⟨fun hr _ _ hbc => hr.trans (rowColumnSumGauge_le_of_eq_add p hbc), le_rowColumnSumGauge⟩

/-- Strict upper-bound characterization of `rowColumnSumGauge p a`. -/
theorem rowColumnSumGauge_lt_iff {p : ℝ≥0} {a : ι → CStarMatrix m m ℂ} {r : ℝ} :
    rowColumnSumGauge p a < r ↔ ∃ b c : ι → CStarMatrix m m ℂ, a = b + c ∧
      matrixLpGauge p (columnSquare b) + matrixLpGauge p (rowSquare c) < r := by
  simp only [← not_le, le_rowColumnSumGauge_iff, not_forall, exists_prop]

/-- Choosing `a = a + 0` bounds `rowColumnSumGauge p a` by the column `Lᵖ` gauge for `0 < p`. -/
theorem rowColumnSumGauge_le_matrixLpGauge_columnSquare {p : ℝ≥0} (hp : 0 < p)
    (a : ι → CStarMatrix m m ℂ) :
    rowColumnSumGauge p a ≤ matrixLpGauge p (columnSquare a) := by
  simpa only [rowSquare_zero, matrixLpGauge_zero hp, add_zero] using
    rowColumnSumGauge_le_of_eq_add p (add_zero a).symm

/-- Choosing `a = 0 + a` bounds `rowColumnSumGauge p a` by the row `Lᵖ` gauge for `0 < p`. -/
theorem rowColumnSumGauge_le_matrixLpGauge_rowSquare {p : ℝ≥0} (hp : 0 < p)
    (a : ι → CStarMatrix m m ℂ) :
    rowColumnSumGauge p a ≤ matrixLpGauge p (rowSquare a) := by
  simpa only [columnSquare_zero, matrixLpGauge_zero hp, zero_add] using
    rowColumnSumGauge_le_of_eq_add p (zero_add a).symm

/-- At `0`, `rowColumnSumGauge p` vanishes for `0 < p`. -/
@[simp] theorem rowColumnSumGauge_zero {p : ℝ≥0} (hp : 0 < p) :
    rowColumnSumGauge p (0 : ι → CStarMatrix m m ℂ) = 0 :=
  le_antisymm ((rowColumnSumGauge_le_matrixLpGauge_columnSquare hp 0).trans_eq
    (by simp [matrixLpGauge_zero hp])) (rowColumnSumGauge_nonneg p 0)

/-- For `0 < p`, `rowColumnSumGauge p a = 0` if and only if `a = 0`. -/
@[simp] theorem rowColumnSumGauge_eq_zero_iff {p : ℝ≥0} (hp : 0 < p) {a : ι → CStarMatrix m m ℂ} :
    rowColumnSumGauge p a = 0 ↔ a = 0 :=
  ⟨fun h => funext fun k => norm_le_zero_iff.mp <| h ▸ le_rowColumnSumGauge fun b c hbc => by
      rw [hbc, Pi.add_apply]
      exact (norm_add_le (b k) (c k)).trans <|
        (add_le_add (norm_apply_le_norm_columnSquare b k) (norm_apply_le_norm_rowSquare c k)).trans
          (add_le_add (norm_le_matrixLpGauge hp _) (norm_le_matrixLpGauge hp _)),
    fun h => h ▸ rowColumnSumGauge_zero hp⟩

/-- `rowColumnSumGauge` is invariant under entrywise `star`. -/
@[simp] theorem rowColumnSumGauge_star (p : ℝ≥0) (a : ι → CStarMatrix m m ℂ) :
    rowColumnSumGauge p (fun k => star (a k)) = rowColumnSumGauge p a := by
  have hle (x : ι → CStarMatrix m m ℂ) :
      rowColumnSumGauge p (fun k => star (x k)) ≤ rowColumnSumGauge p x :=
    le_rowColumnSumGauge fun b c hbc => by
      simpa only [← rowSquare_eq_columnSquare_star, ← columnSquare_eq_rowSquare_star,
        add_comm] using rowColumnSumGauge_le_of_eq_add p (a := fun k => star (x k))
          (b := fun k => star (c k)) (c := fun k => star (b k))
          (funext fun k => by simp [hbc, add_comm])
  exact le_antisymm (hle a) (by simpa only [star_star] using hle (fun k => star (a k)))

/-- `rowColumnSumGauge` is invariant under negation. -/
@[simp] theorem rowColumnSumGauge_neg (p : ℝ≥0) (a : ι → CStarMatrix m m ℂ) :
    rowColumnSumGauge p (-a) = rowColumnSumGauge p a := by
  have hle (x : ι → CStarMatrix m m ℂ) : rowColumnSumGauge p (-x) ≤ rowColumnSumGauge p x :=
    le_rowColumnSumGauge fun b c hbc => by
      have hneg : -x = -b + -c := (congrArg Neg.neg hbc).trans (neg_add b c)
      simpa only [columnSquare_neg, rowSquare_neg] using rowColumnSumGauge_le_of_eq_add p hneg
  exact le_antisymm (hle a) (by simpa only [neg_neg] using hle (-a))

/-- Reindexing a family along an equivalence preserves `rowColumnSumGauge`. -/
theorem rowColumnSumGauge_comp_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι) (p : ℝ≥0)
    (a : ι → CStarMatrix m m ℂ) : rowColumnSumGauge p (a ∘ e) = rowColumnSumGauge p a :=
  le_antisymm
    (le_rowColumnSumGauge fun b c hbc => by
      simpa only [columnSquare_comp_equiv, rowSquare_comp_equiv] using
        rowColumnSumGauge_le_of_eq_add p (a := a ∘ e) (b := b ∘ e) (c := c ∘ e)
          (funext fun k => congrFun hbc (e k)))
    (le_rowColumnSumGauge fun b c hbc => by
      simpa only [columnSquare_comp_equiv, rowSquare_comp_equiv] using
        rowColumnSumGauge_le_of_eq_add p (a := a) (b := b ∘ e.symm) (c := c ∘ e.symm)
          (funext fun i => by simpa using congrFun hbc (e.symm i)))

/-- Extending a family by zero along an injection preserves `rowColumnSumGauge`. -/
theorem rowColumnSumGauge_extend_zero {κ : Type*} [Fintype κ] {f : κ → ι}
    (hf : Function.Injective f) (p : ℝ≥0) (a : κ → CStarMatrix m m ℂ) :
    rowColumnSumGauge p (Function.extend f a 0) = rowColumnSumGauge p a := by
  classical
  rcases eq_zero_or_pos p with rfl | hp
  · simp
  refine le_antisymm ?_ ?_
  · refine le_rowColumnSumGauge fun b c hbc => ?_
    have hext : Function.extend f a 0 = Function.extend f b 0 + Function.extend f c 0 := by
      rw [hbc, ← Function.extend_add, add_zero]
    simpa only [columnSquare_extend_zero hf, rowSquare_extend_zero hf] using
      rowColumnSumGauge_le_of_eq_add p hext
  · refine le_rowColumnSumGauge fun b c hbc => ?_
    have hcomp : a = b ∘ f + c ∘ f := by
      funext k
      have hk := congrFun hbc (f k)
      simpa [hf.extend_apply] using hk
    exact (rowColumnSumGauge_le_of_eq_add p hcomp).trans <|
      add_le_add (matrixLpGauge_columnSquare_comp_le hf hp b)
        (matrixLpGauge_rowSquare_comp_le hf hp c)

/-- Padding a family with zeros preserves `rowColumnSumGauge`. -/
@[simp] theorem rowColumnSumGauge_sumElim_zero {κ : Type*} [Fintype κ] (p : ℝ≥0)
    (a : ι → CStarMatrix m m ℂ) :
    rowColumnSumGauge p (Sum.elim a (0 : κ → CStarMatrix m m ℂ)) = rowColumnSumGauge p a := by
  have h : Sum.elim a (0 : κ → CStarMatrix m m ℂ) = Function.extend Sum.inl a 0 := by
    ext (i | k)
    · simp [Sum.inl_injective.extend_apply]
    · simp
  rw [h, rowColumnSumGauge_extend_zero Sum.inl_injective]

/-- On a single-element index type, `rowColumnSumGauge p a` equals `matrixLpGauge p (a default)`
for `1 ≤ p`. -/
@[simp] theorem rowColumnSumGauge_unique [Unique ι] {p : ℝ≥0} (hp : 1 ≤ p)
    (a : ι → CStarMatrix m m ℂ) :
    rowColumnSumGauge p a = matrixLpGauge p (a default) := by
  refine le_antisymm ?_ (le_rowColumnSumGauge fun b c hbc => ?_)
  · simpa only [matrixLpGauge_columnSquare_unique] using
      rowColumnSumGauge_le_matrixLpGauge_columnSquare (zero_lt_one.trans_le hp) a
  · have hdef : a default = b default + c default := congrFun hbc default
    rw [hdef, matrixLpGauge_columnSquare_unique, matrixLpGauge_rowSquare_unique]
    exact matrixLpGauge_add_le hp (b default) (c default)

/-- The `rowColumnSumGauge p` of a single-entry family `Pi.single i x` equals `matrixLpGauge p x`
for `1 ≤ p`. -/
@[simp] theorem rowColumnSumGauge_single [DecidableEq ι] {p : ℝ≥0} (hp : 1 ≤ p) (i : ι)
    (x : CStarMatrix m m ℂ) :
    rowColumnSumGauge p (Pi.single i x) = matrixLpGauge p x := by
  rw [← Function.extend_const_eq_single (fun _ : Unit => i) x,
    rowColumnSumGauge_extend_zero (Function.injective_of_subsingleton _),
    rowColumnSumGauge_unique hp]

/-- Flipping signs by `δ : ι → ℤˣ` preserves `rowColumnSumGauge`. -/
@[simp] theorem rowColumnSumGauge_units_smul (δ : ι → ℤˣ) (p : ℝ≥0) (a : ι → CStarMatrix m m ℂ) :
    rowColumnSumGauge p (fun k => δ k • a k) = rowColumnSumGauge p a := by
  have hle (x : ι → CStarMatrix m m ℂ) :
      rowColumnSumGauge p (fun k => δ k • x k) ≤ rowColumnSumGauge p x :=
    le_rowColumnSumGauge fun b c hbc => by
      simpa only [columnSquare_units_smul, rowSquare_units_smul] using
        rowColumnSumGauge_le_of_eq_add p (a := fun k => δ k • x k) (b := fun k => δ k • b k)
          (c := fun k => δ k • c k) (funext fun k => by simp [hbc, smul_add])
  exact le_antisymm (hle a) <| by
    simpa only [← mul_smul, Int.units_mul_self, one_smul] using hle (fun k => δ k • a k)

/-- Absolute homogeneity of `rowColumnSumGauge p` for `0 < p`. -/
theorem rowColumnSumGauge_smul {p : ℝ≥0} (hp : 0 < p) (z : ℂ) (a : ι → CStarMatrix m m ℂ) :
    rowColumnSumGauge p (z • a) = ‖z‖ * rowColumnSumGauge p a := by
  by_cases hz : z = 0
  · simp [hz, rowColumnSumGauge_zero hp]
  · have hle {w : ℂ} (hw : w ≠ 0) (x : ι → CStarMatrix m m ℂ) :
        rowColumnSumGauge p (w • x) ≤ ‖w‖ * rowColumnSumGauge p x := by
      rw [← inv_mul_le_iff₀ (norm_pos_iff.mpr hw)]
      refine le_rowColumnSumGauge fun b c h => (inv_mul_le_iff₀ (norm_pos_iff.mpr hw)).mpr <|
        h ▸ (rowColumnSumGauge_le_of_eq_add p (smul_add w b c)).trans_eq ?_
      rw [matrixLpGauge_columnSquare_smul hp, matrixLpGauge_rowSquare_smul hp, mul_add]
    refine le_antisymm (hle hz a) ?_
    simpa only [inv_smul_smul₀ hz, norm_inv, ← mul_assoc,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_mul] using
      mul_le_mul_of_nonneg_left (hle (inv_ne_zero hz) (z • a)) (norm_nonneg z)

variable (ι m) in
/-- For `1 ≤ p`, `rowColumnSumGauge p` bundled as a `ℂ`-seminorm via infimal convolution `⊓`. -/
def rowColumnSumSeminorm (p : ℝ≥0) (hp : 1 ≤ p) : Seminorm ℂ (ι → CStarMatrix m m ℂ) :=
  Seminorm.of (fun b => matrixLpGauge p (columnSquare b)) (matrixLpGauge_columnSquare_add_le hp)
    (matrixLpGauge_columnSquare_smul (zero_lt_one.trans_le hp)) ⊓
  Seminorm.of (fun c => matrixLpGauge p (rowSquare c)) (matrixLpGauge_rowSquare_add_le hp)
    (matrixLpGauge_rowSquare_smul (zero_lt_one.trans_le hp))

@[simp] theorem rowColumnSumSeminorm_apply (p : ℝ≥0) (hp : 1 ≤ p) (a : ι → CStarMatrix m m ℂ) :
    rowColumnSumSeminorm ι m p hp a = rowColumnSumGauge p a := by
  rw [rowColumnSumSeminorm, Seminorm.inf_apply]
  refine le_antisymm ?_
    (le_ciInf fun b => rowColumnSumGauge_le_of_eq_add p (add_sub_cancel b a).symm)
  exact le_rowColumnSumGauge fun b c hbc =>
    (ciInf_le ⟨0, fun _ ⟨_, hr⟩ => hr ▸ add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)⟩
      b).trans_eq (by rw [hbc, add_sub_cancel_left]; rfl)

/-- Subadditivity of `rowColumnSumGauge p` for `1 ≤ p`. -/
theorem rowColumnSumGauge_add_le {p : ℝ≥0} (hp : 1 ≤ p) (a₁ a₂ : ι → CStarMatrix m m ℂ) :
    rowColumnSumGauge p (a₁ + a₂) ≤ rowColumnSumGauge p a₁ + rowColumnSumGauge p a₂ := by
  simpa only [rowColumnSumSeminorm_apply] using map_add_le_add (rowColumnSumSeminorm ι m p hp) a₁ a₂

end RowColumnSumGauge

/-! ### Trace-pairing duality for `rowColumnSumGauge 1` -/

section TraceDuality

variable {ι m : Type*} [Fintype ι] [Fintype m]

/-- **Row/column trace-pairing bound**: if `‖columnSquare x‖ ≤ 1` and `‖rowSquare x‖ ≤ 1`, then
`‖∑ k, tr(x k * a k)‖ ≤ rowColumnSumGauge 1 a`. -/
theorem norm_sum_trace_mul_le_rowColumnSumGauge_one {x a : ι → CStarMatrix m m ℂ}
    (hx_col : ‖columnSquare x‖ ≤ 1) (hx_row : ‖rowSquare x‖ ≤ 1) :
    ‖∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * a k))‖ ≤ rowColumnSumGauge 1 a :=
  le_rowColumnSumGauge fun b c hbc => by
    have hadd : ∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * a k)) =
        (∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * b k))) +
          ∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * c k)) := by
      simp only [hbc, Pi.add_apply, mul_add, ← CStarMatrix.traceLinearMap_apply (R := ℂ),
        map_add, Finset.sum_add_distrib]
    rw [hadd]
    exact (norm_add_le _ _).trans <| add_le_add
      ((norm_sum_trace_mul_le_norm_rowSquare_mul_matrixLpGauge_one_columnSquare x b).trans
        (mul_le_of_le_one_left (matrixLpGauge_nonneg 1 _) hx_row))
      ((norm_sum_trace_mul_le_norm_columnSquare_mul_matrixLpGauge_one_rowSquare x c).trans
        (mul_le_of_le_one_left (matrixLpGauge_nonneg 1 _) hx_col))

/-- **Row/column duality attainment**: there exists `x : ι → CStarMatrix m m ℂ` in the
row/column unit ball (`‖columnSquare x‖ ≤ 1` and `‖rowSquare x‖ ≤ 1`) attaining
`∑ k, tr(x k * a k) = rowColumnSumGauge 1 a`. -/
theorem exists_norm_square_le_one_and_sum_trace_mul_eq_rowColumnSumGauge_one
    (a : ι → CStarMatrix m m ℂ) :
    ∃ x : ι → CStarMatrix m m ℂ,
      ‖columnSquare x‖ ≤ 1 ∧ ‖rowSquare x‖ ≤ 1 ∧
        ∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * a k)) =
          (rowColumnSumGauge 1 a : ℂ) := by
  obtain ⟨φ, hφ_a, hφ_le⟩ := (rowColumnSumSeminorm ι m 1 le_rfl).exists_dual_apply_eq_and_norm_le a
  simp only [rowColumnSumSeminorm_apply, RCLike.ofReal_eq_complex_ofReal] at hφ_a hφ_le
  obtain ⟨x, hφ_tr⟩ := (CStarMatrix.existsUnique_sum_trace_mul_eq φ).exists
  have hx_row : ‖rowSquare x‖ ≤ 1 := norm_rowSquare_le_of_forall_norm_sum_trace_mul_le zero_le_one
    fun b => by
      rw [one_mul, ← hφ_tr b]
      exact (hφ_le b).trans (rowColumnSumGauge_le_matrixLpGauge_columnSquare zero_lt_one b)
  have hx_col : ‖columnSquare x‖ ≤ 1 := norm_columnSquare_le_of_forall_norm_sum_trace_mul_le
    zero_le_one fun c => by
      rw [one_mul, ← hφ_tr c]
      exact (hφ_le c).trans (rowColumnSumGauge_le_matrixLpGauge_rowSquare zero_lt_one c)
  exact ⟨x, hx_col, hx_row, by rw [← hφ_tr a, hφ_a]⟩

/-- **Matrix duality for `rowColumnSumGauge 1` (attained maximum)**: `rowColumnSumGauge 1 a` is
the greatest value of `‖∑ k, tr(x k * a k)‖` over the row/column unit ball
(`‖columnSquare x‖ ≤ 1` and `‖rowSquare x‖ ≤ 1`). -/
theorem isGreatest_rowColumnSumGauge_one (a : ι → CStarMatrix m m ℂ) :
    IsGreatest {r : ℝ | ∃ x : ι → CStarMatrix m m ℂ,
      ‖columnSquare x‖ ≤ 1 ∧ ‖rowSquare x‖ ≤ 1 ∧
        r = ‖∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * a k))‖}
      (rowColumnSumGauge 1 a) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx_col, hx_row, htr⟩ :=
      exists_norm_square_le_one_and_sum_trace_mul_eq_rowColumnSumGauge_one a
    exact ⟨x, hx_col, hx_row, by
      rw [htr, Complex.norm_real, Real.norm_of_nonneg (rowColumnSumGauge_nonneg 1 a)]⟩
  · rintro r ⟨x, hx_col, hx_row, rfl⟩
    exact norm_sum_trace_mul_le_rowColumnSumGauge_one hx_col hx_row

/-- **Matrix duality for `rowColumnSumGauge 1`**: `rowColumnSumGauge 1 a` equals the supremum of
`‖∑ k, tr(x k * a k)‖` over the row/column unit ball (`‖columnSquare x‖ ≤ 1`,
`‖rowSquare x‖ ≤ 1`). -/
theorem rowColumnSumGauge_one_eq_sSup (a : ι → CStarMatrix m m ℂ) :
    rowColumnSumGauge 1 a = sSup {r : ℝ | ∃ x : ι → CStarMatrix m m ℂ,
      ‖columnSquare x‖ ≤ 1 ∧ ‖rowSquare x‖ ≤ 1 ∧
        r = ‖∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * a k))‖} :=
  (isGreatest_rowColumnSumGauge_one a).csSup_eq.symm

end TraceDuality

/-! ### Sign-cube duality and the `p = 1` Khintchine inequality -/

section KhintchineOne

variable {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m]

/-- **Fourier-coefficient trace pairing**: the trace pairing of `rademacherCoeff ℝ Φ` with `a`
equals the expectation over `ε : ι → ℤˣ` of `tr(Φ ε * ∑ k, ε k • a k)`. -/
theorem sum_trace_rademacherCoeff_mul
    (Φ : (ι → ℤˣ) → CStarMatrix m m ℂ) (a : ι → CStarMatrix m m ℂ) :
    ∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (rademacherCoeff ℝ Φ k * a k)) =
      𝔼 ε : ι → ℤˣ, Matrix.trace (CStarMatrix.ofMatrix.symm (Φ ε * ∑ k, ε k • a k)) := by
  simpa only [LinearMap.compr₂_apply, LinearMap.mul_apply', CStarMatrix.traceLinearMap_apply] using
    sum_bilinear_rademacherCoeff_eq_expect
      ((LinearMap.mul ℝ (CStarMatrix m m ℂ)).compr₂ (CStarMatrix.traceLinearMap m ℝ ℂ)) Φ a

/-- **Sign-cube trace-pairing bound**: if `∀ ε, ‖Φ ε‖ ≤ C`, then the Fourier-coefficient pairing
of `Φ` with `a` satisfies
`‖∑ k, tr(rademacherCoeff ℝ Φ k * a k)‖ ≤ C * randomSumGauge 1 a`. -/
theorem norm_sum_trace_rademacherCoeff_mul_le
    {Φ : (ι → ℤˣ) → CStarMatrix m m ℂ} {C : ℝ} (hΦ : ∀ ε, ‖Φ ε‖ ≤ C)
    (a : ι → CStarMatrix m m ℂ) :
    ‖∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (rademacherCoeff ℝ Φ k * a k))‖ ≤
      C * randomSumGauge 1 a := by
  rw [sum_trace_rademacherCoeff_mul, randomSumGauge_one_eq_expect_units, Finset.mul_expect]
  refine (RCLike.norm_expect_le (K := ℂ)).trans (Finset.expect_le_expect fun ε _ => ?_)
  exact (norm_trace_mul_le_norm_mul_matrixLpGauge_one _ _).trans
    (mul_le_mul_of_nonneg_right (hΦ ε) (matrixLpGauge_nonneg 1 _))

/-- **Sign-cube duality attainment**: there exists a pointwise contraction
`Φ : (ι → ℤˣ) → CStarMatrix m m ℂ` (`∀ ε, ‖Φ ε‖ ≤ 1`) whose Fourier coefficients attain
`∑ k, tr(rademacherCoeff ℝ Φ k * a k) = randomSumGauge 1 a`. -/
theorem exists_norm_le_one_and_sum_trace_rademacherCoeff_mul_eq_randomSumGauge_one
    (a : ι → CStarMatrix m m ℂ) :
    ∃ Φ : (ι → ℤˣ) → CStarMatrix m m ℂ, (∀ ε, ‖Φ ε‖ ≤ 1) ∧
      ∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (rademacherCoeff ℝ Φ k * a k)) =
        (randomSumGauge 1 a : ℂ) := by
  choose Φ hΦ_norm hΦ_tr using fun ε : ι → ℤˣ =>
    exists_norm_le_one_and_trace_mul_eq_matrixLpGauge_one (∑ k, ε k • a k)
  refine ⟨Φ, hΦ_norm, ?_⟩
  rw [sum_trace_rademacherCoeff_mul, randomSumGauge_one_eq_expect_units, Complex.ofReal_expect]
  exact Finset.expect_congr rfl fun ε _ => hΦ_tr ε

/-- **Matrix duality for `randomSumGauge 1` (attained maximum)**: `randomSumGauge 1 a` is the
greatest value of `‖∑ k, tr(rademacherCoeff ℝ Φ k * a k)‖` over pointwise contractions
`Φ : (ι → ℤˣ) → CStarMatrix m m ℂ` (`∀ ε, ‖Φ ε‖ ≤ 1`). -/
theorem isGreatest_randomSumGauge_one (a : ι → CStarMatrix m m ℂ) :
    IsGreatest {r : ℝ | ∃ Φ : (ι → ℤˣ) → CStarMatrix m m ℂ, (∀ ε, ‖Φ ε‖ ≤ 1) ∧
      r = ‖∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (rademacherCoeff ℝ Φ k * a k))‖}
      (randomSumGauge 1 a) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨Φ, hΦ_norm, htr⟩ :=
      exists_norm_le_one_and_sum_trace_rademacherCoeff_mul_eq_randomSumGauge_one a
    exact ⟨Φ, hΦ_norm, by
      rw [htr, Complex.norm_real, Real.norm_of_nonneg (randomSumGauge_nonneg 1 a)]⟩
  · rintro r ⟨Φ, hΦ_norm, rfl⟩
    simpa only [one_mul] using norm_sum_trace_rademacherCoeff_mul_le hΦ_norm a

/-- **Matrix duality for `randomSumGauge 1`**: `randomSumGauge 1 a` equals the supremum of
`‖∑ k, tr(rademacherCoeff ℝ Φ k * a k)‖` over sign-cube Fourier coefficients of pointwise
contractions `Φ : (ι → ℤˣ) → CStarMatrix m m ℂ` (`∀ ε, ‖Φ ε‖ ≤ 1`). -/
theorem randomSumGauge_one_eq_sSup (a : ι → CStarMatrix m m ℂ) :
    randomSumGauge 1 a = sSup {r : ℝ | ∃ Φ : (ι → ℤˣ) → CStarMatrix m m ℂ,
      (∀ ε, ‖Φ ε‖ ≤ 1) ∧
        r = ‖∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (rademacherCoeff ℝ Φ k * a k))‖} :=
  (isGreatest_randomSumGauge_one a).csSup_eq.symm

/-- Column upper bound at `p = 1`: `randomSumGauge 1 b ≤ matrixLpGauge 1 (columnSquare b)`. -/
theorem randomSumGauge_one_le_matrixLpGauge_columnSquare (b : ι → CStarMatrix m m ℂ) :
    randomSumGauge 1 b ≤ matrixLpGauge 1 (columnSquare b) := by
  obtain ⟨Φ, hΦ_norm, hexp⟩ :=
    exists_norm_le_one_and_sum_trace_rademacherCoeff_mul_eq_randomSumGauge_one b
  rw [← Real.norm_of_nonneg (randomSumGauge_nonneg 1 b), ← Complex.norm_real, ← hexp]
  exact (norm_sum_trace_mul_le_norm_rowSquare_mul_matrixLpGauge_one_columnSquare
    (rademacherCoeff ℝ Φ) b).trans <|
    mul_le_of_le_one_left (matrixLpGauge_nonneg 1 _) (norm_rowSquare_rademacherCoeff_le hΦ_norm)

/-- Row upper bound at `p = 1`: `randomSumGauge 1 c ≤ matrixLpGauge 1 (rowSquare c)`. -/
theorem randomSumGauge_one_le_matrixLpGauge_rowSquare (c : ι → CStarMatrix m m ℂ) :
    randomSumGauge 1 c ≤ matrixLpGauge 1 (rowSquare c) := by
  rw [← randomSumGauge_star 1 c, rowSquare_eq_columnSquare_star]
  exact randomSumGauge_one_le_matrixLpGauge_columnSquare (fun k => star (c k))

/-- Upper bound in the `p = 1` noncommutative Khintchine inequality:
`randomSumGauge 1 a ≤ rowColumnSumGauge 1 a`. -/
theorem randomSumGauge_one_le_rowColumnSumGauge (a : ι → CStarMatrix m m ℂ) :
    randomSumGauge 1 a ≤ rowColumnSumGauge 1 a :=
  le_rowColumnSumGauge fun b c h => h ▸ (randomSumGauge_add_le le_rfl b c).trans
    (add_le_add (randomSumGauge_one_le_matrixLpGauge_columnSquare b)
      (randomSumGauge_one_le_matrixLpGauge_rowSquare c))

/-- Lower bound in the `p = 1` noncommutative Khintchine inequality:
`(Real.sqrt 3)⁻¹ * rowColumnSumGauge 1 a ≤ randomSumGauge 1 a`. -/
theorem inv_sqrt_three_mul_rowColumnSumGauge_le_randomSumGauge_one (a : ι → CStarMatrix m m ℂ) :
    (Real.sqrt 3)⁻¹ * rowColumnSumGauge 1 a ≤ randomSumGauge 1 a := by
  obtain ⟨x, hx_col, hx_row, htr⟩ :=
    exists_norm_square_le_one_and_sum_trace_mul_eq_rowColumnSumGauge_one a
  obtain ⟨Φ, hΦ_avg, hΦ_norm⟩ := exists_rademacherCoeff_eq_and_norm_le x
  have hΦ_le (ε : ι → ℤˣ) : ‖Φ ε‖ ≤ Real.sqrt 3 :=
    (hΦ_norm ε).trans <| mul_le_of_le_one_right (Real.sqrt_nonneg 3) (max_le hx_col hx_row)
  have hbound := norm_sum_trace_rademacherCoeff_mul_le hΦ_le a
  -- Re-elaborate `hΦ_avg` with the concrete `CStarMatrix` `Module ℝ` instance
  -- (rather than `NonUnitalCStarAlgebra`'s `complexToReal` instance) so `rw` matches syntactically.
  have hΦ_eq : rademacherCoeff ℝ Φ = x := hΦ_avg
  rw [hΦ_eq, htr, Complex.norm_real, Real.norm_of_nonneg (rowColumnSumGauge_nonneg 1 a)] at hbound
  exact (inv_mul_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr hbound

/-- **The `p = 1` noncommutative Khintchine inequality for matrices** (Lust-Piquard–Pisier,
Haagerup–Musat, Pisier): for any finite index types `ι` and `m` and any family
`a : ι → CStarMatrix m m ℂ`,
`(√3)⁻¹ * rowColumnSumGauge 1 a ≤ randomSumGauge 1 a ≤ rowColumnSumGauge 1 a`. -/
theorem matrix_khintchine_one (a : ι → CStarMatrix m m ℂ) :
    (Real.sqrt 3)⁻¹ * rowColumnSumGauge 1 a ≤ randomSumGauge 1 a ∧
      randomSumGauge 1 a ≤ rowColumnSumGauge 1 a :=
  ⟨inv_sqrt_three_mul_rowColumnSumGauge_le_randomSumGauge_one a,
    randomSumGauge_one_le_rowColumnSumGauge a⟩

end KhintchineOne

end TauCeti
