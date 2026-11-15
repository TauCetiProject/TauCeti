/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Data.Fin.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Group.Uniform
import TauCeti.Analysis.Normed.Field.Lipschitz

/-!
# The Dyson repulsive drift and its Lipschitz truncation

The deterministic drift of the Dyson Brownian motion particle system on `ℝⁿ` is
`dysonDrift n x i = n⁻¹ ∑_{j ≠ i} (x i - x j)⁻¹`. Because `(x j - x i)⁻¹ = -(x i - x j)⁻¹` holds
for all real numbers (including at `0` where `0⁻¹ = 0`), any pairing `∑ᵢ uᵢ dysonDrift n x i`
folds onto the increasing index pairs `i < j`, and the total drift sums to zero identically.

On injective configurations `x, y`, the inner product `⟨dysonDrift n x - dysonDrift n y, x - y⟩`
equals `-n⁻¹ ∑_{i < j} ((xᵢ - xⱼ) - (yᵢ - yⱼ))² / ((xᵢ - xⱼ)(yᵢ - yⱼ))`, which is nonpositive on
the open decreasing chamber `{x₁ > ⋯ > xₙ}` (AGZ §4.3.1, Proposition 4.3.5). Testing instead
against the positive parts `max (xᵢ - yᵢ) 0` yields the one-sided dissipativity inequality
`∑ᵢ (dysonDrift n x i - dysonDrift n y i) max (xᵢ - yᵢ) 0 ≤ 0` driving coordinatewise order
comparison (AGZ Lemma 4.3.6).

For localizing singular collisions, `dysonDriftTrunc n δ` replaces `(xᵢ - xⱼ)⁻¹` for `i < j` by
`(max (xᵢ - xⱼ) δ)⁻¹` while preserving off-diagonal antisymmetry. It agrees with `dysonDrift n`
whenever `xᵢ - xⱼ ≥ δ` for all `i < j`, has zero coordinate sum everywhere, and for `δ > 0` is
bounded by `δ⁻¹` and globally Lipschitz with constant `2 / δ²`.

## Main declarations

* `TauCeti.Probability.dysonDrift`: the repulsive drift `n⁻¹ ∑_{j ≠ i} (x i - x j)⁻¹`.
* `TauCeti.Probability.sum_mul_dysonDrift` and `TauCeti.Probability.sum_dysonDrift`: off-diagonal
  pairing over `i < j` and zero coordinate sum.
* `TauCeti.Probability.sum_sub_dysonDrift_mul_sub` and
  `TauCeti.Probability.sum_sub_dysonDrift_mul_sub_nonpos`: monotonicity identity and dissipativity
  on the open chamber.
* `TauCeti.Probability.sum_sub_dysonDrift_mul_max_sub_nonpos`: positive-part dissipativity on the
  open chamber.
* `TauCeti.Probability.dysonDriftTrunc`: antisymmetric truncation at gap threshold `δ`.
* `TauCeti.Probability.dysonDriftTrunc_eq_dysonDrift`: agreement on `{x | ∀ i < j, δ ≤ x i - x j}`.
* `TauCeti.Probability.lipschitzWith_dysonDriftTrunc`: global Lipschitz bound for `0 < δ`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010, §4.3.1, Proposition 4.3.5 and Lemma 4.3.6.
-/

public section

open Finset
open scoped NNReal

namespace TauCeti.Probability

/-- **The Dyson repulsive drift** of `n` particles at positions `x : Fin n → ℝ`, normalized by
`n⁻¹` as in AGZ §4.3.1: `dysonDrift n x i = n⁻¹ ∑_{j ≠ i} (x i - x j)⁻¹`. -/
noncomputable def dysonDrift (n : ℕ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j ∈ univ.erase i, (x i - x j)⁻¹

/-- Evaluation formula for `dysonDrift`. -/
theorem dysonDrift_apply (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    dysonDrift n x i = (n : ℝ)⁻¹ * ∑ j ∈ univ.erase i, (x i - x j)⁻¹ :=
  (rfl)

/-- For at most one particle (`n ≤ 1`), the Dyson drift vanishes identically. -/
@[simp]
theorem dysonDrift_of_subsingleton {n : ℕ} [Subsingleton (Fin n)] (x : Fin n → ℝ) :
    dysonDrift n x = 0 := by
  ext i
  have hempty : (univ : Finset (Fin n)).erase i = ∅ := by
    ext j
    simp [Subsingleton.elim j i]
  simp [dysonDrift, hempty]

/-- First coordinate of the two-particle Dyson drift. -/
theorem dysonDrift_two_zero (x : Fin 2 → ℝ) :
    dysonDrift 2 x 0 = (2 * (x 0 - x 1))⁻¹ := by
  have herase : (univ : Finset (Fin 2)).erase 0 = {1} := by decide
  rw [dysonDrift, herase, sum_singleton, mul_inv]
  norm_num

/-- Second coordinate of the two-particle Dyson drift. -/
theorem dysonDrift_two_one (x : Fin 2 → ℝ) :
    dysonDrift 2 x 1 = -(2 * (x 0 - x 1))⁻¹ := by
  have herase : (univ : Finset (Fin 2)).erase 1 = {0} := by decide
  rw [dysonDrift, herase, sum_singleton, ← neg_sub (x 0) (x 1), inv_neg, mul_neg, mul_inv]
  norm_num

/-- At the zero configuration, `dysonDrift` vanishes identically. -/
@[simp]
theorem dysonDrift_zero (n : ℕ) : dysonDrift n 0 = 0 := by
  ext i
  simp [dysonDrift]

/-- At any constant configuration `fun _ ↦ c`, `dysonDrift` vanishes identically. -/
@[simp]
theorem dysonDrift_fun_const (n : ℕ) (c : ℝ) : dysonDrift n (fun _ ↦ c) = 0 := by
  ext i
  simp [dysonDrift]

/-- Shifting every particle by a common constant leaves `dysonDrift` unchanged. -/
@[simp]
theorem dysonDrift_add_const (n : ℕ) (x : Fin n → ℝ) (c : ℝ) :
    dysonDrift n (fun k ↦ x k + c) = dysonDrift n x := by
  ext i
  simp [dysonDrift]

/-- Reflecting all coordinates negates `dysonDrift`. -/
@[simp]
theorem dysonDrift_neg (n : ℕ) (x : Fin n → ℝ) :
    dysonDrift n (-x) = -dysonDrift n x := by
  ext i
  simp only [dysonDrift, Pi.neg_apply, ← mul_neg, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun j _ ↦ ?_
  have hsub : -x i - -x j = -(x i - x j) := by ring
  rw [hsub, inv_neg]

/-- Scaling all coordinates by `c : ℝ` scales `dysonDrift` by `c⁻¹`, including at `c = 0`. -/
theorem dysonDrift_smul (n : ℕ) (c : ℝ) (x : Fin n → ℝ) :
    dysonDrift n (c • x) = c⁻¹ • dysonDrift n x := by
  ext i
  simp only [dysonDrift, Pi.smul_apply, smul_eq_mul, ← mul_sub, mul_inv, ← mul_sum]
  ring

/-- `dysonDrift n` is continuous at every configuration with pairwise distinct coordinates. -/
theorem continuousAt_dysonDrift {n : ℕ} {x : Fin n → ℝ} (hx : Function.Injective x) :
    ContinuousAt (dysonDrift n) x := by
  refine continuousAt_pi.2 fun i ↦
    continuousAt_const.mul (tendsto_finsetSum _ fun j hj ↦ ?_)
  exact ((continuous_apply i).continuousAt.sub (continuous_apply j).continuousAt).inv₀
    (sub_ne_zero.2 (hx.ne (ne_of_mem_erase hj).symm))

/-- **Off-diagonal pairing identity.** Pairing `dysonDrift n x` against any vector `u` folds onto
strictly increasing index pairs `i < j`. -/
theorem sum_mul_dysonDrift (n : ℕ) (u x : Fin n → ℝ) :
    ∑ i, u i * dysonDrift n x i =
      (n : ℝ)⁻¹ * ∑ i, ∑ j ∈ Ioi i, (u i - u j) * (x i - x j)⁻¹ := by
  have hpull : ∑ i, u i * dysonDrift n x i =
      (n : ℝ)⁻¹ * ∑ i, ∑ j ∈ {i}ᶜ, u i * (x i - x j)⁻¹ := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [dysonDrift, compl_singleton, ← mul_assoc, mul_comm (u i), mul_assoc, mul_sum]
  rw [hpull, ← sum_sum_Ioi_add_eq_sum_sum_off_diag (fun j i ↦ u i * (x i - x j)⁻¹)]
  congr 1
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  rw [← neg_sub (x i) (x j), inv_neg]
  ring

/-- The coordinates of `dysonDrift n x` sum to zero for every configuration `x`. -/
@[simp]
theorem sum_dysonDrift (n : ℕ) (x : Fin n → ℝ) :
    ∑ i, dysonDrift n x i = 0 := by
  simpa using sum_mul_dysonDrift n (fun _ ↦ 1) x

/-- **Monotonicity identity for the Dyson drift** (AGZ §4.3.1, proof of Proposition 4.3.5). For any
two injective configurations `x, y : Fin n → ℝ`, `⟨dysonDrift n x - dysonDrift n y, x - y⟩` equals
`-n⁻¹ ∑_{i < j} ((xᵢ - xⱼ) - (yᵢ - yⱼ))² / ((xᵢ - xⱼ)(yᵢ - yⱼ))`. -/
theorem sum_sub_dysonDrift_mul_sub {n : ℕ} {x y : Fin n → ℝ} (hx : Function.Injective x)
    (hy : Function.Injective y) :
    ∑ i, (dysonDrift n x i - dysonDrift n y i) * (x i - y i) =
      -(n : ℝ)⁻¹ * ∑ i, ∑ j ∈ Ioi i,
        ((x i - x j) - (y i - y j)) ^ 2 / ((x i - x j) * (y i - y j)) := by
  have hrew : ∑ i, (dysonDrift n x i - dysonDrift n y i) * (x i - y i) =
      (∑ i, (x i - y i) * dysonDrift n x i) - ∑ i, (x i - y i) * dysonDrift n y i := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ ↦ by ring
  rw [hrew, sum_mul_dysonDrift, sum_mul_dysonDrift, ← mul_sub, ← sum_sub_distrib, neg_mul,
    ← neg_eq_iff_eq_neg, ← mul_neg, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← sum_sub_distrib, ← sum_neg_distrib]
  refine sum_congr rfl fun j hj ↦ ?_
  have hne : i ≠ j := (mem_Ioi.1 hj).ne
  have hax : x i - x j ≠ 0 := sub_ne_zero.2 (hx.ne hne)
  have hay : y i - y j ≠ 0 := sub_ne_zero.2 (hy.ne hne)
  field_simp
  ring

/-- **Dissipativity of the Dyson drift on the open chamber.** For `StrictAnti x` and `StrictAnti y`,
`∑ᵢ (dysonDrift n x i - dysonDrift n y i) (xᵢ - yᵢ) ≤ 0`. -/
theorem sum_sub_dysonDrift_mul_sub_nonpos {n : ℕ} {x y : Fin n → ℝ} (hx : StrictAnti x)
    (hy : StrictAnti y) :
    ∑ i, (dysonDrift n x i - dysonDrift n y i) * (x i - y i) ≤ 0 := by
  rw [sum_sub_dysonDrift_mul_sub hx.injective hy.injective, neg_mul, neg_nonpos]
  refine mul_nonneg (by positivity) (sum_nonneg fun i _ ↦ sum_nonneg fun j hj ↦ ?_)
  have hij : i < j := mem_Ioi.1 hj
  exact div_nonneg (sq_nonneg _)
    (mul_nonneg (sub_pos.2 (hx hij)).le (sub_pos.2 (hy hij)).le)

/-- **One-sided positive-part dissipativity on the open chamber** (for AGZ Lemma 4.3.6). For
`StrictAnti x` and `StrictAnti y`, testing `dysonDrift n x - dysonDrift n y` against
`i ↦ max (x i - y i) 0` is nonpositive. -/
theorem sum_sub_dysonDrift_mul_max_sub_nonpos {n : ℕ} {x y : Fin n → ℝ} (hx : StrictAnti x)
    (hy : StrictAnti y) :
    ∑ i, (dysonDrift n x i - dysonDrift n y i) * max (x i - y i) 0 ≤ 0 := by
  set u : Fin n → ℝ := fun k ↦ max (x k - y k) 0
  have hrew : ∑ i, (dysonDrift n x i - dysonDrift n y i) * u i =
      (∑ i, u i * dysonDrift n x i) - ∑ i, u i * dysonDrift n y i := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ ↦ by ring
  rw [hrew, sum_mul_dysonDrift, sum_mul_dysonDrift, ← mul_sub, ← sum_sub_distrib]
  refine mul_nonpos_of_nonneg_of_nonpos (by positivity) (sum_nonpos fun i _ ↦ ?_)
  rw [← sum_sub_distrib]
  refine sum_nonpos fun j hj ↦ ?_
  have hij : i < j := mem_Ioi.1 hj
  have ha : 0 < x i - x j := sub_pos.2 (hx hij)
  have hb : 0 < y i - y j := sub_pos.2 (hy hij)
  have hfrac : (u i - u j) * (x i - x j)⁻¹ - (u i - u j) * (y i - y j)⁻¹ =
      (u i - u j) * ((x j - y j) - (x i - y i)) / ((x i - x j) * (y i - y j)) := by
    field_simp
    ring
  rw [hfrac]
  refine div_nonpos_of_nonpos_of_nonneg ?_ (mul_pos ha hb).le
  rcases le_total (x i - y i) (x j - y j) with hle | hge
  · have hu : u i ≤ u j := max_le_max_right 0 hle
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hu) (sub_nonneg.2 hle)
  · have hu : u j ≤ u i := max_le_max_right 0 hge
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hu) (sub_nonpos.2 hge)

/-- **Antisymmetric truncated Dyson drift** at gap threshold `δ`. For `i < j` the singular factor
`(x i - x j)⁻¹` is replaced by `(max (x i - x j) δ)⁻¹`, and for `j < i` by its negation so that
off-diagonal antisymmetry and center-of-mass conservation hold everywhere. -/
noncomputable def dysonDriftTrunc (n : ℕ) (δ : ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j ∈ univ.erase i,
    if i < j then (max (x i - x j) δ)⁻¹ else -(max (x j - x i) δ)⁻¹

/-- Evaluation formula for `dysonDriftTrunc`. -/
theorem dysonDriftTrunc_apply (n : ℕ) (δ : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    dysonDriftTrunc n δ x i = (n : ℝ)⁻¹ * ∑ j ∈ univ.erase i,
      if i < j then (max (x i - x j) δ)⁻¹ else -(max (x j - x i) δ)⁻¹ :=
  (rfl)

/-- For at most one particle (`n ≤ 1`), `dysonDriftTrunc` vanishes identically. -/
@[simp]
theorem dysonDriftTrunc_of_subsingleton {n : ℕ} [Subsingleton (Fin n)] (δ : ℝ) (x : Fin n → ℝ) :
    dysonDriftTrunc n δ x = 0 := by
  ext i
  have hempty : (univ : Finset (Fin n)).erase i = ∅ := by
    ext j
    simp [Subsingleton.elim j i]
  simp [dysonDriftTrunc, hempty]

/-- Shifting every particle by a common constant leaves `dysonDriftTrunc` unchanged. -/
@[simp]
theorem dysonDriftTrunc_add_const (n : ℕ) (δ : ℝ) (x : Fin n → ℝ) (c : ℝ) :
    dysonDriftTrunc n δ (fun k ↦ x k + c) = dysonDriftTrunc n δ x := by
  ext i
  simp [dysonDriftTrunc]

/-- `dysonDriftTrunc n δ x` agrees with `dysonDrift n x` whenever every pair `i < j` satisfies
`δ ≤ x i - x j`. -/
theorem dysonDriftTrunc_eq_dysonDrift {n : ℕ} {δ : ℝ} {x : Fin n → ℝ}
    (hx : ∀ ⦃i j : Fin n⦄, i < j → δ ≤ x i - x j) :
    dysonDriftTrunc n δ x = dysonDrift n x := by
  ext i
  simp only [dysonDriftTrunc, dysonDrift]
  congr 1
  refine sum_congr rfl fun j hj ↦ ?_
  rcases lt_or_gt_of_ne (ne_of_mem_erase hj).symm with hij | hji
  · simp [hij, max_eq_left (hx hij)]
  · simp only [hji.not_gt, ↓reduceIte]
    rw [max_eq_left (hx hji), ← neg_sub (x i) (x j), inv_neg, neg_neg]

/-- Pairing `dysonDriftTrunc n δ x` against `u` folds onto `i < j`. -/
theorem sum_mul_dysonDriftTrunc (n : ℕ) (δ : ℝ) (u x : Fin n → ℝ) :
    ∑ i, u i * dysonDriftTrunc n δ x i =
      (n : ℝ)⁻¹ * ∑ i, ∑ j ∈ Ioi i, (u i - u j) * (max (x i - x j) δ)⁻¹ := by
  have hpull : ∑ i, u i * dysonDriftTrunc n δ x i =
      (n : ℝ)⁻¹ * ∑ i, ∑ j ∈ {i}ᶜ, u i *
        (if i < j then (max (x i - x j) δ)⁻¹ else -(max (x j - x i) δ)⁻¹) := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [dysonDriftTrunc, compl_singleton, ← mul_assoc, mul_comm (u i), mul_assoc, mul_sum]
  rw [hpull, ← sum_sum_Ioi_add_eq_sum_sum_off_diag
    (fun j i ↦ u i * if i < j then (max (x i - x j) δ)⁻¹ else -(max (x j - x i) δ)⁻¹)]
  congr 1
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j hj ↦ ?_
  have hij : i < j := mem_Ioi.1 hj
  simp only [hij, hij.not_gt, ↓reduceIte]
  ring

/-- The coordinates of `dysonDriftTrunc n δ x` sum to zero for every `δ` and `x`. -/
@[simp]
theorem sum_dysonDriftTrunc (n : ℕ) (δ : ℝ) (x : Fin n → ℝ) :
    ∑ i, dysonDriftTrunc n δ x i = 0 := by
  simpa using sum_mul_dysonDriftTrunc n δ (fun _ ↦ 1) x

private theorem inv_natCast_mul_abs_sum_erase_le {n : ℕ} (i : Fin n) {g : Fin n → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hg : ∀ j ∈ univ.erase i, |g j| ≤ C) :
    (n : ℝ)⁻¹ * |∑ j ∈ univ.erase i, g j| ≤ C := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 i.pos.ne'
  calc (n : ℝ)⁻¹ * |∑ j ∈ univ.erase i, g j|
      ≤ (n : ℝ)⁻¹ * ∑ j ∈ univ.erase i, |g j| := by gcongr; exact abs_sum_le_sum_abs _ _
    _ ≤ (n : ℝ)⁻¹ * (((univ.erase i).card : ℝ) * C) := by
        gcongr
        simpa using sum_le_card_nsmul (univ.erase i) (fun j ↦ |g j|) C hg
    _ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * C) := by
        gcongr
        exact_mod_cast (card_le_univ _).trans_eq (Fintype.card_fin n)
    _ = C := inv_mul_cancel_left₀ hn C

/-- For `0 < δ`, the sup norm of `dysonDriftTrunc n δ x` is at most `δ⁻¹` uniformly in `n` and
`x`. -/
theorem norm_dysonDriftTrunc_le (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (x : Fin n → ℝ) :
    ‖dysonDriftTrunc n δ x‖ ≤ δ⁻¹ := by
  refine (pi_norm_le_iff_of_nonneg (inv_nonneg.2 hδ.le)).2 fun i ↦ ?_
  rw [dysonDriftTrunc, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
  refine inv_natCast_mul_abs_sum_erase_le i (inv_nonneg.2 hδ.le) fun j _ ↦ ?_
  split_ifs
  · rw [abs_of_pos (inv_pos.2 (hδ.trans_le (le_max_right _ _)))]
    exact inv_anti₀ hδ (le_max_right _ _)
  · rw [abs_neg, abs_of_pos (inv_pos.2 (hδ.trans_le (le_max_right _ _)))]
    exact inv_anti₀ hδ (le_max_right _ _)

/-- **Global Lipschitz continuity of `dysonDriftTrunc`** for `0 < δ`, with constant `2 / δ²`
independent of the system size `n`. -/
theorem lipschitzWith_dysonDriftTrunc (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    LipschitzWith (2 / Real.toNNReal δ ^ 2) (dysonDriftTrunc n δ) := by
  set K : ℝ≥0 := 2 / Real.toNNReal δ ^ 2
  have hpair : ∀ p q : Fin n, LipschitzWith K (fun z : Fin n → ℝ ↦ (max (z p - z q) δ)⁻¹) := by
    intro p q
    have hsub : LipschitzWith 2 (fun z : Fin n → ℝ ↦ max (z p - z q) δ) := by
      simpa only [(by norm_num : (1 : ℝ≥0) + 1 = 2)] using
        ((LipschitzWith.eval (α := fun _ : Fin n ↦ ℝ) p).sub
          (LipschitzWith.eval (α := fun _ : Fin n ↦ ℝ) q)).max_const δ
    rw [← lipschitzOnWith_univ]
    exact hsub.lipschitzOnWith.inv_of_le_norm (Real.toNNReal_pos.2 hδ) fun z _ ↦ by
      rw [Real.coe_toNNReal δ hδ.le, Real.norm_eq_abs,
        abs_of_pos (hδ.trans_le (le_max_right _ _))]
      exact le_max_right _ _
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_
  rw [Pi.sub_apply, dysonDriftTrunc, dysonDriftTrunc, ← mul_sub, ← sum_sub_distrib,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
  refine inv_natCast_mul_abs_sum_erase_le i (by positivity) fun j _ ↦ ?_
  split_ifs
  · simpa only [Real.dist_eq] using (hpair i j).dist_le_mul x y
  · simpa only [Real.dist_eq, Pi.neg_apply] using (hpair j i).neg.dist_le_mul x y

/-- Continuity of `dysonDriftTrunc n δ` for `0 < δ`. -/
theorem continuous_dysonDriftTrunc (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (dysonDriftTrunc n δ) :=
  (lipschitzWith_dysonDriftTrunc n hδ).continuous

end TauCeti.Probability
