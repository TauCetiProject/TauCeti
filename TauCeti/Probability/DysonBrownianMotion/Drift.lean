/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Monoid
import TauCeti.Algebra.BigOperators.Finset.OffDiagonal
import TauCeti.Algebra.BigOperators.Finset.Pairs
import TauCeti.Analysis.Normed.Field.Lipschitz

/-!
# Repulsive drift of the Dyson particle system and its Lipschitz truncation

For `x : Fin n → ℝ`, the Dyson drift `dysonDrift x` has coordinates
`dysonDrift x i = n⁻¹ ∑_{j ≠ i} (x i - x j)⁻¹`. Pairing `dysonDrift x` against an arbitrary vector
`c : Fin n → ℝ` folds the off-diagonal sum onto strictly increasing index pairs:
`∑ i, c i * dysonDrift x i = n⁻¹ ∑_{i < j} (c i - c j) / (x i - x j)`. Specializing `c` yields:
* center-of-mass conservation `∑ i, dysonDrift x i = 0`;
* the virial identity `∑ i, x i * dysonDrift x i = (n - 1) / 2` for `n ≥ 1` and distinct particles;
* the monotonicity identity
  `∑ i, (dysonDrift x i - dysonDrift y i) * (x i - y i)`
  `= -n⁻¹ ∑_{i < j} ((x i - x j) - (y i - y j))² / ((x i - x j)(y i - y j))`,
  which is nonpositive on the open decreasing chamber `{x | StrictAnti x}`;
* the staircase bound `n⁻¹ ∑_{i < j} (x i - x j)⁻¹ ≤ -∑ i, i * dysonDrift x i` on the open chamber,
  which dominates all singular pairwise reciprocals by a linear combination of the drift.

To regularize collisions, `truncatedDysonDrift ε x` replaces each upper-triangular gap `x i - x j`
(`i < j`) by `max (x i - x j) ε` with opposite signs across the diagonal. It agrees with
`dysonDrift` whenever upper-triangular gaps are at least `ε`, preserves zero total drift and global
monotonicity on all of `Fin n → ℝ`, is uniformly bounded by `ε⁻¹`, and is globally Lipschitz with
constant `2 * ε⁻¹ ^ 2` for `ε > 0`.

## Main definitions

* `TauCeti.Probability.dysonDrift`: the pairwise repulsive drift `n⁻¹ ∑_{j ≠ i} (x i - x j)⁻¹`.
* `TauCeti.Probability.truncatedDysonDrift`: the `ε`-truncated repulsive drift.

## Main results

* `TauCeti.Probability.sum_mul_dysonDrift`: pairing identity over increasing index pairs.
* `TauCeti.Probability.sum_self_mul_dysonDrift` and
  `TauCeti.Probability.sum_self_mul_dysonDrift_of_pos`: the quadratic virial identity.
* `TauCeti.Probability.sum_sub_mul_dysonDrift_sub` and
  `TauCeti.Probability.sum_sub_mul_dysonDrift_sub_nonpos`: monotonicity of the Dyson drift on the
  open chamber.
* `TauCeti.Probability.sum_Ioi_inv_sub_le_neg_sum_natCast_mul_dysonDrift`: staircase domination of
  singular pairwise reciprocals.
* `TauCeti.Probability.truncatedDysonDrift_eq_dysonDrift`: exact agreement on the `ε`-separated
  chamber.
* `TauCeti.Probability.norm_truncatedDysonDrift_le` and
  `TauCeti.Probability.lipschitzWith_truncatedDysonDrift`: global boundedness and Lipschitz
  regularity of the truncated drift.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §4.3.1, Lemma 4.3.3 and Proposition 4.3.5.
-/

public section

noncomputable section

open Finset
open scoped NNReal

namespace TauCeti.Probability

section DysonDrift

variable {n : ℕ}

/-- The repulsive drift of the Dyson system of size `n` at configuration `x : Fin n → ℝ`,
with `i`-th coordinate `n⁻¹ ∑_{j ≠ i} (x i - x j)⁻¹`. -/
def dysonDrift (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j ∈ univ.erase i, (x i - x j)⁻¹

/-- Coordinate formula for `dysonDrift`. -/
theorem dysonDrift_apply (x : Fin n → ℝ) (i : Fin n) :
    dysonDrift x i = (n : ℝ)⁻¹ * ∑ j ∈ univ.erase i, (x i - x j)⁻¹ :=
  (rfl)

/-- For `n ≤ 1`, the Dyson drift vanishes identically. -/
@[simp]
theorem dysonDrift_of_subsingleton [Subsingleton (Fin n)] (x : Fin n → ℝ) :
    dysonDrift x = 0 := by
  ext i
  rw [dysonDrift_apply]
  have hempty : univ.erase i = ∅ := by
    ext j
    simp [Subsingleton.elim j i]
  simp [hempty]

/-- First coordinate of the two-particle Dyson drift. -/
@[simp]
theorem dysonDrift_fin_two_zero (x : Fin 2 → ℝ) :
    dysonDrift x 0 = 2⁻¹ * (x 0 - x 1)⁻¹ := by
  have herase : (univ : Finset (Fin 2)).erase 0 = {1} := by
    ext j
    fin_cases j <;> simp
  simp [dysonDrift_apply, herase]

/-- Second coordinate of the two-particle Dyson drift. -/
@[simp]
theorem dysonDrift_fin_two_one (x : Fin 2 → ℝ) :
    dysonDrift x 1 = -(2⁻¹ * (x 0 - x 1)⁻¹) := by
  have herase : (univ : Finset (Fin 2)).erase 1 = {0} := by
    ext j
    fin_cases j <;> simp
  simp only [dysonDrift_apply, herase, sum_singleton, Nat.cast_ofNat]
  rw [← neg_sub (x 0) (x 1), inv_neg, mul_neg]

/-- The Dyson drift vanishes on constant configurations (where self-differences are `0⁻¹ = 0`). -/
@[simp]
theorem dysonDrift_const (c : ℝ) : dysonDrift (fun _ : Fin n ↦ c) = 0 := by
  ext i
  simp [dysonDrift_apply]

/-- The Dyson drift vanishes at the origin. -/
@[simp]
theorem dysonDrift_zero : dysonDrift (0 : Fin n → ℝ) = 0 :=
  dysonDrift_const 0

/-- The Dyson drift is invariant under uniform spatial translation of all coordinates. -/
@[simp]
theorem dysonDrift_add_const (x : Fin n → ℝ) (c : ℝ) :
    dysonDrift (fun i ↦ x i + c) = dysonDrift x := by
  ext i
  simp [dysonDrift_apply, add_sub_add_right_eq_sub]

/-- The Dyson drift is odd under negation. -/
@[simp]
theorem dysonDrift_neg (x : Fin n → ℝ) : dysonDrift (-x) = -dysonDrift x := by
  ext i
  simp only [dysonDrift_apply, Pi.neg_apply]
  have hneg : ∀ j ∈ univ.erase i, (-x i - -x j)⁻¹ = -(x i - x j)⁻¹ := fun j _ ↦ by
    have hsub : -x i - -x j = -(x i - x j) := by ring
    rw [hsub, inv_neg]
  rw [sum_congr rfl hneg, sum_neg_distrib, mul_neg]

/-- The Dyson drift is homogeneous of degree `-1` under scalar multiplication, including at `0`. -/
theorem dysonDrift_smul (c : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    dysonDrift (c • x) i = c⁻¹ * dysonDrift x i := by
  simp only [dysonDrift_apply, Pi.smul_apply, smul_eq_mul, ← mul_sub, mul_inv, ← mul_sum]
  ring

/-- The Dyson drift is equivariant under permutations of the particle labels. -/
theorem dysonDrift_comp_equiv (σ : Fin n ≃ Fin n) (x : Fin n → ℝ) (i : Fin n) :
    dysonDrift (x ∘ σ) i = dysonDrift x (σ i) := by
  simp only [dysonDrift_apply, Function.comp_apply]
  congr 1
  refine sum_nbij' σ σ.symm ?_ ?_ (fun _ _ ↦ σ.symm_apply_apply _)
    (fun _ _ ↦ σ.apply_symm_apply _) (fun _ _ ↦ rfl)
  · intro j hj
    exact mem_erase.2 ⟨σ.injective.ne (mem_erase.1 hj).1, mem_univ _⟩
  · intro j hj
    refine mem_erase.2 ⟨fun h ↦ (mem_erase.1 hj).1 ?_, mem_univ _⟩
    simpa using congrArg σ h

/-- The sum of all coordinates of the Dyson drift vanishes for every configuration. -/
@[simp]
theorem sum_dysonDrift (x : Fin n → ℝ) : ∑ i, dysonDrift x i = 0 := by
  simp only [dysonDrift_apply, ← mul_sum]
  rw [univ.sum_sum_erase_eq_zero]
  · simp
  · intro i _ j _ _
    rw [← neg_sub (x i) (x j), inv_neg, add_neg_cancel]

/-- Pairing `dysonDrift x` with any vector `c` folds onto strictly increasing index pairs, with no
distinctness or ordering hypothesis on `x`. -/
theorem sum_mul_dysonDrift (c x : Fin n → ℝ) :
    ∑ i, c i * dysonDrift x i =
      (n : ℝ)⁻¹ * ∑ i, ∑ j ∈ Ioi i, (c i - c j) / (x i - x j) := by
  have herase (i : Fin n) :
      ∑ j ∈ univ.erase i, (x i - x j)⁻¹ = ∑ j, (x i - x j)⁻¹ := by
    rw [← add_sum_erase univ (fun j ↦ (x i - x j)⁻¹) (mem_univ i)]
    simp
  simp_rw [dysonDrift_apply, herase, ← mul_assoc, mul_comm (c _) (n : ℝ)⁻¹, mul_assoc, ← mul_sum]
  congr 1
  let F : Fin n × Fin n → ℝ := fun p ↦ c p.1 * (x p.1 - x p.2)⁻¹
  have hprod : (∑ i, c i * ∑ j, (x i - x j)⁻¹) = ∑ p : Fin n × Fin n, F p := by
    simp_rw [mul_sum]
    exact (Fintype.sum_prod_type F).symm
  rw [hprod, TauCeti.sum_univ_prod_eq_sum_lt_add_swap F (fun a ↦ by simp [F])]
  have hcombine : ∀ p ∈ ({p : Fin n × Fin n | p.1 < p.2} : Finset (Fin n × Fin n)),
      F p + F p.swap = (c p.1 - c p.2) / (x p.1 - x p.2) := by
    intro p _
    simp only [F, Prod.fst_swap, Prod.snd_swap]
    rw [← neg_sub (x p.1) (x p.2), inv_neg, mul_neg, div_eq_mul_inv]
    ring
  have hfilter : ({p : Fin n × Fin n | p.1 < p.2} : Finset (Fin n × Fin n)) =
      {p ∈ (univ : Finset (Fin n)) ×ˢ (univ : Finset (Fin n)) | p.1 < p.2} := rfl
  rw [sum_congr rfl hcombine, hfilter, sum_filter, sum_product]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← sum_filter]
  congr 1
  ext j
  simp

/-- **Virial identity for the Dyson drift.** For any configuration `x` with distinct coordinates,
`∑ i, x i * dysonDrift x i = n⁻¹ * n.choose 2`. -/
theorem sum_self_mul_dysonDrift {x : Fin n → ℝ} (hx : Function.Injective x) :
    ∑ i, x i * dysonDrift x i = (n : ℝ)⁻¹ * (n.choose 2 : ℝ) := by
  rw [sum_mul_dysonDrift]
  congr 1
  have hterm : ∀ i : Fin n, ∑ j ∈ Ioi i, (x i - x j) / (x i - x j) = #(Ioi i) := by
    intro i
    rw [sum_congr rfl fun j hj ↦ div_self (sub_ne_zero.2 (hx.ne (mem_Ioi.1 hj).ne))]
    simp
  simp_rw [hterm, ← Nat.cast_sum]
  congr 1
  have hcard : (∑ i : Fin n, #(Ioi i)) = #{p ∈ (univ : Finset (Fin n)) ×ˢ univ | p.1 < p.2} := by
    rw [card_filter, sum_product]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [← card_filter]
    congr 1
    ext j
    simp
  rw [hcard, card_product_filter_lt, card_univ, Fintype.card_fin]

/-- For `n ≥ 1` and distinct coordinates, `∑ i, x i * dysonDrift x i = (n - 1) / 2`. -/
theorem sum_self_mul_dysonDrift_of_pos (hn : 0 < n) {x : Fin n → ℝ} (hx : Function.Injective x) :
    ∑ i, x i * dysonDrift x i = ((n : ℝ) - 1) / 2 := by
  rw [sum_self_mul_dysonDrift hx, Nat.cast_choose_two]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  field_simp [hn']

/-- **Monotonicity identity for the Dyson drift.** For configurations `x` and `y` with distinct
coordinates, the inner product of `dysonDrift x - dysonDrift y` with `x - y` equals
`-n⁻¹ ∑_{i < j} ((x i - x j) - (y i - y j))² / ((x i - x j)(y i - y j))`. -/
theorem sum_sub_mul_dysonDrift_sub {x y : Fin n → ℝ} (hx : Function.Injective x)
    (hy : Function.Injective y) :
    ∑ i, (dysonDrift x i - dysonDrift y i) * (x i - y i) =
      -(n : ℝ)⁻¹ * ∑ i, ∑ j ∈ Ioi i,
        ((x i - x j) - (y i - y j)) ^ 2 / ((x i - x j) * (y i - y j)) := by
  have hsplit : ∑ i, (dysonDrift x i - dysonDrift y i) * (x i - y i) =
      (∑ i, (x - y) i * dysonDrift x i) - ∑ i, (x - y) i * dysonDrift y i := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ ↦ by simp only [Pi.sub_apply]; ring
  rw [hsplit, sum_mul_dysonDrift (x - y) x, sum_mul_dysonDrift (x - y) y, ← mul_sub, neg_mul,
    ← mul_neg]
  congr 1
  rw [← sum_sub_distrib, ← sum_neg_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← sum_sub_distrib, ← sum_neg_distrib]
  refine sum_congr rfl fun j hj ↦ ?_
  simp only [Pi.sub_apply]
  have hij : i ≠ j := (mem_Ioi.1 hj).ne
  have hdx : x i - x j ≠ 0 := sub_ne_zero.2 (hx.ne hij)
  have hdy : y i - y j ≠ 0 := sub_ne_zero.2 (hy.ne hij)
  field_simp [hdx, hdy]
  ring

/-- On the open decreasing chamber `{x | StrictAnti x}`, the Dyson drift is dissipative
(monotone with nonpositive inner product). -/
theorem sum_sub_mul_dysonDrift_sub_nonpos {x y : Fin n → ℝ} (hx : StrictAnti x)
    (hy : StrictAnti y) :
    ∑ i, (dysonDrift x i - dysonDrift y i) * (x i - y i) ≤ 0 := by
  rw [sum_sub_mul_dysonDrift_sub hx.injective hy.injective]
  refine mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity)) ?_
  refine sum_nonneg fun i _ ↦ sum_nonneg fun j hj ↦ ?_
  have hij : i < j := mem_Ioi.1 hj
  have hdx : 0 < x i - x j := sub_pos.2 (hx hij)
  have hdy : 0 < y i - y j := sub_pos.2 (hy hij)
  positivity

example :
    ∑ i : Fin 2, (dysonDrift ![2, 0] i - dysonDrift ![1, 0] i) *
      ((![2, 0] : Fin 2 → ℝ) i - (![1, 0] : Fin 2 → ℝ) i) = -1 / 4 := by
  rw [Fin.sum_univ_two]
  simp only [dysonDrift_fin_two_zero, dysonDrift_fin_two_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  norm_num

/-- **Staircase bound on singular pairwise reciprocals.** On the open decreasing chamber
`{x | StrictAnti x}`, the sum of all positive gap reciprocals `n⁻¹ ∑_{i < j} (x i - x j)⁻¹` is
bounded above by `-∑ i, i * dysonDrift x i`. -/
theorem sum_Ioi_inv_sub_le_neg_sum_natCast_mul_dysonDrift {x : Fin n → ℝ} (hx : StrictAnti x) :
    (n : ℝ)⁻¹ * ∑ i, ∑ j ∈ Ioi i, (x i - x j)⁻¹ ≤
      -∑ i : Fin n, (i : ℝ) * dysonDrift x i := by
  have heq : -∑ i : Fin n, (i : ℝ) * dysonDrift x i =
      ∑ i : Fin n, (-(i : ℝ)) * dysonDrift x i := by
    simp [neg_mul, sum_neg_distrib]
  rw [heq, sum_mul_dysonDrift]
  gcongr with i _ j hj
  have hij : i < j := mem_Ioi.1 hj
  have hgap : 0 < x i - x j := sub_pos.2 (hx hij)
  have hnum : (1 : ℝ) ≤ -(i : ℝ) - -(j : ℝ) := by
    have h1 : (i : ℕ) + 1 ≤ (j : ℕ) := hij
    have h2 : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  simpa only [one_div] using div_le_div_of_nonneg_right hnum hgap.le

/-- The Dyson drift is continuous on the set of configurations with distinct coordinates. -/
theorem continuousOn_dysonDrift :
    ContinuousOn (dysonDrift (n := n)) {x : Fin n → ℝ | Function.Injective x} := by
  rw [continuousOn_pi]
  intro i
  refine ContinuousOn.mul continuousOn_const (continuousOn_finsetSum _ fun j hj ↦ ?_)
  exact ((continuous_apply i).sub (continuous_apply j)).continuousOn.inv₀ fun x hx ↦
    sub_ne_zero.2 (hx.ne (mem_erase.1 hj).1.symm)

end DysonDrift

section TruncatedDysonDrift

variable {n : ℕ}

/-- The `ε`-truncated Dyson drift on `Fin n → ℝ`: for `i < j` the repulsive interaction
`(x i - x j)⁻¹` is truncated to `(max (x i - x j) ε)⁻¹`, and for `j < i` to
`-(max (x j - x i) ε)⁻¹`. -/
def truncatedDysonDrift (ε : ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j ∈ univ.erase i,
    if i < j then (max (x i - x j) ε)⁻¹ else -(max (x j - x i) ε)⁻¹

/-- Coordinate formula for `truncatedDysonDrift`. -/
theorem truncatedDysonDrift_apply (ε : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    truncatedDysonDrift ε x i = (n : ℝ)⁻¹ * ∑ j ∈ univ.erase i,
      if i < j then (max (x i - x j) ε)⁻¹ else -(max (x j - x i) ε)⁻¹ :=
  (rfl)

/-- For `n ≤ 1`, the truncated Dyson drift vanishes identically. -/
@[simp]
theorem truncatedDysonDrift_of_subsingleton [Subsingleton (Fin n)] (ε : ℝ) (x : Fin n → ℝ) :
    truncatedDysonDrift ε x = 0 := by
  ext i
  rw [truncatedDysonDrift_apply]
  have hempty : univ.erase i = ∅ := by
    ext j
    simp [Subsingleton.elim j i]
  simp [hempty]

/-- The truncated Dyson drift is invariant under uniform spatial translation of all coordinates. -/
@[simp]
theorem truncatedDysonDrift_add_const (ε : ℝ) (x : Fin n → ℝ) (c : ℝ) :
    truncatedDysonDrift ε (fun i ↦ x i + c) = truncatedDysonDrift ε x := by
  ext i
  simp [truncatedDysonDrift_apply, add_sub_add_right_eq_sub]

/-- On the `ε`-separated chamber `{x | ∀ i < j, ε ≤ x i - x j}`, `truncatedDysonDrift ε x` agrees
with `dysonDrift x`. -/
theorem truncatedDysonDrift_eq_dysonDrift {ε : ℝ} {x : Fin n → ℝ}
    (hx : ∀ ⦃i j : Fin n⦄, i < j → ε ≤ x i - x j) :
    truncatedDysonDrift ε x = dysonDrift x := by
  ext i
  simp only [truncatedDysonDrift_apply, dysonDrift_apply]
  congr 1
  refine sum_congr rfl fun j hj ↦ ?_
  rcases lt_or_gt_of_ne (mem_erase.1 hj).1.symm with hij | hji
  · simp [hij, max_eq_left (hx hij)]
  · simp only [hji.not_gt, ↓reduceIte, max_eq_left (hx hji)]
    rw [← neg_sub (x j) (x i), inv_neg]

/-- The sum of all coordinates of the truncated Dyson drift vanishes for every configuration. -/
@[simp]
theorem sum_truncatedDysonDrift (ε : ℝ) (x : Fin n → ℝ) :
    ∑ i, truncatedDysonDrift ε x i = 0 := by
  simp only [truncatedDysonDrift_apply, ← mul_sum]
  rw [univ.sum_sum_erase_eq_zero]
  · simp
  · intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with h | h
    · simp [h, h.not_gt]
    · simp [h, h.not_gt]

/-- Pairing `truncatedDysonDrift ε x` with any vector `c` folds onto strictly increasing index
pairs. -/
theorem sum_mul_truncatedDysonDrift (ε : ℝ) (c x : Fin n → ℝ) :
    ∑ i, c i * truncatedDysonDrift ε x i =
      (n : ℝ)⁻¹ * ∑ i, ∑ j ∈ Ioi i, (c i - c j) * (max (x i - x j) ε)⁻¹ := by
  let g : Fin n × Fin n → ℝ := fun p ↦
    if p.1 = p.2 then 0
    else if p.1 < p.2 then (max (x p.1 - x p.2) ε)⁻¹
    else -(max (x p.2 - x p.1) ε)⁻¹
  have herase (i : Fin n) :
      (∑ j ∈ univ.erase i,
        if i < j then (max (x i - x j) ε)⁻¹ else -(max (x j - x i) ε)⁻¹) =
        ∑ j, g (i, j) := by
    rw [← add_sum_erase univ (fun j ↦ g (i, j)) (mem_univ i)]
    simp only [g, ↓reduceIte, zero_add]
    exact sum_congr rfl fun j hj ↦ by simp [(mem_erase.1 hj).1.symm]
  simp_rw [truncatedDysonDrift_apply, herase, ← mul_assoc, mul_comm (c _) (n : ℝ)⁻¹, mul_assoc,
    ← mul_sum]
  congr 1
  let F : Fin n × Fin n → ℝ := fun p ↦ c p.1 * g p
  have hprod : (∑ i, c i * ∑ j, g (i, j)) = ∑ p : Fin n × Fin n, F p := by
    simp_rw [mul_sum]
    exact (Fintype.sum_prod_type F).symm
  rw [hprod, TauCeti.sum_univ_prod_eq_sum_lt_add_swap F (fun a ↦ by simp [F, g])]
  have hcombine : ∀ p ∈ ({p : Fin n × Fin n | p.1 < p.2} : Finset (Fin n × Fin n)),
      F p + F p.swap = (c p.1 - c p.2) * (max (x p.1 - x p.2) ε)⁻¹ := by
    intro p hp
    have hlt : p.1 < p.2 := by simpa using hp
    simp only [F, g, Prod.fst_swap, Prod.snd_swap, hlt.ne, hlt.ne', hlt, hlt.not_gt, ↓reduceIte]
    ring
  have hfilter : ({p : Fin n × Fin n | p.1 < p.2} : Finset (Fin n × Fin n)) =
      {p ∈ (univ : Finset (Fin n)) ×ˢ (univ : Finset (Fin n)) | p.1 < p.2} := rfl
  rw [sum_congr rfl hcombine, hfilter, sum_filter, sum_product]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← sum_filter]
  congr 1
  ext j
  simp

/-- For `ε > 0`, `truncatedDysonDrift ε` is globally dissipative on all of `Fin n → ℝ`, with no
chamber restriction on `x` or `y`. -/
theorem sum_sub_mul_truncatedDysonDrift_sub_nonpos {ε : ℝ} (hε : 0 < ε) (x y : Fin n → ℝ) :
    ∑ i, (truncatedDysonDrift ε x i - truncatedDysonDrift ε y i) * (x i - y i) ≤ 0 := by
  have hsplit : ∑ i, (truncatedDysonDrift ε x i - truncatedDysonDrift ε y i) * (x i - y i) =
      (∑ i, (x - y) i * truncatedDysonDrift ε x i) -
        ∑ i, (x - y) i * truncatedDysonDrift ε y i := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ ↦ by simp only [Pi.sub_apply]; ring
  rw [hsplit, sum_mul_truncatedDysonDrift ε (x - y) x, sum_mul_truncatedDysonDrift ε (x - y) y]
  simp only [Pi.sub_apply, ← mul_sub, ← sum_sub_distrib]
  refine mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (sum_nonpos fun i _ ↦ sum_nonpos fun j _ ↦ ?_)
  set a := x i - x j
  set b := y i - y j
  have hsub : x i - y i - (x j - y j) = a - b := by ring
  rw [hsub]
  have ha : 0 < max a ε := hε.trans_le (le_max_right a ε)
  have hb : 0 < max b ε := hε.trans_le (le_max_right b ε)
  rcases le_total a b with hab | hba
  · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hab)
      (sub_nonneg.2 (inv_anti₀ ha (max_le_max_right ε hab)))
  · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hba)
      (sub_nonpos.2 (inv_anti₀ hb (max_le_max_right ε hba)))

/-- Each coordinate of `truncatedDysonDrift ε x` is bounded in absolute value by `ε⁻¹` when
`ε > 0`. -/
theorem abs_truncatedDysonDrift_le {ε : ℝ} (hε : 0 < ε) (x : Fin n → ℝ) (i : Fin n) :
    |truncatedDysonDrift ε x i| ≤ ε⁻¹ := by
  rw [truncatedDysonDrift_apply, abs_mul, abs_of_nonneg (by positivity)]
  refine (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)).trans ?_
  have hterm : ∀ j ∈ univ.erase i,
      |if i < j then (max (x i - x j) ε)⁻¹ else -(max (x j - x i) ε)⁻¹| ≤ ε⁻¹ := by
    intro j _
    split_ifs with h
    · rw [abs_of_pos (inv_pos.2 (hε.trans_le (le_max_right _ _)))]
      exact inv_anti₀ hε (le_max_right _ _)
    · rw [abs_neg, abs_of_pos (inv_pos.2 (hε.trans_le (le_max_right _ _)))]
      exact inv_anti₀ hε (le_max_right _ _)
  have hcard : (n : ℝ)⁻¹ * (#(univ.erase i) : ℝ) ≤ 1 := by
    calc (n : ℝ)⁻¹ * (#(univ.erase i) : ℝ)
      _ ≤ (n : ℝ)⁻¹ * (n : ℝ) := by gcongr; simp
      _ ≤ 1 := by
          rcases eq_or_ne n 0 with rfl | hn
          · simp
          · rw [inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn)]
  calc
    (n : ℝ)⁻¹ * ∑ j ∈ univ.erase i,
        |if i < j then (max (x i - x j) ε)⁻¹ else -(max (x j - x i) ε)⁻¹|
      ≤ (n : ℝ)⁻¹ * ∑ _j ∈ univ.erase i, ε⁻¹ := by gcongr; exact hterm _ ‹_›
    _ = ((n : ℝ)⁻¹ * (#(univ.erase i) : ℝ)) * ε⁻¹ := by simp [mul_assoc]
    _ ≤ 1 * ε⁻¹ := by gcongr
    _ = ε⁻¹ := one_mul _

/-- In the `Pi` supremum norm on `Fin n → ℝ`, `‖truncatedDysonDrift ε x‖ ≤ ε⁻¹` for `ε > 0`. -/
theorem norm_truncatedDysonDrift_le {ε : ℝ} (hε : 0 < ε) (x : Fin n → ℝ) :
    ‖truncatedDysonDrift ε x‖ ≤ ε⁻¹ :=
  (pi_norm_le_iff_of_nonneg (inv_nonneg.2 hε.le)).2 fun i ↦ by
    simpa only [Real.norm_eq_abs] using abs_truncatedDysonDrift_le hε x i

/-- For `ε > 0`, `truncatedDysonDrift ε` is globally Lipschitz on `Fin n → ℝ` with Lipschitz
constant `2 * ε⁻¹ ^ 2`. -/
theorem lipschitzWith_truncatedDysonDrift {ε : ℝ≥0} (hε : 0 < ε) :
    LipschitzWith (2 * ε⁻¹ ^ 2) (truncatedDysonDrift (ε : ℝ) (n := n)) := by
  set K : ℝ≥0 := 2 * ε⁻¹ ^ 2
  have htwo : (1 + 1 : ℝ≥0) = 2 := one_add_one_eq_two
  have hpair (i j : Fin n) :
      LipschitzWith K (fun x : Fin n → ℝ ↦ (max (x i - x j) (ε : ℝ))⁻¹) := by
    have hdiff : LipschitzWith 2 (fun x : Fin n → ℝ ↦ x i - x j) := by
      simpa only [htwo] using
        (LipschitzWith.eval (α := fun _ : Fin n ↦ ℝ) i).sub
          (LipschitzWith.eval (α := fun _ : Fin n ↦ ℝ) j)
    have hmax : LipschitzWith 2 (fun x : Fin n → ℝ ↦ max (x i - x j) (ε : ℝ)) := by
      simpa only [max_eq_left (zero_le : (0 : ℝ≥0) ≤ 2)] using
        hdiff.max (LipschitzWith.const (ε : ℝ))
    have hinv := (lipschitzOnWith_univ.2 hmax).inv_of_le_norm hε fun x _ ↦ by
      rw [Real.norm_of_nonneg ((NNReal.coe_pos.2 hε).le.trans (le_max_right _ _))]
      exact le_max_right _ _
    simpa only [lipschitzOnWith_univ, div_eq_mul_inv, inv_pow, K] using hinv
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [dist_pi_le_iff (by positivity)]
  intro i
  rw [Real.dist_eq, truncatedDysonDrift_apply, truncatedDysonDrift_apply, ← mul_sub, abs_mul,
    abs_of_nonneg (by positivity), ← sum_sub_distrib]
  have hterm : ∀ j ∈ univ.erase i,
      |(if i < j then (max (x i - x j) (ε : ℝ))⁻¹ else -(max (x j - x i) (ε : ℝ))⁻¹) -
        (if i < j then (max (y i - y j) (ε : ℝ))⁻¹ else -(max (y j - y i) (ε : ℝ))⁻¹)| ≤
        (K : ℝ) * dist x y := by
    intro j _
    split_ifs with h
    · simpa only [Real.dist_eq] using (hpair i j).dist_le_mul x y
    · simpa only [Real.dist_eq, neg_sub_neg, abs_sub_comm] using (hpair j i).dist_le_mul x y
  have hcard : (n : ℝ)⁻¹ * (#(univ.erase i) : ℝ) ≤ 1 := by
    calc (n : ℝ)⁻¹ * (#(univ.erase i) : ℝ)
      _ ≤ (n : ℝ)⁻¹ * (n : ℝ) := by gcongr; simp
      _ ≤ 1 := by
          rcases eq_or_ne n 0 with rfl | hn
          · simp
          · rw [inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn)]
  calc
    (n : ℝ)⁻¹ * |∑ j ∈ univ.erase i,
        ((if i < j then (max (x i - x j) (ε : ℝ))⁻¹ else -(max (x j - x i) (ε : ℝ))⁻¹) -
          (if i < j then (max (y i - y j) (ε : ℝ))⁻¹ else -(max (y j - y i) (ε : ℝ))⁻¹))|
      ≤ (n : ℝ)⁻¹ * ∑ _j ∈ univ.erase i, ((K : ℝ) * dist x y) := by
          refine (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)).trans ?_
          gcongr
          exact hterm _ ‹_›
    _ = ((n : ℝ)⁻¹ * (#(univ.erase i) : ℝ)) * ((K : ℝ) * dist x y) := by simp [mul_assoc]
    _ ≤ 1 * ((K : ℝ) * dist x y) := by gcongr
    _ = (K : ℝ) * dist x y := one_mul _

/-- For `ε > 0`, `truncatedDysonDrift ε` is continuous on `Fin n → ℝ`. -/
theorem continuous_truncatedDysonDrift {ε : ℝ} (hε : 0 < ε) :
    Continuous (truncatedDysonDrift ε (n := n)) :=
  (lipschitzWith_truncatedDysonDrift (ε := ⟨ε, hε.le⟩) hε).continuous

end TruncatedDysonDrift

end TauCeti.Probability
