/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Field
import TauCeti.Algebra.BigOperators.Finset.Pairs

/-!
# Repulsive Coulomb drift of Dyson Brownian motion and its chamber truncations

For `n` particles `x : Fin n → ℝ`, the normalized Dyson drift at coordinate `i` is
`dysonDrift n x i = n⁻¹ * ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹`. It is the gradient of the
normalized logarithmic Vandermonde potential `n⁻¹ * ∑_{i < j} log |x i - x j|`, singular along the
collision hyperplanes `x i = x j` and smooth on the open decreasing Weyl chamber
`{x : Fin n → ℝ | StrictAnti x}`.

Because `(x j - x i)⁻¹ = -(x i - x j)⁻¹`, pairing `dysonDrift n x` against any weight `w` folds
over ordered pairs `i < j`. This single antisymmetric pairing formula yields conservation of the
center of mass (`sum_dysonDrift_eq_zero`), the virial identity (`sum_self_mul_dysonDrift`), the
Rogers–Shi entrance-weight inequality (`mul_sum_Ioi_sub_inv_le_sum_sub_two_mul_mul_dysonDrift`), and
monotone dissipativity (`sum_dysonDrift_sub_mul_sub_nonpos`) on the open chamber. Squaring the drift
and applying the three-term partial-fraction identity `(a - b)⁻¹ (a - c)⁻¹ + cyclic = 0` yields the
Calogero–Moser identity `sum_dysonDrift_sq`, which governs the drift of the logarithmic
Vandermonde potential in the noncollision proof for `β ≥ 1`.

To construct Dyson trajectories up to chamber exit via standard globally Lipschitz ODE theory, we
also define the `ε`-truncated drift `truncatedDysonDrift ε n`, obtained by clamping each ordered
gap `x i - x j` (`i < j`) below at `ε > 0`. It agrees with `dysonDrift n` on the `ε`-interior of
the chamber while remaining globally bounded, `2 ε⁻²`-Lipschitz in the supremum norm (uniformly in
`n`), centered, equivariant under positive rescaling and chamber-preserving reflection
`(-x) ∘ Fin.revPerm`, and monotonically dissipative on all of `Fin n → ℝ`.

## Main declarations

* `TauCeti.Probability.dysonDrift`: the singular Coulomb repulsion drift on `Fin n → ℝ`, with
  permutation equivariance `TauCeti.Probability.dysonDrift_comp_equiv` and continuity
  `TauCeti.Probability.continuousOn_dysonDrift`.
* `TauCeti.Probability.sum_mul_dysonDrift_eq_sum_Ioi`: antisymmetric pairing over `i < j`.
* `TauCeti.Probability.sum_dysonDrift_eq_zero`,
  `TauCeti.Probability.sum_self_mul_dysonDrift_eq_inv_mul_choose`, and
  `TauCeti.Probability.sum_self_mul_dysonDrift`: first- and second-moment identities.
* `TauCeti.Probability.sum_dysonDrift_sub_mul_sub_nonpos`: monotone dissipativity on the chamber.
* `TauCeti.Probability.sum_dysonDrift_sub_mul_comp_sub_nonpos` and
  `TauCeti.Probability.sum_dysonDrift_sub_mul_max_sub_zero_nonpos`: dissipativity against monotone
  test functions of `x - y`, including the positive part.
* `TauCeti.Probability.sum_dysonDrift_sub_mul_comp_sub_nonpos_of_pairwise` and
  `TauCeti.Probability.sum_dysonDrift_sub_mul_sub_nonpos_of_pairwise`: the same dissipativity on
  any common open Weyl chamber.
* `TauCeti.Probability.mul_sum_Ioi_sub_inv_le_sum_sub_two_mul_mul_dysonDrift`: entrance-weight lower
  bound.
* `TauCeti.Probability.sum_dysonDrift_sq`: Calogero–Moser partial-fraction identity.
* `TauCeti.Probability.truncatedDysonDrift`,
  `TauCeti.Probability.truncatedDysonDrift_neg_comp_revPerm`,
  `TauCeti.Probability.truncatedDysonDrift_smul`, and
  `TauCeti.Probability.lipschitzWith_truncatedDysonDrift`: globally Lipschitz `ε`-truncation and
  its symmetries.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010, §4.3.1.
* L. C. G. Rogers, Z. Shi, *Interacting Brownian particles and the Wigner law*, Probab. Theory
  Related Fields 95 (1993), 555–570.
* E. Cépa, D. Lépingle, *Diffusing particles with electrostatic repulsion*, Probab. Theory Related
  Fields 107 (1997), 429–449.
-/

public section

open scoped NNReal

namespace TauCeti.Probability

/-! ### Private pairing helpers -/

private theorem sum_erase_sub_inv_eq_sub {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    (∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹) =
      (∑ j ∈ Finset.Ioi i, (x i - x j)⁻¹) - ∑ j ∈ Finset.Iio i, (x j - x i)⁻¹ := by
  rw [Finset.sum_erase_univ_eq_sum_Ioi_add_sum_Iio, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  exact congrArg _ (Finset.sum_congr rfl fun j _ ↦ by rw [← neg_sub (x j) (x i), inv_neg])

private theorem sum_sub_mul_sub_of_sum_mul_eq_sum_Ioi {n : ℕ} {D : (Fin n → ℝ) → Fin n → ℝ}
    {K : ℝ → ℝ}
    (hpair : ∀ w z : Fin n → ℝ, ∑ i : Fin n, w i * D z i =
      (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, (w i - w j) * K (z i - z j))
    (x y : Fin n → ℝ) :
    ∑ i : Fin n, (D x i - D y i) * (x i - y i) =
      (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
        ((x i - x j) - (y i - y j)) * (K (x i - x j) - K (y i - y j)) := by
  have hlhs : ∑ i : Fin n, (D x i - D y i) * (x i - y i) =
      (∑ i : Fin n, (x i - y i) * D x i) - ∑ i : Fin n, (x i - y i) * D y i := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [hlhs, hpair _ x, hpair _ y, ← mul_sub, ← Finset.sum_sub_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-! ### The singular Dyson drift -/

/-- **Normalized repulsive Coulomb drift of the `n`-particle Dyson system.** At configuration
`x : Fin n → ℝ` and coordinate `i : Fin n`, this is
`n⁻¹ * ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹`. -/
noncomputable def dysonDrift (n : ℕ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹

/-- Coordinate evaluation of `dysonDrift`. -/
theorem dysonDrift_apply (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    dysonDrift n x i = (n : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹ :=
  (rfl)

/-- Since `(0 : ℝ)⁻¹ = 0`, the diagonal `j = i` term vanishes automatically and `dysonDrift` may be
written as an unrestricted sum over `Fin n`. -/
theorem dysonDrift_eq_inv_mul_sum (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    dysonDrift n x i = (n : ℝ)⁻¹ * ∑ j : Fin n, (x i - x j)⁻¹ := by
  rw [dysonDrift_apply, ← Finset.add_sum_erase Finset.univ (fun j ↦ (x i - x j)⁻¹)
    (Finset.mem_univ i), sub_self, inv_zero, zero_add]

/-- For at most one particle (`n ≤ 1`), there is no pairwise repulsion and `dysonDrift n = 0`. -/
theorem dysonDrift_of_le_one {n : ℕ} (hn : n ≤ 1) : dysonDrift n = 0 := by
  have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.2 hn
  ext x i
  have hempty : Finset.univ.erase i = ∅ := by ext j; simp [Subsingleton.elim j i]
  simp [dysonDrift_apply, hempty]

/-- The Dyson drift of an empty particle system vanishes. -/
@[simp]
theorem dysonDrift_zero : dysonDrift 0 = 0 := dysonDrift_of_le_one (Nat.zero_le 1)

/-- A single particle experiences no pairwise repulsion. -/
@[simp]
theorem dysonDrift_one : dysonDrift 1 = 0 := dysonDrift_of_le_one le_rfl

/-- Shifting every coordinate by the same constant leaves `dysonDrift` unchanged. -/
@[simp]
theorem dysonDrift_add_const (n : ℕ) (x : Fin n → ℝ) (c : ℝ) :
    dysonDrift n (fun i ↦ x i + c) = dysonDrift n x := by
  ext i; simp [dysonDrift]

/-- Rescaling a configuration by `c : ℝ` rescales `dysonDrift` by `c⁻¹` (including at `c = 0`). -/
theorem dysonDrift_smul (n : ℕ) (c : ℝ) (x : Fin n → ℝ) :
    dysonDrift n (c • x) = c⁻¹ • dysonDrift n x := by
  ext i
  simp only [dysonDrift, Pi.smul_apply, smul_eq_mul, ← mul_sub, mul_inv, ← Finset.mul_sum]
  ring

/-- At any constant configuration `fun _ ↦ c`, `dysonDrift` vanishes identically. -/
@[simp]
theorem dysonDrift_fun_const (n : ℕ) (c : ℝ) : dysonDrift n (fun _ ↦ c) = 0 := by
  ext i; simp [dysonDrift]

/-- Reflecting all coordinates negates `dysonDrift`. -/
@[simp]
theorem dysonDrift_neg (n : ℕ) (x : Fin n → ℝ) :
    dysonDrift n (-x) = -dysonDrift n x := by
  ext i
  simp only [dysonDrift, Pi.neg_apply, ← mul_neg, ← Finset.sum_neg_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [show -x i - -x j = -(x i - x j) by ring, inv_neg]

/-- Permuting particle labels commutes with `dysonDrift`: evaluating at `x ∘ σ` permutes the
output coordinates by `σ`. -/
theorem dysonDrift_comp_equiv (n : ℕ) (σ : Fin n ≃ Fin n) (x : Fin n → ℝ) :
    dysonDrift n (x ∘ σ) = dysonDrift n x ∘ σ := by
  ext i
  simp only [dysonDrift_eq_inv_mul_sum, Function.comp_apply]
  exact congrArg _ (Equiv.sum_comp σ fun j ↦ (x (σ i) - x j)⁻¹)

/-- First coordinate of the two-particle Dyson drift. -/
theorem dysonDrift_two_zero (x : Fin 2 → ℝ) :
    dysonDrift 2 x 0 = (2 * (x 0 - x 1))⁻¹ := by
  have herase : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  rw [dysonDrift, herase, Finset.sum_singleton, mul_inv]
  norm_num

/-- Second coordinate of the two-particle Dyson drift. -/
theorem dysonDrift_two_one (x : Fin 2 → ℝ) :
    dysonDrift 2 x 1 = -(2 * (x 0 - x 1))⁻¹ := by
  have herase : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  rw [dysonDrift, herase, Finset.sum_singleton, ← neg_sub (x 0) (x 1), inv_neg, mul_neg, mul_inv]
  norm_num

/-- `dysonDrift n` is continuous at every configuration with pairwise distinct coordinates. -/
theorem continuousAt_dysonDrift {n : ℕ} {x : Fin n → ℝ} (hx : Function.Injective x) :
    ContinuousAt (dysonDrift n) x :=
  continuousAt_pi.2 fun i ↦ ContinuousAt.mul continuousAt_const <|
    tendsto_finsetSum _ fun j hj ↦ ((continuousAt_apply i _).sub (continuousAt_apply j _)).inv₀
      (sub_ne_zero.2 (hx.ne (Finset.ne_of_mem_erase hj).symm))

/-- `dysonDrift n` is continuous on the set of configurations with pairwise distinct coordinates. -/
theorem continuousOn_dysonDrift (n : ℕ) :
    ContinuousOn (dysonDrift n) {x : Fin n → ℝ | Function.Injective x} :=
  fun _ hx ↦ (continuousAt_dysonDrift hx).continuousWithinAt

/-! ### Antisymmetric pairing and algebraic identities -/

/-- **Antisymmetric pairing formula for `dysonDrift`.** Pairing `dysonDrift n x` against any weight
`w : Fin n → ℝ` folds over ordered index pairs `i < j`. -/
theorem sum_mul_dysonDrift_eq_sum_Ioi (n : ℕ) (w x : Fin n → ℝ) :
    ∑ i : Fin n, w i * dysonDrift n x i =
      (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, (w i - w j) * (x i - x j)⁻¹ := by
  simp_rw [dysonDrift_apply, sum_erase_sub_inv_eq_sub, ← mul_left_comm (n : ℝ)⁻¹,
    ← Finset.mul_sum, Finset.sum_mul_sum_Ioi_sub_sum_Iio]

/-- **Center-of-mass conservation.** The coordinates of `dysonDrift n x` sum to `0` for every
configuration `x`. -/
@[simp]
theorem sum_dysonDrift_eq_zero (n : ℕ) (x : Fin n → ℝ) :
    ∑ i : Fin n, dysonDrift n x i = 0 := by
  simpa using sum_mul_dysonDrift_eq_sum_Ioi n (fun _ ↦ 1) x

/-- **Virial identity for all `n` (including `n = 0`).** For every `n : ℕ` and any configuration
`x : Fin n → ℝ` with distinct coordinates, `∑ i, x i * dysonDrift n x i = n⁻¹ * n.choose 2`. -/
theorem sum_self_mul_dysonDrift_eq_inv_mul_choose {n : ℕ} {x : Fin n → ℝ}
    (hx : Function.Injective x) :
    ∑ i : Fin n, x i * dysonDrift n x i = (n : ℝ)⁻¹ * (n.choose 2 : ℝ) := by
  rw [sum_mul_dysonDrift_eq_sum_Ioi]
  have hones (i : Fin n) : ∑ j ∈ Finset.Ioi i, (x i - x j) * (x i - x j)⁻¹ =
      (Finset.Ioi i).card := by
    rw [Finset.sum_congr rfl fun j hj ↦
      mul_inv_cancel₀ (sub_ne_zero.2 (hx.ne (Finset.mem_Ioi.1 hj).ne))]
    simp
  simp_rw [hones, ← Nat.cast_sum]
  refine congrArg _ (congrArg Nat.cast ?_)
  have hcard : (∑ i : Fin n, (Finset.Ioi i).card) =
      (((Finset.univ : Finset (Fin n)) ×ˢ Finset.univ).filter fun p ↦ p.1 < p.2).card := by
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.card_filter]
    exact congrArg Finset.card (by ext j; simp)
  rw [hcard, Finset.card_product_filter_lt, Finset.card_univ, Fintype.card_fin]

/-- **Virial identity.** At any configuration with distinct coordinates (`n ≥ 1`), pairing `x`
with `dysonDrift n x` gives `(n - 1) / 2`. -/
theorem sum_self_mul_dysonDrift {n : ℕ} (hn : 0 < n) {x : Fin n → ℝ}
    (hx : Function.Injective x) :
    ∑ i : Fin n, x i * dysonDrift n x i = ((n : ℝ) - 1) / 2 := by
  rw [sum_self_mul_dysonDrift_eq_inv_mul_choose hx, Nat.cast_choose_two]
  have hn₀ : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  field_simp [hn₀]

/-- Difference pairing identity for `dysonDrift` at arbitrary configurations `x` and `y`. -/
theorem sum_dysonDrift_sub_mul_sub_eq_sum_Ioi (n : ℕ) (x y : Fin n → ℝ) :
    ∑ i : Fin n, (dysonDrift n x i - dysonDrift n y i) * (x i - y i) =
      (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
        ((x i - x j) - (y i - y j)) * ((x i - x j)⁻¹ - (y i - y j)⁻¹) :=
  sum_sub_mul_sub_of_sum_mul_eq_sum_Ioi (sum_mul_dysonDrift_eq_sum_Ioi n) x y

/-- Explicit negative-square formula for the drift difference pairing on configurations with
pairwise distinct coordinates. -/
theorem sum_dysonDrift_sub_mul_sub {n : ℕ} {x y : Fin n → ℝ}
    (hx : Function.Injective x) (hy : Function.Injective y) :
    ∑ i : Fin n, (dysonDrift n x i - dysonDrift n y i) * (x i - y i) =
      -(n : ℝ)⁻¹ * ∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
        ((x i - x j) - (y i - y j)) ^ 2 / ((x i - x j) * (y i - y j)) := by
  rw [sum_dysonDrift_sub_mul_sub_eq_sum_Ioi, neg_mul, ← mul_neg, ← Finset.sum_neg_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hdx : x i - x j ≠ 0 := sub_ne_zero.2 (hx.ne (Finset.mem_Ioi.1 hj).ne)
  have hdy : y i - y j ≠ 0 := sub_ne_zero.2 (hy.ne (Finset.mem_Ioi.1 hj).ne)
  field_simp [hdx, hdy]; ring

/-- **Monotone dissipativity on the open Weyl chamber.** For any two strictly decreasing
configurations `x` and `y`, `⟨dysonDrift n x - dysonDrift n y, x - y⟩ ≤ 0`. -/
theorem sum_dysonDrift_sub_mul_sub_nonpos {n : ℕ} {x y : Fin n → ℝ}
    (hx : StrictAnti x) (hy : StrictAnti y) :
    ∑ i : Fin n, (dysonDrift n x i - dysonDrift n y i) * (x i - y i) ≤ 0 := by
  rw [sum_dysonDrift_sub_mul_sub hx.injective hy.injective, neg_mul, neg_nonpos]
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j hj ↦ ?_)
  have hdx : 0 < x i - x j := sub_pos.2 (hx (Finset.mem_Ioi.1 hj))
  have hdy : 0 < y i - y j := sub_pos.2 (hy (Finset.mem_Ioi.1 hj))
  positivity

/-- **Difference pairing identity against an arbitrary test vector.** Pairing
`dysonDrift n x - dysonDrift n y` against any `u : Fin n → ℝ` folds onto ordered pairs `i < j`. -/
theorem sum_dysonDrift_sub_mul_eq_sum_Ioi (n : ℕ) (x y u : Fin n → ℝ) :
    ∑ i : Fin n, (dysonDrift n x i - dysonDrift n y i) * u i =
      (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
        (u i - u j) * ((x i - x j)⁻¹ - (y i - y j)⁻¹) := by
  have hrew : ∑ i : Fin n, (dysonDrift n x i - dysonDrift n y i) * u i =
      (∑ i : Fin n, u i * dysonDrift n x i) - ∑ i : Fin n, u i * dysonDrift n y i := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [hrew, sum_mul_dysonDrift_eq_sum_Ioi, sum_mul_dysonDrift_eq_sum_Ioi, ← mul_sub,
    ← Finset.sum_sub_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **Monotone-test dissipativity on a common open Weyl chamber.** If `x` and `y` order their
particles in the same way, that is `(x i - x j) * (y i - y j) > 0` whenever `i ≠ j`, then for any
monotone `φ : ℝ → ℝ`, testing `dysonDrift n x - dysonDrift n y` against `i ↦ φ (x i - y i)` is
nonpositive. -/
theorem sum_dysonDrift_sub_mul_comp_sub_nonpos_of_pairwise {n : ℕ} {x y : Fin n → ℝ}
    {φ : ℝ → ℝ} (hφ : Monotone φ) (h : Pairwise fun i j ↦ 0 < (x i - x j) * (y i - y j)) :
    ∑ i : Fin n, (dysonDrift n x i - dysonDrift n y i) * φ (x i - y i) ≤ 0 := by
  rw [sum_dysonDrift_sub_mul_eq_sum_Ioi n x y fun k ↦ φ (x k - y k)]
  refine mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (Finset.sum_nonpos fun i _ ↦ Finset.sum_nonpos fun j hj ↦ ?_)
  have hab : 0 < (x i - x j) * (y i - y j) := h (Finset.mem_Ioi.1 hj).ne
  have ha : x i - x j ≠ 0 := left_ne_zero_of_mul hab.ne'
  have hb : y i - y j ≠ 0 := right_ne_zero_of_mul hab.ne'
  have hfrac : (φ (x i - y i) - φ (x j - y j)) * ((x i - x j)⁻¹ - (y i - y j)⁻¹) =
      (φ (x i - y i) - φ (x j - y j)) * ((x j - y j) - (x i - y i)) /
        ((x i - x j) * (y i - y j)) := by
    field_simp
    ring
  rw [hfrac]
  refine div_nonpos_of_nonpos_of_nonneg ?_ hab.le
  rcases le_total (x i - y i) (x j - y j) with hle | hge
  · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (hφ hle)) (sub_nonneg.2 hle)
  · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (hφ hge)) (sub_nonpos.2 hge)

/-- **Dissipativity of the Dyson drift on a common open Weyl chamber.** If `x` and `y` order their
particles in the same way, that is `(x i - x j) * (y i - y j) > 0` whenever `i ≠ j`, then
`⟨dysonDrift n x - dysonDrift n y, x - y⟩ ≤ 0`. -/
theorem sum_dysonDrift_sub_mul_sub_nonpos_of_pairwise {n : ℕ} {x y : Fin n → ℝ}
    (h : Pairwise fun i j ↦ 0 < (x i - x j) * (y i - y j)) :
    ∑ i : Fin n, (dysonDrift n x i - dysonDrift n y i) * (x i - y i) ≤ 0 :=
  sum_dysonDrift_sub_mul_comp_sub_nonpos_of_pairwise monotone_id h

/-- **Monotone-test dissipativity on the open Weyl chamber.** For strictly decreasing `x` and `y`
and any monotone `φ : ℝ → ℝ`, testing `dysonDrift n x - dysonDrift n y` against
`i ↦ φ (x i - y i)` is nonpositive. The case `φ = id` is `sum_dysonDrift_sub_mul_sub_nonpos`; the
positive-part case is `sum_dysonDrift_sub_mul_max_sub_zero_nonpos`. -/
theorem sum_dysonDrift_sub_mul_comp_sub_nonpos {n : ℕ} {x y : Fin n → ℝ} {φ : ℝ → ℝ}
    (hφ : Monotone φ) (hx : StrictAnti x) (hy : StrictAnti y) :
    ∑ i : Fin n, (dysonDrift n x i - dysonDrift n y i) * φ (x i - y i) ≤ 0 := by
  refine sum_dysonDrift_sub_mul_comp_sub_nonpos_of_pairwise hφ fun i j hij ↦ ?_
  rcases hij.lt_or_gt with h | h
  · exact mul_pos (sub_pos.2 (hx h)) (sub_pos.2 (hy h))
  · exact mul_pos_of_neg_of_neg (sub_neg.2 (hx h)) (sub_neg.2 (hy h))

/-- **One-sided positive-part dissipativity on the open Weyl chamber** (for AGZ Lemma 4.3.6). For
strictly decreasing `x` and `y`, testing `dysonDrift n x - dysonDrift n y` against
`i ↦ max (x i - y i) 0` is nonpositive. -/
theorem sum_dysonDrift_sub_mul_max_sub_zero_nonpos {n : ℕ} {x y : Fin n → ℝ}
    (hx : StrictAnti x) (hy : StrictAnti y) :
    ∑ i : Fin n, (dysonDrift n x i - dysonDrift n y i) * max (x i - y i) 0 ≤ 0 :=
  sum_dysonDrift_sub_mul_comp_sub_nonpos (φ := fun t ↦ max t 0)
    (fun _ _ h ↦ max_le_max_right 0 h) hx hy

/-- **Rogers–Shi entrance-weight identity.** Pairing `dysonDrift n x` against the linear staircase
weight `i ↦ n - 1 - 2 i` yields a positive combination of all ordered inverse gaps `(x i - x j)⁻¹`
with coefficients `2 (j - i) / n`. -/
theorem sum_sub_two_mul_mul_dysonDrift (n : ℕ) (x : Fin n → ℝ) :
    ∑ i : Fin n, ((n : ℝ) - 1 - 2 * (i : ℝ)) * dysonDrift n x i =
      2 * (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, ((j : ℝ) - (i : ℝ)) * (x i - x j)⁻¹ := by
  rw [sum_mul_dysonDrift_eq_sum_Ioi, mul_comm 2 (n : ℝ)⁻¹, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **Entrance-weight lower bound on the closed Weyl chamber.** When `x` is antitone, every ordered
gap has `j - i ≥ 1` and `x i - x j ≥ 0` (so `(x i - x j)⁻¹ ≥ 0`, with `0⁻¹ = 0`), bounding the
ordered inverse-gap sum by the entrance-weight pairing. -/
theorem mul_sum_Ioi_sub_inv_le_sum_sub_two_mul_mul_dysonDrift {n : ℕ} {x : Fin n → ℝ}
    (hx : Antitone x) :
    2 * (n : ℝ)⁻¹ * (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, (x i - x j)⁻¹) ≤
      ∑ i : Fin n, ((n : ℝ) - 1 - 2 * (i : ℝ)) * dysonDrift n x i := by
  rw [sum_sub_two_mul_mul_dysonDrift]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j hj ↦ ?_)
    (by positivity)
  have hij : i < j := Finset.mem_Ioi.1 hj
  have hcast : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Fin.lt_def.1 hij)
  exact le_mul_of_one_le_left (inv_nonneg.2 (sub_nonneg.2 (hx hij.le))) (by linarith)

/-- **Calogero–Moser partial-fraction identity for `dysonDrift`.** For any configuration `x` with
pairwise distinct coordinates, all off-diagonal products `(x i - x j)⁻¹ (x i - x k)⁻¹` (`j ≠ k`)
cancel in cyclic triples, leaving
`∑ i, (dysonDrift n x i)^2 = 2 n⁻² * ∑_{i < j} (x i - x j)⁻²`. -/
theorem sum_dysonDrift_sq {n : ℕ} {x : Fin n → ℝ} (hx : Function.Injective x) :
    ∑ i : Fin n, (dysonDrift n x i) ^ 2 =
      2 * ((n : ℝ)⁻¹) ^ 2 * ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, (x i - x j)⁻¹ ^ 2 := by
  have hexpand (i : Fin n) : (∑ j : Fin n, (x i - x j)⁻¹) ^ 2 =
      (∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹ ^ 2) +
        ∑ j : Fin n, ∑ k ∈ Finset.univ.erase j, (x i - x j)⁻¹ * (x i - x k)⁻¹ := by
    rw [sq, Finset.sum_mul]; simp_rw [Finset.mul_sum]
    have hsplit (j : Fin n) : (∑ k : Fin n, (x i - x j)⁻¹ * (x i - x k)⁻¹) =
        (x i - x j)⁻¹ ^ 2 + ∑ k ∈ Finset.univ.erase j, (x i - x j)⁻¹ * (x i - x k)⁻¹ := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j), sq]
    simp_rw [hsplit, Finset.sum_add_distrib]
    rw [← Finset.add_sum_erase Finset.univ (fun j ↦ (x i - x j)⁻¹ ^ 2) (Finset.mem_univ i),
      sub_self, inv_zero, zero_pow two_ne_zero, zero_add]
  simp_rw [dysonDrift_eq_inv_mul_sum, mul_pow, ← Finset.mul_sum, hexpand, Finset.sum_add_distrib]
  rw [Finset.sum_sum_sum_erase_sub_inv_mul_sub_inv_eq_zero Finset.univ hx.injOn, add_zero,
    Finset.sum_sum_erase_sub_inv_sq]
  ring

/-! ### Globally Lipschitz chamber truncations -/

/-- **Chamber-truncated Dyson drift with cutoff `ε`.** Every ordered gap `x i - x j` (`i < j`) is
clamped below at `ε`, producing a vector field on all of `Fin n → ℝ` that coincides with
`dysonDrift n` on `{x | ∀ i j, i < j → ε ≤ x i - x j}` and is globally bounded and Lipschitz for
every `ε > 0`. -/
noncomputable def truncatedDysonDrift (ε : ℝ) (n : ℕ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  (n : ℝ)⁻¹ *
    ((∑ j ∈ Finset.Ioi i, (max (x i - x j) ε)⁻¹) -
      ∑ j ∈ Finset.Iio i, (max (x j - x i) ε)⁻¹)

/-- Coordinate evaluation of `truncatedDysonDrift`. -/
theorem truncatedDysonDrift_apply (ε : ℝ) (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    truncatedDysonDrift ε n x i =
      (n : ℝ)⁻¹ *
        ((∑ j ∈ Finset.Ioi i, (max (x i - x j) ε)⁻¹) -
          ∑ j ∈ Finset.Iio i, (max (x j - x i) ε)⁻¹) :=
  (rfl)

/-- For at most one particle (`n ≤ 1`), `truncatedDysonDrift ε n = 0`. -/
theorem truncatedDysonDrift_of_le_one (ε : ℝ) {n : ℕ} (hn : n ≤ 1) :
    truncatedDysonDrift ε n = 0 := by
  have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.2 hn
  ext x i
  have hIoi : Finset.Ioi i = ∅ := by ext j; simp [Subsingleton.elim i j]
  have hIio : Finset.Iio i = ∅ := by ext j; simp [Subsingleton.elim j i]
  simp [truncatedDysonDrift_apply, hIoi, hIio]

/-- The `ε`-truncated Dyson drift of an empty particle system vanishes. -/
@[simp]
theorem truncatedDysonDrift_zero (ε : ℝ) : truncatedDysonDrift ε 0 = 0 :=
  truncatedDysonDrift_of_le_one ε (Nat.zero_le 1)

/-- The `ε`-truncated Dyson drift of a single particle vanishes. -/
@[simp]
theorem truncatedDysonDrift_one (ε : ℝ) : truncatedDysonDrift ε 1 = 0 :=
  truncatedDysonDrift_of_le_one ε le_rfl

/-- Shifting every coordinate by the same constant leaves `truncatedDysonDrift` unchanged. -/
@[simp]
theorem truncatedDysonDrift_add_const (ε : ℝ) (n : ℕ) (x : Fin n → ℝ) (c : ℝ) :
    truncatedDysonDrift ε n (fun i ↦ x i + c) = truncatedDysonDrift ε n x := by
  ext i; simp [truncatedDysonDrift_apply]

/-- Reflecting and reversing coordinates via `x ↦ (-x) ∘ Fin.revPerm` (which preserves the
decreasing Weyl chamber) negates and reverses `truncatedDysonDrift`. -/
theorem truncatedDysonDrift_neg_comp_revPerm (ε : ℝ) (n : ℕ) (x : Fin n → ℝ) :
    truncatedDysonDrift ε n ((-x) ∘ Fin.revPerm) =
      -(truncatedDysonDrift ε n x ∘ Fin.revPerm) := by
  ext i
  simp only [truncatedDysonDrift_apply, Pi.neg_apply, Function.comp_apply, Fin.revPerm_apply,
    neg_sub_neg]
  rw [← Fin.map_revPerm_Iio i, ← Fin.map_revPerm_Ioi i, Finset.sum_map, Finset.sum_map]
  simp only [Equiv.coe_toEmbedding, Fin.revPerm_apply]
  ring

/-- Rescaling both coordinates and cutoff by `c > 0` rescales `truncatedDysonDrift` by `c⁻¹`. -/
theorem truncatedDysonDrift_smul {c : ℝ} (hc : 0 < c) (ε : ℝ) (n : ℕ) (x : Fin n → ℝ) :
    truncatedDysonDrift (c * ε) n (c • x) = c⁻¹ • truncatedDysonDrift ε n x := by
  ext i
  have hterm (u v : Fin n) :
      (max (c * x u - c * x v) (c * ε))⁻¹ = c⁻¹ * (max (x u - x v) ε)⁻¹ := by
    rw [← mul_sub, ← mul_max_of_nonneg _ _ hc.le, mul_inv]
  simp only [truncatedDysonDrift_apply, Pi.smul_apply, smul_eq_mul, hterm, ← Finset.mul_sum]
  ring

/-- On the `ε`-interior of the open Weyl chamber (`∀ i < j, ε ≤ x i - x j`), the `ε`-truncated
drift agrees with `dysonDrift n`. -/
theorem truncatedDysonDrift_eq_dysonDrift {ε : ℝ} {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i j : Fin n, i < j → ε ≤ x i - x j) :
    truncatedDysonDrift ε n x = dysonDrift n x := by
  ext i
  rw [truncatedDysonDrift_apply, dysonDrift_apply, sum_erase_sub_inv_eq_sub]
  exact congrArg _ (congrArg₂ Sub.sub
    (Finset.sum_congr rfl fun j hj ↦ by rw [max_eq_left (hx i j (Finset.mem_Ioi.1 hj))])
    (Finset.sum_congr rfl fun j hj ↦ by rw [max_eq_left (hx j i (Finset.mem_Iio.1 hj))]))

/-- Antisymmetric pairing formula for `truncatedDysonDrift`. -/
theorem sum_mul_truncatedDysonDrift_eq_sum_Ioi (ε : ℝ) (n : ℕ) (w x : Fin n → ℝ) :
    ∑ i : Fin n, w i * truncatedDysonDrift ε n x i =
      (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, (w i - w j) * (max (x i - x j) ε)⁻¹ := by
  simp_rw [truncatedDysonDrift_apply, ← mul_left_comm (n : ℝ)⁻¹, ← Finset.mul_sum,
    Finset.sum_mul_sum_Ioi_sub_sum_Iio]

/-- The `ε`-truncated Dyson drift has zero coordinate sum at every configuration. -/
@[simp]
theorem sum_truncatedDysonDrift_eq_zero (ε : ℝ) (n : ℕ) (x : Fin n → ℝ) :
    ∑ i : Fin n, truncatedDysonDrift ε n x i = 0 := by
  simpa using sum_mul_truncatedDysonDrift_eq_sum_Ioi ε n (fun _ ↦ 1) x

/-- **Global monotone dissipativity of `truncatedDysonDrift`.** For `ε > 0`, `truncatedDysonDrift`
is dissipative on the entire space `Fin n → ℝ`, without restricting to ordered configurations. -/
theorem sum_truncatedDysonDrift_sub_mul_sub_nonpos {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (x y : Fin n → ℝ) :
    ∑ i : Fin n,
      (truncatedDysonDrift ε n x i - truncatedDysonDrift ε n y i) * (x i - y i) ≤ 0 := by
  rw [sum_sub_mul_sub_of_sum_mul_eq_sum_Ioi (K := fun u ↦ (max u ε)⁻¹)
    (sum_mul_truncatedDysonDrift_eq_sum_Ioi ε n) x y]
  refine mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (Finset.sum_nonpos fun i _ ↦ Finset.sum_nonpos fun j _ ↦ ?_)
  have hanti : Antitone fun u : ℝ ↦ (max u ε)⁻¹ := fun a b hab ↦
    inv_anti₀ (hε.trans_le (le_max_right a ε)) (max_le_max_right ε hab)
  rcases le_total (x i - x j) (y i - y j) with h | h
  · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 h) (sub_nonneg.2 (hanti h))
  · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 h) (sub_nonpos.2 (hanti h))

/-- **Uniform supremum-norm bound on `truncatedDysonDrift`.** For `ε > 0`, every coordinate of
`truncatedDysonDrift ε n x` has absolute value at most `ε⁻¹`, uniformly in `n` and `x`. -/
theorem norm_truncatedDysonDrift_le {ε : ℝ} (hε : 0 < ε) (n : ℕ) (x : Fin n → ℝ) :
    ‖truncatedDysonDrift ε n x‖ ≤ ε⁻¹ := by
  refine (pi_norm_le_iff_of_nonneg (inv_nonneg.2 hε.le)).2 fun i ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Fin.elim0 i
  have hbound (s : Finset (Fin n)) (g : Fin n → ℝ) :
      0 ≤ (∑ j ∈ s, (max (g j) ε)⁻¹) ∧ (∑ j ∈ s, (max (g j) ε)⁻¹) ≤ (n : ℝ) * ε⁻¹ := by
    refine ⟨Finset.sum_nonneg fun _ _ ↦ inv_nonneg.2 (hε.le.trans (le_max_right _ _)), ?_⟩
    calc ∑ j ∈ s, (max (g j) ε)⁻¹
        ≤ ∑ _j ∈ s, ε⁻¹ := Finset.sum_le_sum fun _ _ ↦ inv_anti₀ hε (le_max_right _ _)
      _ ≤ (n : ℝ) * ε⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        exact_mod_cast (Finset.card_le_univ s).trans_eq (Fintype.card_fin n)
  have hA := hbound (Finset.Ioi i) (fun j ↦ x i - x j)
  have hB := hbound (Finset.Iio i) (fun j ↦ x j - x i)
  rw [truncatedDysonDrift_apply, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg n))]
  calc (n : ℝ)⁻¹ * |(∑ j ∈ Finset.Ioi i, (max (x i - x j) ε)⁻¹) -
        ∑ j ∈ Finset.Iio i, (max (x j - x i) ε)⁻¹|
      ≤ (n : ℝ)⁻¹ * ((n : ℝ) * ε⁻¹) :=
        mul_le_mul_of_nonneg_left (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩) (by positivity)
    _ = ε⁻¹ := inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 hn.ne') ε⁻¹

private theorem abs_truncatedGap_sub_le {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    (x y : Fin n → ℝ) (u v : Fin n) :
    |(max (x u - x v) ε)⁻¹ - (max (y u - y v) ε)⁻¹| ≤ 2 * ε⁻¹ ^ 2 * dist x y := by
  set a := x u - x v; set b := y u - y v
  have ha : 0 < max a ε := hε.trans_le (le_max_right a ε)
  have hb : 0 < max b ε := hε.trans_le (le_max_right b ε)
  have hgap : |a - b| ≤ 2 * dist x y := by
    have h1 : |x u - y u| ≤ dist x y := by simpa [Real.dist_eq] using dist_le_pi_dist x y u
    have h2 : |x v - y v| ≤ dist x y := by simpa [Real.dist_eq] using dist_le_pi_dist x y v
    dsimp only [a, b]
    rw [sub_sub_sub_comm]
    exact (abs_sub _ _).trans (by linarith)
  rw [inv_sub_inv ha.ne' hb.ne', abs_div, abs_sub_comm, abs_of_pos (mul_pos ha hb)]
  calc |max a ε - max b ε| / (max a ε * max b ε)
      ≤ |a - b| / (ε * ε) := div_le_div₀ (abs_nonneg _) (abs_max_sub_max_le_abs a b ε)
        (mul_pos hε hε) (mul_le_mul (le_max_right a ε) (le_max_right b ε) hε.le ha.le)
    _ ≤ (2 * dist x y) / (ε * ε) := div_le_div_of_nonneg_right hgap (mul_pos hε hε).le
    _ = 2 * ε⁻¹ ^ 2 * dist x y := by rw [div_eq_inv_mul, mul_inv, sq]; ring

/-- **Global Lipschitz continuity of `truncatedDysonDrift`.** For `ε > 0`, `truncatedDysonDrift ε n`
is globally `(2 ε⁻²)`-Lipschitz on `Fin n → ℝ` in the supremum metric, uniformly in `n`. -/
theorem lipschitzWith_truncatedDysonDrift {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    LipschitzWith (2 * ε⁻¹ ^ 2).toNNReal (truncatedDysonDrift ε n) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [Real.coe_toNNReal (2 * ε⁻¹ ^ 2) (by positivity)]
  refine (dist_pi_le_iff (by positivity)).2 fun i ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Fin.elim0 i
  set f : Fin n → Fin n → ℝ := fun u v ↦ (max (x u - x v) ε)⁻¹ - (max (y u - y v) ε)⁻¹
  set L : ℝ := 2 * ε⁻¹ ^ 2 * dist x y
  have hdiff :
      ((∑ j ∈ Finset.Ioi i, (max (x i - x j) ε)⁻¹) - ∑ j ∈ Finset.Iio i, (max (x j - x i) ε)⁻¹) -
        ((∑ j ∈ Finset.Ioi i, (max (y i - y j) ε)⁻¹) - ∑ j ∈ Finset.Iio i, (max (y j - y i) ε)⁻¹) =
      (∑ j ∈ Finset.Ioi i, f i j) - ∑ j ∈ Finset.Iio i, f j i := by
    simp only [f, Finset.sum_sub_distrib]; ring
  rw [Real.dist_eq, truncatedDysonDrift_apply, truncatedDysonDrift_apply, ← mul_sub, abs_mul,
    abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg n)), hdiff]
  have hcard : ((Finset.Ioi i).card : ℝ) + ((Finset.Iio i).card : ℝ) ≤ n := by
    have hle : (Finset.Ioi i ∪ Finset.Iio i).card ≤ n :=
      (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
    exact_mod_cast (Finset.card_union_of_disjoint (Finset.disjoint_Ioi_Iio i)) ▸ hle
  have hsum : |(∑ j ∈ Finset.Ioi i, f i j) - ∑ j ∈ Finset.Iio i, f j i| ≤ (n : ℝ) * L :=
    calc |(∑ j ∈ Finset.Ioi i, f i j) - ∑ j ∈ Finset.Iio i, f j i|
        ≤ (∑ j ∈ Finset.Ioi i, |f i j|) + ∑ j ∈ Finset.Iio i, |f j i| :=
          (abs_sub _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _)
            (Finset.abs_sum_le_sum_abs _ _))
      _ ≤ (∑ _j ∈ Finset.Ioi i, L) + ∑ _j ∈ Finset.Iio i, L :=
          add_le_add (Finset.sum_le_sum fun j _ ↦ abs_truncatedGap_sub_le hε x y i j)
            (Finset.sum_le_sum fun j _ ↦ abs_truncatedGap_sub_le hε x y j i)
      _ = (((Finset.Ioi i).card : ℝ) + ((Finset.Iio i).card : ℝ)) * L := by
          simp [nsmul_eq_mul, add_mul]
      _ ≤ (n : ℝ) * L := mul_le_mul_of_nonneg_right hcard (by positivity)
  calc (n : ℝ)⁻¹ * |(∑ j ∈ Finset.Ioi i, f i j) - ∑ j ∈ Finset.Iio i, f j i|
      ≤ (n : ℝ)⁻¹ * ((n : ℝ) * L) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = L := inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 hn.ne') _

/-- `truncatedDysonDrift ε n` is globally continuous on `Fin n → ℝ` for every `ε > 0`. -/
theorem continuous_truncatedDysonDrift {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    Continuous (truncatedDysonDrift ε n) :=
  (lipschitzWith_truncatedDysonDrift hε n).continuous

end TauCeti.Probability
