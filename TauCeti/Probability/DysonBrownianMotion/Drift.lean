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
`n`), centered, and monotonically dissipative on all of `Fin n → ℝ`.

## Main declarations

* `TauCeti.Probability.dysonDrift`: the singular Coulomb repulsion drift on `Fin n → ℝ`.
* `TauCeti.Probability.sum_mul_dysonDrift_eq_sum_Ioi`: antisymmetric pairing over `i < j`.
* `TauCeti.Probability.sum_dysonDrift_eq_zero` and `TauCeti.Probability.sum_self_mul_dysonDrift`:
  first- and second-moment identities.
* `TauCeti.Probability.sum_dysonDrift_sub_mul_sub_nonpos`: monotone dissipativity on the chamber.
* `TauCeti.Probability.mul_sum_Ioi_sub_inv_le_sum_sub_two_mul_mul_dysonDrift`: entrance-weight lower
  bound.
* `TauCeti.Probability.sum_dysonDrift_sq`: Calogero–Moser partial-fraction identity.
* `TauCeti.Probability.truncatedDysonDrift` and
  `TauCeti.Probability.lipschitzWith_truncatedDysonDrift`: globally Lipschitz `ε`-truncation.

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
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← neg_sub (x j) (x i), inv_neg]

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
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [hlhs, hpair _ x, hpair _ y, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

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
  have hempty : Finset.univ.erase i = ∅ := by
    ext j
    simp [Subsingleton.elim j i]
  simp [dysonDrift_apply, hempty]

/-- The Dyson drift of an empty particle system vanishes. -/
@[simp]
theorem dysonDrift_zero : dysonDrift 0 = 0 :=
  dysonDrift_of_le_one (Nat.zero_le 1)

/-- A single particle experiences no pairwise repulsion. -/
@[simp]
theorem dysonDrift_one : dysonDrift 1 = 0 :=
  dysonDrift_of_le_one le_rfl

/-- Shifting every coordinate by the same constant leaves `dysonDrift` unchanged. -/
@[simp]
theorem dysonDrift_add_const (n : ℕ) (x : Fin n → ℝ) (c : ℝ) :
    dysonDrift n (fun i ↦ x i + c) = dysonDrift n x := by
  ext i
  simp [dysonDrift]

/-- Rescaling a configuration by `c : ℝ` rescales `dysonDrift` by `c⁻¹` (including at `c = 0`). -/
theorem dysonDrift_smul (n : ℕ) (c : ℝ) (x : Fin n → ℝ) :
    dysonDrift n (c • x) = c⁻¹ • dysonDrift n x := by
  ext i
  simp only [dysonDrift, Pi.smul_apply, smul_eq_mul]
  have hterm : ∀ j : Fin n, (c * x i - c * x j)⁻¹ = c⁻¹ * (x i - x j)⁻¹ := fun j ↦ by
    rw [← mul_sub, mul_inv]
  simp only [hterm, ← Finset.mul_sum]
  ring

/-- `dysonDrift n` is continuous at every configuration with pairwise distinct coordinates. -/
theorem continuousAt_dysonDrift {n : ℕ} {x : Fin n → ℝ} (hx : Function.Injective x) :
    ContinuousAt (dysonDrift n) x := by
  refine continuousAt_pi.2 fun i ↦ ContinuousAt.mul continuousAt_const ?_
  refine tendsto_finsetSum _ fun j hj ↦ ?_
  have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
  exact ((continuousAt_apply i _).sub (continuousAt_apply j _)).inv₀ (sub_ne_zero.2 (hx.ne hij))

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

/-- **Virial identity.** At any configuration with distinct coordinates (`n ≥ 1`), pairing `x`
with `dysonDrift n x` gives `(n - 1) / 2`. -/
theorem sum_self_mul_dysonDrift {n : ℕ} (hn : 0 < n) {x : Fin n → ℝ}
    (hx : Function.Injective x) :
    ∑ i : Fin n, x i * dysonDrift n x i = ((n : ℝ) - 1) / 2 := by
  rw [sum_mul_dysonDrift_eq_sum_Ioi]
  have hones : ∀ i : Fin n, ∑ j ∈ Finset.Ioi i, (x i - x j) * (x i - x j)⁻¹ =
      ∑ _j ∈ Finset.Ioi i, (1 : ℝ) := fun i ↦
    Finset.sum_congr rfl fun j hj ↦
      mul_inv_cancel₀ (sub_ne_zero.2 (hx.ne (Finset.mem_Ioi.1 hj).ne))
  simp_rw [hones]
  have hdouble : 2 * (∑ i : Fin n, ∑ _j ∈ Finset.Ioi i, (1 : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) := by
    have hsym := Finset.sum_sum_Iio_eq_sum_sum_Ioi (ι := Fin n) (fun _ _ ↦ (1 : ℝ))
    have hunion : (∑ i : Fin n, ∑ _j ∈ Finset.Ioi i, (1 : ℝ)) +
        (∑ i : Fin n, ∑ _j ∈ Finset.Iio i, (1 : ℝ)) =
        ∑ i : Fin n, ∑ _j ∈ Finset.univ.erase i, (1 : ℝ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ (Finset.sum_erase_univ_eq_sum_Ioi_add_sum_Iio i _).symm
    have hcard : ∀ i : Fin n, ∑ _j ∈ Finset.univ.erase i, (1 : ℝ) = (n : ℝ) - 1 := fun i ↦ by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin, Nat.cast_sub hn, Nat.cast_one]
    have htotal : (∑ i : Fin n, ∑ _j ∈ Finset.univ.erase i, (1 : ℝ)) =
        (n : ℝ) * ((n : ℝ) - 1) := by
      simp_rw [hcard, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  have hn₀ : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  field_simp [hn₀]
  linarith

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
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hij : i ≠ j := (Finset.mem_Ioi.1 hj).ne
  have hdx : x i - x j ≠ 0 := sub_ne_zero.2 (hx.ne hij)
  have hdy : y i - y j ≠ 0 := sub_ne_zero.2 (hy.ne hij)
  field_simp [hdx, hdy]
  ring

/-- **Monotone dissipativity on the open Weyl chamber.** For any two strictly decreasing
configurations `x` and `y`, `⟨dysonDrift n x - dysonDrift n y, x - y⟩ ≤ 0`. -/
theorem sum_dysonDrift_sub_mul_sub_nonpos {n : ℕ} {x y : Fin n → ℝ}
    (hx : StrictAnti x) (hy : StrictAnti y) :
    ∑ i : Fin n, (dysonDrift n x i - dysonDrift n y i) * (x i - y i) ≤ 0 := by
  rw [sum_dysonDrift_sub_mul_sub hx.injective hy.injective, neg_mul, neg_nonpos]
  refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg n)) (Finset.sum_nonneg fun i _ ↦ ?_)
  refine Finset.sum_nonneg fun j hj ↦ ?_
  have hij : i < j := Finset.mem_Ioi.1 hj
  have hdx : 0 < x i - x j := sub_pos.2 (hx hij)
  have hdy : 0 < y i - y j := sub_pos.2 (hy hij)
  positivity

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
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **Entrance-weight lower bound on the open chamber.** When `x` is strictly decreasing, every
ordered gap has `j - i ≥ 1` and `x i - x j > 0`, bounding the full positive inverse-gap sum by the
entrance-weight pairing. -/
theorem mul_sum_Ioi_sub_inv_le_sum_sub_two_mul_mul_dysonDrift {n : ℕ} {x : Fin n → ℝ}
    (hx : StrictAnti x) :
    2 * (n : ℝ)⁻¹ * (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, (x i - x j)⁻¹) ≤
      ∑ i : Fin n, ((n : ℝ) - 1 - 2 * (i : ℝ)) * dysonDrift n x i := by
  rw [sum_sub_two_mul_mul_dysonDrift]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j hj ↦ ?_)
    (by positivity)
  have hij : i < j := Finset.mem_Ioi.1 hj
  have hgap : 0 ≤ (x i - x j)⁻¹ := inv_nonneg.2 (sub_pos.2 (hx hij)).le
  have hidx : (1 : ℝ) ≤ (j : ℝ) - (i : ℝ) := by
    have hcast : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Fin.lt_def.1 hij)
    linarith
  exact le_mul_of_one_le_left hgap hidx

/-- **Calogero–Moser partial-fraction identity for `dysonDrift`.** For any configuration `x` with
pairwise distinct coordinates, all off-diagonal products `(x i - x j)⁻¹ (x i - x k)⁻¹` (`j ≠ k`)
cancel in cyclic triples, leaving
`∑ i, (dysonDrift n x i)^2 = 2 n⁻² * ∑_{i < j} (x i - x j)⁻²`. -/
theorem sum_dysonDrift_sq {n : ℕ} {x : Fin n → ℝ} (hx : Function.Injective x) :
    ∑ i : Fin n, (dysonDrift n x i) ^ 2 =
      2 * ((n : ℝ)⁻¹) ^ 2 * ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, (x i - x j)⁻¹ ^ 2 := by
  have hexpand (i : Fin n) :
      (∑ j : Fin n, (x i - x j)⁻¹) ^ 2 =
        (∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹ ^ 2) +
          ∑ j : Fin n, ∑ k ∈ Finset.univ.erase j, (x i - x j)⁻¹ * (x i - x k)⁻¹ := by
    rw [sq, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    have hsplit (j : Fin n) : (∑ k : Fin n, (x i - x j)⁻¹ * (x i - x k)⁻¹) =
        (x i - x j)⁻¹ ^ 2 + ∑ k ∈ Finset.univ.erase j, (x i - x j)⁻¹ * (x i - x k)⁻¹ := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j), sq]
    simp_rw [hsplit, Finset.sum_add_distrib]
    rw [← Finset.add_sum_erase Finset.univ (fun j ↦ (x i - x j)⁻¹ ^ 2) (Finset.mem_univ i),
      sub_self, inv_zero, zero_pow two_ne_zero, zero_add]
  have hpair : (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹ ^ 2) =
      2 * ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, (x i - x j)⁻¹ ^ 2 := by
    simp_rw [Finset.sum_erase_univ_eq_sum_Ioi_add_sum_Iio, Finset.sum_add_distrib,
      Finset.sum_sum_Iio_eq_sum_sum_Ioi (fun i j ↦ (x i - x j)⁻¹ ^ 2)]
    have hsym (i j : Fin n) : (x j - x i)⁻¹ ^ 2 = (x i - x j)⁻¹ ^ 2 := by
      rw [← neg_sub (x i) (x j), inv_neg, neg_sq]
    simp_rw [hsym]
    ring
  simp_rw [dysonDrift_eq_inv_mul_sum, mul_pow, ← Finset.mul_sum, hexpand, Finset.sum_add_distrib]
  rw [Finset.sum_sum_erase_sub_inv_mul_sub_inv_eq_zero Finset.univ hx.injOn, add_zero, hpair]
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
  ext i
  simp [truncatedDysonDrift_apply]

/-- On the `ε`-interior of the open Weyl chamber (`∀ i < j, ε ≤ x i - x j`), the `ε`-truncated
drift agrees with `dysonDrift n`. -/
theorem truncatedDysonDrift_eq_dysonDrift {ε : ℝ} {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i j : Fin n, i < j → ε ≤ x i - x j) :
    truncatedDysonDrift ε n x = dysonDrift n x := by
  ext i
  rw [truncatedDysonDrift_apply, dysonDrift_apply, sum_erase_sub_inv_eq_sub]
  congr 1
  exact congrArg₂ Sub.sub
    (Finset.sum_congr rfl fun j hj ↦ by rw [max_eq_left (hx i j (Finset.mem_Ioi.1 hj))])
    (Finset.sum_congr rfl fun j hj ↦ by rw [max_eq_left (hx j i (Finset.mem_Iio.1 hj))])

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
  refine mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (Nat.cast_nonneg n)) ?_
  refine Finset.sum_nonpos fun i _ ↦ Finset.sum_nonpos fun j _ ↦ ?_
  set a := x i - x j
  set b := y i - y j
  rcases le_total a b with hab | hba
  · have hinv : (max b ε)⁻¹ ≤ (max a ε)⁻¹ :=
      inv_anti₀ (lt_of_lt_of_le hε (le_max_right a ε)) (max_le_max_right ε hab)
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hab) (sub_nonneg.2 hinv)
  · have hinv : (max a ε)⁻¹ ≤ (max b ε)⁻¹ :=
      inv_anti₀ (lt_of_lt_of_le hε (le_max_right b ε)) (max_le_max_right ε hba)
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hba) (sub_nonpos.2 hinv)

/-- **Uniform supremum-norm bound on `truncatedDysonDrift`.** For `ε > 0`, every coordinate of
`truncatedDysonDrift ε n x` has absolute value at most `ε⁻¹`, uniformly in `n` and `x`. -/
theorem norm_truncatedDysonDrift_le {ε : ℝ} (hε : 0 < ε) (n : ℕ) (x : Fin n → ℝ) :
    ‖truncatedDysonDrift ε n x‖ ≤ ε⁻¹ := by
  refine (pi_norm_le_iff_of_nonneg (inv_nonneg.2 hε.le)).2 fun i ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Fin.elim0 i
  have hA₀ : 0 ≤ ∑ j ∈ Finset.Ioi i, (max (x i - x j) ε)⁻¹ :=
    Finset.sum_nonneg fun j _ ↦ inv_nonneg.2 (hε.le.trans (le_max_right _ _))
  have hB₀ : 0 ≤ ∑ j ∈ Finset.Iio i, (max (x j - x i) ε)⁻¹ :=
    Finset.sum_nonneg fun j _ ↦ inv_nonneg.2 (hε.le.trans (le_max_right _ _))
  have hA : (∑ j ∈ Finset.Ioi i, (max (x i - x j) ε)⁻¹) ≤ (n : ℝ) * ε⁻¹ := by
    calc (∑ j ∈ Finset.Ioi i, (max (x i - x j) ε)⁻¹)
        ≤ ∑ _j ∈ Finset.Ioi i, ε⁻¹ :=
          Finset.sum_le_sum fun j _ ↦ inv_anti₀ hε (le_max_right _ _)
      _ = ((Finset.Ioi i).card : ℝ) * ε⁻¹ := by simp [nsmul_eq_mul]
      _ ≤ (n : ℝ) * ε⁻¹ := by
          gcongr
          exact_mod_cast (Finset.card_le_univ (Finset.Ioi i)).trans_eq (Fintype.card_fin n)
  have hB : (∑ j ∈ Finset.Iio i, (max (x j - x i) ε)⁻¹) ≤ (n : ℝ) * ε⁻¹ := by
    calc (∑ j ∈ Finset.Iio i, (max (x j - x i) ε)⁻¹)
        ≤ ∑ _j ∈ Finset.Iio i, ε⁻¹ :=
          Finset.sum_le_sum fun j _ ↦ inv_anti₀ hε (le_max_right _ _)
      _ = ((Finset.Iio i).card : ℝ) * ε⁻¹ := by simp [nsmul_eq_mul]
      _ ≤ (n : ℝ) * ε⁻¹ := by
          gcongr
          exact_mod_cast (Finset.card_le_univ (Finset.Iio i)).trans_eq (Fintype.card_fin n)
  rw [truncatedDysonDrift_apply, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg n))]
  have habs : |(∑ j ∈ Finset.Ioi i, (max (x i - x j) ε)⁻¹) -
      ∑ j ∈ Finset.Iio i, (max (x j - x i) ε)⁻¹| ≤ (n : ℝ) * ε⁻¹ :=
    abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  calc (n : ℝ)⁻¹ * |(∑ j ∈ Finset.Ioi i, (max (x i - x j) ε)⁻¹) -
        ∑ j ∈ Finset.Iio i, (max (x j - x i) ε)⁻¹|
      ≤ (n : ℝ)⁻¹ * ((n : ℝ) * ε⁻¹) :=
        mul_le_mul_of_nonneg_left habs (inv_nonneg.2 (Nat.cast_nonneg n))
    _ = ε⁻¹ := inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 hn.ne') ε⁻¹

private theorem abs_truncatedGap_sub_le {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    (x y : Fin n → ℝ) (u v : Fin n) :
    |(max (x u - x v) ε)⁻¹ - (max (y u - y v) ε)⁻¹| ≤ 2 * ε⁻¹ ^ 2 * dist x y := by
  set a := x u - x v
  set b := y u - y v
  have ha : 0 < max a ε := lt_of_lt_of_le hε (le_max_right a ε)
  have hb : 0 < max b ε := lt_of_lt_of_le hε (le_max_right b ε)
  have hden : ε * ε ≤ max a ε * max b ε :=
    mul_le_mul (le_max_right a ε) (le_max_right b ε) hε.le ha.le
  have hgap : |a - b| ≤ 2 * dist x y := by
    have h1 : |x u - y u| ≤ dist x y := by simpa [Real.dist_eq] using dist_le_pi_dist x y u
    have h2 : |x v - y v| ≤ dist x y := by simpa [Real.dist_eq] using dist_le_pi_dist x y v
    have heq : a - b = (x u - y u) - (x v - y v) := by dsimp [a, b]; ring
    rw [heq]
    exact (abs_sub _ _).trans (by linarith)
  rw [inv_sub_inv ha.ne' hb.ne', abs_div, abs_sub_comm, abs_of_pos (mul_pos ha hb)]
  calc |max a ε - max b ε| / (max a ε * max b ε)
      ≤ |a - b| / (ε * ε) :=
        div_le_div₀ (abs_nonneg _) (abs_max_sub_max_le_abs a b ε) (mul_pos hε hε) hden
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
  rw [Real.dist_eq, truncatedDysonDrift_apply, truncatedDysonDrift_apply, ← mul_sub, abs_mul,
    abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg n))]
  have hdiff : ((∑ j ∈ Finset.Ioi i, (max (x i - x j) ε)⁻¹) -
        ∑ j ∈ Finset.Iio i, (max (x j - x i) ε)⁻¹) -
      ((∑ j ∈ Finset.Ioi i, (max (y i - y j) ε)⁻¹) -
        ∑ j ∈ Finset.Iio i, (max (y j - y i) ε)⁻¹) =
      (∑ j ∈ Finset.Ioi i, f i j) - ∑ j ∈ Finset.Iio i, f j i := by
    simp only [f, Finset.sum_sub_distrib]
    ring
  rw [hdiff]
  have hcard : ((Finset.Ioi i).card : ℝ) + ((Finset.Iio i).card : ℝ) ≤ n := by
    have hle : (Finset.Ioi i ∪ Finset.Iio i).card ≤ n :=
      (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
    exact_mod_cast (Finset.card_union_of_disjoint (Finset.disjoint_Ioi_Iio i)) ▸ hle
  have hsum : |(∑ j ∈ Finset.Ioi i, f i j) - ∑ j ∈ Finset.Iio i, f j i| ≤ (n : ℝ) * L := by
    calc |(∑ j ∈ Finset.Ioi i, f i j) - ∑ j ∈ Finset.Iio i, f j i|
        ≤ |∑ j ∈ Finset.Ioi i, f i j| + |∑ j ∈ Finset.Iio i, f j i| := abs_sub _ _
      _ ≤ (∑ j ∈ Finset.Ioi i, |f i j|) + ∑ j ∈ Finset.Iio i, |f j i| :=
          add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ (∑ _j ∈ Finset.Ioi i, L) + ∑ _j ∈ Finset.Iio i, L :=
          add_le_add (Finset.sum_le_sum fun j _ ↦ abs_truncatedGap_sub_le hε x y i j)
            (Finset.sum_le_sum fun j _ ↦ abs_truncatedGap_sub_le hε x y j i)
      _ = (((Finset.Ioi i).card : ℝ) + ((Finset.Iio i).card : ℝ)) * L := by
          simp [nsmul_eq_mul, add_mul]
      _ ≤ (n : ℝ) * L := mul_le_mul_of_nonneg_right hcard (by positivity)
  calc (n : ℝ)⁻¹ * |(∑ j ∈ Finset.Ioi i, f i j) - ∑ j ∈ Finset.Iio i, f j i|
      ≤ (n : ℝ)⁻¹ * ((n : ℝ) * L) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 (Nat.cast_nonneg n))
    _ = L := inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 hn.ne') _

/-- `truncatedDysonDrift ε n` is globally continuous on `Fin n → ℝ` for every `ε > 0`. -/
theorem continuous_truncatedDysonDrift {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    Continuous (truncatedDysonDrift ε n) :=
  (lipschitzWith_truncatedDysonDrift hε n).continuous

end TauCeti.Probability
