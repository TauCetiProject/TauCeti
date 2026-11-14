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

/-!
# Repulsive Coulomb drift of Dyson Brownian motion and its chamber truncations

For `n` particles `x : Fin n → ℝ`, the normalized Dyson drift at coordinate `i` is
`dysonDrift n x i = n⁻¹ * ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹`. It is the gradient of the
normalized logarithmic Vandermonde potential `n⁻¹ * ∑_{i < j} log |x i - x j|`, singular along the
collision hyperplanes `x i = x j` and smooth on the open decreasing Weyl chamber
`{x : Fin n → ℝ | StrictAnti x}`.

Because `(x j - x i)⁻¹ = -(x i - x j)⁻¹`, pairing `dysonDrift n x` against any weight `w` folds
over ordered pairs `i < j`. This single antisymmetric pairing formula yields conservation of the
center of mass (`sum_dysonDrift_eq_zero`), the virial identity (`sum_mul_self_dysonDrift`), the
Rogers–Shi entrance-weight inequality (`le_sum_entranceWeight_mul_dysonDrift`), and monotone
dissipativity (`sum_dysonDrift_sub_mul_sub_nonpos`) on the open chamber. Squaring the drift and
applying the three-term partial-fraction identity `(a - b)⁻¹ (a - c)⁻¹ + cyclic = 0` yields the
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
* `TauCeti.Probability.sum_dysonDrift_eq_zero` and `TauCeti.Probability.sum_mul_self_dysonDrift`:
  first- and second-moment identities.
* `TauCeti.Probability.sum_dysonDrift_sub_mul_sub_nonpos`: monotone dissipativity on the chamber.
* `TauCeti.Probability.le_sum_entranceWeight_mul_dysonDrift`: entrance-weight lower bound.
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

/-! ### Finite-sum swap over ordered index pairs -/

private theorem sum_Iio_eq_sum_Ioi {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ i : Fin n, ∑ j ∈ Finset.Iio i, f i j) = ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, f j i := by
  have hIio : ∀ i : Fin n, Finset.Iio i = Finset.univ.filter (· < i) := fun i ↦ by ext j; simp
  have hIoi : ∀ i : Fin n, Finset.Ioi i = Finset.univ.filter (i < ·) := fun i ↦ by ext j; simp
  simp only [hIio, hIoi, Finset.sum_filter]
  exact Finset.sum_comm

private theorem sum_erase_eq_sum_Ioi_add_sum_Iio {n : ℕ} (i : Fin n) (g : Fin n → ℝ) :
    (∑ j ∈ Finset.univ.erase i, g j) =
      (∑ j ∈ Finset.Ioi i, g j) + ∑ j ∈ Finset.Iio i, g j := by
  rw [← Finset.compl_singleton, ← Finset.Ioi_disjUnion_Iio, Finset.sum_disjUnion]

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

/-- The Dyson drift of an empty particle system vanishes. -/
@[simp]
theorem dysonDrift_zero : dysonDrift 0 = 0 := by
  ext x i
  exact Fin.elim0 i

/-- A single particle experiences no pairwise repulsion. -/
@[simp]
theorem dysonDrift_one (x : Fin 1 → ℝ) : dysonDrift 1 x = 0 := by
  ext i
  have hempty : Finset.univ.erase i = ∅ := by
    ext j
    simp [Subsingleton.elim j i]
  rw [dysonDrift_apply, hempty]
  simp

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
  simp only [dysonDrift_apply, ← mul_left_comm (n : ℝ)⁻¹, ← Finset.mul_sum]
  congr 1
  have hsplit : ∀ i : Fin n,
      w i * (∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹) =
        (∑ j ∈ Finset.Ioi i, w i * (x i - x j)⁻¹) +
          ∑ j ∈ Finset.Iio i, w i * (x i - x j)⁻¹ := fun i ↦ by
    rw [sum_erase_eq_sum_Ioi_add_sum_Iio, mul_add, Finset.mul_sum, Finset.mul_sum]
  simp_rw [hsplit, Finset.sum_add_distrib,
    sum_Iio_eq_sum_Ioi (fun i j ↦ w i * (x i - x j)⁻¹), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  have hneg : (x j - x i)⁻¹ = -(x i - x j)⁻¹ := by
    rw [← neg_sub (x i) (x j), inv_neg]
  rw [hneg]
  ring

/-- **Center-of-mass conservation.** The coordinates of `dysonDrift n x` sum to `0` for every
configuration `x`. -/
@[simp]
theorem sum_dysonDrift_eq_zero (n : ℕ) (x : Fin n → ℝ) :
    ∑ i : Fin n, dysonDrift n x i = 0 := by
  have h := sum_mul_dysonDrift_eq_sum_Ioi n (fun _ ↦ 1) x
  simpa using h

/-- **Virial identity.** At any configuration with distinct coordinates (`n ≥ 1`), pairing `x`
with `dysonDrift n x` gives `(n - 1) / 2`. -/
theorem sum_mul_self_dysonDrift {n : ℕ} (hn : 0 < n) {x : Fin n → ℝ}
    (hx : Function.Injective x) :
    ∑ i : Fin n, x i * dysonDrift n x i = ((n : ℝ) - 1) / 2 := by
  rw [sum_mul_dysonDrift_eq_sum_Ioi]
  have hones : ∀ i : Fin n, ∑ j ∈ Finset.Ioi i, (x i - x j) * (x i - x j)⁻¹ =
      ∑ _j ∈ Finset.Ioi i, (1 : ℝ) := fun i ↦
    Finset.sum_congr rfl fun j hj ↦
      mul_inv_cancel₀ (sub_ne_zero.2 (hx.ne (Finset.mem_Ioi.1 hj).ne))
  simp_rw [hones]
  have hdouble : 2 * (∑ i : Fin n, ∑ _j ∈ Finset.Ioi i, (1 : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) := by
    have hsym := sum_Iio_eq_sum_Ioi (n := n) (fun _ _ ↦ (1 : ℝ))
    have hunion : (∑ i : Fin n, ∑ _j ∈ Finset.Ioi i, (1 : ℝ)) +
        (∑ i : Fin n, ∑ _j ∈ Finset.Iio i, (1 : ℝ)) =
        ∑ i : Fin n, ∑ _j ∈ Finset.univ.erase i, (1 : ℝ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ (sum_erase_eq_sum_Ioi_add_sum_Iio i _).symm
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
        ((x i - x j) - (y i - y j)) * ((x i - x j)⁻¹ - (y i - y j)⁻¹) := by
  have hx := sum_mul_dysonDrift_eq_sum_Ioi n (fun i ↦ x i - y i) x
  have hy := sum_mul_dysonDrift_eq_sum_Ioi n (fun i ↦ x i - y i) y
  have hlhs : ∑ i : Fin n, (dysonDrift n x i - dysonDrift n y i) * (x i - y i) =
      (∑ i : Fin n, (x i - y i) * dysonDrift n x i) -
        ∑ i : Fin n, (x i - y i) * dysonDrift n y i := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hlhs, hx, hy, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp_rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ by ring

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
theorem sum_entranceWeight_mul_dysonDrift (n : ℕ) (x : Fin n → ℝ) :
    ∑ i : Fin n, ((n : ℝ) - 1 - 2 * (i : ℝ)) * dysonDrift n x i =
      2 * (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, ((j : ℝ) - (i : ℝ)) * (x i - x j)⁻¹ := by
  rw [sum_mul_dysonDrift_eq_sum_Ioi, mul_comm 2 (n : ℝ)⁻¹, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ by ring

/-- **Entrance-weight lower bound on the open chamber.** When `x` is strictly decreasing, every
ordered gap has `j - i ≥ 1` and `x i - x j > 0`, bounding the full positive inverse-gap sum by the
entrance-weight pairing. -/
theorem le_sum_entranceWeight_mul_dysonDrift {n : ℕ} {x : Fin n → ℝ} (hx : StrictAnti x) :
    2 * (n : ℝ)⁻¹ * (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, (x i - x j)⁻¹) ≤
      ∑ i : Fin n, ((n : ℝ) - 1 - 2 * (i : ℝ)) * dysonDrift n x i := by
  rw [sum_entranceWeight_mul_dysonDrift]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j hj ↦ ?_)
    (by positivity)
  have hij : i < j := Finset.mem_Ioi.1 hj
  have hgap : 0 ≤ (x i - x j)⁻¹ := inv_nonneg.2 (sub_pos.2 (hx hij)).le
  have hidx : (1 : ℝ) ≤ (j : ℝ) - (i : ℝ) := by
    have hnat : (i : ℕ) + 1 ≤ (j : ℕ) := hij
    have hcast : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith
  exact le_mul_of_one_le_left hgap hidx

private theorem sum_offDiag_mul_sub_inv_eq_zero {n : ℕ} {x : Fin n → ℝ}
    (hx : Function.Injective x) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      if j = k then (0 : ℝ) else (x i - x j)⁻¹ * (x i - x k)⁻¹) = 0 := by
  let f : Fin n → Fin n → Fin n → ℝ := fun i j k ↦
    if j = k then 0 else (x i - x j)⁻¹ * (x i - x k)⁻¹
  have htriple : ∀ i j k : Fin n, f i j k + f j k i + f k i j = 0 := fun i j k ↦ by
    by_cases hij : i = j
    · subst hij; simp [f]
    · by_cases hjk : j = k
      · subst hjk; simp [f]
      · by_cases hki : k = i
        · subst hki; simp [f]
        · simp only [f, hij, hjk, hki, ↓reduceIte]
          have h1 : x i - x j ≠ 0 := sub_ne_zero.2 (hx.ne hij)
          have h2 : x j - x k ≠ 0 := sub_ne_zero.2 (hx.ne hjk)
          have h3 : x k - x i ≠ 0 := sub_ne_zero.2 (hx.ne hki)
          have h4 : x i - x k = -(x k - x i) := by ring
          have h5 : x j - x i = -(x i - x j) := by ring
          have h6 : x k - x j = -(x j - x k) := by ring
          rw [h4, h5, h6]
          field_simp [h1, h2, h3]
          ring
  have hperm₁ : (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, f j k i) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, f i j k := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_comm
  have hperm₂ : (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, f k i j) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, f i j k := by
    rw [← hperm₁, Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_comm
  have hzero : (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, (f i j k + f j k i + f k i j)) = 0 := by
    simp [htriple]
  simp only [Finset.sum_add_distrib, hperm₁, hperm₂] at hzero
  dsimp only [f] at hzero
  linarith

/-- **Calogero–Moser partial-fraction identity for `dysonDrift`.** For any configuration `x` with
pairwise distinct coordinates, all off-diagonal products `(x i - x j)⁻¹ (x i - x k)⁻¹` (`j ≠ k`)
cancel in cyclic triples, leaving
`∑ i, (dysonDrift n x i)^2 = 2 n⁻² * ∑_{i < j} (x i - x j)⁻²`. -/
theorem sum_dysonDrift_sq {n : ℕ} {x : Fin n → ℝ} (hx : Function.Injective x) :
    ∑ i : Fin n, (dysonDrift n x i) ^ 2 =
      2 * ((n : ℝ)⁻¹) ^ 2 * ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, (x i - x j)⁻¹ ^ 2 := by
  let f : Fin n → Fin n → Fin n → ℝ := fun i j k ↦
    if j = k then 0 else (x i - x j)⁻¹ * (x i - x k)⁻¹
  have hexpand : ∀ i : Fin n,
      (∑ j : Fin n, (x i - x j)⁻¹) ^ 2 =
        (∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹ ^ 2) + ∑ j : Fin n, ∑ k : Fin n, f i j k := by
    intro i
    rw [sq, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    have hdiag : ∀ j k : Fin n, (x i - x j)⁻¹ * (x i - x k)⁻¹ =
        (if j = k then (x i - x j)⁻¹ ^ 2 else 0) + f i j k := fun j k ↦ by
      by_cases hjk : j = k
      · subst hjk; simp [f, sq]
      · simp [f, hjk]
    simp_rw [hdiag, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rw [← Finset.add_sum_erase Finset.univ (fun j ↦ (x i - x j)⁻¹ ^ 2) (Finset.mem_univ i),
      sub_self, inv_zero, zero_pow two_ne_zero, zero_add]
  have hpair : (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹ ^ 2) =
      2 * ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, (x i - x j)⁻¹ ^ 2 := by
    simp_rw [sum_erase_eq_sum_Ioi_add_sum_Iio, Finset.sum_add_distrib,
      sum_Iio_eq_sum_Ioi (fun i j ↦ (x i - x j)⁻¹ ^ 2)]
    have hsym : ∀ i j : Fin n, (x j - x i)⁻¹ ^ 2 = (x i - x j)⁻¹ ^ 2 := fun i j ↦ by
      rw [← neg_sub (x i) (x j), inv_neg, neg_sq]
    simp_rw [hsym]
    ring
  simp_rw [dysonDrift_eq_inv_mul_sum, mul_pow, ← Finset.mul_sum, hexpand, Finset.sum_add_distrib]
  dsimp only [f]
  rw [sum_offDiag_mul_sub_inv_eq_zero hx, add_zero, hpair]
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

/-- On the `ε`-interior of the open Weyl chamber (`∀ i < j, ε ≤ x i - x j`), the `ε`-truncated
drift agrees with `dysonDrift n`. -/
theorem truncatedDysonDrift_eq_dysonDrift {ε : ℝ} {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i j : Fin n, i < j → ε ≤ x i - x j) :
    truncatedDysonDrift ε n x = dysonDrift n x := by
  ext i
  rw [truncatedDysonDrift_apply, dysonDrift_apply, sum_erase_eq_sum_Ioi_add_sum_Iio]
  congr 1
  have h1 : (∑ j ∈ Finset.Ioi i, (max (x i - x j) ε)⁻¹) =
      ∑ j ∈ Finset.Ioi i, (x i - x j)⁻¹ :=
    Finset.sum_congr rfl fun j hj ↦ by rw [max_eq_left (hx i j (Finset.mem_Ioi.1 hj))]
  have h2 : -(∑ j ∈ Finset.Iio i, (max (x j - x i) ε)⁻¹) =
      ∑ j ∈ Finset.Iio i, (x i - x j)⁻¹ := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [max_eq_left (hx j i (Finset.mem_Iio.1 hj)), ← neg_sub (x i) (x j), inv_neg, neg_neg]
  linarith

/-- Antisymmetric pairing formula for `truncatedDysonDrift`. -/
theorem sum_mul_truncatedDysonDrift_eq_sum_Ioi (ε : ℝ) (n : ℕ) (w x : Fin n → ℝ) :
    ∑ i : Fin n, w i * truncatedDysonDrift ε n x i =
      (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, (w i - w j) * (max (x i - x j) ε)⁻¹ := by
  simp only [truncatedDysonDrift_apply, ← mul_left_comm (n : ℝ)⁻¹, ← Finset.mul_sum]
  congr 1
  have hdist : ∀ i : Fin n,
      w i * ((∑ j ∈ Finset.Ioi i, (max (x i - x j) ε)⁻¹) -
        ∑ j ∈ Finset.Iio i, (max (x j - x i) ε)⁻¹) =
        (∑ j ∈ Finset.Ioi i, w i * (max (x i - x j) ε)⁻¹) -
          ∑ j ∈ Finset.Iio i, w i * (max (x j - x i) ε)⁻¹ := fun i ↦ by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  simp_rw [hdist, Finset.sum_sub_distrib,
    sum_Iio_eq_sum_Ioi (fun i j ↦ w i * (max (x j - x i) ε)⁻¹), ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

/-- The `ε`-truncated Dyson drift has zero coordinate sum at every configuration. -/
@[simp]
theorem sum_truncatedDysonDrift_eq_zero (ε : ℝ) (n : ℕ) (x : Fin n → ℝ) :
    ∑ i : Fin n, truncatedDysonDrift ε n x i = 0 := by
  have h := sum_mul_truncatedDysonDrift_eq_sum_Ioi ε n (fun _ ↦ 1) x
  simpa using h

/-- **Global monotone dissipativity of `truncatedDysonDrift`.** For `ε > 0`, `truncatedDysonDrift`
is dissipative on the entire space `Fin n → ℝ`, without restricting to ordered configurations. -/
theorem sum_truncatedDysonDrift_sub_mul_sub_nonpos {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (x y : Fin n → ℝ) :
    ∑ i : Fin n,
      (truncatedDysonDrift ε n x i - truncatedDysonDrift ε n y i) * (x i - y i) ≤ 0 := by
  have hx := sum_mul_truncatedDysonDrift_eq_sum_Ioi ε n (fun i ↦ x i - y i) x
  have hy := sum_mul_truncatedDysonDrift_eq_sum_Ioi ε n (fun i ↦ x i - y i) y
  have hlhs : ∑ i : Fin n,
      (truncatedDysonDrift ε n x i - truncatedDysonDrift ε n y i) * (x i - y i) =
      (∑ i : Fin n, (x i - y i) * truncatedDysonDrift ε n x i) -
        ∑ i : Fin n, (x i - y i) * truncatedDysonDrift ε n y i := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hlhs, hx, hy, ← mul_sub, ← Finset.sum_sub_distrib]
  refine mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (Nat.cast_nonneg n)) ?_
  refine Finset.sum_nonpos fun i _ ↦ ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_nonpos fun j _ ↦ ?_
  set a := x i - x j
  set b := y i - y j
  have hterm : ((x i - y i) - (x j - y j)) * (max a ε)⁻¹ -
      ((x i - y i) - (x j - y j)) * (max b ε)⁻¹ =
      (a - b) * ((max a ε)⁻¹ - (max b ε)⁻¹) := by
    dsimp [a, b]
    ring
  rw [hterm]
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
    LipschitzWith ⟨2 * ε⁻¹ ^ 2, by positivity⟩ (truncatedDysonDrift ε n) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  refine (dist_pi_le_iff (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)).2 fun i ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Fin.elim0 i
  rw [Real.dist_eq, truncatedDysonDrift_apply, truncatedDysonDrift_apply, ← mul_sub, abs_mul,
    abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg n))]
  have hdiff : ((∑ j ∈ Finset.Ioi i, (max (x i - x j) ε)⁻¹) -
        ∑ j ∈ Finset.Iio i, (max (x j - x i) ε)⁻¹) -
      ((∑ j ∈ Finset.Ioi i, (max (y i - y j) ε)⁻¹) -
        ∑ j ∈ Finset.Iio i, (max (y j - y i) ε)⁻¹) =
      (∑ j ∈ Finset.Ioi i, ((max (x i - x j) ε)⁻¹ - (max (y i - y j) ε)⁻¹)) -
        ∑ j ∈ Finset.Iio i, ((max (x j - x i) ε)⁻¹ - (max (y j - y i) ε)⁻¹) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    ring
  rw [hdiff]
  have hcard : ((Finset.Ioi i).card : ℝ) + ((Finset.Iio i).card : ℝ) ≤ n := by
    have hunion : (Finset.Ioi i ∪ Finset.Iio i).card =
        (Finset.Ioi i).card + (Finset.Iio i).card :=
      Finset.card_union_of_disjoint (Finset.disjoint_Ioi_Iio i)
    have hle : (Finset.Ioi i ∪ Finset.Iio i).card ≤ n :=
      (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
    exact_mod_cast hunion ▸ hle
  have hsum : |(∑ j ∈ Finset.Ioi i, ((max (x i - x j) ε)⁻¹ - (max (y i - y j) ε)⁻¹)) -
        ∑ j ∈ Finset.Iio i, ((max (x j - x i) ε)⁻¹ - (max (y j - y i) ε)⁻¹)| ≤
      (n : ℝ) * (2 * ε⁻¹ ^ 2 * dist x y) := by
    calc |(∑ j ∈ Finset.Ioi i, ((max (x i - x j) ε)⁻¹ - (max (y i - y j) ε)⁻¹)) -
          ∑ j ∈ Finset.Iio i, ((max (x j - x i) ε)⁻¹ - (max (y j - y i) ε)⁻¹)|
        ≤ |∑ j ∈ Finset.Ioi i, ((max (x i - x j) ε)⁻¹ - (max (y i - y j) ε)⁻¹)| +
            |∑ j ∈ Finset.Iio i, ((max (x j - x i) ε)⁻¹ - (max (y j - y i) ε)⁻¹)| :=
          abs_sub _ _
      _ ≤ (∑ j ∈ Finset.Ioi i, |(max (x i - x j) ε)⁻¹ - (max (y i - y j) ε)⁻¹|) +
            ∑ j ∈ Finset.Iio i, |(max (x j - x i) ε)⁻¹ - (max (y j - y i) ε)⁻¹| :=
          add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ (∑ _j ∈ Finset.Ioi i, 2 * ε⁻¹ ^ 2 * dist x y) +
            ∑ _j ∈ Finset.Iio i, 2 * ε⁻¹ ^ 2 * dist x y :=
          add_le_add (Finset.sum_le_sum fun j _ ↦ abs_truncatedGap_sub_le hε x y i j)
            (Finset.sum_le_sum fun j _ ↦ abs_truncatedGap_sub_le hε x y j i)
      _ = (((Finset.Ioi i).card : ℝ) + ((Finset.Iio i).card : ℝ)) *
            (2 * ε⁻¹ ^ 2 * dist x y) := by
          simp [nsmul_eq_mul, add_mul]
      _ ≤ (n : ℝ) * (2 * ε⁻¹ ^ 2 * dist x y) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
  calc (n : ℝ)⁻¹ * |(∑ j ∈ Finset.Ioi i, ((max (x i - x j) ε)⁻¹ - (max (y i - y j) ε)⁻¹)) -
        ∑ j ∈ Finset.Iio i, ((max (x j - x i) ε)⁻¹ - (max (y j - y i) ε)⁻¹)|
      ≤ (n : ℝ)⁻¹ * ((n : ℝ) * (2 * ε⁻¹ ^ 2 * dist x y)) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 (Nat.cast_nonneg n))
    _ = 2 * ε⁻¹ ^ 2 * dist x y :=
        inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 hn.ne') _

/-- `truncatedDysonDrift ε n` is globally continuous on `Fin n → ℝ` for every `ε > 0`. -/
theorem continuous_truncatedDysonDrift {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    Continuous (truncatedDysonDrift ε n) :=
  (lipschitzWith_truncatedDysonDrift hε n).continuous

end TauCeti.Probability
