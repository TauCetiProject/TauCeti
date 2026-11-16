/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import TauCeti.Analysis.Sobolev.Wkp.Basic

/-!
# Seminorms on higher-order Sobolev spaces

An element of `W^{k,p}(Ω)` (`TauCeti.Wkp`) is built recursively by adjoining one weak derivative
at a time: order `0` is `Lᵖ(Ω)`, order `1` is `TauCeti.W1p`, and each stage `k + 2` adjoins the
weak Fréchet derivative of the highest recorded derivative at stage `k + 1` via
`TauCeti.WeakDerivStep`. Accessing an intermediate weak derivative of order `j + 1 ≤ k`, or the
corresponding homogeneous Sobolev seminorm `|u|_{j+1,p}`, goes through truncating `u` from order
`k` down to order `j + 1` with `TauCeti.Wkp.toOrderL` and applying `TauCeti.Wkp.iteratedGradient`.

This file defines the family of Sobolev seminorms
`TauCeti.Wkp.seminorm k j h : Seminorm ℝ (Wkp mu Omega p k)` for `j ≤ k`. At `j = 0` the seminorm
is `‖value k u‖`; at `j + 1` it is `‖iteratedGradient j (toOrderL h u)‖`.

## Norm comparisons

Let `S(u) = √(∑_{j=0}^k |u|_{j,p}²)`. Above first order, each `WeakDerivStep` uses the Euclidean
product norm, so `‖u‖² = ‖lowerOrder (k + 1) u‖² + ‖iteratedGradient (k + 1) u‖²` holds for every
exponent `p` (`TauCeti.Wkp.norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ`). All
departure between the iterated graph norm `‖u‖` and `S(u)` therefore originates at first order,
where `TauCeti.W1p` takes the `Lᵖ` norm of the pointwise Euclidean norm `√(|u|² + ‖∇u‖²)`:

* For `p = 2`, Fubini's theorem makes the first-order norm satisfy `‖u‖² = |u|_{0,2}² + |u|_{1,2}²`
  as well, so `‖u‖ = S(u)` at every order `k` (`TauCeti.Wkp.norm_eq_sqrt_sum_seminorm_sq`).
* For general `1 ≤ p ≤ ∞` and every order `k`, the component bounds `|u|_{0,p} ≤ ‖u‖` and
  `|u|_{1,p} ≤ ‖u‖` together with the triangle inequality `‖u‖ ≤ |u|_{0,p} + |u|_{1,p}` at order `1`
  propagate up the Euclidean graph stages without accumulating extra factors, giving the uniform
  two-sided equivalence
  `S(u) ≤ √2 ‖u‖` (`TauCeti.Wkp.sqrt_le_sqrt_two_mul_norm`) and
  `‖u‖ ≤ √2 S(u)` (`TauCeti.Wkp.norm_le_sqrt_two_mul`).
  The factor `√2` in the lower comparison is sharp: for `u(x) = sin x` in `W^{1,∞}(0, 2π)`, the
  pointwise Euclidean jet norm `√(sin² x + cos² x)` is identically `1` while `|u|_{0,∞} = 1` and
  `|u|_{1,∞} = 1`, so `‖u‖ = 1` and `S(u) = √2`.

## Main definitions

* `TauCeti.Wkp.seminorm`: the `j`th Sobolev seminorm `|·|_{j,p}` on `W^{k,p}(Ω)` for `j ≤ k`,
  bundled as a `Seminorm ℝ`.

## Main results

* `TauCeti.Wkp.seminorm_comp_toOrderL`, `TauCeti.Wkp.seminorm_toOrderL`,
  `TauCeti.Wkp.seminorm_lowerOrder`: compatibility of Sobolev seminorms with order truncation.
* `TauCeti.Wkp.seminorm_le_norm`, `TauCeti.Wkp.lipschitzWith_seminorm`,
  `TauCeti.Wkp.seminorm_zero_eq_zero_iff`, `TauCeti.Wkp.seminorm_succ_eq_zero_iff`: `1`-Lipschitz
  control by the graph norm and characterization of the kernels of the seminorms.
* `TauCeti.Wkp.norm_le_sqrt_two_mul`, `TauCeti.Wkp.sqrt_le_sqrt_two_mul_norm`,
  `TauCeti.Wkp.norm_eq_sqrt_sum_seminorm_sq`: equivalence between the Sobolev graph norm and the
  Euclidean combination of the seminorms, with equality at `p = 2`.
* `TauCeti.Wkp.norm_le_sum_seminorm`, `TauCeti.Wkp.sum_seminorm_le_mul_norm`: two-sided comparison
  between the Sobolev graph norm and the `ℓ¹` sum of the seminorms.

## References

* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Academic Press, 2003, Chapter 3.
* S. C. Brenner and L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, Chapter 4.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., American Mathematical Society, 2010,
  §5.2.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped ENNReal

section Seminorms

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace Wkp

/-! ### Sobolev seminorms -/

/-- The `j`th Sobolev seminorm `|·|_{j,p}` on `W^{k,p}(Ω)` (`j ≤ k`), bundled as an `ℝ`-seminorm.
At order `0` it is the `Lᵖ(Ω)` norm of `value k u`; at order `j + 1` it is the `Lᵖ(Ω)` norm of the
weak derivative `iteratedGradient j (toOrderL h u)`. -/
def seminorm (k : ℕ) : (j : ℕ) → j ≤ k → Seminorm ℝ (Wkp mu Omega p k)
  | 0, _ =>
      (normSeminorm ℝ (Lp ℝ p (mu.restrict Omega))).comp
        (valueL (mu := mu) (Omega := Omega) (p := p) k).toLinearMap
  | j + 1, h =>
      (normSeminorm ℝ (Lp (IteratedGradient E j) p (mu.restrict Omega))).comp
        ((iteratedGradientL (mu := mu) (Omega := Omega) (p := p) j).comp
          (toOrderL (mu := mu) (Omega := Omega) (p := p) h)).toLinearMap

/-- At derivative order `0`, the Sobolev seminorm is the `Lᵖ` norm of the value component. -/
@[simp low]
theorem seminorm_zero_apply {k : ℕ} (h : 0 ≤ k) (u : Wkp mu Omega p k) :
    seminorm k 0 h u = ‖value k u‖ := by
  simp only [seminorm, Seminorm.comp_apply, ContinuousLinearMap.coe_coe, coe_normSeminorm,
    valueL_apply]

/-- At derivative order `j + 1`, the Sobolev seminorm is the `Lᵖ` norm of the weak derivative
`iteratedGradient j (toOrderL h u)`. -/
@[simp low]
theorem seminorm_succ_apply {j k : ℕ} (h : j + 1 ≤ k) (u : Wkp mu Omega p k) :
    seminorm k (j + 1) h u = ‖iteratedGradient j (toOrderL h u)‖ := by
  simp only [seminorm, Seminorm.comp_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, coe_normSeminorm]
  rw [iteratedGradientL_apply]

/-- At ambient order `0`, the unique Sobolev seminorm is the `Lᵖ` norm itself. -/
theorem seminorm_zero_zero (h : 0 ≤ 0) (u : Wkp mu Omega p 0) :
    seminorm 0 0 h u = ‖u‖ := by
  rw [seminorm_zero_apply, value_zero]

/-- On `W^{1,p}(Ω)`, the `0`th seminorm is the `Lᵖ` norm of `W1p.value`. -/
theorem seminorm_one_zero (h : 0 ≤ 1) (u : Wkp mu Omega p 1) :
    seminorm 1 0 h u = ‖W1p.value u‖ := by
  rw [seminorm_zero_apply, value_one]

/-- On `W^{1,p}(Ω)`, the `1`st seminorm is the `Lᵖ` norm of `W1p.gradient`. -/
theorem seminorm_one_one (h : 1 ≤ 1) (u : Wkp mu Omega p 1) :
    seminorm 1 1 h u = ‖W1p.gradient u‖ := by
  rw [seminorm_succ_apply, toOrderL_self_apply, iteratedGradient_zero]

/-- At positive order `k + 1`, the top seminorm `|u|_{k+1,p}` is `‖iteratedGradient k u‖`. -/
theorem seminorm_top_succ (k : ℕ) (h : k + 1 ≤ k + 1) (u : Wkp mu Omega p (k + 1)) :
    seminorm (k + 1) (k + 1) h u = ‖iteratedGradient k u‖ := by
  rw [seminorm_succ_apply, toOrderL_self_apply]

/-- Pulling back the `i`th seminorm on `W^{j,p}(Ω)` along `toOrderL` gives the `i`th seminorm on
`W^{k,p}(Ω)`. -/
@[simp]
theorem seminorm_comp_toOrderL {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (seminorm (mu := mu) (Omega := Omega) (p := p) j i hij).comp (toOrderL hjk).toLinearMap =
      seminorm k i (hij.trans hjk) := by
  ext u
  cases i with
  | zero =>
      simp only [Seminorm.comp_apply, ContinuousLinearMap.coe_coe, seminorm_zero_apply,
        value_toOrderL]
  | succ i =>
      simp only [Seminorm.comp_apply, ContinuousLinearMap.coe_coe, seminorm_succ_apply]
      rw [toOrderL_toOrderL]

/-- Order truncation preserves every Sobolev seminorm up to the truncated order. -/
@[simp]
theorem seminorm_toOrderL {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (u : Wkp mu Omega p k) :
    seminorm j i hij (toOrderL hjk u) = seminorm k i (hij.trans hjk) u :=
  DFunLike.congr_fun (seminorm_comp_toOrderL hij hjk) u

/-- The `j`th seminorm of `lowerOrder k u` (`j ≤ k`) equals the `j`th seminorm of `u` at order
`k + 1`. -/
theorem seminorm_lowerOrder {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p (k + 1)) :
    seminorm k j h (lowerOrder k u) = seminorm (k + 1) j (Nat.le_succ_of_le h) u := by
  rw [← toOrderL_succ_self_apply k k.le_succ u, seminorm_toOrderL]

/-- For `j ≤ k + 1`, the `j`th seminorm of `mk k u D hD` is the `j`th seminorm of `u`. -/
theorem seminorm_mk_of_le {j k : ℕ} (h : j ≤ k + 1) (h' : j ≤ k + 2)
    (u : Wkp mu Omega p (k + 1))
    (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (hD : HasWeakFDerivOn mu Omega (iteratedGradient k u) D) :
    seminorm (k + 2) j h' (mk k u D hD) = seminorm (k + 1) j h u := by
  rw [← seminorm_lowerOrder h, lowerOrder_mk]

/-- The top seminorm of `mk k u D hD` is the `Lᵖ` norm of the adjoined weak derivative `D`. -/
theorem seminorm_mk_top (k : ℕ) (h : k + 2 ≤ k + 2) (u : Wkp mu Omega p (k + 1))
    (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (hD : HasWeakFDerivOn mu Omega (iteratedGradient k u) D) :
    seminorm (k + 2) (k + 2) h (mk k u D hD) = ‖D‖ := by
  rw [seminorm_top_succ, iteratedGradient_mk]

/-- Every Sobolev seminorm is bounded by the full Sobolev graph norm. -/
theorem seminorm_le_norm {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    seminorm k j h u ≤ ‖u‖ := by
  cases j with
  | zero =>
      rw [seminorm_zero_apply]
      exact norm_value_le k u
  | succ j =>
      rw [seminorm_succ_apply]
      exact (norm_iteratedGradient_le j (toOrderL h u)).trans (norm_toOrderL_apply_le h u)

/-- As bundled seminorms, each `seminorm k j h` is bounded by `normSeminorm`. -/
theorem seminorm_le_normSeminorm {j k : ℕ} (h : j ≤ k) :
    seminorm (mu := mu) (Omega := Omega) (p := p) k j h ≤
      normSeminorm ℝ (Wkp mu Omega p k) :=
  Seminorm.le_def.2 fun u => by
    rw [coe_normSeminorm]
    exact seminorm_le_norm h u

/-- Every Sobolev seminorm is `1`-Lipschitz with respect to the Sobolev graph norm. -/
theorem lipschitzWith_seminorm {j k : ℕ} (h : j ≤ k) :
    LipschitzWith 1 (seminorm (mu := mu) (Omega := Omega) (p := p) k j h) :=
  LipschitzWith.of_dist_le_mul fun u v => by
    rw [NNReal.coe_one, one_mul, Real.dist_eq, ← Real.norm_eq_abs, dist_eq_norm]
    exact ((seminorm k j h).norm_sub_map_le_sub u v).trans (seminorm_le_norm h (u - v))

/-- Every Sobolev seminorm is continuous with respect to the Sobolev graph topology. -/
theorem continuous_seminorm {j k : ℕ} (h : j ≤ k) :
    Continuous (seminorm (mu := mu) (Omega := Omega) (p := p) k j h) :=
  (lipschitzWith_seminorm h).continuous

/-- The `0`th Sobolev seminorm vanishes if and only if the Sobolev function itself vanishes. -/
theorem seminorm_zero_eq_zero_iff {k : ℕ} (h : 0 ≤ k) (u : Wkp mu Omega p k) :
    seminorm k 0 h u = 0 ↔ u = 0 := by
  rw [seminorm_zero_apply, ← toOrderL_zero_apply k h u, norm_eq_zero, toOrderL_eq_zero_iff]

/-- For `j + 1 ≤ k`, the `(j + 1)`st Sobolev seminorm vanishes if and only if the weak derivative
field `iteratedGradient j (toOrderL h u)` vanishes in `Lᵖ(Ω)`. -/
theorem seminorm_succ_eq_zero_iff {j k : ℕ} (h : j + 1 ≤ k) (u : Wkp mu Omega p k) :
    seminorm k (j + 1) h u = 0 ↔ iteratedGradient j (toOrderL h u) = 0 := by
  rw [seminorm_succ_apply, norm_eq_zero]

/-- At positive order `k + 1`, the top seminorm vanishes if and only if `iteratedGradient k u`
vanishes in `Lᵖ(Ω)`. -/
theorem seminorm_top_succ_eq_zero_iff (k : ℕ) (h : k + 1 ≤ k + 1)
    (u : Wkp mu Omega p (k + 1)) :
    seminorm (k + 1) (k + 1) h u = 0 ↔ iteratedGradient k u = 0 := by
  rw [seminorm_top_succ, norm_eq_zero]

/-! ### Equivalence of the Sobolev norm and the seminorms -/

/-- At order `0`, the sum of the Sobolev seminorms is `‖u‖`. -/
theorem sum_seminorm_zero (u : Wkp mu Omega p 0) :
    (∑ j : Fin 1, seminorm 0 j j.is_le u) = ‖u‖ := by
  simp only [Fin.sum_univ_one, Fin.val_zero]
  exact seminorm_zero_zero _ u

/-- Splitting off the top seminorm at order `k + 1` expresses the sum of Sobolev seminorms in
terms of `lowerOrder k u` and `iteratedGradient k u`. -/
theorem sum_seminorm_succ (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    (∑ j : Fin (k + 2), seminorm (k + 1) j j.is_le u) =
      (∑ j : Fin (k + 1), seminorm k j j.is_le (lowerOrder k u)) +
        ‖iteratedGradient k u‖ := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last]
  rw [seminorm_top_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.val_castSucc]
  rw [← seminorm_lowerOrder j.is_le]

/-- At order `0`, the sum of squared seminorms is `‖u‖²`. -/
theorem sum_seminorm_sq_zero (u : Wkp mu Omega p 0) :
    (∑ j : Fin 1, seminorm 0 j j.is_le u ^ 2) = ‖u‖ ^ 2 := by
  simp only [Fin.sum_univ_one, Fin.val_zero]
  rw [seminorm_zero_zero]

/-- Splitting off the top seminorm at order `k + 1` expresses the sum of squared seminorms in
terms of `lowerOrder k u` and `iteratedGradient k u`. -/
theorem sum_seminorm_sq_succ (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    (∑ j : Fin (k + 2), seminorm (k + 1) j j.is_le u ^ 2) =
      (∑ j : Fin (k + 1), seminorm k j j.is_le (lowerOrder k u) ^ 2) +
        ‖iteratedGradient k u‖ ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last]
  rw [seminorm_top_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.val_castSucc]
  rw [← seminorm_lowerOrder j.is_le]

/-- For every order `k` and exponent `1 ≤ p ≤ ∞`, the squared Sobolev norm is at most twice the
sum of squared seminorms. -/
theorem norm_sq_le_two_mul_sum_seminorm_sq :
    ∀ {k : ℕ} (u : Wkp mu Omega p k),
      ‖u‖ ^ 2 ≤ 2 * ∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2
  | 0, u => by
      rw [sum_seminorm_sq_zero]
      linarith [sq_nonneg ‖u‖]
  | 1, u => by
      rw [sum_seminorm_sq_succ 0 u, sum_seminorm_sq_zero]
      have hle := norm_le_norm_lowerOrder_add_norm_iteratedGradient 0 u
      nlinarith [norm_nonneg u, sq_nonneg (‖lowerOrder 0 u‖ - ‖iteratedGradient 0 u‖)]
  | k + 2, u => by
      rw [norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k u,
        sum_seminorm_sq_succ (k + 1) u]
      have hlow := norm_sq_le_two_mul_sum_seminorm_sq (lowerOrder (k + 1) u)
      linarith [sq_nonneg ‖iteratedGradient (k + 1) u‖]

/-- For every order `k` and exponent `1 ≤ p ≤ ∞`, the sum of squared seminorms is at most twice
the squared Sobolev norm. -/
theorem sum_seminorm_sq_le_two_mul_norm_sq :
    ∀ {k : ℕ} (u : Wkp mu Omega p k),
      (∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) ≤ 2 * ‖u‖ ^ 2
  | 0, u => by
      rw [sum_seminorm_sq_zero]
      linarith [sq_nonneg ‖u‖]
  | 1, u => by
      rw [sum_seminorm_sq_succ 0 u, sum_seminorm_sq_zero]
      have h₀ : ‖lowerOrder 0 u‖ ^ 2 ≤ ‖u‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_lowerOrder_le 0 u) 2
      have h₁ : ‖iteratedGradient 0 u‖ ^ 2 ≤ ‖u‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_iteratedGradient_le 0 u) 2
      linarith
  | k + 2, u => by
      rw [norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k u,
        sum_seminorm_sq_succ (k + 1) u]
      have hlow := sum_seminorm_sq_le_two_mul_norm_sq (lowerOrder (k + 1) u)
      linarith [sq_nonneg ‖iteratedGradient (k + 1) u‖]

/-- **Upper comparison of the Sobolev norm with the seminorms.** For every order `k` and exponent
`1 ≤ p ≤ ∞`, `‖u‖ ≤ √2 √(∑_{j=0}^k |u|_{j,p}²)`. -/
theorem norm_le_sqrt_two_mul {k : ℕ} (u : Wkp mu Omega p k) :
    ‖u‖ ≤ √2 * √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) :=
  calc ‖u‖ = √(‖u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg u)).symm
    _ ≤ √(2 * ∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) :=
        Real.sqrt_le_sqrt (norm_sq_le_two_mul_sum_seminorm_sq u)
    _ = √2 * √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) :=
        Real.sqrt_mul zero_le_two _

/-- **Lower comparison of the Sobolev norm with the seminorms.** For every order `k` and exponent
`1 ≤ p ≤ ∞`, `√(∑_{j=0}^k |u|_{j,p}²) ≤ √2 ‖u‖`. -/
theorem sqrt_le_sqrt_two_mul_norm {k : ℕ} (u : Wkp mu Omega p k) :
    √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) ≤ √2 * ‖u‖ :=
  calc √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2)
      ≤ √(2 * ‖u‖ ^ 2) := Real.sqrt_le_sqrt (sum_seminorm_sq_le_two_mul_norm_sq u)
    _ = √2 * ‖u‖ := by rw [Real.sqrt_mul zero_le_two, Real.sqrt_sq (norm_nonneg u)]

/-- At exponent `p = 2`, the squared Sobolev norm equals the sum of squared seminorms at every
order `k`. -/
theorem norm_sq_eq_sum_seminorm_sq :
    ∀ {k : ℕ} (u : Wkp mu Omega 2 k),
      ‖u‖ ^ 2 = ∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2
  | 0, u => (sum_seminorm_sq_zero u).symm
  | k + 1, u => by
      rw [norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq k u,
        norm_sq_eq_sum_seminorm_sq (lowerOrder k u), sum_seminorm_sq_succ k u]

/-- At exponent `p = 2`, the Sobolev norm equals `√(∑_{j=0}^k |u|_{j,2}²)` at every order `k`. -/
theorem norm_eq_sqrt_sum_seminorm_sq {k : ℕ} (u : Wkp mu Omega 2 k) :
    ‖u‖ = √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) := by
  rw [← norm_sq_eq_sum_seminorm_sq u, Real.sqrt_sq (norm_nonneg u)]

/-- The Sobolev norm is bounded by the `ℓ¹` sum of the Sobolev seminorms. -/
theorem norm_le_sum_seminorm :
    ∀ {k : ℕ} (u : Wkp mu Omega p k),
      ‖u‖ ≤ ∑ j : Fin (k + 1), seminorm k j j.is_le u
  | 0, u => by rw [sum_seminorm_zero]
  | k + 1, u => by
      rw [sum_seminorm_succ]
      have hlow := norm_le_sum_seminorm (lowerOrder k u)
      linarith [norm_le_norm_lowerOrder_add_norm_iteratedGradient k u]

/-- The `ℓ¹` sum of the Sobolev seminorms is at most `(k + 1) ‖u‖`. -/
theorem sum_seminorm_le_mul_norm {k : ℕ} (u : Wkp mu Omega p k) :
    (∑ j : Fin (k + 1), seminorm k j j.is_le u) ≤ (k + 1 : ℝ) * ‖u‖ := by
  calc (∑ j : Fin (k + 1), seminorm k j j.is_le u)
      ≤ ∑ _ : Fin (k + 1), ‖u‖ := Finset.sum_le_sum fun j _ => seminorm_le_norm j.is_le u
    _ = (k + 1 : ℝ) * ‖u‖ := by simp [nsmul_eq_mul]

/-- The sum of squared Sobolev seminorms vanishes if and only if `u = 0`. -/
@[simp]
theorem sum_seminorm_sq_eq_zero_iff {k : ℕ} (u : Wkp mu Omega p k) :
    (∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) = 0 ↔ u = 0 := by
  refine ⟨fun h => ?_, fun h => by subst h; simp⟩
  have h0 : ‖u‖ ^ 2 ≤ 0 := by
    simpa only [h, mul_zero] using norm_sq_le_two_mul_sum_seminorm_sq u
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm h0 (sq_nonneg ‖u‖)))

end Wkp

end Seminorms

end TauCeti
