/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import TauCeti.Analysis.Sobolev.Wkp.Classical
public import TauCeti.Analysis.Sobolev.Wkp.Exponent
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Seminorms on arbitrary-order Sobolev spaces

Using the order-truncation operators `TauCeti.Wkp.toOrderL`, each intermediate weak derivative of
order `j + 1 ≤ k` of `u ∈ TauCeti.Wkp mu Omega p k` is accessed uniformly as
`TauCeti.Wkp.iteratedGradient j (toOrderL h u)`. Taking `Lᵖ` norms of the value (`j = 0`) and of
each intermediate weak derivative (`1 ≤ j ≤ k`) defines the standard family of Sobolev seminorms
`TauCeti.Wkp.seminorm k j h` on `W^{k,p}(Ω)`, bundled as Mathlib `Seminorm`s over `ℝ`.

Order truncation (`TauCeti.Wkp.toOrderL`), subdomain restriction (`TauCeti.Wkp.restrictL`), and
exponent lowering on finite-measure domains (`TauCeti.Wkp.ofExponentLEL`) obey the natural seminorm
identities and estimates. On smooth representatives, each seminorm agrees with the classical
multilinear derivative `Lᵖ` norm
`MeasureTheory.lpNorm (iteratedFDeriv ℝ j f) p (mu.restrict Omega)`.

At `p = 2`, the iterated graph norm on `W^{k,2}(Ω)` equals the Euclidean combination
`S(u) = √(∑_{j ≤ k} |u|_{j,2}²)` at every order `k`. For general `1 ≤ p ≤ ∞`, the first-order
norm is the `Lᵖ` norm of the pointwise Euclidean norm of `(u, ∇u)` rather than
`(‖u‖_p² + ‖∇u‖_p²)^{1/2}`, while every higher graph step uses an exact Euclidean product norm.
Consequently `S(u)` and `‖u‖` are equivalent up to a universal factor of `√2` independent of `k`,
`p`, the dimension, and the domain: `‖u‖ ≤ √2 · S(u)` and `S(u) ≤ √2 · ‖u‖`. On `(0, 2π)` at
`p = ∞` and `k = 1`, `sin` has graph norm `1` and `S(sin) = √2`, showing that the factor `√2` in
`TauCeti.Wkp.sqrt_le_sqrt_two_mul_norm` is sharp.

## Main definitions

* `TauCeti.Wkp.seminorm`: the order-`j` Sobolev seminorm `|·|_{j,p}` on `W^{k,p}(Ω)` for `j ≤ k`,
  bundled as a `Seminorm ℝ (Wkp mu Omega p k)`.

## Main results

* `TauCeti.Wkp.seminorm_toOrderL`, `TauCeti.Wkp.seminorm_lowerOrder`,
  `TauCeti.Wkp.seminorm_zero_eq_zero_iff`, `TauCeti.Wkp.continuous_seminorm`: compatibility with
  order truncation, vanishing of the order-zero seminorm, and continuity.
* `TauCeti.Wkp.seminorm_eq_lpNorm_of_contDiffOn`,
  `TauCeti.Wkp.seminorm_rpow_eq_integral_norm_iteratedFDeriv_rpow_of_contDiffOn`,
  `TauCeti.Wkp.seminorm_exponent_top_le_of_contDiffOn`,
  `TauCeti.Wkp.norm_iteratedFDeriv_le_seminorm_exponent_top_of_contDiffOn`: classical
  identification, finite-exponent integral formula, and pointwise `L^∞` bounds for `C^j`
  representatives.
* `TauCeti.Wkp.seminorm_restrictL_le`, `TauCeti.Wkp.seminorm_ofExponentLEL_le`: monotonicity under
  subdomain restriction and Hölder scaling `μ(Ω) ^ (1/p - 1/q)` under exponent lowering.
* `TauCeti.Wkp.norm_eq_sqrt_sum_seminorm_sq`, `TauCeti.Wkp.norm_le_sqrt_two_mul`,
  `TauCeti.Wkp.sqrt_le_sqrt_two_mul_norm`, `TauCeti.Wkp.tendsto_iff_forall_seminorm_sub`: exact
  `p = 2` identity, sharp `√2` norm comparisons for every `k` and `p`, and characterization of
  convergence via seminorms.

## References

* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., §3.1.
* S. C. Brenner and L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  §§4.1–4.2.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open MeasureTheory TopologicalSpace
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega U : Opens E} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-! ### Sobolev seminorms -/

/-- The order-`j` Sobolev seminorm `|·|_{j,p}` on `W^{k,p}(Ω)` for `j ≤ k`, bundled as a Mathlib
`Seminorm` over `ℝ`. At order `0` it is the `Lᵖ` norm of the value; at order `j + 1` it is the `Lᵖ`
norm of the order-`(j + 1)` weak derivative `iteratedGradient j (toOrderL h u)`. -/
def seminorm (k : ℕ) : (j : ℕ) → j ≤ k → Seminorm ℝ (Wkp mu Omega p k)
  | 0, _ => (normSeminorm ℝ (Lp ℝ p (mu.restrict Omega))).comp
      (valueL (mu := mu) (Omega := Omega) (p := p) k).toLinearMap
  | j + 1, h => (normSeminorm ℝ (Lp (IteratedGradient E j) p (mu.restrict Omega))).comp
      ((iteratedGradientL (mu := mu) (Omega := Omega) (p := p) j).comp
        (toOrderL (mu := mu) (Omega := Omega) (p := p) h)).toLinearMap

/-- The order-zero Sobolev seminorm is the pullback of the `Lᵖ` norm along `valueL k`. -/
theorem seminorm_zero (k : ℕ) (h : 0 ≤ k) :
    seminorm (mu := mu) (Omega := Omega) (p := p) k 0 h =
      (normSeminorm ℝ (Lp ℝ p (mu.restrict Omega))).comp
        (valueL (mu := mu) (Omega := Omega) (p := p) k).toLinearMap :=
  (rfl)

/-- The order-`(j + 1)` Sobolev seminorm is the pullback of the `Lᵖ` norm along
`(iteratedGradientL j).comp (toOrderL h)`. -/
theorem seminorm_succ (k j : ℕ) (h : j + 1 ≤ k) :
    seminorm (mu := mu) (Omega := Omega) (p := p) k (j + 1) h =
      (normSeminorm ℝ (Lp (IteratedGradient E j) p (mu.restrict Omega))).comp
        ((iteratedGradientL (mu := mu) (Omega := Omega) (p := p) j).comp
          (toOrderL (mu := mu) (Omega := Omega) (p := p) h)).toLinearMap :=
  (rfl)

/-- Evaluating the order-zero seminorm gives the `Lᵖ` norm of `value k u`. -/
@[simp]
theorem seminorm_zero_apply (k : ℕ) (h : 0 ≤ k) (u : Wkp mu Omega p k) :
    seminorm k 0 h u = ‖value k u‖ := by
  rw [seminorm_zero, Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe,
    valueL_apply]

/-- On `W^{0,p}(Ω) = Lᵖ(Ω)`, the order-zero Sobolev seminorm is `normSeminorm`. -/
@[simp]
theorem seminorm_zero_zero (h : 0 ≤ 0) :
    seminorm (mu := mu) (Omega := Omega) (p := p) 0 0 h =
      normSeminorm ℝ (Lp ℝ p (mu.restrict Omega)) := by
  ext u
  rw [seminorm_zero_apply, value_zero, coe_normSeminorm]

/-- Evaluating the order-`(j + 1)` seminorm gives the `Lᵖ` norm of
`iteratedGradient j (toOrderL h u)`. -/
@[simp]
theorem seminorm_succ_apply (k j : ℕ) (h : j + 1 ≤ k) (u : Wkp mu Omega p k) :
    seminorm k (j + 1) h u = ‖iteratedGradient j (toOrderL h u)‖ := by
  rw [seminorm_succ, Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, iteratedGradientL_apply]

/-- Evaluating the top seminorm on `W^{k+1,p}(Ω)` gives the `Lᵖ` norm of `iteratedGradient k u`. -/
theorem seminorm_succ_self_apply (k : ℕ) (h : k + 1 ≤ k + 1) (u : Wkp mu Omega p (k + 1)) :
    seminorm (k + 1) (k + 1) h u = ‖iteratedGradient k u‖ := by
  rw [seminorm_succ_apply, toOrderL_self, ContinuousLinearMap.id_apply]

/-- Pulling back the order-`i` seminorm along truncation `toOrderL h₂` gives the order-`i` seminorm
on the higher-order space. -/
@[simp]
theorem seminorm_comp_toOrderL {i j k : ℕ} (h₁ : i ≤ j) (h₂ : j ≤ k) :
    (seminorm (mu := mu) (Omega := Omega) (p := p) j i h₁).comp (toOrderL h₂).toLinearMap =
      seminorm k i (h₁.trans h₂) := by
  ext u
  cases i with
  | zero => simp
  | succ i =>
      simp only [Seminorm.comp_apply, ContinuousLinearMap.coe_coe, seminorm_succ_apply]
      rw [toOrderL_toOrderL]

/-- Order truncation preserves all seminorms up to the truncated order. -/
@[simp]
theorem seminorm_toOrderL {i j k : ℕ} (h₁ : i ≤ j) (h₂ : j ≤ k) (u : Wkp mu Omega p k) :
    seminorm j i h₁ (toOrderL h₂ u) = seminorm k i (h₁.trans h₂) u := by
  rw [← ContinuousLinearMap.coe_coe, ← Seminorm.comp_apply, seminorm_comp_toOrderL]

/-- Forgetting the highest derivative preserves every lower-order seminorm. -/
@[simp]
theorem seminorm_lowerOrder {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p (k + 1)) :
    seminorm k j h (lowerOrder k u) = seminorm (k + 1) j (Nat.le_succ_of_le h) u := by
  rw [← lowerOrderL_apply, ← toOrderL_le_succ k (Nat.le_succ k), seminorm_toOrderL]

/-- Adjoining a top derivative via `mk` preserves all seminorms of orders up to `k + 1`. -/
theorem seminorm_mk {j k : ℕ} (h₁ : j ≤ k + 1) (h₂ : j ≤ k + 2) (u : Wkp mu Omega p (k + 1))
    (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (hw : HasWeakFDerivOn mu Omega (iteratedGradient k u) D) :
    seminorm (k + 2) j h₂ (mk k u D hw) = seminorm (k + 1) j h₁ u := by
  rw [← seminorm_lowerOrder h₁ (mk k u D hw), lowerOrder_mk]

/-- The order-zero seminorm vanishes if and only if the Sobolev function itself is zero, since the
`Lᵖ` value determines all weak derivatives. -/
theorem seminorm_zero_eq_zero_iff (k : ℕ) (h : 0 ≤ k) (u : Wkp mu Omega p k) :
    seminorm k 0 h u = 0 ↔ u = 0 := by
  rw [seminorm_zero_apply, norm_eq_zero, ← valueL_apply]
  exact ⟨fun hu => ext k (by rw [← valueL_apply, ← valueL_apply, hu, map_zero]),
    fun hu => by rw [hu, map_zero]⟩

/-- Every Sobolev seminorm is bounded by the full Sobolev norm. -/
theorem seminorm_le_norm {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    seminorm k j h u ≤ ‖u‖ := by
  cases j with
  | zero =>
      rw [seminorm_zero_apply]
      exact norm_value_le k u
  | succ j =>
      rw [seminorm_succ_apply]
      exact (norm_iteratedGradient_le j (toOrderL h u)).trans (norm_toOrderL_le h u)

/-- In the lattice of real seminorms, each Sobolev seminorm is bounded above by `normSeminorm`. -/
theorem seminorm_le_normSeminorm {j k : ℕ} (h : j ≤ k) :
    seminorm (mu := mu) (Omega := Omega) (p := p) k j h ≤
      normSeminorm ℝ (Wkp mu Omega p k) :=
  fun u => seminorm_le_norm h u

/-- Every Sobolev seminorm is continuous with respect to the `W^{k,p}` norm topology. -/
theorem continuous_seminorm {j k : ℕ} (h : j ≤ k) :
    Continuous (seminorm (mu := mu) (Omega := Omega) (p := p) k j h) :=
  Seminorm.continuous_of_le continuous_norm (seminorm_le_normSeminorm h)

/-- Restricting a Sobolev function to an open subdomain does not increase any of its seminorms. -/
theorem seminorm_restrictL_le (hU : U ≤ Omega) {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    seminorm k j h (restrictL hU k u) ≤ seminorm k j h u := by
  cases j with
  | zero =>
      rw [seminorm_zero_apply, seminorm_zero_apply]
      exact (Lp.norm_eq_lpNorm_of_ae_eq (value_restrictL_ae hU k u)).trans_le
        (lpNorm_le_norm_of_ae_eq_of_le
          (Measure.restrict_mono_set mu (SetLike.coe_subset_coe.2 hU)) .rfl)
  | succ j =>
      rw [seminorm_succ_apply, seminorm_succ_apply]
      exact (Lp.norm_eq_lpNorm_of_ae_eq (iteratedGradient_toOrderL_restrictL_ae hU h u)).trans_le
        (lpNorm_le_norm_of_ae_eq_of_le
          (Measure.restrict_mono_set mu (SetLike.coe_subset_coe.2 hU)) .rfl)

/-- On a finite-measure domain, lowering the integrability exponent from `q` to `p ≤ q` scales each
Sobolev seminorm by at most `μ(Ω) ^ (1/p - 1/q)`. -/
theorem seminorm_ofExponentLEL_le [IsFiniteMeasure (mu.restrict (Omega : Set E))]
    (hpq : p ≤ q) {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega q k) :
    seminorm k j h (ofExponentLEL hpq k u) ≤
      (mu Omega ^ (1 / p.toReal - 1 / q.toReal)).toReal * seminorm k j h u := by
  cases j with
  | zero =>
      rw [seminorm_zero_apply, seminorm_zero_apply, value_ofExponentLEL]
      simpa only [Measure.restrict_apply_univ] using
        Lp.norm_ofExponentLEL_apply_le (𝕜 := ℝ) hpq (value k u)
  | succ j =>
      rw [seminorm_succ_apply, seminorm_succ_apply, toOrderL_ofExponentLEL,
        iteratedGradient_ofExponentLEL]
      simpa only [Measure.restrict_apply_univ] using
        Lp.norm_ofExponentLEL_apply_le (𝕜 := ℝ) hpq (iteratedGradient j (toOrderL h u))

/-- If `u ∈ W^{k,p}(Ω)` is represented almost everywhere on `Ω` by a `C^j` function `f` with
`j ≤ k`, then its order-`j` Sobolev seminorm equals the classical `Lᵖ` derivative seminorm
`lpNorm (iteratedFDeriv ℝ j f) p (mu.restrict Omega)`. -/
theorem seminorm_eq_lpNorm_of_contDiffOn {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k)
    {f : E → ℝ} (hf : ContDiffOn ℝ j f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    seminorm k j h u = lpNorm (iteratedFDeriv ℝ j f) p (mu.restrict Omega) := by
  cases j with
  | zero =>
      exact (seminorm_zero_apply k h u).trans (norm_value_eq_lpNorm_iteratedFDeriv_zero k u hu)
  | succ j =>
      rw [seminorm_succ_apply]
      exact norm_iteratedGradient_eq_lpNorm_of_contDiffOn j (toOrderL h u) hf
        (by rwa [value_toOrderL])

/-- At exponent `p = ∞`, if `u ∈ W^{k,∞}(Ω)` is represented almost everywhere on `Ω` by a `C^j`
function `f` with `j ≤ k` whose `j`-th Fréchet derivative has norm at most `C ≥ 0` on `Ω`, then
`seminorm k j h u ≤ C`. -/
theorem seminorm_exponent_top_le_of_contDiffOn {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega ∞ k)
    {f : E → ℝ} (hf : ContDiffOn ℝ j f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x ∈ Omega, ‖iteratedFDeriv ℝ j f x‖ ≤ C) :
    seminorm k j h u ≤ C := by
  have hmem := memLp_iteratedFDeriv_of_contDiffOn j (toOrderL h u) hf
    (by rwa [value_toOrderL]) j le_rfl
  rw [seminorm_eq_lpNorm_of_contDiffOn h u hf hu, ← Lp.norm_eq_lpNorm_of_ae_eq hmem.coeFn_toLp]
  refine Lp.norm_le_of_ae_bound_top hC ?_
  filter_upwards [hmem.coeFn_toLp, ae_restrict_mem Omega.isOpen.measurableSet] with x hx hxΩ
  exact hx ▸ hbound x hxΩ

/-- At exponent `p = ∞`, if `u ∈ W^{k,∞}(Ω)` is represented almost everywhere on `Ω` by a `C^j`
function `f` with `j ≤ k`, then `‖iteratedFDeriv ℝ j f x₀‖ ≤ seminorm k j h u` at every point
`x₀ ∈ Omega`. -/
theorem norm_iteratedFDeriv_le_seminorm_exponent_top_of_contDiffOn {j k : ℕ} (h : j ≤ k)
    (u : Wkp mu Omega ∞ k) {f : E → ℝ} (hf : ContDiffOn ℝ j f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) {x₀ : E} (hx₀ : x₀ ∈ Omega) :
    ‖iteratedFDeriv ℝ j f x₀‖ ≤ seminorm k j h u := by
  rw [seminorm_eq_lpNorm_of_contDiffOn h u hf hu]
  have hae := ae_le_lpNorm_exponent_top
    (memLp_iteratedFDeriv_of_contDiffOn j (toOrderL h u) hf (by rwa [value_toOrderL]) j le_rfl)
  exact sup_eq_right.1 (Measure.eqOn_open_of_ae_eq (hae.mono fun _ => sup_eq_right.2) Omega.isOpen
    (((ContinuousOn.continuousOn_iteratedFDeriv hf Omega.isOpen le_rfl).norm).sup
      continuousOn_const)
    continuousOn_const hx₀)

/-! ### Comparison between the Sobolev norm and the seminorms -/

/-- At order zero, the sum of squared Sobolev seminorms reduces to the squared `Lᵖ` norm. -/
theorem sum_seminorm_sq_zero (u : Wkp mu Omega p 0) :
    ∑ j : Fin 1, seminorm 0 j j.is_le u ^ 2 = ‖u‖ ^ 2 := by
  simp

/-- At order `k + 1`, the sum of squared seminorms splits into the sum of squared seminorms of
`lowerOrder k u` plus the squared norm of the highest weak derivative `iteratedGradient k u`. -/
theorem sum_seminorm_sq_succ (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    ∑ j : Fin (k + 2), seminorm (k + 1) j j.is_le u ^ 2 =
      (∑ j : Fin (k + 1), seminorm k j j.is_le (lowerOrder k u) ^ 2) +
        ‖iteratedGradient k u‖ ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [seminorm_lowerOrder j.is_le u]
    rfl
  · simp only [Fin.val_last]
    rw [seminorm_succ_self_apply]

/-- At exponent `p = 2`, the squared Sobolev norm equals the sum of the squared seminorms at every
order `k`. -/
theorem norm_sq_eq_sum_seminorm_sq :
    ∀ (k : ℕ) (u : Wkp mu Omega 2 k),
      ‖u‖ ^ 2 = ∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2
  | 0, u => (sum_seminorm_sq_zero u).symm
  | k + 1, u => by
      rw [norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq k u,
        norm_sq_eq_sum_seminorm_sq k (lowerOrder k u), sum_seminorm_sq_succ k u]

/-- At exponent `p = 2`, the Sobolev norm equals the square root of the sum of squared seminorms at
every order `k`. -/
theorem norm_eq_sqrt_sum_seminorm_sq (k : ℕ) (u : Wkp mu Omega 2 k) :
    ‖u‖ = √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) := by
  rw [← norm_sq_eq_sum_seminorm_sq k u, Real.sqrt_sq (norm_nonneg u)]

/-- For every order `k` and exponent `p`, the squared Sobolev norm is at most twice the sum of the
squared seminorms. -/
theorem norm_sq_le_two_mul_sum_seminorm_sq :
    ∀ (k : ℕ) (u : Wkp mu Omega p k),
      ‖u‖ ^ 2 ≤ 2 * ∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2
  | 0, u => by
      rw [sum_seminorm_sq_zero]
      nlinarith [sq_nonneg ‖u‖]
  | 1, u => by
      rw [sum_seminorm_sq_succ 0 u, sum_seminorm_sq_zero]
      have hle := norm_le_norm_lowerOrder_add_norm_iteratedGradient 0 u
      nlinarith [norm_nonneg u, sq_nonneg (‖lowerOrder 0 u‖ - ‖iteratedGradient 0 u‖)]
  | k + 2, u => by
      rw [norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k u,
        sum_seminorm_sq_succ (k + 1) u]
      have ih := norm_sq_le_two_mul_sum_seminorm_sq (k + 1) (lowerOrder (k + 1) u)
      nlinarith [sq_nonneg ‖iteratedGradient (k + 1) u‖]

/-- For every order `k` and exponent `p`, the sum of the squared seminorms is at most twice the
squared Sobolev norm. -/
theorem sum_seminorm_sq_le_two_mul_norm_sq :
    ∀ (k : ℕ) (u : Wkp mu Omega p k),
      ∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2 ≤ 2 * ‖u‖ ^ 2
  | 0, u => by
      rw [sum_seminorm_sq_zero]
      nlinarith [sq_nonneg ‖u‖]
  | 1, u => by
      rw [sum_seminorm_sq_succ 0 u, sum_seminorm_sq_zero]
      have hval := norm_lowerOrder_le 0 u
      have hgrad := norm_iteratedGradient_le 0 u
      nlinarith [norm_nonneg (lowerOrder 0 u), norm_nonneg (iteratedGradient 0 u)]
  | k + 2, u => by
      rw [norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k u,
        sum_seminorm_sq_succ (k + 1) u]
      have ih := sum_seminorm_sq_le_two_mul_norm_sq (k + 1) (lowerOrder (k + 1) u)
      nlinarith [sq_nonneg ‖iteratedGradient (k + 1) u‖]

/-- **Upper comparison of the Sobolev norm with the seminorms.** For every order `k` and exponent
`p`, the `W^{k,p}` graph norm is at most `√2` times the Euclidean combination of the seminorms. -/
theorem norm_le_sqrt_two_mul (k : ℕ) (u : Wkp mu Omega p k) :
    ‖u‖ ≤ √2 * √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) := by
  calc
    ‖u‖ = √(‖u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg u)).symm
    _ ≤ √(2 * ∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) :=
      Real.sqrt_le_sqrt (norm_sq_le_two_mul_sum_seminorm_sq k u)
    _ = √2 * √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) :=
      Real.sqrt_mul zero_le_two _

/-- **Lower comparison of the Sobolev norm with the seminorms.** For every order `k` and exponent
`p`, the Euclidean combination of the seminorms is at most `√2` times the `W^{k,p}` graph norm. -/
theorem sqrt_le_sqrt_two_mul_norm (k : ℕ) (u : Wkp mu Omega p k) :
    √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) ≤ √2 * ‖u‖ := by
  calc
    √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) ≤ √(2 * ‖u‖ ^ 2) :=
      Real.sqrt_le_sqrt (sum_seminorm_sq_le_two_mul_norm_sq k u)
    _ = √2 * √(‖u‖ ^ 2) := Real.sqrt_mul zero_le_two _
    _ = √2 * ‖u‖ := by rw [Real.sqrt_sq (norm_nonneg u)]

/-- Convergence in `W^{k,p}(Ω)` is equivalent to convergence to zero in every Sobolev seminorm of
order `j ≤ k`. -/
theorem tendsto_iff_forall_seminorm_sub (k : ℕ) {I : Type*} {l : Filter I}
    {v : I → Wkp mu Omega p k} {u : Wkp mu Omega p k} :
    Filter.Tendsto v l (nhds u) ↔
      ∀ (j : ℕ) (hj : j ≤ k), Filter.Tendsto (fun i => seminorm k j hj (v i - u)) l (nhds 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  constructor
  · intro h j hj
    exact squeeze_zero (fun i => apply_nonneg _ _) (fun i => seminorm_le_norm hj (v i - u)) h
  · intro h
    have hsum : Filter.Tendsto
        (fun i => ∑ j : Fin (k + 1), seminorm k j j.is_le (v i - u) ^ 2) l (nhds 0) := by
      simpa using
        tendsto_finsetSum (Finset.univ : Finset (Fin (k + 1))) fun j _ => (h j j.is_le).pow 2
    have hbound : Filter.Tendsto
        (fun i => √2 * √(∑ j : Fin (k + 1), seminorm k j j.is_le (v i - u) ^ 2)) l (nhds 0) := by
      simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp hsum).const_mul √2
    exact squeeze_zero (fun i => norm_nonneg _) (fun i => norm_le_sqrt_two_mul k (v i - u)) hbound

/-- For a finite exponent `p ≠ ∞`, if `u ∈ W^{k,p}(Ω)` is represented almost everywhere on `Ω` by a
`C^j` function `f` with `j ≤ k`, then the `p`-th power of the order-`j` seminorm equals the integral
over `Ω` of `‖iteratedFDeriv ℝ j f x‖ ^ p.toReal`. -/
theorem seminorm_rpow_eq_integral_norm_iteratedFDeriv_rpow_of_contDiffOn (hp : p ≠ ∞) {j k : ℕ}
    (h : j ≤ k) (u : Wkp mu Omega p k) {f : E → ℝ} (hf : ContDiffOn ℝ j f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    seminorm k j h u ^ p.toReal = ∫ x in Omega, ‖iteratedFDeriv ℝ j f x‖ ^ p.toReal ∂mu := by
  have hmem := memLp_iteratedFDeriv_of_contDiffOn j (toOrderL h u) hf
    (by rwa [value_toOrderL]) j le_rfl
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  rw [seminorm_eq_lpNorm_of_contDiffOn h u hf hu, ← Lp.norm_eq_lpNorm_of_ae_eq hmem.coeFn_toLp,
    ← Lp.integral_norm_rpow_eq_norm_rpow hp0 hp]
  refine integral_congr_ae ?_
  filter_upwards [hmem.coeFn_toLp] with _ hx
  rw [hx]

/-- At exponent `p = 2`, if `u ∈ W^{k,2}(Ω)` is represented almost everywhere on `Ω` by a `C^j`
function `f` with `j ≤ k`, then the squared order-`j` seminorm equals the integral over `Ω` of
`‖iteratedFDeriv ℝ j f x‖ ^ 2`. -/
theorem seminorm_sq_eq_integral_norm_iteratedFDeriv_sq_of_contDiffOn {j k : ℕ} (h : j ≤ k)
    (u : Wkp mu Omega 2 k) {f : E → ℝ} (hf : ContDiffOn ℝ j f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    seminorm k j h u ^ 2 = ∫ x in Omega, ‖iteratedFDeriv ℝ j f x‖ ^ 2 ∂mu := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    seminorm_rpow_eq_integral_norm_iteratedFDeriv_rpow_of_contDiffOn (by norm_num) h u hf hu

/-! ### Concrete checks -/

section Examples

private theorem seminorm_two_Ioo_eq_sqrt_intervalIntegral {a b : ℝ} (hab : a ≤ b) {j k : ℕ}
    (h : j ≤ k) (u : Wkp volume ⟨Set.Ioo a b, isOpen_Ioo⟩ 2 k) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ j f (Set.Ioo a b))
    (hu : (value k u : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioo a b)] f) :
    seminorm k j h u = √(∫ x in a..b, iteratedDeriv j f x ^ 2) := by
  rw [← Real.sqrt_sq (apply_nonneg _ u),
    seminorm_sq_eq_integral_norm_iteratedFDeriv_sq_of_contDiffOn h u hf hu, Opens.coe_mk,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, sq_abs]

private theorem seminorm_exponent_top_eq_of_iteratedDeriv_le {Ω : Opens ℝ} {j k : ℕ} (h : j ≤ k)
    (u : Wkp volume Ω ∞ k) {f : ℝ → ℝ} (hf : ContDiffOn ℝ j f Ω)
    (hu : (value k u : ℝ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝ)] f) {C : ℝ}
    (hbound : ∀ x ∈ Ω, |iteratedDeriv j f x| ≤ C) {x₀ : ℝ} (hx₀ : x₀ ∈ Ω)
    (hattain : C ≤ |iteratedDeriv j f x₀|) :
    seminorm k j h u = C := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hbound x₀ hx₀)
  apply le_antisymm
  · refine seminorm_exponent_top_le_of_contDiffOn h u hf hu hC fun x hx => ?_
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using hbound x hx
  · refine hattain.trans ?_
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
      norm_iteratedFDeriv_le_seminorm_exponent_top_of_contDiffOn h u hf hu hx₀

-- Check 1: On Ω = (0, 1) with p = 2, u(x) = x in W^{1,2}(0, 1) has toOrderL le_rfl u = u,
-- |u|_{0,2} = 1 / √3, |u|_{1,2} = 1, and graph norm ‖u‖ = 2 / √3.
example :
    ∃ u : Wkp volume ⟨Set.Ioo 0 1, isOpen_Ioo⟩ 2 1,
      (value 1 u : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioo 0 1)] (fun x : ℝ => x) ∧
      toOrderL (le_rfl : 1 ≤ 1) u = u ∧
      seminorm 1 0 (Nat.zero_le 1) u = 1 / √3 ∧
      seminorm 1 1 le_rfl u = 1 ∧
      ‖u‖ = 2 / √3 := by
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume)
    (Omega := ⟨Set.Ioo 0 1, isOpen_Ioo⟩) (p := 2) 1 isOpen_univ contDiff_fun_id.contDiffOn
    isCompact_Icc Set.Ioo_subset_Icc_self (Set.subset_univ _)
  have h0 : seminorm 1 0 (Nat.zero_le 1) u = 1 / √3 := by
    rw [seminorm_two_Ioo_eq_sqrt_intervalIntegral zero_le_one (Nat.zero_le 1) u
      contDiff_fun_id.contDiffOn hu]
    simp [integral_pow]
    norm_num
  have h1 : seminorm 1 1 le_rfl u = 1 := by
    rw [seminorm_two_Ioo_eq_sqrt_intervalIntegral zero_le_one le_rfl u
      contDiff_fun_id.contDiffOn hu]
    simp [iteratedDeriv_fun_id]
  have hsqrt4 : √(4 : ℝ) = 2 := by rw [← Real.sqrt_sq zero_le_two]; norm_num
  have hnorm : ‖u‖ = 2 / √3 := by
    have hnsq : ‖u‖ ^ 2 = 4 / 3 := by
      rw [norm_sq_eq_sum_seminorm_sq 1 u, Fin.sum_univ_two]
      simp only [Fin.val_zero, Fin.val_one, h0, h1, div_pow,
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 3)]
      norm_num
    rw [← Real.sqrt_sq (norm_nonneg u), hnsq, Real.sqrt_div (by positivity), hsqrt4]
  exact ⟨u, hu, by simp, h0, h1, hnorm⟩

-- Check 2: On Ω = (0, 1) with p = 2, u(x) = x² in W^{2,2}(0, 1) has
-- |u|_{0,2} = 1 / √5, |u|_{1,2} = 2 / √3, and |u|_{2,2} = 2.
example :
    ∃ u : Wkp volume ⟨Set.Ioo 0 1, isOpen_Ioo⟩ 2 2,
      (value 2 u : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioo 0 1)] (fun x : ℝ => x ^ 2) ∧
      seminorm 2 0 (Nat.zero_le 2) u = 1 / √5 ∧
      seminorm 2 1 (by decide) u = 2 / √3 ∧
      seminorm 2 2 le_rfl u = 2 := by
  have hf : ContDiffOn ℝ 2 (· ^ 2 : ℝ → ℝ) (Set.Ioo 0 1) := (contDiff_fun_id.pow 2).contDiffOn
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume)
    (Omega := ⟨Set.Ioo 0 1, isOpen_Ioo⟩) (p := 2) 2 isOpen_univ (contDiff_fun_id.pow 2).contDiffOn
    isCompact_Icc Set.Ioo_subset_Icc_self (Set.subset_univ _)
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · rw [seminorm_two_Ioo_eq_sqrt_intervalIntegral zero_le_one (Nat.zero_le 2) u
      (hf.of_le (by norm_num)) hu]
    simp [← pow_mul, integral_pow]
    norm_num
  · rw [seminorm_two_Ioo_eq_sqrt_intervalIntegral zero_le_one (by decide) u
      (hf.of_le (by norm_num)) hu]
    simp [mul_pow, integral_pow]
    norm_num
    ring
  · rw [seminorm_two_Ioo_eq_sqrt_intervalIntegral zero_le_one le_rfl u hf hu]
    simp [Nat.descFactorial]

-- Check 3: Sharpness of sqrt_le_sqrt_two_mul_norm at p = ∞, k = 1:
-- on Ω = (0, 2π), u(x) = sin x has ‖u‖ = 1 while √(|u|_{0,∞}² + |u|_{1,∞}²) = √2 = √2 * ‖u‖.
example :
    ∃ u : Wkp volume ⟨Set.Ioo 0 (2 * Real.pi), isOpen_Ioo⟩ ∞ 1,
      (value 1 u : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioo 0 (2 * Real.pi))] Real.sin ∧
      ‖u‖ = 1 ∧
      √(∑ j : Fin 2, seminorm 1 j j.is_le u ^ 2) = √2 := by
  let Ω : Opens ℝ := ⟨Set.Ioo 0 (2 * Real.pi), isOpen_Ioo⟩
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume) (Omega := Ω)
    (p := ∞) 1 isOpen_univ Real.contDiff_sin.contDiffOn isCompact_Icc
    Set.Ioo_subset_Icc_self (Set.subset_univ _)
  have h0 : seminorm 1 0 (Nat.zero_le 1) u = 1 :=
    seminorm_exponent_top_eq_of_iteratedDeriv_le (Nat.zero_le 1) u Real.contDiff_sin.contDiffOn hu
      (fun x _ => by simpa using Real.abs_sin_le_one x)
      (x₀ := Real.pi / 2) ⟨by positivity, by linarith [Real.pi_pos]⟩ (by simp)
  have h1 : seminorm 1 1 le_rfl u = 1 :=
    seminorm_exponent_top_eq_of_iteratedDeriv_le le_rfl u Real.contDiff_sin.contDiffOn hu
      (fun x _ => by simpa [iteratedDeriv_one] using Real.abs_cos_le_one x)
      (x₀ := Real.pi) ⟨Real.pi_pos, by linarith [Real.pi_pos]⟩ (by simp [iteratedDeriv_one])
  let u₁ : W1p volume Ω ∞ := u
  have hgrad : (W1p.gradient u₁ : ℝ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝ)] Real.cos := by
    filter_upwards [W1p.gradient_ae_eq_of_contDiffOn u₁ Real.contDiff_sin.contDiffOn
      (by simpa only [value_one] using hu)] with x hx
    simp [hx, gradient_eq_deriv']
  have hu_norm : ‖u‖ = 1 := by
    apply le_antisymm
    · refine (Submodule.norm_coe u₁).symm.trans_le (Lp.norm_le_of_ae_bound_top zero_le_one ?_)
      filter_upwards [W1p.norm_apply_sq_ae u₁, hu, hgrad] with x hsq hv hg
      have hv' : W1p.value u₁ x = Real.sin x := by simpa only [value_one] using hv
      have h1sq : ‖(u₁ : Sobolev1JetLp volume Ω ∞) x‖ ^ 2 = 1 := by simp [hsq, hv', hg]
      nlinarith [norm_nonneg ((u₁ : Sobolev1JetLp volume Ω ∞) x)]
    · exact h0.symm.le.trans (seminorm_le_norm (Nat.zero_le 1) u)
  refine ⟨u, hu, hu_norm, ?_⟩
  simp [Fin.sum_univ_two, h0, h1]
  norm_num

section

local instance : IsFiniteMeasure
    (volume.restrict ((⟨Set.Ioo (0 : ℝ) 2, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) :=
  Real.isFiniteMeasure_restrict_Ioo 0 2

-- Check 4: Exponent lowering on Ω = (0, 2) from q = 2 to p = 1 for the constant function 1:
-- |1|_{0,2} = √2, |1|_{0,1} = 2, and (volume Ω)^(1/1 - 1/2) * √2 = √2 * √2 = 2.
example :
    ∃ u : Wkp volume ⟨Set.Ioo (0 : ℝ) 2, isOpen_Ioo⟩ 2 1,
      (value 1 u : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 2)] (fun _ : ℝ => (1 : ℝ)) ∧
      seminorm 1 0 (Nat.zero_le 1) u = √2 ∧
      seminorm 1 0 (Nat.zero_le 1) (ofExponentLEL (p := 1) (q := 2) (by norm_num) 1 u) = 2 := by
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume)
    (Omega := ⟨Set.Ioo (0 : ℝ) 2, isOpen_Ioo⟩) (p := 2) 1 isOpen_univ
    (contDiff_const (c := (1 : ℝ))).contDiffOn isCompact_Icc Set.Ioo_subset_Icc_self
    (Set.subset_univ _)
  have h0 : seminorm 1 0 (Nat.zero_le 1) u = √2 := by
    rw [seminorm_two_Ioo_eq_sqrt_intervalIntegral zero_le_two (Nat.zero_le 1) u
      (contDiff_const (c := (1 : ℝ))).contDiffOn hu]
    simp
  let v := ofExponentLEL (p := 1) (q := 2) (by norm_num) 1 u
  have hv : (value 1 v : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 2)] (fun _ : ℝ => (1 : ℝ)) :=
    (value_ofExponentLEL_ae (p := 1) (q := 2) (by norm_num) 1 u).trans hu
  have hv0 : seminorm 1 0 (Nat.zero_le 1) v = 2 := by
    have hpow := seminorm_rpow_eq_integral_norm_iteratedFDeriv_rpow_of_contDiffOn
      ENNReal.one_ne_top (Nat.zero_le 1) v (contDiff_const (c := (1 : ℝ))).contDiffOn hv
    rw [ENNReal.toReal_one, Real.rpow_one, Opens.coe_mk,
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_two] at hpow
    simpa [norm_iteratedFDeriv_zero] using hpow
  exact ⟨u, hu, h0, hv0⟩

end

end Examples

end TauCeti.Wkp
