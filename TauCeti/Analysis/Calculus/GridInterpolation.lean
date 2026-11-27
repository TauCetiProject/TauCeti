/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import TauCeti.Algebra.Order.Floor.Semifield
import TauCeti.Topology.LocallyFinite.Basic
import TauCeti.Topology.Order.Interval.Basic

/-!
# Piecewise gluing and linear/bilinear interpolation on uniform grids

For `τ > 0`, `[0, ∞)` is covered by the uniform grid cells `[n τ, (n + 1) τ)` with `t ≥ 0` in
cell `⌊t / τ⌋₊`. `TauCeti.gridPiecewise τ g` glues `g : ℕ → ℝ → α` via `t ↦ g ⌊t / τ⌋₊ t`; it
is continuous on `[0, ∞)` when adjacent pieces agree at `(n + 1) τ`, and its right-hand derivative
at `t ≥ 0` agrees with `g ⌊t / τ⌋₊`. Using `TauCeti.stepWeight τ n t = ((n + 1) τ - t) / τ`, we
define `TauCeti.stepWeightDiffPrimitive`, `TauCeti.gridLinearInterpolant`, and
`TauCeti.gridBilinearInterpolant`, proving continuity, affine reproduction, monotonicity/bounds,
partial derivatives, and diagonal right-hand derivative.

## Main definitions
* `TauCeti.gridPiecewise`, `TauCeti.stepWeight`, `TauCeti.stepWeightDiffPrimitive`,
  `TauCeti.gridLinearInterpolant`, `TauCeti.gridBilinearInterpolant`.

## Main results
* `TauCeti.continuousOn_gridPiecewise`, `TauCeti.hasDerivWithinAt_gridPiecewise_iff`.
* `TauCeti.continuousOn_stepWeightDiffPrimitive`,
  `TauCeti.hasDerivWithinAt_stepWeightDiffPrimitive`, `TauCeti.stepWeightDiffPrimitive_le`.
* `TauCeti.continuousOn_gridLinearInterpolant`, `TauCeti.hasDerivWithinAt_gridLinearInterpolant`,
  `TauCeti.gridLinearInterpolant_natCast_smul`,
  `TauCeti.gridLinearInterpolant_le_gridLinearInterpolant`.
* `TauCeti.continuousOn_gridBilinearInterpolant`,
  `TauCeti.hasDerivWithinAt_gridBilinearInterpolant_diag`,
  `TauCeti.gridBilinearInterpolant_le_gridBilinearInterpolant`,
  `TauCeti.le_gridBilinearInterpolant`, `TauCeti.gridBilinearInterpolant_le`.
-/

public section

noncomputable section

open Set Topology

namespace TauCeti

/-! ### Uniform-grid gluing -/

section GridPiecewise

/-- Glues a family `g n` along the uniform grid `[n τ, (n + 1) τ)` via `⌊t / τ⌋₊`. -/
def gridPiecewise {α : Type*} (τ : ℝ) (g : ℕ → ℝ → α) (t : ℝ) : α := g ⌊t / τ⌋₊ t

/-- Unconditional defining equation of `gridPiecewise`. -/
theorem gridPiecewise_def {α : Type*} (τ : ℝ) (g : ℕ → ℝ → α) (t : ℝ) :
    gridPiecewise τ g t = g ⌊t / τ⌋₊ t := (rfl)

/-- At `0`, `gridPiecewise τ g` evaluates the `0`-th piece at `0`. -/
@[simp] theorem gridPiecewise_apply_zero {α : Type*} (τ : ℝ) (g : ℕ → ℝ → α) :
    gridPiecewise τ g 0 = g 0 0 := by simp [gridPiecewise_def]

/-- At the grid point `n * τ` (with `τ ≠ 0`), `gridPiecewise τ g` evaluates `g n` at `n * τ`. -/
@[simp] theorem gridPiecewise_natCast_mul {α : Type*} {τ : ℝ} (hτ : τ ≠ 0) (g : ℕ → ℝ → α)
    (n : ℕ) : gridPiecewise τ g ((n : ℝ) * τ) = g n ((n : ℝ) * τ) := by
  simp [gridPiecewise_def, mul_div_cancel_right₀ _ hτ]

/-- Gluing a constant family `fun _ ↦ f` returns `f`. -/
@[simp] theorem gridPiecewise_const {α : Type*} (τ : ℝ) (f : ℝ → α) (t : ℝ) :
    gridPiecewise τ (fun _ ↦ f) t = f t := (rfl)

/-- On the half-open cell `[n τ, (n + 1) τ)`, `gridPiecewise τ g` agrees with `g n`. -/
theorem gridPiecewise_eq_of_mem_Ico {α : Type*} {τ : ℝ} (hτ : 0 < τ) (g : ℕ → ℝ → α) (n : ℕ)
    {t : ℝ} (ht : t ∈ Ico ((n : ℝ) * τ) (((n : ℝ) + 1) * τ)) :
    gridPiecewise τ g t = g n t := by
  have ht0 : 0 ≤ t / τ := div_nonneg ((mul_nonneg n.cast_nonneg hτ.le).trans ht.1) hτ.le
  have hfl : ⌊t / τ⌋₊ = n :=
    (Nat.floor_eq_iff ht0).2 ⟨(le_div_iff₀ hτ).2 ht.1, (div_lt_iff₀ hτ).2 ht.2⟩
  simp [gridPiecewise_def, hfl]

/-- When `g n` and `g (n + 1)` agree at `(n + 1) τ`, `gridPiecewise τ g` agrees with `g n` on
`[n τ, (n + 1) τ]`. -/
theorem gridPiecewise_eq_of_mem_Icc {α : Type*} {τ : ℝ} (hτ : 0 < τ) {g : ℕ → ℝ → α} {n : ℕ}
    (hjoin : g n (((n : ℝ) + 1) * τ) = g (n + 1) (((n : ℝ) + 1) * τ))
    {t : ℝ} (ht : t ∈ Icc ((n : ℝ) * τ) (((n : ℝ) + 1) * τ)) :
    gridPiecewise τ g t = g n t := by
  rcases ht.2.eq_or_lt with rfl | hlt
  · have heq := gridPiecewise_natCast_mul hτ.ne' g (n + 1); push_cast at heq; rw [heq, hjoin]
  · exact gridPiecewise_eq_of_mem_Ico hτ g n ⟨ht.1, hlt⟩

/-- On a right neighborhood of `t ≥ 0`, `gridPiecewise τ g` coincides with `g ⌊t / τ⌋₊`. -/
theorem gridPiecewise_eventuallyEq_nhdsWithin_Ici {α : Type*} {τ : ℝ} (hτ : 0 < τ)
    (g : ℕ → ℝ → α) {t : ℝ} (ht : 0 ≤ t) : gridPiecewise τ g =ᶠ[𝓝[Ici t] t] g ⌊t / τ⌋₊ := by
  have hmem := mem_Ico_floor_div_mul hτ ht
  filter_upwards [mem_nhdsWithin.2 ⟨Iio (((⌊t / τ⌋₊ : ℝ) + 1) * τ), isOpen_Iio, hmem.2,
    Subset.rfl⟩] with s hs
  exact gridPiecewise_eq_of_mem_Ico hτ g ⌊t / τ⌋₊ ⟨hmem.1.trans hs.2, hs.1⟩

/-- A `gridPiecewise` function whose pieces are continuous on `[n τ, (n + 1) τ]` and match at the
grid points is continuous on `[0, ∞)`. -/
theorem continuousOn_gridPiecewise {α : Type*} [TopologicalSpace α] {τ : ℝ} (hτ : 0 < τ)
    {g : ℕ → ℝ → α}
    (hjoin : ∀ n : ℕ, g n (((n : ℝ) + 1) * τ) = g (n + 1) (((n : ℝ) + 1) * τ))
    (hcont : ∀ n : ℕ, ContinuousOn (g n) (Icc ((n : ℝ) * τ) (((n : ℝ) + 1) * τ))) :
    ContinuousOn (gridPiecewise τ g) (Ici 0) := by
  rw [← iUnion_Icc_natCast_mul hτ]
  exact (locallyFinite_Icc_natCast_mul hτ).continuousOn_iUnion (fun _ ↦ isClosed_Icc) fun n ↦
    (hcont n).congr fun _ hs ↦ gridPiecewise_eq_of_mem_Icc hτ (hjoin n) hs

/-- Right-hand derivative of `gridPiecewise τ g` at `t ≥ 0` agrees with `g ⌊t / τ⌋₊` without any
matching condition at grid points. -/
theorem hasDerivWithinAt_gridPiecewise_iff {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousSMul ℝ E] {τ : ℝ} (hτ : 0 < τ) {g : ℕ → ℝ → E}
    {t : ℝ} (ht : 0 ≤ t) {f' : E} :
    HasDerivWithinAt (gridPiecewise τ g) f' (Ici t) t ↔
      HasDerivWithinAt (g ⌊t / τ⌋₊) f' (Ici t) t :=
  (gridPiecewise_eventuallyEq_nhdsWithin_Ici hτ g ht).hasFDerivWithinAt_iff
    (gridPiecewise_def τ g t)

end GridPiecewise

/-! ### Barycentric weight on a grid cell -/

section StepWeight

/-- Barycentric weight `((n + 1) τ - t) / τ` of the left endpoint on `[n τ, (n + 1) τ]`. -/
def stepWeight (τ : ℝ) (n : ℕ) (t : ℝ) : ℝ := (((n : ℝ) + 1) * τ - t) / τ

/-- Unconditional defining equation of `stepWeight`. -/
theorem stepWeight_def (τ : ℝ) (n : ℕ) (t : ℝ) :
    stepWeight τ n t = (((n : ℝ) + 1) * τ - t) / τ := (rfl)

/-- At the left endpoint `n * τ` (with `τ ≠ 0`), `stepWeight τ n` equals `1`. -/
@[simp] theorem stepWeight_natCast_mul {τ : ℝ} (hτ : τ ≠ 0) (n : ℕ) :
    stepWeight τ n ((n : ℝ) * τ) = 1 := by simp only [stepWeight_def]; field_simp; ring

/-- At the right endpoint `(n + 1) * τ`, `stepWeight τ n` vanishes. -/
@[simp] theorem stepWeight_natCast_add_one_mul_eq_zero (τ : ℝ) (n : ℕ) :
    stepWeight τ n (((n : ℝ) + 1) * τ) = 0 := by simp [stepWeight_def]

/-- At `(n + 1) * τ` (with `τ ≠ 0`), `stepWeight τ (n + 1)` equals `1`. -/
@[simp] theorem stepWeight_succ_natCast_add_one_mul {τ : ℝ} (hτ : τ ≠ 0) (n : ℕ) :
    stepWeight τ (n + 1) (((n : ℝ) + 1) * τ) = 1 := by
  simpa [Nat.cast_add, Nat.cast_one] using stepWeight_natCast_mul hτ (n + 1)

/-- At `0` (with `τ ≠ 0`), `stepWeight τ 0` equals `1`. -/
@[simp] theorem stepWeight_apply_zero {τ : ℝ} (hτ : τ ≠ 0) : stepWeight τ 0 0 = 1 := by
  simpa using stepWeight_natCast_mul hτ 0

/-- Barycentric coordinate identity: `stepWeight τ n t` and `1 - stepWeight τ n t` express `t` as
an affine combination of `n * τ` and `(n + 1) * τ`. -/
theorem stepWeight_mul_add_one_sub_mul {τ : ℝ} (hτ : τ ≠ 0) (n : ℕ) (t : ℝ) :
    stepWeight τ n t * ((n : ℝ) * τ) + (1 - stepWeight τ n t) * (((n : ℝ) + 1) * τ) = t := by
  simp only [stepWeight_def]; field_simp; ring

/-- On `[n τ, (n + 1) τ]` with `τ > 0`, `stepWeight τ n t` lies in `[0, 1]`. -/
theorem stepWeight_mem_Icc_of_mem_Icc {τ t : ℝ} (hτ : 0 < τ) {n : ℕ}
    (ht : t ∈ Icc ((n : ℝ) * τ) (((n : ℝ) + 1) * τ)) : stepWeight τ n t ∈ Icc (0 : ℝ) 1 :=
  ⟨div_nonneg (sub_nonneg.2 ht.2) hτ.le, (div_le_one hτ).2 (by linarith [ht.1])⟩

/-- For `τ > 0` and `t ≥ 0`, the active cell weight `stepWeight τ ⌊t / τ⌋₊ t` lies in `[0, 1]`. -/
theorem stepWeight_floor_mem_Icc {τ t : ℝ} (hτ : 0 < τ) (ht : 0 ≤ t) :
    stepWeight τ ⌊t / τ⌋₊ t ∈ Icc (0 : ℝ) 1 :=
  stepWeight_mem_Icc_of_mem_Icc hτ (Ico_subset_Icc_self (mem_Ico_floor_div_mul hτ ht))

/-- `stepWeight τ n` is continuous on `ℝ`. -/
@[fun_prop] theorem continuous_stepWeight (τ : ℝ) (n : ℕ) : Continuous (stepWeight τ n) := by
  unfold stepWeight; fun_prop

/-- The derivative of `stepWeight τ n` at every `t : ℝ` is `-τ⁻¹`. -/
theorem hasDerivAt_stepWeight (τ : ℝ) (n : ℕ) (t : ℝ) : HasDerivAt (stepWeight τ n) (-τ⁻¹) t :=
  (((hasDerivAt_id t).const_sub (((n : ℝ) + 1) * τ)).div_const τ).congr_deriv
    (by simp [neg_div, one_div])

end StepWeight

/-! ### Piecewise quadratic primitive of weighted forward differences -/

section StepWeightDiffPrimitive

/-- Piecewise quadratic primitive of
`t ↦ stepWeight τ ⌊t / τ⌋₊ t • (c ⌊t / τ⌋₊ - c (⌊t / τ⌋₊ + 1))` starting at `0`. -/
def stepWeightDiffPrimitive {E : Type*} [AddCommGroup E] [Module ℝ E]
    (τ : ℝ) (c : ℕ → E) : ℝ → E :=
  gridPiecewise τ fun n t ↦
    (τ / 2) • (c 0 - c (n + 1) + stepWeight τ n t ^ 2 • (c (n + 1) - c n))

/-- Unconditional defining equation of `stepWeightDiffPrimitive`. -/
theorem stepWeightDiffPrimitive_def {E : Type*} [AddCommGroup E] [Module ℝ E]
    (τ : ℝ) (c : ℕ → E) (t : ℝ) :
    stepWeightDiffPrimitive τ c t = (τ / 2) • (c 0 - c (⌊t / τ⌋₊ + 1) +
      stepWeight τ ⌊t / τ⌋₊ t ^ 2 • (c (⌊t / τ⌋₊ + 1) - c ⌊t / τ⌋₊)) := (rfl)

/-- At `0` (with `τ ≠ 0`), `stepWeightDiffPrimitive τ c` vanishes. -/
@[simp] theorem stepWeightDiffPrimitive_apply_zero {E : Type*} [AddCommGroup E] [Module ℝ E]
    {τ : ℝ} (hτ : τ ≠ 0) (c : ℕ → E) : stepWeightDiffPrimitive τ c 0 = 0 := by
  simp [stepWeightDiffPrimitive_def, hτ]

/-- At `n * τ` (with `τ ≠ 0`), `stepWeightDiffPrimitive τ c` equals `(τ / 2) • (c 0 - c n)`. -/
@[simp] theorem stepWeightDiffPrimitive_natCast_mul {E : Type*} [AddCommGroup E] [Module ℝ E]
    {τ : ℝ} (hτ : τ ≠ 0) (c : ℕ → E) (n : ℕ) :
    stepWeightDiffPrimitive τ c ((n : ℝ) * τ) = (τ / 2) • (c 0 - c n) := by
  simp only [stepWeightDiffPrimitive, gridPiecewise_natCast_mul hτ, stepWeight_natCast_mul hτ,
    one_pow, one_smul]; module

/-- For antitone `c` and `τ ≥ 0`, `stepWeightDiffPrimitive τ c t` is bounded by
`(τ / 2) • (c 0 - c (⌊t / τ⌋₊ + 1))`. -/
theorem stepWeightDiffPrimitive_le {E : Type*} [AddCommGroup E] [PartialOrder E]
    [IsOrderedAddMonoid E] [Module ℝ E] [PosSMulMono ℝ E]
    {τ t : ℝ} (hτ : 0 ≤ τ) {c : ℕ → E} (hc : Antitone c) :
    stepWeightDiffPrimitive τ c t ≤ (τ / 2) • (c 0 - c (⌊t / τ⌋₊ + 1)) := by
  rw [stepWeightDiffPrimitive_def]
  exact smul_le_smul_of_nonneg_left (add_le_of_nonpos_right
    (smul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (sub_nonpos.2 (hc (Nat.le_succ _)))))
    (by positivity)

/-- For `τ > 0`, `stepWeightDiffPrimitive τ c` is continuous on `[0, ∞)`. -/
theorem continuousOn_stepWeightDiffPrimitive {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {τ : ℝ} (hτ : 0 < τ) (c : ℕ → E) : ContinuousOn (stepWeightDiffPrimitive τ c) (Ici 0) :=
  continuousOn_gridPiecewise hτ (fun _ ↦ by simp [hτ.ne']) fun _ ↦ by fun_prop

/-- For `τ > 0` and `t ≥ 0`, `stepWeightDiffPrimitive τ c` has right-hand derivative
`stepWeight τ ⌊t / τ⌋₊ t • (c ⌊t / τ⌋₊ - c (⌊t / τ⌋₊ + 1))` at `t`. -/
theorem hasDerivWithinAt_stepWeightDiffPrimitive {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {τ : ℝ} (hτ : 0 < τ) (c : ℕ → E) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (stepWeightDiffPrimitive τ c)
      (stepWeight τ ⌊t / τ⌋₊ t • (c ⌊t / τ⌋₊ - c (⌊t / τ⌋₊ + 1))) (Ici t) t := by
  unfold stepWeightDiffPrimitive; rw [hasDerivWithinAt_gridPiecewise_iff hτ ht]
  have hd := (((((hasDerivAt_stepWeight τ ⌊t / τ⌋₊ t).pow 2).smul_const
    (c (⌊t / τ⌋₊ + 1) - c ⌊t / τ⌋₊)).const_add (c 0 - c (⌊t / τ⌋₊ + 1))).const_smul (τ / 2))
  refine (hd.congr_deriv ?_).hasDerivWithinAt; have : τ ≠ 0 := hτ.ne'
  rw [← neg_sub (c ⌊t / τ⌋₊), smul_neg, ← neg_smul, smul_smul]; congr 1
  simp only [Nat.add_one_sub_one, pow_one, Nat.cast_ofNat]; field_simp

end StepWeightDiffPrimitive

/-! ### Piecewise linear interpolation on a uniform grid -/

section GridLinearInterpolant

section Module

variable {E : Type*} [AddCommMonoid E] [Module ℝ E]

/-- Piecewise linear interpolant of `c : ℕ → E` on `n * τ`, affine on `[n τ, (n + 1) τ]`. -/
def gridLinearInterpolant (τ : ℝ) (c : ℕ → E) : ℝ → E :=
  gridPiecewise τ fun n t ↦ stepWeight τ n t • c n + (1 - stepWeight τ n t) • c (n + 1)

/-- Unconditional defining equation of `gridLinearInterpolant`. -/
theorem gridLinearInterpolant_def (τ : ℝ) (c : ℕ → E) (t : ℝ) :
    gridLinearInterpolant τ c t = stepWeight τ ⌊t / τ⌋₊ t • c ⌊t / τ⌋₊ +
      (1 - stepWeight τ ⌊t / τ⌋₊ t) • c (⌊t / τ⌋₊ + 1) := (rfl)

/-- Unconditional defining equation of the unit-step linear interpolant
`gridLinearInterpolant 1`. -/
theorem gridLinearInterpolant_one_def (c : ℕ → E) (t : ℝ) :
    gridLinearInterpolant 1 c t =
      (⌊t⌋₊ + 1 - t) • c ⌊t⌋₊ + (t - ⌊t⌋₊) • c (⌊t⌋₊ + 1) := by
  simp only [gridLinearInterpolant_def, stepWeight_def, div_one, mul_one]
  congr 2; ring

/-- At the grid point `n * τ` (with `τ ≠ 0`), `gridLinearInterpolant τ c` takes the value `c n`. -/
@[simp] theorem gridLinearInterpolant_natCast_mul {τ : ℝ} (hτ : τ ≠ 0) (c : ℕ → E) (n : ℕ) :
    gridLinearInterpolant τ c ((n : ℝ) * τ) = c n := by
  simp [gridLinearInterpolant, gridPiecewise_natCast_mul hτ, stepWeight_natCast_mul hτ]

/-- At a natural number `n`, the unit-step linear interpolant `gridLinearInterpolant 1 c` takes
the value `c n`. -/
@[simp] theorem gridLinearInterpolant_one_natCast (c : ℕ → E) (n : ℕ) :
    gridLinearInterpolant 1 c n = c n := by
  simpa only [mul_one] using gridLinearInterpolant_natCast_mul one_ne_zero c n

/-- At `0` (with `τ ≠ 0`), `gridLinearInterpolant τ c` takes the value `c 0`. -/
@[simp] theorem gridLinearInterpolant_apply_zero {τ : ℝ} (hτ : τ ≠ 0) (c : ℕ → E) :
    gridLinearInterpolant τ c 0 = c 0 := by simpa using gridLinearInterpolant_natCast_mul hτ c 0

/-- The piecewise linear interpolant of the zero sequence is `0`. -/
@[simp] theorem gridLinearInterpolant_zero (τ t : ℝ) :
    gridLinearInterpolant τ (0 : ℕ → E) t = 0 := by simp [gridLinearInterpolant_def]

/-- The piecewise linear interpolant of a constant sequence is constant. -/
@[simp] theorem gridLinearInterpolant_const (τ : ℝ) (x : E) (t : ℝ) :
    gridLinearInterpolant τ (fun _ ↦ x) t = x := by
  rw [gridLinearInterpolant_def, ← add_smul, add_sub_cancel, one_smul]

/-- `gridLinearInterpolant τ` is additive in the interpolated sequence. -/
@[simp] theorem gridLinearInterpolant_add (τ : ℝ) (c d : ℕ → E) (t : ℝ) :
    gridLinearInterpolant τ (c + d) t =
      gridLinearInterpolant τ c t + gridLinearInterpolant τ d t := by
  simp only [gridLinearInterpolant_def, Pi.add_apply, smul_add]; exact add_add_add_comm _ _ _ _

/-- `gridLinearInterpolant τ` commutes with scalar multiplication commuting with `ℝ`. -/
@[simp] theorem gridLinearInterpolant_smul {R : Type*} [DistribSMul R E] [SMulCommClass ℝ R E]
    (τ : ℝ) (r : R) (c : ℕ → E) (t : ℝ) :
    gridLinearInterpolant τ (r • c) t = r • gridLinearInterpolant τ c t := by
  simp only [gridLinearInterpolant_def, Pi.smul_apply, smul_comm _ r, smul_add]

/-- On `[n τ, (n + 1) τ]` with `τ > 0`, `gridLinearInterpolant τ c` is the affine combination of
`c n` and `c (n + 1)` with weight `stepWeight τ n t`. -/
theorem gridLinearInterpolant_eq_of_mem_Icc {τ : ℝ} (hτ : 0 < τ) (c : ℕ → E) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc ((n : ℝ) * τ) (((n : ℝ) + 1) * τ)) :
    gridLinearInterpolant τ c t = stepWeight τ n t • c n + (1 - stepWeight τ n t) • c (n + 1) :=
  gridPiecewise_eq_of_mem_Icc hτ (by simp [hτ.ne']) ht

/-- `gridLinearInterpolant τ` reproduces `n ↦ c₀ + (n : ℝ) • v` as `t ↦ c₀ + (t / τ) • v`. -/
theorem gridLinearInterpolant_natCast_smul {τ : ℝ} (hτ : τ ≠ 0) (c₀ v : E) (t : ℝ) :
    gridLinearInterpolant τ (fun n ↦ c₀ + (n : ℝ) • v) t = c₀ + (t / τ) • v := by
  simp only [gridLinearInterpolant_def, smul_add, smul_smul]
  rw [add_add_add_comm, ← add_smul, add_sub_cancel, one_smul, ← add_smul]
  congr 2; apply mul_right_cancel₀ hτ
  have h := stepWeight_mul_add_one_sub_mul hτ ⌊t / τ⌋₊ t; push_cast at h ⊢
  linarith [div_mul_cancel₀ t hτ]

/-- `gridLinearInterpolant τ` reproduces `n ↦ c + m * n` as `t ↦ c + m * (t / τ)`. -/
@[simp] theorem gridLinearInterpolant_affine {τ : ℝ} (hτ : τ ≠ 0) (c m t : ℝ) :
    gridLinearInterpolant τ (fun n ↦ c + m * (n : ℝ)) t = c + m * (t / τ) := by
  simpa only [smul_eq_mul, mul_comm m] using gridLinearInterpolant_natCast_smul hτ c m t

/-- For `τ > 0`, `gridLinearInterpolant τ c` is continuous on `[0, ∞)`. -/
theorem continuousOn_gridLinearInterpolant [TopologicalSpace E] [ContinuousAdd E]
    [ContinuousSMul ℝ E] {τ : ℝ} (hτ : 0 < τ) (c : ℕ → E) :
    ContinuousOn (gridLinearInterpolant τ c) (Ici 0) :=
  continuousOn_gridPiecewise hτ (fun _ ↦ by simp [hτ.ne']) fun _ ↦ by fun_prop

end Module

section Order

variable {E : Type*} [AddCommMonoid E] [PartialOrder E] [IsOrderedAddMonoid E]
  [Module ℝ E] [PosSMulMono ℝ E]

/-- At `t ≥ 0`, `gridLinearInterpolant τ` is monotone in `c ⌊t / τ⌋₊` and `c ⌈t / τ⌉₊`. -/
theorem gridLinearInterpolant_le_gridLinearInterpolant {τ : ℝ} (hτ : 0 < τ) {f g : ℕ → E}
    {t : ℝ} (ht : 0 ≤ t) (hfloor : f ⌊t / τ⌋₊ ≤ g ⌊t / τ⌋₊) (hceil : f ⌈t / τ⌉₊ ≤ g ⌈t / τ⌉₊) :
    gridLinearInterpolant τ f t ≤ gridLinearInterpolant τ g t := by
  rcases (Nat.floor_le_ceil (t / τ)).lt_or_eq with hlt | heq
  · rw [le_antisymm (Nat.ceil_le_floor_add_one _) hlt] at hceil
    obtain ⟨hw0, hw1⟩ := stepWeight_floor_mem_Icc hτ ht
    simp only [gridLinearInterpolant_def]
    exact add_le_add (smul_le_smul_of_nonneg_left hfloor hw0)
      (smul_le_smul_of_nonneg_left hceil (sub_nonneg.2 hw1))
  · have ht_eq : t = (⌊t / τ⌋₊ : ℝ) * τ := (div_eq_iff hτ.ne').1 <|
      le_antisymm (heq ▸ Nat.le_ceil _) (Nat.floor_le (div_nonneg ht hτ.le))
    rw [ht_eq, gridLinearInterpolant_natCast_mul hτ.ne', gridLinearInterpolant_natCast_mul hτ.ne']
    exact hfloor

/-- At `t ≥ 0`, `gridLinearInterpolant τ` is monotone in the interpolated sequence. -/
theorem gridLinearInterpolant_mono {τ : ℝ} (hτ : 0 < τ) {f g : ℕ → E} (hfg : f ≤ g)
    {t : ℝ} (ht : 0 ≤ t) : gridLinearInterpolant τ f t ≤ gridLinearInterpolant τ g t :=
  gridLinearInterpolant_le_gridLinearInterpolant hτ ht (hfg _) (hfg _)

/-- If `m` lies below `c ⌊t / τ⌋₊` and `c ⌈t / τ⌉₊`, then `m ≤ gridLinearInterpolant τ c t`. -/
theorem le_gridLinearInterpolant {τ : ℝ} (hτ : 0 < τ) {c : ℕ → E} {t : ℝ} (ht : 0 ≤ t) {m : E}
    (hfloor : m ≤ c ⌊t / τ⌋₊) (hceil : m ≤ c ⌈t / τ⌉₊) : m ≤ gridLinearInterpolant τ c t := by
  simpa using gridLinearInterpolant_le_gridLinearInterpolant hτ ht (f := fun _ ↦ m) hfloor hceil

/-- If `c ⌊t / τ⌋₊ ≤ M` and `c ⌈t / τ⌉₊ ≤ M`, then `gridLinearInterpolant τ c t ≤ M`. -/
theorem gridLinearInterpolant_le {τ : ℝ} (hτ : 0 < τ) {c : ℕ → E} {t : ℝ} (ht : 0 ≤ t) {M : E}
    (hfloor : c ⌊t / τ⌋₊ ≤ M) (hceil : c ⌈t / τ⌉₊ ≤ M) : gridLinearInterpolant τ c t ≤ M := by
  simpa using gridLinearInterpolant_le_gridLinearInterpolant hτ ht (g := fun _ ↦ M) hfloor hceil

end Order

section Mul

variable {A : Type*} [NonUnitalNonAssocSemiring A] [Module ℝ A]

/-- `gridLinearInterpolant τ` commutes with left multiplication by a constant. -/
@[simp] theorem gridLinearInterpolant_const_mul [SMulCommClass ℝ A A] (τ : ℝ) (r : A) (c : ℕ → A)
    (t : ℝ) : gridLinearInterpolant τ (fun n ↦ r * c n) t = r * gridLinearInterpolant τ c t := by
  simpa only [Pi.smul_def, smul_eq_mul] using gridLinearInterpolant_smul τ r c t

/-- `gridLinearInterpolant τ` commutes with right multiplication by a constant. -/
@[simp] theorem gridLinearInterpolant_mul_const [IsScalarTower ℝ A A] (τ : ℝ) (c : ℕ → A) (r : A)
    (t : ℝ) : gridLinearInterpolant τ (fun n ↦ c n * r) t = gridLinearInterpolant τ c t * r := by
  simp only [gridLinearInterpolant_def, add_mul, smul_mul_assoc]

end Mul

section Group

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- `gridLinearInterpolant τ` commutes with negation of the interpolated sequence. -/
@[simp] theorem gridLinearInterpolant_neg (τ : ℝ) (c : ℕ → E) (t : ℝ) :
    gridLinearInterpolant τ (-c) t = -gridLinearInterpolant τ c t := by
  simpa only [neg_one_smul] using gridLinearInterpolant_smul τ (-1 : ℝ) c t

/-- `gridLinearInterpolant τ` preserves subtraction of interpolated sequences. -/
@[simp] theorem gridLinearInterpolant_sub (τ : ℝ) (c d : ℕ → E) (t : ℝ) :
    gridLinearInterpolant τ (c - d) t =
      gridLinearInterpolant τ c t - gridLinearInterpolant τ d t := by
  simp only [sub_eq_add_neg, gridLinearInterpolant_add, gridLinearInterpolant_neg]

end Group

/-- For `τ > 0` and `t ≥ 0`, `gridLinearInterpolant τ c` has right-hand derivative
`τ⁻¹ • (c (⌊t / τ⌋₊ + 1) - c ⌊t / τ⌋₊)` at `t`. -/
theorem hasDerivWithinAt_gridLinearInterpolant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {τ : ℝ} (hτ : 0 < τ) (c : ℕ → E) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (gridLinearInterpolant τ c)
      (τ⁻¹ • (c (⌊t / τ⌋₊ + 1) - c ⌊t / τ⌋₊)) (Ici t) t := by
  unfold gridLinearInterpolant; rw [hasDerivWithinAt_gridPiecewise_iff hτ ht]
  have hd := ((hasDerivAt_stepWeight τ ⌊t / τ⌋₊ t).smul_const (c ⌊t / τ⌋₊)).add
    (((hasDerivAt_stepWeight τ ⌊t / τ⌋₊ t).const_sub 1).smul_const (c (⌊t / τ⌋₊ + 1)))
  exact (hd.congr_deriv (by simp only [neg_neg]; module)).hasDerivWithinAt

end GridLinearInterpolant

/-! ### Piecewise bilinear interpolation on a uniform product grid -/

section GridBilinearInterpolant

section Module

variable {E : Type*} [AddCommMonoid E] [Module ℝ E]

/-- Piecewise bilinear interpolant of `a : ℕ → ℕ → E` on `(n * τ, k * η)`. -/
def gridBilinearInterpolant (τ η : ℝ) (a : ℕ → ℕ → E) (s t : ℝ) : E :=
  gridLinearInterpolant η (fun k ↦ gridLinearInterpolant τ (a · k) s) t

/-- Unconditional defining equation of `gridBilinearInterpolant`. -/
theorem gridBilinearInterpolant_def (τ η : ℝ) (a : ℕ → ℕ → E) (s t : ℝ) :
    gridBilinearInterpolant τ η a s t =
      gridLinearInterpolant η (fun k ↦ gridLinearInterpolant τ (a · k) s) t := (rfl)

/-- Four-corner expansion of `gridBilinearInterpolant τ η a s t`. -/
theorem gridBilinearInterpolant_apply (τ η : ℝ) (a : ℕ → ℕ → E) (s t : ℝ) :
    gridBilinearInterpolant τ η a s t =
      stepWeight η ⌊t / η⌋₊ t • (stepWeight τ ⌊s / τ⌋₊ s • a ⌊s / τ⌋₊ ⌊t / η⌋₊ +
          (1 - stepWeight τ ⌊s / τ⌋₊ s) • a (⌊s / τ⌋₊ + 1) ⌊t / η⌋₊) +
      (1 - stepWeight η ⌊t / η⌋₊ t) • (stepWeight τ ⌊s / τ⌋₊ s • a ⌊s / τ⌋₊ (⌊t / η⌋₊ + 1) +
          (1 - stepWeight τ ⌊s / τ⌋₊ s) • a (⌊s / τ⌋₊ + 1) (⌊t / η⌋₊ + 1)) := (rfl)

/-- On `s = n * τ` (`τ ≠ 0`), `gridBilinearInterpolant τ η a` is `gridLinearInterpolant η (a n)`. -/
@[simp] theorem gridBilinearInterpolant_natCast_mul_left {τ : ℝ} (hτ : τ ≠ 0) (η : ℝ)
    (a : ℕ → ℕ → E) (n : ℕ) (t : ℝ) :
    gridBilinearInterpolant τ η a ((n : ℝ) * τ) t = gridLinearInterpolant η (a n) t := by
  simp [gridBilinearInterpolant_def, hτ]

/-- On `t = k * η` (`η ≠ 0`), `gridBilinearInterpolant τ η a` is
`gridLinearInterpolant τ (a · k)`. -/
@[simp] theorem gridBilinearInterpolant_natCast_mul_right (τ : ℝ) {η : ℝ} (hη : η ≠ 0)
    (a : ℕ → ℕ → E) (s : ℝ) (k : ℕ) :
    gridBilinearInterpolant τ η a s ((k : ℝ) * η) = gridLinearInterpolant τ (a · k) s := by
  simp [gridBilinearInterpolant_def, hη]

/-- At `(n * τ, k * η)` (`τ ≠ 0`, `η ≠ 0`), `gridBilinearInterpolant τ η a` recovers `a n k`. -/
theorem gridBilinearInterpolant_natCast_mul {τ η : ℝ} (hτ : τ ≠ 0) (hη : η ≠ 0)
    (a : ℕ → ℕ → E) (n k : ℕ) :
    gridBilinearInterpolant τ η a ((n : ℝ) * τ) ((k : ℝ) * η) = a n k := by simp [hτ, hη]

/-- On `s = 0` (`τ ≠ 0`), `gridBilinearInterpolant τ η a` is `gridLinearInterpolant η (a 0)`. -/
@[simp] theorem gridBilinearInterpolant_apply_zero_left {τ : ℝ} (hτ : τ ≠ 0) (η : ℝ)
    (a : ℕ → ℕ → E) (t : ℝ) :
    gridBilinearInterpolant τ η a 0 t = gridLinearInterpolant η (a 0) t := by
  simp [gridBilinearInterpolant_def, hτ]

/-- On `t = 0` (`η ≠ 0`), `gridBilinearInterpolant τ η a` is `gridLinearInterpolant τ (a · 0)`. -/
@[simp] theorem gridBilinearInterpolant_apply_zero_right (τ : ℝ) {η : ℝ} (hη : η ≠ 0)
    (a : ℕ → ℕ → E) (s : ℝ) :
    gridBilinearInterpolant τ η a s 0 = gridLinearInterpolant τ (a · 0) s := by
  simp [gridBilinearInterpolant_def, hη]

/-- At `(0, 0)` (`τ ≠ 0`, `η ≠ 0`), `gridBilinearInterpolant τ η a` recovers `a 0 0`. -/
theorem gridBilinearInterpolant_apply_zero {τ η : ℝ} (hτ : τ ≠ 0) (hη : η ≠ 0)
    (a : ℕ → ℕ → E) : gridBilinearInterpolant τ η a 0 0 = a 0 0 := by simp [hτ, hη]

/-- The piecewise bilinear interpolant of the zero family is `0`. -/
@[simp] theorem gridBilinearInterpolant_zero (τ η s t : ℝ) :
    gridBilinearInterpolant τ η (0 : ℕ → ℕ → E) s t = 0 := by simp [gridBilinearInterpolant_def]

/-- The piecewise bilinear interpolant of a constant family is constant. -/
@[simp] theorem gridBilinearInterpolant_const (τ η : ℝ) (x : E) (s t : ℝ) :
    gridBilinearInterpolant τ η (fun _ _ ↦ x) s t = x := by simp [gridBilinearInterpolant_def]

/-- If `a` ignores its first index, `gridBilinearInterpolant` is `gridLinearInterpolant`. -/
@[simp] theorem gridBilinearInterpolant_const_left (τ η : ℝ) (c : ℕ → E) (s t : ℝ) :
    gridBilinearInterpolant τ η (fun _ k ↦ c k) s t = gridLinearInterpolant η c t := by
  simp [gridBilinearInterpolant_def]

/-- If `a` ignores its second index, `gridBilinearInterpolant` is `gridLinearInterpolant`. -/
@[simp] theorem gridBilinearInterpolant_const_right (τ η : ℝ) (c : ℕ → E) (s t : ℝ) :
    gridBilinearInterpolant τ η (fun n _ ↦ c n) s t = gridLinearInterpolant τ c s := by
  simp [gridBilinearInterpolant_def]

/-- `gridBilinearInterpolant τ η` is additive in the interpolated family. -/
@[simp] theorem gridBilinearInterpolant_add (τ η : ℝ) (a b : ℕ → ℕ → E) (s t : ℝ) :
    gridBilinearInterpolant τ η (a + b) s t =
      gridBilinearInterpolant τ η a s t + gridBilinearInterpolant τ η b s t := by
  simp only [gridBilinearInterpolant_def, Pi.add_apply, ← Pi.add_def, gridLinearInterpolant_add]

/-- `gridBilinearInterpolant τ η` commutes with scalar multiplication commuting with `ℝ`. -/
@[simp] theorem gridBilinearInterpolant_smul {R : Type*} [DistribSMul R E] [SMulCommClass ℝ R E]
    (τ η : ℝ) (r : R) (a : ℕ → ℕ → E) (s t : ℝ) :
    gridBilinearInterpolant τ η (r • a) s t = r • gridBilinearInterpolant τ η a s t := by
  simp only [gridBilinearInterpolant_def, Pi.smul_apply, ← Pi.smul_def, gridLinearInterpolant_smul]

/-- Swapping the two coordinates commutes with `gridBilinearInterpolant`. -/
theorem gridBilinearInterpolant_swap (τ η : ℝ) (a : ℕ → ℕ → E) (s t : ℝ) :
    gridBilinearInterpolant η τ (Function.swap a) t s = gridBilinearInterpolant τ η a s t := by
  simp only [gridBilinearInterpolant_apply, Function.swap, smul_add, smul_smul,
    mul_comm (stepWeight τ ⌊s / τ⌋₊ s), mul_comm (1 - stepWeight τ ⌊s / τ⌋₊ s)]; ac_rfl

/-- On `[n τ, (n + 1) τ] × [k η, (k + 1) η]` (`τ, η > 0`), `gridBilinearInterpolant τ η a` agrees
with the four-corner bilinear combination. -/
theorem gridBilinearInterpolant_eq_of_mem_Icc {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η) (a : ℕ → ℕ → E)
    {n k : ℕ} {s t : ℝ} (hs : s ∈ Icc ((n : ℝ) * τ) (((n : ℝ) + 1) * τ))
    (ht : t ∈ Icc ((k : ℝ) * η) (((k : ℝ) + 1) * η)) :
    gridBilinearInterpolant τ η a s t =
      stepWeight η k t • (stepWeight τ n s • a n k + (1 - stepWeight τ n s) • a (n + 1) k) +
      (1 - stepWeight η k t) •
        (stepWeight τ n s • a n (k + 1) + (1 - stepWeight τ n s) • a (n + 1) (k + 1)) := by
  rw [gridBilinearInterpolant_def, gridLinearInterpolant_eq_of_mem_Icc hη _ k ht,
    gridLinearInterpolant_eq_of_mem_Icc hτ _ n hs, gridLinearInterpolant_eq_of_mem_Icc hτ _ n hs]

/-- For `τ, η > 0`, `gridBilinearInterpolant τ η a` is jointly continuous on `[0, ∞) × [0, ∞)`. -/
theorem continuousOn_gridBilinearInterpolant [TopologicalSpace E] [ContinuousAdd E]
    [ContinuousSMul ℝ E] {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η) (a : ℕ → ℕ → E) :
    ContinuousOn (fun p : ℝ × ℝ ↦ gridBilinearInterpolant τ η a p.1 p.2) (Ici 0 ×ˢ Ici 0) := by
  have hlf : LocallyFinite fun p : ℕ × ℕ ↦
      Icc ((p.1 : ℝ) * τ) (((p.1 : ℝ) + 1) * τ) ×ˢ Icc ((p.2 : ℝ) * η) (((p.2 : ℝ) + 1) * η) := by
    simpa only [Set.prod_eq] using
      ((locallyFinite_Icc_natCast_mul hτ).preimage_continuous continuous_fst).inter
        ((locallyFinite_Icc_natCast_mul hη).preimage_continuous continuous_snd)
  nth_rw 1 [← iUnion_Icc_natCast_mul hτ]; rw [← iUnion_Icc_natCast_mul hη, ← iUnion_prod]
  refine hlf.continuousOn_iUnion (fun _ ↦ isClosed_Icc.prod isClosed_Icc) fun ⟨n, k⟩ ↦
    (by fun_prop : ContinuousOn (fun p : ℝ × ℝ ↦
      stepWeight η k p.2 • (stepWeight τ n p.1 • a n k + (1 - stepWeight τ n p.1) • a (n + 1) k) +
      (1 - stepWeight η k p.2) • (stepWeight τ n p.1 • a n (k + 1) +
        (1 - stepWeight τ n p.1) • a (n + 1) (k + 1))) _).congr
      fun _ hp ↦ gridBilinearInterpolant_eq_of_mem_Icc hτ hη a hp.1 hp.2

end Module

section Order

variable {E : Type*} [AddCommMonoid E] [PartialOrder E] [IsOrderedAddMonoid E]
  [Module ℝ E] [PosSMulMono ℝ E]

/-- At `s, t ≥ 0`, `gridBilinearInterpolant τ η` is monotone in the four corners of the active
cell. -/
theorem gridBilinearInterpolant_le_gridBilinearInterpolant {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η)
    {a b : ℕ → ℕ → E} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (h00 : a ⌊s / τ⌋₊ ⌊t / η⌋₊ ≤ b ⌊s / τ⌋₊ ⌊t / η⌋₊)
    (h10 : a (⌊s / τ⌋₊ + 1) ⌊t / η⌋₊ ≤ b (⌊s / τ⌋₊ + 1) ⌊t / η⌋₊)
    (h01 : a ⌊s / τ⌋₊ (⌊t / η⌋₊ + 1) ≤ b ⌊s / τ⌋₊ (⌊t / η⌋₊ + 1))
    (h11 : a (⌊s / τ⌋₊ + 1) (⌊t / η⌋₊ + 1) ≤ b (⌊s / τ⌋₊ + 1) (⌊t / η⌋₊ + 1)) :
    gridBilinearInterpolant τ η a s t ≤ gridBilinearInterpolant τ η b s t := by
  have hceil {u : ℝ} {f g : ℕ → E} (h0 : f ⌊u⌋₊ ≤ g ⌊u⌋₊) (h1 : f (⌊u⌋₊ + 1) ≤ g (⌊u⌋₊ + 1)) :
      f ⌈u⌉₊ ≤ g ⌈u⌉₊ :=
    (ceil_eq_floor_or_add_one u).elim (· ▸ h0) (· ▸ h1)
  have hrow {k : ℕ} (hk0 : a ⌊s / τ⌋₊ k ≤ b ⌊s / τ⌋₊ k)
      (hk1 : a (⌊s / τ⌋₊ + 1) k ≤ b (⌊s / τ⌋₊ + 1) k) :
      gridLinearInterpolant τ (a · k) s ≤ gridLinearInterpolant τ (b · k) s :=
    gridLinearInterpolant_le_gridLinearInterpolant hτ hs hk0
      (hceil (f := (a · k)) (g := (b · k)) hk0 hk1)
  exact gridLinearInterpolant_le_gridLinearInterpolant hη ht (hrow h00 h10)
    (hceil (f := fun k ↦ gridLinearInterpolant τ (a · k) s)
      (g := fun k ↦ gridLinearInterpolant τ (b · k) s) (hrow h00 h10) (hrow h01 h11))

/-- If `m` lies below all four corners of the active cell at `s, t ≥ 0`, then
`m ≤ gridBilinearInterpolant τ η a s t`. -/
theorem le_gridBilinearInterpolant {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η) {a : ℕ → ℕ → E}
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) {m : E}
    (h00 : m ≤ a ⌊s / τ⌋₊ ⌊t / η⌋₊) (h10 : m ≤ a (⌊s / τ⌋₊ + 1) ⌊t / η⌋₊)
    (h01 : m ≤ a ⌊s / τ⌋₊ (⌊t / η⌋₊ + 1)) (h11 : m ≤ a (⌊s / τ⌋₊ + 1) (⌊t / η⌋₊ + 1)) :
    m ≤ gridBilinearInterpolant τ η a s t := by
  simpa using gridBilinearInterpolant_le_gridBilinearInterpolant hτ hη hs ht
    (a := fun _ _ ↦ m) h00 h10 h01 h11

/-- If all four corners of the active cell at `s, t ≥ 0` are at most `M`, then so is
`gridBilinearInterpolant τ η a s t`. -/
theorem gridBilinearInterpolant_le {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η) {a : ℕ → ℕ → E}
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) {M : E}
    (h00 : a ⌊s / τ⌋₊ ⌊t / η⌋₊ ≤ M) (h10 : a (⌊s / τ⌋₊ + 1) ⌊t / η⌋₊ ≤ M)
    (h01 : a ⌊s / τ⌋₊ (⌊t / η⌋₊ + 1) ≤ M) (h11 : a (⌊s / τ⌋₊ + 1) (⌊t / η⌋₊ + 1) ≤ M) :
    gridBilinearInterpolant τ η a s t ≤ M := by
  simpa using gridBilinearInterpolant_le_gridBilinearInterpolant hτ hη hs ht
    (b := fun _ _ ↦ M) h00 h10 h01 h11

end Order

section Mul

variable {A : Type*} [NonUnitalNonAssocSemiring A] [Module ℝ A]

/-- `gridBilinearInterpolant τ η` commutes with left multiplication by a constant. -/
@[simp] theorem gridBilinearInterpolant_const_mul [SMulCommClass ℝ A A] (τ η : ℝ) (r : A)
    (a : ℕ → ℕ → A) (s t : ℝ) : gridBilinearInterpolant τ η (fun n k ↦ r * a n k) s t =
      r * gridBilinearInterpolant τ η a s t := by
  simpa only [Pi.smul_def, smul_eq_mul] using gridBilinearInterpolant_smul τ η r a s t

/-- `gridBilinearInterpolant τ η` commutes with right multiplication by a constant. -/
@[simp] theorem gridBilinearInterpolant_mul_const [IsScalarTower ℝ A A] (τ η : ℝ) (a : ℕ → ℕ → A)
    (r : A) (s t : ℝ) : gridBilinearInterpolant τ η (fun n k ↦ a n k * r) s t =
      gridBilinearInterpolant τ η a s t * r := by
  simp only [gridBilinearInterpolant_def, gridLinearInterpolant_mul_const]

end Mul

section Group

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- `gridBilinearInterpolant τ η` commutes with negation of the interpolated family. -/
@[simp] theorem gridBilinearInterpolant_neg (τ η : ℝ) (a : ℕ → ℕ → E) (s t : ℝ) :
    gridBilinearInterpolant τ η (-a) s t = -gridBilinearInterpolant τ η a s t := by
  simpa only [neg_one_smul] using gridBilinearInterpolant_smul τ η (-1 : ℝ) a s t

/-- `gridBilinearInterpolant τ η` preserves subtraction of interpolated families. -/
@[simp] theorem gridBilinearInterpolant_sub (τ η : ℝ) (a b : ℕ → ℕ → E) (s t : ℝ) :
    gridBilinearInterpolant τ η (a - b) s t =
      gridBilinearInterpolant τ η a s t - gridBilinearInterpolant τ η b s t := by
  simp only [sub_eq_add_neg, gridBilinearInterpolant_add, gridBilinearInterpolant_neg]

end Group

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Right-hand partial derivative in the second argument of `gridBilinearInterpolant` at `t ≥ 0`. -/
theorem hasDerivWithinAt_gridBilinearInterpolant_right (τ : ℝ) {η : ℝ} (hη : 0 < η)
    (a : ℕ → ℕ → E) (s : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (gridBilinearInterpolant τ η a s)
      (η⁻¹ • (gridLinearInterpolant τ (a · (⌊t / η⌋₊ + 1)) s -
        gridLinearInterpolant τ (a · ⌊t / η⌋₊) s)) (Ici t) t :=
  hasDerivWithinAt_gridLinearInterpolant hη (fun k ↦ gridLinearInterpolant τ (a · k) s) ht

/-- Right-hand partial derivative in the first argument of `gridBilinearInterpolant` at `s ≥ 0`. -/
theorem hasDerivWithinAt_gridBilinearInterpolant_left {τ : ℝ} (hτ : 0 < τ) (η : ℝ)
    (a : ℕ → ℕ → E) {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    HasDerivWithinAt (gridBilinearInterpolant τ η a · t)
      (τ⁻¹ • (gridLinearInterpolant η (a (⌊s / τ⌋₊ + 1)) t -
        gridLinearInterpolant η (a ⌊s / τ⌋₊) t)) (Ici s) s :=
  (hasDerivWithinAt_gridLinearInterpolant hτ (fun n ↦ gridLinearInterpolant η (a n) t) hs).congr
    (fun u _ ↦ (gridBilinearInterpolant_swap τ η a u t).symm)
    (gridBilinearInterpolant_swap τ η a s t).symm

/-- Right-hand derivative of the diagonal `u ↦ gridBilinearInterpolant τ η a u u` at `t ≥ 0`. -/
theorem hasDerivWithinAt_gridBilinearInterpolant_diag {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η)
    (a : ℕ → ℕ → E) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun u ↦ gridBilinearInterpolant τ η a u u)
      ((stepWeight η ⌊t / η⌋₊ t / τ) • (a (⌊t / τ⌋₊ + 1) ⌊t / η⌋₊ - a ⌊t / τ⌋₊ ⌊t / η⌋₊) +
        ((1 - stepWeight η ⌊t / η⌋₊ t) / τ) •
          (a (⌊t / τ⌋₊ + 1) (⌊t / η⌋₊ + 1) - a ⌊t / τ⌋₊ (⌊t / η⌋₊ + 1)) +
        (stepWeight τ ⌊t / τ⌋₊ t / η) • (a ⌊t / τ⌋₊ (⌊t / η⌋₊ + 1) - a ⌊t / τ⌋₊ ⌊t / η⌋₊) +
        ((1 - stepWeight τ ⌊t / τ⌋₊ t) / η) •
          (a (⌊t / τ⌋₊ + 1) (⌊t / η⌋₊ + 1) - a (⌊t / τ⌋₊ + 1) ⌊t / η⌋₊))
      (Ici t) t := by
  have hdiag : (fun u ↦ gridBilinearInterpolant τ η a u u) =
      gridPiecewise η fun k u ↦ stepWeight η k u • gridLinearInterpolant τ (a · k) u +
        (1 - stepWeight η k u) • gridLinearInterpolant τ (a · (k + 1)) u := rfl
  rw [hdiag, hasDerivWithinAt_gridPiecewise_iff hη ht]
  have hd1 := ((hasDerivAt_stepWeight η ⌊t / η⌋₊ t).hasDerivWithinAt).smul
    (hasDerivWithinAt_gridLinearInterpolant hτ (a · ⌊t / η⌋₊) ht)
  have hd2 := (((hasDerivAt_stepWeight η ⌊t / η⌋₊ t).const_sub 1).hasDerivWithinAt).smul
    (hasDerivWithinAt_gridLinearInterpolant hτ (a · (⌊t / η⌋₊ + 1)) ht)
  refine (hd1.add hd2).congr_deriv ?_
  simp only [gridLinearInterpolant_def, neg_neg, div_eq_mul_inv, smul_add, smul_sub,
    smul_smul, neg_smul, sub_smul, one_smul]; module

end Normed

end GridBilinearInterpolant

end TauCeti
