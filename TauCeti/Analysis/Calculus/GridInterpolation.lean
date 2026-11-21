/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import TauCeti.Algebra.Order.Floor.Semifield

/-!
# Piecewise gluing and linear/bilinear interpolation on uniform grids

For a step size `τ > 0`, the nonnegative half-line `[0, ∞)` is covered by the uniform grid cells
`[n τ, (n + 1) τ)` (`n : ℕ`), with each `t ≥ 0` lying in the cell indexed by `⌊t / τ⌋₊`. Given a
family of functions `g : ℕ → ℝ → α`, `TauCeti.piecewiseStep τ g` glues the pieces along this grid
by `t ↦ g ⌊t / τ⌋₊ t`. When adjacent pieces agree at each grid point `(n + 1) τ`, the glued
function agrees with `g n` on the closed cell `[n τ, (n + 1) τ]` and is continuous on `[0, ∞)`
whenever each `g n` is continuous on its closed cell; independently of the matching condition, its
right-hand derivative at any `t ≥ 0` equals that of `g ⌊t / τ⌋₊`.

Using the cell barycentric weight `TauCeti.stepWeight τ n t = ((n + 1) τ - t) / τ`, we build:

* `TauCeti.gridLinearInterpolant τ c`: the piecewise linear interpolant of a sequence `c : ℕ → E`
  in a real module `E`, taking the value `c n` at `n τ`, continuous on `[0, ∞)`, and having
  right-hand derivative `τ⁻¹ • (c (⌊t / τ⌋₊ + 1) - c ⌊t / τ⌋₊)` in a real normed space.
* `TauCeti.gridBilinearInterpolant τ η a`: the piecewise bilinear interpolant of a doubly indexed
  family `a : ℕ → ℕ → E` on the product grid `(n τ, k η)`, taking the value `a n k` at
  `(n τ, k η)`, jointly continuous on `[0, ∞) × [0, ∞)`, with explicit one-sided partial
  derivatives and diagonal right-hand derivative along `t ↦ (t, t)`.

## Main definitions

* `TauCeti.piecewiseStep`: glues a family `g : ℕ → ℝ → α` on the uniform grid `[n τ, (n + 1) τ)`.
* `TauCeti.stepWeight`: the barycentric weight `((n + 1) τ - t) / τ` on `[n τ, (n + 1) τ]`.
* `TauCeti.gridLinearInterpolant`: piecewise linear interpolant of `c : ℕ → E` with step `τ`.
* `TauCeti.gridBilinearInterpolant`: piecewise bilinear interpolant of `a : ℕ → ℕ → E` with steps
  `τ` and `η`.

## Main results

* `TauCeti.continuousOn_piecewiseStep`, `TauCeti.hasDerivWithinAt_piecewiseStep_iff`: continuity
  and right-hand derivative of `piecewiseStep` on `[0, ∞)`.
* `TauCeti.continuousOn_gridLinearInterpolant`, `TauCeti.hasDerivWithinAt_gridLinearInterpolant`:
  continuity and right-hand derivative of `gridLinearInterpolant` on `[0, ∞)`, alongside its
  linearity lemmas (`gridLinearInterpolant_add`, `gridLinearInterpolant_smul`, etc.).
* `TauCeti.continuousOn_gridBilinearInterpolant`,
  `TauCeti.hasDerivWithinAt_gridBilinearInterpolant_diag`: joint continuity on `[0, ∞) × [0, ∞)`
  and diagonal right-hand derivative of `gridBilinearInterpolant`, alongside its linearity lemmas
  (`gridBilinearInterpolant_add`, `gridBilinearInterpolant_smul`, etc.).
-/

public section

noncomputable section

open Set Topology

namespace TauCeti

/-! ### Uniform-grid gluing -/

section PiecewiseStep

/-- Glues a family of functions `g n` along the uniform grid `[n τ, (n + 1) τ)` via the floor
index `⌊t / τ⌋₊`. -/
def piecewiseStep {α : Type*} (τ : ℝ) (g : ℕ → ℝ → α) (t : ℝ) : α :=
  g ⌊t / τ⌋₊ t

/-- Unconditional defining equation of `piecewiseStep`. -/
theorem piecewiseStep_def {α : Type*} (τ : ℝ) (g : ℕ → ℝ → α) (t : ℝ) :
    piecewiseStep τ g t = g ⌊t / τ⌋₊ t :=
  (rfl)

/-- At `0`, `piecewiseStep τ g` evaluates the `0`-th piece at `0`. -/
@[simp]
theorem piecewiseStep_zero {α : Type*} (τ : ℝ) (g : ℕ → ℝ → α) :
    piecewiseStep τ g 0 = g 0 0 := by
  simp [piecewiseStep_def]

/-- At the grid point `n * τ` (with `τ ≠ 0`), `piecewiseStep τ g` evaluates `g n` at `n * τ`. -/
@[simp]
theorem piecewiseStep_natCast_mul {α : Type*} {τ : ℝ} (hτ : τ ≠ 0) (g : ℕ → ℝ → α) (n : ℕ) :
    piecewiseStep τ g ((n : ℝ) * τ) = g n ((n : ℝ) * τ) := by
  simp [piecewiseStep_def, mul_div_cancel_right₀ _ hτ]

/-- Gluing a constant family `fun _ ↦ f` returns `f`. -/
@[simp]
theorem piecewiseStep_const {α : Type*} (τ : ℝ) (f : ℝ → α) (t : ℝ) :
    piecewiseStep τ (fun _ ↦ f) t = f t :=
  (rfl)

/-- On the half-open cell `[n τ, (n + 1) τ)`, `piecewiseStep τ g` agrees with `g n`. -/
theorem piecewiseStep_eq_of_mem_Ico {α : Type*} {τ : ℝ} (hτ : 0 < τ) (g : ℕ → ℝ → α) (n : ℕ)
    {t : ℝ} (ht : t ∈ Ico ((n : ℝ) * τ) (((n : ℝ) + 1) * τ)) :
    piecewiseStep τ g t = g n t := by
  have ht0 : 0 ≤ t / τ := div_nonneg ((mul_nonneg n.cast_nonneg hτ.le).trans ht.1) hτ.le
  have hfl : ⌊t / τ⌋₊ = n :=
    (Nat.floor_eq_iff ht0).2 ⟨(le_div_iff₀ hτ).2 ht.1, (div_lt_iff₀ hτ).2 ht.2⟩
  simp [piecewiseStep_def, hfl]

/-- When `g n` and `g (n + 1)` agree at `(n + 1) τ`, `piecewiseStep τ g` agrees with `g n` on the
entire closed interval `[n τ, (n + 1) τ]`. -/
theorem piecewiseStep_eq_of_mem_Icc {α : Type*} {τ : ℝ} (hτ : 0 < τ) {g : ℕ → ℝ → α} {n : ℕ}
    (hjoin : g n (((n : ℝ) + 1) * τ) = g (n + 1) (((n : ℝ) + 1) * τ))
    {t : ℝ} (ht : t ∈ Icc ((n : ℝ) * τ) (((n : ℝ) + 1) * τ)) :
    piecewiseStep τ g t = g n t := by
  rcases ht.2.eq_or_lt with rfl | hlt
  · have heq := piecewiseStep_natCast_mul hτ.ne' g (n + 1)
    push_cast at heq
    rw [heq, hjoin]
  · exact piecewiseStep_eq_of_mem_Ico hτ g n ⟨ht.1, hlt⟩

/-- On a right neighborhood of `t ≥ 0`, `piecewiseStep τ g` coincides with the active piece
`g ⌊t / τ⌋₊`. -/
theorem piecewiseStep_eventuallyEq_nhdsWithin_Ici {α : Type*} {τ : ℝ} (hτ : 0 < τ)
    (g : ℕ → ℝ → α) {t : ℝ} (ht : 0 ≤ t) :
    piecewiseStep τ g =ᶠ[𝓝[Ici t] t] g ⌊t / τ⌋₊ := by
  have hmem : t ∈ Ico ((⌊t / τ⌋₊ : ℝ) * τ) (((⌊t / τ⌋₊ : ℝ) + 1) * τ) := mem_Ico_floor_mul hτ ht
  filter_upwards [mem_nhdsWithin.2 ⟨Iio (((⌊t / τ⌋₊ : ℝ) + 1) * τ), isOpen_Iio, hmem.2,
    Subset.rfl⟩] with s hs
  exact piecewiseStep_eq_of_mem_Ico hτ g ⌊t / τ⌋₊ ⟨hmem.1.trans hs.2, hs.1⟩

private theorem locallyFinite_Icc_natCast_mul {τ : ℝ} (hτ : 0 < τ) :
    LocallyFinite fun n : ℕ ↦ Icc ((n : ℝ) * τ) (((n : ℝ) + 1) * τ) := fun t ↦
  ⟨Iio (t + τ), Iio_mem_nhds (by linarith), (finite_lt_nat (⌊(t + τ) / τ⌋₊ + 1)).subset
    fun n ⟨x, hx, hxt⟩ ↦ Nat.cast_lt (α := ℝ).1 <| by
      push_cast
      exact ((lt_div_iff₀ hτ).2 (hx.1.trans_lt hxt)).trans (Nat.lt_floor_add_one _)⟩

private theorem iUnion_Icc_natCast_mul {τ : ℝ} (hτ : 0 < τ) :
    (⋃ n : ℕ, Icc ((n : ℝ) * τ) (((n : ℝ) + 1) * τ)) = Ici 0 := by
  ext t
  simp only [mem_iUnion, mem_Icc, mem_Ici]
  exact ⟨fun ⟨n, h1, _⟩ ↦ (mul_nonneg n.cast_nonneg hτ.le).trans h1,
    fun ht ↦ ⟨⌊t / τ⌋₊, Ico_subset_Icc_self (mem_Ico_floor_mul hτ ht)⟩⟩

/-- A `piecewiseStep` function whose pieces are continuous on `[n τ, (n + 1) τ]` and match at the
grid points is continuous on `[0, ∞)`. -/
theorem continuousOn_piecewiseStep {α : Type*} [TopologicalSpace α] {τ : ℝ} (hτ : 0 < τ)
    {g : ℕ → ℝ → α}
    (hjoin : ∀ n : ℕ, g n (((n : ℝ) + 1) * τ) = g (n + 1) (((n : ℝ) + 1) * τ))
    (hcont : ∀ n : ℕ, ContinuousOn (g n) (Icc ((n : ℝ) * τ) (((n : ℝ) + 1) * τ))) :
    ContinuousOn (piecewiseStep τ g) (Ici 0) := by
  rw [← iUnion_Icc_natCast_mul hτ]
  exact (locallyFinite_Icc_natCast_mul hτ).continuousOn_iUnion (fun _ ↦ isClosed_Icc) fun n ↦
    (hcont n).congr fun _ hs ↦ piecewiseStep_eq_of_mem_Icc hτ (hjoin n) hs

/-- Right-hand derivative of `piecewiseStep τ g` at `t ≥ 0`. Because `piecewiseStep τ g` coincides
with `g ⌊t / τ⌋₊` on a right neighborhood of `t`, its right-hand derivative at `t` agrees with that
of `g ⌊t / τ⌋₊` without any matching condition at the grid points. -/
theorem hasDerivWithinAt_piecewiseStep_iff {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousSMul ℝ E] {τ : ℝ} (hτ : 0 < τ) {g : ℕ → ℝ → E}
    {t : ℝ} (ht : 0 ≤ t) {f' : E} :
    HasDerivWithinAt (piecewiseStep τ g) f' (Ici t) t ↔
      HasDerivWithinAt (g ⌊t / τ⌋₊) f' (Ici t) t :=
  (piecewiseStep_eventuallyEq_nhdsWithin_Ici hτ g ht).hasFDerivWithinAt_iff
    (piecewiseStep_def τ g t)

end PiecewiseStep

/-! ### Barycentric weight on a grid cell -/

section StepWeight

/-- Barycentric weight `((n + 1) τ - t) / τ` of the left endpoint on the cell
`[n τ, (n + 1) τ]`. -/
def stepWeight (τ : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (((n : ℝ) + 1) * τ - t) / τ

/-- Unconditional defining equation of `stepWeight`. -/
theorem stepWeight_def (τ : ℝ) (n : ℕ) (t : ℝ) :
    stepWeight τ n t = (((n : ℝ) + 1) * τ - t) / τ :=
  (rfl)

/-- At the left endpoint `n * τ` (with `τ ≠ 0`), `stepWeight τ n` equals `1`. -/
@[simp]
theorem stepWeight_natCast_mul {τ : ℝ} (hτ : τ ≠ 0) (n : ℕ) :
    stepWeight τ n ((n : ℝ) * τ) = 1 := by
  simp only [stepWeight_def]
  field_simp
  ring

/-- At the right endpoint `(n + 1) * τ`, `stepWeight τ n` vanishes. -/
@[simp]
theorem stepWeight_add_one_mul (τ : ℝ) (n : ℕ) :
    stepWeight τ n (((n : ℝ) + 1) * τ) = 0 := by
  simp [stepWeight_def]

/-- At `(n + 1) * τ` (with `τ ≠ 0`), the next cell's weight `stepWeight τ (n + 1)` equals `1`. -/
@[simp]
theorem stepWeight_succ_mul {τ : ℝ} (hτ : τ ≠ 0) (n : ℕ) :
    stepWeight τ (n + 1) (((n : ℝ) + 1) * τ) = 1 := by
  simpa [Nat.cast_add, Nat.cast_one] using stepWeight_natCast_mul hτ (n + 1)

/-- At `0` (with `τ ≠ 0`), `stepWeight τ 0` equals `1`. -/
@[simp]
theorem stepWeight_zero {τ : ℝ} (hτ : τ ≠ 0) : stepWeight τ 0 0 = 1 := by
  simpa using stepWeight_natCast_mul hτ 0

/-- Barycentric coordinate identity: `stepWeight τ n t` and `1 - stepWeight τ n t` express `t` as
an affine combination of the cell endpoints `n * τ` and `(n + 1) * τ`. -/
theorem stepWeight_mul_add_one_sub_mul {τ : ℝ} (hτ : τ ≠ 0) (n : ℕ) (t : ℝ) :
    stepWeight τ n t * ((n : ℝ) * τ) + (1 - stepWeight τ n t) * (((n : ℝ) + 1) * τ) = t := by
  simp only [stepWeight_def]
  field_simp
  ring

/-- On `[n τ, (n + 1) τ]` with `τ > 0`, `stepWeight τ n t` lies in `[0, 1]`. -/
theorem stepWeight_mem_Icc_of_mem_Icc {τ t : ℝ} (hτ : 0 < τ) {n : ℕ}
    (ht : t ∈ Icc ((n : ℝ) * τ) (((n : ℝ) + 1) * τ)) :
    stepWeight τ n t ∈ Icc (0 : ℝ) 1 :=
  ⟨div_nonneg (sub_nonneg.2 ht.2) hτ.le, (div_le_one hτ).2 (by linarith [ht.1])⟩

/-- For `τ > 0` and `t ≥ 0`, the active cell weight `stepWeight τ ⌊t / τ⌋₊ t` lies in `[0, 1]`. -/
theorem stepWeight_floor_mem_Icc {τ t : ℝ} (hτ : 0 < τ) (ht : 0 ≤ t) :
    stepWeight τ ⌊t / τ⌋₊ t ∈ Icc (0 : ℝ) 1 :=
  stepWeight_mem_Icc_of_mem_Icc hτ (Ico_subset_Icc_self (mem_Ico_floor_mul hτ ht))

/-- `stepWeight τ n` is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_stepWeight (τ : ℝ) (n : ℕ) : Continuous (stepWeight τ n) := by
  unfold stepWeight
  fun_prop

/-- The derivative of `stepWeight τ n` at every `t : ℝ` is `-τ⁻¹`. -/
theorem hasDerivAt_stepWeight (τ : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (stepWeight τ n) (-τ⁻¹) t :=
  (((hasDerivAt_id t).const_sub (((n : ℝ) + 1) * τ)).div_const τ).congr_deriv
    (by simp [neg_div, one_div])

end StepWeight

/-! ### Piecewise linear interpolation on a uniform grid -/

section GridLinearInterpolant

section Module

variable {E : Type*} [AddCommMonoid E] [Module ℝ E]

/-- Piecewise linear interpolant of a sequence `c : ℕ → E` on the uniform grid `n * τ`, affine on
each cell `[n τ, (n + 1) τ]`. -/
def gridLinearInterpolant (τ : ℝ) (c : ℕ → E) : ℝ → E :=
  piecewiseStep τ fun n t ↦ stepWeight τ n t • c n + (1 - stepWeight τ n t) • c (n + 1)

/-- Unconditional defining equation of `gridLinearInterpolant`. -/
theorem gridLinearInterpolant_def (τ : ℝ) (c : ℕ → E) (t : ℝ) :
    gridLinearInterpolant τ c t =
      stepWeight τ ⌊t / τ⌋₊ t • c ⌊t / τ⌋₊ +
        (1 - stepWeight τ ⌊t / τ⌋₊ t) • c (⌊t / τ⌋₊ + 1) :=
  (rfl)

/-- At the grid point `n * τ` (with `τ ≠ 0`), `gridLinearInterpolant τ c` takes the value `c n`. -/
@[simp]
theorem gridLinearInterpolant_natCast_mul {τ : ℝ} (hτ : τ ≠ 0) (c : ℕ → E) (n : ℕ) :
    gridLinearInterpolant τ c ((n : ℝ) * τ) = c n := by
  simp [gridLinearInterpolant, piecewiseStep_natCast_mul hτ, stepWeight_natCast_mul hτ]

/-- At `0` (with `τ ≠ 0`), `gridLinearInterpolant τ c` takes the value `c 0`. -/
@[simp]
theorem gridLinearInterpolant_apply_zero {τ : ℝ} (hτ : τ ≠ 0) (c : ℕ → E) :
    gridLinearInterpolant τ c 0 = c 0 := by
  simpa using gridLinearInterpolant_natCast_mul hτ c 0

/-- The piecewise linear interpolant of the zero sequence is `0`. -/
@[simp]
theorem gridLinearInterpolant_zero (τ t : ℝ) :
    gridLinearInterpolant τ (0 : ℕ → E) t = 0 := by
  simp [gridLinearInterpolant_def]

/-- The piecewise linear interpolant of a constant sequence is constant. -/
@[simp]
theorem gridLinearInterpolant_const (τ : ℝ) (x : E) (t : ℝ) :
    gridLinearInterpolant τ (fun _ ↦ x) t = x := by
  rw [gridLinearInterpolant_def, ← add_smul, add_sub_cancel, one_smul]

/-- `gridLinearInterpolant τ` is additive in the interpolated sequence. -/
@[simp]
theorem gridLinearInterpolant_add (τ : ℝ) (c d : ℕ → E) (t : ℝ) :
    gridLinearInterpolant τ (c + d) t =
      gridLinearInterpolant τ c t + gridLinearInterpolant τ d t := by
  simp only [gridLinearInterpolant_def, Pi.add_apply, smul_add]
  exact add_add_add_comm _ _ _ _

/-- `gridLinearInterpolant τ` commutes with scalar multiplication by any action commuting with
`ℝ`. -/
@[simp]
theorem gridLinearInterpolant_smul {R : Type*} [DistribSMul R E] [SMulCommClass ℝ R E]
    (τ : ℝ) (r : R) (c : ℕ → E) (t : ℝ) :
    gridLinearInterpolant τ (r • c) t = r • gridLinearInterpolant τ c t := by
  simp only [gridLinearInterpolant_def, Pi.smul_apply, smul_comm _ r, smul_add]

/-- On the closed cell `[n τ, (n + 1) τ]` with `τ > 0`, `gridLinearInterpolant τ c` is the affine
combination of `c n` and `c (n + 1)` with weight `stepWeight τ n t`. -/
theorem gridLinearInterpolant_eq_of_mem_Icc {τ : ℝ} (hτ : 0 < τ) (c : ℕ → E) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc ((n : ℝ) * τ) (((n : ℝ) + 1) * τ)) :
    gridLinearInterpolant τ c t = stepWeight τ n t • c n + (1 - stepWeight τ n t) • c (n + 1) :=
  piecewiseStep_eq_of_mem_Icc hτ (by simp [hτ.ne']) ht

/-- For `τ > 0`, `gridLinearInterpolant τ c` is continuous on `[0, ∞)`. -/
theorem continuousOn_gridLinearInterpolant [TopologicalSpace E] [ContinuousAdd E]
    [ContinuousSMul ℝ E] {τ : ℝ} (hτ : 0 < τ) (c : ℕ → E) :
    ContinuousOn (gridLinearInterpolant τ c) (Ici 0) :=
  continuousOn_piecewiseStep hτ (fun _ ↦ by simp [hτ.ne']) fun _ ↦ by fun_prop

end Module

section Mul

variable {A : Type*} [NonUnitalNonAssocSemiring A] [Module ℝ A]

/-- `gridLinearInterpolant τ` commutes with left multiplication by a constant. -/
@[simp]
theorem gridLinearInterpolant_const_mul [SMulCommClass ℝ A A] (τ : ℝ) (r : A) (c : ℕ → A)
    (t : ℝ) :
    gridLinearInterpolant τ (fun n ↦ r * c n) t = r * gridLinearInterpolant τ c t := by
  simpa only [Pi.smul_def, smul_eq_mul] using gridLinearInterpolant_smul τ r c t

/-- `gridLinearInterpolant τ` commutes with right multiplication by a constant. -/
@[simp]
theorem gridLinearInterpolant_mul_const [IsScalarTower ℝ A A] (τ : ℝ) (c : ℕ → A) (r : A)
    (t : ℝ) :
    gridLinearInterpolant τ (fun n ↦ c n * r) t = gridLinearInterpolant τ c t * r := by
  simp only [gridLinearInterpolant_def, add_mul, smul_mul_assoc]

end Mul

section Group

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- `gridLinearInterpolant τ` commutes with negation of the interpolated sequence. -/
@[simp]
theorem gridLinearInterpolant_neg (τ : ℝ) (c : ℕ → E) (t : ℝ) :
    gridLinearInterpolant τ (-c) t = -gridLinearInterpolant τ c t := by
  simpa only [neg_one_smul] using gridLinearInterpolant_smul τ (-1 : ℝ) c t

/-- `gridLinearInterpolant τ` preserves subtraction of interpolated sequences. -/
@[simp]
theorem gridLinearInterpolant_sub (τ : ℝ) (c d : ℕ → E) (t : ℝ) :
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
  unfold gridLinearInterpolant
  rw [hasDerivWithinAt_piecewiseStep_iff hτ ht]
  have hd := ((hasDerivAt_stepWeight τ ⌊t / τ⌋₊ t).smul_const (c ⌊t / τ⌋₊)).add
    (((hasDerivAt_stepWeight τ ⌊t / τ⌋₊ t).const_sub 1).smul_const (c (⌊t / τ⌋₊ + 1)))
  exact (hd.congr_deriv (by simp only [neg_neg]; module)).hasDerivWithinAt

end GridLinearInterpolant

/-! ### Piecewise bilinear interpolation on a uniform product grid -/

section GridBilinearInterpolant

section Module

variable {E : Type*} [AddCommMonoid E] [Module ℝ E]

/-- Piecewise bilinear interpolant of a doubly indexed family `a : ℕ → ℕ → E` on the uniform
product grid `(n * τ, k * η)`, obtained by applying `gridLinearInterpolant` in each variable. -/
def gridBilinearInterpolant (τ η : ℝ) (a : ℕ → ℕ → E) (s t : ℝ) : E :=
  gridLinearInterpolant η (fun k ↦ gridLinearInterpolant τ (a · k) s) t

/-- Unconditional defining equation of `gridBilinearInterpolant` as iterated linear
interpolation. -/
theorem gridBilinearInterpolant_def (τ η : ℝ) (a : ℕ → ℕ → E) (s t : ℝ) :
    gridBilinearInterpolant τ η a s t =
      gridLinearInterpolant η (fun k ↦ gridLinearInterpolant τ (a · k) s) t :=
  (rfl)

/-- Four-corner expansion of `gridBilinearInterpolant τ η a s t`. -/
theorem gridBilinearInterpolant_apply (τ η : ℝ) (a : ℕ → ℕ → E) (s t : ℝ) :
    gridBilinearInterpolant τ η a s t =
      stepWeight η ⌊t / η⌋₊ t •
        (stepWeight τ ⌊s / τ⌋₊ s • a ⌊s / τ⌋₊ ⌊t / η⌋₊ +
          (1 - stepWeight τ ⌊s / τ⌋₊ s) • a (⌊s / τ⌋₊ + 1) ⌊t / η⌋₊) +
      (1 - stepWeight η ⌊t / η⌋₊ t) •
        (stepWeight τ ⌊s / τ⌋₊ s • a ⌊s / τ⌋₊ (⌊t / η⌋₊ + 1) +
          (1 - stepWeight τ ⌊s / τ⌋₊ s) • a (⌊s / τ⌋₊ + 1) (⌊t / η⌋₊ + 1)) :=
  (rfl)

/-- Along the grid line `s = n * τ` (with `τ ≠ 0`), `gridBilinearInterpolant τ η a` reduces to
`gridLinearInterpolant η (a n)`. -/
@[simp]
theorem gridBilinearInterpolant_natCast_mul_left {τ : ℝ} (hτ : τ ≠ 0) (η : ℝ) (a : ℕ → ℕ → E)
    (n : ℕ) (t : ℝ) :
    gridBilinearInterpolant τ η a ((n : ℝ) * τ) t = gridLinearInterpolant η (a n) t := by
  simp [gridBilinearInterpolant_def, hτ]

/-- Along the grid line `t = k * η` (with `η ≠ 0`), `gridBilinearInterpolant τ η a` reduces to
`gridLinearInterpolant τ (a · k)`. -/
@[simp]
theorem gridBilinearInterpolant_natCast_mul_right (τ : ℝ) {η : ℝ} (hη : η ≠ 0) (a : ℕ → ℕ → E)
    (s : ℝ) (k : ℕ) :
    gridBilinearInterpolant τ η a s ((k : ℝ) * η) = gridLinearInterpolant τ (a · k) s := by
  simp [gridBilinearInterpolant_def, hη]

/-- At the grid vertex `(n * τ, k * η)` (with `τ ≠ 0`, `η ≠ 0`), `gridBilinearInterpolant τ η a`
recovers `a n k`. -/
theorem gridBilinearInterpolant_natCast_mul {τ η : ℝ} (hτ : τ ≠ 0) (hη : η ≠ 0) (a : ℕ → ℕ → E)
    (n k : ℕ) :
    gridBilinearInterpolant τ η a ((n : ℝ) * τ) ((k : ℝ) * η) = a n k := by
  simp [hτ, hη]

/-- Along `s = 0` (with `τ ≠ 0`), `gridBilinearInterpolant τ η a` reduces to
`gridLinearInterpolant η (a 0)`. -/
@[simp]
theorem gridBilinearInterpolant_apply_zero_left {τ : ℝ} (hτ : τ ≠ 0) (η : ℝ) (a : ℕ → ℕ → E)
    (t : ℝ) :
    gridBilinearInterpolant τ η a 0 t = gridLinearInterpolant η (a 0) t := by
  simp [gridBilinearInterpolant_def, hτ]

/-- Along `t = 0` (with `η ≠ 0`), `gridBilinearInterpolant τ η a` reduces to
`gridLinearInterpolant τ (a · 0)`. -/
@[simp]
theorem gridBilinearInterpolant_apply_zero_right (τ : ℝ) {η : ℝ} (hη : η ≠ 0) (a : ℕ → ℕ → E)
    (s : ℝ) :
    gridBilinearInterpolant τ η a s 0 = gridLinearInterpolant τ (a · 0) s := by
  simp [gridBilinearInterpolant_def, hη]

/-- At `(0, 0)` (with `τ ≠ 0`, `η ≠ 0`), `gridBilinearInterpolant τ η a` recovers `a 0 0`. -/
theorem gridBilinearInterpolant_apply_zero {τ η : ℝ} (hτ : τ ≠ 0) (hη : η ≠ 0) (a : ℕ → ℕ → E) :
    gridBilinearInterpolant τ η a 0 0 = a 0 0 := by
  simp [hτ, hη]

/-- The piecewise bilinear interpolant of the zero family is `0`. -/
@[simp]
theorem gridBilinearInterpolant_zero (τ η s t : ℝ) :
    gridBilinearInterpolant τ η (0 : ℕ → ℕ → E) s t = 0 := by
  simp [gridBilinearInterpolant_def]

/-- The piecewise bilinear interpolant of a constant family is constant. -/
@[simp]
theorem gridBilinearInterpolant_const (τ η : ℝ) (x : E) (s t : ℝ) :
    gridBilinearInterpolant τ η (fun _ _ ↦ x) s t = x := by
  simp [gridBilinearInterpolant_def]

/-- `gridBilinearInterpolant τ η` is additive in the interpolated family. -/
@[simp]
theorem gridBilinearInterpolant_add (τ η : ℝ) (a b : ℕ → ℕ → E) (s t : ℝ) :
    gridBilinearInterpolant τ η (a + b) s t =
      gridBilinearInterpolant τ η a s t + gridBilinearInterpolant τ η b s t := by
  simp only [gridBilinearInterpolant_def, Pi.add_apply, ← Pi.add_def, gridLinearInterpolant_add]

/-- `gridBilinearInterpolant τ η` commutes with scalar multiplication by any action commuting with
`ℝ`. -/
@[simp]
theorem gridBilinearInterpolant_smul {R : Type*} [DistribSMul R E] [SMulCommClass ℝ R E]
    (τ η : ℝ) (r : R) (a : ℕ → ℕ → E) (s t : ℝ) :
    gridBilinearInterpolant τ η (r • a) s t = r • gridBilinearInterpolant τ η a s t := by
  simp only [gridBilinearInterpolant_def, Pi.smul_apply, ← Pi.smul_def, gridLinearInterpolant_smul]

/-- Swapping the two coordinates commutes with `gridBilinearInterpolant`. -/
theorem gridBilinearInterpolant_swap (τ η : ℝ) (a : ℕ → ℕ → E) (s t : ℝ) :
    gridBilinearInterpolant η τ (Function.swap a) t s = gridBilinearInterpolant τ η a s t := by
  simp only [gridBilinearInterpolant_apply, Function.swap, smul_add, smul_smul]
  simp only [mul_comm (stepWeight τ ⌊s / τ⌋₊ s), mul_comm (1 - stepWeight τ ⌊s / τ⌋₊ s)]
  ac_rfl

/-- On the closed product cell `[n τ, (n + 1) τ] × [k η, (k + 1) η]` with `τ, η > 0`,
`gridBilinearInterpolant τ η a` agrees with the four-corner bilinear combination of
`a n k`, `a (n + 1) k`, `a n (k + 1)`, and `a (n + 1) (k + 1)`. -/
theorem gridBilinearInterpolant_eq_of_mem_Icc {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η) (a : ℕ → ℕ → E)
    {n k : ℕ} {s t : ℝ} (hs : s ∈ Icc ((n : ℝ) * τ) (((n : ℝ) + 1) * τ))
    (ht : t ∈ Icc ((k : ℝ) * η) (((k : ℝ) + 1) * η)) :
    gridBilinearInterpolant τ η a s t =
      stepWeight η k t •
        (stepWeight τ n s • a n k + (1 - stepWeight τ n s) • a (n + 1) k) +
      (1 - stepWeight η k t) •
        (stepWeight τ n s • a n (k + 1) + (1 - stepWeight τ n s) • a (n + 1) (k + 1)) := by
  rw [gridBilinearInterpolant_def, gridLinearInterpolant_eq_of_mem_Icc hη _ k ht,
    gridLinearInterpolant_eq_of_mem_Icc hτ _ n hs, gridLinearInterpolant_eq_of_mem_Icc hτ _ n hs]

/-- For `τ > 0` and `η > 0`, `gridBilinearInterpolant τ η a` is jointly continuous on
`[0, ∞) × [0, ∞)`. -/
theorem continuousOn_gridBilinearInterpolant [TopologicalSpace E] [ContinuousAdd E]
    [ContinuousSMul ℝ E] {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η) (a : ℕ → ℕ → E) :
    ContinuousOn (fun p : ℝ × ℝ ↦ gridBilinearInterpolant τ η a p.1 p.2) (Ici 0 ×ˢ Ici 0) := by
  have hlf : LocallyFinite fun p : ℕ × ℕ ↦
      Icc ((p.1 : ℝ) * τ) (((p.1 : ℝ) + 1) * τ) ×ˢ Icc ((p.2 : ℝ) * η) (((p.2 : ℝ) + 1) * η) := by
    rintro ⟨s, t⟩
    obtain ⟨U, hU, hUf⟩ := locallyFinite_Icc_natCast_mul hτ s
    obtain ⟨V, hV, hVf⟩ := locallyFinite_Icc_natCast_mul hη t
    refine ⟨U ×ˢ V, prod_mem_nhds hU hV, (hUf.prod hVf).subset ?_⟩
    rintro ⟨n, k⟩ ⟨⟨x, y⟩, ⟨hx, hy⟩, hxs, hyt⟩
    exact ⟨⟨x, hx, hxs⟩, ⟨y, hy, hyt⟩⟩
  have hcov : (⋃ p : ℕ × ℕ,
      Icc ((p.1 : ℝ) * τ) (((p.1 : ℝ) + 1) * τ) ×ˢ Icc ((p.2 : ℝ) * η) (((p.2 : ℝ) + 1) * η)) =
      Ici 0 ×ˢ Ici 0 := by
    rw [iUnion_prod (s := fun n : ℕ ↦ Icc ((n : ℝ) * τ) (((n : ℝ) + 1) * τ))
      (t := fun k : ℕ ↦ Icc ((k : ℝ) * η) (((k : ℝ) + 1) * η)),
      iUnion_Icc_natCast_mul hτ, iUnion_Icc_natCast_mul hη]
  rw [← hcov]
  refine hlf.continuousOn_iUnion (fun _ ↦ isClosed_Icc.prod isClosed_Icc) fun ⟨n, k⟩ ↦ ?_
  exact (by fun_prop : ContinuousOn (fun p : ℝ × ℝ ↦
      stepWeight η k p.2 • (stepWeight τ n p.1 • a n k + (1 - stepWeight τ n p.1) • a (n + 1) k) +
      (1 - stepWeight η k p.2) •
        (stepWeight τ n p.1 • a n (k + 1) + (1 - stepWeight τ n p.1) • a (n + 1) (k + 1))) _).congr
    fun _ hp ↦ gridBilinearInterpolant_eq_of_mem_Icc hτ hη a hp.1 hp.2

end Module

section Mul

variable {A : Type*} [NonUnitalNonAssocSemiring A] [Module ℝ A]

/-- `gridBilinearInterpolant τ η` commutes with left multiplication by a constant. -/
@[simp]
theorem gridBilinearInterpolant_const_mul [SMulCommClass ℝ A A] (τ η : ℝ) (r : A)
    (a : ℕ → ℕ → A) (s t : ℝ) :
    gridBilinearInterpolant τ η (fun n k ↦ r * a n k) s t =
      r * gridBilinearInterpolant τ η a s t := by
  simpa only [Pi.smul_def, smul_eq_mul] using gridBilinearInterpolant_smul τ η r a s t

/-- `gridBilinearInterpolant τ η` commutes with right multiplication by a constant. -/
@[simp]
theorem gridBilinearInterpolant_mul_const [IsScalarTower ℝ A A] (τ η : ℝ) (a : ℕ → ℕ → A)
    (r : A) (s t : ℝ) :
    gridBilinearInterpolant τ η (fun n k ↦ a n k * r) s t =
      gridBilinearInterpolant τ η a s t * r := by
  simp only [gridBilinearInterpolant_def, gridLinearInterpolant_mul_const]

end Mul

section Group

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- `gridBilinearInterpolant τ η` commutes with negation of the interpolated family. -/
@[simp]
theorem gridBilinearInterpolant_neg (τ η : ℝ) (a : ℕ → ℕ → E) (s t : ℝ) :
    gridBilinearInterpolant τ η (-a) s t = -gridBilinearInterpolant τ η a s t := by
  simpa only [neg_one_smul] using gridBilinearInterpolant_smul τ η (-1 : ℝ) a s t

/-- `gridBilinearInterpolant τ η` preserves subtraction of interpolated families. -/
@[simp]
theorem gridBilinearInterpolant_sub (τ η : ℝ) (a b : ℕ → ℕ → E) (s t : ℝ) :
    gridBilinearInterpolant τ η (a - b) s t =
      gridBilinearInterpolant τ η a s t - gridBilinearInterpolant τ η b s t := by
  simp only [sub_eq_add_neg, gridBilinearInterpolant_add, gridBilinearInterpolant_neg]

end Group

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Right-hand partial derivative of `gridBilinearInterpolant τ η a` in its second argument at
`t ≥ 0`. -/
theorem hasDerivWithinAt_gridBilinearInterpolant_right (τ : ℝ) {η : ℝ} (hη : 0 < η)
    (a : ℕ → ℕ → E) (s : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (gridBilinearInterpolant τ η a s)
      (η⁻¹ • (gridLinearInterpolant τ (a · (⌊t / η⌋₊ + 1)) s -
        gridLinearInterpolant τ (a · ⌊t / η⌋₊) s)) (Ici t) t :=
  hasDerivWithinAt_gridLinearInterpolant hη (fun k ↦ gridLinearInterpolant τ (a · k) s) ht

/-- Right-hand partial derivative of `gridBilinearInterpolant τ η a` in its first argument at
`s ≥ 0`. -/
theorem hasDerivWithinAt_gridBilinearInterpolant_left {τ : ℝ} (hτ : 0 < τ) (η : ℝ)
    (a : ℕ → ℕ → E) {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    HasDerivWithinAt (gridBilinearInterpolant τ η a · t)
      (τ⁻¹ • (gridLinearInterpolant η (a (⌊s / τ⌋₊ + 1)) t -
        gridLinearInterpolant η (a ⌊s / τ⌋₊) t)) (Ici s) s :=
  (hasDerivWithinAt_gridLinearInterpolant hτ (fun n ↦ gridLinearInterpolant η (a n) t) hs).congr
    (fun u _ ↦ (gridBilinearInterpolant_swap τ η a u t).symm)
    (gridBilinearInterpolant_swap τ η a s t).symm

/-- Right-hand derivative of the diagonal `u ↦ gridBilinearInterpolant τ η a u u` at `t ≥ 0`,
expressed as a weighted sum of forward difference quotients in the two grid directions. -/
theorem hasDerivWithinAt_gridBilinearInterpolant_diag {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η)
    (a : ℕ → ℕ → E) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun u ↦ gridBilinearInterpolant τ η a u u)
      ((stepWeight η ⌊t / η⌋₊ t / τ) •
          (a (⌊t / τ⌋₊ + 1) ⌊t / η⌋₊ - a ⌊t / τ⌋₊ ⌊t / η⌋₊) +
        ((1 - stepWeight η ⌊t / η⌋₊ t) / τ) •
          (a (⌊t / τ⌋₊ + 1) (⌊t / η⌋₊ + 1) - a ⌊t / τ⌋₊ (⌊t / η⌋₊ + 1)) +
        (stepWeight τ ⌊t / τ⌋₊ t / η) •
          (a ⌊t / τ⌋₊ (⌊t / η⌋₊ + 1) - a ⌊t / τ⌋₊ ⌊t / η⌋₊) +
        ((1 - stepWeight τ ⌊t / τ⌋₊ t) / η) •
          (a (⌊t / τ⌋₊ + 1) (⌊t / η⌋₊ + 1) - a (⌊t / τ⌋₊ + 1) ⌊t / η⌋₊))
      (Ici t) t := by
  have hdiag : (fun u ↦ gridBilinearInterpolant τ η a u u) =
      piecewiseStep η fun k u ↦ stepWeight η k u • gridLinearInterpolant τ (a · k) u +
        (1 - stepWeight η k u) • gridLinearInterpolant τ (a · (k + 1)) u := rfl
  rw [hdiag, hasDerivWithinAt_piecewiseStep_iff hη ht]
  have hd1 := ((hasDerivAt_stepWeight η ⌊t / η⌋₊ t).hasDerivWithinAt).smul
    (hasDerivWithinAt_gridLinearInterpolant hτ (a · ⌊t / η⌋₊) ht)
  have hd2 := (((hasDerivAt_stepWeight η ⌊t / η⌋₊ t).const_sub 1).hasDerivWithinAt).smul
    (hasDerivWithinAt_gridLinearInterpolant hτ (a · (⌊t / η⌋₊ + 1)) ht)
  refine (hd1.add hd2).congr_deriv ?_
  simp only [gridLinearInterpolant_def, neg_neg, div_eq_mul_inv, smul_add, smul_sub,
    smul_smul, neg_smul, sub_smul, one_smul]
  module

end Normed

end GridBilinearInterpolant

end TauCeti
