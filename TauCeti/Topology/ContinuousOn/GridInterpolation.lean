/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import TauCeti.Algebra.Order.Floor.GridInterpolation
import Mathlib.Topology.Algebra.Ring.Real
import TauCeti.Algebra.Order.Floor.Semifield
import TauCeti.Topology.LocallyFinite.Basic
import TauCeti.Topology.Order.Interval.Basic

/-!
# Continuity of piecewise gluing and grid interpolation

Using the locally finite closed cover of `[0, ∞)` by `[n τ, (n + 1) τ]`
(`TauCeti.locallyFinite_Icc_natCast_mul`), this file establishes right-neighborhood agreement and
continuity on `[0, ∞)` (and `[0, ∞) × [0, ∞)`) for `TauCeti.gridPiecewise`, `TauCeti.stepWeight`,
`TauCeti.gridLinearInterpolant`, and `TauCeti.gridBilinearInterpolant`.

## Main results
* `TauCeti.gridPiecewise_eventuallyEq_nhdsWithin_Ici`, `TauCeti.continuousOn_gridPiecewise`.
* `TauCeti.continuous_stepWeight`.
* `TauCeti.continuousOn_gridLinearInterpolant`.
* `TauCeti.continuousOn_gridBilinearInterpolant`.
-/

public section

noncomputable section

open Set Topology

namespace TauCeti

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

/-- `stepWeight τ n` is continuous on `ℝ`. -/
@[fun_prop] theorem continuous_stepWeight (τ : ℝ) (n : ℕ) : Continuous (stepWeight τ n) := by
  simp only [funext (stepWeight_def τ n)]; fun_prop

/-- For `τ > 0`, `gridLinearInterpolant τ c` is continuous on `[0, ∞)`. -/
theorem continuousOn_gridLinearInterpolant {E : Type*} [AddCommMonoid E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E] {τ : ℝ} (hτ : 0 < τ)
    (c : ℕ → E) : ContinuousOn (gridLinearInterpolant τ c) (Ici 0) := by
  rw [← iUnion_Icc_natCast_mul hτ]
  exact (locallyFinite_Icc_natCast_mul hτ).continuousOn_iUnion (fun _ ↦ isClosed_Icc) fun n ↦
    (by fun_prop : ContinuousOn (fun t : ℝ ↦
      stepWeight τ n t • c n + (1 - stepWeight τ n t) • c (n + 1)) _).congr
      fun _ ht ↦ gridLinearInterpolant_eq_of_mem_Icc hτ c n ht

/-- For `τ, η > 0`, `gridBilinearInterpolant τ η a` is jointly continuous on `[0, ∞) × [0, ∞)`. -/
theorem continuousOn_gridBilinearInterpolant {E : Type*} [AddCommMonoid E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E] {τ η : ℝ} (hτ : 0 < τ)
    (hη : 0 < η) (a : ℕ → ℕ → E) :
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

end TauCeti
