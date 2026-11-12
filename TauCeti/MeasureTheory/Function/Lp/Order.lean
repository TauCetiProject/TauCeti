/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.Order.PartialSups

/-!
# `Lᵖ` is an ordered module

Mathlib orders `Lᵖ` almost everywhere (`MeasureTheory.Lp.coeFn_le`). If scalar multiplication on
the values is monotone, then so is scalar multiplication on `Lᵖ` classes, since it is computed
almost everywhere pointwise. In particular real `Lᵖ` is an ordered real module, which is the
hypothesis under which Mathlib's Bochner integral of almost everywhere nonnegative functions is
nonnegative (`MeasureTheory.integral_nonneg_of_ae`), now applicable to `Lᵖ`-valued functions.
Finite running suprema also preserve `MemLp`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

/-- A finite running supremum of `Lᵖ` functions is in `Lᵖ`. -/
theorem MemLp.partialSups {α E ι : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {p : ℝ≥0∞} [NormedAddCommGroup E] [Lattice E] [HasSolidNorm E]
    [IsOrderedAddMonoid E] [Preorder ι] [LocallyFiniteOrderBot ι]
    {f : ι → α → E} {i : ι} (hf : ∀ j ≤ i, MemLp (f j) p μ) :
    MemLp (partialSups f i) p μ := by
  rw [partialSups_apply]
  exact Finset.sup'_induction _ _ (p := fun g ↦ MemLp g p μ)
    (fun _ hf _ hg ↦ hf.sup hg) (fun j hj ↦ hf j (Finset.mem_Iic.mp hj))

end MeasureTheory

namespace MeasureTheory.Lp

variable {α 𝕜 E : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞} [NormedRing 𝕜]
  [PartialOrder 𝕜] [NormedAddCommGroup E] [PartialOrder E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- Multiplying an `Lᵖ` class by a nonnegative scalar is monotone if it is so on the values. -/
instance [PosSMulMono 𝕜 E] : PosSMulMono 𝕜 (Lp E p μ) where
  smul_le_smul_of_nonneg_left c hc f g hfg := by
    rw [← coeFn_le] at hfg ⊢
    filter_upwards [coeFn_smul c f, coeFn_smul c g, hfg] with x hf hg hx
    rw [hf, hg]
    exact smul_le_smul_of_nonneg_left hx hc

/-- Multiplying a nonnegative `Lᵖ` class by scalars is monotone if it is so on the values. -/
instance [SMulPosMono 𝕜 E] : SMulPosMono 𝕜 (Lp E p μ) where
  smul_le_smul_of_nonneg_right f hf c d hcd := by
    rw [← coeFn_nonneg] at hf
    rw [← coeFn_le]
    filter_upwards [coeFn_smul c f, coeFn_smul d f, hf] with x hc hd hx
    rw [hc, hd]
    exact smul_le_smul_of_nonneg_right hcd hx

/-- `Lᵖ` with values in an ordered module is an ordered module, ordered almost everywhere. -/
instance [IsOrderedModule 𝕜 E] : IsOrderedModule 𝕜 (Lp E p μ) where

end MeasureTheory.Lp
