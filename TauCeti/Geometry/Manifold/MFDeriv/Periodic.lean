/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Order.Interval.Set.Union

/-!
# Differentiability of piecewise differentiable periodic curves

Let `γ : ℝ → M` be a `T`-periodic curve in a manifold, `T > 0`, and let
`t 0, …, t n = t 0 + T` be parameters subdividing a period. If `γ` is differentiable on each
open interval `(t i, t (i + 1))`, then it is differentiable at every parameter which is not one
of the `t i` up to an integer multiple of `T`. These parameters form a countable set, so `γ` is
differentiable at almost every parameter. A closed curve on the circle `AddCircle T` given on a
period by finitely many `C¹` pieces, seen as a periodic curve on `ℝ`, is the basic example.

## Main results

* `Function.Periodic.mdifferentiableAt_of_mdifferentiableOn`: differentiability off the
  translates of the subdivision points.
* `Function.Periodic.ae_mdifferentiableAt_of_mdifferentiableOn`: differentiability at almost
  every parameter.
-/

public section

open Set Function MeasureTheory
open scoped Manifold

namespace Function.Periodic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {γ : ℝ → M} {T : ℝ}
  {t : ℕ → ℝ} {n : ℕ}

/-- A `T`-periodic curve which is differentiable on the open intervals `(t i, t (i + 1))` of a
subdivision `t 0, …, t n = t 0 + T` of a period is differentiable at every parameter which is not
one of the `t i` up to an integer multiple of `T`. -/
theorem mdifferentiableAt_of_mdifferentiableOn (hγ : Periodic γ T) (hT : 0 < T)
    (htn : t n = t 0 + T) (hd : ∀ i < n, MDifferentiableOn 𝓘(ℝ, ℝ) I γ (Ioo (t i) (t (i + 1))))
    {s : ℝ} (hs : ∀ i < n, ∀ k : ℤ, s ≠ t i + k * T) :
    MDifferentiableAt 𝓘(ℝ, ℝ) I γ s := by
  set k := toIcoDiv hT (t 0) s
  have hk : s - k * T = toIcoMod hT (t 0) s := by
    rw [← self_sub_toIcoDiv_zsmul, zsmul_eq_mul]
  have hmem : s - k * T ∈ Ico (t 0) (t n) := htn ▸ hk ▸ toIcoMod_mem_Ico hT (t 0) s
  obtain ⟨i, hi, hsi⟩ := mem_iUnion₂.mp (Ico_subset_biUnion_Ico n t hmem)
  have hi : i < n := Finset.mem_range.mp hi
  have hsi' : s - k * T ∈ Ioo (t i) (t (i + 1)) :=
    ⟨hsi.1.lt_of_ne fun h ↦ hs i hi k (by linarith), hsi.2⟩
  have hd' := (hd i hi).mdifferentiableAt (isOpen_Ioo.mem_nhds hsi')
  simpa only [sub_add_cancel] using ((hγ.int_mul k).mdifferentiableAt_add).mpr hd'

/-- A `T`-periodic curve which is differentiable on the open intervals `(t i, t (i + 1))` of a
subdivision `t 0, …, t n = t 0 + T` of a period is differentiable at almost every parameter. -/
theorem ae_mdifferentiableAt_of_mdifferentiableOn (hγ : Periodic γ T) (hT : 0 < T)
    (htn : t n = t 0 + T) (hd : ∀ i < n, MDifferentiableOn 𝓘(ℝ, ℝ) I γ (Ioo (t i) (t (i + 1)))) :
    ∀ᵐ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ s := by
  have hc : (⋃ (i : ℕ) (k : ℤ), ({t i + k * T} : Set ℝ)).Countable :=
    countable_iUnion fun _ ↦ countable_iUnion fun _ ↦ countable_singleton _
  filter_upwards [hc.ae_notMem volume] with s hs
  exact hγ.mdifferentiableAt_of_mdifferentiableOn hT htn hd fun i _ k h ↦
    hs (mem_iUnion₂.mpr ⟨i, k, h⟩)

end Function.Periodic
