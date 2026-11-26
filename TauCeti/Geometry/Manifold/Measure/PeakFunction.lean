/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.BumpFunction
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Smooth peak functions on manifolds

On a manifold modelled on a finite-dimensional real space, with a measure positive on nonempty
open sets and finite on compact sets, every neighbourhood of a point carries a nonnegative smooth
compactly supported function of unit integral whose support closure lies in the neighbourhood: a
smooth bump function, normalized by its integral. Such functions are the building blocks of
smooth approximate identities.

## Main results

* `TauCeti.exists_contMDiff_nonneg_tsupport_subset_integral_eq_one`: every neighbourhood of a
  point carries a nonnegative smooth compactly supported function of unit integral.
-/

public section

open MeasureTheory Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [MeasurableSpace M]

variable (I : ModelWithCorners ℝ E H) in
/-- **Smooth peak functions exist.** On a manifold modelled on a finite-dimensional space, with a
measure positive on nonempty open sets and finite on compact sets, every neighbourhood `U` of a
point carries a nonnegative smooth compactly supported function of unit integral whose support
closure lies in `U`: a smooth bump function, normalized by its integral. -/
theorem exists_contMDiff_nonneg_tsupport_subset_integral_eq_one [FiniteDimensional ℝ E]
    [T2Space M] [IsManifold I ∞ M] [OpensMeasurableSpace M] (μ : Measure M)
    [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ] {x₀ : M} {U : Set M} (hU : U ∈ 𝓝 x₀) :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ f ∧ HasCompactSupport f ∧ 0 ≤ f ∧ tsupport f ⊆ U ∧
      ∫ x, f x ∂μ = 1 := by
  obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x₀).mem_iff.1 hU
  have hpos : 0 < ∫ x, b x ∂μ :=
    b.contMDiff.continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero b.hasCompactSupport
      (fun _ ↦ b.nonneg) (x := x₀) (by simp)
  refine ⟨fun x ↦ (∫ x, b x ∂μ)⁻¹ * b x,
    (contDiff_const_smul (∫ x, b x ∂μ)⁻¹).contMDiff.comp b.contMDiff,
    b.hasCompactSupport.mul_left, fun x ↦ mul_nonneg (inv_nonneg.2 hpos.le) b.nonneg,
    tsupport_mul_subset_right.trans hb, ?_⟩
  rw [integral_const_mul, inv_mul_cancel₀ hpos.ne']

end TauCeti
