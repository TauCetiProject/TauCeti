/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.IntegrableOn
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory

/-!
# Functions continuous on a compact set are essentially bounded

A function continuous on a compact set `K` is bounded there, so it lies in `L^∞(μ.restrict s)` for
every measurable `s ⊆ K` (`ContinuousOn.memLp_top_restrict_of_subset_isCompact`). Allowing `s ⊊ K`
covers the usual case of an open interval `(a, b)` inside the compact interval `[a, b]`. This is the
continuous counterpart of Mathlib's `MonotoneOn.memLp_top`, and the restricted-measure counterpart
of `Continuous.memLp_top_of_hasCompactSupport`.

The same bound controls a pointwise composition `x ↦ A x ∘L B x` of operator families with `A`
continuous on `K`: `A ∘L B` lies in `Lᵖ(s)` whenever `B` does
(`MeasureTheory.MemLp.clm_comp_of_continuousOn`, Hölder's inequality
`ContinuousLinearMap.memLp_of_bilin` for `ContinuousLinearMap.compL` with exponents `(∞, p, p)`).

A bounded weakly measurable family of bilinear forms `A x` evaluated along such a function,
`x ↦ A x (φ x) (φ x)`, is integrable on `s` when `μ.restrict s` is finite
(`MeasureTheory.integrable_apply_apply_of_continuousOn`).

On a compact space with a measure that is finite on compact sets, every continuous function lies in
every `Lᵖ`, so for a finite exponent `p ≠ 0` its `Lᵖ` seminorm is the integral
`(∫ ‖f‖ ^ p dμ) ^ (1 / p)` (`Continuous.eLpNorm_eq_integral_rpow_norm`).
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

variable {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [SeminormedAddGroup E]

/-- A function continuous on a compact set `K` is essentially bounded on every measurable
`s ⊆ K`. -/
theorem ContinuousOn.memLp_top_restrict_of_subset_isCompact {f : X → E} {K s : Set X}
    {μ : Measure X}
    (hf : ContinuousOn f K) (hK : IsCompact K) (hs : MeasurableSet s) (hsK : s ⊆ K) :
    MemLp f ∞ (μ.restrict s) := by
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn (continuous_nnNorm.comp_continuousOn hf)).bddAbove
  refine memLp_top_of_bound_eNorm (hf.aestronglyMeasurable_of_subset_isCompact hK hs hsK) C ?_
  filter_upwards [ae_restrict_mem hs] with x hx using eNorm_le_coe.2 <| hC ⟨x, hsK hx, rfl⟩

section CLMComp

variable {𝕜 F G H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {A : X → G →L[𝕜] H} {B : X → F →L[𝕜] G} {K s : Set X} {μ : Measure X}

/-- **Composing an `Lᵖ` operator family with a continuous one.** If `A` is continuous on a compact
set `K` and `B` is in `Lᵖ` on a measurable `s ⊆ K`, then so is `A ∘L B`. -/
theorem MeasureTheory.MemLp.clm_comp_of_continuousOn {p : ℝ≥0∞} (hB : MemLp B p (μ.restrict s))
    (hA : ContinuousOn A K) (hK : IsCompact K) (hs : MeasurableSet s) (hsK : s ⊆ K) :
    MemLp (fun x => (A x).comp (B x)) p (μ.restrict s) :=
  (ContinuousLinearMap.compL 𝕜 F G H).memLp_of_bilin p
    (hA.memLp_top_restrict_of_subset_isCompact hK hs hsK) hB

end CLMComp

section ApplyApply

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {A : X → V →L[ℝ] StrongDual ℝ V}
  {Λ : ℝ} {φ : X → V} {K s : Set X} {μ : Measure X}

/-- **Integrability of `x ↦ A x (φ x) (φ x)`.** If `A` is a weakly measurable family of bilinear
forms bounded by `Λ` almost everywhere on a measurable `s ⊆ K`, `φ` is continuous on a compact set
`K` and `μ.restrict s` is finite, then `x ↦ A x (φ x) (φ x)` is integrable on `s`. -/
theorem MeasureTheory.integrable_apply_apply_of_continuousOn [IsFiniteMeasure (μ.restrict s)]
    (hA : ∀ u v, AEStronglyMeasurable (fun x => A x u v) (μ.restrict s))
    (hA_bound : ∀ᵐ x ∂μ.restrict s, ‖A x‖ ≤ Λ) (hφ : ContinuousOn φ K) (hK : IsCompact K)
    (hs : MeasurableSet s) (hsK : s ⊆ K) :
    Integrable (fun x => A x (φ x) (φ x)) (μ.restrict s) := by
  set C := lpNorm φ ∞ (μ.restrict s)
  have hC : ∀ᵐ x ∂μ.restrict s, ‖φ x‖ ≤ C :=
    ae_le_lpNorm_exponent_top (hφ.memLp_top_restrict_of_subset_isCompact hK hs hsK)
  have hφm : AEStronglyMeasurable φ (μ.restrict s) :=
    hφ.aestronglyMeasurable_of_subset_isCompact hK hs hsK
  refine (MemLp.of_bound ((hφm.prodMk hφm).apply_of_forall_of_continuousAt
      (g := fun x p => A x p.1 p.2) (fun p => hA p.1 p.2)
      (ae_of_all _ fun x => (A x).continuous₂.continuousAt))
    (Λ * C * C) ?_).integrable le_rfl
  filter_upwards [hA_bound, hC] with x hAx hφx
  have hΛ : 0 ≤ Λ := (norm_nonneg (A x)).trans hAx
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hφx
  calc ‖A x (φ x) (φ x)‖ ≤ ‖A x‖ * ‖φ x‖ * ‖φ x‖ := (A x).le_opNorm₂ _ _
    _ ≤ Λ * C * C := by gcongr

end ApplyApply

/-- The `Lᵖ` seminorm of a continuous function on a compact space, for a finite exponent `p ≠ 0`
and a measure finite on compact sets, as an integral: `‖f‖_{Lᵖ} = (∫ ‖f‖ ^ p dμ) ^ (1 / p)`. -/
theorem Continuous.eLpNorm_eq_integral_rpow_norm {F : Type*} [NormedAddCommGroup F]
    [CompactSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {f : X → F} (hf : Continuous f)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) :
    eLpNorm f p μ = ENNReal.ofReal ((∫ x, ‖f x‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹) :=
  (hf.memLp_of_hasCompactSupport (.of_compactSpace f)).eLpNorm_eq_integral_rpow_norm hp0 hpt
