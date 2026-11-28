/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Density.Regularity
import TauCeti.MeasureTheory.Measure.Haar.OfBasis

/-!
# Positivity and monotonicity of density integration

Proves nonnegativity (`TauCeti.integralDensity_nonneg`), monotonicity
(`TauCeti.integralDensity_mono`), and strict positivity (`TauCeti.integralDensity_pos`,
`TauCeti.integralDensity_pos_of_continuousOn_inChartAt`) for `TauCeti.integralDensity`, in all
dimensions including manifolds with boundary or corners and zero-dimensional manifolds.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16,
  Proposition 16.42.
-/

public section

noncomputable section

open Bundle MeasureTheory Set Module
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {m : ℕ}

/-- **Nonnegativity of density integration.** A rough density nonnegative on every tangent basis
has nonnegative integral, in every dimension `m : ℕ` (no regularity, support, or orientation). -/
theorem integralDensity_nonneg [IsManifold I 1 M] {μ : RoughDensity I M m}
    (hμ : ∀ x (c : Basis (Fin m) ℝ (TangentSpace I x)), 0 ≤ μ x c) : 0 ≤ integralDensity μ := by
  by_cases hi : IntegrableDensity μ
  swap
  · rw [integralDensity_eq_zero_of_not_integrable hi]
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  obtain ⟨b⟩ := hi.nonempty_basis
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let : LocallyCompactSpace H := I.locallyCompactSpace
  rw [integralDensity_eq_sum_chooseChartCover hi b]
  exact Finset.sum_nonneg fun _ _ ↦
    integral_nonneg fun y ↦ RoughDensity.inChartAt_nonneg hμ b _ y

/-- Pointwise dominance on tangent bases implies monotonicity of `integralDensity` in all
dimensions. -/
theorem integralDensity_mono [IsManifold I 1 M] {μ ν : RoughDensity I M m}
    (hμ : IntegrableDensity μ) (hν : IntegrableDensity ν)
    (hle : ∀ x (c : Basis (Fin m) ℝ (TangentSpace I x)), μ x c ≤ ν x c) :
    integralDensity μ ≤ integralDensity ν := by
  rw [← sub_nonneg, ← integralDensity_sub hν hμ]
  exact integralDensity_nonneg fun x c ↦ sub_nonneg.mpr (hle x c)

/-- **Strict positivity of density integration.** An integrable rough density nonnegative on every
tangent basis, positive on one at `x₀`, and continuous in one basis on `(extChartAt I x₀).target`
satisfies `0 < integralDensity μ`. -/
theorem integralDensity_pos_of_continuousOn_inChartAt [IsManifold I 1 M]
    {μ : RoughDensity I M m} (hi : IntegrableDensity μ)
    (hnn : ∀ x (c : Basis (Fin m) ℝ (TangentSpace I x)), 0 ≤ μ x c)
    {x₀ : M} {b₀ : Basis (Fin m) ℝ E}
    (hcont : ContinuousOn (μ.inChartAt b₀ x₀) (extChartAt I x₀).target)
    {c₀ : Basis (Fin m) ℝ (TangentSpace I x₀)} (hpos : 0 < μ x₀ c₀) : 0 < integralDensity μ := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b₀
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let c := chooseChartCover (I := I) (_root_.tsupport (α := Density E m) μ) hi.isCompact
  rw [integralDensity_eq_sum_disjointed_chart_integrals hi b₀ (c.cons x₀).center (c.cons x₀).domain
    (fun i ↦ ((c.cons x₀).isOpen_domain i).isChartMeasurable) (c.cons x₀).domain_subset
    (fun x hx ↦ (c.cons x₀).covers (subset_closure hx)), Fin.sum_univ_succ]
  refine add_pos_of_pos_of_nonneg ?_ (Finset.sum_nonneg fun i _ ↦
    integral_nonneg fun y ↦ RoughDensity.inChartAt_nonneg hnn b₀ ((c.cons x₀).center i.succ) y)
  rw [← ChartCover.piece_def, ChartCover.image_extChartAt_piece_cons_zero,
    ChartCover.cons_center_zero]
  have hg₀ : 0 < μ.inChartAt b₀ x₀ (extChartAt I x₀ x₀) := by
    rw [μ.inChartAt_self b₀ x₀, (μ x₀).apply_eq_abs_det_mul c₀ b₀]
    exact mul_pos (abs_pos.mpr (c₀.is_basis_iff_det.mp
      ⟨b₀.linearIndependent, b₀.span_eq⟩).ne_zero) hpos
  exact setIntegral_pos_of_nonneg_of_pos_at_extChartAt_target (μ := b₀.addHaar) x₀
    (RoughDensity.inChartAt_nonneg hnn b₀ x₀)
    (hi.integrable_inChartAt b₀ x₀).integrableOn
    hcont (mem_extChartAt_target x₀) hg₀

/-- **Strict positivity for continuous density sections** [Lee, Prop. 16.42(b)]: a compactly
supported continuous section nonnegative everywhere and positive at some point satisfies
`0 < integralDensity μ`. -/
theorem integralDensity_pos [FiniteDimensional ℝ E] [IsManifold I 1 M]
    {μ : (x : M) → DensityBundle I M x} (hμ : Continuous fun x ↦ TotalSpace.mk' ℝ x (μ x))
    (hc : IsCompact (_root_.tsupport (α := Density E (finrank ℝ E)) μ))
    (hnn : ∀ x (c : Basis (Fin (finrank ℝ E)) ℝ (TangentSpace I x)), 0 ≤ μ x c)
    (hpos : ∃ x, ∃ c : Basis (Fin (finrank ℝ E)) ℝ (TangentSpace I x), 0 < μ x c) :
    0 < integralDensity μ :=
  let ⟨_, _, hc₀⟩ := hpos
  integralDensity_pos_of_continuousOn_inChartAt
    (RoughDensity.integrableDensity_of_continuous_section hμ hc) hnn
    (RoughDensity.continuousOn_inChartAt_of_continuousOn_section (finBasis ℝ E) hμ.continuousOn)
    hc₀

end TauCeti
