/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Density.Regularity
import TauCeti.Geometry.Manifold.ExtChartAt.Integral
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

namespace RoughDensity

/-- If `μ` is nonnegative on every tangent basis, then its chart coefficient `μ.inChartAt b α`
is nonnegative everywhere. -/
theorem inChartAt_nonneg {μ : RoughDensity I M m}
    (hμ : ∀ x (c : Basis (Fin m) ℝ (TangentSpace I x)), 0 ≤ μ x c)
    (b : Basis (Fin m) ℝ E) (α : M) (y : E) : 0 ≤ μ.inChartAt b α y := by
  by_cases hy : y ∈ (extChartAt I α).target
  · rw [μ.inChartAt_of_mem_target b α hy]
    -- `TangentSpace I ((extChartAt I α).symm y)` is definitionally `E`, so `b` gives a tangent
    -- basis via `tangentSpaceCastModel` to evaluate `apply_eq_abs_det_mul`.
    let c : Basis (Fin m) ℝ (TangentSpace I ((extChartAt I α).symm y)) :=
      b.map (tangentSpaceCastModel I ((extChartAt I α).symm y)).symm.toLinearEquiv
    rw [(μ ((extChartAt I α).symm y)).apply_eq_abs_det_mul c
      (fun i ↦ mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) y (b i))]
    exact mul_nonneg (abs_nonneg _) (hμ _ c)
  · rw [μ.inChartAt_of_notMem_target b α hy]

end RoughDensity

/-- Mapping a model basis along `(tangentSpaceCastModel I x).symm` preserves its underlying
function into `TangentSpace I x`. -/
private theorem coe_map_tangentSpaceCastModel_symm (x : M) (b : Basis (Fin m) ℝ E) :
    (⇑(b.map (tangentSpaceCastModel I x).symm.toLinearEquiv) : Fin m → TangentSpace I x) =
      (⇑b : Fin m → E) :=
  rfl

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
  let α' : Fin (c.n + 1) → M := Fin.cons x₀ c.center
  let u' : Fin (c.n + 1) → Set M := Fin.cons (extChartAt I x₀).source c.domain
  have hu' : ∀ i, IsChartMeasurable I (u' i) := Fin.cases
    (isOpen_extChartAt_source (I := I) x₀).isChartMeasurable
    fun i ↦ (c.isOpen_domain i).isChartMeasurable
  have hs' : ∀ i, u' i ⊆ (extChartAt I (α' i)).source := Fin.cases Subset.rfl c.domain_subset
  have hc' : {x | μ x ≠ 0} ⊆ ⋃ i, u' i := fun x hx ↦
    let ⟨i, hi⟩ := mem_iUnion.mp (c.covers (subset_closure hx))
    mem_iUnion.mpr ⟨i.succ, hi⟩
  rw [integralDensity_eq_sum_disjointed_chart_integrals hi b₀ α' u' hu' hs' hc',
    Fin.sum_univ_succ]
  refine add_pos_of_pos_of_nonneg ?_ (Finset.sum_nonneg fun i _ ↦
    integral_nonneg fun y ↦ RoughDensity.inChartAt_nonneg hnn b₀ (α' i.succ) y)
  have hpiece : (extChartAt I (α' 0)) '' disjointed u' 0 = (extChartAt I x₀).target := by
    rw [← bot_eq_zero, disjointed_bot, bot_eq_zero]
    simp only [α', u', Fin.cons_zero]
    exact (extChartAt I x₀).image_source_eq_target
  have hg₀ : 0 < μ.inChartAt b₀ x₀ (extChartAt I x₀ x₀) := by
    rw [μ.inChartAt_self b₀ x₀]
    let b₀' : Basis (Fin m) ℝ (TangentSpace I x₀) :=
      b₀.map (tangentSpaceCastModel I x₀).symm.toLinearEquiv
    rw [← coe_map_tangentSpaceCastModel_symm x₀ b₀, (μ x₀).apply_eq_abs_det_mul c₀ b₀']
    exact mul_pos (abs_pos.mpr (c₀.isUnit_det b₀').ne_zero) hpos
  rw [hpiece]
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
