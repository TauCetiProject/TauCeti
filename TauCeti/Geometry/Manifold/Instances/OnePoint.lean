/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# The projective line `OnePoint 𝕜` as an analytic manifold

For a nontrivially normed field `𝕜` whose closed balls are compact (`ProperSpace 𝕜`, as for `ℝ`,
`ℂ` and `ℚ_[p]`), the one-point compactification `OnePoint 𝕜 = 𝕜 ∪ {∞}` is the projective line
over `𝕜`. This file charts it by the two classical coordinates: the affine coordinate
`OnePoint.affineChart`, which reads a finite point `z` as `z` and is defined off `∞`, and the
inverted coordinate `OnePoint.invChart`, which reads a point `z` as `z⁻¹` and `∞` as `0` and is
defined off `0`. Their transition map is `z ↦ z⁻¹` on `𝕜ˣ`, which is analytic, so these two charts
make `OnePoint 𝕜` a one-dimensional analytic manifold over `𝕜`
(`OnePoint.instIsManifold`). Properness is what makes the inverted chart
continuous at `∞`: neighbourhoods of `∞` are complements of compact sets, and these must contain
the complements of balls.

For `𝕜 = ℂ` this is the Riemann sphere. Mathlib already shows that `OnePoint ℂ` is compact,
Hausdorff and connected, so it is a compact connected Riemann surface, the target of meromorphic
functions regarded as holomorphic maps. Differentiability (for `𝕜 = ℂ`, holomorphy) of a map into
`OnePoint 𝕜` is tested in the two charts. At a point sent to a finite value it is continuity
together with differentiability in the affine chart
(`OnePoint.mdifferentiableAt_iff_of_ne_infty`); for a map that only takes finite values this is
differentiability of the `𝕜`-valued map (`OnePoint.mdifferentiableAt_coe_comp_iff`). At a point
sent to `∞` it is continuity together with differentiability of the reciprocal, read in the
inverted chart (`OnePoint.mdifferentiableAt_iff_of_eq_infty`).

## Main declarations

* `OnePoint.affineChart` and `OnePoint.invChart`: the two charts of `OnePoint 𝕜`.
* `OnePoint.instChartedSpace`: the charted space structure, with preferred charts
  `OnePoint.chartAt_coe` and `OnePoint.chartAt_infty`.
* `OnePoint.instIsManifold`: the analytic manifold structure.
* `OnePoint.contMDiff_coe`: the inclusion `𝕜 → OnePoint 𝕜` is analytic.
* `OnePoint.mdifferentiableAt_iff_of_ne_infty`, `OnePoint.mdifferentiableAt_iff_of_eq_infty`
  and `OnePoint.mdifferentiableAt_coe_comp_iff`: differentiability of maps into `OnePoint 𝕜`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §1.5 (c).
-/

public noncomputable section

open Filter Function Set Topology

open scoped ContDiff Manifold

namespace OnePoint

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-! ### The affine chart -/

/-- The **affine chart** of the projective line `OnePoint 𝕜`: it reads a finite point `z` as `z`,
and is defined on the complement of `∞`, with target all of `𝕜`. Its inverse is the inclusion
`𝕜 → OnePoint 𝕜` (`OnePoint.affineChart_symm_apply`). -/
def affineChart : OpenPartialHomeomorph (OnePoint 𝕜) 𝕜 where
  toFun x := x.elim 0 id
  invFun z := z
  source := {(∞ : OnePoint 𝕜)}ᶜ
  target := univ
  map_source' _ _ := mem_univ _
  map_target' z _ := coe_ne_infty z
  left_inv' x hx := by
    induction x using OnePoint.rec with
    | infty => exact absurd rfl hx
    | coe z => rfl
  right_inv' _ _ := rfl
  open_source := isClosed_infty.isOpen_compl
  open_target := isOpen_univ
  continuousOn_toFun := by
    refine isClosed_infty.isOpen_compl.continuousOn_iff.2 fun x hx ↦ ?_
    induction x using OnePoint.rec with
    | infty => exact absurd rfl hx
    | coe z => exact continuousAt_coe.2 continuousAt_id
  continuousOn_invFun := continuous_coe.continuousOn

@[simp]
theorem affineChart_source : (affineChart : OpenPartialHomeomorph (OnePoint 𝕜) 𝕜).source =
    {(∞ : OnePoint 𝕜)}ᶜ :=
  (rfl)

@[simp]
theorem affineChart_target : (affineChart : OpenPartialHomeomorph (OnePoint 𝕜) 𝕜).target = univ :=
  (rfl)

@[simp]
theorem affineChart_coe (z : 𝕜) : affineChart (z : OnePoint 𝕜) = z :=
  (rfl)

@[simp]
theorem affineChart_infty : affineChart (∞ : OnePoint 𝕜) = 0 :=
  (rfl)

@[simp]
theorem affineChart_symm_apply (z : 𝕜) : affineChart.symm z = (z : OnePoint 𝕜) :=
  (rfl)

/-! ### The inverted chart -/

section Proper

variable [ProperSpace 𝕜]

open scoped Classical in
/-- The **inverted chart** of the projective line `OnePoint 𝕜`: it reads a point `z` as `z⁻¹` and
`∞` as `0`, and is defined on the complement of `0`, with target all of `𝕜`. Its inverse sends
`0` to `∞` and `w ≠ 0` to `w⁻¹` (`OnePoint.invChart_symm_zero` and
`OnePoint.invChart_symm_of_ne_zero`). -/
def invChart : OpenPartialHomeomorph (OnePoint 𝕜) 𝕜 where
  toFun x := x.elim 0 (·⁻¹)
  invFun w := if w = 0 then ∞ else ((w⁻¹ : 𝕜) : OnePoint 𝕜)
  source := {((0 : 𝕜) : OnePoint 𝕜)}ᶜ
  target := univ
  map_source' _ _ := mem_univ _
  map_target' w _ := by
    split_ifs with hw
    · exact infty_ne_coe 0
    · exact fun h ↦ inv_ne_zero hw (coe_injective h)
  left_inv' x hx := by
    induction x using OnePoint.rec with
    | infty => simp
    | coe z =>
      have hz : z ≠ 0 := fun h ↦ hx (congrArg _ h)
      simp [hz]
  right_inv' w _ := by
    by_cases hw : w = 0 <;> simp [hw]
  open_source := isOpen_compl_singleton
  open_target := isOpen_univ
  continuousOn_toFun := by
    refine isOpen_compl_singleton.continuousOn_iff.2 fun x hx ↦ ?_
    induction x using OnePoint.rec with
    | infty =>
      -- Near `∞` the chart is `z ↦ z⁻¹` on the complements of compact, that is bounded, sets.
      refine continuousAt_infty'.2 ?_
      rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_cobounded
    | coe z =>
      have hz : z ≠ 0 := fun h ↦ hx (congrArg _ h)
      exact continuousAt_coe.2 (continuousAt_inv₀ hz)
  continuousOn_invFun := by
    refine continuousOn_univ.2 (continuous_iff_continuousAt.2 fun w ↦ ?_)
    rcases eq_or_ne w 0 with rfl | hw
    · -- Near `0` the inverse is `w ↦ w⁻¹`, which tends to infinity.
      rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
      simp only [↓reduceIte]
      have h : Tendsto (fun v : 𝕜 ↦ ((v⁻¹ : 𝕜) : OnePoint 𝕜)) (𝓝[≠] 0)
          (𝓝 (∞ : OnePoint 𝕜)) := by
        refine tendsto_coe_infty.comp ?_
        rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
        exact tendsto_inv₀_nhdsNE_zero
      refine h.congr' (eventually_nhdsWithin_of_forall fun v hv ↦ ?_)
      simp [show v ≠ 0 from hv]
    · refine (continuous_coe.continuousAt.comp (continuousAt_inv₀ hw)).congr ?_
      filter_upwards [isOpen_ne.mem_nhds hw] with v hv
      simp [hv]

@[simp]
theorem invChart_source :
    (invChart : OpenPartialHomeomorph (OnePoint 𝕜) 𝕜).source = {((0 : 𝕜) : OnePoint 𝕜)}ᶜ :=
  (rfl)

@[simp]
theorem invChart_target : (invChart : OpenPartialHomeomorph (OnePoint 𝕜) 𝕜).target = univ :=
  (rfl)

@[simp]
theorem invChart_coe (z : 𝕜) : invChart (z : OnePoint 𝕜) = z⁻¹ :=
  (rfl)

@[simp]
theorem invChart_infty : invChart (∞ : OnePoint 𝕜) = 0 :=
  (rfl)

@[simp]
theorem invChart_symm_zero : invChart.symm (0 : 𝕜) = (∞ : OnePoint 𝕜) := by
  simp [invChart]

@[simp]
theorem invChart_symm_of_ne_zero {w : 𝕜} (hw : w ≠ 0) :
    invChart.symm w = ((w⁻¹ : 𝕜) : OnePoint 𝕜) := by
  simp [invChart, hw]

/-! ### The charted space -/

/-- The projective line `OnePoint 𝕜` as a charted space modelled on `𝕜`: its atlas consists of the
affine chart and the inverted chart, the preferred chart at a finite point being the affine chart
(`OnePoint.chartAt_coe`) and the preferred chart at `∞` the inverted chart
(`OnePoint.chartAt_infty`). -/
instance instChartedSpace : ChartedSpace 𝕜 (OnePoint 𝕜) where
  atlas := {affineChart, invChart}
  chartAt x := x.elim invChart fun _ ↦ affineChart
  mem_chart_source x := by
    induction x using OnePoint.rec with
    | infty => exact infty_ne_coe 0
    | coe z => exact coe_ne_infty z
  chart_mem_atlas x := by
    induction x using OnePoint.rec with
    | infty => exact Or.inr rfl
    | coe z => exact Or.inl rfl

@[simp]
theorem chartAt_coe (z : 𝕜) : chartAt 𝕜 (z : OnePoint 𝕜) = affineChart :=
  (rfl)

@[simp]
theorem chartAt_infty : chartAt 𝕜 (∞ : OnePoint 𝕜) = invChart :=
  (rfl)

theorem mem_atlas_iff {e : OpenPartialHomeomorph (OnePoint 𝕜) 𝕜} :
    e ∈ atlas 𝕜 (OnePoint 𝕜) ↔ e = affineChart ∨ e = invChart :=
  Iff.rfl

/-! ### The analytic structure -/

/-- **The projective line is an analytic manifold.** The transition maps between the affine and
inverted charts are `z ↦ z⁻¹` on `𝕜ˣ`, which is analytic. For `𝕜 = ℂ` this makes the Riemann
sphere `OnePoint ℂ` a Riemann surface. -/
instance instIsManifold : IsManifold 𝓘(𝕜) ω (OnePoint 𝕜) := by
  refine isManifold_of_contDiffOn 𝓘(𝕜) ω _ fun e e' he he' ↦ ?_
  simp only [mfld_simps]
  have hself (c : OpenPartialHomeomorph (OnePoint 𝕜) 𝕜) :
      ContDiffOn 𝕜 ω (c ∘ c.symm) (c.target ∩ c.symm ⁻¹' c.source) :=
    contDiffOn_id.congr fun u hu ↦ c.right_inv hu.1
  rcases he with rfl | rfl <;> rcases he' with rfl | rfl
  · exact hself _
  · -- From the affine chart to the inverted chart: `z ↦ z⁻¹` away from `0`.
    refine ((contDiffOn_inv 𝕜).mono fun u hu h ↦ hu.2 (congrArg _ h)).congr fun u _ ↦ ?_
    simp
  · -- From the inverted chart to the affine chart: `w ↦ w⁻¹` away from `0`.
    have hsub : invChart.target ∩ invChart.symm ⁻¹' affineChart.source ⊆ ({0}ᶜ : Set 𝕜) := by
      rintro w ⟨-, hw⟩ (rfl : w = 0)
      exact hw (invChart_symm_zero (𝕜 := 𝕜))
    refine ((contDiffOn_inv 𝕜).mono hsub).congr fun w hw ↦ ?_
    simp [invChart_symm_of_ne_zero (hsub hw)]
  · exact hself _

/-! ### Differentiable maps into the projective line

For `𝕜 = ℂ`, differentiability of a map into `OnePoint ℂ` is holomorphy into the Riemann sphere.
-/

/-- The inclusion `𝕜 → OnePoint 𝕜` is analytic: it is the inverse of the affine chart. -/
theorem contMDiff_coe : ContMDiff 𝓘(𝕜) 𝓘(𝕜) ω ((↑) : 𝕜 → OnePoint 𝕜) := by
  have h := contMDiffOn_chart_symm (I := 𝓘(𝕜)) (n := ω) (x := ((0 : 𝕜) : OnePoint 𝕜))
  have hsymm : ⇑(affineChart.symm : OpenPartialHomeomorph 𝕜 (OnePoint 𝕜)) = (↑) :=
    funext affineChart_symm_apply
  rwa [chartAt_coe, affineChart_target, contMDiffOn_univ, hsymm] at h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A map into `𝕜`, regarded as a map into the projective line `OnePoint 𝕜`, is differentiable at
a point exactly when it is differentiable there as a `𝕜`-valued map. -/
theorem mdifferentiableAt_coe_comp_iff {g : M → 𝕜} {x : M} :
    MDifferentiableAt I 𝓘(𝕜) (fun y ↦ (g y : OnePoint 𝕜)) x ↔ MDifferentiableAt I 𝓘(𝕜) g x := by
  refine ⟨fun h ↦ ?_, fun h ↦ ((contMDiff_coe (g x)).mdifferentiableAt (by simp)).comp x h⟩
  -- Read the map in the affine chart, which is analytic off `∞`.
  have hc : MDifferentiableAt 𝓘(𝕜) 𝓘(𝕜) (affineChart : OnePoint 𝕜 → 𝕜) (g x) :=
    mdifferentiableAt_atlas (Or.inl rfl) (coe_ne_infty _)
  simpa [Function.comp_def] using hc.comp x h

/-- A map into the projective line `OnePoint 𝕜` is differentiable at a point sent to a finite
value exactly when it is continuous there and differentiable there when read in the affine
chart. -/
theorem mdifferentiableAt_iff_of_ne_infty {f : M → OnePoint 𝕜} {x : M}
    (hx : f x ≠ (∞ : OnePoint 𝕜)) :
    MDifferentiableAt I 𝓘(𝕜) f x ↔
      ContinuousAt f x ∧ MDifferentiableAt I 𝓘(𝕜) (affineChart ∘ f) x := by
  obtain ⟨z, hz⟩ := ne_infty_iff_exists.1 hx
  rw [mdifferentiableAt_iff_target, ← hz]
  simp only [mfld_simps, chartAt_coe]

/-- A map into the projective line `OnePoint 𝕜` is differentiable at a point sent to `∞` exactly
when it is continuous there and differentiable there when read in the inverted chart, that is,
when its reciprocal is differentiable there. -/
theorem mdifferentiableAt_iff_of_eq_infty {f : M → OnePoint 𝕜} {x : M}
    (hx : f x = (∞ : OnePoint 𝕜)) :
    MDifferentiableAt I 𝓘(𝕜) f x ↔
      ContinuousAt f x ∧ MDifferentiableAt I 𝓘(𝕜) (invChart ∘ f) x := by
  rw [mdifferentiableAt_iff_target, hx]
  simp only [mfld_simps, chartAt_infty]

end Proper

end OnePoint
