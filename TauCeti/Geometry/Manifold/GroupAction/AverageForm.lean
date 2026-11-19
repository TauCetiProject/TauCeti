/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.MeasureTheory.Group.Integral
public import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import Mathlib.Analysis.Calculus.ParametricIntegral
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart

/-!
# Averaging differential forms over a compact group action

Let a group `G` act on a manifold `M`, and let `μ` be a measure on `G`. The **average** of a
differential form `α` on `M` is the form

`(avg α)_x = ∫ (a^* α)_x dμ(a)`,  that is,  `(avg α)_x(v) = ∫ α_(a • x)(d(a •)_x v) dμ(a)`

(`TauCeti.measureAverageForm μ α`). It is the basic tool for producing invariant forms from
arbitrary ones, for instance invariant symplectic forms and invariant primitives near an orbit of a
compact symmetry group.

When `G` is a compact manifold acting smoothly on a boundaryless manifold `M` and `μ` is a finite
measure, the average has the expected calculus:

* In the chart at `x₀`, the chart expressions of the pullbacks `(a •)^* α` are jointly `C^m` in
  the chart coordinate and in `a` when `α` is `C^m` and the action is `C^(m+1)`
  (`TauCeti.contMDiffAt_inChartAt_mpullback_smul`). The chart expression of the average is the
  average of these chart expressions (`TauCeti.inChartAt_measureAverageForm`), so differentiation
  under the integral over the compact parameter space `G` shows that the average is again `C^m`
  (`TauCeti.IsSmoothForm.measureAverageForm`).
* For a `C¹` form and a `C²` action, the derivative of the chart expression of the average is the
  average of the derivatives (`TauCeti.hasFDerivAt_inChartAt_measureAverageForm`). As pullback
  commutes with the exterior derivative, **averaging commutes with the exterior derivative**,
  `d (avg α) = avg (d α)` (`TauCeti.mextDeriv_measureAverageForm`). In particular the average of a
  closed form is closed.
* For a right-invariant measure, such as the normalized Haar measure `TauCeti.haarProb` of a compact
  group, the average is invariant: `g^* (avg α) = avg α` for every `g`
  (`TauCeti.mpullback_smul_measureAverageForm`). For a probability measure averaging fixes every
  invariant form (`TauCeti.measureAverageForm_eq_self`), so it fixes exactly the invariant forms
  (`TauCeti.measureAverageForm_eq_self_iff`).
* Averaging preserves vanishing along a set `s` invariant under the action
  (`TauCeti.measureAverageForm_apply_eq_zero`), and, for a `C¹` form and a `C²` action, it also
  preserves zero first jets along `s`: if `α` vanishes at the points of `s` and its chart
  expressions have zero derivative there, the same holds for the average
  (`TauCeti.hasFDerivAt_inChartAt_measureAverageForm_of_apply_eq_zero`).

The group need not be connected, and no Lie group structure is used: `G` is a compact Hausdorff
manifold on which `G` acts jointly smoothly. The manifold `M` is boundaryless, so that its chart
targets are open; it need not be finite-dimensional.

## Main definitions

* `TauCeti.measureAverageForm μ α`: the average of `α` over the measure `μ`.

## Main results

* `TauCeti.IsSmoothForm.measureAverageForm`: the average of a `C^m` form over a `C^(m+1)` action
  of a compact group is `C^m`.
* `TauCeti.mextDeriv_measureAverageForm`: averaging commutes with the exterior derivative.
* `TauCeti.mpullback_smul_measureAverageForm`: for a right-invariant measure the average is
  invariant.
* `TauCeti.measureAverageForm_eq_self_iff`: for a right-invariant probability measure, averaging
  fixes exactly the invariant forms.
* `TauCeti.measureAverageForm_apply_eq_zero`,
  `TauCeti.hasFDerivAt_inChartAt_measureAverageForm_of_apply_eq_zero`: averaging preserves
  vanishing and zero first jets along invariant sets.

## References

* G. E. Bredon, *Introduction to Compact Transformation Groups*, Academic Press (1972),
  Chapter VI (averaging over compact transformation groups).
* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 14 (pullback and exterior derivative).
-/

public section

noncomputable section

open Bundle Set Filter Function MeasureTheory
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {G : Type*} [Group G] [MulAction G M] [MeasurableSpace G]

variable (μ : Measure G) in
/-- The average of a form `α` over a measure `μ` on a group acting on `M`: the form
`x ↦ ∫ (a^* α)_x dμ(a)` obtained by integrating the pullbacks of `α` by the action of the group
elements. Its value at `x` on tangent vectors `v` is `∫ α_(a • x)(d(a •)_x v) dμ(a)`
(`TauCeti.measureAverageForm_apply`). -/
def measureAverageForm (α : RoughForm I M F k) : RoughForm I M F k :=
  fun x ↦ integral (G := E [⋀^Fin k]→L[ℝ] F) μ fun a ↦ mpullback I I (a • ·) α x

variable (μ : Measure G)

theorem measureAverageForm_def (α : RoughForm I M F k) (x : M) :
    measureAverageForm μ α x =
      integral (G := E [⋀^Fin k]→L[ℝ] F) μ fun a ↦ mpullback I I (a • ·) α x := (rfl)

@[simp]
theorem measureAverageForm_zero :
    measureAverageForm μ (0 : RoughForm I M F k) = 0 := by
  funext x
  simp only [measureAverageForm_def, mpullback_zero]
  exact integral_zero G (E [⋀^Fin k]→L[ℝ] F)

@[simp]
theorem measureAverageForm_smul (c : ℝ) (α : RoughForm I M F k) :
    measureAverageForm μ (c • α) = c • measureAverageForm μ α := by
  funext x
  simp only [measureAverageForm_def, mpullback_smul]
  exact integral_smul (G := E [⋀^Fin k]→L[ℝ] F) c _

/-- The average of a form invariant under every group element, over a probability measure, is the
form itself. -/
theorem measureAverageForm_eq_self [CompleteSpace F] [IsProbabilityMeasure μ]
    {α : RoughForm I M F k} (hα : ∀ a : G, mpullback I I (a • ·) α = α) :
    measureAverageForm μ α = α := by
  funext x
  simp only [measureAverageForm_def, hα]
  exact (integral_const (E := E [⋀^Fin k]→L[ℝ] F) (α x)).trans
    (by rw [probReal_univ]; exact one_smul ℝ (α x))

/-- **Averaging preserves vanishing on invariant sets.** If `α` vanishes at every point of a set
`s` invariant under the action, then so does its average. -/
theorem measureAverageForm_apply_eq_zero {α : RoughForm I M F k} {s : Set M}
    (hs : ∀ a : G, ∀ x ∈ s, a • x ∈ s) (hα : ∀ x ∈ s, α x = 0) {x : M} (hx : x ∈ s) :
    measureAverageForm μ α x = 0 := by
  rw [measureAverageForm_def]
  exact integral_eq_zero_of_ae (G := E [⋀^Fin k]→L[ℝ] F)
    (Eventually.of_forall fun a ↦ mpullback_apply_eq_zero (hα _ (hs a x hx)))

section Chart

variable [I.Boundaryless] [IsManifold I 1 M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  (J : ModelWithCorners ℝ E' H') [TopologicalSpace G] [ChartedSpace H' G] [IsManifold J 1 G]

omit [MeasurableSpace G] in
/-- **Joint smoothness of the pulled-back forms.** For a `C^m` form `α` and a `C^n` action with
`m + 1 ≤ n`, the chart expressions at `x₀` of the pullbacks `(a •)^* α` are jointly `C^m` in the
chart coordinate and the group element. -/
theorem contMDiffAt_inChartAt_mpullback_smul {m n : WithTop ℕ∞} [IsManifold I n M]
    [ContMDiffSMul J I n G M] (hmn : m + 1 ≤ n) {α : RoughForm I M F k}
    (hα : IsSmoothForm I m α) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target) (a : G) :
    ContMDiffAt (𝓘(ℝ, E).prod J) 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F) m
      (fun p : E × G ↦ (mpullback I I (p.2 • ·) α).inChartAt x₀ p.1) (y, a) := by
  have hn : 1 ≤ n := le_trans le_add_self hmn
  have hsmul (b : G) : MDifferentiable I I (b • · : M → M) :=
    ((ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) b).of_le hn).mdifferentiable
      one_ne_zero
  have hT : IsOpen (extChartAt I x₀).target := isOpen_extChartAt_target x₀
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I n (extChartAt I x₀).symm y :=
    (contMDiffOn_extChartAt_symm x₀ y hy).contMDiffAt (hT.mem_nhds hy)
  -- The family `z ↦ p.2 • (extChartAt I x₀).symm z` is jointly smooth near `((y, a), y)`.
  have hf : ContMDiffAt ((𝓘(ℝ, E).prod J).prod 𝓘(ℝ, E)) I n
      (uncurry fun (p : E × G) (z : E) ↦ p.2 • (extChartAt I x₀).symm z) ((y, a), y) :=
    (contMDiffAt_snd.comp _ contMDiffAt_fst).smul (hsymm.comp _ contMDiffAt_snd)
  have hfam := ContMDiffAt.mpullback_form_family (I := 𝓘(ℝ, E)) (I' := I) (J := 𝓘(ℝ, E).prod J)
    (φ := α) (f := fun (p : E × G) (z : E) ↦ p.2 • (extChartAt I x₀).symm z) (g := Prod.fst)
    (p₀ := (y, a)) (hα.contMDiff _) hf contMDiffAt_fst hmn
  have hcoord := ((contMDiffAt_continuousAlternatingMap_bundle _).mp hfam).2
  refine hcoord.congr_of_eventuallyEq ?_
  filter_upwards [(hT.prod isOpen_univ).mem_nhds (mk_mem_prod hy (mem_univ a))] with p hp
  exact (RoughForm.inChartAt_mpullback_eq_mpullback_comp_symm α _ x₀ hp.1 (hsmul p.2 _)).trans
    (RoughForm.inCoordinates_modelSpace _ _ _).symm

end Chart

section Average

variable [I.Boundaryless] [IsManifold I 1 M] [CompleteSpace F]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  (J : ModelWithCorners ℝ E' H') [TopologicalSpace G] [ChartedSpace H' G] [IsManifold J 1 G]

omit [MeasurableSpace G] [CompleteSpace F] in
/-- The pullbacks of a continuous form by a `C¹` action depend continuously on the group
element. -/
theorem continuous_mpullback_smul [ContMDiffSMul J I 1 G M] {α : RoughForm I M F k}
    (hα : IsSmoothForm I 0 α) (x : M) :
    Continuous (Y := E [⋀^Fin k]→L[ℝ] F) fun a : G ↦ mpullback I I (a • ·) α x := by
  refine continuous_iff_continuousAt.2 fun a₀ ↦ ?_
  have h := ((contMDiffAt_inChartAt_mpullback_smul J (m := 0) (n := 1) (by simp) hα x
    (mem_extChartAt_target x) a₀).continuousAt).comp (f := fun a : G ↦ (extChartAt I x x, a))
    (continuous_const.prodMk continuous_id).continuousAt
  exact h.congr (Eventually.of_forall fun a ↦ RoughForm.inChartAt_extChartAt_self _ x)

variable [CompactSpace G] [T2Space G] [OpensMeasurableSpace G] [IsFiniteMeasure μ]

omit [CompleteSpace F] in
/-- The pullbacks of a continuous form by a `C¹` action of a compact group are integrable in the
group element. -/
theorem integrable_mpullback_smul [ContMDiffSMul J I 1 G M] {α : RoughForm I M F k}
    (hα : IsSmoothForm I 0 α) (x : M) :
    Integrable (ε := E [⋀^Fin k]→L[ℝ] F) (fun a : G ↦ mpullback I I (a • ·) α x) μ :=
  integrableOn_univ.1 <|
    (continuous_mpullback_smul J hα x).continuousOn.integrableOn_compact isCompact_univ

/-- The averaged form evaluates on tangent vectors as the average of the pulled-back
evaluations. -/
theorem measureAverageForm_apply [ContMDiffSMul J I 1 G M] {α : RoughForm I M F k}
    (hα : IsSmoothForm I 0 α) (x : M) (v : Fin k → TangentSpace I x) :
    measureAverageForm μ α x v =
      ∫ a, α (a • x) (fun i ↦ mfderiv I I (a • ·) x (v i)) ∂μ := by
  have h := (ContinuousAlternatingMap.apply ℝ E F v).integral_comp_comm
    (integrable_mpullback_smul μ J hα x)
  rw [measureAverageForm_def]
  exact h.symm.trans (integral_congr_ae (Eventually.of_forall fun a ↦ mpullback_apply _ α x v))

/-- In every chart, the averaged form is the average of the chart expressions of the pulled-back
forms. -/
theorem inChartAt_measureAverageForm [ContMDiffSMul J I 1 G M] {α : RoughForm I M F k}
    (hα : IsSmoothForm I 0 α) (x₀ : M) (y : E) :
    (measureAverageForm μ α).inChartAt x₀ y =
      ∫ a, (mpullback I I (a • ·) α).inChartAt x₀ y ∂μ := by
  simp only [RoughForm.inChartAt_eq_compContinuousLinearMapCLM _ x₀ y]
  rw [measureAverageForm_def]
  exact (ContinuousLinearMap.integral_comp_comm _
    (integrable_mpullback_smul μ J hα ((extChartAt I x₀).symm y))).symm

omit [CompleteSpace F] in
/-- Averaging is additive on continuous forms. -/
theorem measureAverageForm_add [ContMDiffSMul J I 1 G M] {α β : RoughForm I M F k}
    (hα : IsSmoothForm I 0 α) (hβ : IsSmoothForm I 0 β) :
    measureAverageForm μ (α + β) = measureAverageForm μ α + measureAverageForm μ β := by
  funext x
  simp only [measureAverageForm_def, mpullback_add, Pi.add_apply]
  exact integral_add (G := E [⋀^Fin k]→L[ℝ] F) (integrable_mpullback_smul μ J hα x)
    (integrable_mpullback_smul μ J hβ x)

section Invariance

variable [MeasurableMul G] [μ.IsMulRightInvariant] [ContMDiffSMul J I 1 G M]
  {α : RoughForm I M F k}

include J

/-- **Invariance of the average.** For a right-invariant measure, such as the normalized Haar
measure of a compact group, every group element preserves the average of a continuous form. -/
theorem mpullback_smul_measureAverageForm (hα : IsSmoothForm I 0 α) (g : G) :
    mpullback I I (g • ·) (measureAverageForm μ α) = measureAverageForm μ α := by
  have hsmul (b : G) : MDifferentiable I I (b • · : M → M) :=
    (ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) b).mdifferentiable one_ne_zero
  funext x
  rw [mpullback_apply_eq_compContinuousLinearMapCLM, measureAverageForm_def,
    measureAverageForm_def]
  refine (ContinuousLinearMap.integral_comp_comm _
    (integrable_mpullback_smul μ J hα (g • x))).symm.trans <|
      (integral_congr_ae (G := E [⋀^Fin k]→L[ℝ] F) (Eventually.of_forall fun a ↦ ?_)).trans
        (integral_mul_right_eq_self (E := E [⋀^Fin k]→L[ℝ] F) (μ := μ)
          (fun a ↦ mpullback I I (a • ·) α x) g)
  exact (mpullback_apply_eq_compContinuousLinearMapCLM _ _ x).symm.trans <|
    (mpullback_comp_at (hsmul g x) (hsmul a (g • x)) α).symm.trans <|
      congrArg (fun f : M → M ↦ mpullback I I f α x) (funext (mul_smul a g)).symm

/-- For a right-invariant probability measure, averaging fixes exactly the invariant continuous
forms. -/
theorem measureAverageForm_eq_self_iff [IsProbabilityMeasure μ] (hα : IsSmoothForm I 0 α) :
    measureAverageForm μ α = α ↔ ∀ a : G, mpullback I I (a • ·) α = α :=
  ⟨fun h a ↦ by simpa only [h] using mpullback_smul_measureAverageForm μ J hα a,
    measureAverageForm_eq_self μ⟩

/-- For a right-invariant probability measure, averaging a continuous form twice gives the same
invariant form. -/
theorem measureAverageForm_idempotent [IsProbabilityMeasure μ] (hα : IsSmoothForm I 0 α) :
    measureAverageForm μ (measureAverageForm μ α) = measureAverageForm μ α :=
  measureAverageForm_eq_self μ (mpullback_smul_measureAverageForm μ J hα)

end Invariance

/-- **Smoothness of the average.** Averaging a `C^m` form over a `C^(m+1)` action of a compact
group gives a `C^m` form. -/
theorem IsSmoothForm.measureAverageForm {m : ℕ∞} [IsManifold I (m + 1) M] [IsManifold J m G]
    [ContMDiffSMul J I (m + 1) G M] {α : RoughForm I M F k} (hα : IsSmoothForm I m α) :
    IsSmoothForm I m (measureAverageForm μ α) := by
  have hα₀ : IsSmoothForm I 0 α := hα.of_le zero_le
  have : ContMDiffSMul J I 1 G M :=
    ⟨(contMDiff_smul (I := J) (I' := I) (n := m + 1)).of_le le_add_self⟩
  refine IsSmoothForm.of_contDiffWithinAt_inChartAt_self fun x₀ ↦ ?_
  rw [I.range_eq_univ, contDiffWithinAt_univ,
    funext (inChartAt_measureAverageForm μ J hα₀ x₀)]
  refine contMDiffAt_iff_contDiffAt.1 <| contMDiffAt_parametric_integral (J := J)
    fun a ↦ ?_
  exact contMDiffAt_inChartAt_mpullback_smul J le_rfl hα x₀ (mem_extChartAt_target x₀) a

-- Cache the canonical operator-space instances: instance search for the normed structure on the
-- space `E →L[ℝ] E [⋀^Fin k]→L[ℝ] F` of derivatives of chart expressions otherwise fails.
private local instance : NormedAddCommGroup (E →L[ℝ] E [⋀^Fin k]→L[ℝ] F) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] E [⋀^Fin k]→L[ℝ] F) :=
  ContinuousLinearMap.toNormedSpace

section Derivative

variable [IsManifold I 2 M] [ContMDiffSMul J I 2 G M] {α : RoughForm I M F k}

include J

omit [MeasurableSpace G] [CompleteSpace F] [CompactSpace G] [T2Space G] [OpensMeasurableSpace G]
  [IsFiniteMeasure μ] in
/-- On the target of the chart at `x₀`, the derivatives of the chart expressions of the pullbacks of
a `C¹` form by a `C²` action are jointly continuous in the chart coordinate and the group
element. -/
private theorem continuousOn_fderiv_inChartAt_mpullback_smul (hα : IsSmoothForm I 1 α) (x₀ : M) :
    ContinuousOn (fun p : E × G ↦ fderiv ℝ ((mpullback I I (p.2 • ·) α).inChartAt x₀) p.1)
      ((extChartAt I x₀).target ×ˢ univ) := by
  intro p hp
  have hg : ContMDiffAt (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F) 1
      (uncurry fun (a : G) (y : E) ↦ (mpullback I I (a • ·) α).inChartAt x₀ y) p.swap :=
    (contMDiffAt_inChartAt_mpullback_smul J (m := 1) (n := 2) (by norm_num) hα x₀ hp.1 p.2).comp
      p.swap (contMDiffAt_snd.prodMk contMDiffAt_fst)
  exact ((ContMDiffAt.fderiv_right hg (n := 0) (by simp)).continuousAt.comp
    continuous_swap.continuousAt).continuousWithinAt

/-- **Differentiation under the average.** In the chart at `x₀`, the derivative of the chart
expression of the average of a `C¹` form at any point of the chart target is the average of the
derivatives of the chart expressions of the pullbacks. -/
theorem hasFDerivAt_inChartAt_measureAverageForm (hα : IsSmoothForm I 1 α) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    HasFDerivAt ((measureAverageForm μ α).inChartAt x₀)
      (∫ a, fderiv ℝ ((mpullback I I (a • ·) α).inChartAt x₀) y ∂μ) y := by
  have : ContMDiffSMul J I 1 G M := ContMDiffSMul.of_le one_le_two
  set u := (extChartAt I x₀).target
  set f : E → G → E [⋀^Fin k]→L[ℝ] F := fun y a ↦ (mpullback I I (a • ·) α).inChartAt x₀ y
  have hu : u ∈ 𝓝 y := (isOpen_extChartAt_target x₀).mem_nhds hy
  have hB : ∀ z ∈ u, ∀ a, ContMDiffAt (𝓘(ℝ, E).prod J) 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F) 1
      (uncurry f) (z, a) := fun z hz a ↦
    contMDiffAt_inChartAt_mpullback_smul J (m := 1) (n := 2) (by norm_num) hα x₀ hz a
  have hF₂ : ∀ a ∈ (univ : Set G), DifferentiableOn ℝ (fun z ↦ f z a) u := fun a _ z hz ↦
    (mdifferentiableAt_iff_differentiableAt.1 <|
      ((hB z hz a).comp z (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt
        one_ne_zero).differentiableWithinAt
  have hD := hasFDerivAt_integral_of_continuousOn_fderiv (μ := μ) hu isCompact_univ
    MeasurableSet.univ (measure_ne_top μ univ) subset_rfl
    (fun p hp ↦ (hB p.1 hp.1 p.2).continuousAt.continuousWithinAt) hF₂
    (continuousOn_fderiv_inChartAt_mpullback_smul J hα x₀)
  simp only [Measure.restrict_univ] at hD
  rw [funext (inChartAt_measureAverageForm μ J (hα.of_le zero_le) x₀)]
  exact hD

omit [CompleteSpace F] in
/-- At every point of the target of the chart at `x₀`, the derivatives of the chart expressions of
the pullbacks are integrable in the group element. -/
private theorem integrable_fderiv_inChartAt_mpullback_smul (hα : IsSmoothForm I 1 α) (x₀ : M)
    {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    Integrable (fun a ↦ fderiv ℝ ((mpullback I I (a • ·) α).inChartAt x₀) y) μ :=
  integrableOn_univ.1 <| ((continuousOn_fderiv_inChartAt_mpullback_smul J hα x₀).comp_continuous
    (continuous_const.prodMk continuous_id) fun a ↦
      ⟨hy, mem_univ a⟩).continuousOn.integrableOn_compact isCompact_univ

/-- **Averaging commutes with the exterior derivative.** For a `C¹` form `α` and a `C²` action of
a compact group on a boundaryless `C²` manifold, `d (∫ a^* α dμ(a)) = ∫ a^* (d α) dμ(a)`. -/
theorem mextDeriv_measureAverageForm (hα : IsSmoothForm I 1 α) :
    mextDeriv (measureAverageForm μ α) = measureAverageForm μ (mextDeriv α) := by
  funext x₀
  rw [mextDeriv_eq_extDeriv_inChartAt, extDeriv,
    (hasFDerivAt_inChartAt_measureAverageForm μ J hα x₀ (mem_extChartAt_target x₀)).fderiv,
    ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply,
    ← ContinuousLinearMap.integral_comp_comm _
      (integrable_fderiv_inChartAt_mpullback_smul μ J hα x₀ (mem_extChartAt_target x₀)),
    measureAverageForm_def]
  refine congrArg (integral (G := E [⋀^Fin (k + 1)]→L[ℝ] F) μ) (funext fun a ↦ ?_)
  have hsmul : ContMDiff I I 2 (a • · : M → M) :=
    ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) a
  rw [mpullback_mextDeriv hsmul ((isSmoothBundleForm_def 1 α).mpr hα.contMDiff),
    mextDeriv_eq_extDeriv_inChartAt, ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply,
    extDeriv]

/-- The average of a closed `C¹` form over a `C²` action of a compact group is closed. -/
theorem mextDeriv_measureAverageForm_eq_zero (hα : IsSmoothForm I 1 α) (hclosed : mextDeriv α = 0) :
    mextDeriv (measureAverageForm μ α) = 0 := by
  rw [mextDeriv_measureAverageForm μ J hα, hclosed, measureAverageForm_zero]

/-- **Averaging preserves zero first jets on invariant sets.** If a `C¹` form `α` vanishes, with
zero first derivative in charts, at every point of a set `s` invariant under the action, then so
does its average. -/
theorem hasFDerivAt_inChartAt_measureAverageForm_of_apply_eq_zero (hα : IsSmoothForm I 1 α)
    {s : Set M} (hs : ∀ a : G, ∀ x ∈ s, a • x ∈ s) (hα₀ : ∀ x ∈ s, α x = 0)
    (hα₁ : ∀ x ∈ s, HasFDerivAt (α.inChartAt x) (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F)
      (extChartAt I x x))
    {x : M} (hx : x ∈ s) :
    HasFDerivAt ((measureAverageForm μ α).inChartAt x) (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F)
      (extChartAt I x x) := by
  have h := hasFDerivAt_inChartAt_measureAverageForm μ J hα x (mem_extChartAt_target x)
  convert h using 1
  refine (integral_eq_zero_of_ae (G := E →L[ℝ] E [⋀^Fin k]→L[ℝ] F)
    (Eventually.of_forall fun a ↦ ?_)).symm
  have hsmul : ContMDiffAt I I 1 (a • · : M → M) x :=
    (ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) a).of_le one_le_two |>.contMDiffAt
  have hpull := hasFDerivWithinAt_inChartAt_mpullback_of_apply_eq_zero hsmul
    (hα₀ _ (hs a x hx)) ((hα₁ _ (hs a x hx)).hasFDerivWithinAt)
  rw [I.range_eq_univ, hasFDerivWithinAt_univ] at hpull
  exact hpull.fderiv

end Derivative

end Average

end TauCeti
