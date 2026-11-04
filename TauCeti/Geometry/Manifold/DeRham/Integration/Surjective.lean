/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.PoincarePairing
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import Mathlib.Geometry.Manifold.BumpFunction
import TauCeti.Analysis.Normed.Module.Alternating.TopDegree

/-!
# Surjectivity of integration on top compactly supported cohomology

Every neighbourhood of a point of an oriented finite-dimensional smooth manifold with corners
supports a smooth closed top form of integral one. Integration on top compactly supported
de Rham cohomology is therefore surjective on every nonempty boundaryless manifold.
Neither connectedness nor positive dimension is required. These localized representatives
allow cohomology classes to be compared using coordinate neighbourhoods.

Generalize the bump-times-determinant construction of
`Module.Basis.exists_compactlySupportedClosedForms_integralTopForm_model_eq_one` using
Mathlib's `SmoothBumpFunction`, the chart pullback of `Module.Basis.continuousDet`,
and the signed chart formula for `integralTopForm`. The positivity argument follows
`integralTopForm_pos`, using the dense interior of each chart target. Local constancy of the sign
prevents cancellation within the chosen support, including in dimension zero.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 17,
  the integration map on top compactly supported cohomology.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, §4.
-/

public noncomputable section

open Set MeasureTheory Topology Filter
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {n : ℕ}

/-- Cutting the chart pullback of a determinant off inside its chart gives a smooth form. -/
private theorem isSmoothForm_bump_smul_chart_det (x : M) (χ : SmoothBumpFunction I x)
    (b : Module.Basis (Fin n) ℝ E) :
    IsSmoothForm I ∞ (fun y ↦ χ y •
      mpullback I 𝓘(ℝ, E) (extChartAt I x) (fun _ ↦ b.continuousDet) y) := by
  have : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
  rw [isSmoothForm_def]
  exact χ.contMDiff.contMDiffOn.smul_section_of_tsupport
    (isOpen_extChartAt_source x) χ.tsupport_subset_extChartAt_source fun y hy ↦
      (contMDiffAt_mpullback_extChartAt hy contDiffWithinAt_const).contMDiffWithinAt

/-- A chart-supported bump multiple of the determinant has nonzero integral. -/
private theorem exists_topForm_integral_ne_zero (o : Manifold.Orientation I M (Fin n))
    (x : M) {U : Set M} (hU : U ∈ 𝓝 x) :
    ∃ φ : compactlySupportedClosedForms I M n,
      _root_.tsupport (α := E [⋀^Fin n]→L[ℝ] ℝ) φ.1.1 ⊆ U ∧
      integralTopForm o φ.1.1 ≠ 0 := by
  classical
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  obtain ⟨l, rfl⟩ := o.exists_lift
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
  -- Keep the chart sign constant on the bump support to prevent cancellation.
  have hsign : ∀ᶠ y in 𝓝 x, l.signAt x y = l.signAt x x :=
    ((l.continuousOn_signAt x x (mem_chart_source H x)).continuousAt
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))).eventually
        ((isOpen_discrete {l.signAt x x}).mem_nhds rfl)
  obtain ⟨χ, -, hχ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
    (inter_mem hU hsign)
  -- Pull the determinant back through the chart and cut it off inside the chart source.
  let α : RoughForm 𝓘(ℝ, E) E ℝ n := fun _ ↦ b.continuousDet
  let p : RoughForm I M ℝ n := mpullback I 𝓘(ℝ, E) (extChartAt I x) α
  let ψ : RoughForm I M ℝ n := fun y ↦ χ y • p y
  have hs : IsSmoothForm I ∞ ψ := isSmoothForm_bump_smul_chart_det x χ b
  have hsub : _root_.tsupport (α := E [⋀^Fin n]→L[ℝ] ℝ) ψ ⊆ _root_.tsupport χ := by
    -- As in `RoughForm.tsupport_smul_subset`, matching the model-fibre support against the
    -- tangent-fibre scalar action makes `tsupport_smul_subset_left` time out. Use its support
    -- argument pointwise, so that scalar operations remain in a single tangent fibre.
    apply closure_mono
    intro y hy
    by_contra h
    have hχy : χ y = 0 := Function.notMem_support.mp h
    apply hy
    ext v
    simp [ψ, hχy]
    rfl
  have hc : IsCompact (_root_.tsupport (α := E [⋀^Fin n]→L[ℝ] ℝ) ψ) :=
    χ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) hsub
  have hchart := hsub.trans χ.tsupport_subset_extChartAt_source
  have hcoef (z : E) (hz : z ∈ (extChartAt I x).target) :
      RoughForm.inChartAt (I := I) ψ x z b = χ ((extChartAt I x).symm z) := by
    have hp : p.inChartAt x z = α z := RoughForm.inChartAt_mpullback_extChartAt α x hz
    rw [RoughForm.inChartAt_fun_smul, hp]
    simp [α, Module.Basis.continuousDet_apply, Module.Basis.det_self]
  let g := RoughForm.signedInChartAt (I := I) ψ b x (fun _ ↦ 1)
  have hg : ∀ z, 0 ≤ g z := by
    intro z
    dsimp only [g]
    rw [RoughForm.signedInChartAt_apply]
    split_ifs with hz
    · simpa [hcoef z hz] using χ.nonneg (x := (extChartAt I x).symm z)
    · exact le_rfl
  have hgx : g (extChartAt I x x) = 1 := by
    dsimp only [g]
    rw [RoughForm.signedInChartAt_apply_of_mem_source _ _ _ _ (mem_extChartAt_source x),
      hcoef _ (mem_extChartAt_target x), (extChartAt I x).left_inv (mem_extChartAt_source x)]
    simp
  have hcont : ContinuousOn g (extChartAt I x).target :=
    RoughForm.continuousOn_signedInChartAt (I := I) ψ b x _ continuous_const
      (hs.continuousOn_inChartAt x)
  have hpos : 0 < ∫ z, g z ∂b.addHaar := by
    rw [integral_pos_iff_support_of_nonneg hg (hs.integrable_signedInChartAt_one hc b x)]
    -- As in `integralTopForm_pos`, positivity on a relatively open neighbourhood reaches
    -- the interior of the chart target, even when the chosen point is on the boundary.
    obtain ⟨V, hVo, hxV, hV⟩ := mem_nhdsWithin.mp
      ((hcont.continuousWithinAt (mem_extChartAt_target x)).eventually
        (lt_mem_nhds (by rw [hgx]; exact zero_lt_one)))
    obtain ⟨z, hzV, hz⟩ := mem_closure_iff.mp
      (extChartAt_target_subset_closure_interior (mem_extChartAt_target (I := I) x)) V hVo hxV
    let W := interior (extChartAt I x).target ∩ g ⁻¹' Ioi 0
    have hWo : IsOpen W :=
      (hcont.mono interior_subset).isOpen_inter_preimage isOpen_interior isOpen_Ioi
    have hWne : W.Nonempty := ⟨z, hz, hV ⟨hzV, interior_subset hz⟩⟩
    exact (hWo.measure_pos b.addHaar hWne).trans_le
      (measure_mono fun y hy ↦ ne_of_gt hy.2)
  -- The unsigned chart integral is positive; the actual orientation adds only unit signs.
  have hi : integralTopForm (Manifold.Orientation.mk l) ψ ≠ 0 := by
    rw [integralTopForm_eq_chartIntegral l ψ (hs.integrableTopForm hc b) x hchart,
      l.chartIntegral_eq_const_mul_unsigned ψ b x (l.signAt x x)
        (fun y hy ↦ (hχ (hsub hy)).2)]
    exact mul_ne_zero (mul_ne_zero
      (by exact_mod_cast (Orientation.signBasis l.modelOrientation b).ne_zero)
      (by exact_mod_cast (l.signAt x x).ne_zero)) hpos.ne'
  refine ⟨⟨⟨ψ, hs.mem_smoothBundleForms⟩, (mem_compactlySupportedClosedForms I).mpr
    ⟨(mem_compactlySupportedForms I).mpr hc,
      mem_closedForms_of_finrank_le I (by simpa using l.card_eq.ge) _⟩⟩,
    hsub.trans (fun y hy ↦ (hχ hy).1), hi⟩

/-- Every neighbourhood of a point of an oriented smooth manifold with corners supports a
compactly supported closed top form of integral one, also in dimension zero. -/
theorem exists_compactlySupportedClosedForms_integralTopForm_eq_one
    (o : Manifold.Orientation I M (Fin n)) (x : M) {U : Set M} (hU : U ∈ 𝓝 x) :
    ∃ φ : compactlySupportedClosedForms I M n,
      _root_.tsupport (α := E [⋀^Fin n]→L[ℝ] ℝ) φ.1.1 ⊆ U ∧
      integralTopForm o φ.1.1 = 1 := by
  obtain ⟨φ, hφU, hφ⟩ := exists_topForm_integral_ne_zero o x hU
  refine ⟨(integralTopForm o φ.1.1)⁻¹ • φ, ?_, ?_⟩
  · exact (RoughForm.tsupport_smul_subset _ φ.1.1).trans hφU
  · simpa only [Submodule.coe_smul] using
      (integralTopForm_smul o (integralTopForm o φ.1.1)⁻¹ φ.1.1).trans (inv_mul_cancel₀ hφ)

/-- Integration on top compactly supported de Rham cohomology is onto for every nonempty
oriented boundaryless manifold. Connectedness is needed for injectivity, but not for this
assertion. -/
theorem compactlySupportedDeRhamCohomology.surjective_integral [BoundarylessManifold I M]
    [SigmaCompactSpace M] [Nonempty M]
    (o : Manifold.Orientation I M (Fin n)) :
    Function.Surjective (integral o) := by
  obtain ⟨x⟩ := ‹Nonempty M›
  obtain ⟨φ, -, hφ⟩ := exists_compactlySupportedClosedForms_integralTopForm_eq_one o x
    (U := univ) (by simp)
  intro c
  refine ⟨c • mk I n φ, ?_⟩
  simp [hφ]

end TauCeti
