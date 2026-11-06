/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.LocalPrimitive
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization
import TauCeti.Geometry.Manifold.MFDeriv.Chart

/-!
# Linearization of differential forms as bundle sections

The section linearization of a differential form can be read in its preferred
chart: its fibre coordinates are the derivative of `RoughForm.inChartAt`. In particular,
surjectivity of the section linearization is equivalent to surjectivity of this coordinate
derivative. At a zero this is the intrinsic regular-zero condition, independent of
trivialization; away from zeros the linearization uses the preferred trivialization.
The result applies to forms of every degree, without a closedness assumption.

For a locally exact one-form, `IsPrimitiveOn.inChartAt_eventuallyEq_fderiv` identifies
its coordinate germ with the ordinary derivative of a primitive, and
`IsPrimitiveOn.hasFDerivAt_inChartAt` computes its derivative from the primitive's
second derivative. These formulas connect regular zeros of a covector field with
nondegenerate critical points of a potential.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 6 (transversality).
-/

public section

open Bundle Filter Set
open scoped Manifold Topology ContDiff

namespace TauCeti.RoughForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {φ : RoughForm I M F k} {x : M}

/-- In the preferred fibre coordinates, the section linearization of a differential form
is the derivative of its chart expression. -/
theorem continuousLinearMapAt_comp_sectionLinearization
    (hφ : DifferentiableAt ℝ (φ.inChartAt x) (extChartAt I x x)) :
    ((trivializationAt (E [⋀^Fin k]→L[ℝ] F)
      (fun y ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] F) x).continuousLinearMapAt ℝ x).comp
        (sectionLinearization (F := E [⋀^Fin k]→L[ℝ] F)
          (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] F) I id φ x) =
      fderiv ℝ (φ.inChartAt x) (extChartAt I x x) := by
  have hs := mdifferentiableAt_form_of_differentiableWithinAt_inChartAt_self
    hφ.differentiableWithinAt
  have hc := (mdifferentiableAt_section I φ).mp hs
  have heq := φ.trivializationAt_snd_eventuallyEq_inChartAt x
  rw [I.range_eq_univ, nhdsWithin_univ] at heq
  have hd : mvfderiv I (fun y ↦ (trivializationAt (E [⋀^Fin k]→L[ℝ] F)
      (fun y ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] F) x ⟨y, φ y⟩).2) x =
      fderiv ℝ (φ.inChartAt x) (extChartAt I x x) := by
    rw [hc.mvfderiv, I.range_eq_univ, fderivWithin_univ]
    -- The tangent space at the source is the model space; the coefficient bundle is trivial.
    convert! heq.fderiv_eq using 1
  rw [sectionLinearization_def]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, id_eq]
  rw [Trivialization.continuousLinearMapAt_symmL _ (mem_baseSet_trivializationAt _ _ x)]
  exact congrArg (fun L ↦ L v) hd

/-- Surjectivity of a form's section linearization can be checked by differentiating its
preferred chart expression. At a zero this characterizes transversality to the zero section. -/
theorem surjective_sectionLinearization_iff
    (hφ : DifferentiableAt ℝ (φ.inChartAt x) (extChartAt I x x)) :
    Function.Surjective (sectionLinearization (F := E [⋀^Fin k]→L[ℝ] F)
      (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] F) I id φ x) ↔
      Function.Surjective (fderiv ℝ (φ.inChartAt x) (extChartAt I x x)) := by
  rw [← continuousLinearMapAt_comp_sectionLinearization hφ]
  rw [← Trivialization.coe_continuousLinearEquivAt_eq' _
    (mem_baseSet_trivializationAt _ _ x)]
  exact (Function.Surjective.of_comp_iff'
    ((trivializationAt (E [⋀^Fin k]→L[ℝ] F)
      (fun y ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] F) x).continuousLinearEquivAt ℝ x
        (mem_baseSet_trivializationAt _ _ x)).bijective _).symm

end TauCeti.RoughForm

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {α : RoughForm I M F 1} {f : M → F} {U : Set M} {x : M}

/-- Near a point of its domain, the chart expression of a locally exact one-form is the
ordinary derivative of its local primitive, read as an alternating map of one vector. -/
theorem IsPrimitiveOn.inChartAt_eventuallyEq_fderiv (hf : IsPrimitiveOn α f U) (hx : x ∈ U) :
    α.inChartAt x =ᶠ[𝓝 (extChartAt I x x)] fun z ↦
      ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1)
        (fderiv ℝ (f ∘ (extChartAt I x).symm) z) := by
  have hU : (extChartAt I x).symm ⁻¹' U ∈ 𝓝 (extChartAt I x x) := by
    apply (continuousAt_extChartAt_symm (I := I) x).preimage_mem_nhds
    exact hf.isOpen.mem_nhds (by simpa using hx)
  filter_upwards [hU, extChartAt_target_mem_nhds (I := I) x] with z hzU hz
  have hd := (hf.mdifferentiableOn _ hzU).mdifferentiableAt (hf.isOpen.mem_nhds hzU)
  have hψ := mdifferentiableWithinAt_extChartAt_symm (I := I) hz
  rw [I.range_eq_univ] at hψ
  have hcomp := mvfderiv_comp z hd (hψ.mdifferentiableAt univ_mem)
  rw [mvfderiv_eq_fderiv] at hcomp
  ext v
  rw [RoughForm.inChartAt_apply, ← hf.mextDeriv_eq _ hzU, mextDeriv_ofFunction,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply]
  rw [I.range_eq_univ, mfderivWithin_univ]
  -- The tangent identification of the model space is the identity.
  exact congrArg (fun L ↦ L (v 0)) hcomp.symm

/-- The derivative of a locally exact one-form in a preferred chart is the second derivative
of its primitive, followed by the identification of linear maps with degree-one alternating
maps. No critical-point assumption is needed for this coordinate formula. -/
theorem IsPrimitiveOn.hasFDerivAt_inChartAt (hf : IsPrimitiveOn α f U) (hx : x ∈ U)
    (hf₂ : ContMDiffAt I 𝓘(ℝ, F) 2 f x) :
    HasFDerivAt (α.inChartAt x)
      ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F)
          (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I x).symm)) (extChartAt I x x)))
      (extChartAt I x x) := by
  have hD := (hf₂.contDiffAt_comp_extChartAt_symm.fderiv_right
    (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt one_ne_zero
  exact ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F)
    (0 : Fin 1)).toContinuousLinearEquiv.hasFDerivAt.comp _ hD.hasFDerivAt).congr_of_eventuallyEq
      (hf.inChartAt_eventuallyEq_fderiv hx)

end TauCeti
