/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Linearization
public import TauCeti.Geometry.Manifold.Morse.OneForm.Basic

/-!
# Regular zeros of closed one-forms

A zero of a locally exact real one-form is regular as a bundle section exactly when
it is a nondegenerate critical point of a `C²` local primitive. The derivative of the
coordinate covector field is the Hessian of that primitive; the source and the cotangent
fibre have equal finite dimension, so surjectivity is equivalent to invertibility.

Consequently a smooth closed one-form is Morse if and only if its intrinsic section
linearization is surjective at each zero. This is the regular-zero formulation of
transversality to the zero section, with no Morse--Smale or periodic-orbit condition.
One-forms use the existing alternating cotangent fibres; linear functionals and
alternating maps of one vector are identified by `ContinuousAlternatingMap.ofSubsingletonLIE`.

## References

* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 1.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 6 (transversality).
-/

public section

open Set Function
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {α : RoughForm I M ℝ 1} {f : M → ℝ} {U : Set M} {x : M}

/-- At a zero of a locally exact one-form, its section linearization is surjective exactly
when the Hessian of a `C²` local primitive is surjective. This comparison needs no finite
dimensionality assumption. -/
theorem IsPrimitiveOn.surjective_sectionLinearization_iff_surjective_criticalHessian
    (hf : IsPrimitiveOn α f U) (hxU : x ∈ U) (hf₂ : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hx : α x = 0) :
    Surjective (sectionLinearization (F := E [⋀^Fin 1]→L[ℝ] ℝ)
      (E := fun y : M ↦ TangentSpace I y [⋀^Fin 1]→L[ℝ] ℝ) I id α x) ↔
      Surjective (criticalHessian I f x) := by
  have hD := hf.hasFDerivAt_inChartAt hxU hf₂
  have hsurj : Surjective (fderiv ℝ (α.inChartAt x) (extChartAt I x x)) ↔
      Surjective (fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I x).symm)) (extChartAt I x x)) := by
    rw [hD.fderiv, ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    exact Surjective.of_comp_iff' (ContinuousAlternatingMap.ofSubsingletonLIE
      (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).bijective _
  have hs := (mdifferentiableAt_section I α).mp
    (mdifferentiableAt_form_of_differentiableWithinAt_inChartAt_self
      hD.differentiableAt.differentiableWithinAt)
  rw [surjective_sectionLinearization_iff continuousAt_id
    (mem_baseSet_trivializationAt _ _ x) hs hx]
  simp only [id_eq]
  rw [RoughForm.mvfderiv_trivializationAt_eq_fderiv_inChartAt hD.differentiableAt]
  -- The tangent space is the model space; use the Hessian's defining equality explicitly.
  convert! hsurj using 1
  exact iff_of_eq (congrArg (fun A : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ ↦
    Surjective A) criticalHessian_def)

/-- At a zero of a locally exact one-form, its intrinsic section linearization is surjective
if and only if the zero is a nondegenerate critical point of a `C²` local primitive. -/
theorem IsPrimitiveOn.surjective_sectionLinearization_iff [FiniteDimensional ℝ E]
    (hf : IsPrimitiveOn α f U) (hxU : x ∈ U) (hf₂ : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hx : α x = 0) :
    Surjective (sectionLinearization (F := E [⋀^Fin 1]→L[ℝ] ℝ)
      (E := fun y : M ↦ TangentSpace I y [⋀^Fin 1]→L[ℝ] ℝ) I id α x) ↔
      IsManifoldNondegenerateCriticalPoint I f x := by
  rw [hf.surjective_sectionLinearization_iff_surjective_criticalHessian hxU hf₂ hx,
    isManifoldNondegenerateCriticalPoint_iff_criticalHessian]
  have hcrit : mvfderiv I f x = 0 := by
    have hd := mextDeriv_ofFunction_apply_eq_zero_iff.mp ((hf.mextDeriv_eq x hxU).trans hx)
    exact mvfderiv_eq_zero_iff.mpr hd
  exact ⟨fun h ↦ ⟨hf₂, hcrit, ContinuousLinearMap.isInvertible_of_surjective (E := E) h⟩,
    fun h ↦ h.2.2.surjective⟩

/-- The section linearization of a Morse one-form is surjective at every zero. -/
theorem IsMorseOneForm.surjective_sectionLinearization (hα : IsMorseOneForm α)
    (hx : α x = 0) :
    Surjective (sectionLinearization (F := E [⋀^Fin 1]→L[ℝ] ℝ)
      (E := fun y : M ↦ TangentSpace I y [⋀^Fin 1]→L[ℝ] ℝ) I id α x) := by
  obtain ⟨f, U, hxU, hf, hcrit⟩ := hα.exists_nondegenerate_primitive x hx
  exact (hf.surjective_sectionLinearization_iff_surjective_criticalHessian hxU
    hcrit.contMDiffAt hx).2
      (isManifoldNondegenerateCriticalPoint_iff_criticalHessian.mp hcrit).2.2.surjective

/-- A smooth closed real one-form is Morse exactly when it is regular at every zero as a
section of the alternating cotangent bundle. -/
theorem isMorseOneForm_iff_surjective_sectionLinearization [FiniteDimensional ℝ E]
    [T2Space M] [IsManifold I ∞ M]
    (hα : IsSmoothForm I ∞ α) (hclosed : mextDeriv α = 0) :
    IsMorseOneForm α ↔ ∀ x, α x = 0 →
      Surjective (sectionLinearization (F := E [⋀^Fin 1]→L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin 1]→L[ℝ] ℝ) I id α x) := by
  refine ⟨fun h x hx ↦ h.surjective_sectionLinearization hx, fun h ↦ ⟨hα, hclosed, ?_⟩⟩
  intro x hx
  obtain ⟨f, hfs, U, hxU, hf⟩ := exists_contMDiff_isPrimitiveOn (by simp) hα hclosed x
  exact ⟨f, U, hxU, hf,
    (hf.surjective_sectionLinearization_iff hxU (hfs.of_le (by simp) x) hx).1 (h x hx)⟩

end TauCeti
