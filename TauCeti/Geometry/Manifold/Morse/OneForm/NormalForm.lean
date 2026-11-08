/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.OneForm.Index
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Existence
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Local normal forms of Morse one-forms

Near a zero, a Morse closed one-form admits a primitive and a Morse chart whose source lies
in the primitive's domain. In these coordinates the form is the differential of the normalized
quadratic potential `f x + (1/2) ∑ i, w i * (L z i) ^ 2`, where `L` is the chart's linear
coordinate change. Its evaluation is `∑ i, w i * (L z i) * (L v i)`, with exactly as many
negative weights as the index of the zero.
The chart is an actual smooth chart, not merely an equality of Hessians.

The pullback formulas hold only on the chart target. Outside that target the inverse chart
need not be a local diffeomorphism, and no coordinate formula is asserted.

## References

* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 1.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer 2014, Theorem 1.3.1.
-/

public section

noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  {α : RoughForm 𝓘(ℝ, E) M ℝ 1} {f : M → ℝ} {x : M}

namespace MorseChart

omit [FiniteDimensional ℝ E] in
/-- In a Morse chart for a local primitive, the one-form is the differential of the quadratic
normal form. The equality is asserted on the target of the chart. -/
theorem mpullback_eq_mextDeriv_quadratic (φ : MorseChart E f x)
    (hf : IsPrimitiveOn α f φ.toChart.source) {z : E} (hz : z ∈ φ.toChart.target) :
    mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart.symm α z =
      mextDeriv (RoughForm.ofFunction 𝓘(ℝ, E) φ.quadratic) z := by
  have hψ := mdifferentiableAt_symm_of_mem_maximalAtlas φ.mem_maximalAtlas_one hz
  have hdf := (hf.mdifferentiableOn _ (φ.toChart.map_target hz)).mdifferentiableAt
    (hf.isOpen.mem_nhds (φ.toChart.map_target hz))
  have heq : f ∘ φ.toChart.symm =ᶠ[𝓝 z] φ.quadratic := by
    filter_upwards [φ.toChart.open_target.mem_nhds hz] with w hw
    simpa only [comp_apply, φ.toChart.right_inv hw] using
      φ.eqOn_quadratic (φ.toChart.map_target hw)
  calc
    mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart.symm α z =
        mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart.symm
          (mextDeriv (RoughForm.ofFunction 𝓘(ℝ, E) f)) z := by
      ext v
      rw [mpullback_apply, mpullback_apply, hf.mextDeriv_eq _ (φ.toChart.map_target hz)]
    _ = mextDeriv (RoughForm.ofFunction 𝓘(ℝ, E) (f ∘ φ.toChart.symm)) z :=
      mpullback_mextDeriv_ofFunction_apply hψ hdf
    _ = mextDeriv (RoughForm.ofFunction 𝓘(ℝ, E) φ.quadratic) z := by
      rw [mextDeriv_ofFunction, mextDeriv_ofFunction, heq.mvfderiv_eq]

/-- With the Morse chart's linear coordinate change `L = φ.coord`, the coordinate one-form
at `z` evaluates on `v` as `∑ i, φ.weight i * (L z i) * (L v i)`. The tangent vector is
identified with `v` by `NormedSpace.fromTangentSpace z`. In particular the quadratic
potential's factor `1/2` disappears on differentiation. -/
theorem mpullback_apply_eq_sum (φ : MorseChart E f x)
    (hf : IsPrimitiveOn α f φ.toChart.source) {z : E} (hz : z ∈ φ.toChart.target) (v : E) :
    mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart.symm α z
        ![(NormedSpace.fromTangentSpace z).symm v] =
      ∑ i, φ.weight i * φ.coord z i * φ.coord v i := by
  rw [φ.mpullback_eq_mextDeriv_quadratic hf hz, mextDeriv_ofFunction,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply, mvfderiv_eq_fderiv]
  simp [φ.fderiv_quadratic_apply]

end MorseChart

/-- A zero of a Morse one-form admits a Morse chart for a local primitive, with the primitive
valid throughout the chart source and the negative weights counted by the one-form index. -/
theorem IsMorseOneForm.exists_primitive_morseChart [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (hα : IsMorseOneForm α) (hx : α x = 0) :
    ∃ (f : M → ℝ) (φ : MorseChart E f x), IsPrimitiveOn α f φ.toChart.source ∧
      {i | φ.weight i < 0}.ncard = hα.morseIndex x hx := by
  obtain ⟨f, hfs, U, hxU, hf⟩ := exists_contMDiff_isPrimitiveOn (by simp)
    hα.isSmoothForm hα.mextDeriv_eq_zero x
  obtain ⟨φ⟩ := (hα.isManifoldNondegenerateCriticalPoint hf hxU hx).nonempty_morseChart
    (Eventually.of_forall fun y ↦ hfs.contMDiffAt)
  refine ⟨f, φ.restr hf.isOpen hxU, ?_, ?_⟩
  · exact hf.mono (φ.restr hf.isOpen hxU).toChart.open_source
      (by rw [φ.restr_source]; exact inter_subset_right)
  · rw [MorseChart.restr_weight, φ.ncard_weight_neg, hα.morseIndex_eq hx hf hxU]

end TauCeti
