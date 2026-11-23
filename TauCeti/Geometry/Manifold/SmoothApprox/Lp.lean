/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.UrysohnsLemma

/-!
# Smooth approximation in `Lᵖ` on manifolds, with control of the support

On a finite-dimensional real manifold `M`, Hausdorff and second countable, with a measure on its
Borel sets that is finite on compact sets, a function in `Lᵖ`, `1 ≤ p < ∞`, that vanishes almost
everywhere off a closed set `s` is the `Lᵖ` limit of smooth compactly supported functions whose
topological support lies in any prescribed neighbourhood `t` of `s`
(`MeasureTheory.MemLp.exists_contMDiff_tsupport_subset_eLpNorm_sub_le`). This is the manifold
counterpart of `MeasureTheory.MemLp.exist_contDiff_tsupport_subset_eLpNorm_sub_le` on normed
spaces. Support control is what lets the approximants of a function supported in a chart be read
in that chart.

The approximation goes through continuous functions: Mathlib's
`MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le` gives a continuous compactly
supported `h` close to `f` in `Lᵖ`; a continuous cutoff `χ` with values in `[0, 1]`, equal to `1`
on `s` and supported in `t`, does not increase the distance to `f`; and Mathlib's
`Continuous.exists_contMDiff_approx` approximates `χ h` uniformly by a smooth function supported
where `χ h` is, so within a fixed compact set of finite measure.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Manifold ContDiff Topology

namespace MeasureTheory.MemLp

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure M} [IsFiniteMeasureOnCompacts μ]
  {p : ℝ≥0∞}

/-- A function in `Lᵖ`, `1 ≤ p < ∞`, on a finite-dimensional Hausdorff second-countable manifold,
vanishing almost everywhere off a closed set `s`, is the `Lᵖ` limit of smooth compactly supported
functions with topological support in `t`, for any neighbourhood `t` of `s`. -/
theorem exists_contMDiff_tsupport_subset_eLpNorm_sub_le (hp : p ≠ ⊤) (hp₁ : 1 ≤ p) {f : M → F}
    (hf : MemLp f p μ) {s t : Set M} (hs : IsClosed s) (ht : t ∈ 𝓝ˢ s)
    (hfs : ∀ᵐ x ∂μ, x ∉ s → f x = 0) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : C^∞⟮I, M; 𝓘(ℝ, F), F⟯, HasCompactSupport g ∧ tsupport g ⊆ t ∧
      eLpNorm (f - ⇑g) p μ ≤ ε := by
  have := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε).ne'
  -- A continuous cutoff `χ`, equal to `1` on `s`, with topological support inside `t`.
  obtain ⟨u, hu, hsu, hut⟩ := normal_exists_closure_subset hs isOpen_interior
    (subset_interior_iff_mem_nhdsSet.2 ht)
  obtain ⟨χ, hχu, hχs, hχI⟩ := exists_continuous_zero_one_of_isClosed hu.isClosed_compl hs
    (disjoint_compl_left_iff_subset.2 hsu)
  have hχu' : Function.support χ ⊆ u := fun x hx ↦ by_contra fun h ↦ hx (hχu h)
  have hχt : tsupport χ ⊆ t := (closure_mono hχu').trans (hut.trans interior_subset)
  -- A continuous compactly supported `h` close to `f`, and a smooth `g` uniformly close to `χ h`.
  obtain ⟨h, hhc, hfh, hh, -⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le hp hε2
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt (a := μ (tsupport h) ^ p.toReal⁻¹)
    (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      hhc.measure_lt_top.ne) hε2
  set f₁ : M → F := fun x ↦ χ x • h x
  have hf₁ : Continuous f₁ := χ.continuous.smul hh
  obtain ⟨g, hgδ, hgf₁⟩ := hf₁.exists_contMDiff_approx I ⊤ (ε := fun _ ↦ (δ : ℝ))
    continuous_const fun _ ↦ NNReal.coe_pos.2 hδ
  have hf₁h : Function.support f₁ ⊆ tsupport h :=
    (Function.support_smul_subset_right _ _).trans (subset_tsupport h)
  refine ⟨g, hhc.mono' ((hgf₁.trans (Function.support_smul_subset_right _ _)).trans subset_closure),
    (closure_mono (hgf₁.trans (Function.support_smul_subset_left (⇑χ) h))).trans hχt, ?_⟩
  have hgm : AEStronglyMeasurable (g : M → F) μ := g.contMDiff.continuous.aestronglyMeasurable
  have hf₁m : AEStronglyMeasurable f₁ μ := hf₁.aestronglyMeasurable
  -- Cutting off by `χ` does not increase the distance to `f`.
  have h₁ : eLpNorm (f - f₁) p μ ≤ ε / 2 := by
    refine (eLpNorm_mono_ae (hf.aestronglyMeasurable.sub hf₁m) ?_).trans hfh
    filter_upwards [hfs] with x hx
    by_cases hxs : x ∈ s
    · simp [f₁, hχs hxs]
    · have hχx : ‖χ x‖ ≤ 1 := (Real.norm_of_nonneg (hχI x).1).trans_le (hχI x).2
      simpa [f₁, hx hxs, norm_smul] using mul_le_of_le_one_left (norm_nonneg _) hχx
  -- `χ h - g` is uniformly smaller than `δ` and vanishes off the support of `h`.
  have h₂ : eLpNorm (f₁ - ⇑g) p μ ≤ ε / 2 := by
    refine (eLpNorm_sub_le_of_dist_bdd μ hp hhc.isCompact.measurableSet.nullMeasurableSet
      δ.coe_nonneg (hf₁m.sub hgm) (fun x ↦ by rw [dist_comm]; exact (hgδ x).le) hf₁h
      (hgf₁.trans hf₁h)).trans ?_
    rw [one_div, ENNReal.ofReal_coe_nnreal]
    exact hδε.le
  calc eLpNorm (f - ⇑g) p μ = eLpNorm ((f - f₁) + (f₁ - ⇑g)) p μ := by
        rw [sub_add_sub_cancel]
    _ ≤ eLpNorm (f - f₁) p μ + eLpNorm (f₁ - ⇑g) p μ := eLpNorm_add_le hp₁
    _ ≤ ε / 2 + ε / 2 := add_le_add h₁ h₂
    _ = ε := ENNReal.add_halves ε

end MeasureTheory.MemLp
