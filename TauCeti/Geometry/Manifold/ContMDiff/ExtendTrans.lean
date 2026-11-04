/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# Smoothness of moved extended charts

A chart satisfying `OpenPartialHomeomorph.IsExtendTransChart` is a chart from the maximal
atlas, extended to the model vector space and composed with a smooth homeomorphism with smooth
inverse. Both it and its inverse are smooth on their respective domains. These facts allow
regular-domain charts to be compared with the ambient smooth structure.
-/

public section

open scoped ContDiff Manifold

namespace OpenPartialHomeomorph

variable {𝕜 E F H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners 𝕜 E H}
  [I.Boundaryless] {m : ℕ∞ω}

/-- A smoothly moved extended chart is smooth on its source. -/
theorem IsExtendTransChart.contMDiffOn {e : OpenPartialHomeomorph M F}
    (he : e.IsExtendTransChart I m) : ContMDiffOn I 𝓘(𝕜, F) m e e.source := by
  obtain ⟨c, Ψ, hc, hΨ, -, rfl⟩ := isExtendTransChart_iff.mp he
  rw [extendTrans_source]
  refine (hΨ.contMDiff.comp_contMDiffOn (c.contMDiffOn_extend hc)).congr fun w _ ↦ ?_
  simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe, extendTrans_apply]

/-- The inverse of a smoothly moved extended chart is smooth on its target. -/
theorem IsExtendTransChart.contMDiffOn_symm {e : OpenPartialHomeomorph M F}
    (he : e.IsExtendTransChart I m) : ContMDiffOn 𝓘(𝕜, F) I m e.symm e.target := by
  obtain ⟨c, Ψ, hc, -, hΨ, rfl⟩ := isExtendTransChart_iff.mp he
  rw [extendTrans_target]
  refine ((contMDiffOn_extend_symm hc).comp hΨ.contMDiff.contMDiffOn
    (s := Ψ.symm ⁻¹' (I.symm ⁻¹' c.target)) (fun v hv ↦
      ⟨I.symm (Ψ.symm v), hv, I.right_inv (by rw [I.range_eq_univ]; trivial)⟩)).congr
        fun v _ ↦ ?_
  simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe_symm,
    extendTrans_symm_apply]

end OpenPartialHomeomorph
