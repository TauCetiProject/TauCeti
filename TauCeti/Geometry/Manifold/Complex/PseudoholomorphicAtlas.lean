/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Topology.OpenPartialHomeomorph.Composition

/-!
# Complex atlases from pseudoholomorphic charts

`Homeomorph.isManifold_of_isPseudoholomorphicAt` generalizes the isothermal atlas construction
`IsothermalSurface.instIsManifold` from `Complex/Isothermal.lean` to finite-dimensional complex
models. It applies `MDifferentiableOn.differentiableOn_symm_trans_of_isPseudoholomorphicAt` to
the charts of an atlas transported by a homeomorphism. Complex differentiability on the open
chart overlaps gives analytic transitions by `DifferentiableOn.contDiffOn_of_finiteDimensional`.
Mathlib's `isManifold_of_contDiffOn` then gives the analytic manifold structure.
-/

public section

open TauCeti TauCeti.SmoothAlmostComplexStructure
open scoped ContDiff Manifold

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V] {J : SmoothAlmostComplexStructure I M}

/-- For a finite-dimensional complex model `V`, an atlas transported from real charts by a
homeomorphism is complex analytic if the real charts have differentiable inverses and carry the
same almost complex structure `J` to multiplication by `i`. The charted space on `N` need not
already be a manifold. -/
theorem Homeomorph.isManifold_of_isPseudoholomorphicAt
    {N : Type*} [TopologicalSpace N] [ChartedSpace V N] [FiniteDimensional ℂ V]
    (f : N ≃ₜ M)
    (h : ∀ c ∈ atlas V N, ∃ e : OpenPartialHomeomorph M V,
      c = f.transOpenPartialHomeomorph e ∧ MDifferentiableOn 𝓘(ℝ, V) I e.symm e.target ∧
        ∀ x ∈ e.source, IsPseudoholomorphicAt J (ofComplexManifold V V) e x) :
    IsManifold 𝓘(ℂ, V) ω N := by
  refine isManifold_of_contDiffOn 𝓘(ℂ, V) ω N fun c c' hc hc' ↦ ?_
  obtain ⟨e, rfl, he, heJ⟩ := h c hc
  obtain ⟨e', rfl, -, he'J⟩ := h c' hc'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
    Set.inter_univ, Set.preimage_id_eq, CompTriple.comp_eq,
    Homeomorph.transOpenPartialHomeomorph_symm_trans]
  exact (he.differentiableOn_symm_trans_of_isPseudoholomorphicAt heJ he'J)
    |>.contDiffOn_of_finiteDimensional (e.symm.trans e').open_source
