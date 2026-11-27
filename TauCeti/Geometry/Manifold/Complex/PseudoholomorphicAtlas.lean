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

`MDifferentiableOn.differentiableOn_symm_trans_of_isPseudoholomorphicAt`
proves that two real charts straightening the same almost complex structure have a holomorphic
transition. It uses `OpenPartialHomeomorph.MDifferentiable.isPseudoholomorphicAt_symm`
and the comparison between pseudoholomorphic and holomorphic maps.

`Homeomorph.isManifold_of_isPseudoholomorphicAt` applies this transition theorem to an atlas
transported by a homeomorphism. Finite-dimensional complex differentiability implies analyticity
by `DifferentiableOn.contDiffOn_of_finiteDimensional`.
-/

public section

open TauCeti TauCeti.SmoothAlmostComplexStructure
open scoped ContDiff Manifold

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V] {J : SmoothAlmostComplexStructure I M}

/-- The transition from a chart with real differentiable inverse to a second chart is
holomorphic if both charts carry the same almost complex structure `J` to multiplication by `i`
on their sources. -/
theorem MDifferentiableOn.differentiableOn_symm_trans_of_isPseudoholomorphicAt
    {e e' : OpenPartialHomeomorph M V}
    (he : MDifferentiableOn 𝓘(ℝ, V) I e.symm e.target)
    (h : ∀ x ∈ e.source, IsPseudoholomorphicAt J (ofComplexManifold V V) e x)
    (h' : ∀ x ∈ e'.source, IsPseudoholomorphicAt J (ofComplexManifold V V) e' x) :
    DifferentiableOn ℂ (e.symm.trans e') (e.symm.trans e').source := by
  intro z hz
  obtain ⟨hze, hze'⟩ := OpenPartialHomeomorph.mem_target_and_mem_source_of_mem_symm_trans_source hz
  have hed : e.MDifferentiable I 𝓘(ℝ, V) :=
    ⟨fun x hx ↦ (h x hx).mdifferentiableAt.mdifferentiableWithinAt, he⟩
  have hinv := hed.isPseudoholomorphicAt_symm hze (h _ (e.map_target hze))
  have hcomp := (h' _ hze').comp hinv
  rw [isPseudoholomorphicAt_ofComplexManifold_iff, mdifferentiableAt_iff_differentiableAt] at hcomp
  exact hcomp.differentiableWithinAt

/-- An atlas transported from real charts by a homeomorphism is complex analytic if the real
charts have differentiable inverses and carry the same almost complex structure `J` to
multiplication by `i`. The charted space on `N` need not already be a manifold. -/
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
