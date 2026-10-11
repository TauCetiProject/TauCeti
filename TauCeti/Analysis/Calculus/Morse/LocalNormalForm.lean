/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.NormalForm
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The Morse lemma for a locally smooth function

`TauCeti.IsNondegenerateCriticalPoint.exists_morse_chart` puts a globally smooth function in
quadratic normal form near a nondegenerate critical point. The normal form only depends on the
function near the point, and this file states it for a function that is smooth on a
neighbourhood of the critical point only. This is the form in which the Morse lemma applies to the
coordinate expressions of a function on a manifold, which are only defined on chart targets.

## Main declarations

* `TauCeti.IsNondegenerateCriticalPoint.exists_morse_chart_of_contDiffOn`: the Morse lemma for a
  function smooth on a neighbourhood of a nondegenerate critical point, with a chart whose
  source lies in that neighbourhood.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Theorem 1.3.1.
-/

public section

open Set Topology
open scoped ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {g : E → ℝ} {a : E} {U : Set E}

/-- **The Morse lemma for a locally smooth function.** If `g` is smooth on a neighbourhood `U` of
a nondegenerate critical point `a`, there is a chart `ψ` with source in `U`, sending `a` to `0`,
smooth in both directions, on whose source `g` is its Hessian quadratic form read in the chart. -/
theorem IsNondegenerateCriticalPoint.exists_morse_chart_of_contDiffOn (hU : U ∈ 𝓝 a)
    (hg : ContDiffOn ℝ ∞ g U) (h : IsNondegenerateCriticalPoint g a) :
    ∃ ψ : OpenPartialHomeomorph E E, ψ.source ⊆ U ∧ a ∈ ψ.source ∧ ψ a = 0 ∧
      ContDiffOn ℝ ∞ ψ ψ.source ∧ ContDiffOn ℝ ∞ ψ.symm ψ.target ∧
      ∀ y ∈ ψ.source, g y = g a + (2 : ℝ)⁻¹ * fderiv ℝ (fderiv ℝ g) a (ψ y) (ψ y) := by
  obtain ⟨G, hG, -, hGg⟩ := hg.exists_contDiff_eventuallyEq_of_finiteDimensional (n := ⊤) hU
  obtain ⟨V, hGV, hVopen, haV⟩ := _root_.eventually_nhds_iff.1 hGg
  obtain ⟨φ, haφ, hφa, hφ, hφsymm, hφG⟩ :=
    (h.congr_of_eventuallyEq hGg.symm).exists_morse_chart hG
  have hD : fderiv ℝ (fderiv ℝ G) a = fderiv ℝ (fderiv ℝ g) a := hGg.fderiv.fderiv_eq
  refine ⟨φ.restrOpen (V ∩ interior U) (hVopen.inter isOpen_interior), ?_, ?_, hφa, ?_, ?_, ?_⟩
  · intro y hy
    rw [OpenPartialHomeomorph.restrOpen_source] at hy
    exact interior_subset hy.2.2
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨haφ, haV, mem_interior_iff_mem_nhds.2 hU⟩
  · exact hφ.mono (by simp)
  · exact hφsymm.mono fun y hy ↦ hy.1
  · intro y hy
    rw [OpenPartialHomeomorph.restrOpen_source] at hy
    rw [← hGV y hy.2.1, ← hGV a haV, ← hD]
    exact hφG y hy.1

end TauCeti
