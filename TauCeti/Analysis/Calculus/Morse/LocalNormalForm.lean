/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.NormalForm
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# The Morse lemma for a locally smooth function

`TauCeti.IsNondegenerateCriticalPoint.exists_morse_chart` puts a globally smooth function in
quadratic normal form near a nondegenerate critical point. The normal form only depends on the
function near the point, and this file states it for a function that is smooth on an open
neighbourhood of the critical point only. This is the form in which the Morse lemma applies to the
coordinate expressions of a function on a manifold, which are only defined on chart targets.

## Main declarations

* `TauCeti.IsNondegenerateCriticalPoint.exists_morse_chart_of_contDiffOn`: the Morse lemma for a
  function smooth on an open neighbourhood of a nondegenerate critical point, with a chart whose
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

/-- **The Morse lemma for a locally smooth function.** If `g` is smooth on an open neighbourhood
`U` of a nondegenerate critical point `a`, there is a chart `ψ` with source in `U`, sending `a` to
`0`, smooth in both directions, on whose source `g` is its Hessian quadratic form read in the
chart. -/
theorem IsNondegenerateCriticalPoint.exists_morse_chart_of_contDiffOn (hU : IsOpen U)
    (haU : a ∈ U) (hg : ContDiffOn ℝ ∞ g U) (h : IsNondegenerateCriticalPoint g a) :
    ∃ ψ : OpenPartialHomeomorph E E, ψ.source ⊆ U ∧ a ∈ ψ.source ∧ ψ a = 0 ∧
      ContDiffOn ℝ ∞ ψ ψ.source ∧ ContDiffOn ℝ ∞ ψ.symm ψ.target ∧
      ∀ y ∈ ψ.source, g y = g a + (2 : ℝ)⁻¹ * fderiv ℝ (fderiv ℝ g) a (ψ y) (ψ y) := by
  obtain ⟨χ, hχ, -, hχ1, -, hχU⟩ :=
    isCompact_singleton.exists_contDiff_cutoff hU (singleton_subset_iff.2 haU)
  set V := interior (χ ⁻¹' {1})
  have hVopen : IsOpen V := isOpen_interior
  have haV : a ∈ V := hχ1 rfl
  have hχV : ∀ y ∈ V, χ y = 1 := fun y hy ↦ by simpa using interior_subset hy
  set G : E → ℝ := fun y ↦ χ y * g y with hGdef
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · exact hχ.contDiffAt.mul ((hg y hy).contDiffAt (hU.mem_nhds hy))
    · have h0 : G =ᶠ[𝓝 y] fun _ ↦ 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 fun hy' ↦ hy (hχU hy')] with z hz
        simp [hGdef, hz]
      exact contDiffAt_const.congr_of_eventuallyEq h0
  have hGV : ∀ y ∈ V, G y = g y := fun y hy ↦ by simp [hGdef, hχV y hy]
  have hGg : G =ᶠ[𝓝 a] g := Filter.eventuallyEq_of_mem (hVopen.mem_nhds haV) hGV
  obtain ⟨φ, haφ, hφa, hφ, hφsymm, hφG⟩ :=
    (h.congr_of_eventuallyEq hGg.symm).exists_morse_chart hG
  have hD : fderiv ℝ (fderiv ℝ G) a = fderiv ℝ (fderiv ℝ g) a := hGg.fderiv.fderiv_eq
  refine ⟨φ.restrOpen (V ∩ U) (hVopen.inter hU), ?_, ?_, hφa, ?_, ?_, ?_⟩
  · intro y hy
    rw [OpenPartialHomeomorph.restrOpen_source] at hy
    exact hy.2.2
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨haφ, haV, haU⟩
  · exact hφ.mono (by simp)
  · exact hφsymm.mono fun y hy ↦ hy.1
  · intro y hy
    rw [OpenPartialHomeomorph.restrOpen_source] at hy
    rw [← hGV y hy.2.1, ← hGV a haV, ← hD]
    exact hφG y hy.1

end TauCeti
