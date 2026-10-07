/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Index
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Analysis.Calculus.Morse.LocalNormalForm
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# The Morse lemma on a smooth manifold

At a nondegenerate critical point `x` of a smooth function `f` on a boundaryless smooth manifold
modelled on a finite-dimensional real normed space `E`, there is a chart of the maximal atlas,
centred at `x`, in which `f` is a nondegenerate quadratic form: after a linear change of
coordinates `L : E ≃ (Fin n → ℝ)`,

`f y = f x + (1/2) Σᵢ wᵢ (L (ψ y))ᵢ²`, with every `wᵢ = ±1`,

and the number of negative weights is the manifold Morse index of `f` at `x`. Such a chart is
recorded as a `TauCeti.MorseChart`. A Morse chart puts the function in quadratic form; it is
used to choose an adapted pseudo-gradient field that is linear near the critical point, whose
stable and unstable manifolds are then studied.

## Main declarations

* `TauCeti.MorseChart`: a chart centred at a critical point in which the function is a diagonal
  nondegenerate quadratic form.
* `TauCeti.MorseChart.restr`: the restriction of a Morse chart to an open neighbourhood of its
  centre.
* `TauCeti.IsManifoldNondegenerateCriticalPoint.nonempty_morseChart`: the Morse lemma on a
  manifold, for a function smooth near the critical point.
* `TauCeti.IsMorse.nonempty_morseChart`: every critical point of a Morse function has a Morse
  chart.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Theorem 1.3.1.
-/

public section

open Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {x : M}

variable (E) in
/-- A **Morse chart** for `f` at `x`: a chart of the maximal atlas, centred at `x`, together with
a linear change of coordinates `L : E ≃ (Fin n → ℝ)` and weights `wᵢ = ±1`, such that on the source
of the chart `f y = f x + (1/2) Σᵢ wᵢ (L (ψ y))ᵢ²`. The number of negative weights is the manifold
Morse index of `f` at `x`. -/
structure MorseChart (f : M → ℝ) (x : M) where
  /-- The chart. -/
  toChart : OpenPartialHomeomorph M E
  mem_maximalAtlas : toChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M
  mem_source : x ∈ toChart.source
  apply_self : toChart x = 0
  /-- The linear change of coordinates that diagonalizes the Hessian. -/
  coord : E ≃ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ)
  /-- The diagonal weights of the Hessian. -/
  weight : Fin (Module.finrank ℝ E) → ℝ
  weight_eq_neg_one_or_eq_one : ∀ i, weight i = -1 ∨ weight i = 1
  ncard_weight_neg : {i | weight i < 0}.ncard = manifoldMorseIndex 𝓘(ℝ, E) f x
  eq_quadratic : ∀ y ∈ toChart.source,
    f y = f x + (2 : ℝ)⁻¹ * ∑ i, weight i * (coord (toChart y) i) ^ 2

attribute [simp] MorseChart.mem_source MorseChart.apply_self

namespace MorseChart

/-- The restriction of a Morse chart to an open neighbourhood `s` of its centre: the chart is
restricted to `s`, and the coordinates and weights are unchanged. -/
noncomputable def restr (φ : MorseChart E f x) {s : Set M} (hs : IsOpen s) (hx : x ∈ s) :
    MorseChart E f x where
  toChart := φ.toChart.restr s
  mem_maximalAtlas := restr_mem_maximalAtlas _ φ.mem_maximalAtlas hs
  mem_source := by rw [φ.toChart.restr_source' s hs]; exact ⟨φ.mem_source, hx⟩
  apply_self := φ.apply_self
  coord := φ.coord
  weight := φ.weight
  weight_eq_neg_one_or_eq_one := φ.weight_eq_neg_one_or_eq_one
  ncard_weight_neg := φ.ncard_weight_neg
  eq_quadratic y hy := φ.eq_quadratic y (by rw [φ.toChart.restr_source' s hs] at hy; exact hy.1)

variable (φ : MorseChart E f x) {s : Set M} (hs : IsOpen s) (hx : x ∈ s)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The chart of a restricted Morse chart is the restricted chart. -/
@[simp]
theorem restr_toChart : (φ.restr hs hx).toChart = φ.toChart.restr s := by
  rw [restr]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Restricting a Morse chart does not change its coordinates. -/
@[simp]
theorem restr_coord : (φ.restr hs hx).coord = φ.coord := by
  rw [restr]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Restricting a Morse chart does not change its weights. -/
@[simp]
theorem restr_weight : (φ.restr hs hx).weight = φ.weight := by
  rw [restr]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The source of a restricted Morse chart. -/
theorem restr_source : (φ.restr hs hx).toChart.source = φ.toChart.source ∩ s :=
  φ.toChart.restr_source' s hs

end MorseChart

/-- **The Morse lemma on a manifold.** At a nondegenerate critical point `x` of a function `f`
that is smooth at every point of a neighbourhood of `x`, on a manifold modelled on a
finite-dimensional real normed space `E`, there is a Morse chart: a chart `ψ` of the maximal atlas,
centred at `x`, and a linear change of coordinates `L : E ≃ (Fin n → ℝ)` such that on the source
of `ψ`

`f y = f x + (1/2) Σᵢ wᵢ (L (ψ y))ᵢ²`,

where every weight `wᵢ` is `-1` or `1` and the number of negative weights is the manifold Morse
index of `f` at `x`. -/
theorem IsManifoldNondegenerateCriticalPoint.nonempty_morseChart
    (hf : ∀ᶠ y in 𝓝 x, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞ f y)
    (h : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x) : Nonempty (MorseChart E f x) := by
  obtain ⟨s, hfs, hsopen, hxs⟩ := _root_.eventually_nhds_iff.1 hf
  have hs : s ∈ 𝓝 x := hsopen.mem_nhds hxs
  replace hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ f s := fun y hy ↦ (hfs y hy).contMDiffWithinAt
  set c := chartAt E x with hc
  set g : E → ℝ := f ∘ (extChartAt 𝓘(ℝ, E) x).symm with hgdef
  set a : E := extChartAt 𝓘(ℝ, E) x x with hadef
  set U := (extChartAt 𝓘(ℝ, E) x).target ∩ (extChartAt 𝓘(ℝ, E) x).symm ⁻¹' interior s
    with hUdef
  have hU : IsOpen U := (continuousOn_extChartAt_symm x).isOpen_inter_preimage
    (isOpen_extChartAt_target x) isOpen_interior
  have haU : a ∈ U := ⟨mem_extChartAt_target x, by
    rw [mem_preimage, extChartAt_to_inv]
    exact mem_interior_iff_mem_nhds.2 hs⟩
  have hg : ContDiffOn ℝ ∞ g U :=
    ((hf.mono interior_subset).comp ((contMDiffOn_extChartAt_symm x).mono inter_subset_left)
      fun _ hz ↦ hz.2).contDiffOn
  have h' : IsNondegenerateCriticalPoint g a := (isManifoldNondegenerateCriticalPoint_iff _).1 h
  obtain ⟨φ, -, haφ, hφa, hφ, hφsymm, hφg⟩ :=
    h'.exists_morse_chart_of_contDiffOn (hU.mem_nhds haU) hg
  obtain ⟨w, hw, ⟨e⟩⟩ := h'.exists_hessianQuadraticForm_equivalent_weightedSumSquares
  have hext : ∀ y, extChartAt 𝓘(ℝ, E) x y = c y := fun y ↦ by simp [hc]
  have hleft : ∀ y ∈ c.source, g (c y) = f y := fun y hy ↦ by
    have hy' : y ∈ (extChartAt 𝓘(ℝ, E) x).source := by simpa [hc] using hy
    simp only [hgdef, comp_apply, ← hext, (extChartAt 𝓘(ℝ, E) x).left_inv hy']
  have hxc : x ∈ c.source := mem_chart_source E x
  have hca : c x = a := (hext x).symm
  refine ⟨⟨c.trans φ, ?_, ?_, ?_, e.toLinearEquiv, w, hw, ?_, ?_⟩⟩
  · rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
    constructor
    · exact hφ.contMDiffOn.comp (contMDiffOn_chart.mono fun y hy ↦ hy.1) fun y hy ↦ hy.2
    · exact contMDiffOn_chart_symm.comp (hφsymm.contMDiffOn.mono fun y hy ↦ hy.1)
        fun y hy ↦ hy.2
  · refine ⟨hxc, ?_⟩
    rw [mem_preimage, OpenPartialHomeomorph.symm_symm, hca]
    exact haφ
  · simp [hca, hφa]
  · rw [manifoldMorseIndex_def, morseIndex_def]
    exact (QuadraticForm.sigNeg_of_equiv_weightedSumSquares ⟨e⟩).symm
  · intro y hy
    have hy1 : y ∈ c.source := hy.1
    have hy2 : c y ∈ φ.source := hy.2
    have hfx : g a = f x := by rw [← hca]; exact hleft x hxc
    rw [← hleft y hy1, hφg (c y) hy2, hfx]
    have hQ := e.map_app (φ (c y))
    rw [hessianQuadraticForm_apply] at hQ
    rw [← hQ, QuadraticMap.weightedSumSquares_apply]
    simp [sq]

/-- Every critical point of a Morse function has a Morse chart. -/
theorem IsMorse.nonempty_morseChart (hf : IsMorse 𝓘(ℝ, E) f) {x : M}
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) : Nonempty (MorseChart E f x) :=
  ((isMorse_iff.1 hf).2 x ((mfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm hf.contMDiff x).1
    hx)).nonempty_morseChart (Filter.Eventually.of_forall fun _ ↦ hf.contMDiff.contMDiffAt)

end Manifold

end TauCeti
