/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import TauCeti.Geometry.Manifold.Morse.Index
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Analysis.Calculus.Morse.Index
import TauCeti.Analysis.Calculus.Morse.NormalForm

/-!
# The Morse lemma on a smooth manifold

At a nondegenerate critical point `x` of a smooth function `f` on a boundaryless smooth manifold
modelled on a finite-dimensional real inner product space `E`, there is a chart of the maximal
atlas, centred at `x`, in which `f` is a nondegenerate quadratic form: after a linear change of
coordinates `L : E ≃ (Fin n → ℝ)`,

`f y = f x + (1/2) Σᵢ wᵢ (L (ψ y))ᵢ²`, with every `wᵢ = ±1`,

and the number of negative weights is the manifold Morse index of `f` at `x`.

The proof reads `f` in the preferred extended chart at `x`. The coordinate expression is smooth
only on the chart target, while the normed-space Morse lemma
`TauCeti.IsNondegenerateCriticalPoint.exists_morse_chart` is stated for globally smooth functions,
so the coordinate expression is first multiplied by a smooth bump function equal to `1` near the
critical point. The normed-space Morse chart of the product, restricted to the region where the
bump function is `1`, is then composed with the preferred chart. Sylvester's law of inertia
(`TauCeti.IsNondegenerateCriticalPoint.exists_hessianQuadraticForm_equivalent_weightedSumSquares`)
diagonalizes the Hessian.

## Main declarations

* `TauCeti.IsNondegenerateCriticalPoint.exists_morse_chart_of_contDiffOn`: the normed-space Morse
  lemma for a function that is smooth only on an open neighbourhood of the critical point.
* `TauCeti.MorseChart`: a chart centred at a critical point in which the function is a diagonal
  nondegenerate quadratic form.
* `TauCeti.IsManifoldNondegenerateCriticalPoint.nonempty_morseChart`: the Morse lemma on a
  manifold.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Theorem 1.3.1.
-/

public section

open Function Metric Set Topology
open scoped ContDiff Manifold

namespace TauCeti

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
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
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 hU a haU
  let b : ContDiffBump a := ⟨R / 4, R / 2, by positivity, by linarith⟩
  set G : E → ℝ := fun y ↦ b y * g y with hGdef
  have hball : closedBall a (R / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hRU
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · exact (b.contDiff.contDiffAt).mul ((hg y hy).contDiffAt (hU.mem_nhds hy))
    · have hyb : y ∉ tsupport b := by
        rw [b.tsupport_eq]
        exact fun hy' ↦ hy (hball hy')
      have h0 : G =ᶠ[𝓝 y] fun _ ↦ 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hyb] with z hz
        simp [hGdef, hz]
      exact (contDiffAt_const).congr_of_eventuallyEq h0
  have hGg : G =ᶠ[𝓝 a] g := by
    filter_upwards [ball_mem_nhds a (show (0 : ℝ) < R / 4 by positivity)] with z hz
    simp [hGdef, b.one_of_mem_closedBall (ball_subset_closedBall hz)]
  obtain ⟨φ, haφ, hφa, hφ, hφsymm, hφG⟩ :=
    (h.congr_of_eventuallyEq hGg.symm).exists_morse_chart hG
  have hD : fderiv ℝ (fderiv ℝ G) a = fderiv ℝ (fderiv ℝ g) a :=
    hGg.fderiv.fderiv_eq
  refine ⟨φ.restrOpen (ball a (R / 4)) isOpen_ball, ?_, ?_, hφa, ?_, ?_, ?_⟩
  · intro y hy
    rw [OpenPartialHomeomorph.restrOpen_source] at hy
    exact hRU (ball_subset_ball (by linarith) hy.2)
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨haφ, mem_ball_self (by positivity)⟩
  · exact hφ.mono (by simp)
  · exact hφsymm.mono fun y hy ↦ hy.1
  · intro y hy
    rw [OpenPartialHomeomorph.restrOpen_source] at hy
    have hyG : G y = g y := by
      simp [hGdef, b.one_of_mem_closedBall (ball_subset_closedBall hy.2)]
    have haG : G a = g a := hGg.eq_of_nhds
    rw [← hyG, ← haG, ← hD]
    exact hφG y hy.1

end NormedSpace

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
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
  weight_eq : ∀ i, weight i = -1 ∨ weight i = 1
  ncard_weight_neg : {i | weight i < 0}.ncard = manifoldMorseIndex 𝓘(ℝ, E) f x
  eq_quadratic : ∀ y ∈ toChart.source,
    f y = f x + (2 : ℝ)⁻¹ * ∑ i, weight i * (coord (toChart y) i) ^ 2

/-- **The Morse lemma on a manifold.** At a nondegenerate critical point `x` of a smooth function
`f` on a manifold modelled on a finite-dimensional real inner product space `E`, there is a Morse
chart: a chart `ψ` of the maximal atlas, centred at `x`, and a linear change of coordinates
`L : E ≃ (Fin n → ℝ)` such that on the source of `ψ`

`f y = f x + (1/2) Σᵢ wᵢ (L (ψ y))ᵢ²`,

where every weight `wᵢ` is `-1` or `1` and the number of negative weights is the manifold Morse
index of `f` at `x`. -/
theorem IsManifoldNondegenerateCriticalPoint.nonempty_morseChart
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (h : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x) : Nonempty (MorseChart E f x) := by
  set c := chartAt E x with hc
  set g : E → ℝ := f ∘ (extChartAt 𝓘(ℝ, E) x).symm with hgdef
  set a : E := extChartAt 𝓘(ℝ, E) x x with hadef
  have hU : IsOpen (extChartAt 𝓘(ℝ, E) x).target := isOpen_extChartAt_target x
  have haU : a ∈ (extChartAt 𝓘(ℝ, E) x).target := mem_extChartAt_target x
  have hg : ContDiffOn ℝ ∞ g (extChartAt 𝓘(ℝ, E) x).target :=
    (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm x)).contDiffOn
  have h' : IsNondegenerateCriticalPoint g a := (isManifoldNondegenerateCriticalPoint_iff _).1 h
  obtain ⟨φ, -, haφ, hφa, hφ, hφsymm, hφg⟩ :=
    h'.exists_morse_chart_of_contDiffOn hU haU hg
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
  · exact ⟨hxc, show c x ∈ φ.source by rw [hca]; exact haφ⟩
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

end Manifold

end TauCeti
