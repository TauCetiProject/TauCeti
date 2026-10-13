/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.BoundaryChain.Basic
public import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Calculus.Deriv.AffineMap

/-!
# Graph certificates for path integrals

A graph certificate records the trace and regularity of a path, independently of any field
or integral value. Either real coordinate can be the graph parameter. The parameter may
backtrack or have unbounded speed. The resulting coordinate integral is the ordinary
base-interval integral, by Henstock substitution.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

namespace BoundaryChain

/-- The graph path with affine base coordinate from `a` to `b`, in either orientation. -/
def graphPath (d : Coordinate) (g : ℝ → ℝ) (a b : ℝ)
    (hg : ContinuousOn g (uIcc a b)) : Path (d.graph g a) (d.graph g b) :=
  Path.ofLine ((d.continuousOn_graph hg).comp (by fun_prop)
    ((convex_uIcc a b).mapsTo_lineMap left_mem_uIcc right_mem_uIcc))
    (by simp) (by simp)

@[simp]
theorem graphPath_apply (d : Coordinate) (g : ℝ → ℝ) (a b : ℝ)
    (hg : ContinuousOn g (uIcc a b)) (t : unitInterval) :
    graphPath d g a b hg t = d.graph g (AffineMap.lineMap a b (t : ℝ)) := (rfl)

/-- A constant graph with affine base parametrization is exactly the existing straight path. -/
@[simp]
theorem graphPath_const (d : Coordinate) (c a b : ℝ) :
    graphPath d (fun _ ↦ c) a b continuousOn_const =
      Path.segment (d.graph (fun _ ↦ c) a) (d.graph (fun _ ↦ c) b) := by
  ext t
  cases d <;> apply Complex.ext <;>
    simp [graphPath_apply, Path.segment_apply, AffineMap.lineMap_apply_module] <;> ring

/-- A path on a regular graph, with a continuous graph coordinate differentiable outside
countably many exceptions. These are geometric and differential conditions only. -/
structure GraphArc (d : Coordinate) (g : ℝ → ℝ) (a b : ℝ) (γ : Arc) : Prop where
  continuous_graph : ContinuousOn g (Icc a b)
  differentiable_graph : ∃ S : Set ℝ, S.Countable ∧
    ∀ t ∈ Ioo a b \ S, DifferentiableAt ℝ g t
  on_graph : ∀ t : unitInterval, γ.2.2 t = d.graph g (d.proj (γ.2.2 t))
  coordinate_mem : ∀ t : unitInterval, d.proj (γ.2.2 t) ∈ Icc a b
  differentiable_coordinate : ∃ S : Set ℝ, S.Countable ∧
    ∀ t ∈ Ioo 0 1 \ S, DifferentiableAt ℝ (fun t ↦ d.proj (γ.2.2.extend t)) t

/-- Affinely parametrized graph paths give graph certificates for every subinterval and
for both orientations. This includes nonconstant arcs on nonsmooth continuous graphs. -/
theorem graphArc_graphPath (d : Coordinate) {g : ℝ → ℝ} {a b c e : ℝ}
    (hg : ContinuousOn g (Icc c e))
    (hdg : ∃ S : Set ℝ, S.Countable ∧ ∀ t ∈ Ioo c e \ S, DifferentiableAt ℝ g t)
    (ha : a ∈ Icc c e) (hb : b ∈ Icc c e) :
    GraphArc d g c e ⟨_, _, graphPath d g a b (hg.mono (uIcc_subset_Icc ha hb))⟩ where
  continuous_graph := hg
  differentiable_graph := hdg
  on_graph t := by simp
  coordinate_mem t := by
    simpa using (convex_Icc c e).lineMap_mem ha hb t.2
  differentiable_coordinate := by
    refine ⟨∅, countable_empty, ?_⟩
    intro t ht
    apply (AffineMap.hasDerivAt_lineMap (a := a) (b := b) (x := t)).differentiableAt
      |>.congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds ht.1.1 ht.1.2] with u hu
    simp [Path.extend_apply _ hu]

/-- Reversal preserves a graph certificate and reverses its endpoint order. -/
theorem GraphArc.symm {d : Coordinate} {g : ℝ → ℝ} {a b : ℝ} {p q : ℂ}
    {γ : Path p q} (h : GraphArc d g a b ⟨p, q, γ⟩) :
    GraphArc d g a b ⟨q, p, γ.symm⟩ where
  continuous_graph := h.continuous_graph
  differentiable_graph := h.differentiable_graph
  on_graph t := by
    simpa only [Path.symm_apply, Function.comp_apply] using h.on_graph (unitInterval.symm t)
  coordinate_mem t := by
    simpa only [Path.symm_apply, Function.comp_apply] using h.coordinate_mem (unitInterval.symm t)
  differentiable_coordinate := by
    obtain ⟨S, hS, hd⟩ := h.differentiable_coordinate
    refine ⟨(fun t : ℝ ↦ 1 - t) '' S, hS.image _, ?_⟩
    intro t ht
    have hs : 1 - t ∉ S := by
      intro hm
      exact ht.2 ⟨1 - t, hm, by ring⟩
    have hm : 1 - t ∈ Ioo 0 1 \ S := ⟨⟨by linarith [ht.1.2], by linarith [ht.1.1]⟩, hs⟩
    have hp := (hd (1 - t) hm).comp t
      (show DifferentiableAt ℝ (fun t : ℝ ↦ 1 - t) t by fun_prop)
    simpa only [Function.comp_def, Path.extend_symm_apply] using hp

/-- The constant endpoint extension still lies on the same graph. -/
theorem GraphArc.extend_eq {d : Coordinate} {g : ℝ → ℝ} {a b : ℝ} {γ : Arc}
    (h : GraphArc d g a b γ) (t : ℝ) :
    γ.2.2.extend t = d.graph g (d.proj (γ.2.2.extend t)) := by
  obtain ⟨u, hu⟩ := (γ.2.2.extend_range ▸ mem_range_self t : γ.2.2.extend t ∈ range γ.2.2)
  rw [← hu]
  exact h.on_graph u

/-- The graph coordinate of either endpoint lies in the base interval. -/
theorem GraphArc.source_mem {d : Coordinate} {g : ℝ → ℝ} {a b : ℝ} {γ : Arc}
    (h : GraphArc d g a b γ) : d.proj γ.1 ∈ Icc a b := by
  simpa using h.coordinate_mem 0

/-- The graph coordinate of the terminal endpoint lies in the base interval. -/
theorem GraphArc.target_mem {d : Coordinate} {g : ℝ → ℝ} {a b : ℝ} {γ : Arc}
    (h : GraphArc d g a b γ) : d.proj γ.2.1 ∈ Icc a b := by
  simpa using h.coordinate_mem 1

/-- A graph certificate gives the genuine Henstock integral, including backtracking. -/
theorem GraphArc.hasIntegral {d : Coordinate} {g : ℝ → ℝ} {a b : ℝ} {γ : Arc}
    (h : GraphArc d g a b γ) {P : ℂ → ℝ}
    (hP : ContinuousOn P (d.graph g '' Icc a b)) :
    BoxIntegral.HasIntegral (BoxIntegral.intervalBox 0 1 zero_lt_one)
      BoxIntegral.IntegrationParams.Henstock
      (fun t ↦ P (γ.2.2.extend (t 0)) * d.proj (deriv γ.2.2.extend (t 0)))
      BoxIntegral.BoxAdditiveMap.volume (∫ t in d.proj γ.1..d.proj γ.2.1, P (d.graph g t)) := by
  obtain ⟨S, hS, hdg⟩ := h.differentiable_graph
  obtain ⟨s, hs, hdθ⟩ := h.differentiable_coordinate
  have hθ : ContinuousOn (fun t ↦ d.proj (γ.2.2.extend t)) (Icc 0 1) := by fun_prop
  have hmap : MapsTo (fun t ↦ d.proj (γ.2.2.extend t)) (Icc 0 1) (Icc a b) := by
    intro t ht
    simpa only [Path.extend_apply _ ht] using h.coordinate_mem ⟨t, ht⟩
  have heq : (γ.2.2.extend : ℝ → ℂ) = d.graph g ∘ (fun t ↦ d.proj (γ.2.2.extend t)) :=
    funext h.extend_eq
  have hdθ' := fun t ht ↦ (hdθ t ht).hasDerivAt
  have hi := hasIntervalIntegral_graph_reparam d (a := 0) (b := 1)
    (θ := fun t ↦ d.proj (γ.2.2.extend t))
    (θ' := deriv (fun t ↦ d.proj (γ.2.2.extend t))) hs hS h.continuous_graph hdg hP
    (by simpa only [uIcc_of_le zero_le_one] using hθ)
    (by simpa only [uIoo_of_le zero_le_one] using hdθ')
    (by simpa only [uIcc_of_le zero_le_one] using hmap)
  rw [BoxIntegral.hasIntervalIntegral_iff_of_lt zero_lt_one] at hi
  rw [← heq] at hi
  have hp := h.extend_eq
  simpa only [← hp, Path.extend_zero, Path.extend_one] using hi

/-- Graph arcs have the required chain integrability witness. -/
theorem GraphArc.integrable {d : Coordinate} {g : ℝ → ℝ} {a b : ℝ} {γ : Arc}
    (h : GraphArc d g a b γ) {P : ℂ → ℝ}
    (hP : ContinuousOn P (d.graph g '' Icc a b)) :
    Integrable d.proj P (ofPath γ.2.2) :=
  (integrable_ofPath_iff _ _ _).2 (h.hasIntegral hP).integrable

/-- The coordinate integral of a certified graph arc depends only on its endpoints. -/
theorem GraphArc.arcIntegral_eq {d : Coordinate} {g : ℝ → ℝ} {a b : ℝ} {γ : Arc}
    (h : GraphArc d g a b γ) {P : ℂ → ℝ}
    (hP : ContinuousOn P (d.graph g '' Icc a b)) :
    arcIntegral d.proj P γ = ∫ t in d.proj γ.1..d.proj γ.2.1, P (d.graph g t) :=
  by rw [arcIntegral_def]; exact (h.hasIntegral hP).integral_eq

end BoundaryChain
end TauCeti.Green
