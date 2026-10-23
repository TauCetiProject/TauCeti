/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.BoundaryChain.Basic
public import TauCeti.Analysis.Green.GraphIntegral
public import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Mul
import TauCeti.Topology.Path.Extend.Basic

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
    have hreverse : DifferentiableAt ℝ (fun t : ℝ ↦ 1 - t) t := by fun_prop
    have hp := (hd (1 - t) hm).comp t hreverse
    simpa only [Function.comp_def, Path.extend_symm_apply] using hp

/-- The left piece of an actual joined graph arc inherits its geometric and countable
coordinate-regularity certificate. -/
theorem GraphArc.trans_left {d : Coordinate} {g : ℝ → ℝ} {a b : ℝ} {p q r : ℂ}
    {γ : Path p q} {δ : Path q r} (h : GraphArc d g a b ⟨p, r, γ.trans δ⟩) :
    GraphArc d g a b ⟨p, q, γ⟩ := by
  have hscale (x : ℝ) : 2 * (x / 2) = x := by ring
  have hhalf (t : unitInterval) : (t : ℝ) / 2 ∈ Icc 0 1 :=
    ⟨by linarith [t.property.1], by linarith [t.property.2]⟩
  have he (t : unitInterval) : (γ.trans δ).extend ((t : ℝ) / 2) = γ t := by
    rw [γ.extend_trans_of_le_half δ (by linarith [t.property.2]), hscale,
      γ.extend_apply t.property]
  refine ⟨h.continuous_graph, h.differentiable_graph, ?_, ?_, ?_⟩
  · intro t
    have hh := h.on_graph ⟨(t : ℝ) / 2, hhalf t⟩
    rw [← Path.extend_apply _ (hhalf t), he t] at hh
    exact hh
  · intro t
    have hh := h.coordinate_mem ⟨(t : ℝ) / 2, hhalf t⟩
    rw [← Path.extend_apply _ (hhalf t), he t] at hh
    exact hh
  · obtain ⟨s, hs, hd⟩ := h.differentiable_coordinate
    refine ⟨(fun t : ℝ ↦ 2 * t) '' s, hs.image _, ?_⟩
    intro t ht
    have hn : t / 2 ∉ s := fun hm ↦ ht.2 ⟨t / 2, hm, by ring⟩
    have hh := (hd (t / 2) ⟨⟨by linarith [ht.1.1], by linarith [ht.1.2]⟩, hn⟩).comp t
      (differentiableAt_id.div_const (2 : ℝ))
    have he' := (γ.eventuallyEq_extend_trans_of_lt_half δ
      (by linarith [ht.1.2] : t / 2 < 1 / 2)).comp_tendsto
        (continuousAt_id.div_const (2 : ℝ))
    apply hh.congr_of_eventuallyEq
    filter_upwards [he'] with x hx
    simpa only [Function.comp_apply, id_eq, hscale] using (congrArg d.proj hx).symm

/-- The right piece of a joined graph arc inherits its graph certificate. -/
theorem GraphArc.trans_right {d : Coordinate} {g : ℝ → ℝ} {a b : ℝ} {p q r : ℂ}
    {γ : Path p q} {δ : Path q r} (h : GraphArc d g a b ⟨p, r, γ.trans δ⟩) :
    GraphArc d g a b ⟨q, r, δ⟩ := by
  have hh : GraphArc d g a b ⟨r, p, δ.symm.trans γ.symm⟩ := by
    simpa only [Path.trans_symm] using h.symm
  simpa only [Path.symm_symm] using hh.trans_left.symm

/-- Constant selected-coordinate certificates restrict to both pieces of an actual join,
and conversely the two piece certificates imply the whole-arc certificate. -/
theorem coordinate_constant_trans_iff (d : Coordinate) {p q r : ℂ}
    (γ : Path p q) (δ : Path q r) :
    (∀ t : unitInterval, d.proj (γ.trans δ t) = d.proj p) ↔
      (∀ t : unitInterval, d.proj (γ t) = d.proj p) ∧
      (∀ t : unitInterval, d.proj (δ t) = d.proj q) := by
  constructor
  · intro h
    have hr (z : ℂ) (hz : z ∈ range (γ.trans δ)) : d.proj z = d.proj p := by
      obtain ⟨t, rfl⟩ := hz
      exact h t
    have hγ (t : unitInterval) : d.proj (γ t) = d.proj p :=
      hr _ (by rw [Path.trans_range]; exact Or.inl (mem_range_self t))
    refine ⟨hγ, fun t ↦ ?_⟩
    have hq : d.proj q = d.proj p := by simpa only [γ.target] using hγ 1
    exact (hr _ (by rw [Path.trans_range]; exact Or.inr (mem_range_self t))).trans hq.symm
  · rintro ⟨hγ, hδ⟩ t
    have hq : d.proj q = d.proj p := by simpa only [γ.target] using hγ 1
    have hm := mem_range_self t (f := γ.trans δ)
    rw [Path.trans_range] at hm
    rcases hm with ⟨u, hu⟩ | ⟨u, hu⟩
    · exact hu ▸ hγ u
    · exact hu ▸ (hδ u).trans hq

/-- The constant endpoint extension still lies on the same graph. -/
theorem GraphArc.extend_eq {d : Coordinate} {g : ℝ → ℝ} {a b : ℝ} {γ : Arc}
    (h : GraphArc d g a b γ) (t : ℝ) :
    γ.2.2.extend t = d.graph g (d.proj (γ.2.2.extend t)) := by
  exact (γ.2.2.forall_extend_iff (P := fun z ↦ z = d.graph g (d.proj z))).mpr h.on_graph t

/-- The graph coordinate of the initial endpoint lies in the base interval. -/
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
    BoxIntegral.HasIntegral (TauCeti.BoxIntegral.intervalBox 0 1 zero_lt_one)
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
  have hi := hasHenstockIntervalIntegral_graph_reparam d (a := 0) (b := 1)
    (θ := fun t ↦ d.proj (γ.2.2.extend t))
    (θ' := deriv (fun t ↦ d.proj (γ.2.2.extend t))) hs hS h.continuous_graph hdg hP
    (by simpa only [uIcc_of_le zero_le_one] using hθ)
    (by simpa only [uIoo_of_le zero_le_one] using hdθ')
    (by simpa only [uIcc_of_le zero_le_one] using hmap)
  rw [TauCeti.BoxIntegral.hasHenstockIntervalIntegral_iff_of_lt zero_lt_one] at hi
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
