/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.Path.Extend.Basic
public import TauCeti.Analysis.Green.BoundaryChain.PiecewiseGraph
public import TauCeti.MeasureTheory.Integral.CurveIntegral.Henstock

/-!
# Geometric comparison of directional boundary chains

The comparison generators include coordinate-constant arcs, endpoint cycles on one graph,
and actual joins, reversals, and regular reparametrizations of finite graph-piece paths.
They compare original whole arcs with their pieces even when the whole arc is not a graph.
Integer sums of these geometric generators have zero coordinate integral.
Graph containment in `U` is part of the geometric certificate, so field continuity is needed
only on `U`. The two coordinates can use entirely different comparison certificates.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green.BoundaryChain

/-- The integral of a graph-supported chain is the integral primitive evaluated at its
endpoint boundary. This is the telescoping mechanism behind all graph comparisons. -/
theorem integral_eq_boundary_of_graph {d : Coordinate} {g : ℝ → ℝ} {a b : ℝ}
    {c : BoundaryChain} (hc : ∀ γ ∈ c.support, GraphArc d g a b γ) {P : ℂ → ℝ}
    (hP : ContinuousOn P (d.graph g '' Icc a b)) :
    integral d.proj P c = Finsupp.linearCombination ℤ
      (fun z : ℂ ↦ ∫ t in a..d.proj z, P (d.graph g t)) (boundary c) := by
  rw [integral_apply, boundary_apply]
  simp only [Finsupp.sum, map_sum, map_zsmul, map_sub, Finsupp.linearCombination_single, one_smul]
  apply Finset.sum_congr rfl
  intro γ hγ
  congr 1
  rw [(hc γ hγ).arcIntegral_eq hP]
  have hcont := hP.comp (d.continuousOn_graph (hc γ hγ).continuous_graph) (mapsTo_image _ _)
  have hs := (hc γ hγ).source_mem
  have ht := (hc γ hγ).target_mem
  have ha : a ∈ Icc a b := ⟨le_rfl, hs.1.trans hs.2⟩
  have h₁ := (hcont.mono (uIcc_subset_Icc ha hs)).intervalIntegrable (μ := volume)
  have h₂ := (hcont.mono (uIcc_subset_Icc hs ht)).intervalIntegrable (μ := volume)
  exact eq_sub_iff_add_eq.mpr (by
    simpa only [Function.comp_apply, add_comm] using
      intervalIntegral.integral_add_adjacent_intervals h₁ h₂)

/-- Geometric null chains for a directional integral. Graph cycles have zero endpoint
boundary; coordinate-constant arcs are ignored. The constructors contain no integral claims. -/
inductive NullChain (d : Coordinate) (U : Set ℂ) : BoundaryChain → Prop
  | zero : NullChain d U 0
  | add {c e} : NullChain d U c → NullChain d U e → NullChain d U (c + e)
  | neg {c} : NullChain d U c → NullChain d U (-c)
  | constant {p q : ℂ} (γ : Path p q) (hγ : ∀ t : unitInterval, d.proj (γ t) = d.proj p) :
      NullChain d U (ofPath γ)
  | graph {g : ℝ → ℝ} {a b : ℝ} {c : BoundaryChain}
      (hgraph : d.graph g '' Icc a b ⊆ U)
      (harcs : ∀ γ ∈ c.support, GraphArc d g a b γ) (hboundary : boundary c = 0) :
      NullChain d U c
  | join {p q r : ℂ} {γ : Path p q} {δ : Path q r}
      (hγ : PiecewiseGraphArc d U ⟨p, q, γ⟩) (hδ : PiecewiseGraphArc d U ⟨q, r, δ⟩) :
      NullChain d U (ofPath (γ.trans δ) - (ofPath γ + ofPath δ))
  | reverse {p q : ℂ} {γ : Path p q} (hγ : PiecewiseGraphArc d U ⟨p, q, γ⟩) :
      NullChain d U (ofPath γ + ofPath γ.symm)
  | reparam {p q : ℂ} {γ δ : Path p q} (hδ : PiecewiseGraphArc d U ⟨p, q, δ⟩)
      (θ : ℝ → ℝ) (h : RegularReparam θ γ δ) :
      NullChain d U (ofPath γ - ofPath δ)

private def nullChainSubgroup (d : Coordinate) (U : Set ℂ) : AddSubgroup BoundaryChain where
  carrier := {c | NullChain d U c}
  zero_mem' := .zero
  add_mem' := .add
  neg_mem' := .neg

/-- Geometric comparisons compose by actual cancellation of the intermediate chain. -/
theorem NullChain.trans {d : Coordinate} {U : Set ℂ} {c e f : BoundaryChain}
    (hce : NullChain d U (c - e)) (hef : NullChain d U (e - f)) :
    NullChain d U (c - f) := by
  convert hce.add hef using 1
  abel

/-- Integer multiplicities preserve geometric null-chain certificates. -/
theorem NullChain.zsmul {d : Coordinate} {U : Set ℂ} {c : BoundaryChain}
    (h : NullChain d U c) (n : ℤ) : NullChain d U (n • c) :=
  (nullChainSubgroup d U).zsmul_mem h n

/-- Independent geometric comparisons can be added over any finite family. -/
theorem NullChain.sum {d : Coordinate} {U : Set ℂ} {ι : Type*} (s : Finset ι)
    (c : ι → BoundaryChain) (h : ∀ i ∈ s, NullChain d U (c i)) :
    NullChain d U (∑ i ∈ s, c i) :=
  (nullChainSubgroup d U).sum_mem h

/-- Graph reparametrizations with the same endpoints represent the same directional boundary. -/
theorem NullChain.graph_reparam {d : Coordinate} {U : Set ℂ} {g : ℝ → ℝ} {a b : ℝ}
    {p q : ℂ} {γ δ : Path p q} (hγ : GraphArc d g a b ⟨p, q, γ⟩)
    (hδ : GraphArc d g a b ⟨p, q, δ⟩) (hU : d.graph g '' Icc a b ⊆ U) :
    NullChain d U (ofPath γ - ofPath δ) := by
  classical
  refine .graph hU ?_ (by simp)
  intro η hη
  have hm := Finsupp.support_sub hη
  simp only [support_ofPath, Finset.mem_union, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl
  · exact hγ
  · exact hδ

/-- Subdivision at a common endpoint preserves the directional boundary presentation. -/
theorem NullChain.graph_subdivision {d : Coordinate} {U : Set ℂ} {g : ℝ → ℝ} {a b : ℝ}
    {p q r : ℂ} {γ : Path p q} {γ₁ : Path p r} {γ₂ : Path r q}
    (hγ : GraphArc d g a b ⟨p, q, γ⟩) (h₁ : GraphArc d g a b ⟨p, r, γ₁⟩)
    (h₂ : GraphArc d g a b ⟨r, q, γ₂⟩) (hU : d.graph g '' Icc a b ⊆ U) :
    NullChain d U (ofPath γ - (ofPath γ₁ + ofPath γ₂)) := by
  classical
  refine .graph hU ?_ ?_
  · intro η hη
    rcases Finset.mem_union.mp (Finsupp.support_sub hη) with h | h
    · simp only [support_ofPath, Finset.mem_singleton] at h
      subst η
      exact hγ
    · have hm := Finsupp.support_add h
      simp only [support_ofPath, Finset.mem_union, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl
      · exact h₁
      · exact h₂
  · simp only [map_sub, map_add, boundary_ofPath]
    abel

/-- A straight segment parallel to the unused coordinate is ignored by the comparison. -/
theorem NullChain.segment {d : Coordinate} {U : Set ℂ} {p q : ℂ}
    (hpq : d.proj p = d.proj q) : NullChain d U (ofPath (Path.segment p q)) := by
  apply NullChain.constant
  intro t
  simp only [Path.segment_apply, AffineMap.lineMap_apply_module, map_add, map_smul,
    ← hpq, smul_eq_mul]
  ring

/-- Every geometrically null chain is gauge integrable and has zero directional integral. -/
theorem NullChain.integrable_and_integral_eq_zero {d : Coordinate} {U : Set ℂ}
    {c : BoundaryChain} (h : NullChain d U c) {P : ℂ → ℝ} (hP : ContinuousOn P U) :
    Integrable d.proj P c ∧ integral d.proj P c = 0 := by
  induction h with
  | zero => exact ⟨integrable_zero _ _, map_zero _⟩
  | add h₁ h₂ ih₁ ih₂ => exact ⟨ih₁.1.add ih₂.1, by simp [ih₁.2, ih₂.2]⟩
  | neg h ih => exact ⟨integrable_neg_iff.mpr ih.1, by simp [ih.2]⟩
  | constant γ hγ =>
    have hi := TauCeti.BoxIntegral.hasIntegral_Henstock_of_path_projection_constant d.proj γ hγ P
    exact ⟨(integrable_ofPath_iff _ _ _).2 hi.integrable,
      by simpa only [integral_ofPath, arcIntegral_def] using hi.integral_eq⟩
  | graph hgraph harcs hboundary =>
    refine ⟨(integrable_iff _ _ _).2
      (fun γ hγ ↦ ((harcs γ hγ).hasIntegral (hP.mono hgraph)).integrable), ?_⟩
    rw [integral_eq_boundary_of_graph harcs (hP.mono hgraph), hboundary, map_zero]
  | join hγ hδ =>
    refine ⟨?_, ?_⟩
    · exact ((hγ.trans hδ).integrable hP).sub
        ((hγ.integrable hP).add (hδ.integrable hP))
    · rw [map_sub, map_add, integral_ofPath, integral_ofPath, integral_ofPath,
        hγ.arcIntegral_trans hδ hP, sub_self]
  | reverse hγ =>
    refine ⟨(hγ.integrable hP).add (hγ.symm.integrable hP), ?_⟩
    rw [map_add, integral_ofPath, integral_ofPath, hγ.arcIntegral_symm hP, add_neg_cancel]
  | reparam hδ θ h =>
    refine ⟨?_, ?_⟩
    · exact ((hδ.reparam θ h).integrable hP).sub
        (hδ.integrable hP)
    · rw [map_sub, integral_ofPath, integral_ofPath,
        hδ.arcIntegral_reparam h hP, sub_self]

/-- A geometric certificate comparing two boundaries gives equality of their coordinate
integrals. Integrability transfer is given separately by `NullChain.integrable_iff`. -/
theorem NullChain.integral_eq {d : Coordinate} {U : Set ℂ} {c e : BoundaryChain}
    (h : NullChain d U (c - e)) {P : ℂ → ℝ} (hP : ContinuousOn P U) :
    integral d.proj P c = integral d.proj P e := by
  have hi := (h.integrable_and_integral_eq_zero hP).2
  simpa only [map_sub, sub_eq_zero] using hi

/-- Integrability transfers across a geometric comparison certificate. -/
theorem NullChain.integrable_iff {d : Coordinate} {U : Set ℂ} {c e : BoundaryChain}
    (h : NullChain d U (c - e)) {P : ℂ → ℝ} (hP : ContinuousOn P U) :
    Integrable d.proj P c ↔ Integrable d.proj P e := by
  have hi := (h.integrable_and_integral_eq_zero hP).1
  constructor
  · intro hc
    simpa only [sub_sub_cancel] using hc.sub hi
  · intro he
    have := hi.add he
    simpa only [sub_add_cancel] using this

end TauCeti.Green.BoundaryChain
