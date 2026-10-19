/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.BoundaryChain.Relations

/-!
# Constructive subdivisions of graph-piece paths

A subdivision records actual finite path joins and regular countable-fiber changes of parameter.
Its common refinement is an integer chain of the original graph pieces. The geometric
certificate supplies the null-chain comparison; no equality of integrals is a premise.
-/

public section

noncomputable section

open Set

namespace TauCeti.Green.BoundaryChain

/-- A finite subdivision of an actual path into certified graph pieces. Actual joins and
changes of parameter preserve the original path rather than replacing its integral. -/
inductive GraphSubdivision (d : Coordinate) (U : Set ℂ) : Arc → BoundaryChain → Prop
  | single {γ : Arc} (hγ : PiecewiseGraphArc d U γ) :
      GraphSubdivision d U γ (ofPath γ.2.2)
  | join {p q r : ℂ} {γ : Path p q} {δ : Path q r} {c e : BoundaryChain}
      (hγ : GraphSubdivision d U ⟨p, q, γ⟩ c) (hδ : GraphSubdivision d U ⟨q, r, δ⟩ e) :
      GraphSubdivision d U ⟨p, r, γ.trans δ⟩ (c + e)
  | symm {p q : ℂ} {γ : Path p q} {c : BoundaryChain}
      (hγ : GraphSubdivision d U ⟨p, q, γ⟩ c) :
      GraphSubdivision d U ⟨q, p, γ.symm⟩ (-c)
  | reparam {p q : ℂ} {γ δ : Path p q} {c : BoundaryChain}
      (hδ : GraphSubdivision d U ⟨p, q, δ⟩ c)
      (θ : ℝ → ℝ) (hθ : ContinuousOn θ (Icc 0 1))
      (hdθ : ∃ s : Set ℝ, s.Countable ∧ ∀ t ∈ Ioo 0 1 \ s, DifferentiableAt ℝ θ t)
      (hdδ : ∃ s : Set ℝ, s.Countable ∧
        ∀ t ∈ Ioo 0 1 \ s, DifferentiableAt ℝ δ.extend t)
      (hfib : ∀ t : ℝ, (θ ⁻¹' {t}).Countable) (hmap : MapsTo θ (Icc 0 1) (Icc 0 1))
      (h0 : θ 0 = 0) (h1 : θ 1 = 1) (he : ∀ t : unitInterval, γ t = δ.extend (θ t)) :
      GraphSubdivision d U ⟨p, q, γ⟩ c

/-- A graph-certified joined path subdivides into its actual left and right pieces. The
whole-arc certificate supplies both piece certificates, without extra piece assumptions. -/
theorem GraphArc.subdivision_trans {d : Coordinate} {U : Set ℂ} {g : ℝ → ℝ}
    {a b : ℝ} {p q r : ℂ} {γ : Path p q} {δ : Path q r}
    (h : GraphArc d g a b ⟨p, r, γ.trans δ⟩) (hU : d.graph g '' Icc a b ⊆ U) :
    GraphSubdivision d U ⟨p, r, γ.trans δ⟩ (ofPath γ + ofPath δ) :=
  .join (.single (.graph h.trans_left hU)) (.single (.graph h.trans_right hU))

/-- A joined path with constant selected coordinate subdivides into two constant-coordinate
pieces. These ignored pieces need no differentiability or domain-containment assumptions. -/
theorem GraphSubdivision.of_constant_trans {d : Coordinate} {U : Set ℂ}
    {p q r : ℂ} {γ : Path p q} {δ : Path q r}
    (h : ∀ t : unitInterval, d.proj (γ.trans δ t) = d.proj p) :
    GraphSubdivision d U ⟨p, r, γ.trans δ⟩ (ofPath γ + ofPath δ) := by
  obtain ⟨hγ, hδ⟩ := (coordinate_constant_trans_iff d γ δ).mp h
  exact .join (.single (.constant γ hγ)) (.single (.constant δ hδ))

/-- The original path of a subdivision is itself a certified finite graph-piece path. -/
theorem GraphSubdivision.piecewiseGraphArc {d : Coordinate} {U : Set ℂ} {γ : Arc}
    {c : BoundaryChain} (h : GraphSubdivision d U γ c) : PiecewiseGraphArc d U γ := by
  induction h with
  | single hγ => exact hγ
  | join hγ hδ ihγ ihδ => exact ihγ.trans ihδ
  | symm hγ ih => exact ih.symm
  | reparam hδ θ hθ hdθ hdδ hfib hmap h0 h1 he ih =>
    exact ih.reparam θ ⟨hθ, hdθ, hdδ, hfib, hmap, h0, h1, he⟩

/-- Constructive finite subdivision gives the geometric null-chain certificate comparing
its original whole arc with its piece chain. -/
theorem GraphSubdivision.nullChain {d : Coordinate} {U : Set ℂ} {γ : Arc}
    {c : BoundaryChain} (h : GraphSubdivision d U γ c) :
    NullChain d U (ofPath γ.2.2 - c) := by
  induction h with
  | single hγ => simpa only [sub_self] using (NullChain.zero : NullChain d U 0)
  | join hγ hδ ihγ ihδ =>
    convert (NullChain.join hγ.piecewiseGraphArc hδ.piecewiseGraphArc).add (ihγ.add ihδ) using 1
    abel
  | symm hγ ih =>
    convert (NullChain.reverse hγ.piecewiseGraphArc).add ih.neg using 1
    abel
  | reparam hδ θ hθ hdθ hdδ hfib hmap h0 h1 he ih =>
    convert (NullChain.reparam hδ.piecewiseGraphArc θ
      ⟨hθ, hdθ, hdδ, hfib, hmap, h0, h1, he⟩).add ih
      using 1
    abel

/-- Two actual whole arcs with a common finite graph-piece refinement have a geometric
null-chain comparison in the selected coordinate. -/
theorem GraphSubdivision.nullChain_of_common {d : Coordinate} {U : Set ℂ} {γ δ : Arc}
    {c : BoundaryChain} (hγ : GraphSubdivision d U γ c) (hδ : GraphSubdivision d U δ c) :
    NullChain d U (ofPath γ.2.2 - ofPath δ.2.2) := by
  convert hγ.nullChain.add hδ.nullChain.neg using 1
  abel

/-- Subdividing every supported arc yields a constructive comparison for an arbitrary
finite integer-weighted boundary chain. Multiplicity and orientation are preserved. -/
theorem NullChain.of_graphSubdivisions {d : Coordinate} {U : Set ℂ} (c : BoundaryChain)
    (pieces : Arc → BoundaryChain)
    (h : ∀ γ ∈ c.support, GraphSubdivision d U γ (pieces γ)) :
    NullChain d U (c - c.sum (fun γ n ↦ n • pieces γ)) := by
  classical
  have hn := NullChain.sum c.support (fun γ ↦ c γ • (ofPath γ.2.2 - pieces γ))
    (fun γ hγ ↦ (h γ hγ).nullChain.zsmul (c γ))
  have he : (∑ γ ∈ c.support, c γ • ofPath γ.2.2) = c := by
    simpa only [ofPath_def, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.sum]
      using c.sum_single
  simpa only [smul_sub, Finset.sum_sub_distrib, he, Finsupp.sum] using hn

/-- A common refinement of two finite integer chains supplies their geometric comparison.
The common-refinement premise is equality of actual piece chains, not equality of integrals. -/
theorem NullChain.of_common_graphSubdivisions {d : Coordinate} {U : Set ℂ}
    (c e : BoundaryChain) (pieces pieces' : Arc → BoundaryChain)
    (hc : ∀ γ ∈ c.support, GraphSubdivision d U γ (pieces γ))
    (he : ∀ γ ∈ e.support, GraphSubdivision d U γ (pieces' γ))
    (hcommon : c.sum (fun γ n ↦ n • pieces γ) = e.sum (fun γ n ↦ n • pieces' γ)) :
    NullChain d U (c - e) := by
  have hn := (NullChain.of_graphSubdivisions c pieces hc).add
    (NullChain.of_graphSubdivisions e pieces' he).neg
  rw [← hcommon] at hn
  convert hn using 1
  abel

/-- Both the original whole path and its finite piece chain are genuinely gauge integrable;
their coordinate integrals agree under continuity of the field on the geometric domain. -/
theorem GraphSubdivision.integrable_and_integral_eq {d : Coordinate} {U : Set ℂ} {γ : Arc}
    {c : BoundaryChain} (h : GraphSubdivision d U γ c) {P : ℂ → ℝ} (hP : ContinuousOn P U) :
    Integrable d.proj P (ofPath γ.2.2) ∧ Integrable d.proj P c ∧
      integral d.proj P (ofPath γ.2.2) = integral d.proj P c := by
  have hi := h.piecewiseGraphArc.integrable hP
  exact ⟨hi, (h.nullChain.integrable_iff hP).mp hi, h.nullChain.integral_eq hP⟩

end TauCeti.Green.BoundaryChain
