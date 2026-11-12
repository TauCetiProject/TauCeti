/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

import TauCeti.Data.Fin.Basic

/-!
# Cyclic tuples with bounded consecutive distances

A closed broken geodesic in a Riemannian manifold `Q` with `n + 1` breaks is determined by its
vertices `(q₀, …, qₙ)`, provided consecutive vertices, including the closing pair `qₙ, q₀`, are
close enough to be joined by unique short geodesics. Abouzaid's finite-dimensional approximation
of the free loop space cuts the tuples by prescribed bounds on these distances,

`𝓛ⁿQ = {q ∈ Qⁿ⁺¹ | d(qᵢ, qᵢ₋₁) ≤ δᵢ for every i}`,

with the indices read cyclically (`TauCeti.cyclicDistanceCut`). This file develops the cut in an
arbitrary pseudometric space, before any geodesic interpolation is chosen.

* The cut is closed, hence compact in a compact space, and it grows with the cut-offs.
* Repeating the first vertex, `(q₀, …, qₙ) ↦ (q₀, q₀, q₁, …, qₙ)`, adds an edge of length zero and
  keeps the other edges. So it maps the cut with cut-offs `δ` into the cut with cut-offs `δ'` as
  soon as `δ₀ ≤ δ'₀` and `δᵢ ≤ δ'ᵢ₊₁` for every `i` (`TauCeti.cons_mem_cyclicDistanceCut`), for
  instance when every `δᵢ` is at most every `δ'ⱼ`, the monotonicity condition `δᵢⁿ ≤ δⱼⁿ⁺¹`
  imposed on the cut-offs of the approximation. This is its embedding `ιⁿ : 𝓛ⁿQ → 𝓛ⁿ⁺¹Q`
  (`TauCeti.cyclicDistanceCutRepeatFirst`).

The sampling of compact families of free Moore loops into these cuts is in
`TauCeti.Topology.PathSpace.Moore.Sampling`.

## Main definitions

* `TauCeti.cyclicDistanceCut δ`: the cyclic tuples whose consecutive distances are bounded by `δ`.
* `TauCeti.cyclicDistanceCutRepeatFirst`: the map between cuts repeating the first vertex.

## Main results

* `TauCeti.isClosed_cyclicDistanceCut`, `TauCeti.isCompact_cyclicDistanceCut`: the cut is closed,
  and compact in a compact space.
* `TauCeti.cons_mem_cyclicDistanceCut`: repeating the first vertex maps one cut into another.
* `TauCeti.isEmbedding_cyclicDistanceCutRepeatFirst`,
  `TauCeti.isClosedEmbedding_cyclicDistanceCutRepeatFirst`: it is an embedding, closed when the
  space is Hausdorff.

## References

* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry
  and topology*, IRMA Lect. Math. Theor. Phys. 24 (2015), §11.2.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton, 1963, §16.
-/

public section

open Set Topology

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] {n : ℕ}

/-- **Abouzaid's distance cut.** The cyclic tuples `(q₀, …, qₙ)` whose consecutive distances,
including the closing distance from `q₀` to `qₙ`, are bounded by the cut-offs:
`dist (q i) (q (i - 1)) ≤ δ i` for every `i`, with `i - 1` computed in `Fin (n + 1)`. -/
def cyclicDistanceCut (δ : Fin (n + 1) → ℝ) : Set (Fin (n + 1) → X) :=
  {q | ∀ i, dist (q i) (q (i - 1)) ≤ δ i}

@[simp]
theorem mem_cyclicDistanceCut {δ : Fin (n + 1) → ℝ} {q : Fin (n + 1) → X} :
    q ∈ cyclicDistanceCut δ ↔ ∀ i, dist (q i) (q (i - 1)) ≤ δ i :=
  Iff.rfl

/-- The distance cut is closed. -/
theorem isClosed_cyclicDistanceCut (δ : Fin (n + 1) → ℝ) :
    IsClosed (cyclicDistanceCut (X := X) δ) := by
  simp only [cyclicDistanceCut, ofPred_forall]
  exact isClosed_iInter fun i ↦ isClosed_le (by fun_prop) continuous_const

/-- In a compact space the distance cut is compact. -/
theorem isCompact_cyclicDistanceCut [CompactSpace X] (δ : Fin (n + 1) → ℝ) :
    IsCompact (cyclicDistanceCut (X := X) δ) :=
  (isClosed_cyclicDistanceCut δ).isCompact

/-- The distance cut grows with the cut-offs. -/
theorem cyclicDistanceCut_mono {δ δ' : Fin (n + 1) → ℝ} (h : δ ≤ δ') :
    cyclicDistanceCut (X := X) δ ⊆ cyclicDistanceCut δ' :=
  fun _ hq i ↦ (hq i).trans (h i)

/-- The cut-offs of a nonempty distance cut are nonnegative. -/
theorem nonneg_of_mem_cyclicDistanceCut {δ : Fin (n + 1) → ℝ} {q : Fin (n + 1) → X}
    (hq : q ∈ cyclicDistanceCut δ) : 0 ≤ δ :=
  fun i ↦ dist_nonneg.trans (hq i)

/-- The constant tuples lie in the distance cut for nonnegative cut-offs. -/
theorem const_mem_cyclicDistanceCut {δ : Fin (n + 1) → ℝ} (hδ : 0 ≤ δ) (x : X) :
    (fun _ ↦ x) ∈ cyclicDistanceCut δ :=
  fun i ↦ by simpa using hδ i

/-- **Repeating the first vertex maps one distance cut into another.** The tuple
`(q₀, q₀, q₁, …, qₙ)` has the closing edge `(q₀, qₙ)` of `q` at the vertex `0`, a new edge of
length zero at the vertex `1`, and the edge of `q` at the vertex `i` at the vertex `i + 1`
otherwise. So it lies in the cut with cut-offs `δ'` when `q` lies in the cut with cut-offs `δ`,
`δ 0 ≤ δ' 0` and `δ i ≤ δ' (i + 1)` for every `i`. Both hold when every `δ i` is at most every
`δ' j`, the monotonicity condition of the approximation. -/
theorem cons_mem_cyclicDistanceCut {δ : Fin (n + 1) → ℝ} {δ' : Fin (n + 2) → ℝ}
    (h₀ : δ 0 ≤ δ' 0) (h : ∀ i, δ i ≤ δ' i.succ) {q : Fin (n + 1) → X}
    (hq : q ∈ cyclicDistanceCut δ) :
    (Fin.cons (q 0) q : Fin (n + 2) → X) ∈ cyclicDistanceCut δ' := by
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · -- The closing edge `(q₀, qₙ)` is the closing edge of `q`.
    have hq0 := hq 0
    rw [Fin.zero_sub_one_eq_last] at hq0
    rw [Fin.zero_sub_one_eq_last, ← Fin.succ_last, Fin.cons_zero, Fin.cons_succ]
    exact hq0.trans h₀
  · rw [Fin.succ_sub_one_eq_castSucc, Fin.cons_succ]
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · -- The new edge `(q₀, q₀)` has length zero.
      rw [Fin.castSucc_zero, Fin.cons_zero, dist_self]
      exact (nonneg_of_mem_cyclicDistanceCut hq 0).trans (h 0)
    · -- The edge `(qₖ₊₁, qₖ)` is an edge of `q`.
      have hk := hq k.succ
      rw [Fin.succ_sub_one_eq_castSucc] at hk
      rw [← Fin.succ_castSucc, Fin.cons_succ]
      exact hk.trans (h _)

/-- **The embedding `ιⁿ : 𝓛ⁿ → 𝓛ⁿ⁺¹` repeating the first vertex**,
`(q₀, …, qₙ) ↦ (q₀, q₀, q₁, …, qₙ)`, between the distance cuts with cut-offs `δ` and `δ'`, when
`δ 0 ≤ δ' 0` and `δ i ≤ δ' (i + 1)` for every `i`. -/
def cyclicDistanceCutRepeatFirst {δ : Fin (n + 1) → ℝ} {δ' : Fin (n + 2) → ℝ}
    (h₀ : δ 0 ≤ δ' 0) (h : ∀ i, δ i ≤ δ' i.succ) :
    C(cyclicDistanceCut (X := X) δ, cyclicDistanceCut (X := X) δ') where
  toFun q := ⟨Fin.cons (q.1 0) q.1, cons_mem_cyclicDistanceCut h₀ h q.2⟩
  continuous_toFun :=
    (((continuous_apply 0).comp continuous_subtype_val).finCons (A := fun _ ↦ X)
      continuous_subtype_val).subtype_mk _

@[simp]
theorem coe_cyclicDistanceCutRepeatFirst_apply {δ : Fin (n + 1) → ℝ} {δ' : Fin (n + 2) → ℝ}
    (h₀ : δ 0 ≤ δ' 0) (h : ∀ i, δ i ≤ δ' i.succ) (q : cyclicDistanceCut (X := X) δ) :
    (cyclicDistanceCutRepeatFirst h₀ h q : Fin (n + 2) → X) = Fin.cons (q.1 0) q.1 :=
  (rfl)

/-- Repeating the first vertex is an embedding of distance cuts: forgetting the first vertex is a
continuous left inverse on tuples. -/
theorem isEmbedding_cyclicDistanceCutRepeatFirst {δ : Fin (n + 1) → ℝ} {δ' : Fin (n + 2) → ℝ}
    (h₀ : δ 0 ≤ δ' 0) (h : ∀ i, δ i ≤ δ' i.succ) :
    IsEmbedding (cyclicDistanceCutRepeatFirst (X := X) h₀ h) := by
  refine IsEmbedding.of_comp (map_continuous _)
    continuous_subtype_val.finTail ?_
  have hcomp : (fun p : cyclicDistanceCut (X := X) δ' ↦ Fin.tail p.1) ∘
      cyclicDistanceCutRepeatFirst h₀ h = Subtype.val := by
    funext q
    simp
  exact hcomp ▸ IsEmbedding.subtypeVal

/-- The range of the map repeating the first vertex: the tuples of the target cut whose first two
vertices agree and whose tail lies in the source cut. -/
theorem range_cyclicDistanceCutRepeatFirst {δ : Fin (n + 1) → ℝ} {δ' : Fin (n + 2) → ℝ}
    (h₀ : δ 0 ≤ δ' 0) (h : ∀ i, δ i ≤ δ' i.succ) :
    range (cyclicDistanceCutRepeatFirst (X := X) h₀ h) =
      Subtype.val ⁻¹' ({p | p 1 = p 0} ∩ Fin.tail ⁻¹' cyclicDistanceCut δ) := by
  ext ⟨p, hp⟩
  constructor
  · rintro ⟨q, hq⟩
    rw [← hq]
    refine ⟨?_, ?_⟩
    · simp [Fin.cons_one]
    · simpa only [mem_preimage, coe_cyclicDistanceCutRepeatFirst_apply, Fin.tail_cons] using q.2
  · rintro ⟨h01, htail⟩
    refine ⟨⟨Fin.tail p, htail⟩, Subtype.ext ?_⟩
    have h0 : Fin.tail p 0 = p 0 := by
      simp only [Fin.tail, Fin.succ_zero_eq_one]
      exact h01
    simp only [coe_cyclicDistanceCutRepeatFirst_apply]
    rw [h0, Fin.cons_self_tail]

/-- In a Hausdorff space, repeating the first vertex is a closed embedding of distance cuts. -/
theorem isClosedEmbedding_cyclicDistanceCutRepeatFirst [T2Space X] {δ : Fin (n + 1) → ℝ}
    {δ' : Fin (n + 2) → ℝ} (h₀ : δ 0 ≤ δ' 0) (h : ∀ i, δ i ≤ δ' i.succ) :
    IsClosedEmbedding (cyclicDistanceCutRepeatFirst (X := X) h₀ h) := by
  refine ⟨isEmbedding_cyclicDistanceCutRepeatFirst h₀ h, ?_⟩
  rw [range_cyclicDistanceCutRepeatFirst]
  exact ((isClosed_eq (continuous_apply 1) (continuous_apply 0)).inter
    ((isClosed_cyclicDistanceCut δ).preimage continuous_id.finTail)).preimage continuous_subtype_val

end TauCeti
