/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import TauCeti.Topology.ContinuousMap.RestrictPreimage

import TauCeti.Data.Fin.Basic
import TauCeti.Topology.Homotopy.FiberHomotopyEquiv.Basic
import TauCeti.Topology.Constructions.Pi

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
  soon as `δ₀ ≤ δ'₀`, `0 ≤ δ'₁` and `δᵢ ≤ δ'ᵢ₊₁` for every `i ≠ 0`
  (`TauCeti.cons_mem_cyclicDistanceCut`), for instance when the `δᵢ` are nonnegative and every
  `δᵢ` is at most every `δ'ⱼ`, the monotonicity condition `δᵢⁿ ≤ δⱼⁿ⁺¹` imposed on the cut-offs
  of the approximation. This is its embedding `ιⁿ : 𝓛ⁿQ → 𝓛ⁿ⁺¹Q`
  (`TauCeti.cyclicDistanceCutRepeatFirst`).
* Repeating the first vertex `k` more times, `(q₀, …, qₙ) ↦ (q₀, …, q₀, q₁, …, qₙ)`, maps the cut
  with cut-offs `δ` into the cut with cut-offs `δ'` when `δ (j - k) ≤ δ' j` for every `j`. This
  is the iterate `ιⁿ⁺ᵏ⁻¹ ∘ ⋯ ∘ ιⁿ` (`TauCeti.cyclicDistanceCutRepeatFirstIterate`).
* For cut-offs `δ n` at each stage `n` which grow from each stage to the next,
  `δ n i ≤ δ (n + 1) j` for all `i` and `j`, and with `0 ≤ δ 0 0`, the cuts and the maps `ιⁿ` form
  a sequence of spaces `𝓛⁰Q → 𝓛¹Q → 𝓛²Q → ⋯` (`TauCeti.cyclicDistanceCutFunctor`), whose map
  from stage `n` to stage `n + k` is the iterate
  (`TauCeti.cyclicDistanceCutFunctor_map_homOfLE`). This is the diagram whose singular homology
  has the singular homology of the free loop space as its colimit
  (`TauCeti.Manifold.isColimitMapCoconeSingularHomologyCyclicDistanceCutCocone`).

The tuples of the cut with a prescribed first vertex `x` form the **based distance cut**
`𝓛ⁿ_x Q` (`TauCeti.basedCyclicDistanceCut`). Their closed broken geodesics are loops based at `x`,
and repeating the first vertex maps based cuts into each other
(`TauCeti.basedCyclicDistanceCutRepeatFirstIterate`). The maps of the sequence of cuts keep the
first vertex, so the based cuts at `x` form a sequence of their own
(`TauCeti.basedCyclicDistanceCutFunctor`), whose singular homology has the singular homology of
the based loop space as its colimit
(`TauCeti.Manifold.isColimitMapCoconeSingularHomologyBasedCyclicDistanceCutCocone`).

The sampling of compact families of free Moore loops into these cuts is in
`TauCeti.Topology.PathSpace.Moore.Sampling`.

## Main definitions

* `TauCeti.cyclicDistanceCut δ`: the cyclic tuples whose consecutive distances are bounded by `δ`.
* `TauCeti.cyclicDistanceCutRepeatFirst`: the map between cuts repeating the first vertex.
* `TauCeti.cyclicDistanceCutRepeatFirstIterate`: the map between cuts repeating the first vertex
  several times.
* `TauCeti.basedCyclicDistanceCut δ x`: the tuples of the cut with first vertex `x`, and
  `TauCeti.basedCyclicDistanceCutRestrict`, the restriction to them of a map of cuts keeping the
  first vertex, such as `TauCeti.basedCyclicDistanceCutRepeatFirstIterate`.
* `TauCeti.cyclicDistanceCutFunctor`: the sequence of cuts for growing cut-offs.
* `TauCeti.basedCyclicDistanceCutFunctor`: the sequence of based cuts at `x`.

## Main results

* `TauCeti.isClosed_cyclicDistanceCut`, `TauCeti.isCompact_cyclicDistanceCut`: the cut is closed,
  and compact in a compact space.
* `TauCeti.dist_cons_self_zero_sub_one`, `TauCeti.dist_cons_self_one_sub_one`,
  `TauCeti.dist_cons_self_succ_succ_sub_one`: the edge lengths after repeating the first vertex.
* `TauCeti.cons_mem_cyclicDistanceCut`: repeating the first vertex maps one cut into another.
* `TauCeti.isEmbedding_cyclicDistanceCutRepeatFirst`,
  `TauCeti.isClosedEmbedding_cyclicDistanceCutRepeatFirst`: it is an embedding, closed when the
  space is Hausdorff.
* `TauCeti.cyclicDistanceCutFunctor_map_homOfLE`: the maps of the sequence of cuts repeat the
  first vertex.
* `TauCeti.homotopic_basedCyclicDistanceCutRestrict`: homotopies of maps of cuts keeping the
  first vertex restrict to the based distance cuts.

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

/-- If every point of a cyclic tuple is at distance less than `r` from the preceding one, it is at
distance less than `r` from the next one. -/
theorem dist_add_one_lt_of_forall_dist_sub_one_lt {r : ℝ} {q : Fin (n + 1) → X}
    (h : ∀ i, dist (q i) (q (i - 1)) < r) (i : Fin (n + 1)) : dist (q i) (q (i + 1)) < r := by
  simpa only [add_sub_cancel_right, dist_comm] using h (i + 1)

/-- Repeating the first vertex keeps the closing edge `(q₀, qₙ)` at the vertex `0`. -/
theorem dist_cons_self_zero_sub_one (q : Fin (n + 1) → X) :
    dist ((Fin.cons (q 0) q : Fin (n + 2) → X) 0) ((Fin.cons (q 0) q : Fin (n + 2) → X) (0 - 1)) =
      dist (q 0) (q (0 - 1)) := by
  rw [Fin.zero_sub_one_eq_last, Fin.zero_sub_one_eq_last, ← Fin.succ_last, Fin.cons_zero,
    Fin.cons_succ]

/-- Repeating the first vertex adds the edge `(q₀, q₀)` of length zero at the vertex `1`. -/
theorem dist_cons_self_one_sub_one (q : Fin (n + 1) → X) :
    dist ((Fin.cons (q 0) q : Fin (n + 2) → X) 1) ((Fin.cons (q 0) q : Fin (n + 2) → X) (1 - 1)) =
      0 := by
  rw [sub_self, ← Fin.succ_zero_eq_one, Fin.cons_succ, Fin.cons_zero, dist_self]

/-- Repeating the first vertex moves the edge of `q` at the vertex `k + 1` to the vertex
`k + 2`. -/
theorem dist_cons_self_succ_succ_sub_one (q : Fin (n + 1) → X) (k : Fin n) :
    dist ((Fin.cons (q 0) q : Fin (n + 2) → X) k.succ.succ)
        ((Fin.cons (q 0) q : Fin (n + 2) → X) (k.succ.succ - 1)) =
      dist (q k.succ) (q (k.succ - 1)) := by
  rw [Fin.succ_sub_one_eq_castSucc, Fin.succ_sub_one_eq_castSucc, ← Fin.succ_castSucc,
    Fin.cons_succ, Fin.cons_succ]

/-- **Repeating the first vertex maps one distance cut into another.** The tuple
`(q₀, q₀, q₁, …, qₙ)` has the closing edge `(q₀, qₙ)` of `q` at the vertex `0`, a new edge of
length zero at the vertex `1`, and the edge of `q` at the vertex `i` at the vertex `i + 1`
otherwise. So it lies in the cut with cut-offs `δ'` when `q` lies in the cut with cut-offs `δ`,
`δ 0 ≤ δ' 0`, `0 ≤ δ' 1` and `δ i ≤ δ' (i + 1)` for every `i ≠ 0`. These hold when the cut-offs
`δ i` are nonnegative and every `δ i` is at most every `δ' j`, the monotonicity condition of the
approximation. -/
theorem cons_mem_cyclicDistanceCut {δ : Fin (n + 1) → ℝ} {δ' : Fin (n + 2) → ℝ}
    (h₀ : δ 0 ≤ δ' 0) (h₁ : 0 ≤ δ' 1)
    (h : ∀ i : Fin n, δ i.succ ≤ δ' i.succ.succ) {q : Fin (n + 1) → X}
    (hq : q ∈ cyclicDistanceCut δ) :
    (Fin.cons (q 0) q : Fin (n + 2) → X) ∈ cyclicDistanceCut δ' := by
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · -- The closing edge `(q₀, qₙ)` is the closing edge of `q`.
    rw [dist_cons_self_zero_sub_one]
    exact (hq 0).trans h₀
  · refine Fin.cases ?_ (fun k ↦ ?_) j
    · -- The new edge `(q₀, q₀)` has length zero.
      rw [Fin.succ_zero_eq_one, dist_cons_self_one_sub_one]
      exact h₁
    · -- The edge `(qₖ₊₁, qₖ)` is an edge of `q`.
      rw [dist_cons_self_succ_succ_sub_one]
      exact (hq k.succ).trans (h _)

/-- **The embedding `ιⁿ : 𝓛ⁿ → 𝓛ⁿ⁺¹` repeating the first vertex**,
`(q₀, …, qₙ) ↦ (q₀, q₀, q₁, …, qₙ)`, between the distance cuts with cut-offs `δ` and `δ'`, when
`δ 0 ≤ δ' 0`, `0 ≤ δ' 1` and `δ i ≤ δ' (i + 1)` for every `i ≠ 0`. -/
def cyclicDistanceCutRepeatFirst {δ : Fin (n + 1) → ℝ} {δ' : Fin (n + 2) → ℝ}
    (h₀ : δ 0 ≤ δ' 0) (h₁ : 0 ≤ δ' 1)
    (h : ∀ i : Fin n, δ i.succ ≤ δ' i.succ.succ) :
    C(cyclicDistanceCut (X := X) δ, cyclicDistanceCut (X := X) δ') where
  toFun q := ⟨Fin.cons (q.val 0) q.val, cons_mem_cyclicDistanceCut h₀ h₁ h q.property⟩
  continuous_toFun :=
    (((continuous_apply 0).comp continuous_subtypeVal).finCons (A := fun _ ↦ X)
      continuous_subtypeVal).subtype_mk _

@[simp]
theorem coe_cyclicDistanceCutRepeatFirst_apply {δ : Fin (n + 1) → ℝ} {δ' : Fin (n + 2) → ℝ}
    (h₀ : δ 0 ≤ δ' 0) (h₁ : 0 ≤ δ' 1)
    (h : ∀ i : Fin n, δ i.succ ≤ δ' i.succ.succ) (q : cyclicDistanceCut (X := X) δ) :
    (cyclicDistanceCutRepeatFirst h₀ h₁ h q : Fin (n + 2) → X) = Fin.cons (q.val 0) q.val :=
  (rfl)

/-- Repeating the first vertex is an embedding of distance cuts: forgetting the first vertex is a
continuous left inverse on tuples. -/
theorem isEmbedding_cyclicDistanceCutRepeatFirst {δ : Fin (n + 1) → ℝ} {δ' : Fin (n + 2) → ℝ}
    (h₀ : δ 0 ≤ δ' 0) (h₁ : 0 ≤ δ' 1)
    (h : ∀ i : Fin n, δ i.succ ≤ δ' i.succ.succ) :
    IsEmbedding (cyclicDistanceCutRepeatFirst (X := X) h₀ h₁ h) := by
  have hmaps : MapsTo (fun q : Fin (n + 1) → X ↦ (Fin.cons (q 0) q : Fin (n + 2) → X))
      (cyclicDistanceCut δ) (cyclicDistanceCut δ') := fun _ ↦ cons_mem_cyclicDistanceCut h₀ h₁ h
  -- the carrier map is the restriction of the tuple map to the cuts
  have hfun : ⇑(cyclicDistanceCutRepeatFirst (X := X) h₀ h₁ h) = hmaps.restrict := by
    ext q : 2
    rw [coe_cyclicDistanceCutRepeatFirst_apply, MapsTo.val_restrict_apply]
  rw [hfun]
  exact isEmbedding_cons_apply_zero.restrict hmaps

/-- The range of the map repeating the first vertex: the tuples of the target cut whose first two
vertices agree and whose tail lies in the source cut. -/
theorem range_cyclicDistanceCutRepeatFirst {δ : Fin (n + 1) → ℝ} {δ' : Fin (n + 2) → ℝ}
    (h₀ : δ 0 ≤ δ' 0) (h₁ : 0 ≤ δ' 1)
    (h : ∀ i : Fin n, δ i.succ ≤ δ' i.succ.succ) :
    range (cyclicDistanceCutRepeatFirst (X := X) h₀ h₁ h) =
      Subtype.val ⁻¹' ({p | p 1 = p 0} ∩ Fin.tail ⁻¹' cyclicDistanceCut δ) := by
  ext ⟨p, hp⟩
  constructor
  · rintro ⟨q, hq⟩
    rw [← hq]
    refine ⟨?_, ?_⟩
    · simp [Fin.cons_one]
    · simpa only [mem_preimage, coe_cyclicDistanceCutRepeatFirst_apply,
        Fin.tail_cons] using q.property
  · rintro ⟨h01, htail⟩
    refine ⟨⟨Fin.tail p, htail⟩, Subtype.ext ?_⟩
    have h0 : Fin.tail p 0 = p 0 := by
      simp only [Fin.tail, Fin.succ_zero_eq_one]
      exact h01
    simp only [coe_cyclicDistanceCutRepeatFirst_apply]
    rw [h0, Fin.cons_self_tail]

/-- In a Hausdorff space, repeating the first vertex is a closed embedding of distance cuts. -/
theorem isClosedEmbedding_cyclicDistanceCutRepeatFirst [T2Space X] {δ : Fin (n + 1) → ℝ}
    {δ' : Fin (n + 2) → ℝ} (h₀ : δ 0 ≤ δ' 0) (h₁ : 0 ≤ δ' 1)
    (h : ∀ i : Fin n, δ i.succ ≤ δ' i.succ.succ) :
    IsClosedEmbedding (cyclicDistanceCutRepeatFirst (X := X) h₀ h₁ h) := by
  refine ⟨isEmbedding_cyclicDistanceCutRepeatFirst h₀ h₁ h, ?_⟩
  rw [range_cyclicDistanceCutRepeatFirst]
  exact ((isClosed_eq (continuous_apply 1) (continuous_apply 0)).inter
    ((isClosed_cyclicDistanceCut δ).preimage continuous_id.finTail)).preimage continuous_subtypeVal

/-! ### Repeating the first vertex several times -/

/-- **Each edge of the tuple repeating the first vertex `k` more times is at most an edge of the
tuple.** The edge of `(q₀, …, q₀, q₁, …, qₙ)`, with `q₀` repeated `k + 1` times, ending at the
position `j` has length zero when it joins two copies of `q₀`, and otherwise it is the edge of `q`
ending at the vertex `q_{j - k}`. -/
theorem dist_repeatFirstIterate_le {k : ℕ} (q : Fin (n + 1) → X) (j : Fin (n + k + 1)) :
    dist (q ⟨j - k, by omega⟩) (q ⟨(j - 1 : Fin (n + k + 1)) - k, by omega⟩) ≤
      dist (q ⟨j - k, by omega⟩) (q (⟨j - k, by omega⟩ - 1)) := by
  by_cases hj : (j : ℕ) ≤ k ∧ (j : ℕ) ≠ 0
  · -- The edge ending at a repeated copy of `q₀` has length zero.
    have hj' : ((j - 1 : Fin (n + k + 1)) : ℕ) - k = (j : ℕ) - k := by
      simp only [Fin.coe_sub_one, Fin.ext_iff, Fin.val_zero]
      split_ifs <;> omega
    rw [show q ⟨(j - 1 : Fin (n + k + 1)) - k, by omega⟩ = q ⟨j - k, by omega⟩ from
      congrArg q (Fin.ext hj'), dist_self]
    exact dist_nonneg
  · -- Otherwise the edge ending at the vertex `j` is the edge of `q` ending at the vertex `j - k`.
    have hj' : q ⟨(j - 1 : Fin (n + k + 1)) - k, by omega⟩ = q (⟨j - k, by omega⟩ - 1) := by
      refine congrArg q (Fin.ext ?_)
      simp only [Fin.coe_sub_one, Fin.ext_iff, Fin.val_zero]
      split_ifs <;> omega
    rw [hj']

/-- **Repeating the first vertex `k` more times maps one distance cut into another.** The tuple
`(q₀, …, q₀, q₁, …, qₙ)`, with `q₀` repeated `k + 1` times, has the closing edge `(q₀, qₙ)` of `q`,
`k` edges of length zero, and the other edges of `q` (`TauCeti.dist_repeatFirstIterate_le`). So it
lies in the cut with cut-offs `δ'` when `q` lies in the cut with cut-offs `δ` and the cut-off
`δ (j - k)` of the vertex `q_{j - k}` at the position `j` is at most `δ' j`. -/
theorem repeatFirstIterate_mem_cyclicDistanceCut {k : ℕ} {δ : Fin (n + 1) → ℝ}
    {δ' : Fin (n + k + 1) → ℝ} (h : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j)
    {q : Fin (n + 1) → X} (hq : q ∈ cyclicDistanceCut δ) :
    (fun j : Fin (n + k + 1) ↦ q ⟨j - k, by omega⟩) ∈ cyclicDistanceCut δ' :=
  mem_cyclicDistanceCut.2 fun j ↦ ((dist_repeatFirstIterate_le q j).trans (hq _)).trans (h j)

/-- **The iterated embedding `ιⁿ⁺ᵏ⁻¹ ∘ ⋯ ∘ ιⁿ : 𝓛ⁿ → 𝓛ⁿ⁺ᵏ` repeating the first vertex**,
`(q₀, …, qₙ) ↦ (q₀, …, q₀, q₁, …, qₙ)` with `q₀` repeated `k + 1` times, between the distance cuts
with cut-offs `δ` and `δ'`, when `δ (j - k) ≤ δ' j` for every `j`. For `k = 0` it is the inclusion
of the cuts for `δ ≤ δ'` (`TauCeti.coe_cyclicDistanceCutRepeatFirstIterate_zero_apply`), and
repeating the first vertex once more gives the next iterate
(`TauCeti.cyclicDistanceCutRepeatFirst_cyclicDistanceCutRepeatFirstIterate`). -/
def cyclicDistanceCutRepeatFirstIterate (k : ℕ) {δ : Fin (n + 1) → ℝ}
    {δ' : Fin (n + k + 1) → ℝ} (h : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j) :
    C(cyclicDistanceCut (X := X) δ, cyclicDistanceCut (X := X) δ') where
  toFun q :=
    ⟨fun j ↦ q.val ⟨j - k, by omega⟩, repeatFirstIterate_mem_cyclicDistanceCut h q.property⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_pi fun _ ↦ ?_) _
    exact (continuous_apply _).comp continuous_subtypeVal

@[simp]
theorem coe_cyclicDistanceCutRepeatFirstIterate_apply (k : ℕ) {δ : Fin (n + 1) → ℝ}
    {δ' : Fin (n + k + 1) → ℝ} (h : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j)
    (q : cyclicDistanceCut (X := X) δ) (j : Fin (n + k + 1)) :
    (cyclicDistanceCutRepeatFirstIterate k h q : Fin (n + k + 1) → X) j = q.val ⟨j - k, by omega⟩ :=
  (rfl)

/-- Repeating the first vertex keeps the first vertex. -/
theorem coe_cyclicDistanceCutRepeatFirstIterate_apply_zero (k : ℕ) {δ : Fin (n + 1) → ℝ}
    {δ' : Fin (n + k + 1) → ℝ} (h : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j)
    (q : cyclicDistanceCut (X := X) δ) :
    (cyclicDistanceCutRepeatFirstIterate k h q : Fin (n + k + 1) → X) 0 = q.val 0 := by
  rw [coe_cyclicDistanceCutRepeatFirstIterate_apply]
  exact congrArg q.val (Fin.ext (Nat.zero_sub k))

/-- Repeating the first vertex no more times is the inclusion of one distance cut into another. -/
theorem coe_cyclicDistanceCutRepeatFirstIterate_zero_apply {δ δ' : Fin (n + 1) → ℝ}
    (h : δ ≤ δ') (q : cyclicDistanceCut (X := X) δ) :
    (cyclicDistanceCutRepeatFirstIterate 0 (δ' := δ') (fun j ↦ h j) q : Fin (n + 1) → X) = q :=
  funext fun _ ↦ congrArg q.val (Fin.ext (Nat.sub_zero _))

/-- Repeating the first vertex once more after repeating it `k` more times repeats it `k + 1` more
times: `ιⁿ⁺ᵏ ∘ (ιⁿ⁺ᵏ⁻¹ ∘ ⋯ ∘ ιⁿ) = ιⁿ⁺ᵏ ∘ ⋯ ∘ ιⁿ`. -/
theorem cyclicDistanceCutRepeatFirst_cyclicDistanceCutRepeatFirstIterate {k : ℕ}
    {δ : Fin (n + 1) → ℝ} {δ' : Fin (n + k + 1) → ℝ} {δ'' : Fin (n + (k + 1) + 1) → ℝ}
    (h : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j)
    (h' : ∀ j : Fin (n + (k + 1) + 1), δ ⟨j - (k + 1), by omega⟩ ≤ δ'' j) (h₀ : δ' 0 ≤ δ'' 0)
    (h₁ : 0 ≤ δ'' 1) (h₂ : ∀ i : Fin (n + k), δ' i.succ ≤ δ'' i.succ.succ)
    (q : cyclicDistanceCut (X := X) δ) :
    cyclicDistanceCutRepeatFirst h₀ h₁ h₂ (cyclicDistanceCutRepeatFirstIterate k h q) =
      cyclicDistanceCutRepeatFirstIterate (k + 1) h' q := by
  ext j : 2
  rw [coe_cyclicDistanceCutRepeatFirst_apply, coe_cyclicDistanceCutRepeatFirstIterate_apply]
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · rw [Fin.cons_zero, coe_cyclicDistanceCutRepeatFirstIterate_apply]
    exact congrArg q.val (Fin.ext (by simp))
  · rw [Fin.cons_succ, coe_cyclicDistanceCutRepeatFirstIterate_apply]
    exact congrArg q.val (Fin.ext (by simp))

/-! ### Based distance cuts -/

/-- **The based distance cut** at `x`: the tuples of the distance cut with cut-offs `δ` whose
first vertex is `x`, the fibre over `x` of the first vertex on the cut. The closed broken geodesics
through its tuples are loops based at `x`, so it plays for the based loop space the role the
distance cut plays for the free loop space. -/
def basedCyclicDistanceCut (δ : Fin (n + 1) → ℝ) (x : X) : Set (cyclicDistanceCut (X := X) δ) :=
  (⟨fun q ↦ q.val 0, (continuous_apply 0).comp continuous_subtypeVal⟩ :
    C(cyclicDistanceCut (X := X) δ, X)) ⁻¹' {x}

@[simp]
theorem mem_basedCyclicDistanceCut {δ : Fin (n + 1) → ℝ} {x : X} {q : cyclicDistanceCut δ} :
    q ∈ basedCyclicDistanceCut δ x ↔ q.val 0 = x :=
  Iff.rfl

/-- The tuples of the based distance cut at `x` are the tuples of the distance cut with first
vertex `x`. -/
theorem image_val_basedCyclicDistanceCut (δ : Fin (n + 1) → ℝ) (x : X) :
    Subtype.val '' basedCyclicDistanceCut δ x = cyclicDistanceCut δ ∩ (fun q ↦ q 0) ⁻¹' {x} := by
  ext q
  exact ⟨fun ⟨q', hq', hq⟩ ↦ hq ▸ ⟨q'.property, hq'⟩, fun hq ↦ ⟨⟨q, hq.1⟩, hq.2, rfl⟩⟩

/-- In a `T₁` space the based distance cut is closed. -/
theorem isClosed_basedCyclicDistanceCut [T1Space X] (δ : Fin (n + 1) → ℝ) (x : X) :
    IsClosed (basedCyclicDistanceCut δ x) :=
  isClosed_singleton.preimage (map_continuous _)

open Fin.NatCast in
/-- In a proper space the based distance cut is compact: fixing the first vertex bounds the cut,
since every vertex lies within `∑ i, |δ i|` of the first one along the chain of consecutive
distances. So its tuples are those of the closed distance cut in a compact set
`{x} × (closedBall x R)ⁿ`. -/
theorem isCompact_basedCyclicDistanceCut [ProperSpace X] (δ : Fin (n + 1) → ℝ) (x : X) :
    IsCompact (basedCyclicDistanceCut δ x) := by
  set R := ∑ i ∈ Finset.range n, |δ ((i + 1 : ℕ) : Fin (n + 1))|
  have hfib : cyclicDistanceCut δ ∩ (fun q : Fin (n + 1) → X ↦ q 0) ⁻¹' {x} =
      (fun r : Fin n → X ↦ (Fin.cons x r : Fin (n + 1) → X)) ''
        Set.univ.pi (fun _ ↦ Metric.closedBall x R) ∩ cyclicDistanceCut δ := by
    ext q
    refine ⟨fun ⟨hq, hx⟩ ↦ ⟨⟨Fin.tail q, fun j _ ↦ ?_, hx ▸ Fin.cons_self_tail q⟩, hq⟩, ?_⟩
    · rw [Metric.mem_closedBall, ← (hx : q 0 = x), dist_comm]
      have h := dist_le_range_sum_of_dist_le (f := fun i : ℕ ↦ q i) (j.succ : ℕ)
        (d := fun i ↦ |δ ((i + 1 : ℕ) : Fin (n + 1))|) fun {i} _ ↦ by
          refine (dist_comm _ _).trans_le (le_trans ?_ (le_abs_self _))
          simpa using mem_cyclicDistanceCut.1 hq ((i + 1 : ℕ) : Fin (n + 1))
      simp only [Nat.cast_zero, Fin.cast_val_eq_self] at h
      refine h.trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ abs_nonneg _)
      exact Finset.range_subset_range.2 (by simp [j.isLt])
    · rintro ⟨⟨r, -, rfl⟩, hq⟩
      exact ⟨hq, by simp⟩
  rw [Subtype.isCompact_iff, image_val_basedCyclicDistanceCut, hfib]
  exact ((isCompact_univ_pi fun _ ↦ isCompact_closedBall x R).image
    (continuous_const.finCons continuous_id)).inter_right (isClosed_cyclicDistanceCut δ)

/-- The constant tuple at `x` lies in the based distance cut at `x` for nonnegative cut-offs. -/
theorem const_mem_basedCyclicDistanceCut {δ : Fin (n + 1) → ℝ} (hδ : 0 ≤ δ) (x : X) :
    ⟨fun _ ↦ x, const_mem_cyclicDistanceCut hδ x⟩ ∈ basedCyclicDistanceCut δ x :=
  mem_basedCyclicDistanceCut.2 rfl

/-- **Maps of distance cuts keeping the first vertex restrict to based distance cuts.** A
continuous map `f` from the distance cut with cut-offs `δ` to the one with cut-offs `δ'` which
keeps the first vertex maps the based distance cut at `x` into the based distance cut at `x`: it
is a map over the first vertex, restricted to the fibres over `x`. -/
def basedCyclicDistanceCutRestrict {m : ℕ} {δ : Fin (n + 1) → ℝ} {δ' : Fin (m + 1) → ℝ}
    (f : C(cyclicDistanceCut (X := X) δ, cyclicDistanceCut (X := X) δ'))
    (hf : ∀ q, (f q : Fin (m + 1) → X) 0 = q.val 0) (x : X) :
    C(basedCyclicDistanceCut (X := X) δ x, basedCyclicDistanceCut (X := X) δ' x) :=
  restrictPreimageMap {x} (ContinuousMap.ext hf)

@[simp]
theorem coe_basedCyclicDistanceCutRestrict_apply {m : ℕ} {δ : Fin (n + 1) → ℝ}
    {δ' : Fin (m + 1) → ℝ} (f : C(cyclicDistanceCut (X := X) δ, cyclicDistanceCut (X := X) δ'))
    (hf : ∀ q, (f q : Fin (m + 1) → X) 0 = q.val 0) (x : X)
    (q : basedCyclicDistanceCut (X := X) δ x) :
    (basedCyclicDistanceCutRestrict f hf x q : cyclicDistanceCut (X := X) δ') = f q :=
  coe_restrictPreimageMap {x} _ q

/-- **Homotopies keeping the first vertex restrict to based distance cuts.** If two maps of
distance cuts keeping the first vertex are homotopic through maps keeping the first vertex, their
restrictions to the based distance cuts at `x` are homotopic. -/
theorem homotopic_basedCyclicDistanceCutRestrict {m : ℕ} {δ : Fin (n + 1) → ℝ}
    {δ' : Fin (m + 1) → ℝ} {f g : C(cyclicDistanceCut (X := X) δ, cyclicDistanceCut (X := X) δ')}
    {hf : ∀ q, (f q : Fin (m + 1) → X) 0 = q.val 0}
    {hg : ∀ q, (g q : Fin (m + 1) → X) 0 = q.val 0} (H : f.Homotopy g)
    (hH : ∀ p, (H p : Fin (m + 1) → X) 0 = p.2.val 0) (x : X) :
    (basedCyclicDistanceCutRestrict f hf x).Homotopic (basedCyclicDistanceCutRestrict g hg x) :=
  ContinuousMap.homotopic_of_fiber _ _
    (H.toContinuousMap.comp ⟨fun z ↦ (z.2, z.1.val), by fun_prop⟩)
    (fun q ↦ (H.apply_zero q.val).trans (coe_basedCyclicDistanceCutRestrict_apply f hf x q).symm)
    (fun q ↦ (H.apply_one q.val).trans (coe_basedCyclicDistanceCutRestrict_apply g hg x q).symm)
    fun q s ↦ (hH (s, q.val)).trans q.property

/-- **Repeating the first vertex several times maps based distance cuts into each other**: it
keeps the first vertex. This is the restriction of
`TauCeti.cyclicDistanceCutRepeatFirstIterate` to the based distance cuts at `x`. -/
def basedCyclicDistanceCutRepeatFirstIterate (k : ℕ) {δ : Fin (n + 1) → ℝ}
    {δ' : Fin (n + k + 1) → ℝ} (h : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j) (x : X) :
    C(basedCyclicDistanceCut (X := X) δ x, basedCyclicDistanceCut (X := X) δ' x) :=
  basedCyclicDistanceCutRestrict (cyclicDistanceCutRepeatFirstIterate k h)
    (coe_cyclicDistanceCutRepeatFirstIterate_apply_zero k h) x

/-- Repeating the first vertex on based distance cuts is the restriction of repeating it on
distance cuts. -/
theorem basedCyclicDistanceCutRepeatFirstIterate_eq_restrict (k : ℕ) {δ : Fin (n + 1) → ℝ}
    {δ' : Fin (n + k + 1) → ℝ} (h : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j) (x : X) :
    basedCyclicDistanceCutRepeatFirstIterate k h x =
      basedCyclicDistanceCutRestrict (cyclicDistanceCutRepeatFirstIterate k h)
        (coe_cyclicDistanceCutRepeatFirstIterate_apply_zero k h) x :=
  (rfl)

@[simp]
theorem coe_basedCyclicDistanceCutRepeatFirstIterate_apply (k : ℕ) {δ : Fin (n + 1) → ℝ}
    {δ' : Fin (n + k + 1) → ℝ} (h : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j) (x : X)
    (q : basedCyclicDistanceCut (X := X) δ x) (j : Fin (n + k + 1)) :
    (basedCyclicDistanceCutRepeatFirstIterate k h x q : Fin (n + k + 1) → X) j =
      (q : Fin (n + 1) → X) ⟨j - k, by omega⟩ := by
  rw [basedCyclicDistanceCutRepeatFirstIterate_eq_restrict,
    coe_basedCyclicDistanceCutRestrict_apply, coe_cyclicDistanceCutRepeatFirstIterate_apply]

/-! ### The sequence of distance cuts -/

section Sequence

open CategoryTheory

variable {δ : (n : ℕ) → Fin (n + 1) → ℝ}

/-- Cut-offs which grow from each stage to the next, `δ n i ≤ δ (n + 1) j` for all `i` and `j`,
grow from each stage to every later one. -/
theorem cutoff_le_of_forall_le_succ_of_lt (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) {n m : ℕ}
    (h : n < m) (i : Fin (n + 1)) (j : Fin (m + 1)) : δ n i ≤ δ m j := by
  induction m, h using Nat.le_induction with
  | base => exact hδ n i j
  | succ m _ ih => exact (ih 0).trans (hδ m 0 j)

/-- For cut-offs which grow from each stage to the next and start nonnegative, the total cut-off
of the stage `n` is at most `m + 1` times any cut-off of a later stage `m`. -/
theorem sum_cutoff_le_mul_cutoff (h0 : 0 ≤ δ 0 0) (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j)
    {n m : ℕ} (h : n < m) (j : Fin (m + 1)) : ∑ i, δ n i ≤ ((m + 1 : ℕ) : ℝ) * δ m j := by
  have hj : 0 ≤ δ m j := h0.trans (cutoff_le_of_forall_le_succ_of_lt hδ (by omega) 0 j)
  calc ∑ i, δ n i ≤ ∑ _ : Fin (n + 1), δ m j :=
        Finset.sum_le_sum fun i _ ↦ cutoff_le_of_forall_le_succ_of_lt hδ h i j
    _ = ((n + 1 : ℕ) : ℝ) * δ m j := by simp
    _ ≤ ((m + 1 : ℕ) : ℝ) * δ m j :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega)) hj

/-- For cut-offs which grow from each stage to the next, the cut-off of the vertex `q_{j - k}` at
the stage `n` is at most the cut-off of the position `j` at the stage `n + k`: this is the
condition under which repeating the first vertex `k` more times maps the cut of the stage `n` into
the cut of the stage `n + k` (`TauCeti.cyclicDistanceCutRepeatFirstIterate`). -/
theorem cutoff_sub_le_of_forall_le_succ (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) (n k : ℕ)
    (j : Fin (n + k + 1)) : δ n ⟨j - k, by omega⟩ ≤ δ (n + k) j := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact le_of_eq (congrArg (δ n) (Fin.ext (Nat.sub_zero _)))
  · exact cutoff_le_of_forall_le_succ_of_lt hδ (by omega) _ _

variable (X)

/-- **The sequence of distance cuts** `𝓛⁰X → 𝓛¹X → 𝓛²X → ⋯`: the distance cut with cut-offs
`δ n` at the stage `n`, and the maps `ιⁿ` repeating the first vertex
(`TauCeti.cyclicDistanceCutRepeatFirst`), for cut-offs which grow from each stage to the next,
`δ n i ≤ δ (n + 1) j` for all `i` and `j`, and start nonnegative, `0 ≤ δ 0 0`. -/
@[expose, implicit_reducible, simps! obj]
def cyclicDistanceCutFunctor (h0 : 0 ≤ δ 0 0) (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) :
    ℕ ⥤ TopCat :=
  Functor.ofSequence fun n ↦ TopCat.ofHom (cyclicDistanceCutRepeatFirst (X := X) (δ := δ n)
    (δ' := δ (n + 1)) (hδ n 0 0) (h0.trans (cutoff_le_of_forall_le_succ_of_lt hδ n.succ_pos 0 1))
    fun _ ↦ hδ n _ _)

/-- The map of the sequence of distance cuts from the stage `n` to the stage `n + 1` is the map
`ιⁿ` repeating the first vertex (`TauCeti.cyclicDistanceCutRepeatFirst`). -/
theorem cyclicDistanceCutFunctor_map_homOfLE_succ (h0 : 0 ≤ δ 0 0)
    (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) (n : ℕ) (h₀ : δ n 0 ≤ δ (n + 1) 0)
    (h₁ : 0 ≤ δ (n + 1) 1) (h : ∀ i : Fin n, δ n i.succ ≤ δ (n + 1) i.succ.succ) :
    ((cyclicDistanceCutFunctor X h0 hδ).map (homOfLE (Nat.le_add_right n 1))).hom =
      cyclicDistanceCutRepeatFirst h₀ h₁ h := by
  simp only [cyclicDistanceCutFunctor, Functor.ofSequence_map_homOfLE_succ, TopCat.hom_ofHom]

/-- **The maps of the sequence of distance cuts.** The map from the stage `n` to the stage `n + k`
repeats the first vertex `k` more times (`TauCeti.cyclicDistanceCutRepeatFirstIterate`). -/
theorem cyclicDistanceCutFunctor_map_homOfLE (h0 : 0 ≤ δ 0 0)
    (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) (n k : ℕ)
    (h : ∀ j : Fin (n + k + 1), δ n ⟨j - k, by omega⟩ ≤ δ (n + k) j) :
    ((cyclicDistanceCutFunctor X h0 hδ).map (homOfLE (Nat.le_add_right n k))).hom =
      cyclicDistanceCutRepeatFirstIterate k h := by
  induction k with
  | zero =>
    -- The map from a stage to itself is the identity.
    have h1 : homOfLE (Nat.le_add_right n 0) = 𝟙 n := Subsingleton.elim _ _
    ext q : 1
    simp only [h1, CategoryTheory.Functor.map_id, TopCat.hom_id, ContinuousMap.id_apply]
    exact Subtype.ext (coe_cyclicDistanceCutRepeatFirstIterate_zero_apply le_rfl q).symm
  | succ k ih =>
    -- The map to the stage `n + k + 1` is the map to the stage `n + k` followed by `ιⁿ⁺ᵏ`.
    have h1 : homOfLE (Nat.le_add_right n (k + 1)) =
        homOfLE (Nat.le_add_right n k) ≫ homOfLE (Nat.le_add_right (n + k) 1) :=
      Subsingleton.elim _ _
    have h₀ := hδ (n + k) 0 0
    have h₁ := h0.trans (cutoff_le_of_forall_le_succ_of_lt hδ (n + k).succ_pos 0 1)
    have h₂ (i : Fin (n + k)) := hδ (n + k) i.succ i.succ.succ
    ext q : 1
    rw [h1, CategoryTheory.Functor.map_comp, TopCat.hom_comp, ContinuousMap.comp_apply,
      ih (cutoff_sub_le_of_forall_le_succ hδ n k),
      cyclicDistanceCutFunctor_map_homOfLE_succ X h0 hδ (n + k) h₀ h₁ h₂]
    exact cyclicDistanceCutRepeatFirst_cyclicDistanceCutRepeatFirstIterate _ h h₀ h₁ h₂ q

/-- The maps of the sequence of distance cuts keep the first vertex. -/
theorem coe_cyclicDistanceCutFunctor_map_apply_zero (h0 : 0 ≤ δ 0 0)
    (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) {n m : ℕ} (f : n ⟶ m)
    (q : cyclicDistanceCut (X := X) (δ n)) :
    (((cyclicDistanceCutFunctor X h0 hδ).map f).hom q).val 0 = q.val 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (leOfHom f)
  rw [Subsingleton.elim f (homOfLE (Nat.le_add_right n k)),
    cyclicDistanceCutFunctor_map_homOfLE X h0 hδ n k (cutoff_sub_le_of_forall_le_succ hδ n k)]
  exact coe_cyclicDistanceCutRepeatFirstIterate_apply_zero k _ q

/-- **The sequence of based distance cuts** `𝓛⁰_x X → 𝓛¹_x X → 𝓛²_x X → ⋯`: the based distance
cut at `x` with cut-offs `δ n` at the stage `n`, and the restrictions of the maps of the sequence
of distance cuts (`TauCeti.cyclicDistanceCutFunctor`), which keep the first vertex. -/
-- The `obj` lemma is not `@[simp]`: as an `rfl` lemma, dsimp would rewrite `obj n` inside the
-- domain of the maps, so `coe_basedCyclicDistanceCutFunctor_map_apply` would fail simpNF.
@[expose, implicit_reducible, simps -isSimp obj]
def basedCyclicDistanceCutFunctor (h0 : 0 ≤ δ 0 0) (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) (x : X) :
    ℕ ⥤ TopCat where
  obj n := TopCat.of (basedCyclicDistanceCut (δ n) x)
  map f := TopCat.ofHom (basedCyclicDistanceCutRestrict
    ((cyclicDistanceCutFunctor X h0 hδ).map f).hom
    (coe_cyclicDistanceCutFunctor_map_apply_zero X h0 hδ f) x)
  map_id n := by
    ext q : 2
    exact (coe_basedCyclicDistanceCutRestrict_apply _
      (coe_cyclicDistanceCutFunctor_map_apply_zero X h0 hδ _) x q).trans
        (ConcreteCategory.congr_hom ((cyclicDistanceCutFunctor X h0 hδ).map_id n) q.val)
  map_comp f g := by
    ext q : 2
    refine (coe_basedCyclicDistanceCutRestrict_apply _
      (coe_cyclicDistanceCutFunctor_map_apply_zero X h0 hδ _) x q).trans ?_
    rw [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom,
      coe_basedCyclicDistanceCutRestrict_apply, ConcreteCategory.hom_ofHom,
      coe_basedCyclicDistanceCutRestrict_apply]
    exact ConcreteCategory.congr_hom ((cyclicDistanceCutFunctor X h0 hδ).map_comp f g) q.val

/-- The maps of the sequence of based distance cuts are those of the sequence of distance cuts. -/
@[simp]
theorem coe_basedCyclicDistanceCutFunctor_map_apply (h0 : 0 ≤ δ 0 0)
    (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) (x : X) {n m : ℕ} (f : n ⟶ m)
    (q : basedCyclicDistanceCut (X := X) (δ n) x) :
    (((basedCyclicDistanceCutFunctor X h0 hδ x).map f).hom q).val =
      ((cyclicDistanceCutFunctor X h0 hδ).map f).hom q.val :=
  coe_basedCyclicDistanceCutRestrict_apply _
    (coe_cyclicDistanceCutFunctor_map_apply_zero X h0 hδ f) x q

/-- **The maps of the sequence of based distance cuts.** The map from the stage `n` to the stage
`n + k` repeats the first vertex `k` more times
(`TauCeti.basedCyclicDistanceCutRepeatFirstIterate`). -/
theorem basedCyclicDistanceCutFunctor_map_homOfLE (h0 : 0 ≤ δ 0 0)
    (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) (x : X) (n k : ℕ)
    (h : ∀ j : Fin (n + k + 1), δ n ⟨j - k, by omega⟩ ≤ δ (n + k) j) :
    ((basedCyclicDistanceCutFunctor X h0 hδ x).map (homOfLE (Nat.le_add_right n k))).hom =
      basedCyclicDistanceCutRepeatFirstIterate k h x := by
  ext q : 1
  refine Subtype.ext ?_
  rw [coe_basedCyclicDistanceCutFunctor_map_apply,
    cyclicDistanceCutFunctor_map_homOfLE X h0 hδ n k h,
    basedCyclicDistanceCutRepeatFirstIterate_eq_restrict, coe_basedCyclicDistanceCutRestrict_apply]

end Sequence

end TauCeti
