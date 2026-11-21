/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

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
  soon as `δ₀ ≤ δ'₀`, `0 ≤ δ'₁` and `δᵢ ≤ δ'ᵢ₊₁` for every `i ≠ 0`
  (`TauCeti.cons_mem_cyclicDistanceCut`), for instance when the `δᵢ` are nonnegative and every
  `δᵢ` is at most every `δ'ⱼ`, the monotonicity condition `δᵢⁿ ≤ δⱼⁿ⁺¹` imposed on the cut-offs
  of the approximation. This is its embedding `ιⁿ : 𝓛ⁿQ → 𝓛ⁿ⁺¹Q`
  (`TauCeti.cyclicDistanceCutRepeatFirst`).
* Repeating the first vertex `k` more times, `(q₀, …, qₙ) ↦ (q₀, …, q₀, q₁, …, qₙ)`, maps the cut
  with cut-offs `δ` into the cut with cut-offs `δ'` when `δ (j - k) ≤ δ' j` for every `j`. This
  is the iterate `ιⁿ⁺ᵏ⁻¹ ∘ ⋯ ∘ ιⁿ` (`TauCeti.cyclicDistanceCutRepeatFirstIterate`).

The sampling of compact families of free Moore loops into these cuts is in
`TauCeti.Topology.PathSpace.Moore.Sampling`.

## Main definitions

* `TauCeti.cyclicDistanceCut δ`: the cyclic tuples whose consecutive distances are bounded by `δ`.
* `TauCeti.cyclicDistanceCutRepeatFirst`: the map between cuts repeating the first vertex.
* `TauCeti.cyclicDistanceCutRepeatFirstIterate`: the map between cuts repeating the first vertex
  several times.

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
    have hq0 := hq 0
    rw [Fin.zero_sub_one_eq_last] at hq0
    rw [Fin.zero_sub_one_eq_last, ← Fin.succ_last, Fin.cons_zero, Fin.cons_succ]
    exact hq0.trans h₀
  · rw [Fin.succ_sub_one_eq_castSucc, Fin.cons_succ]
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · -- The new edge `(q₀, q₀)` has length zero.
      rw [Fin.castSucc_zero, Fin.cons_zero, dist_self, Fin.succ_zero_eq_one]
      exact h₁
    · -- The edge `(qₖ₊₁, qₖ)` is an edge of `q`.
      have hk := hq k.succ
      rw [Fin.succ_sub_one_eq_castSucc] at hk
      rw [← Fin.succ_castSucc, Fin.cons_succ]
      exact hk.trans (h _)

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
  refine IsEmbedding.of_comp (map_continuous _)
    continuous_subtypeVal.finTail ?_
  have hcomp : (fun p : cyclicDistanceCut (X := X) δ' ↦ Fin.tail p.val) ∘
      cyclicDistanceCutRepeatFirst h₀ h₁ h = Subtype.val := by
    funext q
    simp
  exact hcomp ▸ IsEmbedding.subtypeVal

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

/-- **Repeating the first vertex `k` more times maps one distance cut into another.** The tuple
`(q₀, …, q₀, q₁, …, qₙ)`, with `q₀` repeated `k + 1` times, has the closing edge `(q₀, qₙ)` of `q`,
`k` edges of length zero, and the other edges of `q`. So it lies in the cut with cut-offs `δ'` when
`q` lies in the cut with cut-offs `δ` and the cut-off `δ (j - k)` of the vertex `q_{j - k}` at the
position `j` is at most `δ' j`. -/
theorem repeatFirstIterate_mem_cyclicDistanceCut {k : ℕ} {δ : Fin (n + 1) → ℝ}
    {δ' : Fin (n + k + 1) → ℝ} (h : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j)
    {q : Fin (n + 1) → X} (hq : q ∈ cyclicDistanceCut δ) :
    (fun j : Fin (n + k + 1) ↦ q ⟨j - k, by omega⟩) ∈ cyclicDistanceCut δ' := by
  rw [mem_cyclicDistanceCut]
  intro j
  by_cases hj : (j : ℕ) ≤ k ∧ (j : ℕ) ≠ 0
  · -- The edge ending at a repeated copy of `q₀` has length zero.
    have hj' : ((j - 1 : Fin (n + k + 1)) : ℕ) - k = (j : ℕ) - k := by
      simp only [Fin.coe_sub_one, Fin.ext_iff, Fin.val_zero]
      split_ifs <;> omega
    rw [show q ⟨(j - 1 : Fin (n + k + 1)) - k, by omega⟩ = q ⟨j - k, by omega⟩ from
      congrArg q (Fin.ext hj'), dist_self]
    exact (nonneg_of_mem_cyclicDistanceCut hq _).trans (h j)
  · -- Otherwise the edge ending at the vertex `j` is the edge of `q` ending at the vertex `j - k`.
    have hj' : q ⟨(j - 1 : Fin (n + k + 1)) - k, by omega⟩ = q (⟨j - k, by omega⟩ - 1) := by
      refine congrArg q (Fin.ext ?_)
      simp only [Fin.coe_sub_one, Fin.ext_iff, Fin.val_zero]
      split_ifs <;> omega
    rw [hj']
    exact (hq _).trans (h j)

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

end TauCeti
