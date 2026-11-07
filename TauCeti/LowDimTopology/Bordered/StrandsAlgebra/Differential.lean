/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Ungraded
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Basic
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Resolution
import Mathlib.Algebra.CharP.Two
import TauCeti.Order.MinMax

/-!
# The differential of the strands algebra

The strands algebra `A(n)` of Lipshitz, Ozsváth and Thurston is a differential algebra over `𝔽₂`.
Its differential sends a strand diagram `φ` to the sum of the diagrams obtained from `φ` by
resolving one crossing, keeping only those resolutions with exactly one crossing fewer than `φ`
(`TauCeti.StrandsAlgebra.differential`). Pictorially these are the smoothings of a crossing that
create no pair of strands crossing twice. This file proves that, over a ring of characteristic two,
the differential squares to zero and satisfies the Leibniz rule
`d (x * y) = d x * y + x * d y`, so that the strands algebra is an ungraded differential algebra
(`TauCeti.StrandsAlgebra.isUngradedDGAlgebra_differential`).

## The Leibniz rule

For basis elements `φ` and `ψ`, with `φ` ending where `ψ` starts, all three terms of the Leibniz
rule are sums over the pairs `i < j` of starting points of `φ`, each term resolving the crossing of
the strands starting at `i` and `j`: in the concatenation `φ.trans ψ`, in `φ`, or in `ψ` at the
pair of their end points in `φ`. Those strands cross in the concatenation exactly when they cross
in one piece and not the other. Comparing the crossing counts of the diagrams involved shows that,
pair by pair, the left side has a term exactly when one but not both of the right-hand terms is
present, all present terms being the same diagram. When both right-hand terms are present the
strands cross twice in the concatenation, which is then zero, and the two terms cancel in
characteristic two.

## `d ∘ d = 0`

The terms of `d (d φ)` are the two-step resolution chains `(p, q)`: `p` is a resolvable crossing
of `φ` and `q` a resolvable crossing of its resolution. A chain is determined by its two crossings,
and it is a chain exactly when both are crossings of the relevant diagrams and the end result has
two crossings fewer than `φ`, since each resolution strictly lowers the count
(`TauCeti.StrandDiagram.inversionCount_resolve_lt`). The chains are paired off by an involution
preserving the end result:

* if `p` and `q` involve four distinct strands, the two resolutions commute, and `(p, q)` is
  paired with `(q, p)`;
* if they share a strand, say `p = {s, u}` and `q = {s, w}`, then with `r = {u, w}` the end result
  is also reached by `(q, r)` and by `(r, p)`, by the three-cycle relation
  `(s u) (s w) = (s w) (u w) = (u w) (s u)` of transpositions; a comparison of the end points of the
  three strands shows that exactly one of these is again a chain, and `(p, q)` is paired with it.

Hence `d (d φ)` is a sum of terms appearing twice, which is zero in characteristic two.

## Main definitions

* `TauCeti.StrandsAlgebra.differential`: the differential of the strands algebra.

## Main results

* `TauCeti.StrandsAlgebra.differential_of`: the differential of a basis element.
* `TauCeti.StrandsAlgebra.differential_idem`: the idempotents are cycles.
* `TauCeti.StrandsAlgebra.differential_mul`: the Leibniz rule.
* `TauCeti.StrandsAlgebra.differential_differential`: the differential squares to zero.
* `TauCeti.StrandsAlgebra.isUngradedDGAlgebra_differential`: the strands algebra is an ungraded
  differential algebra.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.1,
  Definition 3.2 (the differential of the strands algebra `A(n, k)`).
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace StrandDiagram

variable {α : Type*} [LinearOrder α] [Fintype α] {φ ψ : StrandDiagram α}

/-! ### The Leibniz rule -/

/-- **The Leibniz rule for one pair of strands.** Let the strands of `φ` starting at `i < j` end at
`a` and `b`, where `ψ` starts. Their crossing is a resolvable crossing of the nonzero product
`φ.trans ψ` exactly when either it is a resolvable crossing of `φ` whose resolution is composable
with `ψ`, or the crossing of the strands of `ψ` starting at `a` and `b` is a resolvable crossing of
`ψ` whose resolution is composable with `φ`, but not both. -/
private theorem composable_and_mem_resolvableInversions_trans_iff (hT : φ.target = ψ.source)
    {i j a b : α} (hij : i < j) (ha : a ∈ φ i) (hb : b ∈ φ j) :
    (φ.Composable ψ ∧ (i, j) ∈ (φ.trans ψ).resolvableInversions) ↔
      Xor ((i, j) ∈ φ.resolvableInversions ∧ (φ.resolve (i, j)).Composable ψ)
        ((min a b, max a b) ∈ ψ.resolvableInversions ∧
          φ.Composable (ψ.resolve (min a b, max a b))) := by
  obtain ⟨c, hc⟩ := mem_source.1 (hT ▸ mem_target.2 ⟨i, ha⟩ : a ∈ ψ.source)
  obtain ⟨d, hd⟩ := mem_source.1 (hT ▸ mem_target.2 ⟨j, hb⟩ : b ∈ ψ.source)
  have hab : a ≠ b := φ.ne_of_mem_of_mem_of_ne ha hb hij.ne
  have hcd : c ≠ d := ψ.ne_of_mem_of_mem_of_ne hc hd hab
  have hX : (i, j) ∈ φ.inversions ↔ b < a := by simp [mem_inversions_iff_of_mem ha hb, hij]
  have hZ : (i, j) ∈ (φ.trans ψ).inversions ↔ d < c := by
    simp [mem_inversions_iff_of_mem (mem_trans.2 ⟨a, ha, hc⟩) (mem_trans.2 ⟨b, hb, hd⟩), hij]
  have hY := min_max_mem_inversions_iff hab hc hd
  have hφψ := inversionCount_trans_le φ ψ
  simp only [mem_resolvableInversions, composable_iff, target_resolve, source_resolve, hT,
    true_and]
  rcases lt_or_gt_of_ne hab with hab' | hab' <;> rcases lt_or_gt_of_ne hcd.symm with hcd' | hcd'
  · -- The strands cross in `ψ` only.
    have hYm := hY.2 (iff_of_true hab' hcd')
    have hZm := hZ.2 hcd'
    have hXm : (i, j) ∉ φ.inversions := fun h ↦ (hX.1 h).asymm hab'
    have h₁ := inversionCount_resolve_lt hYm
    have h₂ := inversionCount_resolve_lt hZm
    have h₃ := inversionCount_trans_le φ (ψ.resolve (min a b, max a b))
    rw [trans_resolve_eq_trans_resolve ha hb hYm hZm] at h₂ ⊢
    simp only [hXm, hYm, hZm, false_and, true_and, xor_def, not_false_eq_true, and_true,
      false_or, not_and]
    omega
  · -- The strands cross in neither piece.
    have hYm : (min a b, max a b) ∉ ψ.inversions := fun h ↦ hcd'.asymm ((hY.1 h).1 hab')
    have hZm : (i, j) ∉ (φ.trans ψ).inversions := fun h ↦ hcd'.asymm (hZ.1 h)
    have hXm : (i, j) ∉ φ.inversions := fun h ↦ (hX.1 h).asymm hab'
    simp [hXm, hYm, hZm]
  · -- The strands cross in `φ` only.
    have hXm := hX.2 hab'
    have hZm := hZ.2 hcd'
    have hYm : (min a b, max a b) ∉ ψ.inversions := fun h ↦ hab'.asymm ((hY.1 h).2 hcd')
    have h₁ := inversionCount_resolve_lt hXm
    have h₂ := inversionCount_resolve_lt hZm
    have h₃ := inversionCount_trans_le (φ.resolve (i, j)) ψ
    rw [trans_resolve_eq_resolve_trans hXm hZm] at h₂ ⊢
    simp only [hXm, hYm, hZm, false_and, true_and, xor_def, not_false_eq_true, and_true,
      or_false, not_and]
    omega
  · -- The strands cross in both pieces, so twice in the concatenation.
    have hXm := hX.2 hab'
    have hYm := hY.2 (iff_of_false hab'.not_gt hcd'.not_gt)
    have hZm : (i, j) ∉ (φ.trans ψ).inversions := fun h ↦ hcd'.asymm (hZ.1 h)
    have h₁ := inversionCount_resolve_lt hXm
    have h₂ := inversionCount_resolve_lt hYm
    have h₃ := inversionCount_trans_le (φ.resolve (i, j)) ψ
    have h₄ := inversionCount_trans_le φ (ψ.resolve (min a b, max a b))
    rw [resolve_trans_eq_trans_resolve ha hb hXm hYm] at h₃ ⊢
    simp only [hXm, hYm, hZm, true_and, false_and, and_false, false_iff, xor_def, not_or,
      not_and]
    omega

/-! ### Chains of two resolutions -/

/-- The two-step resolution chains of `φ`: a resolvable crossing `p` of `φ` together with a
resolvable crossing of its resolution. They index the terms of `d (d φ)`. -/
private def chains (φ : StrandDiagram α) : Finset ((_ : α × α) × (α × α)) :=
  φ.resolvableInversions.sigma fun p ↦ (φ.resolve p).resolvableInversions

/-- A chain is a pair of successive crossings whose resolutions lower the count by two in total. -/
private theorem mem_chains_iff {p q : α × α} :
    (⟨p, q⟩ : (_ : α × α) × (α × α)) ∈ φ.chains ↔ p ∈ φ.inversions ∧
      q ∈ (φ.resolve p).inversions ∧
        ((φ.resolve p).resolve q).inversionCount + 2 = φ.inversionCount := by
  simp only [chains, mem_sigma, mem_resolvableInversions]
  constructor
  · rintro ⟨⟨hp, h₁⟩, hq, h₂⟩
    exact ⟨hp, hq, by omega⟩
  · rintro ⟨hp, hq, h⟩
    have h₁ := inversionCount_resolve_lt hp
    have h₂ := inversionCount_resolve_lt hq
    exact ⟨⟨hp, by omega⟩, hq, by omega⟩

/-- A chain at two disjoint pairs of strands can be run in the other order. -/
private theorem mem_chains_swap {p q : α × α}
    (hx : (⟨p, q⟩ : (_ : α × α) × (α × α)) ∈ φ.chains)
    (h : q.1 ≠ p.1 ∧ q.1 ≠ p.2 ∧ q.2 ≠ p.1 ∧ q.2 ≠ p.2) :
    (⟨q, p⟩ : (_ : α × α) × (α × α)) ∈ φ.chains ∧
      (φ.resolve q).resolve p = (φ.resolve p).resolve q := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  obtain ⟨hp, hq, hc⟩ := mem_chains_iff.1 hx
  have hq' : q ∈ φ.inversions := (mem_inversions_resolve_iff_of_ne hp h₁ h₂ h₃ h₄).1 hq
  have hp' : p ∈ (φ.resolve q).inversions :=
    (mem_inversions_resolve_iff_of_ne hq' h₁.symm h₃.symm h₂.symm h₄.symm).2 hp
  have he := resolve_resolve_comm hp hq' h₁ h₂ h₃ h₄
  exact ⟨mem_chains_iff.2 ⟨hq', hp', he ▸ hc⟩, he.symm⟩

/-- **The three-cycle pairing of chains.** For strands starting at distinct `s`, `u`, `w`, if
resolving `{s, u}` and then `{s, w}` is a chain, then exactly one of resolving `{s, w}` and then
`{u, w}`, or `{u, w}` and then `{s, u}`, is a chain, and each of these has the same end result. -/
private theorem chains_three_cycle {s u w : α} (hsu : s ≠ u) (hsw : s ≠ w) (huw : u ≠ w)
    (hx : (⟨(min s u, max s u), (min s w, max s w)⟩ : (_ : α × α) × (α × α)) ∈ φ.chains) :
    Xor ((⟨(min s w, max s w), (min u w, max u w)⟩ : (_ : α × α) × (α × α)) ∈ φ.chains)
        ((⟨(min u w, max u w), (min s u, max s u)⟩ : (_ : α × α) × (α × α)) ∈ φ.chains) ∧
      ((⟨(min s w, max s w), (min u w, max u w)⟩ : (_ : α × α) × (α × α)) ∈ φ.chains →
        (φ.resolve (min s w, max s w)).resolve (min u w, max u w) =
          (φ.resolve (min s u, max s u)).resolve (min s w, max s w)) ∧
      ((⟨(min u w, max u w), (min s u, max s u)⟩ : (_ : α × α) × (α × α)) ∈ φ.chains →
        (φ.resolve (min u w, max u w)).resolve (min s u, max s u) =
          (φ.resolve (min s u, max s u)).resolve (min s w, max s w)) := by
  obtain ⟨h₁, h₂, hc⟩ := mem_chains_iff.1 hx
  -- The two other chains, granted that their two steps are crossings, end where `hx` does.
  have hqr (h₃ : (min s w, max s w) ∈ φ.inversions)
      (h₄ : (min u w, max u w) ∈ (φ.resolve (min s w, max s w)).inversions) :
      (φ.resolve (min s w, max s w)).resolve (min u w, max u w) =
        (φ.resolve (min s u, max s u)).resolve (min s w, max s w) :=
    (resolve_resolve_eq_resolve_resolve h₁ h₂ h₃ h₄).symm
  have hrp (h₃ : (min u w, max u w) ∈ φ.inversions)
      (h₄ : (min s u, max s u) ∈ (φ.resolve (min u w, max u w)).inversions) :
      (φ.resolve (min u w, max u w)).resolve (min s u, max s u) =
        (φ.resolve (min s u, max s u)).resolve (min s w, max s w) := by
    rw [min_max_comm s u] at h₁ h₂ h₄ ⊢
    rw [min_max_comm s w] at h₂ ⊢
    exact resolve_resolve_eq_resolve_resolve h₃ h₄ h₁ h₂
  refine ⟨?_, fun h ↦ hqr (mem_chains_iff.1 h).1 (mem_chains_iff.1 h).2.1,
    fun h ↦ hrp (mem_chains_iff.1 h).1 (mem_chains_iff.1 h).2.1⟩
  have hA : (⟨(min s w, max s w), (min u w, max u w)⟩ : (_ : α × α) × (α × α)) ∈ φ.chains ↔
      (min s w, max s w) ∈ φ.inversions ∧
        (min u w, max u w) ∈ (φ.resolve (min s w, max s w)).inversions :=
    ⟨fun h ↦ ⟨(mem_chains_iff.1 h).1, (mem_chains_iff.1 h).2.1⟩,
      fun ⟨h₃, h₄⟩ ↦ mem_chains_iff.2 ⟨h₃, h₄, by rwa [hqr h₃ h₄]⟩⟩
  have hB : (⟨(min u w, max u w), (min s u, max s u)⟩ : (_ : α × α) × (α × α)) ∈ φ.chains ↔
      (min u w, max u w) ∈ φ.inversions ∧
        (min s u, max s u) ∈ (φ.resolve (min u w, max u w)).inversions :=
    ⟨fun h ↦ ⟨(mem_chains_iff.1 h).1, (mem_chains_iff.1 h).2.1⟩,
      fun ⟨h₃, h₄⟩ ↦ mem_chains_iff.2 ⟨h₃, h₄, by rwa [hrp h₃ h₄]⟩⟩
  -- Read every crossing condition off the end points `S`, `U`, `W` of the three strands.
  have hsuS := mem_source_of_min_max_mem_inversions h₁
  have hswS := mem_source_of_min_max_mem_inversions h₂
  rw [source_resolve] at hswS
  obtain ⟨S, hS⟩ := mem_source.1 hsuS.1
  obtain ⟨U, hU⟩ := mem_source.1 hsuS.2
  obtain ⟨W, hW⟩ := mem_source.1 hswS.2
  have h₃ : (min s w, max s w) ∈ φ.inversions ↔ (s < w ↔ W < S) :=
    min_max_mem_inversions_iff hsw hS hW
  have h₅ : (min u w, max u w) ∈ φ.inversions ↔ (u < w ↔ W < U) :=
    min_max_mem_inversions_iff huw hU hW
  have h₁' := (min_max_mem_inversions_iff hsu hS hU).1 h₁
  -- After resolving `{s, u}`, the strand from `s` ends at `U`.
  have h₂' : s < w ↔ W < U := by
    refine (min_max_mem_inversions_iff (φ := φ.resolve (min s u, max s u)) hsw ?_ ?_).1 h₂
    · rw [resolve_min_max_apply h₁, Equiv.swap_apply_left]
      exact hU
    · rw [resolve_min_max_apply h₁, Equiv.swap_apply_of_ne_of_ne hsw.symm huw.symm]
      exact hW
  have h₄ (h : (min s w, max s w) ∈ φ.inversions) :
      (min u w, max u w) ∈ (φ.resolve (min s w, max s w)).inversions ↔ (u < w ↔ S < U) := by
    refine min_max_mem_inversions_iff huw ?_ ?_
    · rw [resolve_min_max_apply h, Equiv.swap_apply_of_ne_of_ne hsu.symm huw]
      exact hU
    · rw [resolve_min_max_apply h, Equiv.swap_apply_right]
      exact hS
  have h₆ (h : (min u w, max u w) ∈ φ.inversions) :
      (min s u, max s u) ∈ (φ.resolve (min u w, max u w)).inversions ↔ (s < u ↔ W < S) := by
    refine min_max_mem_inversions_iff hsu ?_ ?_
    · rw [resolve_min_max_apply h, Equiv.swap_apply_of_ne_of_ne hsu hsw]
      exact hS
    · rw [resolve_min_max_apply h, Equiv.swap_apply_left]
      exact hW
  have key := xor_of_lt_iff hsu hsw huw
    (φ.ne_of_mem_of_mem_of_ne hS hU hsu) (φ.ne_of_mem_of_mem_of_ne hS hW hsw)
    (φ.ne_of_mem_of_mem_of_ne hU hW huw) h₁' h₂'
  have hA' : (⟨(min s w, max s w), (min u w, max u w)⟩ : (_ : α × α) × (α × α)) ∈ φ.chains ↔
      (s < w ↔ W < S) ∧ (u < w ↔ S < U) :=
    hA.trans ⟨fun ⟨h, h'⟩ ↦ ⟨h₃.1 h, (h₄ h).1 h'⟩, fun ⟨h, h'⟩ ↦ ⟨h₃.2 h, (h₄ (h₃.2 h)).2 h'⟩⟩
  have hB' : (⟨(min u w, max u w), (min s u, max s u)⟩ : (_ : α × α) × (α × α)) ∈ φ.chains ↔
      (u < w ↔ W < U) ∧ (s < u ↔ W < S) :=
    hB.trans ⟨fun ⟨h, h'⟩ ↦ ⟨h₅.1 h, (h₆ h).1 h'⟩, fun ⟨h, h'⟩ ↦ ⟨h₅.2 h, (h₆ (h₅.2 h)).2 h'⟩⟩
  rw [hA', hB']
  exact key

/-- The sorted pair of the two strands of `p` and `q` other than a strand they share. -/
private def third (p q : α × α) : α × α :=
  (min (if p.1 = q.1 ∨ p.1 = q.2 then p.2 else p.1) (if q.1 = p.1 ∨ q.1 = p.2 then q.2 else q.1),
    max (if p.1 = q.1 ∨ p.1 = q.2 then p.2 else p.1) (if q.1 = p.1 ∨ q.1 = p.2 then q.2 else q.1))

omit [Fintype α] in
private theorem third_min_max {s u w : α} (hsu : s ≠ u) (hsw : s ≠ w) (huw : u ≠ w) :
    third (min s u, max s u) (min s w, max s w) = (min u w, max u w) := by
  rcases lt_or_gt_of_ne hsu with h₁ | h₁ <;> rcases lt_or_gt_of_ne hsw with h₂ | h₂ <;>
    simp [third, h₁.le, h₂.le, hsu, hsw, huw, hsu.symm, hsw.symm, huw.symm]

/-- The chain paired with a chain `(p, q)` in `d (d φ)`: `(q, p)` when `p` and `q` are disjoint,
and otherwise whichever of `(q, r)` and `(r, p)` is a chain, `r` being the third pair of the three
strands involved. -/
private def chainPartner (φ : StrandDiagram α) (x : (_ : α × α) × (α × α)) :
    (_ : α × α) × (α × α) :=
  if x.2.1 ≠ x.1.1 ∧ x.2.1 ≠ x.1.2 ∧ x.2.2 ≠ x.1.1 ∧ x.2.2 ≠ x.1.2 then ⟨x.2, x.1⟩
  else if (⟨x.2, third x.1 x.2⟩ : (_ : α × α) × (α × α)) ∈ φ.chains then ⟨x.2, third x.1 x.2⟩
  else ⟨third x.1 x.2, x.1⟩

/-- `chainPartner φ` is a fixed-point-free involution of the chains of `φ` preserving their end
result. -/
private theorem chainPartner_spec {x : (_ : α × α) × (α × α)} (hx : x ∈ φ.chains) :
    φ.chainPartner x ∈ φ.chains ∧ φ.chainPartner x ≠ x ∧
      φ.chainPartner (φ.chainPartner x) = x ∧
      (φ.resolve (φ.chainPartner x).1).resolve (φ.chainPartner x).2 =
        (φ.resolve x.1).resolve x.2 := by
  obtain ⟨p, q⟩ := x
  by_cases hd : q.1 ≠ p.1 ∧ q.1 ≠ p.2 ∧ q.2 ≠ p.1 ∧ q.2 ≠ p.2
  · have hpart : φ.chainPartner ⟨p, q⟩ = ⟨q, p⟩ := ite_eq_left hd
    obtain ⟨hmem, he⟩ := mem_chains_swap hx hd
    have hd' : p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2 :=
      ⟨hd.1.symm, hd.2.2.1.symm, hd.2.1.symm, hd.2.2.2.symm⟩
    have hqp : q ≠ p := fun h ↦ hd.1 (by rw [h])
    rw [hpart]
    exact ⟨hmem, fun h ↦ hqp (Sigma.mk.inj_iff.1 h).1, ite_eq_left hd', he⟩
  obtain ⟨hp, hq, -⟩ := mem_chains_iff.1 hx
  have hpq : p ≠ q := by
    rintro rfl
    exact notMem_inversions_resolve_self hp hq
  obtain ⟨s, u, w, hsu, hsw, huw, rfl, rfl⟩ :=
    exists_min_max_of_share_coord (mem_inversions.1 hp).1 (mem_inversions.1 hq).1 hpq hd
  obtain ⟨hxor, hqr, hrp⟩ := chains_three_cycle hsu hsw huw hx
  have ht : third (min s u, max s u) (min s w, max s w) = (min u w, max u w) :=
    third_min_max hsu hsw huw
  by_cases h₁ : (⟨(min s w, max s w), (min u w, max u w)⟩ : (_ : α × α) × (α × α)) ∈ φ.chains
  · have hpart : φ.chainPartner ⟨(min s u, max s u), (min s w, max s w)⟩ =
        ⟨(min s w, max s w), (min u w, max u w)⟩ := by
      rw [chainPartner, ite_eq_right hd, ht, ite_eq_left h₁]
    have h₂ : (⟨(min u w, max u w), (min s u, max s u)⟩ : (_ : α × α) × (α × α)) ∉ φ.chains :=
      fun h₂ ↦ by simp [h₁, h₂] at hxor
    -- `(q, r)` shares `w`, and its third pair is `p`.
    have ht' : third (min s w, max s w) (min u w, max u w) = (min s u, max s u) := by
      rw [min_max_comm s w, min_max_comm u w, third_min_max hsw.symm huw.symm hsu]
    rw [hpart]
    refine ⟨h₁, fun h ↦ hpq (Sigma.mk.inj_iff.1 h).1.symm, ?_, hqr h₁⟩
    rw [chainPartner, ite_eq_right (min_max_share_coord s u w), ht', ite_eq_right h₂]
  · have h₂ : (⟨(min u w, max u w), (min s u, max s u)⟩ : (_ : α × α) × (α × α)) ∈ φ.chains := by
      simpa [xor_def, h₁] using hxor
    have hpart : φ.chainPartner ⟨(min s u, max s u), (min s w, max s w)⟩ =
        ⟨(min u w, max u w), (min s u, max s u)⟩ := by
      rw [chainPartner, ite_eq_right hd, ht, ite_eq_right h₁]
    -- `(r, p)` shares `u`, and its third pair is `q`.
    have ht' : third (min u w, max u w) (min s u, max s u) = (min s w, max s w) := by
      rw [min_max_comm s u, third_min_max huw hsu.symm hsw.symm, min_max_comm w s]
    have hnd := min_max_share_coord w s u
    rw [min_comm w u, max_comm w u] at hnd
    rw [hpart]
    refine ⟨h₂, fun h ↦ hpq (eq_of_heq (Sigma.mk.inj_iff.1 h).2), ?_, hrp h₂⟩
    rw [chainPartner, ite_eq_right hnd, ht', ite_eq_left hx]

end StrandDiagram

namespace StrandsAlgebra

open StrandDiagram

variable {R α : Type*} [CommSemiring R] [LinearOrder α] [Fintype α]

variable (R α) in
/-- The differential of the strands algebra: on a strand diagram `φ`, the sum of the resolutions of
the crossings of `φ` that lower the number of crossings by exactly one, extended linearly. For
`R = ZMod 2` and `α = Fin n` this is the differential of the strands algebra `A(n)` of Lipshitz,
Ozsváth and Thurston. -/
def differential : StrandsAlgebra R α →ₗ[R] StrandsAlgebra R α :=
  (basis R α).constr R fun φ ↦ ∑ p ∈ φ.resolvableInversions, of (φ.resolve p)

/-- The differential of a strand diagram is the sum of its resolutions at the crossings whose
resolution has exactly one crossing fewer. -/
theorem differential_of (φ : StrandDiagram α) :
    differential R α (of φ) = ∑ p ∈ φ.resolvableInversions, of (φ.resolve p) := by
  rw [differential, ← basis_apply, Module.Basis.constr_basis]

/-- The idempotents are cycles. -/
@[simp]
theorem differential_idem (s : Finset α) : differential R α (idem s) = 0 := by
  simp [idem_def, differential_of]

/-- A sum over the resolvable crossings of `σ` as a sum over all increasing pairs of starting
points. -/
private theorem sum_resolvableInversions_eq {M : Type*} [AddCommMonoid M] (σ : StrandDiagram α)
    (f : α × α → M) :
    ∑ p ∈ σ.resolvableInversions, f p =
      ∑ p ∈ (σ.source ×ˢ σ.source).filter (fun p : α × α ↦ p.1 < p.2),
        if p ∈ σ.resolvableInversions then f p else 0 := by
  rw [← sum_filter]
  congr 1
  ext p
  simp only [mem_filter, mem_product]
  refine ⟨fun hp ↦ ⟨?_, hp⟩, And.right⟩
  have hp' := resolvableInversions_subset_inversions σ hp
  exact ⟨⟨fst_mem_source_of_mem_inversions hp', snd_mem_source_of_mem_inversions hp'⟩,
    (mem_inversions.1 hp').1⟩

/-- When `φ` ends where `ψ` starts, the end points `g x ∈ φ x` of the strands of `φ` identify the
increasing pairs of starting points of `φ` with those of `ψ`, after sorting. -/
private theorem sum_filter_lt_source_eq_of_target_eq {M : Type*} [AddCommMonoid M]
    {φ ψ : StrandDiagram α} (hT : φ.target = ψ.source) {g : α → α}
    (hg : ∀ x ∈ φ.source, g x ∈ φ x) (f : α × α → M) :
    ∑ q ∈ (ψ.source ×ˢ ψ.source).filter (fun q : α × α ↦ q.1 < q.2), f q =
      ∑ p ∈ (φ.source ×ˢ φ.source).filter (fun p : α × α ↦ p.1 < p.2),
        f (min (g p.1) (g p.2), max (g p.1) (g p.2)) := by
  -- The starting point `g' t` of the strand of `φ` ending at `t`.
  set g' : α → α := fun t ↦ (φ.toPEquiv.symm t).getD t with hg'_def
  have hg' {t : α} (ht : t ∈ ψ.source) : g' t ∈ φ.source ∧ t ∈ φ (g' t) := by
    rw [← hT] at ht
    obtain ⟨x, hx⟩ := mem_target.1 ht
    have hs : φ.toPEquiv.symm t = some x := (PEquiv.eq_some_iff _).2 hx
    simp only [hg'_def, hs, Option.getD_some]
    exact ⟨mem_source.2 ⟨t, hx⟩, hx⟩
  have hgT {x : α} (hx : x ∈ φ.source) : g x ∈ ψ.source := hT ▸ mem_target.2 ⟨x, hg x hx⟩
  have hg'g {x : α} (hx : x ∈ φ.source) : g' (g x) = x := by
    have hs : φ.toPEquiv.symm (g x) = some x := (PEquiv.eq_some_iff _).2 (hg x hx)
    simp only [hg'_def, hs, Option.getD_some]
  have hgg' {t : α} (ht : t ∈ ψ.source) : g (g' t) = t :=
    Option.mem_unique (hg _ (hg' ht).1) (hg' ht).2
  symm
  refine sum_nbij' (fun p ↦ (min (g p.1) (g p.2), max (g p.1) (g p.2)))
    (fun q ↦ (min (g' q.1) (g' q.2), max (g' q.1) (g' q.2))) ?_ ?_ ?_ ?_ fun _ _ ↦ rfl
  · rintro ⟨x, y⟩ hp
    simp only [mem_filter, mem_product] at hp ⊢
    obtain ⟨⟨hx, hy⟩, hxy⟩ := hp
    refine ⟨⟨?_, ?_⟩, min_lt_max.2 (φ.ne_of_mem_of_mem_of_ne (hg x hx) (hg y hy) hxy.ne)⟩
    · rcases min_choice (g x) (g y) with h | h <;> rw [h]
      exacts [hgT hx, hgT hy]
    · rcases max_choice (g x) (g y) with h | h <;> rw [h]
      exacts [hgT hx, hgT hy]
  · rintro ⟨t, t'⟩ hq
    simp only [mem_filter, mem_product] at hq ⊢
    obtain ⟨⟨ht, ht'⟩, htt'⟩ := hq
    refine ⟨⟨?_, ?_⟩, min_lt_max.2 fun h ↦ htt'.ne ?_⟩
    · rcases min_choice (g' t) (g' t') with h | h <;> rw [h]
      exacts [(hg' ht).1, (hg' ht').1]
    · rcases max_choice (g' t) (g' t') with h | h <;> rw [h]
      exacts [(hg' ht).1, (hg' ht').1]
    · rw [← hgg' ht, ← hgg' ht', h]
  · rintro ⟨x, y⟩ hp
    simp only [mem_filter, mem_product] at hp
    obtain ⟨⟨hx, hy⟩, hxy⟩ := hp
    dsimp only
    rw [min_apply_min_max, max_apply_min_max, hg'g hx, hg'g hy, min_eq_left hxy.le,
      max_eq_right hxy.le]
  · rintro ⟨t, t'⟩ hq
    simp only [mem_filter, mem_product] at hq
    obtain ⟨⟨ht, ht'⟩, htt'⟩ := hq
    dsimp only
    rw [min_apply_min_max, max_apply_min_max, hgg' ht, hgg' ht', min_eq_left htt'.le,
      max_eq_right htt'.le]

/-- **The Leibniz rule for basis elements.** -/
theorem differential_of_mul_of [CharP R 2] (φ ψ : StrandDiagram α) :
    differential R α (of φ * of ψ) =
      differential R α (of φ) * of ψ + of φ * differential R α (of ψ) := by
  by_cases hT : φ.target = ψ.source
  swap
  · -- All three terms vanish when `φ` does not end where `ψ` starts.
    have h₁ (p : α × α) : (of (φ.resolve p) * of ψ : StrandsAlgebra R α) = 0 :=
      of_mul_of_of_not_composable fun h ↦ hT (by simpa using h.target_eq)
    have h₂ (q : α × α) : (of φ * of (ψ.resolve q) : StrandsAlgebra R α) = 0 :=
      of_mul_of_of_not_composable fun h ↦ hT (by simpa using h.target_eq)
    rw [of_mul_of_of_not_composable fun h ↦ hT h.target_eq, map_zero, differential_of,
      differential_of, sum_mul, mul_sum]
    simp [h₁, h₂]
  -- The end point `g x` of the strand from `x`.
  set g : α → α := fun x ↦ (φ x).getD x with hg_def
  have hg {x : α} (hx : x ∈ φ.source) : g x ∈ φ x := by
    obtain ⟨a, ha⟩ := mem_source.1 hx
    rw [Option.mem_def] at ha ⊢
    simp [hg_def, ha]
  -- Write the three terms as sums over the increasing pairs of starting points of `φ`.
  have hL : differential R α (of φ * of ψ) =
      ∑ p ∈ (φ.source ×ˢ φ.source).filter (fun p : α × α ↦ p.1 < p.2),
        if φ.Composable ψ ∧ p ∈ (φ.trans ψ).resolvableInversions then
          of ((φ.trans ψ).resolve p) else 0 := by
    rw [of_mul_of]
    split_ifs with hc
    · rw [differential_of, sum_resolvableInversions_eq, source_trans_of_target_eq hT]
      simp [hc]
    · simp [hc]
  have h₁ : differential R α (of φ) * of ψ =
      ∑ p ∈ (φ.source ×ˢ φ.source).filter (fun p : α × α ↦ p.1 < p.2),
        if p ∈ φ.resolvableInversions ∧ (φ.resolve p).Composable ψ then
          of ((φ.resolve p).trans ψ) else 0 := by
    rw [differential_of, sum_mul, sum_resolvableInversions_eq]
    simp only [of_mul_of, ite_and]
  have h₂ : of φ * differential R α (of ψ) =
      ∑ p ∈ (φ.source ×ˢ φ.source).filter (fun p : α × α ↦ p.1 < p.2),
        if (min (g p.1) (g p.2), max (g p.1) (g p.2)) ∈ ψ.resolvableInversions ∧
          φ.Composable (ψ.resolve (min (g p.1) (g p.2), max (g p.1) (g p.2))) then
          of (φ.trans (ψ.resolve (min (g p.1) (g p.2), max (g p.1) (g p.2)))) else 0 := by
    rw [differential_of, mul_sum, sum_resolvableInversions_eq,
      sum_filter_lt_source_eq_of_target_eq hT fun _ ↦ hg]
    simp only [of_mul_of, ite_and]
  rw [hL, h₁, h₂, ← sum_add_distrib]
  refine sum_congr rfl fun p hp ↦ ?_
  obtain ⟨i, j⟩ := p
  obtain ⟨⟨hi, hj⟩, hij⟩ : (i ∈ φ.source ∧ j ∈ φ.source) ∧ i < j := by
    simpa only [mem_filter, mem_product] using hp
  dsimp only
  -- Compare the three terms at the pair `(i, j)`.
  have key := composable_and_mem_resolvableInversions_trans_iff hT hij (hg hi) (hg hj)
  by_cases c₁ : (i, j) ∈ φ.resolvableInversions ∧ (φ.resolve (i, j)).Composable ψ <;>
    by_cases c₂ : (min (g i) (g j), max (g i) (g j)) ∈ ψ.resolvableInversions ∧
      φ.Composable (ψ.resolve (min (g i) (g j), max (g i) (g j)))
  · rw [ite_eq_right (by rw [key, eq_true c₁, eq_true c₂]; simp), ite_eq_left c₁, ite_eq_left c₂,
      resolve_trans_eq_trans_resolve (hg hi) (hg hj)
        (resolvableInversions_subset_inversions _ c₁.1)
        (resolvableInversions_subset_inversions _ c₂.1), ← two_smul R, CharTwo.two_eq_zero,
      zero_smul]
  · have hl := key.2 (by rw [eq_true c₁, eq_false c₂]; simp)
    rw [ite_eq_left hl, ite_eq_left c₁, ite_eq_right c₂, add_zero,
      trans_resolve_eq_resolve_trans (resolvableInversions_subset_inversions _ c₁.1)
        (resolvableInversions_subset_inversions _ hl.2)]
  · have hl := key.2 (by rw [eq_false c₁, eq_true c₂]; simp)
    rw [ite_eq_left hl, ite_eq_right c₁, ite_eq_left c₂, zero_add,
      trans_resolve_eq_trans_resolve (hg hi) (hg hj)
        (resolvableInversions_subset_inversions _ c₂.1)
        (resolvableInversions_subset_inversions _ hl.2)]
  · rw [ite_eq_right (by rw [key, eq_false c₁, eq_false c₂]; simp), ite_eq_right c₁,
      ite_eq_right c₂, add_zero]

/-- **The Leibniz rule** for the differential of the strands algebra over a ring of characteristic
two. -/
theorem differential_mul [CharP R 2] (x y : StrandsAlgebra R α) :
    differential R α (x * y) = differential R α x * y + x * differential R α y := by
  induction x using induction_on with
  | zero => simp
  | add x x' hx hx' =>
    simp only [add_mul, map_add, hx, hx']
    abel
  | smul_of r φ =>
    induction y using induction_on with
    | zero => simp
    | add y y' hy hy' =>
      simp only [mul_add, map_add, hy, hy']
      abel
    | smul_of r' ψ =>
      simp only [smul_mul_assoc, mul_smul_comm, map_smul, differential_of_mul_of, smul_add]

private theorem chains_def (φ : StrandDiagram α) :
    φ.resolvableInversions.sigma (fun p ↦ (φ.resolve p).resolvableInversions) = φ.chains :=
  rfl

/-- The differential squares to zero on a strand diagram, over a ring of characteristic two: the
two-step resolution chains cancel in pairs. -/
theorem differential_differential_of [CharP R 2] (φ : StrandDiagram α) :
    differential R α (differential R α (of φ)) = 0 := by
  rw [differential_of, map_sum]
  simp only [differential_of]
  rw [sum_sigma', chains_def]
  refine sum_involution (fun x _ ↦ φ.chainPartner x) (fun x hx ↦ ?_)
    (fun x hx _ ↦ (chainPartner_spec hx).2.1) (fun x hx ↦ (chainPartner_spec hx).1)
    (fun x hx ↦ (chainPartner_spec hx).2.2.1)
  rw [(chainPartner_spec hx).2.2.2, ← two_smul R, CharTwo.two_eq_zero, zero_smul]

/-- **The differential of the strands algebra squares to zero** over a ring of characteristic two.
-/
@[simp]
theorem differential_differential [CharP R 2] (x : StrandsAlgebra R α) :
    differential R α (differential R α x) = 0 := by
  induction x using induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | smul_of r φ => simp [differential_differential_of]

/-- Over a ring of characteristic two, such as `𝔽₂`, the strands algebra with its differential is
an ungraded differential algebra. -/
theorem isUngradedDGAlgebra_differential {R : Type*} [CommRing R] [CharP R 2] :
    IsUngradedDGAlgebra (differential R α) :=
  ⟨differential_mul, differential_differential⟩

end StrandsAlgebra

end TauCeti
