/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.StrandDiagram
import Mathlib.Algebra.Group.End
import TauCeti.Logic.Equiv.Basic

/-!
# Resolving a crossing of a strand diagram

The differential of the strands algebra of Lipshitz, Ozsváth and Thurston sums over the ways of
*resolving* (smoothing) one crossing of a strand diagram. If the strands starting at `i < j` cross,
`φ j < φ i`, the resolution exchanges their end points: the new diagram sends `i` to `φ j` and `j`
to `φ i`, and agrees with `φ` elsewhere (`TauCeti.StrandDiagram.resolve`). It is again a strand
diagram, with the same starting and ending points, and it has strictly fewer crossings
(`TauCeti.StrandDiagram.inversionCount_resolve_lt`), because its crossings correspond to distinct
crossings of `φ` other than `(i, j)` (`Finset.card_inversions_comp_swap_lt`). The count drops by
exactly one unless some third strand runs between the two resolved strands at both ends, in which
case the picture of the resolved diagram has a double crossing. The differential keeps only the
crossings whose resolution lowers the count by exactly one
(`TauCeti.StrandDiagram.resolvableInversions`).

This file also records how resolutions interact with concatenation and with each other, as needed
for the Leibniz rule and for `d ∘ d = 0`.

* Resolving a crossing of the concatenation `φ.trans ψ` is the same as resolving it in the piece
  where it occurs: in `φ` (`TauCeti.StrandDiagram.trans_resolve_eq_resolve_trans`), or in `ψ` at
  the end points in `φ` of the two strands (`TauCeti.StrandDiagram.trans_resolve_eq_trans_resolve`).
  When the two strands cross in both pieces, resolving the crossing in either piece gives the same
  concatenation (`TauCeti.StrandDiagram.resolve_trans_eq_trans_resolve`).
* Resolutions at disjoint pairs of strands commute (`TauCeti.StrandDiagram.resolve_resolve_comm`).
  Resolutions at two pairs sharing a strand satisfy the three-cycle relation of transpositions
  (`TauCeti.StrandDiagram.resolve_resolve_eq_resolve_resolve`).

## Main definitions

* `TauCeti.StrandDiagram.resolve φ p`: the resolution of `φ` at the crossing `p`, or `φ` itself if
  `p` is not a crossing.
* `TauCeti.StrandDiagram.resolvableInversions φ`: the crossings of `φ` whose resolution has exactly
  one crossing fewer.

## Main results

* `TauCeti.StrandDiagram.source_resolve`, `TauCeti.StrandDiagram.target_resolve`: resolving keeps
  the starting and ending points.
* `TauCeti.StrandDiagram.inversionCount_resolve_lt`: resolving a crossing lowers the number of
  crossings.
* `TauCeti.StrandDiagram.trans_resolve_eq_resolve_trans`,
  `TauCeti.StrandDiagram.trans_resolve_eq_trans_resolve`,
  `TauCeti.StrandDiagram.resolve_trans_eq_trans_resolve`: resolving a crossing of a concatenation.
* `TauCeti.StrandDiagram.resolve_resolve_comm`,
  `TauCeti.StrandDiagram.resolve_resolve_eq_resolve_resolve`: two successive resolutions.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.1,
  Definition 3.2 (the differential of the strands algebra `A(n, k)`, which resolves crossings).
-/

public section

open Finset

namespace TauCeti

namespace StrandDiagram

variable {α : Type*} [LinearOrder α] [Fintype α]

/-- The resolution of a crossing `p = (i, j)` of a strand diagram `φ`: the diagram that sends `i`
to `φ j` and `j` to `φ i` and otherwise agrees with `φ`. Pictorially the crossing is smoothed. When
`p` is not a crossing of `φ`, the resolution is `φ` itself. -/
def resolve (φ : StrandDiagram α) (p : α × α) : StrandDiagram α :=
  if h : p ∈ φ.inversions then
    { toPEquiv := (Equiv.swap p.1 p.2).toPEquiv.trans φ.toPEquiv
      le_of_mem' := by
        obtain ⟨hlt, a, ha, b, hb, hba⟩ := mem_inversions.1 h
        intro x y hy
        obtain ⟨z, hz, hy⟩ := (PEquiv.mem_trans _ _ _ _).1 hy
        rw [Equiv.toPEquiv_apply, Option.mem_def, Option.some_inj] at hz
        subst hz
        rcases eq_or_ne x p.1 with rfl | h₁
        · rw [Equiv.swap_apply_left] at hy
          exact hlt.le.trans (φ.le_of_mem hy)
        rcases eq_or_ne x p.2 with rfl | h₂
        · rw [Equiv.swap_apply_right, Option.mem_unique hy ha] at *
          exact (φ.le_of_mem hb).trans hba.le
        rw [Equiv.swap_apply_of_ne_of_ne h₁ h₂] at hy
        exact φ.le_of_mem hy }
  else φ

variable {φ ψ : StrandDiagram α} {p q : α × α}

theorem toPEquiv_resolve (h : p ∈ φ.inversions) :
    (φ.resolve p).toPEquiv = (Equiv.swap p.1 p.2).toPEquiv.trans φ.toPEquiv := by
  simp [resolve, h]

theorem resolve_apply (h : p ∈ φ.inversions) (x : α) :
    φ.resolve p x = φ (Equiv.swap p.1 p.2 x) := by
  refine Option.ext fun y ↦ ?_
  rw [← coe_toPEquiv, toPEquiv_resolve h, PEquiv.trans_eq_some]
  simp

@[simp]
theorem resolve_of_notMem (h : p ∉ φ.inversions) : φ.resolve p = φ := by
  simp [resolve, h]

/-- The resolution at a crossing written as the sorted pair of its two starting points. -/
theorem resolve_min_max_apply {x y : α} (h : (min x y, max x y) ∈ φ.inversions) (z : α) :
    φ.resolve (min x y, max x y) z = φ (Equiv.swap x y z) := by
  rw [resolve_apply h, Equiv.swap_min_max]

/-- The transposition of the two strands of a crossing preserves the starting points. -/
theorem swap_mem_source_iff (h : p ∈ φ.inversions) {x : α} :
    Equiv.swap p.1 p.2 x ∈ φ.source ↔ x ∈ φ.source := by
  rcases eq_or_ne x p.1 with rfl | h₁
  · simp [fst_mem_source_of_mem_inversions h, snd_mem_source_of_mem_inversions h]
  rcases eq_or_ne x p.2 with rfl | h₂
  · simp [fst_mem_source_of_mem_inversions h, snd_mem_source_of_mem_inversions h]
  rw [Equiv.swap_apply_of_ne_of_ne h₁ h₂]

@[simp]
theorem source_resolve (φ : StrandDiagram α) (p : α × α) : (φ.resolve p).source = φ.source := by
  by_cases h : p ∈ φ.inversions
  · ext x
    rw [← swap_mem_source_iff h, mem_source, mem_source, resolve_apply h]
  · rw [resolve_of_notMem h]

@[simp]
theorem target_resolve (φ : StrandDiagram α) (p : α × α) : (φ.resolve p).target = φ.target := by
  by_cases h : p ∈ φ.inversions
  · ext y
    simp only [mem_target, resolve_apply h]
    exact ⟨fun ⟨x, hx⟩ ↦ ⟨_, hx⟩, fun ⟨x, hx⟩ ↦ ⟨Equiv.swap p.1 p.2 x, by simpa using hx⟩⟩
  · rw [resolve_of_notMem h]

/-- The crossings of a resolution are the inversions of the end-point map of `φ` composed with the
transposition of the two resolved strands. -/
theorem inversions_resolve (h : p ∈ φ.inversions) :
    (φ.resolve p).inversions = φ.source.inversions (φ.endpoint ∘ Equiv.swap p.1 p.2) := by
  rw [inversions_def, source_resolve]
  refine Finset.inversions_congr fun x hx ↦ ?_
  obtain ⟨c, hc⟩ := mem_source.1 ((swap_mem_source_iff h).2 hx)
  rw [Function.comp_apply, endpoint_eq_of_mem hc, endpoint_eq_of_mem (by rwa [resolve_apply h])]

/-- **Resolving a crossing lowers the number of crossings.** -/
theorem inversionCount_resolve_lt (h : p ∈ φ.inversions) :
    (φ.resolve p).inversionCount < φ.inversionCount := by
  rw [inversionCount_def, inversionCount_def, inversions_resolve h, inversions_def φ]
  exact Finset.card_inversions_comp_swap_lt (by rwa [inversions_def] at h)

/-- A resolved crossing is no longer a crossing. -/
theorem notMem_inversions_resolve_self : p ∉ (φ.resolve p).inversions := by
  by_cases h : p ∈ φ.inversions
  · obtain ⟨hlt, a, ha, b, hb, -⟩ := mem_inversions.1 h
    rw [mem_inversions, resolve_apply h, resolve_apply h, Equiv.swap_apply_left,
      Equiv.swap_apply_right]
    rintro ⟨-, a', ha', b', hb', hba'⟩
    rw [Option.mem_unique ha' hb, Option.mem_unique hb' ha] at hba'
    obtain ⟨-, a'', ha'', b'', hb'', hab⟩ := mem_inversions.1 h
    rw [Option.mem_unique ha'' ha, Option.mem_unique hb'' hb] at hab
    exact hab.not_gt hba'
  · rwa [resolve_of_notMem h]

/-- A pair of strands disjoint from a resolved crossing crosses after the resolution exactly when
it crossed before. -/
theorem mem_inversions_resolve_iff_of_ne (h₁ : q.1 ≠ p.1)
    (h₂ : q.1 ≠ p.2) (h₃ : q.2 ≠ p.1) (h₄ : q.2 ≠ p.2) :
    q ∈ (φ.resolve p).inversions ↔ q ∈ φ.inversions := by
  by_cases h : p ∈ φ.inversions
  · rw [mem_inversions, mem_inversions, resolve_apply h, resolve_apply h,
      Equiv.swap_apply_of_ne_of_ne h₁ h₂, Equiv.swap_apply_of_ne_of_ne h₃ h₄]
  · rw [resolve_of_notMem h]

omit [Fintype α] in
/-- Precomposing with the transposition of two strands is postcomposing with the transposition of
their end points. -/
theorem swap_trans_eq_trans_swap {a b : α} (ha : a ∈ φ p.1) (hb : b ∈ φ p.2) :
    (Equiv.swap p.1 p.2).toPEquiv.trans φ.toPEquiv =
      φ.toPEquiv.trans (Equiv.swap a b).toPEquiv := by
  refine PEquiv.ext fun x ↦ Option.ext fun y ↦ ?_
  simp only [PEquiv.trans_eq_some, Equiv.toPEquiv_apply, Option.some.injEq, exists_eq_left',
    coe_toPEquiv]
  rw [Option.mem_def] at ha hb
  rcases eq_or_ne x p.1 with rfl | h₁
  · simp [ha, hb]
  rcases eq_or_ne x p.2 with rfl | h₂
  · simp [ha, hb]
  rw [Equiv.swap_apply_of_ne_of_ne h₁ h₂]
  cases hx : φ x with
  | none => simp
  | some c =>
    simp [Equiv.swap_apply_of_ne_of_ne (φ.ne_of_mem_of_mem_of_ne hx ha h₁)
      (φ.ne_of_mem_of_mem_of_ne hx hb h₂)]

section Trans

variable {a b : α}

/-- Resolving, in a concatenation, a crossing of the first piece is resolving it in that piece. -/
theorem trans_resolve_eq_resolve_trans (h : p ∈ φ.inversions) (h' : p ∈ (φ.trans ψ).inversions) :
    (φ.trans ψ).resolve p = (φ.resolve p).trans ψ := by
  refine toPEquiv_injective ?_
  rw [toPEquiv_resolve h', toPEquiv_trans, toPEquiv_trans, toPEquiv_resolve h,
    PEquiv.trans_assoc]

/-- Resolving, in a concatenation, a crossing that comes from the second piece is resolving it in
that piece: there the two strands start at their end points `a` and `b` in the first piece. -/
theorem trans_resolve_eq_trans_resolve (ha : a ∈ φ p.1) (hb : b ∈ φ p.2)
    (h : (min a b, max a b) ∈ ψ.inversions) (h' : p ∈ (φ.trans ψ).inversions) :
    (φ.trans ψ).resolve p = φ.trans (ψ.resolve (min a b, max a b)) := by
  refine toPEquiv_injective ?_
  rw [toPEquiv_resolve h', toPEquiv_trans, toPEquiv_trans, toPEquiv_resolve h,
    ← PEquiv.trans_assoc, swap_trans_eq_trans_swap ha hb, PEquiv.trans_assoc, Equiv.swap_min_max]

/-- When the strands starting at `p.1` and `p.2`, with end points `a` and `b` in `φ`, cross in
both pieces of a concatenation, resolving the crossing in either piece gives the same
concatenation. -/
theorem resolve_trans_eq_trans_resolve (ha : a ∈ φ p.1) (hb : b ∈ φ p.2)
    (h : p ∈ φ.inversions) (h' : (min a b, max a b) ∈ ψ.inversions) :
    (φ.resolve p).trans ψ = φ.trans (ψ.resolve (min a b, max a b)) := by
  refine toPEquiv_injective ?_
  rw [toPEquiv_trans, toPEquiv_trans, toPEquiv_resolve h, toPEquiv_resolve h',
    swap_trans_eq_trans_swap ha hb, Equiv.swap_min_max, PEquiv.trans_assoc]

end Trans

/-- **Resolutions of disjoint pairs of strands commute.** -/
theorem resolve_resolve_comm (hp : p ∈ φ.inversions) (hq : q ∈ φ.inversions)
    (h₁ : q.1 ≠ p.1) (h₂ : q.1 ≠ p.2) (h₃ : q.2 ≠ p.1) (h₄ : q.2 ≠ p.2) :
    (φ.resolve p).resolve q = (φ.resolve q).resolve p := by
  have hp' : p ∈ (φ.resolve q).inversions :=
    (mem_inversions_resolve_iff_of_ne h₁.symm h₃.symm h₂.symm h₄.symm).2 hp
  have hq' : q ∈ (φ.resolve p).inversions := (mem_inversions_resolve_iff_of_ne h₁ h₂ h₃ h₄).2 hq
  refine toPEquiv_injective ?_
  rw [toPEquiv_resolve hq', toPEquiv_resolve hp', toPEquiv_resolve hp, toPEquiv_resolve hq,
    ← PEquiv.trans_assoc, ← PEquiv.trans_assoc, ← Equiv.toPEquiv_trans, ← Equiv.toPEquiv_trans]
  congr 2
  -- Conjugating `swap q.1 q.2` by `swap p.1 p.2`, which fixes `q.1` and `q.2`, gives it back.
  have hc := Equiv.swap_apply_apply (Equiv.swap p.1 p.2) q.1 q.2
  rw [Equiv.swap_apply_of_ne_of_ne h₁ h₂, Equiv.swap_apply_of_ne_of_ne h₃ h₄,
    eq_mul_inv_iff_mul_eq] at hc
  ext x
  simpa [Equiv.Perm.mul_apply] using (congrArg (· x) hc).symm

/-- **The three-cycle relation for resolutions.** For three strands starting at distinct points `s`,
`u` and `w`, resolving the pair `{s, u}` and then `{s, w}` gives the same diagram as resolving
`{s, w}` and then `{u, w}`. -/
theorem resolve_resolve_eq_resolve_resolve {s u w : α}
    (h₁ : (min s u, max s u) ∈ φ.inversions)
    (h₂ : (min s w, max s w) ∈ (φ.resolve (min s u, max s u)).inversions)
    (h₃ : (min s w, max s w) ∈ φ.inversions)
    (h₄ : (min u w, max u w) ∈ (φ.resolve (min s w, max s w)).inversions) :
    (φ.resolve (min s u, max s u)).resolve (min s w, max s w) =
      (φ.resolve (min s w, max s w)).resolve (min u w, max u w) := by
  have hsu : s ≠ u := by
    rintro rfl
    simpa using (mem_inversions.1 h₁).1
  have huw : u ≠ w := by
    rintro rfl
    simpa using (mem_inversions.1 h₄).1
  refine toPEquiv_injective ?_
  rw [toPEquiv_resolve h₂, toPEquiv_resolve h₁, toPEquiv_resolve h₄, toPEquiv_resolve h₃,
    ← PEquiv.trans_assoc, ← PEquiv.trans_assoc, ← Equiv.toPEquiv_trans, ← Equiv.toPEquiv_trans]
  simp only [Equiv.swap_min_max]
  congr 2
  -- Conjugating `swap u w` by `swap s w` gives `swap s u`.
  have hc := Equiv.swap_mul_swap_mul_swap huw hsu.symm
  rw [Equiv.swap_comm w s] at hc
  have hc' : Equiv.swap s u * Equiv.swap s w = Equiv.swap s w * Equiv.swap u w := by
    rw [← hc, mul_assoc, Equiv.swap_mul_self, mul_one]
  ext x
  simpa [Equiv.Perm.mul_apply] using congrArg (· x) hc'

/-- The crossings of `φ` whose resolution has exactly one crossing fewer than `φ`. These are the
crossings whose resolution, drawn by smoothing the crossing, has no pair of strands crossing twice;
the differential of the strands algebra sums the resolutions at these crossings. -/
def resolvableInversions (φ : StrandDiagram α) : Finset (α × α) :=
  {p ∈ φ.inversions | (φ.resolve p).inversionCount + 1 = φ.inversionCount}

@[simp]
theorem mem_resolvableInversions :
    p ∈ φ.resolvableInversions ↔
      p ∈ φ.inversions ∧ (φ.resolve p).inversionCount + 1 = φ.inversionCount :=
  mem_filter

theorem resolvableInversions_subset_inversions (φ : StrandDiagram α) :
    φ.resolvableInversions ⊆ φ.inversions :=
  filter_subset _ _

@[simp]
theorem resolvableInversions_idOn (s : Finset α) : (idOn s).resolvableInversions = ∅ := by
  simp [resolvableInversions]

end StrandDiagram

end TauCeti
