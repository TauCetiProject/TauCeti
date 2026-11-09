/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Resolution

/-!
# Moving horizontal strands

The algebra `A(Z)` of a pointed matched circle `Z` is built from the strands algebra by summing
strand diagrams over the ways of placing each horizontal strand at one of two matched points
(Lipshitz, Ozsváth and Thurston). This file develops the elementary step relating the terms of
such a sum: moving a horizontal strand of a strand diagram from `a` to a point `b` at which no
strand starts or ends (`TauCeti.StrandDiagram.swapHorizontal`). The moved diagram is the conjugate
of the diagram by the transposition of `a` and `b`, and moving twice gives the diagram back.

Moving the strand changes the crossings: those of other strands with a horizontal strand at `a`
are replaced by those with a horizontal strand at `b`
(`TauCeti.StrandDiagram.inversionCount_swapHorizontal_add`). The number of strands crossing a
horizontal strand at a point (`TauCeti.StrandDiagram.crossingCount`) adds up under concatenation and
is unchanged by resolving a crossing, since an upward strand crosses a horizontal one at most once.
Hence moving a horizontal strand that runs through both pieces of a nonzero product of diagrams
gives a nonzero product (`TauCeti.StrandDiagram.Composable.swapHorizontal`), and it neither creates
nor destroys resolvable crossings of the other strands
(`TauCeti.StrandDiagram.mem_resolvableInversions_swapHorizontal_iff`). These are the facts behind
the closure of the matched subalgebra (`TauCeti.StrandsAlgebra.matchedSubalgebra`) under the
product and the differential.

## Main definitions

* `TauCeti.StrandDiagram.CanMoveHorizontal φ a b`: `φ` has a horizontal strand at `a`, and no
  strand of `φ` starts or ends at `b`.
* `TauCeti.StrandDiagram.swapHorizontal φ a b`: the diagram `φ` with its horizontal strand moved
  between `a` and `b`, or `φ` itself when no such move is possible.
* `TauCeti.StrandDiagram.crossingCount φ c`: the number of strands of `φ` crossing a horizontal
  strand at `c`.

## Main results

* `TauCeti.StrandDiagram.swapHorizontal_swapHorizontal`: moving a horizontal strand is an
  involution.
* `TauCeti.StrandDiagram.inversionCount_swapHorizontal_add`: the change in the number of crossings.
* `TauCeti.StrandDiagram.swapHorizontal_trans_swapHorizontal`,
  `TauCeti.StrandDiagram.Composable.swapHorizontal`: moving a horizontal strand in both pieces of a
  product.
* `TauCeti.StrandDiagram.resolve_swapHorizontal`,
  `TauCeti.StrandDiagram.mem_resolvableInversions_swapHorizontal_iff`: moving a horizontal strand
  commutes with resolving a crossing.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.1 (the
  strands algebra and its differential) and §3.2 (the algebra of a pointed matched circle, whose
  elements sum over the placements of horizontal strands at matched points).
-/

public section

open Finset

namespace TauCeti

namespace StrandDiagram

variable {α : Type*} [LinearOrder α] [Fintype α] {φ ψ : StrandDiagram α} {a b c x y : α}
  {q : α × α}

/-! ### Moving a horizontal strand -/

/-- `φ` has a horizontal strand at `a`, and no strand of `φ` starts or ends at `b`, so that the
horizontal strand can be moved from `a` to `b` (`TauCeti.StrandDiagram.swapHorizontal`). -/
def CanMoveHorizontal (φ : StrandDiagram α) (a b : α) : Prop :=
  φ a = some a ∧ b ∉ φ.source ∧ b ∉ φ.target

theorem canMoveHorizontal_iff :
    φ.CanMoveHorizontal a b ↔ φ a = some a ∧ b ∉ φ.source ∧ b ∉ φ.target :=
  (Iff.rfl)

instance (φ : StrandDiagram α) (a b : α) : Decidable (φ.CanMoveHorizontal a b) :=
  decidable_of_iff _ canMoveHorizontal_iff.symm

theorem CanMoveHorizontal.mem (h : φ.CanMoveHorizontal a b) : a ∈ φ a :=
  h.1

theorem CanMoveHorizontal.notMem_source (h : φ.CanMoveHorizontal a b) : b ∉ φ.source :=
  h.2.1

theorem CanMoveHorizontal.notMem_target (h : φ.CanMoveHorizontal a b) : b ∉ φ.target :=
  h.2.2

theorem CanMoveHorizontal.ne (h : φ.CanMoveHorizontal a b) : a ≠ b := by
  rintro rfl
  exact h.notMem_source (mem_source.2 ⟨a, h.mem⟩)

theorem CanMoveHorizontal.not_symm (h : φ.CanMoveHorizontal a b) : ¬φ.CanMoveHorizontal b a :=
  fun h' ↦ h.notMem_source (mem_source.2 ⟨b, h'.mem⟩)

/-- The partial bijection `φ` conjugated by the transposition of `a` and `b`. -/
private def conjSwap (φ : StrandDiagram α) (a b : α) : α ≃. α :=
  (Equiv.swap a b).toPEquiv.trans (φ.toPEquiv.trans (Equiv.swap a b).toPEquiv)

omit [Fintype α] in
private theorem conjSwap_comm (φ : StrandDiagram α) (a b : α) :
    φ.conjSwap a b = φ.conjSwap b a := by
  rw [conjSwap, conjSwap, Equiv.swap_comm]

private theorem mem_conjSwap_iff (h : φ.CanMoveHorizontal a b) :
    y ∈ φ.conjSwap a b x ↔ (x = b ∧ y = b) ∨ (x ≠ a ∧ x ≠ b ∧ y ∈ φ x) := by
  rw [conjSwap, Option.mem_def]
  simp only [PEquiv.trans_eq_some, Equiv.toPEquiv_apply, Option.some.injEq, exists_eq_left',
    coe_toPEquiv, Option.mem_def]
  have hab := h.ne
  rcases eq_or_ne x a with rfl | hxa
  · rw [Equiv.swap_apply_left]
    have : φ b = none := apply_eq_none_of_notMem_source h.notMem_source
    simp [this, hab]
  rcases eq_or_ne x b with rfl | hxb
  · have ha : φ a = some a := h.mem
    rw [Equiv.swap_apply_right]
    simp [ha, eq_comm]
  rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
  simp only [hxa, hxb, ne_eq, not_false_eq_true, true_and, false_and, false_or]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hza : z ≠ a := fun hza ↦ hxa (φ.eq_of_mem_of_mem hz (hza ▸ h.mem))
    have hzb : z ≠ b := fun hzb ↦ h.notMem_target (mem_target.2 ⟨x, hzb ▸ hz⟩)
    rwa [Equiv.swap_apply_of_ne_of_ne hza hzb]
  · intro hy
    have hya : y ≠ a := fun hya ↦ hxa (φ.eq_of_mem_of_mem (hya ▸ hy) h.mem)
    have hyb : y ≠ b := fun hyb ↦ h.notMem_target (mem_target.2 ⟨x, hyb ▸ hy⟩)
    exact ⟨y, hy, Equiv.swap_apply_of_ne_of_ne hya hyb⟩

private theorem le_of_mem_conjSwap (h : φ.CanMoveHorizontal a b) (hy : y ∈ φ.conjSwap a b x) :
    x ≤ y := by
  rcases (mem_conjSwap_iff h).1 hy with ⟨rfl, rfl⟩ | ⟨-, -, hy⟩
  exacts [le_rfl, φ.le_of_mem hy]

/-- The strand diagram `φ` with a horizontal strand moved between `a` and `b`: if `φ` has a
horizontal strand at one of `a` and `b` and no strand starts or ends at the other, the horizontal
strand is moved to the other point, and otherwise `φ` is unchanged. When such a move is possible,
the result is the conjugate of `φ` by the transposition of `a` and `b`. -/
def swapHorizontal (φ : StrandDiagram α) (a b : α) : StrandDiagram α :=
  if h : φ.CanMoveHorizontal a b then ⟨φ.conjSwap a b, fun _ _ ↦ le_of_mem_conjSwap h⟩
  else if h' : φ.CanMoveHorizontal b a then ⟨φ.conjSwap b a, fun _ _ ↦ le_of_mem_conjSwap h'⟩
  else φ

theorem mem_swapHorizontal (h : φ.CanMoveHorizontal a b) :
    y ∈ φ.swapHorizontal a b x ↔ (x = b ∧ y = b) ∨ (x ≠ a ∧ x ≠ b ∧ y ∈ φ x) := by
  rw [swapHorizontal, dite_eq_left h, ← mem_conjSwap_iff h]
  rfl

theorem swapHorizontal_comm (φ : StrandDiagram α) (a b : α) :
    φ.swapHorizontal a b = φ.swapHorizontal b a := by
  by_cases h : φ.CanMoveHorizontal a b
  · rw [swapHorizontal, dite_eq_left h, swapHorizontal, dite_eq_right h.not_symm, dite_eq_left h]
  by_cases h' : φ.CanMoveHorizontal b a
  · rw [swapHorizontal, dite_eq_right h, dite_eq_left h', swapHorizontal, dite_eq_left h']
  · rw [swapHorizontal, dite_eq_right h, dite_eq_right h', swapHorizontal, dite_eq_right h',
      dite_eq_right h]

theorem swapHorizontal_of_not (h : ¬φ.CanMoveHorizontal a b) (h' : ¬φ.CanMoveHorizontal b a) :
    φ.swapHorizontal a b = φ := by
  rw [swapHorizontal, dite_eq_right h, dite_eq_right h']

/-- Moving a horizontal strand between `a` and `b` changes no strand starting elsewhere. -/
theorem swapHorizontal_apply_of_ne (hxa : x ≠ a) (hxb : x ≠ b) :
    φ.swapHorizontal a b x = φ x := by
  by_cases h : φ.CanMoveHorizontal a b
  · refine Option.ext fun y ↦ ?_
    rw [← Option.mem_def, ← Option.mem_def, mem_swapHorizontal h]
    simp [hxa, hxb]
  by_cases h' : φ.CanMoveHorizontal b a
  · refine Option.ext fun y ↦ ?_
    rw [swapHorizontal_comm, ← Option.mem_def, ← Option.mem_def, mem_swapHorizontal h']
    simp [hxa, hxb]
  · rw [swapHorizontal_of_not h h']

theorem CanMoveHorizontal.swapHorizontal (h : φ.CanMoveHorizontal a b) :
    (φ.swapHorizontal a b).CanMoveHorizontal b a := by
  have hab := h.ne
  refine ⟨?_, fun ha ↦ ?_, fun ha ↦ ?_⟩
  · rw [← Option.mem_def, mem_swapHorizontal h]
    simp
  · obtain ⟨y, hy⟩ := mem_source.1 ha
    rw [mem_swapHorizontal h] at hy
    rcases hy with ⟨rfl, -⟩ | ⟨hne, -⟩
    exacts [hab rfl, hne rfl]
  · obtain ⟨x, hx⟩ := mem_target.1 ha
    rw [mem_swapHorizontal h] at hx
    rcases hx with ⟨-, rfl⟩ | ⟨hne, -, hx⟩
    exacts [hab rfl, hne (φ.eq_of_mem_of_mem hx h.mem)]

@[simp]
theorem swapHorizontal_swapHorizontal (φ : StrandDiagram α) (a b : α) :
    (φ.swapHorizontal a b).swapHorizontal a b = φ := by
  -- It suffices to treat a diagram with a horizontal strand at `a` that can move to `b`.
  have key {φ : StrandDiagram α} {a b : α} (h : φ.CanMoveHorizontal a b) :
      (φ.swapHorizontal a b).swapHorizontal a b = φ := by
    have h' := h.swapHorizontal
    ext x y
    rw [← Option.mem_def, ← Option.mem_def, swapHorizontal_comm (φ.swapHorizontal a b),
      mem_swapHorizontal h', mem_swapHorizontal h]
    rcases eq_or_ne x a with rfl | hxa
    · have ha : φ x = some x := h.mem
      simp [h.ne, ha, eq_comm]
    rcases eq_or_ne x b with rfl | hxb
    · simp [apply_eq_none_of_notMem_source h.notMem_source, hxa]
    simp [hxa, hxb]
  by_cases h : φ.CanMoveHorizontal a b
  · exact key h
  by_cases h' : φ.CanMoveHorizontal b a
  · rw [swapHorizontal_comm φ, swapHorizontal_comm _ a b]
    exact key h'
  · rw [swapHorizontal_of_not h h', swapHorizontal_of_not h h']

theorem swapHorizontal_involutive (a b : α) :
    Function.Involutive fun φ : StrandDiagram α ↦ φ.swapHorizontal a b :=
  fun φ ↦ swapHorizontal_swapHorizontal φ a b

theorem source_swapHorizontal (h : φ.CanMoveHorizontal a b) :
    (φ.swapHorizontal a b).source = insert b (φ.source.erase a) := by
  ext x
  simp only [mem_source, mem_swapHorizontal h, mem_insert, mem_erase]
  rcases eq_or_ne x b with rfl | hxb
  · simp
  simp [hxb]

theorem target_swapHorizontal (h : φ.CanMoveHorizontal a b) :
    (φ.swapHorizontal a b).target = insert b (φ.target.erase a) := by
  ext y
  simp only [mem_target, mem_swapHorizontal h, mem_insert, mem_erase]
  rcases eq_or_ne y b with rfl | hyb
  · simp
  simp only [hyb, false_or, and_false]
  constructor
  · rintro ⟨x, hxa, -, hy⟩
    exact ⟨fun hya ↦ hxa (φ.eq_of_mem_of_mem hy (hya ▸ h.mem)), x, hy⟩
  · rintro ⟨hya, x, hy⟩
    refine ⟨x, fun hxa ↦ hya ?_, fun hxb ↦ h.notMem_source (mem_source.2 ⟨y, hxb ▸ hy⟩), hy⟩
    exact Option.mem_unique hy (hxa ▸ h.mem)

/-- Moving a horizontal strand of an identity diagram gives an identity diagram. -/
theorem swapHorizontal_idOn {s : Finset α} (ha : a ∈ s) (hb : b ∉ s) :
    (idOn s).swapHorizontal a b = idOn (insert b (s.erase a)) := by
  have h : (idOn s).CanMoveHorizontal a b := by
    refine ⟨?_, by simpa using hb, by simpa using hb⟩
    simp [ha]
  ext x y
  rw [← Option.mem_def, ← Option.mem_def, mem_swapHorizontal h, mem_idOn, mem_idOn, mem_insert,
    mem_erase]
  rcases eq_or_ne x b with rfl | hxb
  · simp [eq_comm]
  simp only [hxb, false_and, ne_eq, not_false_eq_true, true_and, false_or]
  tauto

/-! ### Strands crossing a horizontal strand -/

/-- The number of strands of `φ` that cross a horizontal strand at `c`: the strands starting below
`c` and ending above it. -/
def crossingCount (φ : StrandDiagram α) (c : α) : ℕ :=
  #{x ∈ φ.source | x < c ∧ c < φ.endpoint x}

theorem crossingCount_def (φ : StrandDiagram α) (c : α) :
    φ.crossingCount c = #{x ∈ φ.source | x < c ∧ c < φ.endpoint x} :=
  (rfl)

/-- Moving the horizontal strand at `a` to `b` trades the crossings with the horizontal strand at
`a` for crossings with one at `b`. -/
theorem inversionCount_swapHorizontal_add (h : φ.CanMoveHorizontal a b) :
    (φ.swapHorizontal a b).inversionCount + φ.crossingCount a =
      φ.inversionCount + φ.crossingCount b := by
  set φ' := φ.swapHorizontal a b
  set S₀ := φ.source.erase a
  have haS₀ : a ∉ S₀ := notMem_erase a _
  have hbS₀ : b ∉ S₀ := fun hb ↦ h.notMem_source (mem_of_mem_erase hb)
  have hS : φ.source = insert a S₀ := (insert_erase (mem_source.2 ⟨a, h.mem⟩)).symm
  have hS' : φ'.source = insert b S₀ := source_swapHorizontal h
  have hfa : φ.endpoint a = a := endpoint_eq_of_mem h.mem
  have hfb : φ'.endpoint b = b := endpoint_eq_of_mem ((mem_swapHorizontal h).2 (Or.inl ⟨rfl, rfl⟩))
  have hf (x : α) (hx : x ∈ S₀) : φ'.endpoint x = φ.endpoint x := by
    rw [endpoint_def, endpoint_def,
      swapHorizontal_apply_of_ne (ne_of_mem_erase hx) fun hxb : x = b ↦ hbS₀ (hxb ▸ hx)]
  have hle (x : α) (hx : x ∈ S₀) : x ≤ φ.endpoint x :=
    φ.le_of_mem (endpoint_mem (mem_of_mem_erase hx))
  -- No strand starting above a horizontal strand ends below it.
  have h₁ : #{x ∈ S₀ | a < x ∧ φ.endpoint x < φ.endpoint a} = 0 := by
    refine card_eq_zero.2 (filter_eq_empty_iff.2 fun x hx ⟨hax, hxa⟩ ↦ ?_)
    rw [hfa] at hxa
    exact (hax.trans_le (hle x hx)).not_gt hxa
  have h₂ : #{x ∈ S₀ | b < x ∧ φ'.endpoint x < φ'.endpoint b} = 0 := by
    refine card_eq_zero.2 (filter_eq_empty_iff.2 fun x hx ⟨hbx, hxb⟩ ↦ ?_)
    rw [hfb, hf x hx] at hxb
    exact (hbx.trans_le (hle x hx)).not_gt hxb
  have h₃ : #{x ∈ S₀ | x < b ∧ φ'.endpoint b < φ'.endpoint x} = φ.crossingCount b := by
    rw [crossingCount_def, hS, filter_insert,
      ite_eq_right fun h ↦ h.1.not_gt (by simpa [hfa] using h.2), hfb]
    exact congrArg card (filter_congr fun x hx ↦ by rw [hf x hx])
  have h₄ : #{x ∈ S₀ | x < a ∧ φ.endpoint a < φ.endpoint x} = φ.crossingCount a := by
    rw [crossingCount_def, hS, filter_insert, ite_eq_right fun h ↦ h.1.false, hfa]
  rw [inversionCount_def, inversionCount_def, inversions_def, inversions_def, hS', hS,
    card_inversions_insert _ hbS₀, card_inversions_insert _ haS₀, inversions_congr hf, h₁, h₂,
    ← h₃, ← h₄]
  omega

/-- The strands of a concatenation crossing a horizontal strand at `c` are those crossing it in
the first piece and those crossing it in the second, provided no strand of the first piece other
than a horizontal one ends at `c`. -/
theorem crossingCount_trans (hT : φ.target = ψ.source) (hc : ∀ x, c ∈ φ x → x = c) :
    (φ.trans ψ).crossingCount c = φ.crossingCount c + ψ.crossingCount c := by
  have hfS {x : α} (hx : x ∈ φ.source) : φ.endpoint x ∈ ψ.source := hT ▸ endpoint_mem_target hx
  have hfg {x : α} (hx : x ∈ φ.source) :
      (φ.trans ψ).endpoint x = ψ.endpoint (φ.endpoint x) :=
    endpoint_eq_of_mem (mem_trans.2 ⟨_, endpoint_mem hx, endpoint_mem (hfS hx)⟩)
  -- Transport the crossings of `ψ` to the starting points of `φ`.
  have hψ : ψ.crossingCount c =
      #{x ∈ φ.source | φ.endpoint x < c ∧ c < ψ.endpoint (φ.endpoint x)} := by
    rw [crossingCount_def]
    refine card_nbij' φ.startpoint φ.endpoint (fun y hy ↦ ?_) (fun x hx ↦ ?_) (fun y hy ↦ ?_)
      (fun x hx ↦ ?_)
    · simp only [mem_coe, mem_filter] at hy ⊢
      have hy' : y ∈ φ.target := hT ▸ hy.1
      rw [endpoint_startpoint hy']
      exact ⟨startpoint_mem_source hy', hy.2⟩
    · simp only [mem_coe, mem_filter] at hx ⊢
      exact ⟨hfS hx.1, hx.2⟩
    · simp only [mem_coe, mem_filter] at hy
      exact endpoint_startpoint (hT ▸ hy.1)
    · simp only [mem_coe, mem_filter] at hx
      exact startpoint_endpoint hx.1
  rw [crossingCount_def, crossingCount_def, hψ, source_trans_of_target_eq hT,
    ← card_union_of_disjoint (disjoint_filter.2 fun x _ h₁ h₂ ↦ h₁.2.asymm h₂.1), ← filter_or]
  refine congrArg card (filter_congr fun x hx ↦ ?_)
  have h₁ : x ≤ φ.endpoint x := φ.le_of_mem (endpoint_mem hx)
  have h₂ : φ.endpoint x ≤ ψ.endpoint (φ.endpoint x) := ψ.le_of_mem (endpoint_mem (hfS hx))
  have h₃ : φ.endpoint x = c → x = c := fun h ↦ hc x (h ▸ endpoint_mem hx)
  rw [hfg hx]
  constructor
  · rintro ⟨hxc, hcg⟩
    rcases lt_trichotomy c (φ.endpoint x) with hcf | hcf | hcf
    · exact Or.inl ⟨hxc, hcf⟩
    · exact absurd (h₃ hcf.symm) hxc.ne
    · exact Or.inr ⟨hcf, hcg⟩
  · rintro (⟨hxc, hcf⟩ | ⟨hfc, hcg⟩)
    exacts [⟨hxc, hcf.trans_le h₂⟩, ⟨h₁.trans_lt hfc, hcg⟩]

/-- Resolving a crossing `q` does not change the number of strands crossing a horizontal strand at
`c`, provided `c` is not `q.2`, the larger of the two starting points of the crossing. -/
theorem crossingCount_resolve (hq : q ∈ φ.inversions) (hc : c ≠ q.2) :
    (φ.resolve q).crossingCount c = φ.crossingCount c := by
  obtain ⟨i, j⟩ := q
  obtain ⟨hij, A, hA, B, hB, hBA⟩ := mem_inversions.1 hq
  dsimp only at hij hA hB hc
  have hfi : φ.endpoint i = A := endpoint_eq_of_mem hA
  have hfj : φ.endpoint j = B := endpoint_eq_of_mem hB
  have hjB : j ≤ B := φ.le_of_mem hB
  have he {x : α} (hx : x ∈ φ.source) :
      (φ.resolve (i, j)).endpoint x = φ.endpoint (Equiv.swap i j x) := by
    obtain ⟨z, hz⟩ := mem_source.1 ((swap_mem_source_iff hq).2 hx)
    refine (endpoint_eq_of_mem ?_).trans (endpoint_eq_of_mem hz).symm
    rwa [resolve_apply hq]
  rw [crossingCount_def, crossingCount_def, source_resolve,
    filter_congr fun x hx ↦ by rw [he hx]]
  rcases lt_or_gt_of_ne hc with hcj | hjc
  · -- Below `j` the two counts agree strand by strand.
    refine congrArg card (filter_congr fun x hx ↦ ?_)
    rcases eq_or_ne x i with rfl | hxi
    · rw [Equiv.swap_apply_left, hfi, hfj]
      exact and_congr_right fun _ ↦ iff_of_true (hcj.trans_le hjB) (hcj.trans (hjB.trans_lt hBA))
    rcases eq_or_ne x j with rfl | hxj
    · exact iff_of_false (fun h ↦ hcj.not_gt h.1) fun h ↦ hcj.not_gt h.1
    rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]
  · -- Above `j` the transposition of `i` and `j` matches the crossing strands.
    have hlt {x : α} (hx : x < c) : Equiv.swap i j x < c := by
      rcases eq_or_ne x i with rfl | hxi
      · rwa [Equiv.swap_apply_left]
      rcases eq_or_ne x j with rfl | hxj
      · rw [Equiv.swap_apply_right]
        exact hij.trans hx
      rwa [Equiv.swap_apply_of_ne_of_ne hxi hxj]
    refine card_nbij' (Equiv.swap i j) (Equiv.swap i j) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
      (fun x _ ↦ Equiv.swap_apply_self i j x) (fun x _ ↦ Equiv.swap_apply_self i j x)
    · simp only [mem_coe, mem_filter] at hx ⊢
      exact ⟨(swap_mem_source_iff hq).2 hx.1, hlt hx.2.1, hx.2.2⟩
    · simp only [mem_coe, mem_filter] at hx ⊢
      rw [Equiv.swap_apply_self]
      exact ⟨(swap_mem_source_iff hq).2 hx.1, hlt hx.2.1, hx.2.2⟩

/-! ### Moving horizontal strands through products and resolutions -/

/-- A horizontal strand at `a` that can move to `b` in both pieces of a concatenation can move to
`b` in the concatenation. -/
theorem CanMoveHorizontal.trans (hφ : φ.CanMoveHorizontal a b) (hψ : ψ.CanMoveHorizontal a b) :
    (φ.trans ψ).CanMoveHorizontal a b := by
  refine ⟨mem_trans.2 ⟨a, hφ.mem, hψ.mem⟩, fun hb ↦ ?_, fun hb ↦ ?_⟩
  · obtain ⟨y, hy⟩ := mem_source.1 hb
    obtain ⟨z, hz, -⟩ := mem_trans.1 hy
    exact hφ.notMem_source (mem_source.2 ⟨z, hz⟩)
  · obtain ⟨x, hx⟩ := mem_target.1 hb
    obtain ⟨z, -, hz⟩ := mem_trans.1 hx
    exact hψ.notMem_target (mem_target.2 ⟨z, hz⟩)

/-- A horizontal strand of a concatenation is horizontal in its first piece. -/
theorem CanMoveHorizontal.mem_left_of_trans (h : (φ.trans ψ).CanMoveHorizontal a b) : a ∈ φ a := by
  obtain ⟨d, hd, had⟩ := mem_trans.1 h.mem
  obtain rfl : d = a := le_antisymm (ψ.le_of_mem had) (φ.le_of_mem hd)
  exact hd

/-- If `φ` ends where `ψ` starts and their concatenation has a horizontal strand at `a` that can
move to a point `b` at which `φ` does not end, then that strand is horizontal in both pieces and
can move to `b` in each. -/
theorem CanMoveHorizontal.of_trans (hT : φ.target = ψ.source)
    (h : (φ.trans ψ).CanMoveHorizontal a b) (hb : b ∉ φ.target) :
    φ.CanMoveHorizontal a b ∧ ψ.CanMoveHorizontal a b := by
  have ha := h.mem_left_of_trans
  obtain ⟨d, hd, had⟩ := mem_trans.1 h.mem
  obtain rfl := Option.mem_unique hd ha
  refine ⟨⟨hd, ?_, hb⟩, ⟨had, hT ▸ hb, ?_⟩⟩
  · rw [← source_trans_of_target_eq hT]
    exact h.notMem_source
  · rw [← target_trans_of_target_eq hT]
    exact h.notMem_target

/-- Moving a horizontal strand commutes with concatenation. -/
theorem swapHorizontal_trans_swapHorizontal (hφ : φ.CanMoveHorizontal a b)
    (hψ : ψ.CanMoveHorizontal a b) :
    (φ.swapHorizontal a b).trans (ψ.swapHorizontal a b) = (φ.trans ψ).swapHorizontal a b := by
  ext x y
  rw [← Option.mem_def, ← Option.mem_def, mem_trans, mem_swapHorizontal (hφ.trans hψ), mem_trans]
  simp only [mem_swapHorizontal hφ, mem_swapHorizontal hψ]
  constructor
  · rintro ⟨z, hxz | ⟨hxa, hxb, hz⟩, hzy | ⟨-, hzb, hy⟩⟩
    · exact Or.inl ⟨hxz.1, hzy.2⟩
    · exact absurd hxz.2 hzb
    · exact absurd (mem_target.2 ⟨x, hzy.1 ▸ hz⟩) hφ.notMem_target
    · exact Or.inr ⟨hxa, hxb, z, hz, hy⟩
  · rintro (⟨rfl, rfl⟩ | ⟨hxa, hxb, z, hz, hy⟩)
    · exact ⟨_, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
    refine ⟨z, Or.inr ⟨hxa, hxb, hz⟩, Or.inr ⟨fun hza ↦ ?_, fun hzb ↦ ?_, hy⟩⟩
    · exact hxa (φ.eq_of_mem_of_mem hz (hza ▸ hφ.mem))
    · exact hφ.notMem_target (mem_target.2 ⟨x, hzb ▸ hz⟩)

/-- Moving a horizontal strand in both pieces of a nonzero product of strand diagrams gives a
nonzero product. -/
theorem Composable.swapHorizontal (h : φ.Composable ψ) (hφ : φ.CanMoveHorizontal a b)
    (hψ : ψ.CanMoveHorizontal a b) :
    (φ.swapHorizontal a b).Composable (ψ.swapHorizontal a b) := by
  refine composable_iff.2
    ⟨by rw [target_swapHorizontal hφ, source_swapHorizontal hψ, h.target_eq], ?_⟩
  rw [swapHorizontal_trans_swapHorizontal hφ hψ]
  have h₁ := inversionCount_swapHorizontal_add (hφ.trans hψ)
  have h₂ := inversionCount_swapHorizontal_add hφ
  have h₃ := inversionCount_swapHorizontal_add hψ
  have h₄ := crossingCount_trans (c := a) h.target_eq fun x hx ↦ φ.eq_of_mem_of_mem hx hφ.mem
  have h₅ := crossingCount_trans (c := b) h.target_eq fun x hx ↦
    absurd (mem_target.2 ⟨x, hx⟩) hφ.notMem_target
  have h₆ := h.inversionCount_trans
  omega

/-- If resolving a crossing `q` of `φ` gives a diagram with a horizontal strand at `a` that can
move to `b`, then that horizontal strand is already one of `φ`, and the two strands of `q` start
neither at `a` nor at `b`. -/
theorem CanMoveHorizontal.of_resolve (hq : q ∈ φ.inversions)
    (h : (φ.resolve q).CanMoveHorizontal a b) :
    φ.CanMoveHorizontal a b ∧ q.1 ≠ a ∧ q.2 ≠ a ∧ q.1 ≠ b ∧ q.2 ≠ b := by
  obtain ⟨hlt, A, hA, B, hB, hBA⟩ := mem_inversions.1 hq
  have hm : a ∈ φ (Equiv.swap q.1 q.2 a) := by
    rw [← resolve_apply hq]
    exact h.mem
  have h₁ : q.1 ≠ a := by
    rintro rfl
    rw [Equiv.swap_apply_left] at hm
    exact hlt.not_ge (φ.le_of_mem hm)
  have h₂ : q.2 ≠ a := by
    intro h₂
    rw [← h₂, Equiv.swap_apply_right] at hm
    have hA' := Option.mem_unique hm hA
    exact hBA.not_ge (by rw [← hA']; exact φ.le_of_mem hB)
  rw [Equiv.swap_apply_of_ne_of_ne h₁.symm h₂.symm] at hm
  have hb := h.notMem_source
  rw [source_resolve] at hb
  refine ⟨⟨hm, hb, by simpa using h.notMem_target⟩, h₁, h₂, ?_, ?_⟩
  · exact fun h ↦ hb (h ▸ fst_mem_source_of_mem_inversions hq)
  · exact fun h ↦ hb (h ▸ snd_mem_source_of_mem_inversions hq)

/-- If resolving a crossing `q` of `φ` gives a diagram with a horizontal strand at `a` that can
move to `b`, then `q` is still a crossing of `φ` with that strand moved. -/
theorem mem_inversions_swapHorizontal (hq : q ∈ φ.inversions)
    (h : (φ.resolve q).CanMoveHorizontal a b) : q ∈ (φ.swapHorizontal a b).inversions := by
  obtain ⟨-, h₁a, h₂a, h₁b, h₂b⟩ := h.of_resolve hq
  rw [mem_inversions, swapHorizontal_apply_of_ne h₁a h₁b, swapHorizontal_apply_of_ne h₂a h₂b]
  exact mem_inversions.1 hq

/-- If resolving a crossing `q` of `φ` gives a diagram with a horizontal strand at `a` that can
move to `b`, then resolving `q` after moving the strand is resolving `q` and then moving the
strand. -/
theorem resolve_swapHorizontal (hq : q ∈ φ.inversions) (h : (φ.resolve q).CanMoveHorizontal a b) :
    (φ.swapHorizontal a b).resolve q = (φ.resolve q).swapHorizontal a b := by
  obtain ⟨hφ, h₁a, h₂a, h₁b, h₂b⟩ := h.of_resolve hq
  have hq' := mem_inversions_swapHorizontal hq h
  set e := Equiv.swap q.1 q.2
  have hea : e a = a := Equiv.swap_apply_of_ne_of_ne h₁a.symm h₂a.symm
  have heb : e b = b := Equiv.swap_apply_of_ne_of_ne h₁b.symm h₂b.symm
  ext x y
  rw [← Option.mem_def, ← Option.mem_def, resolve_apply hq', mem_swapHorizontal h, resolve_apply hq]
  rcases eq_or_ne x a with rfl | hxa
  · rw [hea, mem_swapHorizontal hφ]
  rcases eq_or_ne x b with rfl | hxb
  · rw [heb, mem_swapHorizontal hφ]
  rw [swapHorizontal_apply_of_ne (fun h ↦ hxa (e.injective (h.trans hea.symm)))
    (fun h ↦ hxb (e.injective (h.trans heb.symm)))]
  simp only [hxa, hxb, false_and, ne_eq, not_false_eq_true, true_and, false_or]
  exact Iff.rfl

/-- If resolving a crossing `q` of `φ` gives a diagram with a horizontal strand at `a` that can
move to `b`, then `q` is a resolvable crossing of `φ` with that strand moved exactly when it is a
resolvable crossing of `φ`. -/
theorem mem_resolvableInversions_swapHorizontal_iff (hq : q ∈ φ.inversions)
    (h : (φ.resolve q).CanMoveHorizontal a b) :
    q ∈ (φ.swapHorizontal a b).resolvableInversions ↔ q ∈ φ.resolvableInversions := by
  obtain ⟨hφ, -, h₂a, -, h₂b⟩ := h.of_resolve hq
  have hq' := mem_inversions_swapHorizontal hq h
  have he := resolve_swapHorizontal hq h
  have h₁ := inversionCount_swapHorizontal_add hφ
  have h₂ := inversionCount_swapHorizontal_add h
  have h₃ := crossingCount_resolve (c := a) hq h₂a.symm
  have h₄ := crossingCount_resolve (c := b) hq h₂b.symm
  simp only [mem_resolvableInversions, hq, hq', true_and, he]
  omega

end StrandDiagram

end TauCeti
