/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Resolution

/-!
# Moving a horizontal strand

The algebra `A(Z)` of a pointed matched circle `Z` (Lipshitz, Ozsváth and Thurston) is spanned by
sums of strand diagrams which differ only in the position of their horizontal strands: each
horizontal strand may sit at either of two matched points. This file studies the elementary step
relating such diagrams. For a strand diagram `φ` with a horizontal strand at `p` and a point `q`
at which no strand of `φ` starts or ends, `TauCeti.StrandDiagram.moveHorizontal φ p q` is the
diagram with that strand moved to `q`. Moving it back recovers `φ`, and moving commutes with
concatenation and with resolving a crossing of two other strands.

The number of crossings changes in a controlled way: the moved strand crosses the strands passing
over `q` instead of those passing over `p`, and the number of strands passing over a point is the
number of starting points below it minus the number of ending points below it
(`TauCeti.StrandDiagram.inversionCount_moveHorizontal_add`). Since concatenation and resolution
preserve the relevant starting and ending points, moving a horizontal strand in both pieces of a
nonzero product of strand diagrams gives a nonzero product
(`TauCeti.StrandDiagram.Composable.moveHorizontal`), and keeps a crossing whose resolution enters
the differential resolvable (`TauCeti.StrandDiagram.mem_resolvableInversions_moveHorizontal`).
These are the facts behind the closure of `A(Z)` under products and the differential, in
`TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Matched`.

## Main definitions

* `TauCeti.StrandDiagram.moveHorizontal φ p q`: `φ` with its horizontal strand at `p` moved to
  `q`.

## Main results

* `TauCeti.StrandDiagram.moveHorizontal_moveHorizontal`: moving the strand back recovers `φ`.
* `TauCeti.StrandDiagram.moveHorizontal_trans`, `TauCeti.StrandDiagram.moveHorizontal_resolve`:
  moving commutes with concatenation and with resolutions.
* `TauCeti.StrandDiagram.inversionCount_moveHorizontal_add`: the change in the number of crossings.
* `TauCeti.StrandDiagram.Composable.moveHorizontal`,
  `TauCeti.StrandDiagram.mem_resolvableInversions_moveHorizontal`: moving preserves nonzero
  products and the terms of the differential.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.2
  (the algebra of a pointed matched circle, spanned by sums over horizontal strands at matched
  points).
-/

public section

open Finset

namespace TauCeti

namespace StrandDiagram

variable {α : Type*} [LinearOrder α] [Fintype α]

/-- Moving the horizontal strand of `φ` at `p` to a point `q` at which no strand of `φ` starts or
ends: the diagram with a horizontal strand at `q` in place of the one at `p`, and otherwise the
strands of `φ`. It is `φ` itself when `φ` has no horizontal strand at `p` or a strand starts or
ends at `q`. It conjugates the partial bijection `φ` by the transposition of `p` and `q`. -/
def moveHorizontal (φ : StrandDiagram α) (p q : α) : StrandDiagram α :=
  if h : p ∈ φ p ∧ q ∉ φ.source ∧ q ∉ φ.target then
    { toPEquiv := (Equiv.swap p q).toPEquiv.trans (φ.toPEquiv.trans (Equiv.swap p q).toPEquiv)
      le_of_mem' := by
        obtain ⟨hp, hs, ht⟩ := h
        intro i j hj
        obtain ⟨i', hi', hj'⟩ := (PEquiv.mem_trans _ _ _ _).1 hj
        obtain ⟨k, hk, hkj⟩ := (PEquiv.mem_trans _ _ _ _).1 hj'
        rw [Equiv.toPEquiv_apply, Option.mem_def, Option.some_inj] at hi' hkj
        subst hi' hkj
        rw [coe_toPEquiv] at hk
        by_cases hiq : i = q
        · rw [hiq, Equiv.swap_apply_right] at hk
          rw [hiq, Option.mem_unique hk hp, Equiv.swap_apply_left]
        by_cases hip : i = p
        · rw [hip, Equiv.swap_apply_left, apply_eq_none_of_notMem_source hs] at hk
          cases hk
        rw [Equiv.swap_apply_of_ne_of_ne hip hiq] at hk
        have hkp : k ≠ p := φ.ne_of_mem_of_mem_of_ne hk hp hip
        have hkq : k ≠ q := fun h ↦ ht (mem_target.2 ⟨i, h ▸ hk⟩)
        rw [Equiv.swap_apply_of_ne_of_ne hkp hkq]
        exact φ.le_of_mem hk }
  else φ

variable {φ ψ : StrandDiagram α} {p q : α}

theorem toPEquiv_moveHorizontal (hp : p ∈ φ p) (hs : q ∉ φ.source) (ht : q ∉ φ.target) :
    (φ.moveHorizontal p q).toPEquiv =
      (Equiv.swap p q).toPEquiv.trans (φ.toPEquiv.trans (Equiv.swap p q).toPEquiv) := by
  simp [moveHorizontal, hp, hs, ht]

/-- Without a horizontal strand at `p` to move to a free point `q`, nothing moves. -/
theorem moveHorizontal_of_not (h : ¬(p ∈ φ p ∧ q ∉ φ.source ∧ q ∉ φ.target)) :
    φ.moveHorizontal p q = φ := by
  rw [moveHorizontal, dite_eq_right_iff.2 fun h' ↦ absurd h' h]

/-- The strands of the moved diagram: a horizontal strand at `q`, none at `p`, and the strands of
`φ` elsewhere. -/
theorem moveHorizontal_apply (hp : p ∈ φ p) (hs : q ∉ φ.source) (ht : q ∉ φ.target) (i : α) :
    φ.moveHorizontal p q i = if i = q then some q else if i = p then none else φ i := by
  have hconj : φ.moveHorizontal p q i = (φ (Equiv.swap p q i)).map (Equiv.swap p q) := by
    refine Option.ext fun y ↦ ?_
    rw [← coe_toPEquiv, toPEquiv_moveHorizontal hp hs ht]
    simp [PEquiv.trans_eq_some]
  rw [hconj]
  rw [Option.mem_def] at hp
  split_ifs with hiq hip
  · simp [hiq, hp]
  · simp [hip, apply_eq_none_of_notMem_source hs]
  · obtain hi | ⟨k, hk⟩ := Option.eq_none_or_eq_some (φ i)
    · simp [Equiv.swap_apply_of_ne_of_ne hip hiq, hi]
    · have hkp : k ≠ p := φ.ne_of_mem_of_mem_of_ne hk hp hip
      have hkq : k ≠ q := fun h ↦ ht (mem_target.2 ⟨i, h ▸ hk⟩)
      simp [Equiv.swap_apply_of_ne_of_ne hip hiq, hk, Equiv.swap_apply_of_ne_of_ne hkp hkq]

/-- A free point differs from the starting point of a horizontal strand. -/
private theorem ne_of_mem_of_notMem_source (hp : p ∈ φ p) (hs : q ∉ φ.source) : p ≠ q := by
  rintro rfl
  exact hs (mem_source.2 ⟨_, hp⟩)

/-- Moving a horizontal strand from `p` to `q` replaces `p` by `q` among the starting points. -/
theorem source_moveHorizontal (hp : p ∈ φ p) (hs : q ∉ φ.source) (ht : q ∉ φ.target) :
    (φ.moveHorizontal p q).source = insert q (φ.source.erase p) := by
  ext i
  simp only [mem_source, moveHorizontal_apply hp hs ht, mem_insert, mem_erase]
  split_ifs with hiq hip <;> simp_all

/-- Moving a horizontal strand from `p` to `q` replaces `p` by `q` among the ending points. -/
theorem target_moveHorizontal (hp : p ∈ φ p) (hs : q ∉ φ.source) (ht : q ∉ φ.target) :
    (φ.moveHorizontal p q).target = insert q (φ.target.erase p) := by
  have hpq := ne_of_mem_of_notMem_source hp hs
  ext j
  simp only [mem_target, moveHorizontal_apply hp hs ht, mem_insert, mem_erase]
  constructor
  · rintro ⟨i, hi⟩
    split_ifs at hi with hiq hip
    · exact Or.inl (Option.mem_unique hi rfl)
    · cases hi
    · refine Or.inr ⟨?_, i, hi⟩
      rintro rfl
      exact hip (φ.eq_of_mem_of_mem hi hp)
  · rintro (rfl | ⟨hjp, i, hi⟩)
    · exact ⟨j, by simp⟩
    · refine ⟨i, ?_⟩
      have hiq : i ≠ q := fun h ↦ hs (mem_source.2 ⟨j, h ▸ hi⟩)
      have hip : i ≠ p := by
        rintro rfl
        exact hjp (Option.mem_unique hi hp)
      simpa [hiq, hip] using hi

/-- The moved strand is horizontal at `q`. -/
theorem mem_moveHorizontal_self (hp : p ∈ φ p) (hs : q ∉ φ.source) (ht : q ∉ φ.target) :
    q ∈ φ.moveHorizontal p q q := by
  simp [moveHorizontal_apply hp hs ht]

/-- Moving the horizontal strand back from `q` to `p` recovers `φ`. -/
theorem moveHorizontal_moveHorizontal (hp : p ∈ φ p) (hs : q ∉ φ.source) (ht : q ∉ φ.target) :
    (φ.moveHorizontal p q).moveHorizontal q p = φ := by
  have hpq := ne_of_mem_of_notMem_source hp hs
  have hs' : p ∉ (φ.moveHorizontal p q).source := by
    simp [source_moveHorizontal hp hs ht, hpq]
  have ht' : p ∉ (φ.moveHorizontal p q).target := by
    simp [target_moveHorizontal hp hs ht, hpq]
  ext i : 1
  rw [moveHorizontal_apply (mem_moveHorizontal_self hp hs ht) hs' ht',
    moveHorizontal_apply hp hs ht]
  rw [Option.mem_def] at hp
  split_ifs with h₁ h₂ <;> subst_vars <;> simp_all [apply_eq_none_of_notMem_source hs]

/-- Moving a horizontal strand of both pieces of a concatenation moves it in the concatenation. -/
theorem moveHorizontal_trans (hpφ : p ∈ φ p) (hsφ : q ∉ φ.source) (htφ : q ∉ φ.target)
    (hpψ : p ∈ ψ p) (hsψ : q ∉ ψ.source) (htψ : q ∉ ψ.target) :
    (φ.moveHorizontal p q).trans (ψ.moveHorizontal p q) = (φ.trans ψ).moveHorizontal p q := by
  have hp : p ∈ φ.trans ψ p := mem_trans.2 ⟨p, hpφ, hpψ⟩
  have hs : q ∉ (φ.trans ψ).source := by
    simp only [mem_source, mem_trans, not_exists, not_and]
    exact fun j k hk _ ↦ hsφ (mem_source.2 ⟨k, hk⟩)
  have ht : q ∉ (φ.trans ψ).target := by
    simp only [mem_target, mem_trans, not_exists, not_and]
    exact fun i k _ hk ↦ htψ (mem_target.2 ⟨k, hk⟩)
  ext i : 1
  rw [trans_apply, moveHorizontal_apply hpφ hsφ htφ, moveHorizontal_apply hp hs ht, trans_apply]
  split_ifs with hiq hip
  · simp [moveHorizontal_apply hpψ hsψ htψ]
  · rfl
  · obtain hi | ⟨k, hk⟩ := Option.eq_none_or_eq_some (φ i)
    · simp [hi]
    · have hkp : k ≠ p := φ.ne_of_mem_of_mem_of_ne hk hpφ hip
      have hkq : k ≠ q := fun h ↦ htφ (mem_target.2 ⟨i, h ▸ hk⟩)
      simp [hk, moveHorizontal_apply hpψ hsψ htψ, hkp, hkq]

/-- Moving a horizontal strand does not change whether two other strands cross. -/
theorem mem_inversions_moveHorizontal_iff (hp : p ∈ φ p) (hs : q ∉ φ.source)
    (ht : q ∉ φ.target) {r : α × α} (h₁ : r.1 ≠ p) (h₂ : r.2 ≠ p) (h₃ : r.1 ≠ q)
    (h₄ : r.2 ≠ q) : r ∈ (φ.moveHorizontal p q).inversions ↔ r ∈ φ.inversions := by
  simp [mem_inversions, moveHorizontal_apply hp hs ht, h₁, h₂, h₃, h₄]

/-- Moving a horizontal strand commutes with resolving a crossing of two other strands. -/
theorem moveHorizontal_resolve (hp : p ∈ φ p) (hs : q ∉ φ.source) (ht : q ∉ φ.target)
    {r : α × α} (hr : r ∈ φ.inversions) (h₁ : r.1 ≠ p) (h₂ : r.2 ≠ p) :
    (φ.resolve r).moveHorizontal p q = (φ.moveHorizontal p q).resolve r := by
  have h₃ : r.1 ≠ q := fun h ↦ hs (h ▸ fst_mem_source_of_mem_inversions hr)
  have h₄ : r.2 ≠ q := fun h ↦ hs (h ▸ snd_mem_source_of_mem_inversions hr)
  have hr' := (mem_inversions_moveHorizontal_iff hp hs ht h₁ h₂ h₃ h₄).2 hr
  have hp' : p ∈ φ.resolve r p := by
    rwa [resolve_apply hr, Equiv.swap_apply_of_ne_of_ne h₁.symm h₂.symm]
  have hs' : q ∉ (φ.resolve r).source := by rwa [source_resolve]
  have ht' : q ∉ (φ.resolve r).target := by rwa [target_resolve]
  ext i : 1
  rw [moveHorizontal_apply hp' hs' ht', resolve_apply hr', resolve_apply hr,
    moveHorizontal_apply hp hs ht]
  rcases eq_or_ne i q with rfl | hiq
  · simp [Equiv.swap_apply_of_ne_of_ne h₃.symm h₄.symm]
  rcases eq_or_ne i p with rfl | hip
  · simp [Equiv.swap_apply_of_ne_of_ne h₁.symm h₂.symm, hiq]
  have hsq : Equiv.swap r.1 r.2 i ≠ q := by
    intro h
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne h₃.symm h₄.symm] at h
    exact hiq h
  have hsp : Equiv.swap r.1 r.2 i ≠ p := by
    intro h
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne h₁.symm h₂.symm] at h
    exact hip h
  simp [hiq, hip, hsq, hsp]

/-- The strands of `φ` passing over a point `x` that is not the end point of a strand starting
elsewhere: the starting points of `φ` below `x` are those of these strands and of the strands
ending below `x`. -/
private theorem card_filter_lt_lt_endpoint_add_card_filter_target_lt {x : α}
    (hx : x ∈ φ x ∨ x ∉ φ.target) :
    #{i ∈ φ.source | i < x ∧ x < φ.endpoint i} + #{j ∈ φ.target | j < x} =
      #{i ∈ φ.source | i < x} := by
  have h := card_filter_add_card_filter_not (s := {i ∈ φ.source | i < x}) (x < φ.endpoint ·)
  simp only [filter_filter] at h
  rw [← h, card_nbij' (s := {i ∈ φ.source | i < x ∧ ¬x < φ.endpoint i}) φ.endpoint φ.startpoint]
  · intro i hi
    simp only [coe_filter, Set.mem_ofPred_eq, not_lt] at hi ⊢
    refine ⟨endpoint_mem_target hi.1, lt_of_le_of_ne hi.2.2 fun he ↦ ?_⟩
    have hmem : x ∈ φ i := he ▸ endpoint_mem hi.1
    rcases hx with hx | hx
    · exact hi.2.1.ne (φ.eq_of_mem_of_mem hmem hx)
    · exact hx (mem_target.2 ⟨i, hmem⟩)
  · intro j hj
    simp only [coe_filter, Set.mem_ofPred_eq, not_lt] at hj ⊢
    refine ⟨startpoint_mem_source hj.1, ?_, by rw [endpoint_startpoint hj.1]; exact hj.2.le⟩
    exact (φ.le_of_mem (mem_startpoint hj.1)).trans_lt hj.2
  · intro i hi
    simp only [coe_filter, Set.mem_ofPred_eq] at hi
    exact startpoint_endpoint hi.1
  · intro j hj
    simp only [coe_filter, Set.mem_ofPred_eq] at hj
    exact endpoint_startpoint hj.1

/-- The crossings of `φ` other than those of a horizontal strand at `p`, and those of the strands
of `φ` passing over `p`. -/
private theorem inversionCount_eq_of_mem (hp : p ∈ φ p) :
    φ.inversionCount = #((φ.source.erase p).inversions φ.endpoint) +
      #{i ∈ φ.source | i < p ∧ p < φ.endpoint i} := by
  have hpS : p ∈ φ.source := mem_source.2 ⟨p, hp⟩
  have key := card_inversions_insert φ.endpoint (notMem_erase p φ.source)
  rw [insert_erase hpS, endpoint_eq_of_mem hp] at key
  have h₂ : #{b ∈ φ.source.erase p | b < p ∧ p < φ.endpoint b} =
      #{i ∈ φ.source | i < p ∧ p < φ.endpoint i} := by
    rw [filter_erase, erase_eq_of_notMem (by simp)]
  have h₃ : #{b ∈ φ.source.erase p | p < b ∧ φ.endpoint b < p} = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro b hb ⟨hpb, hbp⟩
    exact (hpb.trans_le (φ.le_of_mem (endpoint_mem (mem_of_mem_erase hb)))).not_gt hbp
  rw [inversionCount_def, inversions_def, key]
  omega

/-- **Crossings after moving a horizontal strand.** Moving the horizontal strand of `φ` at `p` to
a point `q` where `φ` has no strand changes the crossings with that strand from the strands passing
over `p` to those passing over `q`. Counting the strands passing over a point by their starting and
ending points below it, the crossing counts satisfy
`inv φ' + #{i ∈ S | i < p} + #{j ∈ T | j < q} = inv φ + #{i ∈ S | i < q} + #{j ∈ T | j < p}`,
where `S` and `T` are the starting and ending points of `φ`. -/
theorem inversionCount_moveHorizontal_add (hp : p ∈ φ p) (hs : q ∉ φ.source)
    (ht : q ∉ φ.target) :
    (φ.moveHorizontal p q).inversionCount + #{i ∈ φ.source | i < p} + #{j ∈ φ.target | j < q} =
      φ.inversionCount + #{i ∈ φ.source | i < q} + #{j ∈ φ.target | j < p} := by
  have hpq := ne_of_mem_of_notMem_source hp hs
  set φ' := φ.moveHorizontal p q
  have hq' : q ∈ φ' q := mem_moveHorizontal_self hp hs ht
  have hS' : φ'.source.erase q = φ.source.erase p := by
    rw [source_moveHorizontal hp hs ht, erase_insert (by simp [hs])]
  -- Both diagrams share their strands away from `p` and `q`.
  have he : ∀ i ∈ φ.source.erase p, φ'.endpoint i = φ.endpoint i := by
    intro i hi
    have hiq : i ≠ q := fun h ↦ hs (h ▸ mem_of_mem_erase hi)
    simp [endpoint_def, φ', moveHorizontal_apply hp hs ht, hiq, ne_of_mem_erase hi]
  have h₁ := inversionCount_eq_of_mem hp
  have h₂ := inversionCount_eq_of_mem hq'
  rw [hS', inversions_congr he] at h₂
  -- The strands passing over `q` in `φ'` and in `φ` are the same.
  have h₃ : #{i ∈ φ'.source | i < q ∧ q < φ'.endpoint i} =
      #{i ∈ φ.source | i < q ∧ q < φ.endpoint i} := by
    rw [source_moveHorizontal hp hs ht, filter_insert, ite_eq_right (by simp),
      filter_congr fun i hi ↦ by rw [he i hi], filter_erase, erase_eq_of_notMem]
    simp only [mem_filter, endpoint_eq_of_mem hp, not_and, not_lt]
    exact fun _ h ↦ h.le
  have h₄ := card_filter_lt_lt_endpoint_add_card_filter_target_lt (Or.inl hp)
  have h₅ := card_filter_lt_lt_endpoint_add_card_filter_target_lt (φ := φ) (x := q) (Or.inr ht)
  omega

/-- Moving a horizontal strand of an identity diagram gives the identity diagram on the moved
set. -/
theorem moveHorizontal_idOn {s : Finset α} (hp : p ∈ s) (hq : q ∉ s) :
    (idOn s).moveHorizontal p q = idOn (insert q (s.erase p)) := by
  have hpq : p ≠ q := fun h ↦ hq (h ▸ hp)
  ext i : 1
  rw [moveHorizontal_apply (mem_idOn.2 ⟨rfl, hp⟩) (by rwa [source_idOn])
    (by rwa [target_idOn])]
  simp only [idOn_apply, mem_insert, mem_erase]
  split_ifs <;> simp_all

/-- Moving a horizontal strand in both pieces of a nonzero product of strand diagrams gives a
nonzero product. -/
theorem Composable.moveHorizontal (h : φ.Composable ψ) (hpφ : p ∈ φ p) (hsφ : q ∉ φ.source)
    (htφ : q ∉ φ.target) (hpψ : p ∈ ψ p) (hsψ : q ∉ ψ.source) (htψ : q ∉ ψ.target) :
    (φ.moveHorizontal p q).Composable (ψ.moveHorizontal p q) := by
  have hp : p ∈ φ.trans ψ p := mem_trans_self_iff.2 ⟨hpφ, hpψ⟩
  have hs : q ∉ (φ.trans ψ).source := by rwa [source_trans_of_target_eq h.target_eq]
  have ht : q ∉ (φ.trans ψ).target := by rwa [target_trans_of_target_eq h.target_eq]
  have h₁ := inversionCount_moveHorizontal_add hpφ hsφ htφ
  have h₂ := inversionCount_moveHorizontal_add hpψ hsψ htψ
  have h₃ := inversionCount_moveHorizontal_add hp hs ht
  rw [← moveHorizontal_trans hpφ hsφ htφ hpψ hsψ htψ, source_trans_of_target_eq h.target_eq,
    target_trans_of_target_eq h.target_eq] at h₃
  rw [← h.target_eq] at h₂
  have h₄ := h.inversionCount_trans
  refine composable_iff.2 ⟨?_, by omega⟩
  rw [target_moveHorizontal hpφ hsφ htφ, source_moveHorizontal hpψ hsψ htψ, h.target_eq]

/-- Moving a horizontal strand of the resolution of a crossing keeps the crossing resolvable. -/
theorem mem_resolvableInversions_moveHorizontal {r : α × α} (hr : r ∈ φ.resolvableInversions)
    (hp : p ∈ φ.resolve r p) (hs : q ∉ φ.source) (ht : q ∉ φ.target) :
    r ∈ (φ.moveHorizontal p q).resolvableInversions := by
  rw [mem_resolvableInversions] at hr ⊢
  obtain ⟨hpφ, h₁, h₂⟩ := mem_resolve_self hr.1 hp
  have h₃ : r.1 ≠ q := fun h ↦ hs (h ▸ fst_mem_source_of_mem_inversions hr.1)
  have h₄ : r.2 ≠ q := fun h ↦ hs (h ▸ snd_mem_source_of_mem_inversions hr.1)
  have hs' : q ∉ (φ.resolve r).source := by rwa [source_resolve]
  have ht' : q ∉ (φ.resolve r).target := by rwa [target_resolve]
  have hφ := inversionCount_moveHorizontal_add hpφ hs ht
  have hχ := inversionCount_moveHorizontal_add hp hs' ht'
  rw [moveHorizontal_resolve hpφ hs ht hr.1 h₁ h₂, source_resolve, target_resolve] at hχ
  exact ⟨(mem_inversions_moveHorizontal_iff hpφ hs ht h₁ h₂ h₃ h₄).2 hr.1, by omega⟩

end StrandDiagram

end TauCeti
