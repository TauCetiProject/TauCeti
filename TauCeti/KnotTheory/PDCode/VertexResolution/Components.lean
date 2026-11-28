/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.VertexResolution
import TauCeti.GroupTheory.Perm.SwapFactors

/-!
# Identifying the component-count alternatives at a resolved crossing

`TauCeti.PDCode.componentCount_resolveCrossing_cases` shows that resolving a crossing `c` of an
unoriented `PDCode` `D` with `n + 1` crossings either lowers the component count by one in both
smoothings or yields component counts `D.componentCount` and `D.componentCount + 1`. This file
identifies **which** alternative occurs from the directed `componentPerm` orbits at `c`, without
any orientation or planarity hypothesis:

* `D.resolvedTurn c t * D.edgePair.val` is obtained from `D.componentPerm` by multiplying on the
  left by the transposition `Equiv.swap (D.crossing c 0) (D.crossing c k)` and its `crossingTurn`
  conjugate, where `k = slotSmoothing (!(bif t then D.overPair c else !D.overPair c)) 0`.
* When slot `0` shares a directed `componentPerm` orbit with neither slot `1` nor slot `3` (the
  two strands at `c` lie on different undirected components), both transpositions merge distinct
  orbits and both smoothings have `D.componentCount - 1` components
  (`TauCeti.PDCode.componentCount_resolveCrossing_add_one_of_not_sameCycle`).
* When slot `0` shares a directed `componentPerm` orbit with slot `1`
  (`TauCeti.PDCode.componentCount_resolveCrossing_of_sameCycle_zero_one`) or with slot `3`
  (`TauCeti.PDCode.componentCount_resolveCrossing_of_sameCycle_zero_three`), one smoothing splits
  that component into two (`D.componentCount + 1` components) and the opposite smoothing leaves
  `D.componentCount` components.

## Main results

* `TauCeti.PDCode.componentCount_resolveCrossing_add_one_of_not_sameCycle`: resolving a crossing
  between two distinct undirected components merges them (`c - 1` components in both smoothings).
* `TauCeti.PDCode.componentCount_resolveCrossing_of_sameCycle_zero_one` and
  `TauCeti.PDCode.componentCount_resolveCrossing_of_sameCycle_zero_three`: identify which smoothing
  splits a self-crossing (`c + 1` components) and which leaves `c` components.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapters 1–3.
* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §3.
-/

public section

namespace TauCeti.PDCode

open Equiv Equiv.Perm

variable {n : ℕ} (D : PDCode (n + 1)) (c : Fin (n + 1))

/-- Each local smoothing on `Fin 4` is obtained from `oppositeCrossingSlot` by two disjoint
transpositions pairing `0` with `slotSmoothing (!b) 0` and `2` with its opposite slot. -/
private theorem slotSmoothing_eq_swap_mul_swap_mul_oppositeCrossingSlot (b : Bool) :
    ∀ m : Fin 4, slotSmoothing b m =
      Equiv.swap 2 (oppositeCrossingSlot (slotSmoothing (!b) 0))
        (Equiv.swap 0 (slotSmoothing (!b) 0) (oppositeCrossingSlot m)) := by
  cases b <;> simp only [Bool.not_false, Bool.not_true, slotSmoothing_true, slotSmoothing_false,
    oppositeCrossingSlot_apply] <;> decide

/-- `D.resolvedTurn c t` multiplies `D.crossingTurn` on the left by two opposite transpositions at
crossing `c`. -/
private theorem resolvedTurn_eq_swap_mul_swap_mul_crossingTurn (t : Bool) :
    D.resolvedTurn c t =
      let k := slotSmoothing (!(bif t then D.overPair c else !D.overPair c)) 0
      Equiv.swap (D.crossingTurn (D.crossing c 0)) (D.crossingTurn (D.crossing c k)) *
        Equiv.swap (D.crossing c 0) (D.crossing c k) * D.crossingTurn := by
  set b := bif t then D.overPair c else !D.overPair c
  set k := slotSmoothing (!b) 0
  have ht₀ : D.crossingTurn (D.crossing c 0) = D.crossing c 2 := D.crossingTurn_crossing_zero c
  have htk : D.crossingTurn (D.crossing c k) = D.crossing c (oppositeCrossingSlot k) := by
    rw [crossing_apply, crossingTurn_crossing]
  have hinj : Function.Injective (D.crossing c) :=
    fun _ _ h ↦ (D.crossing_eq_crossing_iff.mp h).right
  ext h : 1
  obtain ⟨x, rfl⟩ := D.halfEdge.surjective h
  obtain ⟨⟨j, l⟩, rfl⟩ := (crossingSlotEquiv (n + 1)).surjective x
  by_cases hj : j = c
  · subst hj
    rw [resolvedTurn_crossing_self, Perm.mul_apply, Perm.mul_apply,
      crossingTurn_crossing, ht₀, htk, slotSmoothing_eq_swap_mul_swap_mul_oppositeCrossingSlot,
      hinj.swap_apply, hinj.swap_apply]
  · have hne : ∀ s : Fin 4, D.crossing j (oppositeCrossingSlot l) ≠ D.crossing c s :=
      fun s hs ↦ hj (D.crossing_eq_crossing_iff.mp hs).left
    rw [D.resolvedTurn_crossing_of_ne c t hj, Perm.mul_apply, Perm.mul_apply,
      crossingTurn_crossing, ht₀, htk,
      Equiv.swap_apply_of_ne_of_ne (hne 0) (hne k),
      Equiv.swap_apply_of_ne_of_ne (hne 2) (hne (oppositeCrossingSlot k))]

/-- When `u ≠ v` share a directed `componentPerm` orbit, both `Equiv.swap u v` and its
`crossingTurn` conjugate split an orbit, increasing `orbitCount` by two. -/
private theorem orbitCount_swap_crossingTurn_mul_of_sameCycle {m : ℕ} (E : PDCode m)
    {u v : Fin (4 * m)} (huv : u ≠ v) (h : E.componentPerm.SameCycle u v) :
    orbitCount (Equiv.swap (E.crossingTurn u) (E.crossingTurn v) *
        (Equiv.swap u v * E.componentPerm)) =
      orbitCount E.componentPerm + 2 := by
  have htuv : E.crossingTurn u ≠ E.crossingTurn v := E.crossingTurn.injective.ne huv
  have htu_u : ¬ E.componentPerm.SameCycle (E.crossingTurn u) u := fun h' ↦
    E.not_sameCycle_componentPerm_crossingTurn u h'.symm
  have htu_v : ¬ E.componentPerm.SameCycle (E.crossingTurn u) v := fun h' ↦
    htu_u (h'.trans h.symm)
  have hsc₂ : (Equiv.swap u v * E.componentPerm).SameCycle
      (E.crossingTurn u) (E.crossingTurn v) := by
    have hsq : (Equiv.swap u v * (Equiv.swap u v * E.componentPerm)).SameCycle
        (E.crossingTurn u) (E.crossingTurn v) := by
      rw [Equiv.swap_mul_self_mul]
      exact (E.sameCycle_componentPerm_crossingTurn_iff).mpr h
    rcases hsq.sameCycle_or_of_swap_mul with hsc | ⟨hu | hv, -⟩
    · exact hsc
    · rcases hu.sameCycle_or_of_swap_mul with h₁ | ⟨h₁ | h₁, -⟩
      · exact absurd h₁ htu_u
      · exact absurd h₁ htu_u
      · exact absurd h₁ htu_v
    · rcases hv.sameCycle_or_of_swap_mul with h₁ | ⟨h₁ | h₁, -⟩
      · exact absurd h₁ htu_v
      · exact absurd h₁ htu_u
      · exact absurd h₁ htu_v
  rw [orbitCount_swap_mul_of_sameCycle htuv hsc₂, orbitCount_swap_mul_of_sameCycle huv h]

/-- When `u` shares a directed `componentPerm` orbit with `E.crossingTurn v` (and `u ≠ v`),
`Equiv.swap u v` merges the two opposite directed orbits into one and its `crossingTurn` conjugate
splits that merged orbit back into two, leaving `orbitCount` unchanged. -/
private theorem orbitCount_swap_crossingTurn_mul_of_sameCycle_crossingTurn {m : ℕ} (E : PDCode m)
    {u v : Fin (4 * m)} (huv : u ≠ v) (h : E.componentPerm.SameCycle u (E.crossingTurn v)) :
    orbitCount (Equiv.swap (E.crossingTurn u) (E.crossingTurn v) *
        (Equiv.swap u v * E.componentPerm)) =
      orbitCount E.componentPerm := by
  have huv_not : ¬ E.componentPerm.SameCycle u v := fun h' ↦
    E.not_sameCycle_componentPerm_crossingTurn v (h'.symm.trans h)
  have htuv : E.crossingTurn u ≠ E.crossingTurn v := E.crossingTurn.injective.ne huv
  have hab : (Equiv.swap u v * E.componentPerm).SameCycle u v :=
    sameCycle_swap_mul_of_mem_periodicPts_of_not_sameCycle
      (E.componentPerm.injective.mem_periodicPts v) huv_not
  have htu_v : E.componentPerm.SameCycle (E.crossingTurn u) v := by
    have h' := (E.sameCycle_componentPerm_crossingTurn_iff).mpr h
    rwa [E.crossingTurn_apply_apply] at h'
  have hsc₂ : (Equiv.swap u v * E.componentPerm).SameCycle (E.crossingTurn u) (E.crossingTurn v) :=
    (hab.swap_mul_of_sameCycle htu_v).trans (hab.symm.trans (hab.swap_mul_of_sameCycle h))
  have hmerge := orbitCount_swap_mul_add_one_of_not_sameCycle huv_not
  rw [orbitCount_swap_mul_of_sameCycle htuv hsc₂]
  omega

/-- When `u` and `v` lie on distinct undirected components, both `Equiv.swap u v` and its
`crossingTurn` conjugate merge distinct orbits, decreasing `orbitCount` by two. -/
private theorem orbitCount_swap_crossingTurn_mul_add_two_of_not_sameCycle {m : ℕ} (E : PDCode m)
    {u v : Fin (4 * m)} (h₁ : ¬ E.componentPerm.SameCycle u v)
    (h₂ : ¬ E.componentPerm.SameCycle u (E.crossingTurn v)) :
    orbitCount (Equiv.swap (E.crossingTurn u) (E.crossingTurn v) *
        (Equiv.swap u v * E.componentPerm)) + 2 =
      orbitCount E.componentPerm := by
  have hsc₂ : ¬ (Equiv.swap u v * E.componentPerm).SameCycle
      (E.crossingTurn u) (E.crossingTurn v) := by
    intro hcon
    rcases hcon.sameCycle_or_of_swap_mul with htu | ⟨htu | htu, -⟩
    · exact h₁ ((E.sameCycle_componentPerm_crossingTurn_iff).mp htu)
    · exact E.not_sameCycle_componentPerm_crossingTurn u htu.symm
    · have h' := (E.sameCycle_componentPerm_crossingTurn_iff).mpr htu
      rw [E.crossingTurn_apply_apply] at h'
      exact h₂ h'
  have hm₁ := orbitCount_swap_mul_add_one_of_not_sameCycle h₁
  have hm₂ := orbitCount_swap_mul_add_one_of_not_sameCycle hsc₂
  omega

/-- Twice the component count of `D.resolveCrossing c t` equals the orbit count of the
double-transposition perturbation of `D.componentPerm` at `c`, plus twice the crossing-free
circles of `D`. -/
private theorem two_mul_componentCount_resolveCrossing_eq_orbitCount (t : Bool) :
    2 * (D.resolveCrossing c t).componentCount =
      let k := slotSmoothing (!(bif t then D.overPair c else !D.overPair c)) 0
      orbitCount (Equiv.swap (D.crossingTurn (D.crossing c 0)) (D.crossingTurn (D.crossing c k)) *
        (Equiv.swap (D.crossing c 0) (D.crossing c k) * D.componentPerm)) +
        2 * D.crossinglessComponentCount := by
  rw [D.two_mul_componentCount_resolveCrossing c t,
    D.resolvedTurn_eq_swap_mul_swap_mul_crossingTurn c t]
  dsimp only
  rw [mul_assoc, mul_assoc, ← componentPerm_def]

/-- **Component count when resolving a crossing between two distinct components.** If the two
strands at crossing `c` belong to different undirected components (so slot `0` shares a directed
`componentPerm` orbit with neither slot `1` nor slot `3`), then both the `A`- and `B`-resolutions
merge those two components into one and have `D.componentCount - 1` components. -/
theorem componentCount_resolveCrossing_add_one_of_not_sameCycle (t : Bool)
    (h₁ : ¬ D.componentPerm.SameCycle (D.crossing c 0) (D.crossing c 1))
    (h₃ : ¬ D.componentPerm.SameCycle (D.crossing c 0) (D.crossing c 3)) :
    (D.resolveCrossing c t).componentCount + 1 = D.componentCount := by
  have h2 := D.two_mul_componentCount_resolveCrossing_eq_orbitCount c t
  dsimp only at h2
  set b := bif t then D.overPair c else !D.overPair c
  have horb : orbitCount (Equiv.swap (D.crossingTurn (D.crossing c 0))
        (D.crossingTurn (D.crossing c (slotSmoothing (!b) 0))) *
      (Equiv.swap (D.crossing c 0) (D.crossing c (slotSmoothing (!b) 0)) *
        D.componentPerm)) + 2 = orbitCount D.componentPerm := by
    cases hb : b
    · have hk : slotSmoothing (!false) 0 = 1 := by rw [Bool.not_false, slotSmoothing_true]; decide
      rw [hk]
      exact D.orbitCount_swap_crossingTurn_mul_add_two_of_not_sameCycle h₁
        (by rwa [D.crossingTurn_crossing_one c])
    · have hk : slotSmoothing (!true) 0 = 3 := by rw [Bool.not_true, slotSmoothing_false]; decide
      rw [hk]
      exact D.orbitCount_swap_crossingTurn_mul_add_two_of_not_sameCycle h₃
        (by rwa [D.crossingTurn_crossing_three c])
  obtain ⟨r, hr⟩ := D.even_orbitCount_componentPerm
  have hD : D.componentCount = orbitCount D.componentPerm / 2 + D.crossinglessComponentCount := by
    rw [componentCount_eq, crossingComponentCount_def]
  omega

/-- Unified self-crossing helper: when slot `0` shares a directed `componentPerm` orbit with
`slotSmoothing (!b₀) 0`, choosing `t` with local smoothing `b₀` splits the component (`c + 1`) and
choosing `!t` leaves the component count at `c`. -/
private theorem componentCount_resolveCrossing_of_sameCycle_slotSmoothing (t : Bool)
    (h : D.componentPerm.SameCycle (D.crossing c 0)
      (D.crossing c (slotSmoothing (!(bif t then D.overPair c else !D.overPair c)) 0))) :
    (D.resolveCrossing c t).componentCount = D.componentCount + 1 ∧
      (D.resolveCrossing c (!t)).componentCount = D.componentCount := by
  have hb' : (bif !t then D.overPair c else !D.overPair c) =
      !(bif t then D.overPair c else !D.overPair c) := by
    cases t <;> cases D.overPair c <;> rfl
  have hc₁ := D.two_mul_componentCount_resolveCrossing_eq_orbitCount c t
  have hc₂ := D.two_mul_componentCount_resolveCrossing_eq_orbitCount c (!t)
  dsimp only at hc₁ hc₂
  rw [hb', Bool.not_not] at hc₂
  generalize (bif t then D.overPair c else !D.overPair c) = b at h hc₁ hc₂
  have hne₁ : D.crossing c 0 ≠ D.crossing c (slotSmoothing (!b) 0) := fun hc ↦
    slotSmoothing_ne (!b) 0 (D.crossing_eq_crossing_iff.mp hc).right.symm
  have hne₂ : D.crossing c 0 ≠ D.crossing c (slotSmoothing b 0) := fun hc ↦
    slotSmoothing_ne b 0 (D.crossing_eq_crossing_iff.mp hc).right.symm
  have htk : D.crossingTurn (D.crossing c (slotSmoothing b 0)) =
      D.crossing c (slotSmoothing (!b) 0) := by
    rw [crossing_apply, crossingTurn_crossing]
    congr 1
    cases b <;> simp only [Bool.not_false, Bool.not_true, slotSmoothing_true, slotSmoothing_false,
      oppositeCrossingSlot_apply] <;> decide
  rw [D.orbitCount_swap_crossingTurn_mul_of_sameCycle hne₁ h] at hc₁
  rw [D.orbitCount_swap_crossingTurn_mul_of_sameCycle_crossingTurn hne₂ (by rwa [htk])] at hc₂
  obtain ⟨r, hr⟩ := D.even_orbitCount_componentPerm
  have hD : D.componentCount = orbitCount D.componentPerm / 2 + D.crossinglessComponentCount := by
    rw [componentCount_eq, crossingComponentCount_def]
  omega

/-- If slots `0` and `1` of crossing `c` lie in the same directed `componentPerm` orbit, resolving
`c` by `!D.overPair c` splits that component (`c + 1` components), whereas resolving `c` by
`D.overPair c` leaves the component count unchanged (`c` components). -/
theorem componentCount_resolveCrossing_of_sameCycle_zero_one
    (h : D.componentPerm.SameCycle (D.crossing c 0) (D.crossing c 1)) :
    (D.resolveCrossing c (!D.overPair c)).componentCount = D.componentCount + 1 ∧
      (D.resolveCrossing c (D.overPair c)).componentCount = D.componentCount := by
  have hb : (bif !D.overPair c then D.overPair c else !D.overPair c) = false := by
    cases D.overPair c <;> rfl
  have hk : slotSmoothing (!false) 0 = 1 := by rw [Bool.not_false, slotSmoothing_true]; decide
  simpa using D.componentCount_resolveCrossing_of_sameCycle_slotSmoothing c (!D.overPair c)
    (by rwa [hb, hk])

/-- If slots `0` and `3` of crossing `c` lie in the same directed `componentPerm` orbit, resolving
`c` by `D.overPair c` splits that component (`c + 1` components), whereas resolving `c` by
`!D.overPair c` leaves the component count unchanged (`c` components). -/
theorem componentCount_resolveCrossing_of_sameCycle_zero_three
    (h : D.componentPerm.SameCycle (D.crossing c 0) (D.crossing c 3)) :
    (D.resolveCrossing c (D.overPair c)).componentCount = D.componentCount + 1 ∧
      (D.resolveCrossing c (!D.overPair c)).componentCount = D.componentCount := by
  have hb : (bif D.overPair c then D.overPair c else !D.overPair c) = true := by
    cases D.overPair c <;> rfl
  have hk : slotSmoothing (!true) 0 = 3 := by rw [Bool.not_true, slotSmoothing_false]; decide
  exact D.componentCount_resolveCrossing_of_sameCycle_slotSmoothing c (D.overPair c)
    (by rwa [hb, hk])

end TauCeti.PDCode
