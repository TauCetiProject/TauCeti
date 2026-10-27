/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Kauffman
import Mathlib.Logic.Equiv.Fin.Basic
import TauCeti.GroupTheory.Perm.SumCongr

/-!
# Resolving a crossing of a PD-code

Smoothing one crossing `c` of a PD-code `D` with `n + 1` crossings, and leaving the others
alone, gives a PD-code with `n` crossings: `TauCeti.PDCode.resolveCrossing D c t`, with `t = true`
for the `A`-smoothing and `t = false` for the `B`-smoothing, the same convention as a state.
This is the vertex resolution behind the skein relations of the Kauffman bracket and of the
Khovanov complex: the two resolutions of `c` are the diagrams `D_A` and `D_B` of
`⟨D⟩ = A ⟨D_A⟩ + A⁻¹ ⟨D_B⟩`.

The local smoothing joins the four slots of `c` in two pairs. An arc of `D` arriving at a slot of
`c` is continued through the smoothing and, if it arrives at `c` again, through the smoothing once
more, until it reaches another crossing; the resulting arcs form the perfect matching of the
resolved code. A circle of the smoothing that never leaves `c` becomes a crossing-free circle of
the resolved code, so the degree-two vertices left by the smoothing are suppressed and every
newly detached circle is counted (`TauCeti.PDCode.detachedCircleCount`). Such circles arise when
an arc of `D` joins two slots of `c`, as at a kink.

The remaining crossings keep their order: crossing `i` of the resolved code is crossing
`c.succAbove i` of `D`, with the same over-strand. The half-edges of the resolved code are labelled
by their positions, so its `halfEdge` permutation is the identity.

The arcs are built on `Fin (4 * n) ⊕ Fin 4`, the positions of the other crossings followed by the
slots of `c`. Reconnecting the arcs of `D` so that they join the two ends of each smoothing arc
(`TauCeti.PerfectMatching.reconnect`) cuts each smoothing arc off as a two-point circle of its own,
and what remains on the other positions is the resolved matching
(`TauCeti.PerfectMatching.restrictInl`). A smoothing arc whose two ends are already joined when it
is cut off is a detached circle.

A state of `D` leaves as many circles as its restriction to the other crossings leaves in the
resolution chosen by its value at `c` (`TauCeti.PDCode.stateLoopCount_insertNth`). Summing over
states gives the skein relation of the Kauffman bracket at an arbitrary crossing,
`TauCeti.PDCode.kauffmanBracket_eq_resolveCrossing`, including crossings to which an arc returns,
which `TauCeti.PDCode.kauffmanBracket_insertCrossing` excludes.

## Main definitions

* `TauCeti.PDCode.detachedCircleCount D c t`: the circles of the smoothing of `c` that meet no
  other crossing.
* `TauCeti.PDCode.resolveCrossing D c t`: the code with the crossing `c` smoothed.

## Main results

* `TauCeti.PDCode.stateLoopCount_insertNth`: a state of `D` leaves as many circles as its
  restriction leaves in the corresponding resolution.
* `TauCeti.PDCode.kauffmanBracket_eq_resolveCrossing`: the skein relation of the Kauffman bracket.
* `TauCeti.PDCode.resolveCrossing_edgePair_val_of_edgePair_val_eq`,
  `TauCeti.PDCode.resolveCrossing_edgePair_val_of_edgePair_val_eq_crossing` and
  `TauCeti.PDCode.resolveCrossing_edgePair_val_of_edgePair_val_eq_crossing_twice`: the arcs of the
  resolution that avoid `c`, and those passing once or twice through its smoothing.
* `TauCeti.PDCode.detachedCircleCount_eq`: the detached circles in terms of the arcs of `D`.
* `TauCeti.PDCode.mirror_resolveCrossing`: mirroring exchanges the two resolutions.
* `TauCeti.PDCode.detachedCircleCount_eq_zero`: no circle is detached when no arc of `D` joins
  two slots of `c`; on the other hand the two resolutions of the kink consist of two and of one
  crossing-free circles (`TauCeti.PDCode.crossinglessComponentCount_resolveCrossing_kink_true`).

## References

* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395-407.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3,
  Definition 3.1 (the skein relation defining the bracket).
-/

public section

namespace TauCeti

open Equiv Equiv.Perm TemperleyLieb

namespace PDCode

variable {n : ℕ} (D : PDCode (n + 1)) (c : Fin (n + 1))

/-! ### The positions around a crossing -/

/-- The half-edges of `D`, indexed by the positions of the crossings other than `c`, in their
order, followed by the four slots of `c`. -/
private def slotEquiv : Fin (4 * n) ⊕ Fin 4 ≃ Fin (4 * (n + 1)) :=
  ((Equiv.sumCongr (crossingSlotEquiv n).symm (Equiv.punitProd (Fin 4)).symm).trans
    ((Equiv.sumProdDistrib (Fin n) PUnit.{1} (Fin 4)).symm.trans
      (Equiv.prodCongr ((Equiv.optionEquivSumPUnit (Fin n)).symm.trans (finSuccEquiv' c).symm)
        (Equiv.refl _)))).trans
    ((crossingSlotEquiv (n + 1)).trans D.halfEdge)

private theorem slotEquiv_inl (i : Fin n) (k : Fin 4) :
    D.slotEquiv c (.inl (crossingSlotEquiv n (i, k))) = D.crossing (c.succAbove i) k := by
  simp [slotEquiv]

private theorem slotEquiv_inr (k : Fin 4) : D.slotEquiv c (.inr k) = D.crossing c k := by
  simp [slotEquiv]

/-- The arcs of `D` on the positions of the other crossings and the slots of `c`. -/
private def slotMatching : PerfectMatching (Fin (4 * n) ⊕ Fin 4) :=
  PerfectMatching.congr (D.slotEquiv c).symm D.edgePair

private theorem slotMatching_val :
    (D.slotMatching c).val = (D.slotEquiv c).symm.permCongr D.edgePair.val :=
  PerfectMatching.congr_val _ _

/-- The arc of `D` at a slot of a crossing other than `c`. -/
private theorem slotMatching_val_inl_eq_iff (i : Fin n) (k : Fin 4) {y : Fin (4 * n) ⊕ Fin 4} :
    (D.slotMatching c).val (.inl (crossingSlotEquiv n (i, k))) = y ↔
      D.edgePair.val (D.crossing (c.succAbove i) k) = D.slotEquiv c y := by
  rw [slotMatching_val, permCongr_apply, symm_symm, slotEquiv_inl, Equiv.symm_apply_eq]

/-- The arc of `D` at a slot of `c`. -/
private theorem slotMatching_val_inr_eq_iff (k : Fin 4) {y : Fin (4 * n) ⊕ Fin 4} :
    (D.slotMatching c).val (.inr k) = y ↔ D.edgePair.val (D.crossing c k) = D.slotEquiv c y := by
  rw [slotMatching_val, permCongr_apply, symm_symm, slotEquiv_inr, Equiv.symm_apply_eq]

/-- The local smoothing selecting the `A`-smoothing of `c` for `t = true` and the `B`-smoothing
for `t = false`. -/
private def localSmoothing (t : Bool) : Perm (Fin 4) :=
  slotSmoothing (bif t then D.overPair c else !D.overPair c)

/-- The arcs of `D` with the first smoothing arc, at slot `0`, cut off. -/
private def pinchedOnce (t : Bool) : PerfectMatching (Fin (4 * n) ⊕ Fin 4) :=
  (D.slotMatching c).reconnect (.inr 0) (.inr (D.localSmoothing c t 0))

/-- The arcs of `D` with both smoothing arcs, at slots `0` and `2`, cut off. -/
private def pinchedTwice (t : Bool) : PerfectMatching (Fin (4 * n) ⊕ Fin 4) :=
  (D.pinchedOnce c t).reconnect (.inr 2) (.inr (D.localSmoothing c t 2))

private theorem localSmoothing_apply_apply (t : Bool) (m : Fin 4) :
    D.localSmoothing c t (D.localSmoothing c t m) = m :=
  slotSmoothing_apply_apply _ m

/-- The slots of `c` are `0`, `2` and their smoothing partners, and these four are distinct. -/
private theorem localSmoothing_facts (t : Bool) :
    D.localSmoothing c t 0 ≠ 0 ∧ D.localSmoothing c t 2 ≠ 2 ∧ D.localSmoothing c t 0 ≠ 2 ∧
      D.localSmoothing c t 2 ≠ 0 ∧ D.localSmoothing c t 0 ≠ D.localSmoothing c t 2 ∧
      ∀ m, m = 0 ∨ m = D.localSmoothing c t 0 ∨ m = 2 ∨ m = D.localSmoothing c t 2 := by
  rw [localSmoothing]
  generalize (bif t then D.overPair c else !D.overPair c) = b
  refine ⟨slotSmoothing_ne b 0, slotSmoothing_ne b 2, ?_⟩
  cases b <;>
    simp only [slotSmoothing_true, slotSmoothing_false, Perm.mul_apply, swap_apply_def] <;>
    exact ⟨by decide, by decide, by decide, by decide⟩

/-- The smoothing arcs at slots `0` and `2` are disjoint. -/
private theorem ne_of_localSmoothing {t : Bool} {p r : Fin 4}
    (hp : p = 0 ∨ p = D.localSmoothing c t 0) (hr : r = 2 ∨ r = D.localSmoothing c t 2) :
    r ≠ p := by
  revert p r
  rw [localSmoothing]
  generalize (bif t then D.overPair c else !D.overPair c) = b
  cases b <;>
    simp only [slotSmoothing_true, slotSmoothing_false, Perm.mul_apply, swap_apply_def] <;> decide

/-- Two slots `m` and `m'` of `c`, with `m'` neither `m` nor its smoothing partner, lie on the two
different smoothing arcs. -/
private theorem localSmoothing_pair {t : Bool} {m m' : Fin 4} (h : m' ≠ m)
    (h' : m' ≠ D.localSmoothing c t m) :
    (m = 0 ∨ m = D.localSmoothing c t 0) ∧ (m' = 2 ∨ m' = D.localSmoothing c t 2) ∨
      (m = 2 ∨ m = D.localSmoothing c t 2) ∧ (m' = 0 ∨ m' = D.localSmoothing c t 0) := by
  revert m m'
  rw [localSmoothing]
  generalize (bif t then D.overPair c else !D.overPair c) = b
  cases b <;>
    simp only [slotSmoothing_true, slotSmoothing_false, Perm.mul_apply, swap_apply_def] <;> decide

private theorem pinchedTwice_inr (t : Bool) (k : Fin 4) :
    (D.pinchedTwice c t).val (.inr k) = .inr (D.localSmoothing c t k) := by
  obtain ⟨h0, h2, h02, h20, h22, hm⟩ := D.localSmoothing_facts c t
  have hSS := D.localSmoothing_apply_apply c t
  set S := D.localSmoothing c t
  set M₁ := D.pinchedOnce c t
  have h₀ : M₁.val (.inr 0) = .inr (S 0) :=
    PerfectMatching.reconnect_val_self (by simpa using h0)
  have h₀' : M₁.val (.inr (S 0)) = .inr 0 :=
    PerfectMatching.reconnect_val_right (by simpa using h0)
  -- The second reconnection, at slots `2` and `S 2`, keeps the arc joining `0` to `S 0`.
  have h2' : (Sum.inr (S 2) : Fin (4 * n) ⊕ Fin 4) ≠ .inr 2 := by simpa using h2
  rcases hm k with rfl | rfl | rfl | rfl
  · exact PerfectMatching.reconnect_val_of_val_eq h₀ (by simp) (by simpa using h20.symm)
      (by simpa using h02) (fun h ↦ h22 (Sum.inr_injective h))
  · rw [hSS]
    exact PerfectMatching.reconnect_val_of_val_eq h₀' (by simpa using h02)
      (fun h ↦ h22 (Sum.inr_injective h)) (by simp) (by simpa using h20.symm)
  · exact PerfectMatching.reconnect_val_self h2'
  · rw [hSS]
    exact PerfectMatching.reconnect_val_right h2'

/-- The first reconnection continues an arc arriving at slot `0`, or at its smoothing partner,
through the smoothing. -/
private theorem pinchedOnce_val_of_val_eq_inr {t : Bool} {x : Fin (4 * n) ⊕ Fin 4} {m : Fin 4}
    (hx : (D.slotMatching c).val x = .inr m) (hm : m = 0 ∨ m = D.localSmoothing c t 0) :
    (D.pinchedOnce c t).val x = (D.slotMatching c).val (.inr (D.localSmoothing c t m)) := by
  have h0 : (Sum.inr (D.localSmoothing c t 0) : Fin (4 * n) ⊕ Fin 4) ≠ .inr 0 := by
    simpa using (D.localSmoothing_facts c t).1
  rw [pinchedOnce, ← (D.slotMatching c).apply_eq_of_apply_eq hx]
  rcases hm with rfl | rfl
  · exact PerfectMatching.reconnect_val_val_self h0
  · rw [localSmoothing_apply_apply]
    exact PerfectMatching.reconnect_val_val_right h0

/-- The second reconnection continues an arc arriving at slot `2`, or at its smoothing partner,
through the smoothing. -/
private theorem pinchedTwice_val_of_val_eq_inr {t : Bool} {x : Fin (4 * n) ⊕ Fin 4} {m : Fin 4}
    (hx : (D.pinchedOnce c t).val x = .inr m) (hm : m = 2 ∨ m = D.localSmoothing c t 2) :
    (D.pinchedTwice c t).val x = (D.pinchedOnce c t).val (.inr (D.localSmoothing c t m)) := by
  have h2 : (Sum.inr (D.localSmoothing c t 2) : Fin (4 * n) ⊕ Fin 4) ≠ .inr 2 := by
    simpa using (D.localSmoothing_facts c t).2.1
  rw [pinchedTwice, ← (D.pinchedOnce c t).apply_eq_of_apply_eq hx]
  rcases hm with rfl | rfl
  · exact PerfectMatching.reconnect_val_val_self h2
  · rw [localSmoothing_apply_apply]
    exact PerfectMatching.reconnect_val_val_right h2

/-- The smoothing partner of a slot on a smoothing arc lies on the same smoothing arc. -/
private theorem localSmoothing_mem_pair {t : Bool} {k m : Fin 4}
    (hm : m = k ∨ m = D.localSmoothing c t k) :
    D.localSmoothing c t m = k ∨ D.localSmoothing c t m = D.localSmoothing c t k := by
  rcases hm with rfl | rfl
  exacts [.inr rfl, .inl (D.localSmoothing_apply_apply c t _)]

/-- The first reconnection keeps an arc from another crossing to the smoothing arc at slot `2`. -/
private theorem pinchedOnce_val_inl_of_val_eq_inr_two {t : Bool} {y : Fin (4 * n)} {m : Fin 4}
    (hx : (D.slotMatching c).val (.inl y) = .inr m) (hm : m = 2 ∨ m = D.localSmoothing c t 2) :
    (D.pinchedOnce c t).val (.inl y) = .inr m :=
  PerfectMatching.reconnect_val_of_val_eq hx Sum.inl_ne_inr Sum.inl_ne_inr
    (by simpa using D.ne_of_localSmoothing c (.inl rfl) hm)
    (by simpa using D.ne_of_localSmoothing c (.inr rfl) hm)

/-- The first reconnection keeps an arc from the smoothing arc at slot `2` to another crossing. -/
private theorem pinchedOnce_val_inr_of_val_eq_inl_two {t : Bool} {y : Fin (4 * n)} {m : Fin 4}
    (hx : (D.slotMatching c).val (.inr m) = .inl y) (hm : m = 2 ∨ m = D.localSmoothing c t 2) :
    (D.pinchedOnce c t).val (.inr m) = .inl y :=
  (D.pinchedOnce c t).apply_eq_of_apply_eq
    (D.pinchedOnce_val_inl_of_val_eq_inr_two c ((D.slotMatching c).apply_eq_of_apply_eq hx) hm)

private theorem isRight_pinchedTwice (t : Bool) (k : Fin 4) :
    ((D.pinchedTwice c t).val (.inr k)).isRight := by
  simp [pinchedTwice_inr]

/-! ### The resolution -/

/-- The number of circles of the smoothing of the crossing `c` that meet no other crossing, for the
`A`-smoothing when `t = true` and the `B`-smoothing when `t = false`. The smoothing arc at slot `0`
closes into such a circle when the arc of `D` at slot `0` returns to its smoothing partner; once
that arc has been cut off, the smoothing arc at slot `2` closes into such a circle when the
remaining arcs join its two ends. There are at most two such circles. -/
def detachedCircleCount (t : Bool) : ℕ :=
  (if (D.slotMatching c).val (.inr 0) = .inr (D.localSmoothing c t 0) then 1 else 0) +
    if (D.pinchedOnce c t).val (.inr 2) = .inr (D.localSmoothing c t 2) then 1 else 0

/-- **Resolving a crossing.** The PD-code with `n` crossings obtained from `D` by smoothing the
crossing `c`, by its `A`-smoothing when `t = true` and its `B`-smoothing when `t = false`. Its
crossing `i` is the crossing `c.succAbove i` of `D` with the same over-strand, its half-edges are
labelled by their positions, its arcs follow the arcs of `D` through the smoothing of `c`, and its
crossing-free circles are those of `D` together with the circles of the smoothing that meet no
other crossing. -/
def resolveCrossing (t : Bool) : PDCode n where
  halfEdge := 1
  edgePair := PerfectMatching.restrictInl (D.pinchedTwice c t) (D.isRight_pinchedTwice c t)
  crossinglessComponentCount := D.crossinglessComponentCount + D.detachedCircleCount c t
  overPair := D.overPair ∘ c.succAbove

variable (t : Bool)

/-- The half-edges of a resolution are labelled by their positions. -/
@[simp] theorem resolveCrossing_halfEdge : (D.resolveCrossing c t).halfEdge = 1 := (rfl)

-- Not `@[simp]`: `crossing_apply` and `resolveCrossing_halfEdge` already prove it.
/-- The half-edge in slot `k` of crossing `i` of a resolution is its position. -/
theorem crossing_resolveCrossing (i : Fin n) (k : Fin 4) :
    (D.resolveCrossing c t).crossing i k = crossingSlotEquiv n (i, k) := by
  rw [crossing_apply, resolveCrossing_halfEdge, Perm.one_apply]

/-- Crossing `i` of a resolution has the over-strand of crossing `c.succAbove i` of `D`. -/
@[simp] theorem resolveCrossing_overPair (i : Fin n) :
    (D.resolveCrossing c t).overPair i = D.overPair (c.succAbove i) := (rfl)

/-- A resolution keeps the crossing-free circles and adds the detached circles of the
smoothing. -/
@[simp] theorem resolveCrossing_crossinglessComponentCount :
    (D.resolveCrossing c t).crossinglessComponentCount =
      D.crossinglessComponentCount + D.detachedCircleCount c t := (rfl)

private theorem resolveCrossing_edgePair_val :
    (D.resolveCrossing c t).edgePair.val =
      (PerfectMatching.restrictInl (D.pinchedTwice c t) (D.isRight_pinchedTwice c t)).val := (rfl)

/-- The smoothing of the crossing `c` with the arcs cut off is the resolved matching on the
other positions together with the local smoothing on the slots of `c`. -/
private theorem pinchedTwice_val :
    (D.pinchedTwice c t).val =
      Perm.sumCongr (D.resolveCrossing c t).edgePair.val (D.localSmoothing c t) := by
  ext x : 1
  rcases x with y | k
  · rw [Perm.sumCongr_apply, Sum.map_inl, resolveCrossing_edgePair_val,
      PerfectMatching.inl_restrictInl_val]
  · rw [Perm.sumCongr_apply, Sum.map_inr, pinchedTwice_inr]

/-- An arc of `D` between two crossings other than `c` is an arc of every resolution of `c`. -/
theorem resolveCrossing_edgePair_val_of_edgePair_val_eq {i j : Fin n} {k l : Fin 4}
    (h : D.edgePair.val (D.crossing (c.succAbove i) k) = D.crossing (c.succAbove j) l) :
    (D.resolveCrossing c t).edgePair.val (crossingSlotEquiv n (i, k)) =
      crossingSlotEquiv n (j, l) := by
  rw [resolveCrossing_edgePair_val, PerfectMatching.restrictInl_val_eq_iff, pinchedTwice,
    pinchedOnce]
  have hM : (D.slotMatching c).val (.inl (crossingSlotEquiv n (i, k))) =
      .inl (crossingSlotEquiv n (j, l)) :=
    (D.slotMatching_val_inl_eq_iff c i k).2 (by rwa [slotEquiv_inl])
  exact PerfectMatching.reconnect_val_of_val_eq
    (PerfectMatching.reconnect_val_of_val_eq hM Sum.inl_ne_inr Sum.inl_ne_inr Sum.inl_ne_inr
      Sum.inl_ne_inr) Sum.inl_ne_inr Sum.inl_ne_inr Sum.inl_ne_inr Sum.inl_ne_inr

/-- Smoothing a resolution reconnects its slots by the chosen local smoothings. -/
@[simp] theorem smoothingTurn_resolveCrossing (b : Fin n → Bool) (i : Fin n) (k : Fin 4) :
    (D.resolveCrossing c t).smoothingTurn b (crossingSlotEquiv n (i, k)) =
      crossingSlotEquiv n (i, slotSmoothing (b i) k) := by
  simpa using (D.resolveCrossing c t).smoothingTurn_crossing b i k

/-- At a crossing other than `c`, a state of `D` selects the smoothing its restriction selects in
a resolution of `c`. -/
theorem smoothingChoice_insertNth_succAbove (s : Fin n → Bool) (i : Fin n) :
    D.smoothingChoice (c.insertNth t s) (c.succAbove i) =
      (D.resolveCrossing c t).smoothingChoice s i := by
  cases hs : s i <;> simp [hs]

/-- Smoothing the crossings of `D` according to a state is, on the positions of the other
crossings, smoothing the resolution of `c` chosen by the state at `c`, and on the slots of `c`,
the local smoothing chosen there. -/
private theorem permCongr_smoothingTurn (s : Fin n → Bool) :
    (D.slotEquiv c).symm.permCongr (D.smoothingTurn (D.smoothingChoice (c.insertNth t s))) =
      Perm.sumCongr ((D.resolveCrossing c t).smoothingTurn
        ((D.resolveCrossing c t).smoothingChoice s)) (D.localSmoothing c t) := by
  ext x : 1
  rcases x with y | k
  · obtain ⟨⟨i, k⟩, rfl⟩ := (crossingSlotEquiv n).surjective y
    rw [permCongr_apply, symm_symm, Equiv.symm_apply_eq]
    simp [slotEquiv_inl, smoothingTurn_crossing, smoothingChoice_insertNth_succAbove D c t]
  · rw [permCongr_apply, symm_symm, Equiv.symm_apply_eq]
    cases t <;> simp [slotEquiv_inr, smoothingTurn_crossing, localSmoothing]

/-- The local smoothing is an involution. -/
private theorem localSmoothing_mul_self : D.localSmoothing c t * D.localSmoothing c t = 1 := by
  ext k : 1
  simp [localSmoothing]

/-- One reconnection of the arcs of `D` at a slot `k` of `c`, joining `k` to its smoothing
partner, gains the two traversals of a new circle unless the arc at `k` already returns to that
partner. -/
private theorem orbitCount_mul_reconnect_inr (s : Fin n → Bool)
    (M : PerfectMatching (Fin (4 * n) ⊕ Fin 4)) (k : Fin 4) :
    orbitCount (Perm.sumCongr ((D.resolveCrossing c t).smoothingTurn
        ((D.resolveCrossing c t).smoothingChoice s)) (D.localSmoothing c t) *
        (M.reconnect (.inr k) (.inr (D.localSmoothing c t k))).val) =
      orbitCount (Perm.sumCongr ((D.resolveCrossing c t).smoothingTurn
        ((D.resolveCrossing c t).smoothingChoice s)) (D.localSmoothing c t) * M.val) +
        if M.val (.inr k) = .inr (D.localSmoothing c t k) then 0 else 2 := by
  split_ifs with h
  · rw [← h, PerfectMatching.reconnect_partner, add_zero]
  · have hk : D.localSmoothing c t k ≠ k := slotSmoothing_ne _ k
    exact M.orbitCount_mul_reconnect (a := .inr k) (by simp [localSmoothing])
      (by simpa using hk) h

/-- **Circles after resolving a crossing.** A state of `D` leaves as many circles as its
restriction to the other crossings leaves in the resolution of `c` chosen by its value at `c`. -/
@[simp] theorem stateLoopCount_insertNth (s : Fin n → Bool) :
    D.stateLoopCount (c.insertNth t s) = (D.resolveCrossing c t).stateLoopCount s := by
  set R := D.resolveCrossing c t
  set T := Perm.sumCongr (R.smoothingTurn (R.smoothingChoice s)) (D.localSmoothing c t)
  have horb : orbitCount (D.statePerm (c.insertNth t s)) =
      orbitCount (T * (D.slotMatching c).val) := by
    rw [statePerm_def, ← Equiv.orbitCount_permCongr (D.slotEquiv c).symm, Equiv.permCongr_mul,
      permCongr_smoothingTurn, slotMatching_val]
  -- Cutting off the two smoothing arcs leaves the traversal of `R` and four fixed points.
  have h₁ : orbitCount (T * (D.pinchedOnce c t).val) = orbitCount (T * (D.slotMatching c).val) +
      if (D.slotMatching c).val (.inr 0) = .inr (D.localSmoothing c t 0) then 0 else 2 :=
    D.orbitCount_mul_reconnect_inr c t s _ 0
  have h₂ : orbitCount (T * (D.pinchedTwice c t).val) = orbitCount (T * (D.pinchedOnce c t).val) +
      if (D.pinchedOnce c t).val (.inr 2) = .inr (D.localSmoothing c t 2) then 0 else 2 :=
    D.orbitCount_mul_reconnect_inr c t s _ 2
  have h₃ : orbitCount (T * (D.pinchedTwice c t).val) = orbitCount (R.statePerm s) + 4 := by
    rw [pinchedTwice_val, Perm.sumCongr_mul, localSmoothing_mul_self, Perm.orbitCount_sumCongr,
      statePerm_def, orbitCount_one, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [h₃] at h₂
  rw [stateLoopCount_def, stateLoopCount_def, horb, resolveCrossing_crossinglessComponentCount,
    detachedCircleCount]
  obtain ⟨r, hr⟩ := R.even_orbitCount_statePerm s
  split_ifs at h₁ h₂ ⊢ <;> omega

/-- **The skein relation of the Kauffman bracket** at a crossing `c`: the bracket of `D` is `a`
times the bracket of the `A`-resolution of `c` plus `a⁻¹` times the bracket of its
`B`-resolution. -/
theorem kauffmanBracket_eq_resolveCrossing {R : Type*} [CommRing R] (a : Rˣ) :
    D.kauffmanBracket a =
      a * (D.resolveCrossing c true).kauffmanBracket a +
        ((a⁻¹ : Rˣ) : R) * (D.resolveCrossing c false).kauffmanBracket a := by
  rw [kauffmanBracket_def, kauffmanBracket_def, kauffmanBracket_def,
    ← (Fin.insertNthEquiv (fun _ ↦ Bool) c).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    Finset.mul_sum, Finset.mul_sum]
  simp only [Fin.insertNthEquiv_apply, stateLoopCount_insertNth, stateWeight_insertNth,
    Bool.cond_true, Bool.cond_false, Units.val_mul, mul_assoc]

/-- A code with one crossing has, in its resolution, one crossing-free circle for each circle of
the corresponding state. -/
theorem crossinglessComponentCount_resolveCrossing_eq_stateLoopCount (D : PDCode 1) (t : Bool) :
    (D.resolveCrossing 0 t).crossinglessComponentCount = D.stateLoopCount fun _ ↦ t := by
  have h := D.stateLoopCount_insertNth 0 t Fin.elim0
  rw [stateLoopCount_eq_crossinglessComponentCount] at h
  rw [← h]
  congr 1
  funext i
  rw [Fin.fin_one_eq_zero i, Fin.insertNth_apply_same]

/-- Mirroring a resolution resolves the mirror code by the other smoothing: mirroring exchanges
the `A`- and `B`-smoothings. -/
theorem mirror_resolveCrossing :
    (D.resolveCrossing c t).mirror = D.mirror.resolveCrossing c !t := by
  have hS : D.mirror.localSmoothing c (!t) = D.localSmoothing c t := by
    cases t <;> simp [localSmoothing]
  have hM : D.mirror.slotMatching c = D.slotMatching c := by
    simp only [slotMatching, slotEquiv, mirror_halfEdge, mirror_edgePair]
  have hO : D.mirror.pinchedOnce c (!t) = D.pinchedOnce c t := by
    rw [pinchedOnce, pinchedOnce, hS, hM]
  have hT : D.mirror.pinchedTwice c (!t) = D.pinchedTwice c t := by
    rw [pinchedTwice, pinchedTwice, hS, hO]
  apply PDCode.ext
  · simp
  · refine Subtype.ext (Equiv.ext fun y ↦ Sum.inl_injective (β := Fin 4) ?_)
    rw [mirror_edgePair, resolveCrossing_edgePair_val, resolveCrossing_edgePair_val,
      PerfectMatching.inl_restrictInl_val, PerfectMatching.inl_restrictInl_val, hT]
  · simp [detachedCircleCount, hS, hM, hO]
  · funext i
    simp

/-- The circles of the smoothing of `c` that meet no other crossing, in terms of the arcs of `D`:
the smoothing arc at slot `0` is detached when the arc of `D` at slot `0` returns to its smoothing
partner, and the smoothing arc at slot `2` when the arc of `D` at slot `2` returns to its smoothing
partner, either directly or through the smoothing arc at slot `0`. -/
theorem detachedCircleCount_eq :
    D.detachedCircleCount c t =
      (if D.edgePair.val (D.crossing c 0) =
          D.crossing c (slotSmoothing (bif t then D.overPair c else !D.overPair c) 0) then 1
        else 0) +
        if D.edgePair.val (D.crossing c 2) =
              D.crossing c (slotSmoothing (bif t then D.overPair c else !D.overPair c) 2) ∨
            D.edgePair.val (D.crossing c 2) = D.crossing c 0 ∧
              D.edgePair.val
                  (D.crossing c (slotSmoothing (bif t then D.overPair c else !D.overPair c) 0)) =
                D.crossing c (slotSmoothing (bif t then D.overPair c else !D.overPair c) 2) ∨
            D.edgePair.val (D.crossing c 2) =
                D.crossing c (slotSmoothing (bif t then D.overPair c else !D.overPair c) 0) ∧
              D.edgePair.val (D.crossing c 0) =
                D.crossing c (slotSmoothing (bif t then D.overPair c else !D.overPair c) 2) then 1
        else 0 := by
  obtain ⟨h0, -, h02, h20, -, -⟩ := D.localSmoothing_facts c t
  rw [detachedCircleCount, ← localSmoothing]
  have hE (k l : Fin 4) : D.edgePair.val (D.crossing c k) = D.crossing c l ↔
      (D.slotMatching c).val (.inr k) = .inr l := by
    rw [slotMatching_val_inr_eq_iff, slotEquiv_inr]
  simp only [hE]
  set S := D.localSmoothing c t
  set M := D.slotMatching c
  have h0' : (Sum.inr (S 0) : Fin (4 * n) ⊕ Fin 4) ≠ .inr 0 := by simpa using h0
  -- The first reconnection changes the arc at slot `2` only when it ends at slot `0` or `S 0`.
  have key : (D.pinchedOnce c t).val (.inr 2) = .inr (S 2) ↔ M.val (.inr 2) = .inr (S 2) ∨
      M.val (.inr 2) = .inr 0 ∧ M.val (.inr (S 0)) = .inr (S 2) ∨
      M.val (.inr 2) = .inr (S 0) ∧ M.val (.inr 0) = .inr (S 2) := by
    by_cases hA : M.val (.inr 2) = .inr 0
    · have hP : (D.pinchedOnce c t).val (M.val (.inr 0)) = M.val (.inr (S 0)) :=
        PerfectMatching.reconnect_val_val_self h0'
      rw [M.apply_eq_of_apply_eq hA] at hP
      simp [hP, hA, h20.symm, h0.symm]
    by_cases hB : M.val (.inr 2) = .inr (S 0)
    · have hP : (D.pinchedOnce c t).val (M.val (.inr (S 0))) = M.val (.inr 0) :=
        PerfectMatching.reconnect_val_val_right h0'
      rw [M.apply_eq_of_apply_eq hB] at hP
      simp [hP, hB, h0]
    rw [pinchedOnce, PerfectMatching.reconnect_val_of_ne (by simp) (by simpa using h02.symm)
      (fun h ↦ hA (M.apply_eq_of_apply_eq h.symm)) (fun h ↦ hB (M.apply_eq_of_apply_eq h.symm))]
    simp [hA, hB]
  simp only [key]

/-- No circle of the smoothing of `c` is detached when no arc of `D` joins two slots of `c`. -/
theorem detachedCircleCount_eq_zero (h : ∀ k l, D.edgePair.val (D.crossing c k) ≠ D.crossing c l) :
    D.detachedCircleCount c t = 0 := by
  simp only [detachedCircleCount_eq, h, false_and, or_self, ↓reduceIte, add_zero]

/-- An arc of `D` from a crossing other than `c` to a slot `m` of `c`, continued through the
smoothing of `c` to another crossing other than `c`, is an arc of the resolution. -/
theorem resolveCrossing_edgePair_val_of_edgePair_val_eq_crossing {i j : Fin n} {k l m : Fin 4}
    (h₁ : D.edgePair.val (D.crossing (c.succAbove i) k) = D.crossing c m)
    (h₂ : D.edgePair.val
        (D.crossing c (slotSmoothing (bif t then D.overPair c else !D.overPair c) m)) =
      D.crossing (c.succAbove j) l) :
    (D.resolveCrossing c t).edgePair.val (crossingSlotEquiv n (i, k)) =
      crossingSlotEquiv n (j, l) := by
  obtain ⟨-, -, -, -, -, hm⟩ := D.localSmoothing_facts c t
  rw [← localSmoothing] at h₂
  set S := D.localSmoothing c t
  set M := D.slotMatching c
  have hM₁ : M.val (.inl (crossingSlotEquiv n (i, k))) = .inr m :=
    (D.slotMatching_val_inl_eq_iff c i k).2 (by rwa [slotEquiv_inr])
  have hM₂ : M.val (.inr (S m)) = .inl (crossingSlotEquiv n (j, l)) :=
    (D.slotMatching_val_inr_eq_iff c _).2 (by rwa [slotEquiv_inl])
  rw [resolveCrossing_edgePair_val, PerfectMatching.restrictInl_val_eq_iff]
  obtain hA | hB : (m = 0 ∨ m = S 0) ∨ (m = 2 ∨ m = S 2) := by simpa only [or_assoc] using hm m
  · -- The arc enters `c` on the smoothing arc at slot `0`: the first reconnection continues it.
    rw [pinchedTwice]
    exact PerfectMatching.reconnect_val_of_val_eq
      ((D.pinchedOnce_val_of_val_eq_inr c hM₁ hA).trans hM₂) Sum.inl_ne_inr Sum.inl_ne_inr
      Sum.inl_ne_inr Sum.inl_ne_inr
  · -- The arc enters `c` on the smoothing arc at slot `2`: the second reconnection continues it.
    rw [D.pinchedTwice_val_of_val_eq_inr c (D.pinchedOnce_val_inl_of_val_eq_inr_two c hM₁ hB) hB]
    exact D.pinchedOnce_val_inr_of_val_eq_inl_two c hM₂ (D.localSmoothing_mem_pair c hB)

/-- An arc of `D` from a crossing other than `c` to a slot `m` of `c`, continued through the
smoothing of `c` to a slot `m'` of `c`, and through the smoothing once more to another crossing
other than `c`, is an arc of the resolution. -/
theorem resolveCrossing_edgePair_val_of_edgePair_val_eq_crossing_twice {i j : Fin n}
    {k l m m' : Fin 4} (h₁ : D.edgePair.val (D.crossing (c.succAbove i) k) = D.crossing c m)
    (h₂ : D.edgePair.val
        (D.crossing c (slotSmoothing (bif t then D.overPair c else !D.overPair c) m)) =
      D.crossing c m')
    (h₃ : D.edgePair.val
        (D.crossing c (slotSmoothing (bif t then D.overPair c else !D.overPair c) m')) =
      D.crossing (c.succAbove j) l) :
    (D.resolveCrossing c t).edgePair.val (crossingSlotEquiv n (i, k)) =
      crossingSlotEquiv n (j, l) := by
  rw [← localSmoothing] at h₂ h₃
  set S := D.localSmoothing c t
  set M := D.slotMatching c
  have hM₁ : M.val (.inl (crossingSlotEquiv n (i, k))) = .inr m :=
    (D.slotMatching_val_inl_eq_iff c i k).2 (by rwa [slotEquiv_inr])
  have hM₂ : M.val (.inr (S m)) = .inr m' :=
    (D.slotMatching_val_inr_eq_iff c _).2 (by rwa [slotEquiv_inr])
  have hM₃ : M.val (.inr (S m')) = .inl (crossingSlotEquiv n (j, l)) :=
    (D.slotMatching_val_inr_eq_iff c _).2 (by rwa [slotEquiv_inl])
  -- The arc of `D` from `S m` to `m'` joins the two smoothing arcs.
  have hm : m' ≠ m := by
    rintro rfl
    simpa using (M.apply_eq_of_apply_eq hM₁).symm.trans (M.apply_eq_of_apply_eq hM₂)
  have hm' : m' ≠ S m := fun h ↦ M.apply_ne _ (by rw [hM₂, h])
  rw [resolveCrossing_edgePair_val, PerfectMatching.restrictInl_val_eq_iff]
  rcases D.localSmoothing_pair c hm hm' with ⟨hA, hB⟩ | ⟨hB, hA⟩
  · -- The first reconnection continues the arc to `m'`, and the second continues it to `S m'`.
    rw [D.pinchedTwice_val_of_val_eq_inr c ((D.pinchedOnce_val_of_val_eq_inr c hM₁ hA).trans hM₂)
      hB]
    exact D.pinchedOnce_val_inr_of_val_eq_inl_two c hM₃ (D.localSmoothing_mem_pair c hB)
  · -- The second reconnection continues the arc to `S m`, and the first continues it to `S m'`.
    rw [D.pinchedTwice_val_of_val_eq_inr c (D.pinchedOnce_val_inl_of_val_eq_inr_two c hM₁ hB) hB,
      D.pinchedOnce_val_of_val_eq_inr c hM₂ hA, hM₃]

/-- The `A`-resolution of the kink consists of two crossing-free circles. -/
theorem crossinglessComponentCount_resolveCrossing_kink_true :
    (kink.resolveCrossing 0 true).crossinglessComponentCount = 2 := by
  rw [crossinglessComponentCount_resolveCrossing_eq_stateLoopCount, stateLoopCount_kink_true]

/-- The `B`-resolution of the kink consists of one crossing-free circle. -/
theorem crossinglessComponentCount_resolveCrossing_kink_false :
    (kink.resolveCrossing 0 false).crossinglessComponentCount = 1 := by
  rw [crossinglessComponentCount_resolveCrossing_eq_stateLoopCount, stateLoopCount_kink_false]

end PDCode

end TauCeti
