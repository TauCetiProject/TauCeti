/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Saddle
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

The two smoothed diagrams are in fact the same circles: the resolved circles of the restricted
state correspond to those of the state of `D`
(`TauCeti.PDCode.resolveCrossingResolvedCircleEquiv`). A circle through a half-edge of the
resolution is the circle of `D` through the same half-edge, a crossing-free circle of `D` keeps its
label, and a detached circle is the circle of `D` through slot `0` or slot `2` of `c`. The
correspondence carries the circles through each other crossing onto those of `D`, and commutes
with the saddle correspondences in the directions of the other crossings. This is the comparison
of resolved circles behind the identification of the two faces of the cube of resolutions of `D`
in the direction of `c` with the cubes of resolutions of its two resolutions, from which the
Khovanov skein exact sequence is built.

## Main definitions

* `TauCeti.PDCode.detachedCircleCount D c t`: the circles of the smoothing of `c` that meet no
  other crossing.
* `TauCeti.PDCode.resolveCrossing D c t`: the code with the crossing `c` smoothed.
* `TauCeti.PDCode.resolveCrossingResolvedCircleEquiv D c t s`: the resolved circles of a state of
  the resolution are those of `D` smoothed by the extended state `c.insertNth t s`.

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
* `TauCeti.PDCode.card_circlesAt_resolveCrossing`: a crossing of a resolution meets as many
  circles as the corresponding crossing of `D`.
* `TauCeti.PDCode.resolveCrossingResolvedCircleEquiv_saddleResolvedCircleMap`: the circle
  correspondence commutes with the saddles at the other crossings.

## References

* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395-407.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3,
  Definition 3.1 (the skein relation defining the bracket).
* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), 359-426,
  §3 (the cube of resolutions).
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
theorem stateLoopCount_insertNth (s : Fin n → Bool) :
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
@[simp] theorem mirror_resolveCrossing :
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

/-- An arc of `D` joining two slots of `c`. -/
private theorem slotMatching_val_inr_eq_inr_iff (k l : Fin 4) :
    (D.slotMatching c).val (.inr k) = .inr l ↔
      D.edgePair.val (D.crossing c k) = D.crossing c l := by
  rw [slotMatching_val_inr_eq_iff, slotEquiv_inr]

/-- Once the smoothing arc at slot `0` is cut off, the remaining arcs join the two ends of the
smoothing arc at slot `2` exactly when an arc of `D` joins them, either directly or through the
smoothing arc at slot `0`. -/
private theorem pinchedOnce_val_inr_two_eq_iff :
    (D.pinchedOnce c t).val (.inr 2) = .inr (D.localSmoothing c t 2) ↔
      (D.slotMatching c).val (.inr 2) = .inr (D.localSmoothing c t 2) ∨
        (D.slotMatching c).val (.inr 2) = .inr 0 ∧
          (D.slotMatching c).val (.inr (D.localSmoothing c t 0)) =
            .inr (D.localSmoothing c t 2) ∨
        (D.slotMatching c).val (.inr 2) = .inr (D.localSmoothing c t 0) ∧
          (D.slotMatching c).val (.inr 0) = .inr (D.localSmoothing c t 2) := by
  obtain ⟨h0, -, h02, h20, -, -⟩ := D.localSmoothing_facts c t
  set S := D.localSmoothing c t
  set M := D.slotMatching c
  have h0' : (Sum.inr (S 0) : Fin (4 * n) ⊕ Fin 4) ≠ .inr 0 := by simpa using h0
  -- The first reconnection changes the arc at slot `2` only when it ends at slot `0` or `S 0`.
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
  rw [detachedCircleCount]
  simp only [pinchedOnce_val_inr_two_eq_iff]
  simp only [slotMatching_val_inr_eq_inr_iff, localSmoothing]

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

/-! ### The circles of a resolution

A state `s` of a resolution of `c`, extended by the chosen smoothing `t` at `c`, is a state
`c.insertNth t s` of `D`, and the two smoothed diagrams are the same collection of circles. A
circle of the resolution meeting a crossing is the circle of `D` through the same half-edge, an
old crossing-free circle keeps its label, and a detached circle is the circle of `D` through
slot `0` or `2` of `c` that meets no other crossing. -/

section ResolvedCircle

variable (s : Fin n → Bool)

/-- The circle of the smoothing of `D` through the half-edge at a position. -/
private def positionCircle (x : Fin (4 * n) ⊕ Fin 4) : D.CrossingCircle (c.insertNth t s) :=
  ⟦D.slotEquiv c x⟧

/-- The two ends of an arc of `D` lie on one circle. -/
private theorem positionCircle_slotMatching (x : Fin (4 * n) ⊕ Fin 4) :
    D.positionCircle c t s ((D.slotMatching c).val x) = D.positionCircle c t s x := by
  rw [positionCircle, positionCircle, slotMatching_val, permCongr_apply, symm_symm,
    apply_symm_apply, CrossingCircle.mk_edgePair]

/-- The two ends of an arc of the smoothing lie on one circle. -/
private theorem positionCircle_sumCongr (x : Fin (4 * n) ⊕ Fin 4) :
    D.positionCircle c t s (Perm.sumCongr ((D.resolveCrossing c t).smoothingTurn
      ((D.resolveCrossing c t).smoothingChoice s)) (D.localSmoothing c t) x) =
      D.positionCircle c t s x := by
  rw [← permCongr_smoothingTurn, positionCircle, positionCircle, permCongr_apply, symm_symm,
    apply_symm_apply, CrossingCircle.mk_smoothingTurn]

/-- The two slots of `c` joined by the local smoothing lie on one circle. -/
private theorem positionCircle_localSmoothing (k : Fin 4) :
    D.positionCircle c t s (.inr (D.localSmoothing c t k)) = D.positionCircle c t s (.inr k) := by
  simpa using D.positionCircle_sumCongr c t s (.inr k)

/-- The two ends of an arc of `D` with the smoothing arcs cut off lie on one circle. -/
private theorem positionCircle_pinchedTwice (x : Fin (4 * n) ⊕ Fin 4) :
    D.positionCircle c t s ((D.pinchedTwice c t).val x) = D.positionCircle c t s x :=
  PerfectMatching.apply_reconnect_val
    (PerfectMatching.apply_reconnect_val (D.positionCircle_slotMatching c t s)
      (D.positionCircle_localSmoothing c t s 0).symm)
    (D.positionCircle_localSmoothing c t s 2).symm x

/-- The circles of a resolution meeting a crossing, as circles of `D`. -/
private def crossingCircleMap :
    (D.resolveCrossing c t).CrossingCircle s → D.CrossingCircle (c.insertNth t s) :=
  Quotient.lift (fun y ↦ D.positionCircle c t s (.inl y)) fun _ _ h ↦ by
    induction h with
    | rel y z h =>
      rcases h with rfl | rfl
      · rw [← D.positionCircle_pinchedTwice c t s (.inl y), pinchedTwice_val,
          Perm.sumCongr_apply, Sum.map_inl]
      · rw [← D.positionCircle_sumCongr c t s (.inl y), Perm.sumCongr_apply, Sum.map_inl]
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem crossingCircleMap_mk (y : Fin (4 * n)) :
    D.crossingCircleMap c t s ⟦y⟧ = D.positionCircle c t s (.inl y) := (rfl)

/-- The slot of `c` through which the detached circle with index `j` passes: slot `0` for the
first one when the arc of `D` at slot `0` returns to its smoothing partner, and slot `2`
otherwise. -/
private def detachedSlot (j : Fin (D.detachedCircleCount c t)) : Fin 4 :=
  if (j : ℕ) = 0 ∧ (D.slotMatching c).val (.inr 0) = .inr (D.localSmoothing c t 0) then 0 else 2

/-- The map underlying `TauCeti.PDCode.resolveCrossingResolvedCircleEquiv`. -/
private def resolvedCircleMap :
    (D.resolveCrossing c t).ResolvedCircle s → D.ResolvedCircle (c.insertNth t s) :=
  Sum.elim (fun C ↦ .inl (D.crossingCircleMap c t s C))
    (Fin.addCases (motive := fun _ ↦ D.ResolvedCircle (c.insertNth t s)) (fun i ↦ .inr i)
      fun j ↦ .inl (D.positionCircle c t s (.inr (D.detachedSlot c t j))))

private theorem resolvedCircleMap_inl_mk (y : Fin (4 * n)) :
    D.resolvedCircleMap c t s (.inl ⟦y⟧) = .inl (D.positionCircle c t s (.inl y)) := (rfl)

private theorem resolvedCircleMap_inr_castAdd (i : Fin D.crossinglessComponentCount) :
    D.resolvedCircleMap c t s (.inr (Fin.castAdd _ i)) = .inr i :=
  Fin.addCases_left (motive := fun _ ↦ D.ResolvedCircle (c.insertNth t s)) (left := fun i ↦ .inr i)
    (right := fun j ↦ .inl (D.positionCircle c t s (.inr (D.detachedSlot c t j)))) i

private theorem resolvedCircleMap_inr_natAdd (j : Fin (D.detachedCircleCount c t)) :
    D.resolvedCircleMap c t s (.inr (Fin.natAdd _ j)) =
      .inl (D.positionCircle c t s (.inr (D.detachedSlot c t j))) :=
  Fin.addCases_right (motive := fun _ ↦ D.ResolvedCircle (c.insertNth t s)) (left := fun i ↦ .inr i)
    (right := fun j ↦ .inl (D.positionCircle c t s (.inr (D.detachedSlot c t j)))) j

/-- A circle of `D` through a slot of `c` whose arc runs to another crossing is the image of
the circle of the resolution through that crossing. -/
private theorem exists_resolvedCircleMap_eq_of_inl {k : Fin 4} {y : Fin (4 * n)}
    (hy : (D.slotMatching c).val (.inr k) = .inl y) :
    ∃ C, D.resolvedCircleMap c t s C = .inl (D.positionCircle c t s (.inr k)) :=
  ⟨.inl ⟦y⟧, by rw [resolvedCircleMap_inl_mk, ← hy, positionCircle_slotMatching]⟩

/-- The circle of `D` through slot `0` of `c` is the first detached circle when the arc of `D`
there returns to its smoothing partner. -/
private theorem exists_resolvedCircleMap_eq_zero_of
    (h : (D.slotMatching c).val (.inr 0) = .inr (D.localSmoothing c t 0)) :
    ∃ C, D.resolvedCircleMap c t s C = .inl (D.positionCircle c t s (.inr 0)) := by
  have hj : 0 < D.detachedCircleCount c t := by
    rw [detachedCircleCount]
    simp [h]
  refine ⟨.inr (Fin.natAdd _ ⟨0, hj⟩), ?_⟩
  rw [resolvedCircleMap_inr_natAdd]
  simp [detachedSlot, h]

/-- The circle of `D` through slot `2` of `c` is the last detached circle when, after cutting off
the smoothing arc at slot `0`, the remaining arcs join the two ends of the smoothing arc at
slot `2`. -/
private theorem exists_resolvedCircleMap_eq_two_of
    (h : (D.pinchedOnce c t).val (.inr 2) = .inr (D.localSmoothing c t 2)) :
    ∃ C, D.resolvedCircleMap c t s C = .inl (D.positionCircle c t s (.inr 2)) := by
  have hj : (if (D.slotMatching c).val (.inr 0) = .inr (D.localSmoothing c t 0) then 1 else 0) <
      D.detachedCircleCount c t := by
    rw [detachedCircleCount]
    simp [h]
  refine ⟨.inr (Fin.natAdd _ ⟨_, hj⟩), ?_⟩
  rw [resolvedCircleMap_inr_natAdd, detachedSlot]
  split_ifs <;> simp_all

/-- If the arc of `D` at slot `2` of `c` ends at a slot `m` of the smoothing arc at slot `0`, and
the arc at the other end `S m` of that smoothing arc ends at a slot `m'` of `c`, then `m'` is the
smoothing partner of slot `2`. -/
private theorem eq_localSmoothing_two_of_slotMatching {m m' : Fin 4}
    (hA : m = 0 ∨ m = D.localSmoothing c t 0)
    (hM : (D.slotMatching c).val (.inr 2) = .inr m)
    (hM' : (D.slotMatching c).val (.inr (D.localSmoothing c t m)) = .inr m') :
    m' = D.localSmoothing c t 2 := by
  have hSm := D.localSmoothing_mem_pair c hA
  have hne₁ : m' ≠ D.localSmoothing c t m := fun h ↦
    (D.slotMatching c).apply_ne _ (by rw [hM', h])
  have hne₂ : m' ≠ m := by
    rintro rfl
    have := (D.slotMatching c).apply_eq_of_apply_eq hM'
    rw [(D.slotMatching c).apply_eq_of_apply_eq hM, Sum.inr.injEq] at this
    exact D.ne_of_localSmoothing c hSm (.inl rfl) this
  have hne₃ : m' ≠ 2 := by
    rintro rfl
    have := (D.slotMatching c).apply_eq_of_apply_eq hM'
    rw [hM, Sum.inr.injEq] at this
    exact slotSmoothing_ne _ m this.symm
  rcases (D.localSmoothing_facts c t).2.2.2.2.2 m' with h | h | h | h
  · rcases hA with rfl | rfl
    · exact absurd h hne₂
    · exact absurd (h.trans (D.localSmoothing_apply_apply c t 0).symm) hne₁
  · rcases hA with rfl | rfl
    · exact absurd h hne₁
    · exact absurd h hne₂
  · exact absurd h hne₃
  · exact h

/-- The circle of `D` through slot `2` of `c` is a circle of the resolution. -/
private theorem exists_resolvedCircleMap_eq_two :
    ∃ C, D.resolvedCircleMap c t s C = .inl (D.positionCircle c t s (.inr 2)) := by
  rcases hM : (D.slotMatching c).val (.inr 2) with y | m
  · exact D.exists_resolvedCircleMap_eq_of_inl c t s hM
  obtain hA | hB : (m = 0 ∨ m = D.localSmoothing c t 0) ∨
      (m = 2 ∨ m = D.localSmoothing c t 2) := by
    simpa only [or_assoc] using (D.localSmoothing_facts c t).2.2.2.2.2 m
  · -- The arc at slot `2` runs to the smoothing arc at slot `0`: follow that smoothing arc.
    have e : D.positionCircle c t s (.inr 2) =
        D.positionCircle c t s (.inr (D.localSmoothing c t m)) := by
      rw [positionCircle_localSmoothing, ← hM, positionCircle_slotMatching]
    rcases hM' : (D.slotMatching c).val (.inr (D.localSmoothing c t m)) with y | m'
    · rw [e]
      exact D.exists_resolvedCircleMap_eq_of_inl c t s hM'
    -- Otherwise the arc from there returns to the smoothing arc at slot `2`, at the end other
    -- than slot `2`: the circle passes through all four slots and is detached.
    obtain rfl := D.eq_localSmoothing_two_of_slotMatching c t hA hM hM'
    refine D.exists_resolvedCircleMap_eq_two_of c t s
      ((D.pinchedOnce_val_inr_two_eq_iff c t).2 (.inr ?_))
    rcases hA with rfl | rfl
    · exact .inl ⟨hM, hM'⟩
    · rw [D.localSmoothing_apply_apply c t] at hM'
      exact .inr ⟨hM, hM'⟩
  · rcases hB with rfl | rfl
    · exact absurd hM ((D.slotMatching c).apply_ne _)
    · -- The arc at slot `2` returns to its smoothing partner: a detached circle.
      exact D.exists_resolvedCircleMap_eq_two_of c t s
        ((D.pinchedOnce_val_inr_two_eq_iff c t).2 (.inl hM))

/-- The circle of `D` through slot `0` of `c` is a circle of the resolution. -/
private theorem exists_resolvedCircleMap_eq_zero :
    ∃ C, D.resolvedCircleMap c t s C = .inl (D.positionCircle c t s (.inr 0)) := by
  rcases hM : (D.slotMatching c).val (.inr 0) with y | m
  · exact D.exists_resolvedCircleMap_eq_of_inl c t s hM
  obtain hA | hB : (m = 0 ∨ m = D.localSmoothing c t 0) ∨
      (m = 2 ∨ m = D.localSmoothing c t 2) := by
    simpa only [or_assoc] using (D.localSmoothing_facts c t).2.2.2.2.2 m
  · rcases hA with rfl | rfl
    · exact absurd hM ((D.slotMatching c).apply_ne _)
    · exact D.exists_resolvedCircleMap_eq_zero_of c t s hM
  · -- The arc at slot `0` runs to the smoothing arc at slot `2`.
    have e : D.positionCircle c t s (.inr 0) = D.positionCircle c t s (.inr 2) := by
      rw [← positionCircle_slotMatching, hM]
      rcases hB with rfl | rfl
      exacts [rfl, D.positionCircle_localSmoothing c t s 2]
    rw [e]
    exact D.exists_resolvedCircleMap_eq_two c t s

/-- The circle of `D` through a slot of `c` is a circle of the resolution. -/
private theorem exists_resolvedCircleMap_eq (k : Fin 4) :
    ∃ C, D.resolvedCircleMap c t s C = .inl (D.positionCircle c t s (.inr k)) := by
  rcases (D.localSmoothing_facts c t).2.2.2.2.2 k with rfl | rfl | rfl | rfl
  · exact D.exists_resolvedCircleMap_eq_zero c t s
  · rw [positionCircle_localSmoothing]
    exact D.exists_resolvedCircleMap_eq_zero c t s
  · exact D.exists_resolvedCircleMap_eq_two c t s
  · rw [positionCircle_localSmoothing]
    exact D.exists_resolvedCircleMap_eq_two c t s

private theorem resolvedCircleMap_surjective : Function.Surjective (D.resolvedCircleMap c t s) := by
  rintro (C | i)
  · induction C using Quotient.ind with | _ x
    obtain ⟨a, rfl⟩ := (D.slotEquiv c).surjective x
    rcases a with y | k
    · exact ⟨.inl ⟦y⟧, D.resolvedCircleMap_inl_mk c t s y⟩
    · exact D.exists_resolvedCircleMap_eq c t s k
  · exact ⟨.inr (Fin.castAdd _ i), D.resolvedCircleMap_inr_castAdd c t s i⟩

/-- **The circles of a resolution.** The diagram obtained by smoothing every crossing of a
resolution of `c` according to `s` has the same circles as `D` smoothed according to `s` and the
chosen smoothing `t` at `c`. A circle through a half-edge of the resolution is the circle of `D`
through the same half-edge (`TauCeti.PDCode.resolveCrossingResolvedCircleEquiv_inl_mk`), the
crossing-free circles of `D` keep their labels
(`TauCeti.PDCode.resolveCrossingResolvedCircleEquiv_inr_castAdd`), and each detached circle is a
circle of `D` through a slot of `c`
(`TauCeti.PDCode.resolveCrossingResolvedCircleEquiv_inr_natAdd`). -/
noncomputable def resolveCrossingResolvedCircleEquiv :
    (D.resolveCrossing c t).ResolvedCircle s ≃ D.ResolvedCircle (c.insertNth t s) :=
  Equiv.ofBijective (D.resolvedCircleMap c t s) <|
    (Fintype.bijective_iff_surjective_and_card _).2 ⟨D.resolvedCircleMap_surjective c t s, by
      rw [card_resolvedCircle, card_resolvedCircle, stateLoopCount_insertNth]⟩

private theorem resolveCrossingResolvedCircleEquiv_apply
    (C : (D.resolveCrossing c t).ResolvedCircle s) :
    D.resolveCrossingResolvedCircleEquiv c t s C = D.resolvedCircleMap c t s C := (rfl)

/-- The circle of the resolution through the half-edge in slot `k` of its crossing `i` is the
circle of `D` through the half-edge in slot `k` of the crossing `c.succAbove i`. -/
@[simp]
theorem resolveCrossingResolvedCircleEquiv_inl_mk (i : Fin n) (k : Fin 4) :
    D.resolveCrossingResolvedCircleEquiv c t s (.inl ⟦crossingSlotEquiv n (i, k)⟧) =
      .inl ⟦D.crossing (c.succAbove i) k⟧ := by
  rw [resolveCrossingResolvedCircleEquiv_apply, resolvedCircleMap_inl_mk, positionCircle,
    slotEquiv_inl]

/-- The crossing-free circles of `D` keep their labels in every resolution. -/
@[simp]
theorem resolveCrossingResolvedCircleEquiv_inr_castAdd (i : Fin D.crossinglessComponentCount) :
    D.resolveCrossingResolvedCircleEquiv c t s
        (.inr ((Fin.castAdd (D.detachedCircleCount c t) i).cast
          (D.resolveCrossing_crossinglessComponentCount c t).symm)) = .inr i :=
  D.resolvedCircleMap_inr_castAdd c t s i

/-- The detached circle with index `j` is the circle of `D` through slot `0` of `c` when `j = 0`
and the arc of `D` at slot `0` returns to its smoothing partner, and through slot `2`
otherwise. -/
@[simp]
theorem resolveCrossingResolvedCircleEquiv_inr_natAdd (j : Fin (D.detachedCircleCount c t)) :
    D.resolveCrossingResolvedCircleEquiv c t s
        (.inr ((Fin.natAdd D.crossinglessComponentCount j).cast
          (D.resolveCrossing_crossinglessComponentCount c t).symm)) =
      .inl ⟦D.crossing c (if (j : ℕ) = 0 ∧ D.edgePair.val (D.crossing c 0) =
          D.crossing c (slotSmoothing (bif t then D.overPair c else !D.overPair c) 0)
        then 0 else 2)⟧ := by
  refine (D.resolvedCircleMap_inr_natAdd c t s j).trans ?_
  simp only [positionCircle, slotEquiv_inr, detachedSlot, slotMatching_val_inr_eq_inr_iff,
    localSmoothing]

-- Not `@[simp]`: `TauCeti.PDCode.crossing_apply` rewrites the left-hand side.
/-- The circle of `D` through the half-edge in slot `k` of a crossing other than `c` is the circle
of the resolution through the corresponding half-edge. -/
theorem resolveCrossingResolvedCircleEquiv_symm_inl_mk (i : Fin n) (k : Fin 4) :
    (D.resolveCrossingResolvedCircleEquiv c t s).symm (.inl ⟦D.crossing (c.succAbove i) k⟧) =
      .inl ⟦crossingSlotEquiv n (i, k)⟧ := by
  rw [Equiv.symm_apply_eq, resolveCrossingResolvedCircleEquiv_inl_mk]

/-- A crossing-free circle of `D` is a crossing-free circle of every resolution, with the same
label. -/
@[simp]
theorem resolveCrossingResolvedCircleEquiv_symm_inr (i : Fin D.crossinglessComponentCount) :
    (D.resolveCrossingResolvedCircleEquiv c t s).symm (.inr i) =
      .inr ((Fin.castAdd (D.detachedCircleCount c t) i).cast
        (D.resolveCrossing_crossinglessComponentCount c t).symm) := by
  rw [Equiv.symm_apply_eq, resolveCrossingResolvedCircleEquiv_inr_castAdd]

open Finset in
/-- A crossing of a resolution meets as many circles as the corresponding crossing of `D`, so the
edges of the two cubes of resolutions in its direction are merges, or splits, together. -/
theorem card_circlesAt_resolveCrossing (i : Fin n) :
    #((D.resolveCrossing c t).circlesAt s i) =
      #(D.circlesAt (c.insertNth t s) (c.succAbove i)) := by
  have hinj : Function.Injective (D.crossingCircleMap c t s) := fun C C' h ↦
    Sum.inl_injective <| (D.resolveCrossingResolvedCircleEquiv c t s).injective <| by
      rw [resolveCrossingResolvedCircleEquiv_apply, resolveCrossingResolvedCircleEquiv_apply]
      exact congrArg Sum.inl h
  rw [← card_image_of_injective _ hinj]
  congr 1
  ext C
  simp only [mem_image, mem_circlesAt, exists_exists_eq_and, crossing_resolveCrossing,
    crossingCircleMap_mk, positionCircle, slotEquiv_inl]

/-- A crossing-free circle of a resolution is a crossing-free circle of `D` or a detached
circle. -/
private theorem resolveCrossing_crossinglessComponentCount_cases
    (j : Fin (D.resolveCrossing c t).crossinglessComponentCount) :
    (∃ i, j = (Fin.castAdd (D.detachedCircleCount c t) i).cast
      (D.resolveCrossing_crossinglessComponentCount c t).symm) ∨
    ∃ i, j = (Fin.natAdd D.crossinglessComponentCount i).cast
      (D.resolveCrossing_crossinglessComponentCount c t).symm := by
  induction j using Fin.addCases with
  | left i => exact .inl ⟨i, rfl⟩
  | right i => exact .inr ⟨i, rfl⟩

open Finset in
/-- **Saddles commute with resolving another crossing.** The saddle correspondence of a
resolution in the direction of its crossing `i` is the saddle correspondence of `D` in the
direction of `c.succAbove i`, every crossing-free and detached circle included. -/
theorem resolveCrossingResolvedCircleEquiv_saddleResolvedCircleMap {s s' : Fin n → Bool}
    {i : Fin n} (h : ∀ j, j ≠ i → s j = s' j) (hs' : #((D.resolveCrossing c t).circlesAt s' i) = 1)
    (hD : ∀ j, j ≠ c.succAbove i →
      (c.insertNth t s : Fin (n + 1) → Bool) j = (c.insertNth t s' : Fin (n + 1) → Bool) j)
    (hD' : #(D.circlesAt (c.insertNth t s') (c.succAbove i)) = 1)
    (C : (D.resolveCrossing c t).ResolvedCircle s) :
    D.resolveCrossingResolvedCircleEquiv c t s'
        ((D.resolveCrossing c t).saddleResolvedCircleMap h hs' C) =
      D.saddleResolvedCircleMap hD hD' (D.resolveCrossingResolvedCircleEquiv c t s C) := by
  rcases C with C | j
  · induction C using Quotient.ind with | _ y
    simp only [saddleResolvedCircleMap_inl, saddleCircleMap_mk,
      resolveCrossingResolvedCircleEquiv_apply, resolvedCircleMap_inl_mk, positionCircle]
  · rcases D.resolveCrossing_crossinglessComponentCount_cases c t j with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simp only [saddleResolvedCircleMap_inr, resolveCrossingResolvedCircleEquiv_inr_castAdd]
    · simp only [saddleResolvedCircleMap_inr, resolveCrossingResolvedCircleEquiv_inr_natAdd,
        saddleResolvedCircleMap_inl, saddleCircleMap_mk]

end ResolvedCircle

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
