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
* `TauCeti.PDCode.resolveCrossing_edgePair_val_of_edgePair_val_eq` and
  `TauCeti.PDCode.resolveCrossing_edgePair_val_of_edgePair_val_eq_crossing`: the arcs of the
  resolution that avoid `c`, and those passing once through its smoothing.
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

/-- Reconnecting a matching of `α ⊕ β` at two points of `β` keeps an arc from a point of `α` to a
point of `α`, or to a third point of `β`. -/
private theorem reconnect_inr_val_inl {α β : Type*} [DecidableEq α] [DecidableEq β]
    {M : PerfectMatching (α ⊕ β)} {x : α} {y : α ⊕ β} (h : M.val (.inl x) = y) {p q : β}
    (hp : y ≠ .inr p) (hq : y ≠ .inr q) : (M.reconnect (.inr p) (.inr q)).val (.inl x) = y := by
  have hne (r : β) (hr : y ≠ .inr r) : Sum.inl x ≠ M.val (.inr r) := fun h' ↦
    hr (h ▸ M.apply_eq_of_apply_eq h'.symm)
  rw [PerfectMatching.reconnect_val_of_ne (by simp) (by simp) (hne p hp) (hne q hq), h]

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

private theorem pinchedTwice_inr (t : Bool) (k : Fin 4) :
    (D.pinchedTwice c t).val (.inr k) = .inr (D.localSmoothing c t k) := by
  obtain ⟨h0, h2, h02, h20, h22, hm⟩ := D.localSmoothing_facts c t
  have hSS (m : Fin 4) : D.localSmoothing c t (D.localSmoothing c t m) = m :=
    slotSmoothing_apply_apply _ m
  set S := D.localSmoothing c t
  set M₁ := D.pinchedOnce c t
  have h₀ : M₁.val (.inr 0) = .inr (S 0) :=
    PerfectMatching.reconnect_val_self (by simpa using h0)
  have h₀' : M₁.val (.inr (S 0)) = .inr 0 :=
    PerfectMatching.reconnect_val_right (by simpa using h0)
  -- The second reconnection, at slots `2` and `S 2`, keeps the arc joining `0` to `S 0`.
  have hkeep (x y : Fin 4) (hxy : M₁.val (.inr x) = .inr y) (hx : x ≠ 2) (hx' : x ≠ S 2)
      (hy : y ≠ 2) (hy' : y ≠ S 2) : (D.pinchedTwice c t).val (.inr x) = .inr y := by
    have hne (r : Fin 4) (hr : y ≠ r) : (Sum.inr x : Fin (4 * n) ⊕ Fin 4) ≠ M₁.val (.inr r) :=
      fun h' ↦ hr (Sum.inr_injective (hxy ▸ M₁.apply_eq_of_apply_eq h'.symm))
    rw [pinchedTwice, PerfectMatching.reconnect_val_of_ne (by simpa using hx)
      (by simpa using hx') (hne 2 hy) (hne _ hy'), hxy]
  have h2' : (Sum.inr (S 2) : Fin (4 * n) ⊕ Fin 4) ≠ .inr 2 := by simpa using h2
  rcases hm k with rfl | rfl | rfl | rfl
  · exact hkeep 0 (S 0) h₀ (by decide) h20.symm h02 h22
  · rw [hSS]
    exact hkeep (S 0) 0 h₀' h02 h22 (by decide) h20.symm
  · exact PerfectMatching.reconnect_val_self h2'
  · rw [hSS]
    exact PerfectMatching.reconnect_val_right h2'

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
      .inl (crossingSlotEquiv n (j, l)) := by
    rw [slotMatching_val, permCongr_apply, symm_symm, slotEquiv_inl, h, Equiv.symm_apply_eq,
      slotEquiv_inl]
  exact reconnect_inr_val_inl (reconnect_inr_val_inl hM (by simp) (by simp)) (by simp) (by simp)

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
    rw [permCongr_apply, symm_symm, slotEquiv_inl, crossing_apply, smoothingTurn_crossing,
      Equiv.symm_apply_eq, Perm.sumCongr_apply, Sum.map_inl, smoothingTurn_resolveCrossing,
      slotEquiv_inl, smoothingChoice_insertNth_succAbove D c t]
  · rw [permCongr_apply, symm_symm, slotEquiv_inr, crossing_apply, smoothingTurn_crossing,
      Equiv.symm_apply_eq, Perm.sumCongr_apply, Sum.map_inr, slotEquiv_inr, localSmoothing]
    cases t <;> simp

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

/-- No circle of the smoothing of `c` is detached when no arc of `D` joins two slots of `c`. -/
theorem detachedCircleCount_eq_zero (h : ∀ k l, D.edgePair.val (D.crossing c k) ≠ D.crossing c l) :
    D.detachedCircleCount c t = 0 := by
  have hM (k l : Fin 4) : (D.slotMatching c).val (.inr k) ≠ .inr l := by
    rw [slotMatching_val, permCongr_apply, symm_symm, slotEquiv_inr, Ne, Equiv.symm_apply_eq,
      slotEquiv_inr]
    exact h k l
  have hne (k l : Fin 4) : (Sum.inr k : Fin (4 * n) ⊕ Fin 4) ≠ (D.slotMatching c).val (.inr l) :=
    fun hk ↦ hM l k hk.symm
  have h02 : D.localSmoothing c t 0 ≠ 2 := by
    rw [localSmoothing]
    generalize (bif t then D.overPair c else !D.overPair c) = b
    cases b <;> simp [Perm.mul_apply, swap_apply_def]
  have h₂ : (D.pinchedOnce c t).val (.inr 2) = (D.slotMatching c).val (.inr 2) :=
    PerfectMatching.reconnect_val_of_ne (by simp) (by simpa using h02.symm) (hne _ _) (hne _ _)
  simp [detachedCircleCount, h₂, hM]

/-- An arc of `D` from a crossing other than `c` to a slot `m` of `c`, continued through the
smoothing of `c` to another crossing other than `c`, is an arc of the resolution. -/
theorem resolveCrossing_edgePair_val_of_edgePair_val_eq_crossing {i j : Fin n} {k l m : Fin 4}
    (h₁ : D.edgePair.val (D.crossing (c.succAbove i) k) = D.crossing c m)
    (h₂ : D.edgePair.val
        (D.crossing c (slotSmoothing (bif t then D.overPair c else !D.overPair c) m)) =
      D.crossing (c.succAbove j) l) :
    (D.resolveCrossing c t).edgePair.val (crossingSlotEquiv n (i, k)) =
      crossingSlotEquiv n (j, l) := by
  obtain ⟨h0, h2, h02, h20, h22, hm⟩ := D.localSmoothing_facts c t
  have hSS (m : Fin 4) : D.localSmoothing c t (D.localSmoothing c t m) = m :=
    slotSmoothing_apply_apply _ m
  have h₂' : D.edgePair.val (D.crossing c (D.localSmoothing c t m)) =
      D.crossing (c.succAbove j) l := h₂
  set S := D.localSmoothing c t
  set M := D.slotMatching c
  have hM₁ : M.val (.inl (crossingSlotEquiv n (i, k))) = .inr m := by
    rw [slotMatching_val, permCongr_apply, symm_symm, slotEquiv_inl, h₁, Equiv.symm_apply_eq,
      slotEquiv_inr]
  have hM₂ : M.val (.inr (S m)) = .inl (crossingSlotEquiv n (j, l)) := by
    rw [slotMatching_val, permCongr_apply, symm_symm, slotEquiv_inr, h₂', Equiv.symm_apply_eq,
      slotEquiv_inl]
  rw [resolveCrossing_edgePair_val, PerfectMatching.restrictInl_val_eq_iff, pinchedTwice]
  have h0' : (Sum.inr (S 0) : Fin (4 * n) ⊕ Fin 4) ≠ .inr 0 := by simpa using h0
  have h2' : (Sum.inr (S 2) : Fin (4 * n) ⊕ Fin 4) ≠ .inr 2 := by simpa using h2
  rcases hm m with rfl | rfl | rfl | rfl
  · -- The arc enters `c` at slot `0`: the first reconnection joins it to the arc leaving `S 0`.
    have hx : (D.pinchedOnce c t).val (.inl (crossingSlotEquiv n (i, k))) =
        .inl (crossingSlotEquiv n (j, l)) := by
      rw [pinchedOnce, ← M.apply_eq_of_apply_eq hM₁, PerfectMatching.reconnect_val_val_self h0',
        hM₂]
    exact reconnect_inr_val_inl hx (by simp) (by simp)
  · have hx : (D.pinchedOnce c t).val (.inl (crossingSlotEquiv n (i, k))) =
        .inl (crossingSlotEquiv n (j, l)) := by
      rw [hSS] at hM₂
      rw [pinchedOnce, ← M.apply_eq_of_apply_eq hM₁, PerfectMatching.reconnect_val_val_right h0',
        hM₂]
    exact reconnect_inr_val_inl hx (by simp) (by simp)
  · -- The arc enters `c` at slot `2`, which the first reconnection keeps; the second joins it to
    -- the arc leaving `S 2`.
    have hx : (D.pinchedOnce c t).val (.inl (crossingSlotEquiv n (i, k))) = .inr 2 :=
      reconnect_inr_val_inl hM₁ (by simp) (by simpa using h02.symm)
    have hy : (D.pinchedOnce c t).val (.inl (crossingSlotEquiv n (j, l))) = .inr (S 2) :=
      reconnect_inr_val_inl (M.apply_eq_of_apply_eq hM₂) (by simpa using h20)
        (fun h ↦ h22 (Sum.inr_injective h).symm)
    rw [← (D.pinchedOnce c t).apply_eq_of_apply_eq hx, PerfectMatching.reconnect_val_val_self h2',
      (D.pinchedOnce c t).apply_eq_of_apply_eq hy]
  · rw [hSS] at hM₂
    have hx : (D.pinchedOnce c t).val (.inl (crossingSlotEquiv n (i, k))) = .inr (S 2) :=
      reconnect_inr_val_inl hM₁ (by simpa using h20) (fun h ↦ h22 (Sum.inr_injective h).symm)
    have hy : (D.pinchedOnce c t).val (.inl (crossingSlotEquiv n (j, l))) = .inr 2 :=
      reconnect_inr_val_inl (M.apply_eq_of_apply_eq hM₂) (by simp) (by simpa using h02.symm)
    rw [← (D.pinchedOnce c t).apply_eq_of_apply_eq hx, PerfectMatching.reconnect_val_val_right h2',
      (D.pinchedOnce c t).apply_eq_of_apply_eq hy]

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
