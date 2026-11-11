/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Brauer.Generator
public import TauCeti.Combinatorics.NoncrossingPartition.PerfectMatching
public import TauCeti.Combinatorics.PlanarMatching.TLDiagram
public import TauCeti.Data.Finset.Sum
public import TauCeti.Logic.Equiv.Fin.Basic

/-!
# Planar Brauer diagrams and Temperley–Lieb diagrams

A Brauer diagram on `k` strands matches the bottom points `Sum.inl i` and the top points
`Sum.inr j` of a rectangle, both rows read from left to right. A Temperley–Lieb diagram `k → k`
numbers the same `k + k` boundary points counterclockwise: `0, …, k - 1` along the bottom from
left to right, then `k, …, 2k - 1` along the top from right to left. The equivalence
`TauCeti.finSumFinRevEquiv k k (k + k) rfl : Fin k ⊕ Fin k ≃ Fin (k + k)`, which keeps the first
block in order and reverses the second, passes from the first labelling to the second: it sends
the bottom point `Sum.inl i` to `i` and the top point `Sum.inr j` to `k + (k - 1 - j)`.

A Brauer diagram is **planar** (`TauCeti.BrauerDiagram.IsPlanar`) when, read in the
counterclockwise numbering, no two of its arcs interleave; these are the diagrams whose arcs can
be drawn inside the rectangle without crossing. Transport along the numbering identifies the
planar matchings of `k + k` points with the planar Brauer diagrams on `k` strands
(`TauCeti.PlanarMatching.brauerDiagramEquiv`). So a Temperley–Lieb diagram `k → k` has an
underlying Brauer diagram (`TauCeti.TLDiagram.toBrauerDiagram`, which forgets the closed
circles), two diagrams have the same underlying Brauer diagram exactly when they have the same
matching, and the Brauer diagrams that arise are exactly the planar ones. Under this comparison
the identity diagram is the identity permutation diagram, vertical reflection is
`TauCeti.BrauerDiagram.flip`, and horizontal reflection relabels both rows by `Fin.rev`.

Stacking planar diagrams gives a planar diagram (`TauCeti.BrauerDiagram.IsPlanar.composeDiagram`),
so the Brauer diagrams of Temperley–Lieb diagrams `k → k` are closed under
`TauCeti.composeDiagram`. The proof is a parity count. If an arc `{y, y'}` of the composite
crossed the arc `{x, x'}`, then the strand from `y` to `y'` would have to cross the strand from
`x` to `x'` inside one of the two diagrams. Counting, modulo `2`, the points of the strand from
`x` that precede a point of either diagram detects such a crossing: by planarity of the two
diagrams the count does not change along the strand from `y`, although it is odd at `y` and even
at `y'`.

Two classes of Brauer diagrams are sorted by planarity. A permutation diagram is planar only for
the identity permutation (`TauCeti.BrauerDiagram.isPlanar_permToBrauer_iff`): two through
strands that swap their order cross. A cap-cup diagram `TauCeti.capCup a b` with `a ≠ b` is
planar exactly when `a` and `b` are adjacent (`TauCeti.BrauerDiagram.isPlanar_capCup_iff`),
since a strand starting strictly between them crosses the cap.

## Main definitions

* `TauCeti.BrauerDiagram.IsPlanar`: no two arcs interleave in the counterclockwise numbering.
* `TauCeti.PlanarMatching.brauerDiagramEquiv k`: planar matchings of `k + k` points are planar
  Brauer diagrams on `k` strands.
* `TauCeti.TLDiagram.toBrauerDiagram`: the Brauer diagram underlying a Temperley–Lieb diagram
  `k → k`.

## Main results

* `TauCeti.BrauerDiagram.isPlanar_iff`: planarity in terms of the arcs of the diagram.
* `TauCeti.TLDiagram.toBrauerDiagram_eq_toBrauerDiagram_iff`,
  `TauCeti.TLDiagram.exists_toBrauerDiagram_eq_iff`:
  the comparison is injective on matchings, with image the planar Brauer diagrams.
* `TauCeti.BrauerDiagram.card_isPlanar`: there are `catalan k` planar Brauer diagrams on `k`
  strands.
* `TauCeti.BrauerDiagram.IsPlanar.composeDiagram`: the composite of two planar Brauer diagrams is
  planar.
* `TauCeti.TLDiagram.toBrauerDiagram_id`, `TauCeti.TLDiagram.toBrauerDiagram_verticalReflect`,
  `TauCeti.TLDiagram.toBrauerDiagram_reflect`: the comparison carries the identity and the two
  reflections to their Brauer counterparts.
* `TauCeti.BrauerDiagram.isPlanar_permToBrauer_iff`, `TauCeti.BrauerDiagram.isPlanar_capCup_iff`:
  the planar permutation diagrams and the planar cap-cup diagrams.

## References

* T. Halverson, A. Ram, *Partition algebras*, European J. Combin. 26 (2005), 869–921
  (the Temperley–Lieb algebra as the planar part of the Brauer algebra).
* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845.
-/

public section

open Equiv

namespace TauCeti

namespace BrauerDiagram

variable {k : ℕ}

/-! ### Planar Brauer diagrams -/

/-- A Brauer diagram is **planar** when its arcs can be drawn inside the rectangle without
crossing: numbering the boundary points counterclockwise by `TauCeti.finSumFinRevEquiv` (the
bottom row from left to right, then the top row from right to left), no two arcs interleave. -/
def IsPlanar (D : BrauerDiagram k) : Prop :=
  (PerfectMatching.congr (finSumFinRevEquiv k k (k + k) rfl) D).val.IsNoncrossingMatching

instance (D : BrauerDiagram k) : Decidable D.IsPlanar :=
  inferInstanceAs (Decidable
    (PerfectMatching.congr (finSumFinRevEquiv k k (k + k) rfl) D).val.IsNoncrossingMatching)

/-- **Planarity on the arcs**: a Brauer diagram is planar when there are no two arcs
`{x, D x}` and `{y, D y}` whose endpoints come in the counterclockwise order
`x < y < D x < D y`. -/
theorem isPlanar_iff {D : BrauerDiagram k} :
    D.IsPlanar ↔ ∀ ⦃x y : Fin k ⊕ Fin k⦄,
      finSumFinRevEquiv k k (k + k) rfl x < finSumFinRevEquiv k k (k + k) rfl y →
      finSumFinRevEquiv k k (k + k) rfl y < finSumFinRevEquiv k k (k + k) rfl (D.val x) →
      ¬ finSumFinRevEquiv k k (k + k) rfl (D.val x) <
        finSumFinRevEquiv k k (k + k) rfl (D.val y) := by
  rw [IsPlanar, Perm.isNoncrossingMatching_iff]
  simp only [PerfectMatching.congr_val_apply]
  refine ⟨fun h x y => ?_, fun h a b => ?_⟩
  · simpa using @h (finSumFinRevEquiv k k (k + k) rfl x) (finSumFinRevEquiv k k (k + k) rfl y)
  · simpa using @h ((finSumFinRevEquiv k k (k + k) rfl).symm a)
      ((finSumFinRevEquiv k k (k + k) rfl).symm b)

/-- A Brauer diagram fails to be planar exactly when two of its arcs interleave in the
counterclockwise numbering. -/
theorem not_isPlanar_iff {D : BrauerDiagram k} :
    ¬ D.IsPlanar ↔ ∃ x y : Fin k ⊕ Fin k,
      finSumFinRevEquiv k k (k + k) rfl x < finSumFinRevEquiv k k (k + k) rfl y ∧
      finSumFinRevEquiv k k (k + k) rfl y < finSumFinRevEquiv k k (k + k) rfl (D.val x) ∧
      finSumFinRevEquiv k k (k + k) rfl (D.val x) <
        finSumFinRevEquiv k k (k + k) rfl (D.val y) := by
  simp only [isPlanar_iff, not_forall, not_not, exists_prop]

end BrauerDiagram

/-! ### Planar matchings are planar Brauer diagrams -/

namespace PlanarMatching

open BrauerDiagram

/-- **Planar matchings of `k + k` points are planar Brauer diagrams on `k` strands**: transport
from the counterclockwise numbering of the boundary to the bottom and top rows, along the inverse
of `TauCeti.finSumFinRevEquiv`. -/
def brauerDiagramEquiv (k : ℕ) :
    PlanarMatching (k + k) ≃ {D : BrauerDiagram k // D.IsPlanar} :=
  (PerfectMatching.congr (finSumFinRevEquiv k k (k + k) rfl).symm).subtypeEquiv fun D => by
    rw [IsPlanar, ← PerfectMatching.congr_symm, Equiv.apply_symm_apply]

@[simp]
theorem coe_brauerDiagramEquiv_apply {k : ℕ} (x : PlanarMatching (k + k)) :
    (brauerDiagramEquiv k x : BrauerDiagram k) =
      PerfectMatching.congr (finSumFinRevEquiv k k (k + k) rfl).symm x.1 :=
  (rfl)

@[simp]
theorem coe_brauerDiagramEquiv_symm_apply {k : ℕ} (D : {D : BrauerDiagram k // D.IsPlanar}) :
    ((brauerDiagramEquiv k).symm D : PerfectMatching (Fin (k + k))) =
      PerfectMatching.congr (finSumFinRevEquiv k k (k + k) rfl) D.1 := by
  simp [brauerDiagramEquiv]

end PlanarMatching

namespace BrauerDiagram

/-- **There are `catalan k` planar Brauer diagrams on `k` strands**, as many as planar
matchings of `2k` points. -/
theorem card_isPlanar (k : ℕ) : Fintype.card {D : BrauerDiagram k // D.IsPlanar} = catalan k := by
  rw [← Fintype.card_congr (PlanarMatching.brauerDiagramEquiv k), ← Nat.card_eq_fintype_card]
  exact PerfectMatching.card_isNoncrossingMatching_eq_catalan (by simp [two_mul])

/-- Two Brauer diagrams are equal when they join the same positions of the counterclockwise
numbering. -/
private theorem ext_finSumFinRevEquiv {D D' : BrauerDiagram k}
    (h : ∀ y, finSumFinRevEquiv k k (k + k) rfl (D.val y) =
      finSumFinRevEquiv k k (k + k) rfl (D'.val y)) : D = D' :=
  Subtype.ext (Equiv.ext fun y => (finSumFinRevEquiv k k (k + k) rfl).injective (h y))

end BrauerDiagram

/-! ### The Brauer diagram of a Temperley–Lieb diagram -/

namespace TLDiagram

open BrauerDiagram

variable {n : ℕ}

/-- **The Brauer diagram of a Temperley–Lieb diagram** `n → n`: its matching, transported from
the counterclockwise numbering of the boundary to the bottom and top rows. The closed circles
are forgotten. -/
def toBrauerDiagram (x : TLDiagram n n) : BrauerDiagram n :=
  PlanarMatching.brauerDiagramEquiv n x.matching

/-- The Brauer diagram of `x` joins two boundary points exactly when `x` joins their positions
in the counterclockwise numbering. -/
@[simp]
theorem finSumFinRevEquiv_toBrauerDiagram_val (x : TLDiagram n n) (y : Fin n ⊕ Fin n) :
    finSumFinRevEquiv n n (n + n) rfl (x.toBrauerDiagram.val y) =
      x.matching.1.val (finSumFinRevEquiv n n (n + n) rfl y) := by
  rw [toBrauerDiagram, PlanarMatching.coe_brauerDiagramEquiv_apply,
    PerfectMatching.congr_val_apply, Equiv.symm_symm, Equiv.apply_symm_apply]

/-- The Brauer diagram of a Temperley–Lieb diagram is planar. -/
@[simp]
theorem isPlanar_toBrauerDiagram (x : TLDiagram n n) : x.toBrauerDiagram.IsPlanar :=
  (PlanarMatching.brauerDiagramEquiv n x.matching).2

/-- **The comparison is injective on matchings**: two Temperley–Lieb diagrams `n → n` have the
same Brauer diagram exactly when they have the same matching. -/
@[simp]
theorem toBrauerDiagram_eq_toBrauerDiagram_iff {x y : TLDiagram n n} :
    x.toBrauerDiagram = y.toBrauerDiagram ↔ x.matching = y.matching := by
  rw [toBrauerDiagram, toBrauerDiagram, ← Subtype.ext_iff, Equiv.apply_eq_iff_eq]

/-- **The image of the comparison is the planar Brauer diagrams**. -/
theorem exists_toBrauerDiagram_eq_iff {D : BrauerDiagram n} :
    (∃ x : TLDiagram n n, x.toBrauerDiagram = D) ↔ D.IsPlanar := by
  refine ⟨fun ⟨x, hx⟩ => hx ▸ x.isPlanar_toBrauerDiagram, fun hD => ?_⟩
  exact ⟨⟨(PlanarMatching.brauerDiagramEquiv n).symm ⟨D, hD⟩, 0⟩, by simp [toBrauerDiagram]⟩

/-- The identity diagram has the identity permutation diagram as its Brauer diagram. -/
@[simp]
theorem toBrauerDiagram_id (n : ℕ) : (id n).toBrauerDiagram = permToBrauer 1 := by
  refine ext_finSumFinRevEquiv fun y => ?_
  rw [finSumFinRevEquiv_toBrauerDiagram_val, id_matching_val, Fin.revPerm_apply,
    ← finSumFinRevEquiv_swap]
  rcases y with i | j <;> simp [Equiv.Perm.one_def]

/-- **Vertical reflection is the reflection `TauCeti.BrauerDiagram.flip`** of Brauer diagrams. -/
@[simp]
theorem toBrauerDiagram_verticalReflect (x : TLDiagram n n) :
    (verticalReflect n n x).toBrauerDiagram = x.toBrauerDiagram.flip := by
  refine ext_finSumFinRevEquiv fun y => ?_
  rw [finSumFinRevEquiv_toBrauerDiagram_val, flip_val, finSumFinRevEquiv_swap,
    finSumFinRevEquiv_toBrauerDiagram_val, finSumFinRevEquiv_swap]
  simp

/-- **Horizontal reflection relabels both rows by `Fin.rev`**: the mirror image of a diagram in
the vertical axis of the rectangle. -/
@[simp]
theorem toBrauerDiagram_reflect (x : TLDiagram n n) :
    (reflect n n x).toBrauerDiagram = x.toBrauerDiagram.relabel Fin.revPerm Fin.revPerm := by
  have hrev : ⇑(Fin.revPerm : Perm (Fin n)) = Fin.rev := funext Fin.revPerm_apply
  refine ext_finSumFinRevEquiv fun y => ?_
  obtain ⟨y, rfl⟩ : ∃ y', Sum.map Fin.revPerm Fin.revPerm y' = y :=
    ⟨Sum.map Fin.revPerm Fin.revPerm y, by rcases y with i | j <;> simp⟩
  rw [relabel_val_map, hrev, finSumFinRevEquiv_toBrauerDiagram_val, finSumFinRevEquiv_map_rev,
    finSumFinRevEquiv_map_rev, finSumFinRevEquiv_toBrauerDiagram_val]
  simp only [matching_reflect, PlanarMatching.coe_rotate_pow_apply,
    PlanarMatching.coe_reflect_apply, PerfectMatching.congr_trans]
  exact PerfectMatching.congr_val_apply_apply _ _ _

end TLDiagram

/-! ### Planar permutation diagrams and planar cap-cup diagrams -/

namespace BrauerDiagram

/-- **The only planar permutation diagram is the identity**: if `σ` moves some point then it
reverses the order of two points `i < i'`, and the through strands from `i` and `i'` cross. -/
@[simp]
theorem isPlanar_permToBrauer_iff {σ : Perm (Fin k)} : (permToBrauer σ).IsPlanar ↔ σ = 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra hσ
    have hmono : ¬ StrictMono σ := fun hm => hσ (Equiv.ext fun i => congrFun hm.eq_id i)
    simp only [StrictMono, not_forall] at hmono
    obtain ⟨i, i', hii', hle⟩ := hmono
    have hlt : σ i' < σ i :=
      (not_lt.mp hle).lt_of_ne fun he => hii'.ne (σ.injective he.symm)
    refine not_isPlanar_iff.mpr ⟨Sum.inl i, Sum.inl i', ?_, ?_, ?_⟩ h
    all_goals
      simp only [permToBrauer_val_inl, Fin.lt_def, finSumFinRevEquiv_inl_val,
        finSumFinRevEquiv_inr_val]
      have := (σ i).isLt
      omega
  · rintro rfl
    rw [← TLDiagram.toBrauerDiagram_id k]
    exact TLDiagram.isPlanar_toBrauerDiagram _

/-- The position, in the counterclockwise numbering, of the partner of a boundary point in a
cap-cup diagram. -/
private theorem finSumFinRevEquiv_capCup_val {a b : Fin k} (hab : a ≠ b) (x : Fin k ⊕ Fin k) :
    (finSumFinRevEquiv k k (k + k) rfl ((capCup a b).val x) : ℕ) =
      Sum.elim
        (fun i : Fin k => if (i : ℕ) = a then (b : ℕ) else if (i : ℕ) = b then (a : ℕ)
          else k + (k - 1 - i))
        (fun j : Fin k => if (j : ℕ) = a then k + (k - 1 - b) else if (j : ℕ) = b
          then k + (k - 1 - a) else (j : ℕ)) x := by
  have hab' : (a : ℕ) ≠ b := Fin.val_ne_iff.mpr hab
  rcases x with i | j
  · by_cases hia : i = a
    · subst hia
      simp [capCup_val_inl_left hab]
    by_cases hib : i = b
    · subst hib
      simp [capCup_val_inl_right hab, hab'.symm]
    simp [capCup_val_inl_of_ne hia hib, Fin.val_ne_iff.mpr hia, Fin.val_ne_iff.mpr hib]
  · by_cases hja : j = a
    · subst hja
      simp [capCup_val_inr_left hab]
    by_cases hjb : j = b
    · subst hjb
      simp [capCup_val_inr_right hab, hab'.symm]
    simp [capCup_val_inr_of_ne hja hjb, Fin.val_ne_iff.mpr hja, Fin.val_ne_iff.mpr hjb]

/-- `isPlanar_capCup_iff` for a pair `a < b`. -/
private theorem isPlanar_capCup_iff_of_lt {a b : Fin k} (hab : a < b) :
    (capCup a b).IsPlanar ↔ (a : ℕ) + 1 = b := by
  have hlt : (a : ℕ) < b := hab
  have hb := b.isLt
  rw [isPlanar_iff]
  constructor
  · -- A strand starting at a bottom point strictly between `a` and `b` crosses the cap.
    intro h
    by_contra hne
    have h1 := @h (Sum.inl a) (Sum.inl ⟨a + 1, by omega⟩)
    simp only [Fin.lt_def, finSumFinRevEquiv_capCup_val hab.ne, finSumFinRevEquiv_inl_val,
      Sum.elim_inl] at h1
    split_ifs at h1 <;> omega
  · rintro hb' (i | i) (j | j) <;>
    · have := i.isLt
      have := j.isLt
      simp only [Fin.lt_def, finSumFinRevEquiv_capCup_val hab.ne, finSumFinRevEquiv_inl_val,
        finSumFinRevEquiv_inr_val, Sum.elim_inl, Sum.elim_inr]
      split_ifs <;> omega

/-- **A cap-cup diagram is planar exactly on adjacent pairs**: for `a ≠ b`, the cap-cup diagram
on `{a, b}` is planar exactly when `a` and `b` are adjacent. Otherwise a strand starting strictly
between `a` and `b` crosses the cap. -/
@[simp]
theorem isPlanar_capCup_iff {a b : Fin k} (hab : a ≠ b) :
    (capCup a b).IsPlanar ↔ (a : ℕ) + 1 = b ∨ (b : ℕ) + 1 = a := by
  rcases hab.lt_or_gt with h | h
  · rw [isPlanar_capCup_iff_of_lt h, or_iff_left (by have : (a : ℕ) < b := h; omega)]
  · rw [← capCup_comm, isPlanar_capCup_iff_of_lt h,
      or_iff_right (by have : (b : ℕ) < a := h; omega)]

end BrauerDiagram

/-! ### Stacking planar diagrams

The composite of two planar diagrams is planar. Suppose that the arc `{x, x'}` of the composite
interleaved the arc `{y, y'}`. Collect the strand from `x` to `x'` into a set `P` of points of the
two stacked diagrams, closed under the arcs of both. For a point `z` of either diagram outside
`P`, count the points of `P` of that diagram preceding `z` in its counterclockwise numbering. Since
each diagram is planar, the parity of this count is the same at both ends of each of its arcs
outside `P` (`Equiv.Perm.IsNoncrossingMatching.card_filter_lt_apply_modEq`), and at a middle
point the counts in the two diagrams add up to a number depending on `P` alone. So, suitably
normalised, the parity is constant along the strand from `y` to `y'`, which avoids `P`. On the
outer boundary it counts the points of `{x, x'}` preceding a point, which is odd at `y` and even
at `y'`. -/

namespace BrauerDiagram

open Finset Relation

/-- The number of points of `s` preceding the boundary point `z` in the counterclockwise
numbering. -/
private def countBefore (s : Finset (Fin k ⊕ Fin k)) (z : Fin k ⊕ Fin k) : ℕ :=
  {x ∈ s | finSumFinRevEquiv k k (k + k) rfl x < finSumFinRevEquiv k k (k + k) rfl z}.card

/-- Count separately the points of the bottom and of the top row preceding `z`. -/
private theorem countBefore_eq (s : Finset (Fin k ⊕ Fin k)) (z : Fin k ⊕ Fin k) :
    countBefore s z =
      {i ∈ s.toLeft | finSumFinRevEquiv k k (k + k) rfl (Sum.inl i) <
          finSumFinRevEquiv k k (k + k) rfl z}.card +
        {j ∈ s.toRight | finSumFinRevEquiv k k (k + k) rfl (Sum.inr j) <
          finSumFinRevEquiv k k (k + k) rfl z}.card := by
  rw [countBefore, ← card_toLeft_add_card_toRight, toLeft_filter, toRight_filter]

/-- In a planar diagram, the parity of the number of points of a union `s` of arcs preceding a
point is the same at both ends of an arc outside `s`. -/
private theorem IsPlanar.countBefore_val_mod_two {D : BrauerDiagram k} (hD : D.IsPlanar)
    {s : Finset (Fin k ⊕ Fin k)} (hs : ∀ x ∈ s, D.val x ∈ s) {z : Fin k ⊕ Fin k} (hz : z ∉ s) :
    countBefore s (D.val z) % 2 = countBefore s z % 2 := by
  set e := finSumFinRevEquiv k k (k + k) rfl
  rw [IsPlanar] at hD
  have key := hD.card_filter_lt_apply_modEq (PerfectMatching.congr e D).prop
    (s := s.map e.toEmbedding) (a := e z)
    (fun y hy => by
      rw [mem_map_equiv] at hy ⊢
      rw [PerfectMatching.congr_val_apply, Equiv.symm_apply_apply]
      exact hs _ hy)
    (by rwa [mem_map_equiv, Equiv.symm_apply_apply])
  rw [PerfectMatching.congr_val_apply_apply, filter_map, filter_map, card_map, card_map] at key
  exact key

/-- A point outside a union of arcs is matched with a point outside it. -/
private theorem val_notMem {D : BrauerDiagram k} {s : Finset (Fin k ⊕ Fin k)}
    (hs : ∀ x ∈ s, D.val x ∈ s) {z : Fin k ⊕ Fin k} (hz : z ∉ s) : D.val z ∉ s :=
  fun h => hz (D.apply_apply z ▸ hs _ h)

variable {X : Finset (Fin k ⊕ Fin k)} {M : Finset (Fin k)}

/-- At a middle point `a` outside `M`, the points of the lower diagram preceding `a` are the
bottom points in `X` and the middle points of `M` to the right of `a`, and the points of the upper
diagram preceding `a` are the middle points of `M` to the left of `a`. -/
private theorem countBefore_disjSum_add_countBefore_disjSum {a : Fin k} (ha : a ∉ M) :
    countBefore (X.toLeft.disjSum M) (Sum.inr a) + countBefore (M.disjSum X.toRight) (Sum.inl a) =
      X.toLeft.card + M.card := by
  have hsplit := card_filter_add_card_filter_not (s := M) (a < ·)
  have hcongr : {b ∈ M | ¬a < b} = {b ∈ M | b < a} := filter_congr fun b hb => by
    rw [not_lt]
    exact ⟨fun h => h.lt_of_ne (ne_of_mem_of_not_mem hb ha), le_of_lt⟩
  rw [hcongr] at hsplit
  simp [countBefore_eq]
  omega

/-- The normalised count along a strand avoiding the union of strands, at an outer point: the
count in the lower diagram at a bottom point, and the count in the upper diagram, shifted by a
number depending only on `X` and `M`, at a top point. -/
private def outerCount (X : Finset (Fin k ⊕ Fin k)) (M : Finset (Fin k)) (y : Fin k ⊕ Fin k) :
    ℕ :=
  Sum.elim (fun i => countBefore (X.toLeft.disjSum M) (Sum.inl i))
    (fun j => countBefore (M.disjSum X.toRight) (Sum.inr j) +
      (X.toLeft.card + M.card)) y

/-- The normalised count at a middle point: the count in the lower diagram. -/
private def middleCount (X : Finset (Fin k ⊕ Fin k)) (M : Finset (Fin k)) (a : Fin k) : ℕ :=
  countBefore (X.toLeft.disjSum M) (Sum.inr a)

/-- On the outer boundary, the normalised count is the number of points of `X` preceding the
point, modulo `2`. -/
private theorem outerCount_mod_two (y : Fin k ⊕ Fin k) :
    outerCount X M y % 2 = countBefore X y % 2 := by
  rcases y with i | j
  · simp [outerCount, countBefore_eq]
  · simp [outerCount, countBefore_eq]
    omega

variable (D₁ D₂ : BrauerDiagram k)

open Classical in
/-- The middle points of the strand of the stack of `D₁` above `D₂` that starts at the outer
point `w`. -/
private noncomputable def strandMiddle (w : Fin k ⊕ Fin k) : Finset (Fin k) :=
  {a | ∃ s t, stackStart D₁ D₂ w = Sum.inr s ∧
    ReflTransGen (fun u v => stackStep D₁ D₂ u = Sum.inr v) s t ∧ middlePoint t = a}

variable {D₁ D₂}

private theorem mem_strandMiddle {w : Fin k ⊕ Fin k} {a : Fin k} :
    a ∈ strandMiddle D₁ D₂ w ↔ ∃ s t, stackStart D₁ D₂ w = Sum.inr s ∧
      ReflTransGen (fun u v => stackStep D₁ D₂ u = Sum.inr v) s t ∧ middlePoint t = a := by
  simp [strandMiddle]

/-- The middle point of each middle state reached by the strand from `w` is on it. -/
private theorem middlePoint_mem_strandMiddle {w s t : Fin k ⊕ Fin k}
    (hs : stackStart D₁ D₂ w = Sum.inr s)
    (hst : ReflTransGen (fun u v => stackStep D₁ D₂ u = Sum.inr v) s t) :
    middlePoint t ∈ strandMiddle D₁ D₂ w :=
  mem_strandMiddle.mpr ⟨s, t, hs, hst, rfl⟩

/-- The lower diagram matches the bottom end `w` of a strand with a point of that strand. -/
private theorem lower_val_inl_mem {w : Fin k ⊕ Fin k}
    (hw' : (composeDiagram D₁ D₂).val w ∈ X) (hM : strandMiddle D₁ D₂ w ⊆ M) {i : Fin k}
    (hi : Sum.inl i = w) : D₂.val (Sum.inl i) ∈ X.toLeft.disjSum M := by
  subst hi
  rcases h : D₂.val (Sum.inl i) with i' | a
  · have hstart : stackStart D₁ D₂ (Sum.inl i) = Sum.inl (Sum.inl i') := by simp [h]
    rw [inl_mem_disjSum, mem_toLeft, ← (composeDiagram_val_eq_iff D₁ D₂).mpr (Or.inl hstart)]
    exact hw'
  · have hstart : stackStart D₁ D₂ (Sum.inl i) = Sum.inr (Sum.inl a) := by simp [h]
    exact inr_mem_disjSum.mpr (hM (by simpa using middlePoint_mem_strandMiddle hstart .refl))

/-- The lower diagram matches a middle point of a strand with a point of that strand. -/
private theorem lower_val_inr_mem {w : Fin k ⊕ Fin k} (hw : w ∈ X)
    (hw' : (composeDiagram D₁ D₂).val w ∈ X) (hM : strandMiddle D₁ D₂ w ⊆ M) {a : Fin k}
    (ha : a ∈ strandMiddle D₁ D₂ w) : D₂.val (Sum.inr a) ∈ X.toLeft.disjSum M := by
  obtain ⟨s, t, hs, hst, hta⟩ := mem_strandMiddle.mp ha
  rcases t with b | b <;> simp only [middlePoint_inl, middlePoint_inr] at hta <;> subst hta
  · -- The strand reached `b` coming up through `D₂`: from `w` itself, or along a cup of `D₂`.
    rcases hst.cases_tail with rfl | ⟨u, hsu, hu⟩
    · obtain ⟨hl, he⟩ := stackStart_eq_inr_inl_iff.mp hs
      rcases w with i | j
      · rw [he]
        simpa using hw
      · simp at hl
    · obtain ⟨c, rfl, hc⟩ := stackStep_eq_inr_inl_iff.mp hu
      rw [hc, inr_mem_disjSum]
      exact hM (by simpa using middlePoint_mem_strandMiddle hs hsu)
  · -- The strand leaves `b` going down through `D₂`: out of the stack, or along a cup of `D₂`.
    rcases h : D₂.val (Sum.inr b) with i | c
    · have hstep : stackStep D₁ D₂ (Sum.inr b) = Sum.inl (Sum.inl i) := by simp [h]
      rw [inl_mem_disjSum, mem_toLeft,
        ← (composeDiagram_val_eq_iff D₁ D₂).mpr (Or.inr ⟨s, _, hs, hst, hstep⟩)]
      exact hw'
    · have hstep : stackStep D₁ D₂ (Sum.inr b) = Sum.inr (Sum.inl c) := by simp [h]
      exact inr_mem_disjSum.mpr
        (hM (by simpa using middlePoint_mem_strandMiddle hs (hst.tail hstep)))

/-- The upper diagram matches the top end `w` of a strand with a point of that strand. -/
private theorem upper_val_inr_mem {w : Fin k ⊕ Fin k}
    (hw' : (composeDiagram D₁ D₂).val w ∈ X) (hM : strandMiddle D₁ D₂ w ⊆ M) {j : Fin k}
    (hj : Sum.inr j = w) : D₁.val (Sum.inr j) ∈ M.disjSum X.toRight := by
  subst hj
  rcases h : D₁.val (Sum.inr j) with a | j'
  · have hstart : stackStart D₁ D₂ (Sum.inr j) = Sum.inr (Sum.inr a) := by simp [h]
    exact inl_mem_disjSum.mpr (hM (by simpa using middlePoint_mem_strandMiddle hstart .refl))
  · have hstart : stackStart D₁ D₂ (Sum.inr j) = Sum.inl (Sum.inr j') := by simp [h]
    rw [inr_mem_disjSum, mem_toRight, ← (composeDiagram_val_eq_iff D₁ D₂).mpr (Or.inl hstart)]
    exact hw'

/-- The upper diagram matches a middle point of a strand with a point of that strand. -/
private theorem upper_val_inl_mem {w : Fin k ⊕ Fin k} (hw : w ∈ X)
    (hw' : (composeDiagram D₁ D₂).val w ∈ X) (hM : strandMiddle D₁ D₂ w ⊆ M) {a : Fin k}
    (ha : a ∈ strandMiddle D₁ D₂ w) : D₁.val (Sum.inl a) ∈ M.disjSum X.toRight := by
  obtain ⟨s, t, hs, hst, hta⟩ := mem_strandMiddle.mp ha
  rcases t with b | b <;> simp only [middlePoint_inl, middlePoint_inr] at hta <;> subst hta
  · -- The strand leaves `b` going up through `D₁`: out of the stack, or along a cap of `D₁`.
    rcases h : D₁.val (Sum.inl b) with c | j
    · have hstep : stackStep D₁ D₂ (Sum.inl b) = Sum.inr (Sum.inr c) := by simp [h]
      exact inl_mem_disjSum.mpr
        (hM (by simpa using middlePoint_mem_strandMiddle hs (hst.tail hstep)))
    · have hstep : stackStep D₁ D₂ (Sum.inl b) = Sum.inl (Sum.inr j) := by simp [h]
      rw [inr_mem_disjSum, mem_toRight,
        ← (composeDiagram_val_eq_iff D₁ D₂).mpr (Or.inr ⟨s, _, hs, hst, hstep⟩)]
      exact hw'
  · -- The strand reached `b` coming down through `D₁`: from `w` itself, or along a cap of `D₁`.
    rcases hst.cases_tail with rfl | ⟨u, hsu, hu⟩
    · obtain ⟨hr, he⟩ := stackStart_eq_inr_inr_iff.mp hs
      rcases w with i | j
      · simp at hr
      · rw [he]
        simpa using hw
    · obtain ⟨c, rfl, hc⟩ := stackStep_eq_inr_inr_iff.mp hu
      rw [hc, inl_mem_disjSum]
      exact hM (by simpa using middlePoint_mem_strandMiddle hs hsu)

/-- A union of strands, given by outer points `X` closed under the composite and middle points
`M` lying exactly on the strands from `X`, is closed under the lower diagram. -/
private theorem lower_mapsTo
    (hX : ∀ w ∈ X, (composeDiagram D₁ D₂).val w ∈ X ∧ strandMiddle D₁ D₂ w ⊆ M)
    (hM : ∀ a ∈ M, ∃ w ∈ X, a ∈ strandMiddle D₁ D₂ w) :
    ∀ z ∈ X.toLeft.disjSum M, D₂.val z ∈ X.toLeft.disjSum M := by
  rintro (i | a) hz
  · rw [inl_mem_disjSum, mem_toLeft] at hz
    exact lower_val_inl_mem (hX _ hz).1 (hX _ hz).2 rfl
  · obtain ⟨w, hw, ha⟩ := hM a (inr_mem_disjSum.mp hz)
    exact lower_val_inr_mem hw (hX w hw).1 (hX w hw).2 ha

/-- A union of strands, given by outer points `X` closed under the composite and middle points
`M` lying exactly on the strands from `X`, is closed under the upper diagram. -/
private theorem upper_mapsTo
    (hX : ∀ w ∈ X, (composeDiagram D₁ D₂).val w ∈ X ∧ strandMiddle D₁ D₂ w ⊆ M)
    (hM : ∀ a ∈ M, ∃ w ∈ X, a ∈ strandMiddle D₁ D₂ w) :
    ∀ z ∈ M.disjSum X.toRight, D₁.val z ∈ M.disjSum X.toRight := by
  rintro (a | j) hz
  · obtain ⟨w, hw, ha⟩ := hM a (inl_mem_disjSum.mp hz)
    exact upper_val_inl_mem hw (hX w hw).1 (hX w hw).2 ha
  · rw [inr_mem_disjSum, mem_toRight] at hz
    exact upper_val_inr_mem (hX _ hz).1 (hX _ hz).2 rfl

section Parity

variable (h₁ : D₁.IsPlanar) (h₂ : D₂.IsPlanar)
  (hlow : ∀ z ∈ X.toLeft.disjSum M, D₂.val z ∈ X.toLeft.disjSum M)
  (hup : ∀ z ∈ M.disjSum X.toRight, D₁.val z ∈ M.disjSum X.toRight)
include h₁ h₂ hlow hup

/-- A strand outside the union of strands that leaves the stack along its first arc keeps the
normalised count modulo `2`. -/
private theorem outerCount_mod_two_of_stackStart_eq_inl {y y' : Fin k ⊕ Fin k} (hy : y ∉ X)
    (h : stackStart D₁ D₂ y = Sum.inl y') : outerCount X M y' % 2 = outerCount X M y % 2 := by
  rcases y with i | j
  · rcases hD : D₂.val (Sum.inl i) with i' | a <;>
      simp only [stackStart_inl, hD, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq,
        reduceCtorEq] at h
    subst h
    have hpar := h₂.countBefore_val_mod_two hlow (z := Sum.inl i) (by simpa using hy)
    rw [hD] at hpar
    simpa [outerCount] using hpar
  · rcases hD : D₁.val (Sum.inr j) with a | j' <;>
      simp only [stackStart_inr, hD, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq,
        reduceCtorEq] at h
    subst h
    have hpar := h₁.countBefore_val_mod_two hup (z := Sum.inr j) (by simpa using hy)
    rw [hD] at hpar
    simp only [outerCount, Sum.elim_inr]
    omega

/-- A strand outside the union of strands that crosses into the middle along its first arc
reaches a middle point outside `M` with the same normalised count modulo `2`. -/
private theorem middleCount_mod_two_of_stackStart_eq_inr {y s : Fin k ⊕ Fin k} (hy : y ∉ X)
    (h : stackStart D₁ D₂ y = Sum.inr s) :
    middlePoint s ∉ M ∧ middleCount X M (middlePoint s) % 2 = outerCount X M y % 2 := by
  rcases y with i | j
  · rcases hD : D₂.val (Sum.inl i) with i' | a <;>
      simp only [stackStart_inl, hD, Sum.elim_inl, Sum.elim_inr, Sum.inr.injEq,
        reduceCtorEq] at h
    subst h
    have hz : Sum.inl i ∉ X.toLeft.disjSum M := by simpa using hy
    have hpar := h₂.countBefore_val_mod_two hlow hz
    have hnot := val_notMem hlow hz
    rw [hD] at hpar hnot
    exact ⟨by simpa using hnot, by simpa [middleCount, outerCount] using hpar⟩
  · rcases hD : D₁.val (Sum.inr j) with a | j' <;>
      simp only [stackStart_inr, hD, Sum.elim_inl, Sum.elim_inr, Sum.inr.injEq,
        reduceCtorEq] at h
    subst h
    have hz : Sum.inr j ∉ M.disjSum X.toRight := by simpa using hy
    have hpar := h₁.countBefore_val_mod_two hup hz
    have hnot := val_notMem hup hz
    rw [hD] at hpar hnot
    have ha : a ∉ M := by simpa using hnot
    have hsum := countBefore_disjSum_add_countBefore_disjSum (X := X) ha
    simp only [middlePoint_inr, middleCount, outerCount, Sum.elim_inr]
    exact ⟨ha, by omega⟩

/-- A strand outside the union of strands that stays in the middle keeps the normalised count
modulo `2`. -/
private theorem middleCount_mod_two_of_stackStep_eq_inr {u v : Fin k ⊕ Fin k}
    (hu : middlePoint u ∉ M) (h : stackStep D₁ D₂ u = Sum.inr v) :
    middlePoint v ∉ M ∧ middleCount X M (middlePoint v) % 2 = middleCount X M (middlePoint u) % 2
    := by
  rcases u with a | a
  · obtain ⟨b, rfl, hD⟩ := stackStep_inl_eq_inr_iff.mp h
    simp only [middlePoint_inl, middlePoint_inr] at hu ⊢
    have hz : Sum.inl a ∉ M.disjSum X.toRight := by simpa using hu
    have hpar := h₁.countBefore_val_mod_two hup hz
    have hnot := val_notMem hup hz
    rw [hD] at hpar hnot
    have hb : b ∉ M := by simpa using hnot
    have hsa := countBefore_disjSum_add_countBefore_disjSum (X := X) hu
    have hsb := countBefore_disjSum_add_countBefore_disjSum (X := X) hb
    simp only [middleCount]
    exact ⟨hb, by omega⟩
  · obtain ⟨b, rfl, hD⟩ := stackStep_inr_eq_inr_iff.mp h
    simp only [middlePoint_inl, middlePoint_inr] at hu ⊢
    have hz : Sum.inr a ∉ X.toLeft.disjSum M := by simpa using hu
    have hpar := h₂.countBefore_val_mod_two hlow hz
    have hnot := val_notMem hlow hz
    rw [hD] at hpar hnot
    exact ⟨by simpa using hnot, hpar⟩

/-- A strand outside the union of strands that leaves the middle keeps the normalised count
modulo `2`. -/
private theorem outerCount_mod_two_of_stackStep_eq_inl {u y : Fin k ⊕ Fin k}
    (hu : middlePoint u ∉ M) (h : stackStep D₁ D₂ u = Sum.inl y) :
    outerCount X M y % 2 = middleCount X M (middlePoint u) % 2 := by
  rcases u with a | a
  · rcases hD : D₁.val (Sum.inl a) with b | j <;>
      simp only [stackStep_inl, hD, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq,
        reduceCtorEq] at h
    subst h
    simp only [middlePoint_inl] at hu
    have hpar := h₁.countBefore_val_mod_two hup (z := Sum.inl a) (by simpa using hu)
    rw [hD] at hpar
    have hsum := countBefore_disjSum_add_countBefore_disjSum (X := X) hu
    simp only [outerCount, middleCount, middlePoint_inl, Sum.elim_inr]
    omega
  · rcases hD : D₂.val (Sum.inr a) with i | b <;>
      simp only [stackStep_inr, hD, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq,
        reduceCtorEq] at h
    subst h
    simp only [middlePoint_inr] at hu
    have hpar := h₂.countBefore_val_mod_two hlow (z := Sum.inr a) (by simpa using hu)
    rw [hD] at hpar
    simpa [outerCount, middleCount] using hpar

/-- **The normalised count is constant along a strand** outside the union of strands, modulo
`2`. -/
private theorem outerCount_composeDiagram_val_mod_two {y : Fin k ⊕ Fin k} (hy : y ∉ X) :
    outerCount X M ((composeDiagram D₁ D₂).val y) % 2 = outerCount X M y % 2 := by
  rcases (composeDiagram_val_eq_iff D₁ D₂).mp rfl with h | ⟨s, t, hs, hst, ht⟩
  · exact outerCount_mod_two_of_stackStart_eq_inl h₁ h₂ hlow hup hy h
  · have key : middlePoint t ∉ M ∧
        middleCount X M (middlePoint t) % 2 = outerCount X M y % 2 := by
      clear ht
      induction hst with
      | refl => exact middleCount_mod_two_of_stackStart_eq_inr h₁ h₂ hlow hup hy hs
      | tail _ huv ih =>
        obtain ⟨hv, hcount⟩ := middleCount_mod_two_of_stackStep_eq_inr h₁ h₂ hlow hup ih.1 huv
        exact ⟨hv, hcount.trans ih.2⟩
    rw [outerCount_mod_two_of_stackStep_eq_inl h₁ h₂ hlow hup key.1 ht, key.2]

end Parity

/-- **Stacking planar diagrams gives a planar diagram**: the arcs of the composite of two planar
Brauer diagrams can again be drawn inside the rectangle without crossing. -/
theorem IsPlanar.composeDiagram (h₁ : D₁.IsPlanar) (h₂ : D₂.IsPlanar) :
    (TauCeti.composeDiagram D₁ D₂).IsPlanar := by
  rw [isPlanar_iff]
  intro x y hxy hyx hlt
  -- The strand from `x` to its partner `x'`, and the parity count it induces.
  set x' := (TauCeti.composeDiagram D₁ D₂).val x
  set X : Finset (Fin k ⊕ Fin k) := {x, x'}
  set M := strandMiddle D₁ D₂ x ∪ strandMiddle D₁ D₂ x'
  have hX : ∀ w ∈ X, (TauCeti.composeDiagram D₁ D₂).val w ∈ X ∧ strandMiddle D₁ D₂ w ⊆ M := by
    simp only [X, mem_insert, mem_singleton]
    rintro w (rfl | rfl)
    · exact ⟨Or.inr rfl, subset_union_left⟩
    · exact ⟨Or.inl ((TauCeti.composeDiagram D₁ D₂).apply_apply _), subset_union_right⟩
  have hM : ∀ a ∈ M, ∃ w ∈ X, a ∈ strandMiddle D₁ D₂ w := by
    intro a ha
    rcases mem_union.mp ha with ha | ha
    exacts [⟨x, by simp [X], ha⟩, ⟨x', by simp [X], ha⟩]
  have hy : y ∉ X := by
    simp only [X, mem_insert, mem_singleton, not_or]
    exact ⟨fun h => hxy.ne' (by rw [h]), fun h => hyx.ne (by rw [h])⟩
  have key := outerCount_composeDiagram_val_mod_two h₁ h₂ (lower_mapsTo hX hM)
    (upper_mapsTo hX hM) hy
  rw [outerCount_mod_two, outerCount_mod_two] at key
  -- Exactly one point of `{x, x'}` precedes `y`, and both precede the partner of `y`.
  have hxx' : x ≠ x' := ((TauCeti.composeDiagram D₁ D₂).apply_ne x).symm
  have hcy : countBefore X y = 1 := by
    simp [countBefore, X, filter_insert, filter_singleton, hxy, hyx.not_gt]
  have hcy' : countBefore X ((TauCeti.composeDiagram D₁ D₂).val y) = 2 := by
    simp [countBefore, X, filter_insert, filter_singleton, hxy.trans (hyx.trans hlt), hlt, hxx']
  omega

end BrauerDiagram

/-- The Temperley–Lieb generator `e₁ : 2 → 2`, the cap on the two bottom points `{0, 1}` below
the cup on the two top points `{2, 3}`, has as its Brauer diagram the cap-cup diagram on the
pair `{0, 1}`. -/
example : (⟨⟨⟨swap 0 1 * swap 2 3, by decide⟩, by decide⟩, 0⟩ : TLDiagram 2 2).toBrauerDiagram =
    capCup 0 1 := by
  have e0 : finSumFinRevEquiv 2 2 (2 + 2) rfl (Sum.inl 0) = 0 := Fin.ext (by simp)
  have e1 : finSumFinRevEquiv 2 2 (2 + 2) rfl (Sum.inl 1) = 1 := Fin.ext (by simp)
  have e2 : finSumFinRevEquiv 2 2 (2 + 2) rfl (Sum.inr 1) = 2 := Fin.ext (by simp)
  have e3 : finSumFinRevEquiv 2 2 (2 + 2) rfl (Sum.inr 0) = 3 := Fin.ext (by simp)
  refine (eq_capCup_iff (by decide)).mpr ⟨?_, ?_, fun i h0 h1 => by fin_cases i <;> simp_all⟩ <;>
  · refine (finSumFinRevEquiv 2 2 (2 + 2) rfl).injective ?_
    rw [TLDiagram.finSumFinRevEquiv_toBrauerDiagram_val]
    simp only [e0, e1, e2, e3]
    decide

/-- The crossing on two strands is a Brauer diagram that is not planar, so it is the Brauer
diagram of no Temperley–Lieb diagram. -/
example : ¬ ∃ x : TLDiagram 2 2, x.toBrauerDiagram = permToBrauer (swap 0 1) := by
  rw [TLDiagram.exists_toBrauerDiagram_eq_iff, BrauerDiagram.isPlanar_permToBrauer_iff]
  decide

end TauCeti
