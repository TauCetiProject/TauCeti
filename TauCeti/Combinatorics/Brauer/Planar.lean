/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Brauer.Generator
public import TauCeti.Combinatorics.NoncrossingPartition.PerfectMatching
public import TauCeti.Combinatorics.PlanarMatching.TLDiagram
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
