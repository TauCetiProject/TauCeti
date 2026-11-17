/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.Compose
public import TauCeti.Combinatorics.PlanarMatching.Through
import all TauCeti.Combinatorics.PlanarMatching.Glue
import all TauCeti.Combinatorics.PlanarMatching.Associativity

/-!
# Inserting adjacent arcs in planar matchings and Temperley–Lieb diagrams

Inductive arguments on Temperley–Lieb diagrams peel off an innermost boundary arc — an arc joining
two consecutive points on the top or bottom boundary — and re-insert it by composing with an
elementary cup or cap. At the level of planar matchings, `TauCeti.PlanarMatching.insertArc` inserts
an arc `{a.castSucc, a.succ}` while shifting all boundary points from `a` onwards up by two, giving
a right inverse to `TauCeti.PlanarMatching.contract`. Lifting `insertArc` to diagrams defines
`TauCeti.TLDiagram.insertTopArc`, `TauCeti.TLDiagram.insertBottomArc`, and the elementary generators
`TauCeti.TLDiagram.cupAt` and `TauCeti.TLDiagram.capAt`.

Because a newly inserted top arc lies away from the middle boundary where composition contracts
pairs, post-composing with `cupAt c` simply inserts a top arc at `c` without changing the closed
circles, the through-strand count, or the bottom half-diagram. Conversely, any diagram whose top
half-diagram joins `c.castSucc` to `c.succ` factors through `cupAt c` on the right; dual results
for `insertBottomArc` and `capAt c` follow by vertical reflection. Finally,
`TauCeti.TLDiagram.cupAt_comp_capAt` shows that `cupAt c` followed by `capAt c` closes one circle
and leaves `q` straight strands.

## Main definitions

* `TauCeti.PlanarMatching.insertArc`: insert an adjacent arc `{a.castSucc, a.succ}` into a planar
  matching, right inverse to `TauCeti.PlanarMatching.contract`.
* `TauCeti.TLDiagram.insertTopArc`, `TauCeti.TLDiagram.insertBottomArc`: insert an adjacent arc on
  the top or bottom boundary of a diagram.
* `TauCeti.TLDiagram.cupAt`, `TauCeti.TLDiagram.capAt`: elementary cup `q → q + 2` and cap
  `q + 2 → q` at position `c : Fin (q + 1)`.

## Main results

* `TauCeti.PlanarMatching.contract_insertArc`, `TauCeti.PlanarMatching.insertArc_contract`:
  `insertArc` is right inverse to `contract`, and left inverse when `{a.castSucc, a.succ}` is an
  arc.
* `TauCeti.TLDiagram.comp_insertTopArc`, `TauCeti.TLDiagram.insertBottomArc_comp`,
  `TauCeti.TLDiagram.comp_cupAt`, `TauCeti.TLDiagram.capAt_comp`: compatibility of composition with
  boundary arc insertion.
* `TauCeti.TLDiagram.exists_comp_cupAt_of_topHalf_apply_eq`,
  `TauCeti.TLDiagram.exists_capAt_comp_of_bottomHalf_apply_eq`: peeling an adjacent top or bottom
  arc as a `cupAt` or `capAt` factor.
* `TauCeti.TLDiagram.cupAt_comp_capAt`: `cupAt c` composed with `capAt c` is the identity matching
  with one closed circle.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845.
* D. Ridout and Y. Saint-Aubin, *Standard modules, induction and the structure of the
  Temperley–Lieb algebra*, arXiv:1204.4505.
-/

public section

open Equiv Finset

namespace TauCeti

/-! ### Inserting an adjacent arc in a planar matching -/

namespace PlanarMatching

section InsertArc

variable {k : ℕ}

private def skipEquiv (a : Fin (k + 1)) :
    Fin k ≃ {y : Fin (k + 2) // y ≠ a.castSucc ∧ y ≠ a.succ} where
  toFun i := ⟨skip a i, skip_ne_castSucc a i, skip_ne_succ a i⟩
  invFun y := unskip a y.1 y.2
  left_inv i := (skip_strictMono a).injective
    (skip_unskip a (skip a i) ⟨skip_ne_castSucc a i, skip_ne_succ a i⟩)
  right_inv y := Subtype.ext (skip_unskip a y.1 y.2)

private abbrev insertArcPM (x : PlanarMatching k) (a : Fin (k + 1)) :
    PerfectMatching (Fin (k + 2)) :=
  PerfectMatching.extend (succ_ne_castSucc a).symm (PerfectMatching.congr (skipEquiv a) x.1)

private theorem insertArcPM_skip (x : PlanarMatching k) (a : Fin (k + 1)) (i : Fin k) :
    (insertArcPM x a).val (skip a i) = skip a (x.1.val i) := by
  rw [insertArcPM,
    PerfectMatching.extend_apply_of_mem _ _ ⟨skip_ne_castSucc a i, skip_ne_succ a i⟩]
  exact congrArg Subtype.val (PerfectMatching.congr_val_apply_apply (skipEquiv a) x.1 i)

private theorem insertArcPM_noncrossing (x : PlanarMatching k) (a : Fin (k + 1)) :
    (insertArcPM x a).val.IsNoncrossingMatching := by
  have hno : ∀ p q, p < q → q < (insertArcPM x a).val p →
      p ≠ a.castSucc ∧ p ≠ a.succ := by
    rintro p q hpq hqp
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, insertArcPM, PerfectMatching.extend_apply_left] at hqp; rw [h] at hpq
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at hpq hqp; omega
    · rw [h, insertArcPM, PerfectMatching.extend_apply_right] at hqp; rw [h] at hpq
      exact absurd (hpq.trans hqp) (not_lt_of_gt Fin.castSucc_lt_succ)
  rw [Perm.isNoncrossingMatching_iff]
  intro u v huv hvu hlt
  have hu := hno u v huv hvu
  have hv := hno v ((insertArcPM x a).val u) hvu hlt
  rw [← skip_unskip a u hu, ← skip_unskip a v hv] at huv hvu hlt
  simp only [insertArcPM_skip] at hvu hlt
  exact Perm.isNoncrossingMatching_iff.mp x.2 ((skip_strictMono a).lt_iff_lt.mp huv)
    ((skip_strictMono a).lt_iff_lt.mp hvu) ((skip_strictMono a).lt_iff_lt.mp hlt)

/-- **Inserting an adjacent arc** `{a.castSucc, a.succ}` into a planar matching `x` of `k` points,
shifting all boundary points from `a` onwards up by two. It is a right inverse to
`TauCeti.PlanarMatching.contract`. -/
def insertArc (x : PlanarMatching k) (a : Fin (k + 1)) : PlanarMatching (k + 2) :=
  ⟨insertArcPM x a, insertArcPM_noncrossing x a⟩

@[simp] theorem insertArc_val_castSucc (x : PlanarMatching k) (a : Fin (k + 1)) :
    (x.insertArc a).1.val a.castSucc = a.succ :=
  PerfectMatching.extend_apply_left (succ_ne_castSucc a).symm _

@[simp] theorem insertArc_val_succ (x : PlanarMatching k) (a : Fin (k + 1)) :
    (x.insertArc a).1.val a.succ = a.castSucc :=
  PerfectMatching.extend_apply_right (succ_ne_castSucc a).symm _

/-- Outside the inserted arc, `insertArc` acts on boundary points as the original planar matching
conjugated by skipping the two inserted positions. -/
@[simp] theorem insertArc_val_succAbove_succAbove (x : PlanarMatching k) (a : Fin (k + 1))
    (i : Fin k) :
    (x.insertArc a).1.val (a.castSucc.succAbove (a.succAbove i)) =
      a.castSucc.succAbove (a.succAbove (x.1.val i)) :=
  insertArcPM_skip x a i

private theorem pv_insertArc (x : PlanarMatching k) (a : Fin (k + 1)) {q : ℕ} (hq : q < k + 2) :
    pv (x.insertArc a) q =
      if q = (a : ℕ) then (a : ℕ) + 1
      else if q = (a : ℕ) + 1 then (a : ℕ)
      else skipN a (pv x (unskipN a q)) := by
  by_cases h₁ : q = a
  · subst h₁; rw [← Fin.val_castSucc a, pv_coe, insertArc_val_castSucc]; simp
  by_cases h₂ : q = (a : ℕ) + 1
  · subst h₂; rw [← Fin.val_succ a, pv_coe, insertArc_val_succ]; simp
  have hz : (⟨q, hq⟩ : Fin (k + 2)) ≠ a.castSucc ∧
      (⟨q, hq⟩ : Fin (k + 2)) ≠ a.succ := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]; exact ⟨h₁, h₂⟩
  rw [pv_of_lt _ hq, ← skip_unskip a ⟨q, hq⟩ hz, insertArc, insertArcPM_skip, coe_skip,
    ← pv_coe, coe_unskip_eq_unskipN, ite_eq_right h₁, ite_eq_right h₂, skipN]

private theorem pv_insertArc_self (x : PlanarMatching k) (a : Fin (k + 1)) :
    pv (x.insertArc a) a = (a : ℕ) + 1 :=
  (val_castSucc_eq_succ_iff _ a).mp (insertArc_val_castSucc x a)

/-- Contracting the arc just inserted by `insertArc` recovers the original planar matching. -/
@[simp] theorem contract_insertArc (x : PlanarMatching k) (a : Fin (k + 1)) :
    (x.insertArc a).contract a = x :=
  ext_pv fun q hq => by
    have hns := skipN_lt_and_ne (a := a) hq
    rw [pv_contract _ _ hq, pv_insertArc _ _ hns.1, ite_eq_right hns.2.1, ite_eq_right hns.2.2,
      unskipN_skipN]
    simp only [joinN, unskipN, skipN]; split_ifs <;> omega

private theorem contractFn_pv_insertArc (x : PlanarMatching k) (a : Fin (k + 1)) :
    contractFn a (pv (x.insertArc a)) = pv x :=
  (pv_contract_eq (x.insertArc a) a).symm.trans (by rw [contract_insertArc])

/-- Re-inserting an adjacent arc `{a.castSucc, a.succ}` after contracting it recovers the original
planar matching. -/
theorem insertArc_contract {x : PlanarMatching (k + 2)} {a : Fin (k + 1)}
    (h : x.1.val a.castSucc = a.succ) : (x.contract a).insertArc a = x :=
  ext_pv fun q hq => by
    have _ := a.isLt
    have hpva : pv x a = (a : ℕ) + 1 := (val_castSucc_eq_succ_iff x a).mp h
    have hpva' : pv x ((a : ℕ) + 1) = a := by simpa [hpva] using pv_pv x (q := a) (by omega)
    rw [pv_insertArc _ _ hq]
    by_cases h₁ : q = a
    · simp [h₁, hpva]
    by_cases h₂ : q = (a : ℕ) + 1
    · simp [h₂, hpva']
    have hnq : pv x q ≠ a ∧ pv x q ≠ (a : ℕ) + 1 :=
      ⟨fun h' => h₂ (by rw [← pv_pv x hq, h', hpva]),
       fun h' => h₁ (by rw [← pv_pv x hq, h', hpva'])⟩
    rw [ite_eq_right h₁, ite_eq_right h₂,
      pv_contract _ _ (by simp only [unskipN]; split_ifs <;> omega), skipN_unskipN h₁ h₂]
    simp only [joinN, hnq.1, hnq.2, ite_false, skipN, unskipN]; split_ifs <;> omega

/-- Reflecting a planar matching with an inserted arc inserts the reflected arc into the reflected
matching. -/
theorem reflect_insertArc (x : PlanarMatching k) (a : Fin (k + 1)) :
    reflect (k + 2) (x.insertArc a) = (reflect k x).insertArc (Fin.rev a) :=
  ext_pv fun q hq => by
    have _ := a.isLt
    have hr : (Fin.rev a : ℕ) = k - a := by simp [Fin.val_rev]
    rw [pv_reflect _ hq, pv_insertArc _ _ (by omega), pv_insertArc _ _ hq, hr]
    by_cases h₁ : k + 2 - 1 - q = a
    · rw [ite_eq_left h₁, ite_eq_right (by omega), ite_eq_left (by omega)]; omega
    by_cases h₂ : k + 2 - 1 - q = (a : ℕ) + 1
    · rw [ite_eq_right h₁, ite_eq_left h₂, ite_eq_left (by omega)]; omega
    have hu : unskipN (k - a) q < k := by simp only [unskipN]; split_ifs <;> omega
    have _ := pv_lt x (q := k - 1 - unskipN (k - a) q) (by omega)
    rw [ite_eq_right h₁, ite_eq_right h₂, ite_eq_right (by omega), ite_eq_right (by omega),
      show unskipN (a : ℕ) (k + 2 - 1 - q) = k - 1 - unskipN (k - a) q by
        simp only [unskipN]; split_ifs <;> omega, pv_reflect _ hu]
    simp only [skipN]; split_ifs <;> omega

/-- Transport commutes with `insertArc`. -/
theorem cast_insertArc {k' : ℕ} (h : k = k') (x : PlanarMatching k) (a : Fin (k + 1)) :
    cast (congrArg (· + 2) h) (x.insertArc a) =
      (cast h x).insertArc (Fin.cast (congrArg (· + 1) h) a) := by subst h; simp

/-- Juxtaposing on the left shifts the insertion position of `insertArc` on the right factor. -/
theorem append_insertArc {k l : ℕ} (x : PlanarMatching k) (y : PlanarMatching l)
    (b : Fin (l + 1)) :
    x.append (y.insertArc b) = (x.append y).insertArc ⟨k + b, by omega⟩ :=
  ext_pv fun q hq => by
    have _ := b.isLt
    by_cases hqk : q < k
    · have _ := pv_lt x hqk
      rw [pv_append_left _ _ hqk, pv_insertArc _ _ hq,
        ite_eq_right (by dsimp; omega), ite_eq_right (by dsimp; omega),
        unskipN_of_lt (by dsimp; omega), pv_append_left _ _ hqk, skipN_of_lt (by dsimp; omega)]
    · rw [pv_append_right _ _ (by omega) hq, pv_insertArc _ _ (by omega), pv_insertArc _ _ hq]
      by_cases h₁ : q = k + b
      · simp [h₁]; omega
      by_cases h₂ : q = k + b + 1
      · simp [h₂, show k + (b : ℕ) + 1 - k = (b : ℕ) + 1 by omega]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by dsimp; exact h₁),
        ite_eq_right (by dsimp; exact h₂),
        show unskipN (⟨k + b, by omega⟩ : Fin (k + l + 1)) q = k + unskipN b (q - k) by
          simp only [unskipN]; split_ifs <;> omega,
        pv_append_right _ _ (by omega) (by simp only [unskipN]; split_ifs <;> omega),
        Nat.add_sub_cancel_left]
      simp only [skipN]; split_ifs <;> omega

private theorem glueFn_of_adj_right {n d : ℕ} :
    ∀ (m : ℕ) {φ : ℕ → ℕ}, φ (n + 2 * m + d) = n + 2 * m + d + 1 →
      glueFn n m φ (n + d) = n + d + 1
  | 0, _, h => by simpa [glueFn] using h
  | m + 1, φ, h => glueFn_of_adj_right m (φ := contractFn (n + m) φ) <| by
      rw [contractFn, erasePair_apply, skipN_of_le (by omega),
        show n + 2 * m + d + 2 = n + 2 * (m + 1) + d by omega,
        splice_of_ne _ (by omega) (by omega), h, rejoin_of_ne _ (by omega) (by omega),
        unskipN_of_le (by omega)]
      omega

/-- `glueMiddle` commutes with inserting an arc strictly to the right of the glued middle block,
and closes the same number of circles. -/
private theorem glueMiddle_insertArc_right {n p r : ℕ} (hr : r ≤ p) (m : ℕ)
    (x : PlanarMatching (n + m + (m + p))) :
    glueMiddle (n := n) (p := p + 2) m
      (cast (by omega) (x.insertArc ⟨n + 2 * m + r, by omega⟩)) =
      cast (by omega) ((glueMiddle m x).insertArc ⟨n + r, by omega⟩) ∧
    glueMiddleCircles (n := n) (p := p + 2) m
      (cast (by omega) (x.insertArc ⟨n + 2 * m + r, by omega⟩)) =
      glueMiddleCircles (n := n) (p := p) m x := by
  let a : Fin (n + m + (m + p) + 1) := ⟨n + 2 * m + r, by omega⟩
  let b : Fin (n + p + 1) := ⟨n + r, by omega⟩
  let z := x.insertArc a
  let w' : PlanarMatching (n + p + 2) :=
    cast (by omega) (glueMiddle (n := n) (p := p + 2) m (cast (by omega) z))
  have hz_arc : pv z (n + 2 * m + r) = n + 2 * m + r + 1 := pv_insertArc_self x a
  have hw_arc : glueFn n m (pv z) (n + r) = n + r + 1 := glueFn_of_adj_right m hz_arc
  obtain ⟨hfn, hcirc⟩ := glueFn_glueFn (n := n) (j := 1) m r (n + m + (m + p) + 2) z (by omega)
  simp only [glueFn, glueCircles, add_zero, zero_add] at hfn hcirc
  rw [contractFn_pv_insertArc x a] at hfn hcirc
  have hw'_contract : w'.contract b = glueMiddle m x := eq_of_pv_eq <| by
    rw [pv_contract_eq w' b, pv_cast_eq, pv_glueMiddle, pv_cast_eq, ← hfn, pv_glueMiddle]
  have hw'_arc : w'.1.val b.castSucc = b.succ := (val_castSucc_eq_succ_iff w' b).mpr <| by
    rw [pv_cast_eq, pv_glueMiddle, pv_cast_eq]; exact hw_arc
  refine ⟨?_, ?_⟩
  · have h : w' = (glueMiddle m x).insertArc b := by
      rw [← hw'_contract, insertArc_contract hw'_arc]
    rw [← h]; simp [w', z, a]
  · rw [glueMiddleCircles_eq, pv_cast_eq, glueMiddleCircles_eq]
    have hc₁ : circleInd (n + 2 * m + r) (pv z) = 1 := by simp only [circleInd, hz_arc, ite_true]
    have hc₂ : circleInd (n + r) (glueFn n m (pv z)) = 1 := by
      simp only [circleInd, hw_arc, ite_true]
    dsimp only [z, a] at hcirc hc₁ hc₂; omega

end InsertArc

end PlanarMatching

/-! ### Cups and caps at adjacent positions -/

namespace TLDiagram

variable {n m p q : ℕ}

/-- **Insert a top arc** joining the consecutive top points `c.castSucc` and `c.succ` (numbered
left to right along the top boundary) into a diagram `D : n → q`, keeping its closed circles. -/
def insertTopArc (D : TLDiagram n q) (c : Fin (q + 1)) : TLDiagram n (q + 2) where
  matching := PlanarMatching.cast (by omega) (D.matching.insertArc ⟨n + (q - c), by omega⟩)
  circles := D.circles

/-- **Insert a bottom arc** joining the consecutive bottom points `c.castSucc` and `c.succ` into a
diagram `D : q → m`, keeping its closed circles. -/
def insertBottomArc (D : TLDiagram q m) (c : Fin (q + 1)) : TLDiagram (q + 2) m :=
  verticalReflect m (q + 2) ((verticalReflect q m D).insertTopArc c)

/-- **A cup at position `c`**: the diagram `q → q + 2` with no circles that carries the `q` bottom
points straight to the top and inserts a cup joining the top points `c.castSucc` and `c.succ`
(numbered left to right). -/
def cupAt (c : Fin (q + 1)) : TLDiagram q (q + 2) := (id q).insertTopArc c

/-- **A cap at position `c`**: the diagram `q + 2 → q` with no circles that joins the bottom points
`c.castSucc` and `c.succ` by a cap and carries the remaining `q` bottom points straight to the
top. It is the vertical reflection of `TauCeti.TLDiagram.cupAt`. -/
def capAt (c : Fin (q + 1)) : TLDiagram (q + 2) q := verticalReflect q (q + 2) (cupAt c)

/-- The matching of `D.insertTopArc c` inserts an adjacent arc at cyclic label `n + (q - c)`. -/
@[simp] theorem matching_insertTopArc (D : TLDiagram n q) (c : Fin (q + 1)) :
    (D.insertTopArc c).matching =
      PlanarMatching.cast (by omega) (D.matching.insertArc ⟨n + (q - c), by omega⟩) := (rfl)

/-- The matching of `D.insertBottomArc c` inserts an adjacent arc at position `c` on the bottom
boundary. -/
@[simp] theorem matching_insertBottomArc (D : TLDiagram q m) (c : Fin (q + 1)) :
    (D.insertBottomArc c).matching =
      PlanarMatching.cast (by omega) (D.matching.insertArc ⟨c, by omega⟩) := by
  have _ := c.isLt
  have hrev : Fin.rev (⟨m + (q - c), by omega⟩ : Fin (m + q + 1)) =
      Fin.cast (by omega) (⟨c, by omega⟩ : Fin (q + m + 1)) := by
    ext; simp only [Fin.val_rev, Fin.val_cast]; omega
  rw [insertBottomArc, matching_verticalReflect, matching_insertTopArc, matching_verticalReflect,
    ← PlanarMatching.cast_reflect, PlanarMatching.cast_cast, PlanarMatching.reflect_insertArc,
    ← PlanarMatching.cast_reflect, PlanarMatching.reflect_reflect, hrev,
    ← PlanarMatching.cast_insertArc (by omega), PlanarMatching.cast_cast]

/-- Inserting a top arc into `id q` gives `cupAt c`. -/
@[simp] theorem insertTopArc_id (c : Fin (q + 1)) : (id q).insertTopArc c = cupAt c := (rfl)

/-- Inserting a bottom arc into `id q` gives `capAt c`. -/
@[simp] theorem insertBottomArc_id (c : Fin (q + 1)) : (id q).insertBottomArc c = capAt c := by
  rw [insertBottomArc, verticalReflect_id, insertTopArc_id, capAt]

/-- The matching of `cupAt c` inserts an adjacent arc into `PlanarMatching.nested q` at
`q + (q - c)`. -/
@[simp] theorem matching_cupAt (c : Fin (q + 1)) :
    (cupAt c).matching =
      PlanarMatching.cast (by omega)
        ((PlanarMatching.nested q).insertArc ⟨q + (q - c), by omega⟩) := by
  rw [cupAt, matching_insertTopArc, matching_id]

/-- The matching of `capAt c` inserts an adjacent arc into `PlanarMatching.nested q` at `c`. -/
@[simp] theorem matching_capAt (c : Fin (q + 1)) :
    (capAt c).matching =
      PlanarMatching.cast (by omega) ((PlanarMatching.nested q).insertArc ⟨c, by omega⟩) := by
  rw [← insertBottomArc_id, matching_insertBottomArc, matching_id]

@[simp] theorem circles_insertTopArc (D : TLDiagram n q) (c : Fin (q + 1)) :
    (D.insertTopArc c).circles = D.circles := (rfl)
@[simp] theorem circles_insertBottomArc (D : TLDiagram q m) (c : Fin (q + 1)) :
    (D.insertBottomArc c).circles = D.circles := by
  rw [insertBottomArc, circles_verticalReflect, circles_insertTopArc, circles_verticalReflect]
@[simp] theorem circles_cupAt (c : Fin (q + 1)) : (cupAt c).circles = 0 := by
  rw [← insertTopArc_id, circles_insertTopArc, circles_id]
@[simp] theorem circles_capAt (c : Fin (q + 1)) : (capAt c).circles = 0 := by
  rw [capAt, circles_verticalReflect, circles_cupAt]

/-- Vertically reflecting `D.insertTopArc c` inserts a bottom arc at `c` into the reflected
diagram. -/
@[simp] theorem verticalReflect_insertTopArc (D : TLDiagram n q) (c : Fin (q + 1)) :
    verticalReflect n (q + 2) (D.insertTopArc c) = (verticalReflect n q D).insertBottomArc c := by
  rw [insertBottomArc, verticalReflect_verticalReflect]

/-- Vertically reflecting `D.insertBottomArc c` inserts a top arc at `c` into the reflected
diagram. -/
@[simp] theorem verticalReflect_insertBottomArc (D : TLDiagram q m) (c : Fin (q + 1)) :
    verticalReflect (q + 2) m (D.insertBottomArc c) = (verticalReflect q m D).insertTopArc c := by
  rw [insertBottomArc, verticalReflect_verticalReflect]

@[simp] theorem verticalReflect_cupAt (c : Fin (q + 1)) :
    verticalReflect q (q + 2) (cupAt c) = capAt c := (rfl)
@[simp] theorem verticalReflect_capAt (c : Fin (q + 1)) :
    verticalReflect (q + 2) q (capAt c) = cupAt c := verticalReflect_verticalReflect (cupAt c)

@[simp] theorem cupAt_zero : cupAt (0 : Fin 1) = cup :=
  TLDiagram.ext (PlanarMatching.ext fun i => by
    rw [matching_cupAt, cup_matching_val, PlanarMatching.cast_refl, Equiv.refl_apply,
      Subsingleton.elim (⟨0 + (0 - (0 : Fin 1)), by omega⟩ : Fin 1) 0]
    fin_cases i
    · exact PlanarMatching.insertArc_val_castSucc _ 0
    · exact PlanarMatching.insertArc_val_succ _ 0) (by rw [circles_cupAt, circles_cup])

@[simp] theorem capAt_zero : capAt (0 : Fin 1) = cap := by
  rw [capAt, cupAt_zero, verticalReflect_cup]

/-- Pre-composing (composing on the left) commutes with inserting a top arc: the inserted top arc
lies away from the middle junction, so gluing across the middle leaves it untouched and closes the
same circles. -/
theorem comp_insertTopArc (f : TLDiagram n m) (g : TLDiagram m q) (c : Fin (q + 1)) :
    f.comp (g.insertTopArc c) = (f.comp g).insertTopArc c := by
  open PlanarMatching in
  have _ := c.isLt
  have happ : f.matching.append (g.insertTopArc c).matching =
      PlanarMatching.cast (by omega)
        ((f.matching.append g.matching).insertArc ⟨n + 2 * m + (q - c), by omega⟩) := by
    have h := append_cast rfl (by omega : m + q + 2 = m + (q + 2))
      f.matching (g.matching.insertArc ⟨m + (q - c), by omega⟩)
    rw [PlanarMatching.cast_refl, Equiv.refl_apply, ← matching_insertTopArc, append_insertArc] at h
    exact h.trans (congrArg (PlanarMatching.cast _) (congrArg _ (Fin.ext (by dsimp; omega))))
  obtain ⟨hm, hcirc⟩ := glueMiddle_insertArc_right (n := n) (p := q) (r := q - c) (by omega) m
    (f.matching.append g.matching)
  exact TLDiagram.ext (by rw [matching_comp, happ, hm, matching_insertTopArc, matching_comp])
    (by rw [circles_comp, circles_insertTopArc, circles_insertTopArc, circles_comp, happ, hcirc])

/-- Post-composing (composing on the right) commutes with inserting a bottom arc. -/
theorem insertBottomArc_comp (f : TLDiagram q m) (g : TLDiagram m p) (c : Fin (q + 1)) :
    (f.insertBottomArc c).comp g = (f.comp g).insertBottomArc c :=
  (verticalReflect (q + 2) p).injective <| by
    rw [verticalReflect_comp, verticalReflect_insertBottomArc, comp_insertTopArc,
      ← verticalReflect_comp, verticalReflect_insertBottomArc]

/-- Post-composing a diagram with `cupAt c` inserts a top arc at position `c`. -/
theorem comp_cupAt (f : TLDiagram n q) (c : Fin (q + 1)) :
    f.comp (cupAt c) = f.insertTopArc c := by rw [← insertTopArc_id, comp_insertTopArc, comp_id]

/-- Pre-composing a diagram with `capAt c` inserts a bottom arc at position `c`. -/
theorem capAt_comp (c : Fin (q + 1)) (g : TLDiagram q m) :
    (capAt c).comp g = g.insertBottomArc c := by
  rw [← insertBottomArc_id, insertBottomArc_comp, id_comp]

/-- Inserting a top arc leaves the bottom half-diagram unchanged. -/
@[simp] theorem bottomHalf_insertTopArc_val (D : TLDiagram n q) (c : Fin (q + 1)) :
    (D.insertTopArc c).bottomHalf.val = D.bottomHalf.val := by
  open PlanarMatching in
  have _ := c.isLt; ext i; have _ := i.isLt
  have hpv₁ : ((D.insertTopArc c).matching.1.val (i.castAdd (q + 2)) : ℕ) =
      pv (D.insertTopArc c).matching i := by rw [← pv_coe, Fin.val_castAdd]
  have hpv₂ : (D.matching.1.val (i.castAdd q) : ℕ) = pv D.matching i := by
    rw [← pv_coe, Fin.val_castAdd]
  have hpv_eq : pv (D.insertTopArc c).matching i = skipN (n + (q - c)) (pv D.matching i) := by
    rw [matching_insertTopArc, pv_cast, pv_insertArc _ _ (by omega)]
    dsimp only; rw [ite_eq_right (by omega), ite_eq_right (by omega), unskipN_of_lt (by omega)]
  rw [bottomHalf_apply, bottomHalf_apply]
  simp only [hpv₁, hpv₂, hpv_eq, skipN]; split_ifs <;> dsimp only <;> omega

/-- Inserting a top arc does not change the number of through strands. -/
@[simp] theorem through_insertTopArc (D : TLDiagram n q) (c : Fin (q + 1)) :
    (D.insertTopArc c).through = D.through :=
  through_eq_of_bottomHalf_val_eq (bottomHalf_insertTopArc_val D c)

/-- Inserting a bottom arc does not change the number of through strands. -/
@[simp] theorem through_insertBottomArc (D : TLDiagram q m) (c : Fin (q + 1)) :
    (D.insertBottomArc c).through = D.through := by
  rw [insertBottomArc, through_verticalReflect, through_insertTopArc, through_verticalReflect]

/-- Inserting a bottom arc leaves the top half-diagram unchanged. -/
@[simp] theorem topHalf_insertBottomArc_val (D : TLDiagram q m) (c : Fin (q + 1)) :
    (D.insertBottomArc c).topHalf.val = D.topHalf.val := by
  rw [insertBottomArc, topHalf_verticalReflect_val, bottomHalf_insertTopArc_val, ← topHalf_val]

/-- The bottom half-diagram of `D.insertBottomArc c` joins `c.castSucc` to `c.succ`. -/
@[simp] theorem bottomHalf_insertBottomArc_val_castSucc (D : TLDiagram q m) (c : Fin (q + 1)) :
    (D.insertBottomArc c).bottomHalf.val c.castSucc = c.succ := by
  have _ := c.isLt
  have hpv :
      ((D.insertBottomArc c).matching.1.val (c.castSucc.castAdd m) : ℕ) = (c : ℕ) + 1 := by
    rw [← PlanarMatching.pv_coe, Fin.val_castAdd, Fin.val_castSucc, matching_insertBottomArc,
      PlanarMatching.pv_cast, PlanarMatching.pv_insertArc_self]
  apply Fin.ext
  rw [bottomHalf_apply]
  simp only [hpv, show (c : ℕ) + 1 < q + 2 by omega, dite_true, Fin.val_succ]

/-- The bottom half-diagram of `D.insertBottomArc c` joins `c.succ` to `c.castSucc`. -/
@[simp] theorem bottomHalf_insertBottomArc_val_succ (D : TLDiagram q m) (c : Fin (q + 1)) :
    (D.insertBottomArc c).bottomHalf.val c.succ = c.castSucc := by
  rw [← bottomHalf_insertBottomArc_val_castSucc D c,
    (Equiv.Perm.isHalfDiagram_iff.mp (D.insertBottomArc c).bottomHalf.2.1).1 c.castSucc]

/-- Away from the inserted arc, the bottom half-diagram of `D.insertBottomArc c` acts as
`D.bottomHalf` conjugated by skipping the two inserted positions. -/
@[simp] theorem bottomHalf_insertBottomArc_val_succAbove_succAbove (D : TLDiagram q m)
    (c : Fin (q + 1)) (i : Fin q) :
    (D.insertBottomArc c).bottomHalf.val (c.castSucc.succAbove (c.succAbove i)) =
      c.castSucc.succAbove (c.succAbove (D.bottomHalf.val i)) := by
  open PlanarMatching in
  have _ := c.isLt; have _ := i.isLt
  have hns := skipN_lt_and_ne (a := c) i.isLt
  have hs : ∀ j : Fin q,
      ((c.castSucc.succAbove (c.succAbove j) : Fin (q + 2)) : ℕ) = skipN c j :=
    fun j => by rw [← skip, coe_skip, skipN]
  have hpv₁ : ((D.insertBottomArc c).matching.1.val
      ((c.castSucc.succAbove (c.succAbove i)).castAdd m) : ℕ) = skipN c (pv D.matching i) := by
    rw [← pv_coe, Fin.val_castAdd, hs i, matching_insertBottomArc, pv_cast,
      pv_insertArc _ _ (by omega)]
    dsimp only; rw [ite_eq_right hns.2.1, ite_eq_right hns.2.2, unskipN_skipN]
  have hpv₂ : (D.matching.1.val (i.castAdd m) : ℕ) = pv D.matching i := by
    rw [← pv_coe, Fin.val_castAdd]
  apply Fin.ext
  rw [bottomHalf_apply, hs, bottomHalf_apply]
  simp only [hpv₁, hpv₂]
  by_cases hlt : pv D.matching i < q
  · simp only [hlt, (skipN_lt_and_ne (a := c) hlt).1, dite_true]
  · simp only [hlt, show ¬ skipN c (pv D.matching i) < q + 2 by
      rw [skipN_of_le (by omega)]; omega, dite_false, hs i]

/-- The top half-diagram of `D.insertTopArc c` joins `c.castSucc` to `c.succ`. -/
@[simp] theorem topHalf_insertTopArc_val_castSucc (D : TLDiagram n q) (c : Fin (q + 1)) :
    (D.insertTopArc c).topHalf.val c.castSucc = c.succ := by
  rw [topHalf_val, verticalReflect_insertTopArc, bottomHalf_insertBottomArc_val_castSucc]

/-- The top half-diagram of `D.insertTopArc c` joins `c.succ` to `c.castSucc`. -/
@[simp] theorem topHalf_insertTopArc_val_succ (D : TLDiagram n q) (c : Fin (q + 1)) :
    (D.insertTopArc c).topHalf.val c.succ = c.castSucc := by
  rw [topHalf_val, verticalReflect_insertTopArc, bottomHalf_insertBottomArc_val_succ]

/-- Away from the inserted arc, the top half-diagram of `D.insertTopArc c` acts as `D.topHalf`
conjugated by skipping the two inserted positions. -/
@[simp] theorem topHalf_insertTopArc_val_succAbove_succAbove (D : TLDiagram n q) (c : Fin (q + 1))
    (j : Fin q) :
    (D.insertTopArc c).topHalf.val (c.castSucc.succAbove (c.succAbove j)) =
      c.castSucc.succAbove (c.succAbove (D.topHalf.val j)) := by
  rw [topHalf_val, verticalReflect_insertTopArc,
    bottomHalf_insertBottomArc_val_succAbove_succAbove, ← topHalf_val]

@[simp] theorem through_cupAt (c : Fin (q + 1)) : (cupAt c).through = q := by
  rw [← insertTopArc_id, through_insertTopArc, through_id]
@[simp] theorem through_capAt (c : Fin (q + 1)) : (capAt c).through = q := by
  rw [capAt, through_verticalReflect, through_cupAt]

/-- The bottom half-diagram of `cupAt c` has no arcs. -/
@[simp] theorem bottomHalf_cupAt_val (c : Fin (q + 1)) : (cupAt c).bottomHalf.val = 1 := by
  rw [← insertTopArc_id, bottomHalf_insertTopArc_val, bottomHalf_id_val]

/-- The top half-diagram of `capAt c` has no arcs. -/
@[simp] theorem topHalf_capAt_val (c : Fin (q + 1)) : (capAt c).topHalf.val = 1 := by
  rw [← insertBottomArc_id, topHalf_insertBottomArc_val, topHalf_id_val]

/-- The bottom half-diagram of `capAt c` has a single arc joining `c.castSucc` and `c.succ`. -/
@[simp] theorem bottomHalf_capAt_val (c : Fin (q + 1)) :
    (capAt c).bottomHalf.val = Equiv.swap c.castSucc c.succ := by
  ext j
  by_cases h₁ : j = c.castSucc
  · subst h₁
    rw [← insertBottomArc_id, bottomHalf_insertBottomArc_val_castSucc, swap_apply_left]
  by_cases h₂ : j = c.succ
  · subst h₂; rw [← insertBottomArc_id, bottomHalf_insertBottomArc_val_succ, swap_apply_right]
  rw [← PlanarMatching.skip_unskip c j ⟨h₁, h₂⟩,
    swap_apply_of_ne_of_ne (PlanarMatching.skip_ne_castSucc c _) (PlanarMatching.skip_ne_succ c _),
    PlanarMatching.skip, ← insertBottomArc_id, bottomHalf_insertBottomArc_val_succAbove_succAbove,
    bottomHalf_id_val, Perm.one_apply]

/-- The top half-diagram of `cupAt c` has a single arc joining `c.castSucc` and `c.succ`. -/
@[simp] theorem topHalf_cupAt_val (c : Fin (q + 1)) :
    (cupAt c).topHalf.val = Equiv.swap c.castSucc c.succ := by
  rw [topHalf_val, verticalReflect_cupAt, bottomHalf_capAt_val]

/-- If a diagram `D : n → q + 2` has an arc joining the consecutive top points `c.castSucc` and
`c.succ`, it is obtained by post-composing a diagram `D' : n → q` with `cupAt c`. -/
theorem exists_comp_cupAt_of_topHalf_apply_eq {D : TLDiagram n (q + 2)} {c : Fin (q + 1)}
    (h : D.topHalf.val c.castSucc = c.succ) :
    ∃ D' : TLDiagram n q, D'.through = D.through ∧ D'.circles = D.circles ∧
      D'.comp (cupAt c) = D := by
  open PlanarMatching in
  have _ := c.isLt
  let a : Fin (n + q + 1) := ⟨n + (q - c), by omega⟩
  let y : PlanarMatching (n + q + 2) := cast (by omega) D.matching
  have hy : y.1.val a.castSucc = a.succ := by
    let b : Fin (n + (q + 2)) := ⟨n + (q + 2) - 1 - c, by omega⟩
    have htop := congrArg Fin.val ((D.topHalf_apply c.castSucc).symm.trans h)
    simp only [Fin.val_castSucc, Fin.val_succ] at htop
    have hb_lt := (D.matching.1.val b).isLt
    have hb_eq : D.matching.1.val b = ⟨n + (q - c), by omega⟩ := Fin.ext <| by
      dsimp only [b] at hb_lt ⊢
      split_ifs at htop <;> simp only [Fin.val_castSucc] at htop <;> omega
    have hpva : pv D.matching (n + (q - c)) = n + (q + 2) - 1 - c := by
      rw [pv_of_lt D.matching (by omega), ← hb_eq, D.matching.1.apply_apply]
    exact (val_castSucc_eq_succ_iff y a).mpr <| by dsimp only [y, a]; rw [pv_cast, hpva]; omega
  have hd : (⟨y.contract a, D.circles⟩ : TLDiagram n q).insertTopArc c = D :=
    TLDiagram.ext (by rw [matching_insertTopArc, insertArc_contract hy]; simp [y]) rfl
  exact ⟨⟨y.contract a, D.circles⟩, by rw [← through_insertTopArc _ c, hd], rfl,
    by rw [comp_cupAt, hd]⟩

/-- If a diagram `D : q + 2 → m` has an arc joining the consecutive bottom points `c.castSucc` and
`c.succ`, it is obtained by pre-composing a diagram `D' : q → m` with `capAt c`. -/
theorem exists_capAt_comp_of_bottomHalf_apply_eq {D : TLDiagram (q + 2) m} {c : Fin (q + 1)}
    (h : D.bottomHalf.val c.castSucc = c.succ) :
    ∃ D' : TLDiagram q m, D'.through = D.through ∧ D'.circles = D.circles ∧
      (capAt c).comp D' = D := by
  obtain ⟨E, hth, hcirc, heq⟩ := exists_comp_cupAt_of_topHalf_apply_eq
    (D := verticalReflect (q + 2) m D) (by rwa [topHalf_verticalReflect_val])
  refine ⟨verticalReflect m q E, by rw [through_verticalReflect, hth, through_verticalReflect],
    by rw [circles_verticalReflect, hcirc, circles_verticalReflect],
    (verticalReflect (q + 2) m).injective ?_⟩
  rw [verticalReflect_comp, verticalReflect_capAt, verticalReflect_verticalReflect, heq]

/-! ### Computing `cupAt c ≫ capAt c` -/

section CupCompCap

open PlanarMatching

private theorem glueFn_add (n a : ℕ) :
    ∀ (b : ℕ) (φ : ℕ → ℕ),
      glueFn n (a + b) φ = glueFn n a (glueFn (n + a) b φ) ∧
      glueCircles n (a + b) φ = glueCircles n a (glueFn (n + a) b φ) + glueCircles (n + a) b φ
  | 0, _ => ⟨rfl, (Nat.add_zero _).symm⟩
  | b + 1, φ => by
    obtain ⟨h₁, h₂⟩ := glueFn_add n a b (contractFn (n + a + b) φ)
    rw [Nat.add_succ, glueFn, glueFn, glueCircles, glueCircles, ← Nat.add_assoc n a b]
    exact ⟨h₁, by omega⟩

private theorem exists_pv_eq_glueFn {n : ℕ} :
    ∀ (j K : ℕ) (x : PlanarMatching K), n + 2 * j ≤ K →
      ∃ y : PlanarMatching (K - 2 * j), pv y = glueFn n j (pv x)
  | 0, _, x, _ => ⟨x, rfl⟩
  | j + 1, K, x, hK => by
    obtain ⟨y, hy⟩ := exists_pv_eq_contractFn x (a := n + j) (by omega)
    obtain ⟨z, hz⟩ := exists_pv_eq_glueFn (n := n) j (K - 2) y (by omega)
    exact ⟨PlanarMatching.cast (by omega) z, by rw [pv_cast_eq, hz, hy, glueFn]⟩

private theorem glueFn_of_adj_left {a m : ℕ} (ham : a + 2 ≤ m) :
    ∀ (j : ℕ) {φ : ℕ → ℕ}, φ a = a + 1 → glueFn m j φ a = a + 1
  | 0, _, h => h
  | j + 1, φ, h => glueFn_of_adj_left ham j <| by
      rw [contractFn, erasePair_apply, skipN_of_lt (by omega),
        splice_of_ne _ (by omega) (by omega), h,
        rejoin_of_ne _ (by omega) (by omega), unskipN_of_lt (by omega)]

private theorem glueFn_two_of_adj {a : ℕ} {ψ : ℕ → ℕ} (hψ : ∀ u, ψ (ψ u) = u)
    (h₁ : ψ a = a + 1) (h₂ : ψ (a + 2) = a + 3) :
    glueFn a 2 ψ = contractFn a (contractFn (a + 2) ψ) ∧ glueCircles a 2 ψ = 1 := by
  have h₁' : ψ (a + 1) = a := by rw [← h₁, hψ]
  have h₂' : ψ (a + 3) = a + 2 := by rw [← h₂, hψ]
  have hc₁ : contractFn (a + 1) ψ a = a + 1 := by
    rw [contractFn, erasePair_apply, skipN_of_lt (by omega), splice_of_ne _ (by omega) (by omega),
      h₁, rejoin_of_eq_left _ rfl, h₂, unskipN_of_le (by omega)]; omega
  have h_out : ∀ b, b = a + 1 ∨ b = a + 2 → ∀ r, r ≠ a → r ≠ a + 1 →
      contractFn b ψ r = unskipN b (ψ (skipN b r)) ∧
      unskipN b (ψ (skipN b r)) ≠ a ∧ unskipN b (ψ (skipN b r)) ≠ a + 1 := by
    intro b hb r hr0 hr1
    set v := skipN b r with hv_def
    have hz : v ≠ a ∧ v ≠ a + 1 ∧ v ≠ a + 2 ∧ v ≠ a + 3 := by
      simp only [hv_def, skipN]; rcases hb with rfl | rfl <;> split_ifs <;> omega
    have hv : ψ v ≠ a ∧ ψ v ≠ a + 1 ∧ ψ v ≠ a + 2 ∧ ψ v ≠ a + 3 :=
      ⟨fun h => hz.2.1 (by rw [← hψ v, h, h₁]), fun h => hz.1 (by rw [← hψ v, h, h₁']),
       fun h => hz.2.2.2 (by rw [← hψ v, h, h₂]),
       fun h => hz.2.2.1 (by rw [← hψ v, h, h₂'])⟩
    refine ⟨?_, by simp only [unskipN]; rcases hb with rfl | rfl <;> split_ifs <;> omega,
      by simp only [unskipN]; rcases hb with rfl | rfl <;> split_ifs <;> omega⟩
    rw [contractFn, erasePair_apply, ← hv_def,
      splice_of_ne _ (by rcases hb with rfl | rfl <;> omega)
        (by rcases hb with rfl | rfl <;> omega),
      rejoin_of_ne _ (by rcases hb with rfl | rfl <;> omega)
        (by rcases hb with rfl | rfl <;> omega)]
  refine ⟨funext fun q => ?_, by
      rw [glueCircles, glueCircles, glueCircles, Nat.add_zero, circleInd, circleInd, hc₁, h₁',
        ite_eq_left rfl, ite_eq_right (by omega)]⟩
  have hr : skipN a q ≠ a ∧ skipN a q ≠ a + 1 := by simp only [skipN]; split_ifs <;> omega
  obtain ⟨e₁, n₁, n₁'⟩ := h_out (a + 1) (Or.inl rfl) (skipN a q) hr.1 hr.2
  obtain ⟨e₂, n₂, n₂'⟩ := h_out (a + 2) (Or.inr rfl) (skipN a q) hr.1 hr.2
  have hsk : skipN (a + 1) (skipN a q) = skipN (a + 2) (skipN a q) := by
    simp only [skipN]; split_ifs <;> omega
  have hcf (f : ℕ → ℕ) : contractFn a f q = unskipN a (splice a f (skipN a q)) := by
    rw [contractFn, erasePair_apply]
  simp only [glueFn, Nat.add_zero]
  rw [hcf, hcf, splice_of_ne _ hr.1 hr.2, splice_of_ne _ hr.1 hr.2, e₁, e₂,
    rejoin_of_ne _ n₁ n₁', rejoin_of_ne _ n₂ n₂', ← hsk]
  rw [← hsk] at n₂ n₂'
  simp only [unskipN] at n₁ n₁' n₂ n₂' ⊢; split_ifs at * <;> omega

private theorem glueFn_two_add_of_flanking_adj {K K₁ K₀ a c : ℕ} {z : PlanarMatching K}
    {z₁ : PlanarMatching K₁} {z₀ : PlanarMatching K₀} (hK : a + 2 + 2 * c + 2 ≤ K)
    (hK₁ : a + 2 + 2 * c ≤ K₁) (hzL : pv z a = a + 1)
    (hzR : pv z (a + 2 + 2 * c) = a + 2 + 2 * c + 1) (hz₁L : pv z₁ a = a + 1)
    (hcR : contractFn (a + 2 + 2 * c) (pv z) = pv z₁) (hcL : contractFn a (pv z₁) = pv z₀) :
    glueFn a (2 + c) (pv z) = glueFn a c (pv z₀) ∧
    glueCircles a (2 + c) (pv z) = glueCircles a c (pv z₀) + 1 := by
  obtain ⟨y, hy⟩ := exists_pv_eq_glueFn (n := a + 2) c _ z (by omega)
  have hψ₁ := glueFn_of_adj_left (a := a) (m := a + 2) (by omega) c hzL
  have hψ₂ : glueFn (a + 2) c (pv z) (a + 2) = a + 2 + 1 := by
    simpa only [add_zero] using glueFn_of_adj_right (n := a + 2) (d := 0) c
      (by simpa only [add_zero] using hzR)
  obtain ⟨h2fn, h2c⟩ := glueFn_two_of_adj (by rw [← hy]; exact pv_pv_eq y) hψ₁ hψ₂
  obtain ⟨hRfn, hRc⟩ := glueFn_glueFn (n := a + 2) (j := 1) c 0 _ z (by omega)
  simp only [glueFn, glueCircles, add_zero, zero_add] at hRfn hRc
  rw [hcR] at hRfn hRc
  obtain ⟨hLfn, hLc⟩ := contractFn_glueFn (a := a) c a _ z₁ (le_refl _) (by omega)
  rw [hcL] at hLfn hLc
  obtain ⟨hs, hsc⟩ := glueFn_add a 2 c (pv z)
  have hi : ∀ {k} {φ : ℕ → ℕ}, φ k = k + 1 → circleInd k φ = 1 :=
    fun h => by simp only [circleInd, h, ite_true]
  have h₁ := hi hzR; have h₂ := hi hψ₂; have h₃ := hi hz₁L
  have h₄ := hi (glueFn_of_adj_left (m := a + 2) (by omega) c hz₁L)
  exact ⟨by rw [hs, h2fn, ← hRfn, hLfn], by rw [hsc, h2c]; omega⟩

/-- **A cup at position `c` followed by the matching cap closes one circle**: `cupAt c ≫ capAt c`
is the identity matching on `q` strands carrying one closed circle. -/
@[simp] theorem cupAt_comp_capAt {q : ℕ} (c : Fin (q + 1)) :
    (cupAt c).comp (capAt c) = ⟨PlanarMatching.nested q, 1⟩ := by
  have _ := c.isLt
  let z := (cupAt c).matching.append (capAt c).matching
  let z₁ := (cupAt c).matching.append (nested q)
  let z₀ := (nested q).append (nested q)
  have hcup_pv : pv (cupAt c).matching (2 * q - c) = 2 * q - c + 1 := by
    rw [matching_cupAt, pv_cast, show 2 * q - (c : ℕ) = q + (q - c) by omega]
    exact pv_insertArc_self (nested q) ⟨q + (q - c), by omega⟩
  have hcap_pv : pv (capAt c).matching c = (c : ℕ) + 1 := by
    rw [matching_capAt, pv_cast]; exact pv_insertArc_self (nested q) ⟨c, by omega⟩
  have hz_cup : pv z (2 * q - c) = 2 * q - c + 1 := by rw [pv_append_left _ _ (by omega), hcup_pv]
  have hz_cap : pv z (2 * q + 2 + c) = 2 * q + 2 + c + 1 := by
    rw [pv_append_right _ _ (by omega) (by omega),
      show 2 * q + 2 + (c : ℕ) - (q + (q + 2)) = c by omega, hcap_pv]; omega
  have hcup_c : contractFn (2 * q - c) (pv (cupAt c).matching) = pv (nested q) := by
    rw [matching_cupAt, pv_cast_eq, show 2 * q - (c : ℕ) = q + (q - c) by omega]
    exact contractFn_pv_insertArc (nested q) ⟨q + (q - c), by omega⟩
  have hcap_c : contractFn c (pv (capAt c).matching) = pv (nested q) := by
    rw [matching_capAt, pv_cast_eq]; exact contractFn_pv_insertArc (nested q) ⟨c, by omega⟩
  have hz_c : contractFn (2 * q + 2 + c) (pv z) = pv z₁ := by
    rw [pv_append_eq, show 2 * q + 2 + (c : ℕ) = q + (q + 2) + c by omega,
      contractFn_appendFn_right _ _ (by omega), hcap_c,
      show q + 2 + q - 2 = q + q by omega, pv_append_eq]
  have hz₁_c : contractFn (2 * q - c) (pv z₁) = pv z₀ := by
    rw [pv_append_eq, contractFn_appendFn_left _ _ (by omega), hcup_c,
      show q + (q + 2) - 2 = q + q by omega, pv_append_eq]
  have hidx : 2 * q - (c : ℕ) + 2 + 2 * c = 2 * q + 2 + c := by omega
  obtain ⟨hmid_fn, hmid_c⟩ := glueFn_two_add_of_flanking_adj (a := 2 * q - c) (c := c)
    (by omega) (by omega) hz_cup (by rwa [hidx])
    (by rw [pv_append_left _ _ (by omega), hcup_pv]) (by rwa [hidx]) hz₁_c
  obtain ⟨hs₁, hs₁c⟩ := glueFn_add q (q - c) (2 + c) (pv z)
  obtain ⟨hs₀, hs₀c⟩ := glueFn_add q (q - c) c (pv z₀)
  rw [show q - (c : ℕ) + (2 + c) = q + 2 by omega,
    show q + (q - (c : ℕ)) = 2 * q - c by omega] at hs₁ hs₁c
  rw [show q - (c : ℕ) + c = q by omega,
    show q + (q - (c : ℕ)) = 2 * q - c by omega] at hs₀ hs₀c
  exact TLDiagram.ext
    (eq_of_pv_eq <| by
      rw [matching_comp, pv_glueMiddle, hs₁, hmid_fn, ← hs₀, ← pv_glueMiddle,
        glueMiddle_append_nested])
    (by rw [circles_comp, circles_cupAt, circles_capAt, zero_add, zero_add, glueMiddleCircles_eq,
          hs₁c, hmid_fn, hmid_c]
        have hz₀c : glueCircles q q (pv z₀) = 0 := by
          rw [← glueMiddleCircles_eq, glueMiddleCircles_append_nested]
        dsimp only; omega)

end CupCompCap

end TLDiagram

end TauCeti
