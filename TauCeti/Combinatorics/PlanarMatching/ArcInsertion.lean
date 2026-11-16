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
  rw [insertArcPM, PerfectMatching.extend_apply_of_mem _ _ ⟨skip_ne_castSucc a i, skip_ne_succ a i⟩]
  exact congrArg Subtype.val (PerfectMatching.congr_val_apply_apply (skipEquiv a) x.1 i)

private theorem insertArcPM_noncrossing (x : PlanarMatching k) (a : Fin (k + 1)) :
    (insertArcPM x a).val.IsNoncrossingMatching := by
  rw [Perm.isNoncrossingMatching_iff]
  intro u v huv hvu hlt
  by_cases hu₁ : u = a.castSucc
  · rw [hu₁] at huv hvu; rw [insertArcPM, PerfectMatching.extend_apply_left] at hvu
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at huv hvu; omega
  by_cases hu₂ : u = a.succ
  · rw [hu₂] at huv hvu; rw [insertArcPM, PerfectMatching.extend_apply_right] at hvu
    exact absurd (huv.trans hvu) (not_lt_of_gt Fin.castSucc_lt_succ)
  rw [← skip_unskip a u ⟨hu₁, hu₂⟩] at huv hvu hlt; rw [insertArcPM_skip] at hvu hlt
  by_cases hv₁ : v = a.castSucc
  · rw [hv₁] at hvu hlt; rw [insertArcPM, PerfectMatching.extend_apply_left] at hlt
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at hvu hlt; omega
  by_cases hv₂ : v = a.succ
  · rw [hv₂] at hvu hlt; rw [insertArcPM, PerfectMatching.extend_apply_right] at hlt
    exact absurd (hvu.trans hlt) (not_lt_of_gt Fin.castSucc_lt_succ)
  rw [← skip_unskip a v ⟨hv₁, hv₂⟩] at huv hvu hlt; rw [insertArcPM_skip] at hlt
  exact Perm.isNoncrossingMatching_iff.mp x.2 ((skip_strictMono a).lt_iff_lt.mp huv)
    ((skip_strictMono a).lt_iff_lt.mp hvu) ((skip_strictMono a).lt_iff_lt.mp hlt)

/-- **Inserting an adjacent arc** `{a.castSucc, a.succ}` into a planar matching `x` of `k` points,
shifting all boundary points from `a` onwards up by two. It is a right inverse to
`TauCeti.PlanarMatching.contract`. -/
def insertArc (x : PlanarMatching k) (a : Fin (k + 1)) : PlanarMatching (k + 2) :=
  ⟨insertArcPM x a, insertArcPM_noncrossing x a⟩

@[simp]
theorem insertArc_val_castSucc (x : PlanarMatching k) (a : Fin (k + 1)) :
    (x.insertArc a).1.val a.castSucc = a.succ :=
  PerfectMatching.extend_apply_left (succ_ne_castSucc a).symm _

@[simp]
theorem insertArc_val_succ (x : PlanarMatching k) (a : Fin (k + 1)) :
    (x.insertArc a).1.val a.succ = a.castSucc :=
  PerfectMatching.extend_apply_right (succ_ne_castSucc a).symm _

private theorem insertArc_val_skip (x : PlanarMatching k) (a : Fin (k + 1)) (i : Fin k) :
    (x.insertArc a).1.val (skip a i) = skip a (x.1.val i) :=
  insertArcPM_skip x a i

/-- Outside the inserted arc, `insertArc` acts on boundary points as the original planar matching
conjugated by skipping the two inserted positions. -/
@[simp]
theorem insertArc_val_succAbove_succAbove (x : PlanarMatching k) (a : Fin (k + 1)) (i : Fin k) :
    (x.insertArc a).1.val (a.castSucc.succAbove (a.succAbove i)) =
      a.castSucc.succAbove (a.succAbove (x.1.val i)) :=
  insertArc_val_skip x a i

private theorem pv_insertArc (x : PlanarMatching k) (a : Fin (k + 1)) {q : ℕ} (hq : q < k + 2) :
    pv (x.insertArc a) q =
      if q = (a : ℕ) then (a : ℕ) + 1
      else if q = (a : ℕ) + 1 then (a : ℕ)
      else skipN a (pv x (unskipN a q)) := by
  by_cases h₁ : q = a
  · subst h₁; rw [← Fin.val_castSucc a, pv_coe, insertArc_val_castSucc]; simp
  by_cases h₂ : q = (a : ℕ) + 1
  · subst h₂; rw [← Fin.val_succ a, pv_coe, insertArc_val_succ]; simp
  have hz : (⟨q, hq⟩ : Fin (k + 2)) ≠ a.castSucc ∧ (⟨q, hq⟩ : Fin (k + 2)) ≠ a.succ := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]; exact ⟨h₁, h₂⟩
  rw [pv_of_lt _ hq, ← skip_unskip a ⟨q, hq⟩ hz, insertArc_val_skip, coe_skip_eq_skipN,
    ← pv_coe, coe_unskip_eq_unskipN, ite_eq_right h₁, ite_eq_right h₂]

/-- Contracting the arc just inserted by `insertArc` recovers the original planar matching. -/
@[simp]
theorem contract_insertArc (x : PlanarMatching k) (a : Fin (k + 1)) :
    (x.insertArc a).contract a = x :=
  ext_pv fun q hq => by
    have hns := skipN_lt_and_ne (a := a) hq
    rw [pv_contract _ _ hq, pv_insertArc _ _ hns.1, ite_eq_right hns.2.1, ite_eq_right hns.2.2,
      unskipN_skipN]
    simp only [joinN, unskipN, skipN]; split_ifs <;> omega

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

private theorem contractFn_of_adj_right {a b : ℕ} {φ : ℕ → ℕ} (hab : a + 2 ≤ b)
    (hφ : φ b = b + 1) : contractFn a φ (b - 2) = b - 2 + 1 := by
  rw [contractFn, erasePair_apply, skipN_of_le (by omega),
    show b - 2 + 2 = b by omega, splice_of_ne _ (by omega) (by omega), hφ,
    rejoin_of_ne _ (by omega) (by omega), unskipN_of_le (by omega)]
  omega

private theorem glueFn_of_adj_right {n d : ℕ} :
    ∀ (m : ℕ) {φ : ℕ → ℕ}, φ (n + 2 * m + d) = n + 2 * m + d + 1 →
      glueFn n m φ (n + d) = n + d + 1
  | 0, _, h => by simpa [glueFn] using h
  | m + 1, φ, h =>
    glueFn_of_adj_right m (φ := contractFn (n + m) φ) <| by
      have h' := contractFn_of_adj_right (a := n + m) (b := n + 2 * (m + 1) + d) (by omega) h
      rwa [show n + 2 * (m + 1) + d - 2 = n + 2 * m + d by omega] at h'

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
  let z : PlanarMatching (n + m + (m + p) + 2) := x.insertArc a
  let w : PlanarMatching (n + (p + 2)) := glueMiddle (n := n) (p := p + 2) m (cast (by omega) z)
  let w' : PlanarMatching (n + p + 2) := cast (by omega) w
  have hz_arc : pv z (n + 2 * m + r) = n + 2 * m + r + 1 :=
    (val_castSucc_eq_succ_iff z a).mp (insertArc_val_castSucc x a)
  have hw_arc : glueFn n m (pv z) (n + r) = n + r + 1 := glueFn_of_adj_right m hz_arc
  have hzc : contractFn (n + 2 * m + r) (pv z) = pv x := by
    rw [← pv_contract_eq z a, contract_insertArc]
  obtain ⟨hfn, hcirc⟩ := glueFn_glueFn (n := n) (j := 1) m r (n + m + (m + p) + 2) z (by omega)
  simp only [glueFn, glueCircles, add_zero, zero_add] at hfn hcirc
  rw [hzc] at hfn hcirc
  have hw'_contract : w'.contract b = glueMiddle m x := eq_of_pv_eq <| by
    rw [pv_contract_eq w' b, pv_cast_eq, pv_glueMiddle, pv_cast_eq, ← hfn, pv_glueMiddle]
  have hw'_arc : w'.1.val b.castSucc = b.succ := (val_castSucc_eq_succ_iff w' b).mpr <| by
    rw [pv_cast_eq, pv_glueMiddle, pv_cast_eq]; exact hw_arc
  refine ⟨?_, ?_⟩
  · have h : w' = (glueMiddle m x).insertArc b := by
      rw [← hw'_contract, insertArc_contract hw'_arc]
    rw [← h]; simp [w', w, z, a]
  · rw [glueMiddleCircles_eq, pv_cast_eq, glueMiddleCircles_eq]
    have hc₁ : circleInd (n + 2 * m + r) (pv z) = 1 := by simp [circleInd, hz_arc]
    have hc₂ : circleInd (n + r) (glueFn n m (pv z)) = 1 := by simp [circleInd, hw_arc]
    dsimp only [z, a] at hcirc hc₁ hc₂
    omega

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
@[simp]
theorem matching_insertTopArc (D : TLDiagram n q) (c : Fin (q + 1)) :
    (D.insertTopArc c).matching =
      PlanarMatching.cast (by omega) (D.matching.insertArc ⟨n + (q - c), by omega⟩) := (rfl)

/-- The matching of `D.insertBottomArc c` inserts an adjacent arc at position `c` on the bottom
boundary. -/
@[simp]
theorem matching_insertBottomArc (D : TLDiagram q m) (c : Fin (q + 1)) :
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
@[simp]
theorem insertTopArc_id (c : Fin (q + 1)) : (id q).insertTopArc c = cupAt c := (rfl)

/-- Inserting a bottom arc into `id q` gives `capAt c`. -/
@[simp]
theorem insertBottomArc_id (c : Fin (q + 1)) : (id q).insertBottomArc c = capAt c := by
  rw [insertBottomArc, verticalReflect_id, insertTopArc_id, capAt]

/-- The matching of `cupAt c` inserts an adjacent arc into `PlanarMatching.nested q` at
`q + (q - c)`. -/
@[simp]
theorem matching_cupAt (c : Fin (q + 1)) :
    (cupAt c).matching =
      PlanarMatching.cast (by omega)
        ((PlanarMatching.nested q).insertArc ⟨q + (q - c), by omega⟩) := by
  rw [cupAt, matching_insertTopArc, matching_id]

/-- The matching of `capAt c` inserts an adjacent arc into `PlanarMatching.nested q` at `c`. -/
@[simp]
theorem matching_capAt (c : Fin (q + 1)) :
    (capAt c).matching =
      PlanarMatching.cast (by omega) ((PlanarMatching.nested q).insertArc ⟨c, by omega⟩) := by
  rw [← insertBottomArc_id, matching_insertBottomArc, matching_id]

@[simp]
theorem circles_insertTopArc (D : TLDiagram n q) (c : Fin (q + 1)) :
    (D.insertTopArc c).circles = D.circles := (rfl)

@[simp]
theorem circles_insertBottomArc (D : TLDiagram q m) (c : Fin (q + 1)) :
    (D.insertBottomArc c).circles = D.circles := by
  rw [insertBottomArc, circles_verticalReflect, circles_insertTopArc, circles_verticalReflect]

@[simp]
theorem circles_cupAt (c : Fin (q + 1)) : (cupAt c).circles = 0 := by
  rw [← insertTopArc_id, circles_insertTopArc, circles_id]

@[simp]
theorem circles_capAt (c : Fin (q + 1)) : (capAt c).circles = 0 := by
  rw [capAt, circles_verticalReflect, circles_cupAt]

/-- Vertically reflecting `D.insertTopArc c` inserts a bottom arc at `c` into the reflected
diagram. -/
@[simp]
theorem verticalReflect_insertTopArc (D : TLDiagram n q) (c : Fin (q + 1)) :
    verticalReflect n (q + 2) (D.insertTopArc c) = (verticalReflect n q D).insertBottomArc c := by
  rw [insertBottomArc, verticalReflect_verticalReflect]

/-- Vertically reflecting `D.insertBottomArc c` inserts a top arc at `c` into the reflected
diagram. -/
@[simp]
theorem verticalReflect_insertBottomArc (D : TLDiagram q m) (c : Fin (q + 1)) :
    verticalReflect (q + 2) m (D.insertBottomArc c) = (verticalReflect q m D).insertTopArc c := by
  rw [insertBottomArc, verticalReflect_verticalReflect]

@[simp]
theorem verticalReflect_cupAt (c : Fin (q + 1)) :
    verticalReflect q (q + 2) (cupAt c) = capAt c := (rfl)

@[simp]
theorem verticalReflect_capAt (c : Fin (q + 1)) :
    verticalReflect (q + 2) q (capAt c) = cupAt c := verticalReflect_verticalReflect (cupAt c)

@[simp]
theorem cupAt_zero : cupAt (0 : Fin 1) = cup :=
  TLDiagram.ext (PlanarMatching.ext fun i => by
    rw [matching_cupAt, cup_matching_val, PlanarMatching.cast_refl, Equiv.refl_apply,
      Subsingleton.elim (⟨0 + (0 - (0 : Fin 1)), by omega⟩ : Fin 1) 0]
    fin_cases i
    · exact PlanarMatching.insertArc_val_castSucc _ 0
    · exact PlanarMatching.insertArc_val_succ _ 0) (by rw [circles_cupAt, circles_cup])

@[simp]
theorem capAt_zero : capAt (0 : Fin 1) = cap := by rw [capAt, cupAt_zero, verticalReflect_cup]

/-- Pre-composing (composing on the left) commutes with inserting a top arc: the inserted top arc
lies away from the middle junction, so gluing across the middle leaves it untouched and closes the
same circles. -/
theorem comp_insertTopArc (f : TLDiagram n m) (g : TLDiagram m q) (c : Fin (q + 1)) :
    f.comp (g.insertTopArc c) = (f.comp g).insertTopArc c := by
  have _ := c.isLt
  have happ : f.matching.append (g.insertTopArc c).matching =
      PlanarMatching.cast (by omega)
        ((f.matching.append g.matching).insertArc ⟨n + 2 * m + (q - c), by omega⟩) := by
    calc f.matching.append (g.insertTopArc c).matching
        = (PlanarMatching.cast rfl f.matching).append
            (PlanarMatching.cast (by omega)
              (g.matching.insertArc ⟨m + (q - c), by omega⟩)) := by
          simp only [matching_insertTopArc, PlanarMatching.cast_refl, Equiv.refl_apply]
      _ = PlanarMatching.cast (by omega)
            (f.matching.append (g.matching.insertArc ⟨m + (q - c), by omega⟩)) :=
          PlanarMatching.append_cast rfl (by omega) _ _
      _ = _ := by rw [PlanarMatching.append_insertArc]; congr 2; ext; dsimp; omega
  obtain ⟨hm, hcirc⟩ := PlanarMatching.glueMiddle_insertArc_right (n := n) (p := q)
    (r := q - c) (by omega) m (f.matching.append g.matching)
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
@[simp]
theorem bottomHalf_insertTopArc_val (D : TLDiagram n q) (c : Fin (q + 1)) :
    (D.insertTopArc c).bottomHalf.val = D.bottomHalf.val := by
  have _ := c.isLt; ext i; have _ := i.isLt
  have hpv₁ : ((D.insertTopArc c).matching.1.val (i.castAdd (q + 2)) : ℕ) =
      PlanarMatching.pv (D.insertTopArc c).matching i := by
    rw [← PlanarMatching.pv_coe, Fin.val_castAdd]
  have hpv₂ : (D.matching.1.val (i.castAdd q) : ℕ) = PlanarMatching.pv D.matching i := by
    rw [← PlanarMatching.pv_coe, Fin.val_castAdd]
  have hpv_eq : PlanarMatching.pv (D.insertTopArc c).matching i =
      PlanarMatching.skipN (n + (q - c)) (PlanarMatching.pv D.matching i) := by
    rw [matching_insertTopArc, PlanarMatching.pv_cast, PlanarMatching.pv_insertArc _ _ (by omega)]
    dsimp only
    rw [ite_eq_right (by omega), ite_eq_right (by omega), PlanarMatching.unskipN_of_lt (by omega)]
  rw [bottomHalf_apply, bottomHalf_apply]
  simp only [hpv₁, hpv₂, hpv_eq, PlanarMatching.skipN]
  split_ifs <;> dsimp only <;> omega

/-- Inserting a top arc does not change the number of through strands. -/
@[simp]
theorem through_insertTopArc (D : TLDiagram n q) (c : Fin (q + 1)) :
    (D.insertTopArc c).through = D.through :=
  through_eq_of_bottomHalf_val_eq (bottomHalf_insertTopArc_val D c)

/-- Inserting a bottom arc does not change the number of through strands. -/
@[simp]
theorem through_insertBottomArc (D : TLDiagram q m) (c : Fin (q + 1)) :
    (D.insertBottomArc c).through = D.through := by
  rw [insertBottomArc, through_verticalReflect, through_insertTopArc, through_verticalReflect]

/-- Inserting a bottom arc leaves the top half-diagram unchanged. -/
@[simp]
theorem topHalf_insertBottomArc_val (D : TLDiagram q m) (c : Fin (q + 1)) :
    (D.insertBottomArc c).topHalf.val = D.topHalf.val := by
  rw [insertBottomArc, topHalf_verticalReflect_val, bottomHalf_insertTopArc_val, ← topHalf_val]

/-- The bottom half-diagram of `D.insertBottomArc c` joins `c.castSucc` to `c.succ`. -/
@[simp]
theorem bottomHalf_insertBottomArc_val_castSucc (D : TLDiagram q m) (c : Fin (q + 1)) :
    (D.insertBottomArc c).bottomHalf.val c.castSucc = c.succ := by
  have _ := c.isLt
  have hpv : ((D.insertBottomArc c).matching.1.val (c.castSucc.castAdd m) : ℕ) = (c : ℕ) + 1 := by
    rw [← PlanarMatching.pv_coe, Fin.val_castAdd, Fin.val_castSucc, matching_insertBottomArc,
      PlanarMatching.pv_cast, PlanarMatching.pv_insertArc _ _ (by omega)]
    simp
  apply Fin.ext
  rw [bottomHalf_apply]
  simp only [hpv, show (c : ℕ) + 1 < q + 2 by omega, dite_true, Fin.val_succ]

/-- The bottom half-diagram of `D.insertBottomArc c` joins `c.succ` to `c.castSucc`. -/
@[simp]
theorem bottomHalf_insertBottomArc_val_succ (D : TLDiagram q m) (c : Fin (q + 1)) :
    (D.insertBottomArc c).bottomHalf.val c.succ = c.castSucc := by
  rw [← bottomHalf_insertBottomArc_val_castSucc D c,
    (Equiv.Perm.isHalfDiagram_iff.mp (D.insertBottomArc c).bottomHalf.2.1).1 c.castSucc]

/-- Away from the inserted arc, the bottom half-diagram of `D.insertBottomArc c` acts as
`D.bottomHalf` conjugated by skipping the two inserted positions. -/
@[simp]
theorem bottomHalf_insertBottomArc_val_succAbove_succAbove (D : TLDiagram q m) (c : Fin (q + 1))
    (i : Fin q) :
    (D.insertBottomArc c).bottomHalf.val (c.castSucc.succAbove (c.succAbove i)) =
      c.castSucc.succAbove (c.succAbove (D.bottomHalf.val i)) := by
  have _ := c.isLt; have _ := i.isLt
  have hns := PlanarMatching.skipN_lt_and_ne (a := c) i.isLt
  have hs : ((c.castSucc.succAbove (c.succAbove i) : Fin (q + 2)) : ℕ) =
      PlanarMatching.skipN c i := PlanarMatching.coe_skip_eq_skipN c i
  have hs' : ((c.castSucc.succAbove (c.succAbove (D.bottomHalf.val i)) : Fin (q + 2)) : ℕ) =
      PlanarMatching.skipN c (D.bottomHalf.val i) := PlanarMatching.coe_skip_eq_skipN c _
  have hpv₁ : ((D.insertBottomArc c).matching.1.val
      ((c.castSucc.succAbove (c.succAbove i)).castAdd m) : ℕ) =
      PlanarMatching.skipN c (PlanarMatching.pv D.matching i) := by
    rw [← PlanarMatching.pv_coe, Fin.val_castAdd, hs, matching_insertBottomArc,
      PlanarMatching.pv_cast, PlanarMatching.pv_insertArc _ _ (by omega)]
    dsimp only
    rw [ite_eq_right hns.2.1, ite_eq_right hns.2.2, PlanarMatching.unskipN_skipN]
  have hpv₂ : (D.matching.1.val (i.castAdd m) : ℕ) = PlanarMatching.pv D.matching i := by
    rw [← PlanarMatching.pv_coe, Fin.val_castAdd]
  apply Fin.ext
  rw [bottomHalf_apply, hs', bottomHalf_apply]
  simp only [hpv₁, hpv₂]
  by_cases hlt : PlanarMatching.pv D.matching i < q
  · have hlt' : PlanarMatching.skipN c (PlanarMatching.pv D.matching i) < q + 2 :=
      (PlanarMatching.skipN_lt_and_ne (a := c) hlt).1
    simp only [hlt, hlt', dite_true]
  · have hge : ¬ PlanarMatching.skipN c (PlanarMatching.pv D.matching i) < q + 2 := by
      rw [PlanarMatching.skipN_of_le (by omega)]; omega
    simp only [hlt, hge, dite_false, hs]

/-- The top half-diagram of `D.insertTopArc c` joins `c.castSucc` to `c.succ`. -/
@[simp]
theorem topHalf_insertTopArc_val_castSucc (D : TLDiagram n q) (c : Fin (q + 1)) :
    (D.insertTopArc c).topHalf.val c.castSucc = c.succ := by
  rw [topHalf_val, verticalReflect_insertTopArc, bottomHalf_insertBottomArc_val_castSucc]

/-- The top half-diagram of `D.insertTopArc c` joins `c.succ` to `c.castSucc`. -/
@[simp]
theorem topHalf_insertTopArc_val_succ (D : TLDiagram n q) (c : Fin (q + 1)) :
    (D.insertTopArc c).topHalf.val c.succ = c.castSucc := by
  rw [topHalf_val, verticalReflect_insertTopArc, bottomHalf_insertBottomArc_val_succ]

/-- Away from the inserted arc, the top half-diagram of `D.insertTopArc c` acts as `D.topHalf`
conjugated by skipping the two inserted positions. -/
@[simp]
theorem topHalf_insertTopArc_val_succAbove_succAbove (D : TLDiagram n q) (c : Fin (q + 1))
    (j : Fin q) :
    (D.insertTopArc c).topHalf.val (c.castSucc.succAbove (c.succAbove j)) =
      c.castSucc.succAbove (c.succAbove (D.topHalf.val j)) := by
  rw [topHalf_val, verticalReflect_insertTopArc,
    bottomHalf_insertBottomArc_val_succAbove_succAbove, ← topHalf_val]

@[simp]
theorem through_cupAt (c : Fin (q + 1)) : (cupAt c).through = q := by
  rw [← insertTopArc_id, through_insertTopArc, through_id]

@[simp]
theorem through_capAt (c : Fin (q + 1)) : (capAt c).through = q := by
  rw [capAt, through_verticalReflect, through_cupAt]

/-- The bottom half-diagram of `cupAt c` has no arcs. -/
@[simp]
theorem bottomHalf_cupAt_val (c : Fin (q + 1)) : (cupAt c).bottomHalf.val = 1 := by
  rw [← insertTopArc_id, bottomHalf_insertTopArc_val, bottomHalf_id_val]

/-- The top half-diagram of `capAt c` has no arcs. -/
@[simp]
theorem topHalf_capAt_val (c : Fin (q + 1)) : (capAt c).topHalf.val = 1 := by
  rw [← insertBottomArc_id, topHalf_insertBottomArc_val, topHalf_id_val]

/-- The bottom half-diagram of `capAt c` has a single arc joining `c.castSucc` and `c.succ`. -/
@[simp]
theorem bottomHalf_capAt_val (c : Fin (q + 1)) :
    (capAt c).bottomHalf.val = Equiv.swap c.castSucc c.succ := by
  ext j
  by_cases h₁ : j = c.castSucc
  · subst h₁; rw [← insertBottomArc_id, bottomHalf_insertBottomArc_val_castSucc, swap_apply_left]
  by_cases h₂ : j = c.succ
  · subst h₂; rw [← insertBottomArc_id, bottomHalf_insertBottomArc_val_succ, swap_apply_right]
  rw [← PlanarMatching.skip_unskip c j ⟨h₁, h₂⟩,
    swap_apply_of_ne_of_ne (PlanarMatching.skip_ne_castSucc c _) (PlanarMatching.skip_ne_succ c _),
    PlanarMatching.skip, ← insertBottomArc_id, bottomHalf_insertBottomArc_val_succAbove_succAbove,
    bottomHalf_id_val, Perm.one_apply]

/-- The top half-diagram of `cupAt c` has a single arc joining `c.castSucc` and `c.succ`. -/
@[simp]
theorem topHalf_cupAt_val (c : Fin (q + 1)) :
    (cupAt c).topHalf.val = Equiv.swap c.castSucc c.succ := by
  rw [topHalf_val, verticalReflect_cupAt, bottomHalf_capAt_val]

/-- If a diagram `D : n → q + 2` has an arc joining the consecutive top points `c.castSucc` and
`c.succ`, it is obtained by post-composing a diagram `D' : n → q` with `cupAt c`. -/
theorem exists_comp_cupAt_of_topHalf_apply_eq {D : TLDiagram n (q + 2)} {c : Fin (q + 1)}
    (h : D.topHalf.val c.castSucc = c.succ) :
    ∃ D' : TLDiagram n q, D'.through = D.through ∧ D'.circles = D.circles ∧
      D'.comp (cupAt c) = D := by
  have _ := c.isLt
  let a : Fin (n + q + 1) := ⟨n + (q - c), by omega⟩
  let y : PlanarMatching (n + q + 2) := PlanarMatching.cast (by omega) D.matching
  have hy : y.1.val a.castSucc = a.succ := by
    let b : Fin (n + (q + 2)) := ⟨n + (q + 2) - 1 - c, by omega⟩
    have htop := congrArg Fin.val ((D.topHalf_apply c.castSucc).symm.trans h)
    simp only [Fin.val_castSucc, Fin.val_succ] at htop
    have hb_lt := (D.matching.1.val b).isLt
    have hb_eq : D.matching.1.val b = ⟨n + (q - c), by omega⟩ := Fin.ext <| by
      dsimp only [b] at hb_lt ⊢
      split_ifs at htop <;> simp only [Fin.val_castSucc] at htop <;> omega
    have hpva : PlanarMatching.pv D.matching (n + (q - c)) = n + (q + 2) - 1 - c := by
      rw [PlanarMatching.pv_of_lt D.matching (by omega), ← hb_eq, D.matching.1.apply_apply]
    exact (PlanarMatching.val_castSucc_eq_succ_iff y a).mpr <| by
      dsimp only [y, a]; rw [PlanarMatching.pv_cast, hpva]; omega
  have hd : (⟨y.contract a, D.circles⟩ : TLDiagram n q).insertTopArc c = D :=
    TLDiagram.ext
      (by rw [matching_insertTopArc, PlanarMatching.insertArc_contract hy]; simp [y]) rfl
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

private theorem pv_cupAt_matching (q : ℕ) (c : Fin (q + 1)) {w : ℕ} (hw : w < q + (q + 2)) :
    PlanarMatching.pv (cupAt c).matching w =
      if w < c then 2 * q + 1 - w
      else if w < q + (q - c) then 2 * q - 1 - w
      else if w = q + (q - c) then q + (q - c) + 1
      else if w = q + (q - c) + 1 then q + (q - c)
      else 2 * q + 1 - w := by
  have _ := c.isLt
  rw [matching_cupAt, PlanarMatching.pv_cast, PlanarMatching.pv_insertArc _ _ (by omega)]
  dsimp only
  by_cases h₁ : w = q + (q - c)
  · simp only [h₁, ite_true]; split_ifs <;> omega
  by_cases h₂ : w = q + (q - c) + 1
  · simp only [h₂, show q + (q - (c : ℕ)) + 1 ≠ q + (q - c) by omega, ite_false, ite_true]
    split_ifs <;> omega
  rw [ite_eq_right h₁, ite_eq_right h₂,
    PlanarMatching.pv_nested q (by simp only [PlanarMatching.unskipN]; split_ifs <;> omega)]
  simp only [PlanarMatching.skipN, PlanarMatching.unskipN]; split_ifs <;> omega

private theorem matching_cupAt_zero (q : ℕ) :
    (cupAt (0 : Fin (q + 1))).matching =
      PlanarMatching.cast (by omega) ((PlanarMatching.nested q).append cup.matching) := by
  have hcup : cup.matching = (PlanarMatching.nested 0).insertArc 0 := by
    rw [← cupAt_zero, matching_cupAt, PlanarMatching.cast_refl, Equiv.refl_apply,
      Subsingleton.elim (⟨0 + (0 - (0 : Fin 1)), by omega⟩ : Fin 1) 0]
  have h0 : (PlanarMatching.nested q).append (PlanarMatching.nested 0) =
      PlanarMatching.cast (by omega) (PlanarMatching.nested q) :=
    PlanarMatching.ext_pv fun w hw => by
      rw [PlanarMatching.pv_append_left _ _ (by omega), PlanarMatching.pv_cast]
  have hidx : (⟨q + q + (0 : Fin 1), by omega⟩ : Fin (q + q + 0 + 1)) =
      Fin.cast (by omega) (⟨q + (q - (0 : Fin (q + 1))), by omega⟩ : Fin (q + q + 1)) := by
    ext; simp
  rw [hcup, PlanarMatching.append_insertArc, h0, hidx, ← PlanarMatching.cast_insertArc (by omega),
    PlanarMatching.cast_cast, matching_cupAt]

private theorem matching_capAt_zero (q : ℕ) :
    (capAt (0 : Fin (q + 1))).matching =
      PlanarMatching.cast (by omega) (cap.matching.append (PlanarMatching.nested q)) := by
  have hcap : PlanarMatching.reflect (0 + 2) cup.matching = cap.matching := by
    have h := congrArg TLDiagram.matching verticalReflect_cup
    rwa [matching_verticalReflect, PlanarMatching.cast_refl, Equiv.refl_apply] at h
  have hrefl : PlanarMatching.reflect (q + q) (PlanarMatching.nested q) =
      PlanarMatching.nested q := by
    have h := congrArg TLDiagram.matching (verticalReflect_id q)
    rwa [matching_verticalReflect, matching_id, PlanarMatching.cast_refl, Equiv.refl_apply] at h
  rw [capAt, matching_verticalReflect, matching_cupAt_zero, ← PlanarMatching.cast_reflect,
    PlanarMatching.cast_cast, PlanarMatching.reflect_append, PlanarMatching.cast_cast, hcap, hrefl]

private theorem cupAt_zero_comp_capAt_zero (q : ℕ) :
    (cupAt (0 : Fin (q + 1))).comp (capAt (0 : Fin (q + 1))) = ⟨PlanarMatching.nested q, 1⟩ := by
  open PlanarMatching in
  have hmid_fn : glueFn 0 2 (pv (cup.matching.append cap.matching)) = pv (nested 0) := by
    rw [← pv_glueMiddle 2, ← matching_comp, cup_comp_cap, matching_id]
  have hmid_c : glueCircles 0 2 (pv (cup.matching.append cap.matching)) = 1 := by
    have hc := congrArg TLDiagram.circles cup_comp_cap
    rw [circles_comp, circles_cup, circles_cap, zero_add, zero_add, glueMiddleCircles_eq] at hc
    exact hc
  have hL := glueFn_appendFn_left (n := 0) (nested q) 2 4 (cup.matching.append cap.matching)
    (by omega)
  have hR := glueFn_appendFn_right (n := 0) (nested q) 2 (4 + (q + q))
    ((cup.matching.append cap.matching).append (nested q)) (by omega)
  simp only [add_zero] at hR
  have h0_app : appendFn 0 (q + q) (pv (nested 0)) (pv (nested q)) = pv (nested q) := by
    rw [← pv_append_eq]
    exact funext fun w => by
      by_cases hw : w < q + q
      · rw [pv_append_right _ _ (by omega) (by omega), zero_add, Nat.sub_zero]
      · rw [pv_of_le _ (by omega), pv_of_le _ (by omega)]
  have happ : pv ((cupAt (0 : Fin (q + 1))).matching.append (capAt (0 : Fin (q + 1))).matching) =
      appendFn (q + q) (4 + (q + q)) (pv (nested q))
        (pv ((cup.matching.append cap.matching).append (nested q))) := by
    rw [matching_cupAt_zero, matching_capAt_zero,
      append_cast (by omega : q + q + 2 = q + (q + 2)) (by omega : 2 + (q + q) = q + 2 + q),
      pv_cast_eq, pv_append_eq, pv_append_eq, pv_append_eq, pv_append_eq, pv_append_eq,
      appendFn_assoc, ← appendFn_assoc 2 2 (q + q), ← Nat.add_assoc 2 2 (q + q)]
  have hstep : glueFn (q + q) 2
      (pv ((cupAt (0 : Fin (q + 1))).matching.append (capAt (0 : Fin (q + 1))).matching)) =
      pv ((nested q).append (nested q)) := by
    rw [happ, ← hR.1, pv_append_eq, ← hL.1, hmid_fn, h0_app,
      show 4 + (q + q) - 2 * 2 = q + q by omega, ← pv_append_eq]
  have hstep_c : glueCircles (q + q) 2
      (pv ((cupAt (0 : Fin (q + 1))).matching.append (capAt (0 : Fin (q + 1))).matching)) = 1 := by
    rw [happ, hR.2, pv_append_eq, hL.2, hmid_c]
  have hglue_unfold : ∀ φ : ℕ → ℕ, glueFn q (q + 2) φ = glueFn q q (glueFn (q + q) 2 φ) :=
    fun φ => by simp only [glueFn, Nat.add_assoc, add_zero]
  have hcirc_unfold : ∀ φ : ℕ → ℕ,
      glueCircles q (q + 2) φ = glueCircles q q (glueFn (q + q) 2 φ) + glueCircles (q + q) 2 φ :=
    fun φ => by simp only [glueFn, glueCircles, Nat.add_assoc, add_zero, zero_add]
  exact TLDiagram.ext (eq_of_pv_eq <| by
      rw [matching_comp, pv_glueMiddle, hglue_unfold, hstep, ← pv_glueMiddle,
        glueMiddle_append_nested])
    (by rw [circles_comp, circles_cupAt, circles_capAt, zero_add, zero_add, glueMiddleCircles_eq,
          hcirc_unfold, hstep, hstep_c, ← glueMiddleCircles_eq, glueMiddleCircles_append_nested,
          zero_add])

/-- `IsWrapped y x` means `y` has `k + 2` boundary points and is obtained from `x` by wrapping an
outer arc `{0, k + 1}` around `x` and shifting the `k` points of `x` into `1, ..., k`. -/
private structure IsWrapped {K k : ℕ} (y : PlanarMatching K) (x : PlanarMatching k) : Prop where
  card_eq : K = k + 2
  pv_zero : PlanarMatching.pv y 0 = k + 1
  pv_succ : ∀ i < k, PlanarMatching.pv y (i + 1) = PlanarMatching.pv x i + 1

private theorem IsWrapped.cast {K K' k k' : ℕ} (hK : K = K') (hk : k = k')
    {y : PlanarMatching K} {x : PlanarMatching k} (h : IsWrapped y x) :
    IsWrapped (PlanarMatching.cast hK y) (PlanarMatching.cast hk x) := by
  subst hK; subst hk; simpa using h

private theorem IsWrapped.pv_last {K k : ℕ} {y : PlanarMatching K} {x : PlanarMatching k}
    (h : IsWrapped y x) : PlanarMatching.pv y (k + 1) = 0 := by
  have := h.card_eq; rw [← h.pv_zero, PlanarMatching.pv_pv y (by omega)]

private theorem IsWrapped.reflect {K k : ℕ} {y : PlanarMatching K} {x : PlanarMatching k}
    (h : IsWrapped y x) :
    IsWrapped (PlanarMatching.reflect K y) (PlanarMatching.reflect k x) := by
  have _ := h.card_eq
  refine ⟨h.card_eq, ?_, fun i hi => ?_⟩
  · rw [PlanarMatching.pv_reflect _ (by omega), show K - 1 - 0 = k + 1 by omega, h.pv_last]; omega
  · have _ := PlanarMatching.pv_lt x (q := k - 1 - i) (by omega)
    rw [PlanarMatching.pv_reflect _ (by omega), PlanarMatching.pv_reflect _ hi,
      show K - 1 - (i + 1) = k - 1 - i + 1 by omega, h.pv_succ _ (by omega)]; omega

private theorem IsWrapped.eq_nested {q : ℕ} {y : PlanarMatching ((q + 1) + (q + 1))}
    (h : IsWrapped y (PlanarMatching.nested q)) : y = PlanarMatching.nested (q + 1) :=
  PlanarMatching.ext_pv fun w hw => by
    by_cases hw₀ : w = 0
    · rw [hw₀, h.pv_zero, PlanarMatching.pv_nested _ (by omega)]; omega
    by_cases hwl : w = 2 * q + 1
    · rw [hwl, show 2 * q + 1 = q + q + 1 by omega, h.pv_last,
        PlanarMatching.pv_nested _ (by omega)]; omega
    have hi := h.pv_succ (w - 1) (by omega)
    rw [show w - 1 + 1 = w by omega] at hi
    rw [hi, PlanarMatching.pv_nested _ (by omega), PlanarMatching.pv_nested _ hw]; omega

private theorem IsWrapped.contract_succ {K k : ℕ} {y : PlanarMatching (K + 2)}
    {x : PlanarMatching (k + 2)} (h : IsWrapped y x)
    (a' : Fin (K + 1)) (a : Fin (k + 1)) (ha' : (a' : ℕ) = (a : ℕ) + 1) :
    IsWrapped (y.contract a') (x.contract a) ∧
      ((y.1.val ⟨a', by omega⟩ = ⟨(a' : ℕ) + 1, by omega⟩) ↔
        x.1.val ⟨a, by omega⟩ = ⟨(a : ℕ) + 1, by omega⟩) := by
  have _ := a.isLt; have _ := h.card_eq
  refine ⟨⟨by omega, ?_, fun i hi => ?_⟩, ?_⟩
  · rw [PlanarMatching.pv_contract _ _ (by omega), ha', PlanarMatching.skipN_of_lt (by omega)]
    simp only [PlanarMatching.joinN, h.pv_zero, show k + 2 + 1 ≠ (a : ℕ) + 1 by omega,
      show k + 2 + 1 ≠ (a : ℕ) + 1 + 1 by omega, ite_false, PlanarMatching.unskipN]
    split_ifs <;> omega
  · set s := PlanarMatching.skipN a i
    have hs : s < k + 2 ∧ s ≠ a ∧ s ≠ (a : ℕ) + 1 := PlanarMatching.skipN_lt_and_ne hi
    rw [PlanarMatching.pv_contract _ _ (by omega), PlanarMatching.pv_contract _ _ hi, ha',
      show PlanarMatching.skipN ((a : ℕ) + 1) (i + 1) = s + 1 by
        simp only [s, PlanarMatching.skipN]; split_ifs <;> omega, h.pv_succ s hs.1]
    have hjoin : PlanarMatching.joinN y ((a : ℕ) + 1) (PlanarMatching.pv x s + 1) =
        PlanarMatching.joinN x a (PlanarMatching.pv x s) + 1 := by
      simp only [PlanarMatching.joinN]
      rw [h.pv_succ a (by omega), h.pv_succ ((a : ℕ) + 1) (by omega)]; split_ifs <;> omega
    obtain ⟨hw₁, hw₂⟩ := PlanarMatching.joinN_pv_ne x a hs.2.1 hs.2.2
    rw [hjoin]
    suffices ∀ w : ℕ, w ≠ a → w ≠ (a : ℕ) + 1 →
        PlanarMatching.unskipN ((a : ℕ) + 1) (w + 1) = PlanarMatching.unskipN a w + 1 from
      this _ hw₁ hw₂
    intro w _ _; simp only [PlanarMatching.unskipN]; split_ifs <;> omega
  · rw [PlanarMatching.val_mk_eq_mk_iff, PlanarMatching.val_mk_eq_mk_iff, ha',
      h.pv_succ a (by omega)]
    omega

private theorem IsWrapped.glueMiddle {n p : ℕ} :
    ∀ (m : ℕ) {y : PlanarMatching ((n + 1) + m + (m + (p + 1)))}
      {x : PlanarMatching (n + m + (m + p))},
      IsWrapped y x →
        IsWrapped (PlanarMatching.glueMiddle m y) (PlanarMatching.glueMiddle m x) ∧
        PlanarMatching.glueMiddleCircles (n := n + 1) (p := p + 1) m y =
          PlanarMatching.glueMiddleCircles (n := n) (p := p) m x
  | 0, _, _, h => ⟨h.cast (by omega) (by omega), rfl⟩
  | m + 1, _, _, h => by
    obtain ⟨hc, hind⟩ := (h.cast
      (K' := (n + 1) + m + (m + (p + 1)) + 2) (k' := n + m + (m + p) + 2)
      (by omega) (by omega)).contract_succ
      ⟨(n + 1) + m, by omega⟩ ⟨n + m, by omega⟩ (by dsimp; omega)
    obtain ⟨ih₁, ih₂⟩ := IsWrapped.glueMiddle m hc
    refine ⟨by rw [PlanarMatching.glueMiddle_succ, PlanarMatching.glueMiddle_succ]; exact ih₁, ?_⟩
    rw [PlanarMatching.glueMiddleCircles_succ (n := n + 1) (p := p + 1),
      PlanarMatching.glueMiddleCircles_succ (n := n) (p := p), ih₂]
    simp only [hind]

private theorem IsWrapped.append_contract_mid {n m p : ℕ}
    {f' : PlanarMatching ((n + 1) + (m + 1))} {f : PlanarMatching (n + m)}
    {g' : PlanarMatching ((m + 1) + (p + 1))} {g : PlanarMatching (m + p)}
    (hf : IsWrapped f' f) (hg : IsWrapped g' g) :
    IsWrapped
      ((PlanarMatching.cast (k' := (n + 1) + m + (m + (p + 1)) + 2) (by omega)
        (f'.append g')).contract ⟨(n + 1) + m, by omega⟩)
      (f.append g) ∧
    (PlanarMatching.cast (k' := (n + 1) + m + (m + (p + 1)) + 2) (by omega)
      (f'.append g')).1.val ⟨(n + 1) + m, by omega⟩ ≠ ⟨(n + 1) + m + 1, by omega⟩ := by
  let y₀ : PlanarMatching ((n + 1) + m + (m + (p + 1)) + 2) :=
    PlanarMatching.cast (by omega) (f'.append g')
  have hpva : PlanarMatching.pv y₀ ((n + 1) + m) = 0 := by
    dsimp only [y₀]; rw [PlanarMatching.pv_cast, PlanarMatching.pv_append_left _ _ (by omega),
      show (n + 1) + m = n + m + 1 by omega, hf.pv_last]
  have hpva1 : PlanarMatching.pv y₀ ((n + 1) + m + 1) = (n + 1) + (m + 1) + (m + p + 1) := by
    dsimp only [y₀]; rw [PlanarMatching.pv_cast,
      PlanarMatching.pv_append_right _ _ (by omega) (by omega),
      show (n + 1) + m + 1 - ((n + 1) + (m + 1)) = 0 by omega, hg.pv_zero]
  have hy0 : PlanarMatching.pv y₀ 0 = (n + 1) + m := by
    dsimp only [y₀]
    rw [PlanarMatching.pv_cast, PlanarMatching.pv_append_left _ _ (by omega), hf.pv_zero]; omega
  refine ⟨⟨by omega, ?_, fun i hi => ?_⟩, PlanarMatching.val_ne_of_pv_ne
    (a := ⟨(n + 1) + m, by omega⟩) (by dsimp; rw [hpva]; omega) (by dsimp; omega) (by simp)⟩
  · rw [PlanarMatching.pv_contract y₀ _ (by omega), PlanarMatching.skipN_of_lt (by dsimp; omega)]
    simp only [PlanarMatching.joinN, hy0, hpva1, ite_true, PlanarMatching.unskipN]
    split_ifs <;> omega
  · rw [PlanarMatching.pv_contract y₀ _ (by omega)]
    simp only [PlanarMatching.joinN, hpva, hpva1]
    by_cases hleft : i < n + m
    · have _ := PlanarMatching.pv_lt f hleft
      rw [PlanarMatching.skipN_of_lt (by omega)]
      dsimp only [y₀]; rw [PlanarMatching.pv_cast, PlanarMatching.pv_append_left _ _ (by omega),
        hf.pv_succ i hleft, PlanarMatching.pv_append_left _ _ hleft]
      simp only [PlanarMatching.unskipN]; split_ifs <;> omega
    · rw [PlanarMatching.skipN_of_le (by omega)]
      dsimp only [y₀]; rw [PlanarMatching.pv_cast,
        PlanarMatching.pv_append_right _ _ (by omega) (by omega),
        show i + 1 + 2 - ((n + 1) + (m + 1)) = i - (n + m) + 1 by omega,
        hg.pv_succ (i - (n + m)) (by omega), PlanarMatching.pv_append_right _ _ (by omega) hi]
      simp only [PlanarMatching.unskipN]; split_ifs <;> omega

private theorem isWrapped_cupAt_succ {q : ℕ} (c : Fin (q + 1)) :
    IsWrapped (cupAt c.succ).matching (cupAt c).matching := by
  have _ := c.isLt
  refine ⟨by omega, ?_, fun i hi => ?_⟩
  · rw [pv_cupAt_matching (q + 1) c.succ (by omega)]
    simp only [Fin.val_succ, show 0 < (c : ℕ) + 1 by omega, ite_true]; omega
  · rw [pv_cupAt_matching (q + 1) c.succ (by omega), pv_cupAt_matching q c hi]
    simp only [Fin.val_succ]; split_ifs <;> omega

private theorem isWrapped_capAt_succ {q : ℕ} (c : Fin (q + 1)) :
    IsWrapped (capAt c.succ).matching (capAt c).matching := by
  simpa only [capAt, matching_verticalReflect] using
    (isWrapped_cupAt_succ c).reflect.cast (by omega) (by omega)

/-- **A cup at position `c` followed by the matching cap closes one circle**: `cupAt c ≫ capAt c`
is the identity matching on `q` strands carrying one closed circle. -/
@[simp]
theorem cupAt_comp_capAt : ∀ {q : ℕ} (c : Fin (q + 1)),
    (cupAt c).comp (capAt c) = ⟨PlanarMatching.nested q, 1⟩
  | 0, c => Fin.cases (cupAt_zero_comp_capAt_zero 0) (fun i => i.elim0) c
  | q + 1, c => Fin.cases (cupAt_zero_comp_capAt_zero (q + 1)) (fun c => by
      obtain ⟨hstep, hne⟩ := IsWrapped.append_contract_mid
        (isWrapped_cupAt_succ c) (isWrapped_capAt_succ c)
      obtain ⟨hglue, hcirc⟩ := IsWrapped.glueMiddle (q + 2) hstep
      have ih := cupAt_comp_capAt c
      rw [show PlanarMatching.glueMiddle (q + 2) ((cupAt c).matching.append (capAt c).matching) =
        PlanarMatching.nested q by simpa [matching_comp] using congrArg TLDiagram.matching ih]
          at hglue
      exact TLDiagram.ext
        (by rw [matching_comp, PlanarMatching.glueMiddle_succ]; exact hglue.eq_nested)
        (by rw [circles_comp, circles_cupAt, circles_capAt, zero_add, zero_add,
              PlanarMatching.glueMiddleCircles_succ (n := q + 1) (p := q + 1), ite_eq_right hne,
              add_zero, hcirc]
            simpa [circles_comp] using congrArg TLDiagram.circles ih)) c

end CupCompCap

end TLDiagram

end TauCeti
