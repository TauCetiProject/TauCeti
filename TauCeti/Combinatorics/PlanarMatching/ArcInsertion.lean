/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.Compose
public import TauCeti.Combinatorics.PlanarMatching.Through
import all TauCeti.Combinatorics.PlanarMatching.Glue
import all TauCeti.Combinatorics.PlanarMatching.Compose

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
for `capAt c` follow by vertical reflection. Finally, `TauCeti.TLDiagram.cupAt_comp_capAt` shows
that `cupAt c` followed by `capAt c` closes one circle and leaves `q` straight strands.

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
* `TauCeti.TLDiagram.comp_insertTopArc`, `TauCeti.TLDiagram.comp_cupAt`,
  `TauCeti.TLDiagram.capAt_comp`: compatibility of composition with boundary arc insertion.
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

private def insertArcFun (x : PlanarMatching k) (a : Fin (k + 1)) (z : Fin (k + 2)) : Fin (k + 2) :=
  if h₁ : z = a.castSucc then a.succ
  else if h₂ : z = a.succ then a.castSucc
  else skip a (x.1.val (unskip a z ⟨h₁, h₂⟩))

private theorem insertArcFun_castSucc (x : PlanarMatching k) (a : Fin (k + 1)) :
    insertArcFun x a a.castSucc = a.succ := by simp [insertArcFun]

private theorem insertArcFun_succ (x : PlanarMatching k) (a : Fin (k + 1)) :
    insertArcFun x a a.succ = a.castSucc := by simp [insertArcFun, succ_ne_castSucc]

private theorem unskip_skip (a : Fin (k + 1)) (i : Fin k) :
    unskip a (skip a i) ⟨skip_ne_castSucc a i, skip_ne_succ a i⟩ = i :=
  (skip_strictMono a).injective (skip_unskip a _ _)

private theorem insertArcFun_skip (x : PlanarMatching k) (a : Fin (k + 1)) (i : Fin k) :
    insertArcFun x a (skip a i) = skip a (x.1.val i) := by
  simp only [insertArcFun, skip_ne_castSucc, skip_ne_succ, dite_false]; rw [unskip_skip]

private theorem insertArcFun_involutive (x : PlanarMatching k) (a : Fin (k + 1)) :
    Function.Involutive (insertArcFun x a) := fun z => by
  by_cases h₁ : z = a.castSucc
  · rw [h₁, insertArcFun_castSucc, insertArcFun_succ]
  by_cases h₂ : z = a.succ
  · rw [h₂, insertArcFun_succ, insertArcFun_castSucc]
  rw [← skip_unskip a z ⟨h₁, h₂⟩, insertArcFun_skip, insertArcFun_skip, x.1.apply_apply]

private theorem insertArcFun_ne (x : PlanarMatching k) (a : Fin (k + 1)) (z : Fin (k + 2)) :
    insertArcFun x a z ≠ z := by
  by_cases h₁ : z = a.castSucc
  · rw [h₁, insertArcFun_castSucc]; exact succ_ne_castSucc a
  by_cases h₂ : z = a.succ
  · rw [h₂, insertArcFun_succ]; exact (succ_ne_castSucc a).symm
  rw [← skip_unskip a z ⟨h₁, h₂⟩, insertArcFun_skip]
  exact (skip_strictMono a).injective.ne (x.1.apply_ne _)

private theorem insertArcFun_noncrossing (x : PlanarMatching k) (a : Fin (k + 1)) :
    (PerfectMatching.ofInvolutive (insertArcFun_involutive x a)
      (insertArcFun_ne x a)).val.IsNoncrossingMatching := by
  rw [Perm.isNoncrossingMatching_iff]
  intro u v huv hvu hlt
  simp only [PerfectMatching.ofInvolutive_apply] at hvu hlt
  by_cases hu₁ : u = a.castSucc
  · rw [hu₁] at huv hvu
    rw [insertArcFun_castSucc] at hvu
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at huv hvu
    omega
  by_cases hu₂ : u = a.succ
  · rw [hu₂] at huv hvu
    rw [insertArcFun_succ] at hvu
    exact absurd (huv.trans hvu) (not_lt_of_gt Fin.castSucc_lt_succ)
  rw [← skip_unskip a u ⟨hu₁, hu₂⟩] at huv hvu hlt
  rw [insertArcFun_skip] at hvu hlt
  set i := unskip a u ⟨hu₁, hu₂⟩
  by_cases hv₁ : v = a.castSucc
  · rw [hv₁] at hvu hlt
    rw [insertArcFun_castSucc] at hlt
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at hvu hlt
    omega
  by_cases hv₂ : v = a.succ
  · rw [hv₂] at hvu hlt
    rw [insertArcFun_succ] at hlt
    exact absurd (hvu.trans hlt) (not_lt_of_gt Fin.castSucc_lt_succ)
  rw [← skip_unskip a v ⟨hv₁, hv₂⟩] at huv hvu hlt
  rw [insertArcFun_skip] at hlt
  exact Perm.isNoncrossingMatching_iff.mp x.2
    ((skip_strictMono a).lt_iff_lt.mp huv)
    ((skip_strictMono a).lt_iff_lt.mp hvu)
    ((skip_strictMono a).lt_iff_lt.mp hlt)

/-- **Inserting an adjacent arc** `{a.castSucc, a.succ}` into a planar matching `x` of `k` points,
shifting all boundary points from `a` onwards up by two. It is a right inverse to
`TauCeti.PlanarMatching.contract`. -/
def insertArc (x : PlanarMatching k) (a : Fin (k + 1)) : PlanarMatching (k + 2) :=
  ⟨PerfectMatching.ofInvolutive (insertArcFun_involutive x a) (insertArcFun_ne x a),
    insertArcFun_noncrossing x a⟩

@[simp]
theorem insertArc_val_castSucc (x : PlanarMatching k) (a : Fin (k + 1)) :
    (x.insertArc a).1.val a.castSucc = a.succ :=
  (PerfectMatching.ofInvolutive_apply _ _ _).trans (insertArcFun_castSucc x a)

@[simp]
theorem insertArc_val_succ (x : PlanarMatching k) (a : Fin (k + 1)) :
    (x.insertArc a).1.val a.succ = a.castSucc :=
  (PerfectMatching.ofInvolutive_apply _ _ _).trans (insertArcFun_succ x a)

/-- Outside the inserted arc, `insertArc` acts on boundary points as the original planar matching
conjugated by skipping the two inserted positions. -/
theorem insertArc_val_succAbove_succAbove (x : PlanarMatching k) (a : Fin (k + 1)) (i : Fin k) :
    (x.insertArc a).1.val (a.castSucc.succAbove (a.succAbove i)) =
      a.castSucc.succAbove (a.succAbove (x.1.val i)) :=
  (PerfectMatching.ofInvolutive_apply _ _ _).trans (insertArcFun_skip x a i)

private theorem pv_insertArc (x : PlanarMatching k) (a : Fin (k + 1)) {q : ℕ} (hq : q < k + 2) :
    pv (x.insertArc a) q =
      if q = (a : ℕ) then (a : ℕ) + 1
      else if q = (a : ℕ) + 1 then (a : ℕ)
      else skipN a (pv x (unskipN a q)) := by
  by_cases h₁ : q = a
  · subst h₁
    rw [← Fin.val_castSucc a, pv_coe, insertArc_val_castSucc]
    simp
  by_cases h₂ : q = (a : ℕ) + 1
  · subst h₂
    rw [← Fin.val_succ a, pv_coe, insertArc_val_succ]
    simp
  have hz : (⟨q, hq⟩ : Fin (k + 2)) ≠ a.castSucc ∧ (⟨q, hq⟩ : Fin (k + 2)) ≠ a.succ := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
    exact ⟨h₁, h₂⟩
  set i := unskip a ⟨q, hq⟩ hz
  have hi : (i : ℕ) = unskipN a q := by simp only [i, unskip, unskipN]
  have hq_eq : (⟨q, hq⟩ : Fin (k + 2)) = skip a i := (skip_unskip a _ hz).symm
  have hskip_val : ((a.castSucc.succAbove (a.succAbove (x.1.val i))) : ℕ) =
      skipN a (x.1.val i) := coe_skip a (x.1.val i)
  dsimp only [skip] at hq_eq
  rw [pv_of_lt _ hq, hq_eq, insertArc_val_succAbove_succAbove, hskip_val, ← pv_coe, hi,
    ite_eq_right h₁, ite_eq_right h₂]

/-- Contracting the arc just inserted by `insertArc` recovers the original planar matching. -/
@[simp]
theorem contract_insertArc (x : PlanarMatching k) (a : Fin (k + 1)) :
    (x.insertArc a).contract a = x :=
  ext_pv fun q hq => by
    have hlt : skipN a q < k + 2 := by simp only [skipN]; split_ifs <;> omega
    have hns : skipN a q ≠ a ∧ skipN a q ≠ (a : ℕ) + 1 := by simp only [skipN]; split_ifs <;> omega
    have hu : unskipN a (skipN a q) = q := by simp only [unskipN, skipN]; split_ifs <;> omega
    rw [pv_contract _ _ hq, pv_insertArc _ _ hlt, ite_eq_right hns.1, ite_eq_right hns.2, hu]
    simp only [joinN, unskipN, skipN]
    split_ifs <;> omega

/-- Re-inserting an adjacent arc `{a.castSucc, a.succ}` after contracting it recovers the original
planar matching. -/
theorem insertArc_contract {x : PlanarMatching (k + 2)} {a : Fin (k + 1)}
    (h : x.1.val a.castSucc = a.succ) : (x.contract a).insertArc a = x :=
  ext_pv fun q hq => by
    have ha := a.isLt
    have hpva : pv x a = (a : ℕ) + 1 := by
      rw [← Fin.val_castSucc a, pv_coe, h, Fin.val_succ, Fin.val_castSucc]
    have hpva' : pv x ((a : ℕ) + 1) = a := by
      have := pv_pv x (q := a) (by omega)
      rwa [hpva] at this
    rw [pv_insertArc _ _ hq]
    by_cases h₁ : q = a
    · simp [h₁, hpva]
    by_cases h₂ : q = (a : ℕ) + 1
    · simp [h₂, hpva']
    have hu : unskipN a q < k := by simp only [unskipN]; split_ifs <;> omega
    have hsu : skipN a (unskipN a q) = q := by simp only [skipN, unskipN]; split_ifs <;> omega
    have hnq : pv x q ≠ a ∧ pv x q ≠ (a : ℕ) + 1 :=
      ⟨fun h' => h₂ (by rw [← pv_pv x hq, h', hpva]),
       fun h' => h₁ (by rw [← pv_pv x hq, h', hpva'])⟩
    rw [ite_eq_right h₁, ite_eq_right h₂, pv_contract _ _ hu, hsu]
    simp only [joinN, hnq.1, hnq.2, ite_false, skipN, unskipN]
    split_ifs <;> omega

/-- Reflecting a planar matching with an inserted arc inserts the reflected arc into the reflected
matching. -/
theorem reflect_insertArc (x : PlanarMatching k) (a : Fin (k + 1)) :
    reflect (k + 2) (x.insertArc a) = (reflect k x).insertArc (Fin.rev a) :=
  ext_pv fun q hq => by
    have ha := a.isLt
    have hr : (Fin.rev a : ℕ) = k - a := by simp [Fin.val_rev]
    rw [pv_reflect _ hq, pv_insertArc _ _ (by omega), pv_insertArc _ _ hq, hr]
    by_cases h₁ : k + 2 - 1 - q = a
    · rw [ite_eq_left h₁, ite_eq_right (by omega), ite_eq_left (by omega)]
      omega
    by_cases h₂ : k + 2 - 1 - q = (a : ℕ) + 1
    · rw [ite_eq_right h₁, ite_eq_left h₂, ite_eq_left (by omega)]
      omega
    have hu : unskipN (k - a) q < k := by simp only [unskipN]; split_ifs <;> omega
    have _ := pv_lt x (q := k - 1 - unskipN (k - a) q) (by omega)
    rw [ite_eq_right h₁, ite_eq_right h₂, ite_eq_right (by omega), ite_eq_right (by omega),
      show unskipN (a : ℕ) (k + 2 - 1 - q) = k - 1 - unskipN (k - a) q by
        simp only [unskipN]; split_ifs <;> omega,
      pv_reflect _ hu]
    simp only [skipN]
    split_ifs <;> omega

/-- Transport commutes with `insertArc`. -/
theorem cast_insertArc {k' : ℕ} (h : k = k') (x : PlanarMatching k) (a : Fin (k + 1)) :
    cast (congrArg (· + 2) h) (x.insertArc a) =
      (cast h x).insertArc (Fin.cast (congrArg (· + 1) h) a) := by
  subst h
  simp

/-- Juxtaposing on the left shifts the insertion position of `insertArc` on the right factor. -/
theorem append_insertArc {k l : ℕ} (x : PlanarMatching k) (y : PlanarMatching l)
    (b : Fin (l + 1)) :
    x.append (y.insertArc b) = (x.append y).insertArc ⟨k + b, by omega⟩ :=
  ext_pv fun q hq => by
    have hb := b.isLt
    by_cases hqk : q < k
    · have hpvx := pv_lt x hqk
      rw [pv_append_left _ _ hqk, pv_insertArc _ _ hq,
        ite_eq_right (by dsimp; omega), ite_eq_right (by dsimp; omega),
        show unskipN (⟨k + b, by omega⟩ : Fin (k + l + 1)) q = q by
          simp only [unskipN]; split_ifs <;> omega,
        pv_append_left _ _ hqk]
      simp only [skipN]
      split_ifs <;> omega
    · rw [pv_append_right _ _ (by omega) hq, pv_insertArc _ _ (by omega), pv_insertArc _ _ hq]
      by_cases h₁ : q = k + b
      · simp [h₁]; omega
      by_cases h₂ : q = k + b + 1
      · simp [h₂, show k + (b : ℕ) + 1 - k = (b : ℕ) + 1 by omega]
      have hu : unskipN b (q - k) < l := by simp only [unskipN]; split_ifs <;> omega
      rw [ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by dsimp; exact h₁), ite_eq_right (by dsimp; exact h₂),
        show unskipN (⟨k + b, by omega⟩ : Fin (k + l + 1)) q = k + unskipN b (q - k) by
          simp only [unskipN]; split_ifs <;> omega,
        pv_append_right _ _ (by omega) (by omega),
        show k + unskipN b (q - k) - k = unskipN b (q - k) by omega]
      simp only [skipN]
      split_ifs <;> omega

private theorem joinN_pv_ne {k : ℕ} (x : PlanarMatching (k + 2)) (a : Fin (k + 1)) {s : ℕ}
    (hsa : s ≠ a) (hsa' : s ≠ (a : ℕ) + 1) :
    joinN x a (pv x s) ≠ a ∧ joinN x a (pv x s) ≠ (a : ℕ) + 1 := by
  have _ := a.isLt
  by_cases hs : s < k + 2
  · have hne_a : pv x a ≠ a :=
      fun h => x.1.apply_ne a.castSucc (Fin.ext ((pv_coe x a.castSucc).symm.trans h))
    have hne_a' : pv x ((a : ℕ) + 1) ≠ (a : ℕ) + 1 :=
      fun h => x.1.apply_ne a.succ (Fin.ext ((pv_coe x a.succ).symm.trans h))
    simp only [joinN]
    split_ifs with h₁ h₂
    · exact ⟨fun h => hsa' <| (pv_pv x hs).symm.trans
        ((congrArg (pv x) (h₁.trans h.symm)).trans (pv_pv x (by omega))), hne_a'⟩
    · exact ⟨hne_a, fun h => hsa <| (pv_pv x hs).symm.trans
        ((congrArg (pv x) (h₂.trans h.symm)).trans (pv_pv x (by omega)))⟩
    · exact ⟨h₁, h₂⟩
  · simp only [joinN, pv, hs, dite_false]
    split_ifs <;> omega

/-- Contracting a pair `{a, a + 1}` strictly to the left of an inserted arc `{b, b + 1}` commutes
with `insertArc` (shifting `b` down by `2`). -/
private theorem contract_insertArc_of_add_two_le {k : ℕ} (x : PlanarMatching (k + 2))
    (a : Fin (k + 1)) (b : Fin (k + 3)) (hab : (a : ℕ) + 2 ≤ b) :
    (x.insertArc b).contract ⟨a, by omega⟩ = (x.contract a).insertArc ⟨b - 2, by omega⟩ :=
  ext_pv fun q hq => by
    have _ := a.isLt
    have _ := b.isLt
    rw [pv_contract _ _ hq, pv_insertArc _ _ hq]
    dsimp only
    by_cases h₁ : q = (b : ℕ) - 2
    · rw [ite_eq_left h₁, show skipN (a : ℕ) q = b by
        simp only [skipN]; split_ifs <;> omega, pv_insertArc _ _ (by omega)]
      simp only [ite_true, joinN, unskipN]
      split_ifs <;> omega
    by_cases h₂ : q = (b : ℕ) - 2 + 1
    · rw [ite_eq_right h₁, ite_eq_left h₂,
        show skipN (a : ℕ) q = (b : ℕ) + 1 by simp only [skipN]; split_ifs <;> omega,
        pv_insertArc _ _ (by omega)]
      simp only [show (b : ℕ) + 1 ≠ b by omega, ite_false, ite_true, joinN, unskipN]
      split_ifs <;> omega
    have hsq : skipN (a : ℕ) q < k + 4 ∧ skipN (a : ℕ) q ≠ b ∧ skipN (a : ℕ) q ≠ (b : ℕ) + 1 := by
      simp only [skipN]
      refine ⟨by split_ifs <;> omega, by split_ifs <;> omega, by split_ifs <;> omega⟩
    have hus : unskipN b (skipN (a : ℕ) q) = skipN a (unskipN ((b : ℕ) - 2) q) := by
      simp only [unskipN, skipN]; split_ifs <;> omega
    have hlt_u : unskipN ((b : ℕ) - 2) q < k := by simp only [unskipN]; split_ifs <;> omega
    let s := skipN a (unskipN ((b : ℕ) - 2) q)
    have hs : s < k + 2 ∧ s ≠ a ∧ s ≠ (a : ℕ) + 1 := by
      simp only [s, skipN]
      refine ⟨by split_ifs <;> omega, by split_ifs <;> omega, by split_ifs <;> omega⟩
    rw [ite_eq_right h₁, ite_eq_right h₂,
      pv_contract _ _ hlt_u, pv_insertArc _ _ hsq.1, ite_eq_right hsq.2.1, ite_eq_right hsq.2.2,
      hus]
    have hjoin : joinN (x.insertArc b) a (skipN b (pv x s)) = skipN b (joinN x a (pv x s)) := by
      have _ := pv_lt x hs.1
      have _ := pv_lt x (q := a) (by omega)
      have _ := pv_lt x (q := (a : ℕ) + 1) (by omega)
      simp only [joinN]
      rw [pv_insertArc _ _ (by omega), pv_insertArc _ _ (by omega)]
      simp only [show (a : ℕ) ≠ b by omega, show (a : ℕ) ≠ (b : ℕ) + 1 by omega,
        show (a : ℕ) + 1 ≠ b by omega, show (a : ℕ) + 1 ≠ (b : ℕ) + 1 by omega, ite_false,
        show unskipN (b : ℕ) a = a by simp only [unskipN]; split_ifs <;> omega,
        show unskipN (b : ℕ) ((a : ℕ) + 1) = (a : ℕ) + 1 by
          simp only [unskipN]; split_ifs <;> omega, skipN]
      split_ifs <;> omega
    rw [hjoin]
    have hw_ne := joinN_pv_ne x a hs.2.1 hs.2.2
    suffices ∀ w : ℕ, w ≠ a → w ≠ (a : ℕ) + 1 →
        unskipN a (skipN b w) = skipN ((b : ℕ) - 2) (unskipN a w) from
      this _ hw_ne.1 hw_ne.2
    intro w _ _
    simp only [unskipN, skipN]
    split_ifs <;> omega

private theorem insertArc_val_eq_iff_of_add_two_le {k : ℕ} (x : PlanarMatching (k + 2))
    (a : Fin (k + 1)) (b : Fin (k + 3)) (hab : (a : ℕ) + 2 ≤ b) :
    ((x.insertArc b).1.val ⟨a, by omega⟩ = ⟨(a : ℕ) + 1, by omega⟩) ↔
      x.1.val a.castSucc = a.succ := by
  have h₁ : ((x.insertArc b).1.val ⟨a, by omega⟩ = ⟨(a : ℕ) + 1, by omega⟩) ↔
      pv (x.insertArc b) a = (a : ℕ) + 1 := by
    rw [Fin.ext_iff, ← pv_of_lt _ (by omega)]
  have h₂ : (x.1.val a.castSucc = a.succ) ↔ pv x a = (a : ℕ) + 1 := by
    rw [← Fin.val_castSucc a, pv_coe, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
  rw [h₁, h₂, pv_insertArc _ _ (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  simp only [unskipN, skipN]
  split_ifs <;> omega

/-- `glueMiddle` commutes with inserting an arc strictly to the right of the glued middle block,
and closes the same number of circles. -/
private theorem glueMiddle_insertArc_right {n p r : ℕ} (hr : r ≤ p) :
    ∀ (m : ℕ) (x : PlanarMatching (n + m + (m + p))),
      glueMiddle (n := n) (p := p + 2) m
        (cast (by omega) (x.insertArc ⟨n + 2 * m + r, by omega⟩)) =
        cast (by omega) ((glueMiddle m x).insertArc ⟨n + r, by omega⟩) ∧
      glueMiddleCircles (n := n) (p := p + 2) m
        (cast (by omega) (x.insertArc ⟨n + 2 * m + r, by omega⟩)) =
        glueMiddleCircles (n := n) (p := p) m x
  | 0, x =>
    ⟨ext_pv fun q hq => by
      simp only [glueMiddle_zero, pv_cast]
      rw [pv_insertArc _ _ (by omega), pv_insertArc _ _ (by omega)]
      simp only [pv_cast, unskipN, skipN]
      split_ifs <;> omega, rfl⟩
  | m + 1, x => by
    let y : PlanarMatching (n + m + (m + p) + 2) := cast (by omega) x
    let a : Fin (n + m + (m + p) + 1) := ⟨n + m, by omega⟩
    let b : Fin (n + m + (m + p) + 3) := ⟨n + 2 * (m + 1) + r, by omega⟩
    let z : PlanarMatching (n + m + (m + (p + 2)) + 2) :=
      cast (by omega) (cast (k' := n + (m + 1) + (m + 1 + (p + 2))) (by omega)
        (x.insertArc ⟨n + 2 * (m + 1) + r, by omega⟩))
    have hc := contract_insertArc_of_add_two_le y a b (by simp [a, b]; omega)
    have hind := insertArc_val_eq_iff_of_add_two_le y a b (by simp [a, b]; omega)
    have hy : z = cast (congrArg (· + 2)
        (show n + m + (m + p) + 2 = n + m + (m + (p + 2)) by omega)) (y.insertArc b) :=
      ext_pv fun q hq => by
        dsimp only [z, y, b]
        rw [pv_cast, pv_cast, pv_cast, pv_insertArc _ _ (by omega), pv_insertArc _ _ (by omega)]
        simp only [pv_cast, unskipN, skipN]
        split_ifs <;> omega
    have hstep : z.contract ⟨n + m, by omega⟩ =
        cast (by omega) ((y.contract a).insertArc ⟨n + 2 * m + r, by omega⟩) := by
      have ha_eq : (⟨n + m, by omega⟩ : Fin (n + m + (m + (p + 2)) + 1)) =
          Fin.cast (by omega) (⟨a, by omega⟩ : Fin (n + m + (m + p) + 3)) := rfl
      rw [hy, ha_eq, cast_contract (by omega), hc]
      refine ext_pv fun q hq => ?_
      dsimp only [b]
      rw [pv_cast, pv_cast, pv_insertArc _ _ (by omega), pv_insertArc _ _ (by omega)]
      dsimp only
      have hb2 : n + 2 * (m + 1) + r - 2 = n + 2 * m + r := by omega
      simp only [hb2]
    have hind' : (z.1.val ⟨n + m, by omega⟩ = ⟨n + m + 1, by omega⟩) ↔
        y.1.val a.castSucc = a.succ := by
      have h₁ : (z.1.val ⟨n + m, by omega⟩ = ⟨n + m + 1, by omega⟩) ↔
          pv (y.insertArc b) a = (a : ℕ) + 1 := by
        rw [Fin.ext_iff, ← pv_of_lt _ (by omega), hy, pv_cast]
      have h₂ : ((y.insertArc b).1.val ⟨a, by omega⟩ = ⟨(a : ℕ) + 1, by omega⟩) ↔
          pv (y.insertArc b) a = (a : ℕ) + 1 := by
        rw [Fin.ext_iff, ← pv_of_lt _ (by omega)]
      exact h₁.trans (h₂.symm.trans hind)
    obtain ⟨ih₁, ih₂⟩ := glueMiddle_insertArc_right (p := p) hr m (y.contract a)
    dsimp only [z] at hstep hind'
    dsimp only [y, a] at hind'
    refine ⟨?_, ?_⟩
    · rw [glueMiddle_succ, glueMiddle_succ, hstep, ih₁]
    · rw [glueMiddleCircles_succ (n := n) (p := p + 2), glueMiddleCircles_succ (n := n) (p := p),
        hstep, ih₂]
      simp only [hind']
      rfl

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
def cupAt (c : Fin (q + 1)) : TLDiagram q (q + 2) :=
  (id q).insertTopArc c

/-- **A cap at position `c`**: the diagram `q + 2 → q` with no circles that joins the bottom points
`c.castSucc` and `c.succ` by a cap and carries the remaining `q` bottom points straight to the
top. It is the vertical reflection of `TauCeti.TLDiagram.cupAt`. -/
def capAt (c : Fin (q + 1)) : TLDiagram (q + 2) q :=
  verticalReflect q (q + 2) (cupAt c)

@[simp]
theorem circles_insertTopArc (D : TLDiagram n q) (c : Fin (q + 1)) :
    (D.insertTopArc c).circles = D.circles := (rfl)

@[simp]
theorem circles_insertBottomArc (D : TLDiagram q m) (c : Fin (q + 1)) :
    (D.insertBottomArc c).circles = D.circles := by simp [insertBottomArc]

@[simp]
theorem circles_cupAt (c : Fin (q + 1)) : (cupAt c).circles = 0 := by simp [cupAt]

@[simp]
theorem circles_capAt (c : Fin (q + 1)) : (capAt c).circles = 0 := by
  rw [capAt, circles_verticalReflect, circles_cupAt]

@[simp]
theorem verticalReflect_cupAt (c : Fin (q + 1)) :
    verticalReflect q (q + 2) (cupAt c) = capAt c := (rfl)

@[simp]
theorem verticalReflect_capAt (c : Fin (q + 1)) :
    verticalReflect (q + 2) q (capAt c) = cupAt c :=
  verticalReflect_verticalReflect (cupAt c)

@[simp]
theorem cupAt_zero : cupAt (0 : Fin 1) = cup := by
  ext : 1
  · refine PlanarMatching.ext fun i => ?_
    have hcast : (cupAt (0 : Fin 1)).matching = (PlanarMatching.nested 0).insertArc 0 := by
      simp [cupAt, insertTopArc]
    rw [hcast, cup_matching_val]
    fin_cases i
    · exact PlanarMatching.insertArc_val_castSucc _ 0
    · exact PlanarMatching.insertArc_val_succ _ 0
  · rw [circles_cupAt, circles_cup]

@[simp]
theorem capAt_zero : capAt (0 : Fin 1) = cap := by rw [capAt, cupAt_zero, verticalReflect_cup]

/-- Composing on the right commutes with inserting a top arc: the inserted top arc lies away from
the middle junction, so gluing across the middle leaves it untouched and closes the same circles. -/
theorem comp_insertTopArc (f : TLDiagram n m) (g : TLDiagram m q) (c : Fin (q + 1)) :
    f.comp (g.insertTopArc c) = (f.comp g).insertTopArc c := by
  have hc := c.isLt
  have happ : f.matching.append (g.insertTopArc c).matching =
      PlanarMatching.cast (by omega)
        ((f.matching.append g.matching).insertArc ⟨n + 2 * m + (q - c), by omega⟩) :=
    PlanarMatching.ext_pv fun w hw => by
      have hidx : (⟨(n + m) + (⟨m + (q - c), by omega⟩ : Fin (m + q + 1)), by omega⟩ :
          Fin ((n + m) + (m + q) + 1)) = ⟨n + 2 * m + (q - c), by omega⟩ := by ext; dsimp; omega
      rw [PlanarMatching.pv_cast, ← hidx, ← PlanarMatching.append_insertArc]
      by_cases hleft : w < n + m
      · rw [PlanarMatching.pv_append_left _ _ hleft, PlanarMatching.pv_append_left _ _ hleft]
      · rw [PlanarMatching.pv_append_right _ _ (by omega) hw,
          PlanarMatching.pv_append_right _ _ (by omega) (by omega), insertTopArc,
          PlanarMatching.pv_cast]
  obtain ⟨hm, hcirc⟩ := PlanarMatching.glueMiddle_insertArc_right (n := n) (p := q)
    (r := q - c) (by omega) m (f.matching.append g.matching)
  ext : 1
  · rw [matching_comp, happ, hm]; rfl
  · rw [circles_comp, circles_insertTopArc, circles_insertTopArc, circles_comp, happ, hcirc]

/-- Post-composing a diagram with `cupAt c` inserts a top arc at position `c`. -/
theorem comp_cupAt (f : TLDiagram n q) (c : Fin (q + 1)) :
    f.comp (cupAt c) = f.insertTopArc c := by rw [cupAt, comp_insertTopArc, comp_id]

/-- Pre-composing a diagram with `capAt c` inserts a bottom arc at position `c`. -/
theorem capAt_comp (c : Fin (q + 1)) (g : TLDiagram q m) :
    (capAt c).comp g = g.insertBottomArc c := by
  apply (verticalReflect (q + 2) m).injective
  rw [insertBottomArc, verticalReflect_verticalReflect, verticalReflect_comp, verticalReflect_capAt,
    comp_cupAt]

/-- Inserting a top arc does not change the number of through strands. -/
@[simp]
theorem through_insertTopArc (D : TLDiagram n q) (c : Fin (q + 1)) :
    (D.insertTopArc c).through = D.through := by
  have hc := c.isLt
  rw [through_def, through_def]
  congr 1
  ext i
  have hi := i.isLt
  simp only [mem_filter, mem_univ, true_and]
  have h₁ : ((D.insertTopArc c).matching.1.val (i.castAdd (q + 2)) : ℕ) =
      PlanarMatching.pv (D.insertTopArc c).matching i :=
    (PlanarMatching.pv_of_lt _ (by omega)).symm
  have h₂ : (D.matching.1.val (i.castAdd q) : ℕ) = PlanarMatching.pv D.matching i :=
    (PlanarMatching.pv_of_lt _ (by omega)).symm
  rw [h₁, h₂, insertTopArc, PlanarMatching.pv_cast, PlanarMatching.pv_insertArc _ _ (by omega)]
  dsimp only
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  simp only [PlanarMatching.unskipN, PlanarMatching.skipN]
  split_ifs <;> omega

/-- Inserting a top arc leaves the bottom half-diagram unchanged. -/
@[simp]
theorem bottomHalf_insertTopArc_val (D : TLDiagram n q) (c : Fin (q + 1)) :
    (D.insertTopArc c).bottomHalf.val = D.bottomHalf.val := by
  have hc := c.isLt
  ext i
  have hi := i.isLt
  have h₁ : ((D.insertTopArc c).matching.1.val (i.castAdd (q + 2)) : ℕ) =
      PlanarMatching.pv (D.insertTopArc c).matching i :=
    (PlanarMatching.pv_of_lt _ (by omega)).symm
  have h₂ : (D.matching.1.val (i.castAdd q) : ℕ) = PlanarMatching.pv D.matching i :=
    (PlanarMatching.pv_of_lt _ (by omega)).symm
  have hpv_eq : PlanarMatching.pv (D.insertTopArc c).matching i =
      if PlanarMatching.pv D.matching i < n + (q - c) then PlanarMatching.pv D.matching i
      else PlanarMatching.pv D.matching i + 2 := by
    rw [insertTopArc, PlanarMatching.pv_cast, PlanarMatching.pv_insertArc _ _ (by omega)]
    dsimp only
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    simp only [PlanarMatching.skipN, PlanarMatching.unskipN,
      ite_eq_left (show (i : ℕ) < n + (q - c) by omega)]
  rw [bottomHalf_apply, bottomHalf_apply]
  split_ifs at hpv_eq <;> split_ifs <;> dsimp only <;> omega

@[simp]
theorem through_insertBottomArc (D : TLDiagram q m) (c : Fin (q + 1)) :
    (D.insertBottomArc c).through = D.through := by simp [insertBottomArc]

@[simp]
theorem topHalf_insertBottomArc_val (D : TLDiagram q m) (c : Fin (q + 1)) :
    (D.insertBottomArc c).topHalf.val = D.topHalf.val := by
  rw [insertBottomArc, topHalf_verticalReflect_val, bottomHalf_insertTopArc_val, ← topHalf_val]

@[simp]
theorem through_cupAt (c : Fin (q + 1)) : (cupAt c).through = q := by simp [cupAt]

@[simp]
theorem through_capAt (c : Fin (q + 1)) : (capAt c).through = q := by
  rw [capAt, through_verticalReflect, through_cupAt]

/-- If a diagram `D : n → q + 2` has an arc joining the consecutive top points `c.castSucc` and
`c.succ`, it is obtained by post-composing a diagram `D' : n → q` with `cupAt c`. -/
theorem exists_comp_cupAt_of_topHalf_apply_eq {D : TLDiagram n (q + 2)} {c : Fin (q + 1)}
    (h : D.topHalf.val c.castSucc = c.succ) :
    ∃ D' : TLDiagram n q, D'.through = D.through ∧ D'.circles = D.circles ∧
      D'.comp (cupAt c) = D := by
  have hc := c.isLt
  let a : Fin (n + q + 1) := ⟨n + (q - c), by omega⟩
  let y : PlanarMatching (n + q + 2) := PlanarMatching.cast (by omega) D.matching
  have hy : y.1.val a.castSucc = a.succ := by
    let b : Fin (n + (q + 2)) := ⟨n + (q + 2) - 1 - c, by omega⟩
    have htop := congrArg Fin.val ((D.topHalf_apply c.castSucc).symm.trans h)
    simp only [Fin.val_castSucc, Fin.val_succ] at htop
    have hb_lt := (D.matching.1.val b).isLt
    have hpvb : (D.matching.1.val b : ℕ) = n + (q - c) := by
      dsimp only [b] at hb_lt ⊢
      split_ifs at htop with hge
      · dsimp only at htop; omega
      · simp only [Fin.val_castSucc] at htop; omega
    have hb_eq : D.matching.1.val b = ⟨n + (q - c), by omega⟩ := Fin.ext hpvb
    have ha_eq : D.matching.1.val ⟨n + (q - c), by omega⟩ = b := by
      rw [← hb_eq, D.matching.1.apply_apply]
    have hpva : PlanarMatching.pv D.matching (n + (q - c)) = n + (q + 2) - 1 - c := by
      rw [PlanarMatching.pv_of_lt D.matching (by omega), ha_eq]
    apply Fin.ext
    rw [← PlanarMatching.pv_coe, Fin.val_castSucc, Fin.val_succ]
    dsimp only [y, a]
    rw [PlanarMatching.pv_cast, hpva]; omega
  have hd : (⟨y.contract a, D.circles⟩ : TLDiagram n q).insertTopArc c = D := by
    ext : 1
    · simp only [insertTopArc]; rw [PlanarMatching.insertArc_contract hy]; simp [y]
    · rfl
  exact ⟨⟨y.contract a, D.circles⟩, by rw [← through_insertTopArc _ c, hd], rfl,
    by rw [comp_cupAt, hd]⟩

/-- If a diagram `D : q + 2 → m` has an arc joining the consecutive bottom points `c.castSucc` and
`c.succ`, it is obtained by pre-composing a diagram `D' : q → m` with `capAt c`. -/
theorem exists_capAt_comp_of_bottomHalf_apply_eq {D : TLDiagram (q + 2) m} {c : Fin (q + 1)}
    (h : D.bottomHalf.val c.castSucc = c.succ) :
    ∃ D' : TLDiagram q m, D'.through = D.through ∧ D'.circles = D.circles ∧
      (capAt c).comp D' = D := by
  have ht : (verticalReflect (q + 2) m D).topHalf.val c.castSucc = c.succ := by
    rwa [topHalf_verticalReflect_val]
  obtain ⟨E, hth, hcirc, heq⟩ := exists_comp_cupAt_of_topHalf_apply_eq ht
  refine ⟨verticalReflect m q E, ?_, ?_, ?_⟩
  · rw [through_verticalReflect, hth, through_verticalReflect]
  · rw [circles_verticalReflect, hcirc, circles_verticalReflect]
  · apply (verticalReflect (q + 2) m).injective
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
  have hc := c.isLt
  rw [cupAt, insertTopArc, PlanarMatching.pv_cast, PlanarMatching.pv_insertArc _ _ (by omega)]
  dsimp only
  by_cases h₁ : w = q + (q - c)
  · simp only [h₁, ite_true]
    split_ifs <;> omega
  by_cases h₂ : w = q + (q - c) + 1
  · simp only [h₂, show q + (q - (c : ℕ)) + 1 ≠ q + (q - c) by omega, ite_false, ite_true]
    split_ifs <;> omega
  rw [ite_eq_right h₁, ite_eq_right h₂, matching_id,
    PlanarMatching.pv_nested q (by simp only [PlanarMatching.unskipN]; split_ifs <;> omega)]
  simp only [PlanarMatching.skipN, PlanarMatching.unskipN]
  split_ifs <;> omega

private theorem pv_cupAt_zero_append_capAt_zero (q : ℕ) {w : ℕ}
    (hw : w < q + (q + 2) + (q + 2 + q)) :
    PlanarMatching.pv ((cupAt (0 : Fin (q + 1))).matching.append
        (capAt (0 : Fin (q + 1))).matching) w =
      if w < 2 * q then 2 * q - 1 - w
      else if w = 2 * q then 2 * q + 1
      else if w = 2 * q + 1 then 2 * q
      else if w = 2 * q + 2 then 2 * q + 3
      else if w = 2 * q + 3 then 2 * q + 2
      else 6 * q + 7 - w := by
  have hz : ((0 : Fin (q + 1)) : ℕ) = 0 := rfl
  by_cases hleft : w < q + (q + 2)
  · rw [PlanarMatching.pv_append_left _ _ hleft, pv_cupAt_matching q 0 hleft, hz]
    simp only [Nat.not_lt_zero, Nat.sub_zero, ite_false]
    split_ifs <;> omega
  · rw [PlanarMatching.pv_append_right _ _ (by omega) hw, capAt, matching_verticalReflect,
      PlanarMatching.pv_cast, PlanarMatching.pv_reflect _ (by omega),
      pv_cupAt_matching q 0 (by omega), hz]
    simp only [Nat.not_lt_zero, Nat.sub_zero, ite_false]
    split_ifs <;> omega

private theorem pv_cupAt_zero_step1 (q : ℕ) {w : ℕ} (hw : w < 4 * q + 2) :
    PlanarMatching.pv
        ((PlanarMatching.cast (k' := q + (q + 1) + (q + 1 + q) + 2) (by omega)
          ((cupAt (0 : Fin (q + 1))).matching.append
            (capAt (0 : Fin (q + 1))).matching)).contract ⟨q + (q + 1), by omega⟩) w =
      if w < 2 * q then 2 * q - 1 - w
      else if w = 2 * q then 2 * q + 1
      else if w = 2 * q + 1 then 2 * q
      else 6 * q + 3 - w := by
  have hpv₁ : PlanarMatching.pv (PlanarMatching.cast (k' := q + (q + 1) + (q + 1 + q) + 2)
      (by omega) ((cupAt (0 : Fin (q + 1))).matching.append
        (capAt (0 : Fin (q + 1))).matching)) (q + (q + 1)) = 2 * q := by
    rw [PlanarMatching.pv_cast, pv_cupAt_zero_append_capAt_zero q (by omega)]
    split_ifs <;> omega
  have hpv₂ : PlanarMatching.pv (PlanarMatching.cast (k' := q + (q + 1) + (q + 1 + q) + 2)
      (by omega) ((cupAt (0 : Fin (q + 1))).matching.append
        (capAt (0 : Fin (q + 1))).matching)) (q + (q + 1) + 1) = 2 * q + 3 := by
    rw [PlanarMatching.pv_cast, pv_cupAt_zero_append_capAt_zero q (by omega)]
    split_ifs <;> omega
  rw [PlanarMatching.pv_contract _ _ (by omega)]
  simp only [PlanarMatching.joinN, hpv₁, hpv₂, PlanarMatching.pv_cast]
  by_cases hw₁ : w < q + (q + 1)
  · rw [show PlanarMatching.skipN (q + (q + 1)) w = w by simp [PlanarMatching.skipN, hw₁],
      pv_cupAt_zero_append_capAt_zero q (by omega)]
    simp only [PlanarMatching.unskipN]
    split_ifs <;> omega
  · rw [show PlanarMatching.skipN (q + (q + 1)) w = w + 2 by simp [PlanarMatching.skipN, hw₁],
      pv_cupAt_zero_append_capAt_zero q (by omega)]
    simp only [show ¬ w + 2 < 2 * q by omega, show w + 2 ≠ 2 * q by omega,
      show w + 2 ≠ 2 * q + 1 by omega, show w + 2 ≠ 2 * q + 2 by omega, ite_false,
      PlanarMatching.unskipN]
    split_ifs <;> omega

private theorem cupAt_zero_step2 (q : ℕ) :
    (PlanarMatching.cast (k' := q + q + (q + q) + 2) (by omega)
      ((PlanarMatching.cast (k' := q + (q + 1) + (q + 1 + q) + 2) (by omega)
        ((cupAt (0 : Fin (q + 1))).matching.append
          (capAt (0 : Fin (q + 1))).matching)).contract ⟨q + (q + 1), by omega⟩)).contract
      ⟨q + q, by omega⟩ =
      (PlanarMatching.nested q).append (PlanarMatching.nested q) := by
  set y₂ : PlanarMatching (q + q + (q + q) + 2) := PlanarMatching.cast (by omega)
    ((PlanarMatching.cast (k' := q + (q + 1) + (q + 1 + q) + 2) (by omega)
      ((cupAt (0 : Fin (q + 1))).matching.append
        (capAt (0 : Fin (q + 1))).matching)).contract ⟨q + (q + 1), by omega⟩)
  have h₁ : PlanarMatching.pv y₂ (q + q) = 2 * q + 1 := by
    dsimp only [y₂]; rw [PlanarMatching.pv_cast, pv_cupAt_zero_step1 q (by omega)]
    split_ifs <;> omega
  have h₂ : PlanarMatching.pv y₂ (q + q + 1) = 2 * q := by
    dsimp only [y₂]; rw [PlanarMatching.pv_cast, pv_cupAt_zero_step1 q (by omega)]
    split_ifs <;> omega
  refine PlanarMatching.ext_pv fun w hw => ?_
  rw [PlanarMatching.pv_contract _ _ hw]
  simp only [PlanarMatching.joinN, h₁, h₂]
  dsimp only [y₂]
  rw [PlanarMatching.pv_cast]
  by_cases hwq : w < q + q
  · rw [show PlanarMatching.skipN (q + q) w = w by simp [PlanarMatching.skipN, hwq],
      pv_cupAt_zero_step1 q (by omega), PlanarMatching.pv_append_left _ _ hwq,
      PlanarMatching.pv_nested q hwq]
    simp only [PlanarMatching.unskipN]; split_ifs <;> omega
  · rw [show PlanarMatching.skipN (q + q) w = w + 2 by simp [PlanarMatching.skipN, hwq],
      pv_cupAt_zero_step1 q (by omega), PlanarMatching.pv_append_right _ _ (by omega) hw,
      PlanarMatching.pv_nested q (by omega)]
    simp only [PlanarMatching.unskipN]; split_ifs <;> omega

private theorem cupAt_zero_comp_capAt_zero (q : ℕ) :
    (cupAt (0 : Fin (q + 1))).comp (capAt (0 : Fin (q + 1))) = ⟨PlanarMatching.nested q, 1⟩ := by
  let x₀ := (cupAt (0 : Fin (q + 1))).matching.append (capAt (0 : Fin (q + 1))).matching
  let y₁ : PlanarMatching (q + (q + 1) + (q + 1 + q) + 2) := PlanarMatching.cast (by omega) x₀
  let y₂ : PlanarMatching (q + q + (q + q) + 2) :=
    PlanarMatching.cast (by omega) (y₁.contract ⟨q + (q + 1), by omega⟩)
  have hne₁ : y₁.1.val ⟨q + (q + 1), by omega⟩ ≠ ⟨q + (q + 1) + 1, by omega⟩ := by
    have hpv := PlanarMatching.pv_of_lt y₁ (q := q + (q + 1)) (by omega)
    dsimp only [y₁, x₀] at hpv
    rw [PlanarMatching.pv_cast, pv_cupAt_zero_append_capAt_zero q (by omega)] at hpv
    intro heq; rw [heq] at hpv; simp only at hpv; split_ifs at hpv <;> omega
  have heq₂ : y₂.1.val ⟨q + q, by omega⟩ = ⟨q + q + 1, by omega⟩ := by
    ext
    rw [← PlanarMatching.pv_of_lt y₂ (by omega)]
    dsimp only [y₂, y₁, x₀]
    rw [PlanarMatching.pv_cast, pv_cupAt_zero_step1 q (by omega)]
    split_ifs <;> omega
  ext : 1
  · rw [matching_comp, PlanarMatching.glueMiddle_succ, PlanarMatching.glueMiddle_succ,
      cupAt_zero_step2 q, PlanarMatching.glueMiddle_append_nested]
  · rw [circles_comp, circles_cupAt, circles_capAt, zero_add, zero_add,
      PlanarMatching.glueMiddleCircles_succ (n := q) (p := q), ite_eq_right hne₁, add_zero,
      PlanarMatching.glueMiddleCircles_succ (n := q) (p := q), ite_eq_left heq₂,
      cupAt_zero_step2 q, PlanarMatching.glueMiddleCircles_append_nested]

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
  have hK := h.card_eq
  refine ⟨hK, ?_, fun i hi => ?_⟩
  · rw [PlanarMatching.pv_reflect _ (by omega), show K - 1 - 0 = k + 1 by omega, h.pv_last]; omega
  · have hpv := PlanarMatching.pv_lt x (q := k - 1 - i) (by omega)
    rw [PlanarMatching.pv_reflect _ (by omega), PlanarMatching.pv_reflect _ hi,
      show K - 1 - (i + 1) = k - 1 - i + 1 by omega, h.pv_succ _ (by omega)]; omega

private theorem IsWrapped.eq_nested {q : ℕ} {y : PlanarMatching ((q + 1) + (q + 1))}
    (h : IsWrapped y (PlanarMatching.nested q)) :
    y = PlanarMatching.nested (q + 1) :=
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
  have _ := a.isLt
  have _ := h.card_eq
  refine ⟨⟨by omega, ?_, fun i hi => ?_⟩, ?_⟩
  · rw [PlanarMatching.pv_contract _ _ (by omega), ha',
      show PlanarMatching.skipN ((a : ℕ) + 1) 0 = 0 by simp [PlanarMatching.skipN]]
    simp only [PlanarMatching.joinN, h.pv_zero,
      show k + 2 + 1 ≠ (a : ℕ) + 1 by omega, show k + 2 + 1 ≠ (a : ℕ) + 1 + 1 by omega,
      ite_false, PlanarMatching.unskipN]
    split_ifs <;> omega
  · let s := PlanarMatching.skipN a i
    have hs : s < k + 2 ∧ s ≠ a ∧ s ≠ (a : ℕ) + 1 := by
      simp only [s, PlanarMatching.skipN]
      refine ⟨by split_ifs <;> omega, by split_ifs <;> omega, by split_ifs <;> omega⟩
    rw [PlanarMatching.pv_contract _ _ (by omega), PlanarMatching.pv_contract _ _ hi, ha',
      show PlanarMatching.skipN ((a : ℕ) + 1) (i + 1) = s + 1 by
        simp only [s, PlanarMatching.skipN]; split_ifs <;> omega,
      h.pv_succ s hs.1]
    have hjoin : PlanarMatching.joinN y ((a : ℕ) + 1) (PlanarMatching.pv x s + 1) =
        PlanarMatching.joinN x a (PlanarMatching.pv x s) + 1 := by
      simp only [PlanarMatching.joinN]
      rw [h.pv_succ a (by omega), h.pv_succ ((a : ℕ) + 1) (by omega)]
      split_ifs <;> omega
    rw [hjoin]
    have hw_ne := PlanarMatching.joinN_pv_ne x a hs.2.1 hs.2.2
    suffices ∀ w : ℕ, w ≠ a → w ≠ (a : ℕ) + 1 →
        PlanarMatching.unskipN ((a : ℕ) + 1) (w + 1) = PlanarMatching.unskipN a w + 1 from
      this _ hw_ne.1 hw_ne.2
    intro w _ _
    simp only [PlanarMatching.unskipN]
    split_ifs <;> omega
  · have h₁ : (y.1.val ⟨a', by omega⟩ = ⟨(a' : ℕ) + 1, by omega⟩) ↔
        PlanarMatching.pv y a' = (a' : ℕ) + 1 := by
      rw [Fin.ext_iff, ← PlanarMatching.pv_of_lt y (by omega)]
    have h₂ : (x.1.val ⟨a, by omega⟩ = ⟨(a : ℕ) + 1, by omega⟩) ↔
        PlanarMatching.pv x a = (a : ℕ) + 1 := by
      rw [Fin.ext_iff, ← PlanarMatching.pv_of_lt x (by omega)]
    rw [h₁, h₂, ha', h.pv_succ a (by omega)]
    omega

private theorem IsWrapped.glueMiddle {n p : ℕ} :
    ∀ (m : ℕ) {y : PlanarMatching ((n + 1) + m + (m + (p + 1)))}
      {x : PlanarMatching (n + m + (m + p))},
      IsWrapped y x →
        IsWrapped (PlanarMatching.glueMiddle m y) (PlanarMatching.glueMiddle m x) ∧
        PlanarMatching.glueMiddleCircles (n := n + 1) (p := p + 1) m y =
          PlanarMatching.glueMiddleCircles (n := n) (p := p) m x
  | 0, _, _, h => ⟨h.cast (by omega) (by omega), rfl⟩
  | m + 1, y, x, h => by
    obtain ⟨hc, hind⟩ := (h.cast
      (K' := (n + 1) + m + (m + (p + 1)) + 2) (k' := n + m + (m + p) + 2)
      (by omega) (by omega)).contract_succ
      ⟨(n + 1) + m, by omega⟩ ⟨n + m, by omega⟩ (by dsimp; omega)
    obtain ⟨ih₁, ih₂⟩ := IsWrapped.glueMiddle m hc
    refine ⟨?_, ?_⟩
    · rw [PlanarMatching.glueMiddle_succ, PlanarMatching.glueMiddle_succ]
      exact ih₁
    · rw [PlanarMatching.glueMiddleCircles_succ (n := n + 1) (p := p + 1),
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
    dsimp only [y₀]
    rw [PlanarMatching.pv_cast, PlanarMatching.pv_append_left _ _ (by omega),
      show (n + 1) + m = n + m + 1 by omega, hf.pv_last]
  have hpva1 : PlanarMatching.pv y₀ ((n + 1) + m + 1) =
      (n + 1) + (m + 1) + (m + p + 1) := by
    dsimp only [y₀]
    rw [PlanarMatching.pv_cast, PlanarMatching.pv_append_right _ _ (by omega) (by omega),
      show (n + 1) + m + 1 - ((n + 1) + (m + 1)) = 0 by omega, hg.pv_zero]
  have hy0 : PlanarMatching.pv y₀ 0 = (n + 1) + m := by
    dsimp only [y₀]
    rw [PlanarMatching.pv_cast, PlanarMatching.pv_append_left _ _ (by omega), hf.pv_zero]
    omega
  refine ⟨⟨by omega, ?_, fun i hi => ?_⟩, ?_⟩
  · rw [PlanarMatching.pv_contract y₀ _ (by omega),
      show PlanarMatching.skipN ((n + 1) + m) 0 = 0 by simp [PlanarMatching.skipN]]
    simp only [PlanarMatching.joinN, hy0, hpva1, ite_true, PlanarMatching.unskipN]
    split_ifs <;> omega
  · rw [PlanarMatching.pv_contract y₀ _ (by omega)]
    simp only [PlanarMatching.joinN, hpva, hpva1]
    by_cases hleft : i < n + m
    · have hpvf := PlanarMatching.pv_lt f hleft
      rw [show PlanarMatching.skipN ((n + 1) + m) (i + 1) = i + 1 by
        simp [PlanarMatching.skipN, show i + 1 < (n + 1) + m by omega]]
      dsimp only [y₀]
      rw [PlanarMatching.pv_cast, PlanarMatching.pv_append_left _ _ (by omega),
        hf.pv_succ i hleft, PlanarMatching.pv_append_left _ _ hleft]
      simp only [PlanarMatching.unskipN]
      split_ifs <;> omega
    · rw [show PlanarMatching.skipN ((n + 1) + m) (i + 1) = i + 3 by
        simp [PlanarMatching.skipN, show ¬ i + 1 < (n + 1) + m by omega]]
      dsimp only [y₀]
      rw [PlanarMatching.pv_cast, PlanarMatching.pv_append_right _ _ (by omega) (by omega),
        show i + 3 - ((n + 1) + (m + 1)) = i - (n + m) + 1 by omega,
        hg.pv_succ (i - (n + m)) (by omega),
        PlanarMatching.pv_append_right _ _ (by omega) hi]
      simp only [PlanarMatching.unskipN]
      split_ifs <;> omega
  · have hpv_coe := PlanarMatching.pv_of_lt y₀ (q := (n + 1) + m) (by omega)
    intro heq
    rw [heq, hpva] at hpv_coe
    simp only at hpv_coe
    omega

private theorem isWrapped_cupAt_succ {q : ℕ} (c : Fin (q + 1)) :
    IsWrapped (cupAt c.succ).matching (cupAt c).matching := by
  have hc := c.isLt
  refine ⟨by omega, ?_, fun i hi => ?_⟩
  · rw [pv_cupAt_matching (q + 1) c.succ (by omega)]
    simp only [Fin.val_succ, show 0 < (c : ℕ) + 1 by omega, ite_true]
    omega
  · rw [pv_cupAt_matching (q + 1) c.succ (by omega), pv_cupAt_matching q c hi]
    simp only [Fin.val_succ]
    split_ifs <;> omega

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
      have ih_m : PlanarMatching.glueMiddle (q + 2)
          ((cupAt c).matching.append (capAt c).matching) = PlanarMatching.nested q := by
        simpa [matching_comp] using congrArg TLDiagram.matching ih
      have ih_c : PlanarMatching.glueMiddleCircles (n := q) (p := q) (q + 2)
          ((cupAt c).matching.append (capAt c).matching) = 1 := by
        simpa [circles_comp] using congrArg TLDiagram.circles ih
      rw [ih_m] at hglue
      ext : 1
      · rw [matching_comp, PlanarMatching.glueMiddle_succ]
        exact hglue.eq_nested
      · rw [circles_comp, circles_cupAt, circles_capAt, zero_add, zero_add,
          PlanarMatching.glueMiddleCircles_succ (n := q + 1) (p := q + 1),
          ite_eq_right hne, add_zero, hcirc, ih_c]) c

end CupCompCap

end TLDiagram

end TauCeti
