/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.GaussCode.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Inserting kinks into Gauss codes

A *kink* is a small loop of a knot diagram crossing itself once. Read along the traversal of the
knot, it is a crossing whose two visits come one right after the other.

`TauCeti.BasedOrientedGaussCode.insertKink D k o s` inserts two visits of a new crossing, the last
one, at positions `k` and `k + 1` of the traversal of `D`: the first of them is over exactly when
`o` is true, and the new crossing has sign `s`. The old visits keep their order, crossings,
over/under data and signs; `TauCeti.BasedOrientedGaussCode.kinkVisitEquiv` records where they go.
The four choices of `o` and `s` are the four kinks: for a kink of given sign, whether the strand
first passes over or under decides on which side of the cut arc its loop lies.

That inserting a kink is a first Reidemeister move on the PD-code of the diagram is proved in
`TauCeti.KnotTheory.GaussCode.PDCode.Kink`.

## Main definitions

* `TauCeti.BasedOrientedGaussCode.kinkVisitEquiv`: the positions of the old and the inserted
  visits after inserting two visits at position `k`.
* `TauCeti.BasedOrientedGaussCode.insertKink`: insert a kink into a based oriented Gauss code.

## Main results

* `TauCeti.BasedOrientedGaussCode.writhe_insertKink`: the kink adds its sign to the writhe.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1 (knot
  diagrams and the Reidemeister moves).
-/

public section

namespace TauCeti

namespace BasedOrientedGaussCode

variable {n : ℕ}

/-! ### Inserting two consecutive visits -/

/-- The position of an old visit, or of one of the two new visits, after two visits are inserted
at position `k`. -/
private def kinkVisitFun (n : ℕ) (k : Fin (2 * n + 1)) : Fin (2 * n) ⊕ Fin 2 → Fin (2 * (n + 1)) :=
  Sum.elim (fun j ↦ ⟨if j.val < k.val then j.val else j.val + 2, by split_ifs <;> omega⟩)
    (fun t ↦ ⟨k.val + t.val, by omega⟩)

private theorem kinkVisitFun_injective (n : ℕ) (k : Fin (2 * n + 1)) :
    Function.Injective (kinkVisitFun n k) := by
  rintro (j | t) (j' | t') h <;>
    simp only [kinkVisitFun, Sum.elim_inl, Sum.elim_inr, Fin.mk.injEq, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq] at h ⊢ <;>
    (try split_ifs at h) <;> omega

/-- The visits of a Gauss code with two visits inserted at position `k`: the `2 * n` old visits,
in their old order, and the two new visits, which become visits `k` and `k + 1`. An old visit `j`
keeps its position if `j < k` and moves up by two otherwise. -/
noncomputable def kinkVisitEquiv (n : ℕ) (k : Fin (2 * n + 1)) :
    Fin (2 * n) ⊕ Fin 2 ≃ Fin (2 * (n + 1)) :=
  Equiv.ofBijective (kinkVisitFun n k) <| (kinkVisitFun_injective n k).bijective_of_nat_card_le
    (by simp [Nat.card_eq_fintype_card]; omega)

/-- An old visit keeps its position if it comes before the inserted visits, and moves up by two
otherwise. -/
@[simp]
theorem kinkVisitEquiv_apply_inl_val (k : Fin (2 * n + 1)) (j : Fin (2 * n)) :
    (kinkVisitEquiv n k (.inl j)).val = if j.val < k.val then j.val else j.val + 2 :=
  (rfl)

/-- The two inserted visits are visits `k` and `k + 1`. -/
@[simp]
theorem kinkVisitEquiv_apply_inr_val (k : Fin (2 * n + 1)) (t : Fin 2) :
    (kinkVisitEquiv n k (.inr t)).val = k.val + t.val :=
  (rfl)

/-- The matching of visits of a code with a kink inserted, before the visits are renumbered: the
old matching on the old visits, and the two new visits matched with each other. -/
private def kinkPartner (D : BasedOrientedGaussCode n) : PerfectMatching (Fin (2 * n) ⊕ Fin 2) :=
  PerfectMatching.mk (Equiv.sumCongr D.partner.val (Equiv.swap 0 1))
    (by rintro (j | t) <;> simp)
    (by
      rintro (j | t)
      · simp [D.partner.apply_ne]
      · simp only [Equiv.sumCongr_apply, Sum.map_inr, ne_eq, Sum.inr.injEq]
        fin_cases t <;> decide)

/-- Insert a **kink** into a based oriented Gauss code: two consecutive visits `k` and `k + 1` of a
new crossing, the last one, `Fin.last n`, of sign `s`. The first of the two visits is over exactly
when `o` is true. The old visits keep their order, crossings, over/under data and signs.

In a diagram this cuts the arc running from visit `k - 1` to visit `k` of the old code, cyclically,
and splices in a small loop crossing itself once. Each of the four choices of `o` and `s` is the
kink on one side of the arc with one of the two crossing types. -/
noncomputable def insertKink (D : BasedOrientedGaussCode n) (k : Fin (2 * n + 1)) (o : Bool)
    (s : ℤˣ) : BasedOrientedGaussCode (n + 1) where
  visit i := Sum.elim (fun j ↦ (D.visit j).castSucc) (fun _ ↦ Fin.last n)
    ((kinkVisitEquiv n k).symm i)
  over i := Sum.elim D.over (fun t ↦ if t = 0 then o else !o) ((kinkVisitEquiv n k).symm i)
  sign := Fin.lastCases s D.sign
  partner := PerfectMatching.congr (kinkVisitEquiv n k) (kinkPartner D)
  visit_eq_iff i j := by
    obtain ⟨x, rfl⟩ := (kinkVisitEquiv n k).surjective i
    obtain ⟨y, rfl⟩ := (kinkVisitEquiv n k).surjective j
    rw [PerfectMatching.congr_val_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      (kinkVisitEquiv n k).injective.eq_iff, (kinkVisitEquiv n k).injective.eq_iff]
    rcases x with x | t <;> rcases y with y | t'
    · simp [kinkPartner, Fin.castSucc_inj, D.visit_eq_iff, eq_comm]
    · simp [kinkPartner, Fin.castSucc_ne_last]
    · simp [kinkPartner, (Fin.castSucc_ne_last _).symm]
    · simp only [kinkPartner, PerfectMatching.val_mk, Equiv.sumCongr_apply, Sum.map_inr,
        Sum.elim_inr, Sum.inr.injEq, true_iff]
      fin_cases t <;> fin_cases t' <;> decide
  over_partner i := by
    obtain ⟨x, rfl⟩ := (kinkVisitEquiv n k).surjective i
    rw [PerfectMatching.congr_val_apply_apply, Equiv.symm_apply_apply]
    rcases x with x | t
    · simp [kinkPartner]
    · simp only [kinkPartner, PerfectMatching.val_mk, Equiv.sumCongr_apply, Sum.map_inr,
        Sum.elim_inr]
      fin_cases t <;> simp

variable (D : BasedOrientedGaussCode n) (k : Fin (2 * n + 1)) (o : Bool) (s : ℤˣ)

/-- An old visit keeps its crossing. -/
@[simp]
theorem visit_insertKink_inl (j : Fin (2 * n)) :
    (D.insertKink k o s).visit (kinkVisitEquiv n k (.inl j)) = (D.visit j).castSucc := by
  simp [insertKink]

/-- The two inserted visits are visits of the new last crossing. -/
@[simp]
theorem visit_insertKink_inr (t : Fin 2) :
    (D.insertKink k o s).visit (kinkVisitEquiv n k (.inr t)) = Fin.last n := by
  simp [insertKink]

/-- An old visit keeps its over/under data. -/
@[simp]
theorem over_insertKink_inl (j : Fin (2 * n)) :
    (D.insertKink k o s).over (kinkVisitEquiv n k (.inl j)) = D.over j := by
  simp [insertKink]

/-- The first inserted visit is over exactly when `o` is true. -/
@[simp]
theorem over_insertKink_inr_zero :
    (D.insertKink k o s).over (kinkVisitEquiv n k (.inr 0)) = o := by
  simp [insertKink]

/-- The second inserted visit is over exactly when `o` is false. -/
@[simp]
theorem over_insertKink_inr_one :
    (D.insertKink k o s).over (kinkVisitEquiv n k (.inr 1)) = !o := by
  simp [insertKink]

/-- An old crossing keeps its sign. -/
@[simp]
theorem sign_insertKink_castSucc (c : Fin n) :
    (D.insertKink k o s).sign c.castSucc = D.sign c := by
  simp [insertKink]

/-- The new crossing has sign `s`. -/
@[simp]
theorem sign_insertKink_last : (D.insertKink k o s).sign (Fin.last n) = s := by
  simp [insertKink]

/-- The partner of an old visit is the old partner. -/
@[simp]
theorem partner_insertKink_inl (j : Fin (2 * n)) :
    (D.insertKink k o s).partner.val (kinkVisitEquiv n k (.inl j)) =
      kinkVisitEquiv n k (.inl (D.partner.val j)) := by
  simp [insertKink, kinkPartner]

/-- The two inserted visits are partners. -/
@[simp]
theorem partner_insertKink_inr (t : Fin 2) :
    (D.insertKink k o s).partner.val (kinkVisitEquiv n k (.inr t)) =
      kinkVisitEquiv n k (.inr (t + 1)) := by
  simp only [insertKink, kinkPartner, PerfectMatching.congr_val_apply_apply,
    PerfectMatching.val_mk, Equiv.sumCongr_apply, Sum.map_inr]
  congr 2
  fin_cases t <;> rfl

/-- The kink adds the sign of its crossing to the writhe. -/
@[simp]
theorem writhe_insertKink : (D.insertKink k o s).writhe = D.writhe + s := by
  simp [writhe_def, Fin.sum_univ_castSucc]

end BasedOrientedGaussCode

end TauCeti
