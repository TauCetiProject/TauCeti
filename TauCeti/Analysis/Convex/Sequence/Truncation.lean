/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Vertex

/-!
# Restricting a lower convex envelope at contact points

Discarding coefficient points after an index can raise the lower convex envelope. If a
contact point is retained, however, the envelope is unchanged up to that point. Consequently
truncation preserves the polygon through any retained geometric vertex, since a strict
increase of adjacent finite slopes forces contact. The same statements preserve every finite
unit edge strictly before the retained point.

Deleting coefficient points before a contact likewise preserves the remaining envelope.
After reindexing, the tail is the envelope of the coefficient tail, allowing the
minimal-slope construction to restart. Conversely, this reindexing preserves the envelope
only when the cut is a contact.

These contact-point theorems also apply to collinear contact points, which need not be
geometric vertices. Restarting can therefore give the same slope again. No boundedness of
the original finite domain or finiteness of the contact height is assumed.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, Chapter IV §3.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

namespace TauCeti

namespace IsLowerConvexEnvelope

variable {a h : ℕ → WithTop ℝ}

/-- Truncation at any later index preserves the envelope through a retained contact point.
The retained point need not be a strict vertex or even have finite height. -/
theorem eqOn_lowerConvexEnvelope_truncate (hh : IsLowerConvexEnvelope a h) {p N : ℕ}
    (hp : h p = a p) (hpN : p ≤ N) :
    Set.EqOn (lowerConvexEnvelope (fun n => if n ≤ N then a n else ⊤)) h (Set.Iic p) := by
  let b : ℕ → WithTop ℝ := fun n => if n ≤ N then a n else ⊤
  have hb : IsAdmissible b := isAdmissible_of_forall_gt (p := N) fun n hn =>
    ite_eq_right (not_le.mpr hn)
  have hab : a ≤ b := fun n => by simp only [b]; split_ifs <;> simp
  have hle : h ≤ lowerConvexEnvelope b := by
    rw [hh.eq_lowerConvexEnvelope]
    exact lowerConvexEnvelope_mono hh.isAdmissible hab
  have hjoin : lowerConvexEnvelope b p = h p := by
    apply le_antisymm _ (hle p)
    simpa only [b, ite_eq_left hpN, hp] using lowerConvexEnvelope_le hb p
  -- Splice the truncated prefix back into the original envelope. Greatestness prevents
  -- this convex minorant from being any higher than the original envelope.
  have hcv := (isConvexSeq_lowerConvexEnvelope b).ite_le_of_le_of_eq hh.isConvexSeq
    (fun n _ => hle n) hjoin
  have hminor : (fun n => if n ≤ p then lowerConvexEnvelope b n else h n) ≤ a := by
    intro n
    dsimp only
    split_ifs with hn
    · simpa only [b, ite_eq_left (hn.trans hpN)] using lowerConvexEnvelope_le hb n
    · exact hh.le n
  intro n hn
  exact le_antisymm
    (by simpa only [ite_eq_left (Set.mem_Iic.mp hn)] using hh.greatest hcv hminor n) (hle n)

/-- Truncating precisely at `p` preserves the entire prefix if and only if `p` is a
contact point. This includes missing heights and empty polygons. -/
@[simp]
theorem eqOn_lowerConvexEnvelope_truncate_iff (hh : IsLowerConvexEnvelope a h) (p : ℕ) :
    Set.EqOn (lowerConvexEnvelope (fun n => if n ≤ p then a n else ⊤)) h (Set.Iic p) ↔
      h p = a p := by
  constructor
  · intro heq
    rw [← heq (Set.mem_Iic.mpr le_rfl),
      lowerConvexEnvelope_eq_of_forall_gt (p := p)
        (fun n hn => ite_eq_right (not_le.mpr hn))]
    simp
  · intro hp
    exact hh.eqOn_lowerConvexEnvelope_truncate hp le_rfl

/-- Discarding all points before a contact preserves the envelope from that contact
onwards. The original absolute indices are retained, with infinity before the cut. -/
theorem eqOn_lowerConvexEnvelope_drop (hh : IsLowerConvexEnvelope a h) {p : ℕ}
    (hp : h p = a p) :
    Set.EqOn (lowerConvexEnvelope (fun n => if p ≤ n then a n else ⊤)) h (Set.Ici p) := by
  let b : ℕ → WithTop ℝ := fun n => if p ≤ n then a n else ⊤
  have hab : a ≤ b := fun n => by simp only [b]; split_ifs <;> simp
  have hb := hh.isAdmissible.mono hab
  have hle : h ≤ lowerConvexEnvelope b :=
    le_lowerConvexEnvelope hh.isConvexSeq (hh.le.trans hab)
  have hjoin : h p = lowerConvexEnvelope b p := by
    apply le_antisymm (hle p)
    simpa only [b, ite_true, le_refl, hp] using lowerConvexEnvelope_le hb p
  -- Raise the suffix to the envelope of the retained points. The original prefix
  -- and equality at the contact make this a convex minorant of the original data.
  have hcv := hh.isConvexSeq.ite_le_of_le_of_eq_right
    (isConvexSeq_lowerConvexEnvelope b) (fun n _ => hle n) hjoin
  have hminor : (fun n => if n ≤ p then h n else lowerConvexEnvelope b n) ≤ a := by
    intro n
    dsimp only
    split_ifs with hn
    · exact hh.le n
    · simpa only [b, ite_eq_left (by omega : p ≤ n)] using lowerConvexEnvelope_le hb n
  intro n hn
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hn) with rfl | hn
  · exact hjoin.symm
  · exact le_antisymm
      (by simpa only [ite_eq_right (not_le.mpr hn)] using hh.greatest hcv hminor n) (hle n)

/-- At a contact, the tail of an envelope is the envelope of the reindexed point tail.
This is the universal property needed to restart a one-sided construction. -/
theorem comp_add_right (hh : IsLowerConvexEnvelope a h) {p : ℕ} (hp : h p = a p) :
    IsLowerConvexEnvelope (fun n => a (n + p)) (fun n => h (n + p)) := by
  have hshift : (fun n => if p ≤ n then a (n - p + p) else ⊤) =
      (fun n => if p ≤ n then a n else ⊤) := by
    funext n
    split_ifs with hn
    · rw [Nat.sub_add_cancel hn]
    · rfl
  have heq : lowerConvexEnvelope (fun n => a (n + p)) = fun n => h (n + p) := by
    funext n
    have hdrop := hh.eqOn_lowerConvexEnvelope_drop hp (Set.mem_Ici.mpr (Nat.le_add_left p n))
    rw [← hshift, lowerConvexEnvelope_shift (fun n => a (n + p)) p] at hdrop
    simpa using hdrop
  rw [← heq]
  exact isLowerConvexEnvelope_lowerConvexEnvelope
    ((hh.isConvexSeq.comp_add_right p).isAdmissible.mono (fun n => hh.le (n + p)))

/-- Reindexing a tail preserves the envelope exactly when the cut is a contact point.
No finiteness hypothesis is imposed on the joining height. -/
@[simp]
theorem comp_add_right_iff (hh : IsLowerConvexEnvelope a h) (p : ℕ) :
    IsLowerConvexEnvelope (fun n => a (n + p)) (fun n => h (n + p)) ↔ h p = a p := by
  refine ⟨fun ht => ?_, hh.comp_add_right⟩
  have heq := lowerConvexEnvelope_eq_of_forall_lt ht.isAdmissible
    (p := 0) (fun n hn => by omega)
  rw [← ht.eq_lowerConvexEnvelope] at heq
  simpa using heq

/-- Truncation preserves all finite unit edges strictly before a retained contact point. -/
theorem mem_finiteEdges_lowerConvexEnvelope_truncate (hh : IsLowerConvexEnvelope a h)
    {p N n : ℕ} (hp : h p = a p) (hpN : p ≤ N) (hn : n < p) :
    n ∈ finiteEdges (lowerConvexEnvelope (fun k => if k ≤ N then a k else ⊤)) ↔
      n ∈ finiteEdges h := by
  have heq := hh.eqOn_lowerConvexEnvelope_truncate hp hpN
  simp only [mem_finiteEdges, heq (Set.mem_Iic.mpr (by omega : n ≤ p)),
    heq (Set.mem_Iic.mpr (by omega : n + 1 ≤ p))]

/-- Every unit increment strictly before a retained contact point survives truncation.
Only increments on finite edges are geometric slopes. -/
theorem unitSlope_lowerConvexEnvelope_truncate (hh : IsLowerConvexEnvelope a h)
    {p N n : ℕ} (hp : h p = a p) (hpN : p ≤ N) (hn : n < p) :
    unitSlope (lowerConvexEnvelope (fun k => if k ≤ N then a k else ⊤)) n =
      unitSlope h n := by
  have heq := hh.eqOn_lowerConvexEnvelope_truncate hp hpN
  simp only [unitSlope_def, heq (Set.mem_Iic.mpr (by omega : n ≤ p)),
    heq (Set.mem_Iic.mpr (by omega : n + 1 ≤ p))]

/-- The lower hull is unchanged through a retained geometric vertex. A vertex here is a
strict increase between adjacent finite slopes; no endpoint sentinel is used. -/
theorem eqOn_lowerConvexEnvelope_truncate_of_unitSlope_lt
    (hh : IsLowerConvexEnvelope a h) {n N : ℕ}
    (hn : h n ≠ ⊤) (hn₂ : h (n + 2) ≠ ⊤)
    (hs : unitSlope h n < unitSlope h (n + 1)) (hN : n + 1 ≤ N) :
    Set.EqOn (lowerConvexEnvelope (fun k => if k ≤ N then a k else ⊤)) h
      (Set.Iic (n + 1)) :=
  hh.eqOn_lowerConvexEnvelope_truncate (hh.eq_of_unitSlope_lt hn hn₂ hs) hN

end IsLowerConvexEnvelope

end TauCeti
