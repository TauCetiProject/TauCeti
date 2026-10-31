/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.MinimalSlope

/-!
# Continuing a lower convex envelope at a contact point

Deleting coefficient points before a contact point preserves the entire remaining
lower convex envelope. After reindexing, the tail of the polygon is therefore the
lower convex envelope of the coefficient tail. This allows the minimal-secant-slope
construction to restart at successive contacts, rather than only at the first point.
The converse holds too: deleting a prefix preserves the remaining polygon only if
the new initial point is a contact.

A contact need not be a geometric vertex. In particular, restarting the construction
may give the same slope again, so collinear pieces still need to be merged when
extracting vertices. None of the results assumes a bounded finite domain.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, Chapter IV §3.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

namespace TauCeti

namespace IsLowerConvexEnvelope

variable {a h : ℕ → WithTop ℝ}

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

/-- The first outgoing edge at a finite contact is computed from the minimal secant
slope of the coefficient tail. A later finite point excludes the singleton case. -/
theorem unitSlope_eq_sInf_secantSlopes_tail (hh : IsLowerConvexEnvelope a h) {p : ℕ}
    (hp : h p = a p) (hpf : a p ≠ ⊤)
    (hne : (secantSlopes (fun n => a (n + p)) 0).Nonempty) :
    unitSlope h p = sInf (secantSlopes (fun n => a (n + p)) 0) := by
  have ht := hh.comp_add_right hp
  have hs := unitSlope_lowerConvexEnvelope_eq_sInf_secantSlopes ht.isAdmissible
    (p := 0) (by simpa using hpf) (fun n hn => by omega) hne
  rw [← ht.eq_lowerConvexEnvelope] at hs
  simpa only [unitSlope_def, zero_add, Nat.add_comm 1 p] using hs

end IsLowerConvexEnvelope

end TauCeti
