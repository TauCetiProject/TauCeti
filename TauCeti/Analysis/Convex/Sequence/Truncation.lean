/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Vertex

/-!
# Truncation at contact points of a lower convex envelope

Discarding coefficient points after an index can raise the lower convex envelope. If a
contact point is retained, however, the envelope is unchanged up to that point. Consequently
truncation preserves the polygon through any retained geometric vertex, since a strict
increase of adjacent finite slopes forces contact. The same statements preserve every finite
unit edge strictly before the retained point.

The contact-point theorem also applies to collinear contact points, which need not be
geometric vertices. No boundedness of the original finite domain is assumed.
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
