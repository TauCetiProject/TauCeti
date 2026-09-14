/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.Basis

/-!
# The multiplication table of a skew-zigzag algebra

The skew-zigzag relation quotient `TauCeti.skewZigzagQuotient` of a finite simple graph is spanned
by the vertex idempotents `e_i`, the oriented edges `a_d`, and the volume classes
`TauCeti.skewZigzagVolume`, each taken relative to a chosen incident edge. This file computes the
products of two of these classes.

The table has the same shape as the ordinary one in
`TauCeti.RepresentationTheory.Quiver.Zigzag.Multiplication`. The idempotents are orthogonal local
units; an arrow is absorbed by the idempotent at its head on the left and at its tail on the right;
a volume class is absorbed by the idempotent at its base on either side. Two arrows multiply to the
volume class along the first of them when the later factor is its reverse, and to zero otherwise.
Every product reaching path length three vanishes. The skew parameter only enters when a volume
class is compared with one taken along a different incident edge, through
`TauCeti.skewZigzagMk_backtrackElem_eq_smul_skewZigzagVolume`; no statement below needs it.

## Main results

* `TauCeti.skewZigzagMk_ofArrow_mul_ofArrow_symm` and
  `TauCeti.skewZigzagMk_ofArrow_mul_ofArrow_of_ne`: two arrows multiply to a volume class when the
  second is the reverse of the first, and to zero otherwise.
* `TauCeti.skewZigzagMk_vertexIdempotent_mul_skewZigzagVolume` and its three companions: the
  idempotent at the base of a volume class is a two-sided unit for it, and the other idempotents
  kill it.
* `TauCeti.skewZigzagMk_ofArrow_mul_skewZigzagVolume`,
  `TauCeti.skewZigzagVolume_mul_skewZigzagMk_ofArrow` and
  `TauCeti.skewZigzagVolume_mul_skewZigzagVolume`: every product reaching path length three
  vanishes.

## References

See C. Couture, *Skew-Zigzag Algebras*, Section 3, https://arxiv.org/abs/1509.08405.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]
  (c : SkewZigzagParameter k G)

/-! ### Products of vertex idempotents and arrows -/

/-- A vertex idempotent is idempotent in the skew-zigzag quotient. -/
@[simp]
theorem skewZigzagMk_vertexIdempotent_mul_self (i : V) :
    skewZigzagMk k G c (vertexIdempotent k (vertex G i)) *
        skewZigzagMk k G c (vertexIdempotent k (vertex G i)) =
      skewZigzagMk k G c (vertexIdempotent k (vertex G i)) := by
  rw [← map_mul, vertexIdempotent_mul_self]

/-- Distinct vertex idempotents are orthogonal in the skew-zigzag quotient. -/
@[simp]
theorem skewZigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne {i j : V} (h : i ≠ j) :
    skewZigzagMk k G c (vertexIdempotent k (vertex G i)) *
        skewZigzagMk k G c (vertexIdempotent k (vertex G j)) = 0 := by
  rw [← map_mul, vertexIdempotent_mul_vertexIdempotent_of_ne ((vertex_injective G).ne h),
    map_zero]

/-- The vertex idempotent at the head of a dart is a left unit for its arrow. -/
theorem skewZigzagMk_vertexIdempotent_mul_ofArrow (d : G.Dart) :
    skewZigzagMk k G c (vertexIdempotent k (vertex G d.snd)) *
        skewZigzagMk k G c (ofArrow (arrow G d.adj)) =
      skewZigzagMk k G c (ofArrow (arrow G d.adj)) := by
  rw [← map_mul, vertexIdempotent_mul_ofArrow]

/-- A vertex idempotent away from the head of a dart kills its arrow on the left. -/
theorem skewZigzagMk_vertexIdempotent_mul_ofArrow_of_ne {v : V} (d : G.Dart) (h : v ≠ d.snd) :
    skewZigzagMk k G c (vertexIdempotent k (vertex G v)) *
        skewZigzagMk k G c (ofArrow (arrow G d.adj)) = 0 := by
  rw [← map_mul, vertexIdempotent_mul_ofArrow_of_ne _ _ d.adj h, map_zero]

/-- The vertex idempotent at the tail of a dart is a right unit for its arrow. -/
theorem skewZigzagMk_ofArrow_mul_vertexIdempotent (d : G.Dart) :
    skewZigzagMk k G c (ofArrow (arrow G d.adj)) *
        skewZigzagMk k G c (vertexIdempotent k (vertex G d.fst)) =
      skewZigzagMk k G c (ofArrow (arrow G d.adj)) := by
  rw [← map_mul, ofArrow_mul_vertexIdempotent]

/-- A vertex idempotent away from the tail of a dart kills its arrow on the right. -/
theorem skewZigzagMk_ofArrow_mul_vertexIdempotent_of_ne {v : V} (d : G.Dart) (h : v ≠ d.fst) :
    skewZigzagMk k G c (ofArrow (arrow G d.adj)) *
        skewZigzagMk k G c (vertexIdempotent k (vertex G v)) = 0 := by
  rw [← map_mul, ofArrow_mul_vertexIdempotent_of_ne _ _ d.adj h, map_zero]

/-! ### Products of a vertex idempotent and a volume class -/

/-- The vertex idempotent at the base of a volume class is a left unit for it. -/
@[simp]
theorem skewZigzagMk_vertexIdempotent_mul_skewZigzagVolume {i : V} (e : {j : V // G.Adj i j}) :
    skewZigzagMk k G c (vertexIdempotent k (vertex G i)) * skewZigzagVolume k G c e =
      skewZigzagVolume k G c e := by
  rw [skewZigzagVolume_def, ← map_mul, vertexIdempotent_mul_backtrackElem]

/-- A vertex idempotent away from the base of a volume class kills it on the left. -/
@[simp]
theorem skewZigzagMk_vertexIdempotent_mul_skewZigzagVolume_of_ne {v i : V}
    (e : {j : V // G.Adj i j}) (h : v ≠ i) :
    skewZigzagMk k G c (vertexIdempotent k (vertex G v)) * skewZigzagVolume k G c e = 0 := by
  rw [skewZigzagVolume_def, ← map_mul, vertexIdempotent_mul_backtrackElem_of_ne _ _ e.2 h,
    map_zero]

/-- The vertex idempotent at the base of a volume class is a right unit for it. -/
@[simp]
theorem skewZigzagVolume_mul_skewZigzagMk_vertexIdempotent {i : V} (e : {j : V // G.Adj i j}) :
    skewZigzagVolume k G c e * skewZigzagMk k G c (vertexIdempotent k (vertex G i)) =
      skewZigzagVolume k G c e := by
  rw [skewZigzagVolume_def, ← map_mul, backtrackElem_mul_vertexIdempotent]

/-- A vertex idempotent away from the base of a volume class kills it on the right. -/
@[simp]
theorem skewZigzagVolume_mul_skewZigzagMk_vertexIdempotent_of_ne {i v : V}
    (e : {j : V // G.Adj i j}) (h : v ≠ i) :
    skewZigzagVolume k G c e * skewZigzagMk k G c (vertexIdempotent k (vertex G v)) = 0 := by
  rw [skewZigzagVolume_def, ← map_mul, backtrackElem_mul_vertexIdempotent_of_ne _ _ e.2 h,
    map_zero]

/-! ### Products of two arrows -/

/-- **Traversing a dart and returning is a volume class.** In the later-factor-first convention
the reverse dart is traversed first, so the composite is the volume class at the head of `d` taken
along the edge back to the tail of `d`. -/
theorem skewZigzagMk_ofArrow_mul_ofArrow_symm (d : G.Dart) :
    skewZigzagMk k G c (ofArrow (arrow G d.adj)) *
        skewZigzagMk k G c (ofArrow (arrow G d.symm.adj)) =
      skewZigzagVolume k G c (⟨d.fst, d.adj.symm⟩ : {j : V // G.Adj d.snd j}) := by
  have key : (ofArrow (arrow G d.adj) : pathAlgebra k (DoubledQuiver G))
      * ofArrow (arrow G d.symm.adj) = backtrackElem G k d.symm.adj :=
    ofArrow_symm_mul_ofArrow G k d.symm.adj
  rw [← map_mul, key, skewZigzagVolume_def]
  -- both backtracks run along the reverse of `d`; only the spelling of their endpoints differs
  rfl

/-- **Two arrows that are not reverse to one another multiply to zero.** Either they do not meet, in
which case the product already vanishes in the path algebra, or they meet and the composite is a
length-two path with distinct endpoints, which the skew-zigzag relations kill. -/
theorem skewZigzagMk_ofArrow_mul_ofArrow_of_ne {d e : G.Dart} (h : e ≠ d.symm) :
    skewZigzagMk k G c (ofArrow (arrow G d.adj)) *
        skewZigzagMk k G c (ofArrow (arrow G e.adj)) = 0 := by
  obtain ⟨⟨i, j⟩, hd⟩ := d
  obtain ⟨⟨a, b⟩, he⟩ := e
  rcases eq_or_ne b i with rfl | hbi
  · have hne : a ≠ j := fun hab => h (SimpleGraph.Dart.ext _ _ (by simp [hab]))
    rw [← map_mul, ofArrow_mul_ofArrow G k he hd]
    exact skewZigzagMk_ofPath_eq_zero_of_ne k G c _ (by simp) (by simpa using hne)
  · rw [← map_mul, ofArrow_mul_ofArrow_of_ne G k he hd (Ne.symm hbi), map_zero]

/-! ### Products reaching path length three -/

/-- A product of two path classes vanishes when their total path length is at least three. -/
theorem skewZigzagMk_ofPath_mul_ofPath_eq_zero_of_three_le
    (x y : Quiver.TotalPath (DoubledQuiver G))
    (h : 3 ≤ x.2.2.length + y.2.2.length) :
    skewZigzagMk k G c (ofPath x * ofPath y) = 0 := by
  obtain ⟨a, b, p⟩ := x
  obtain ⟨d, e, q⟩ := y
  rcases eq_or_ne e a with rfl | hea
  · rw [ofPath_mul_ofPath_of_comp]
    exact skewZigzagMk_ofPath_eq_zero_of_three_le k G c _
      (by simpa only [_root_.Quiver.Path.length_comp, Nat.add_comm] using h)
  · rw [ofPath_mul_ofPath_of_not_composable hea, map_zero]

/-- An arrow times a volume class vanishes: the composite has path length three. -/
theorem skewZigzagMk_ofArrow_mul_skewZigzagVolume (d : G.Dart) {i : V}
    (e : {j : V // G.Adj i j}) :
    skewZigzagMk k G c (ofArrow (arrow G d.adj)) * skewZigzagVolume k G c e = 0 := by
  rw [skewZigzagVolume_def, ← map_mul, backtrackElem_eq_ofPath, ofArrow_eq_ofPath_arrowPath]
  exact skewZigzagMk_ofPath_mul_ofPath_eq_zero_of_three_le k G c _ _
    (by simp [length_backtrackPath, length_arrowPath])

/-- A volume class times an arrow vanishes: the composite has path length three. -/
theorem skewZigzagVolume_mul_skewZigzagMk_ofArrow {i : V} (e : {j : V // G.Adj i j})
    (d : G.Dart) :
    skewZigzagVolume k G c e * skewZigzagMk k G c (ofArrow (arrow G d.adj)) = 0 := by
  rw [skewZigzagVolume_def, ← map_mul, backtrackElem_eq_ofPath, ofArrow_eq_ofPath_arrowPath]
  exact skewZigzagMk_ofPath_mul_ofPath_eq_zero_of_three_le k G c _ _
    (by simp [length_backtrackPath, length_arrowPath])

/-- Two volume classes multiply to zero: they either do not meet or compose to path length four. -/
@[simp]
theorem skewZigzagVolume_mul_skewZigzagVolume {i i' : V} (e : {j : V // G.Adj i j})
    (e' : {j : V // G.Adj i' j}) :
    skewZigzagVolume k G c e * skewZigzagVolume k G c e' = 0 := by
  rw [skewZigzagVolume_def, skewZigzagVolume_def, ← map_mul, backtrackElem_eq_ofPath,
    backtrackElem_eq_ofPath]
  exact skewZigzagMk_ofPath_mul_ofPath_eq_zero_of_three_le k G c _ _
    (by simp [length_backtrackPath])

end TauCeti
