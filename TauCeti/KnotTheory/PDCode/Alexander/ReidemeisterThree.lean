/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Alexander.Basic
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Three
import TauCeti.Algebra.Module.Basic

/-!
# The Alexander module under the third Reidemeister move

The third Reidemeister move on an oriented PD-code, `TauCeti.OrientedPDCode.reidemeisterThree`,
replaces the triangular tangle `σ₁ σ₂ σ₁` at three crossings by `σ₂ σ₁ σ₂`. This file shows that,
whenever the three crossings form a Reidemeister triangle
(`TauCeti.PDCode.HasReidemeisterThreeTriangle`), the move keeps the Alexander module
(`TauCeti.OrientedPDCode.AlexanderModule`) up to `ℤ[T;T⁻¹]`-linear equivalence, and therefore every
elementary ideal. All six height orders of the three strands and all eight orientations are
covered.

The argument reads each crossing from its slots `0` and `3`. At every crossing of either triangle,
one strand runs from slot `0` to slot `2` and the other from slot `3` to slot `1`, so the relations
of the crossing express the generators of slots `2` and `1` as affine combinations
`w • x + (1 - w) • y` of those of slots `0` and `3`, with weight `w = 1` on the over-strand
(`TauCeti.OrientedPDCode.alexanderGenerator_crossing_two`). The relations of each triangle thus
compute the three values leaving the triangle from the three values entering it, passing the three
crossings in opposite orders before and after the move. The move permutes the weights as it
permutes the crossing signs (`TauCeti.OrientedPDCode.alexanderWeight_reidemeisterThree`), and the
strand on top acts on the other two by the same weight, up to inversion when it is read from
opposite sides; the two computations then agree
(`TauCeti.smul_add_one_sub_smul_braid_relation`). This is the self-distributivity of the Alexander
quandle.

The equivalence sends the generator of a half-edge to the generator of the half-edge it is moved
from, except on the three arcs inside the triangle, whose generators are expressed through the
relations of the triangle.

## Main definitions

* `TauCeti.OrientedPDCode.alexanderModuleReidemeisterThreeEquiv`: the third Reidemeister move keeps
  the Alexander module.

## Main results

* `TauCeti.OrientedPDCode.alexanderWeight_reidemeisterThree`: the move exchanges the weights of the
  first and third crossing of the triangle.
* `TauCeti.OrientedPDCode.elementaryIdeal_reidemeisterThree`: the move keeps every elementary ideal.

## References

* R. H. Crowell, R. H. Fox, *Introduction to Knot Theory*, Graduate Texts in Mathematics 57,
  Springer (1977), Chapters VI and VII.
* D. Joyce, *A classifying invariant of knots, the knot quandle*, J. Pure Appl. Algebra 23 (1982),
  37–65 (the third Reidemeister move as self-distributivity).
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Graduate Texts in Mathematics 175,
  Springer (1997), Chapters 1 and 6.
-/

public section

noncomputable section

open LaurentPolynomial

namespace TauCeti

open PDCode

namespace OrientedPDCode

variable {n : ℕ}

/-! ### The weights of the three crossings of a Reidemeister triangle -/

section Triangle

variable (D : OrientedPDCode n) (c : Fin 3 ↪ Fin n)

private theorem crossing_reidemeisterThree (i : Fin n) (s : Fin 4) :
    (D.reidemeisterThree c).crossing i s = D.crossing i s := by
  rw [toPDCode_reidemeisterThree, reidemeisterThree_crossing]

/-- Along each strand of the triangle, the slots facing the top of the tangle share their
orientation: the first strand at its two crossings, the second strand at the crossings `c 0`
and `c 2`, the third strand at the crossings `c 1` and `c 2`. -/
private theorem orientation_triangle (h : D.HasReidemeisterThreeTriangleArcs c) :
    D.orientation (D.crossing (c 1) 0) = D.orientation (D.crossing (c 0) 0) ∧
    D.orientation (D.crossing (c 2) 0) = D.orientation (D.crossing (c 0) 3) ∧
    D.orientation (D.crossing (c 2) 3) = D.orientation (D.crossing (c 1) 3) := by
  obtain ⟨ha, hb, hc⟩ := (hasReidemeisterThreeTriangleArcs_iff D.toPDCode c).mp h
  refine ⟨?_, ?_, ?_⟩
  · rw [← ha, D.orientation_edgePair, D.orientation_crossing_of_add_two_eq _ (s := 0) (t := 2) rfl,
      Bool.not_not]
  · rw [← hc, D.orientation_edgePair, D.orientation_crossing_of_add_two_eq _ (s := 3) (t := 1) rfl,
      Bool.not_not]
  · rw [← hb, D.orientation_edgePair, D.orientation_crossing_of_add_two_eq _ (s := 3) (t := 1) rfl,
      Bool.not_not]

/-- **The oriented third Reidemeister move permutes the weights of the Alexander relations**
exactly as it permutes the crossing signs: the first and the third crossing of the triangle
exchange their weights, and every other crossing keeps them. -/
@[simp]
theorem alexanderWeight_reidemeisterThree (h : D.HasReidemeisterThreeTriangleArcs c) (i : Fin n)
    (slot : Fin 4) :
    (D.reidemeisterThree c).alexanderWeight i slot =
      D.alexanderWeight (Equiv.swap (c 0) (c 2) i) slot := by
  obtain ⟨h₁, h₂, h₃⟩ := D.orientation_triangle c h
  simp only [crossing_apply] at h₁ h₂ h₃
  -- The over-pair indicators are exchanged like the crossings; it remains to compare the
  -- orientations at the slots `0` and `3`.
  refine alexanderWeight_eq_of_orientation_eq _ _ (by simp) ?_ ?_ slot
  all_goals
    rw [crossing_reidemeisterThree]
    by_cases hi : i ∈ Set.range c
    · obtain ⟨j, rfl⟩ := hi
      rw [← c.injective.map_swap, orientation_reidemeisterThree_crossing]
      fin_cases j <;> simp [reidemeisterThreeSlots_symm_apply, Equiv.swap_apply_def, h₁, h₂, h₃]
    · rw [Equiv.swap_apply_of_ne_of_ne (fun h ↦ hi ⟨0, h.symm⟩) (fun h ↦ hi ⟨2, h.symm⟩),
        orientation_reidemeisterThree_crossing_of_notMem _ _ hi]

/-- The weights of the three crossings of a Reidemeister triangle, by the strand on top: the
first strand (over at `c 0` and `c 1`), the third strand (over at `c 1` and `c 2`), or the second
strand (over at `c 0` and `c 2`). The top strand acts on the other two strands by the same weight,
up to an inversion when it is read from opposite sides at its two crossings. -/
private theorem alexanderWeight_triangle (h : D.HasReidemeisterThreeTriangle c) :
    (D.alexanderWeight (c 0) 0 = 1 ∧ D.alexanderWeight (c 1) 0 = 1 ∧
        D.alexanderWeight (c 0) 3 = D.alexanderWeight (c 1) 3 ∧
        (D.alexanderWeight (c 2) 0 = 1 ∨ D.alexanderWeight (c 2) 3 = 1)) ∨
      (D.alexanderWeight (c 1) 3 = 1 ∧ D.alexanderWeight (c 2) 3 = 1 ∧
        D.alexanderWeight (c 1) 0 = D.alexanderWeight (c 2) 0 ∧
        (D.alexanderWeight (c 0) 0 = 1 ∨ D.alexanderWeight (c 0) 3 = 1)) ∨
      (D.alexanderWeight (c 0) 3 = 1 ∧ D.alexanderWeight (c 2) 0 = 1 ∧
        D.alexanderWeight (c 0) 0 * D.alexanderWeight (c 2) 3 = 1 ∧
        (D.alexanderWeight (c 1) 0 = 1 ∨ D.alexanderWeight (c 1) 3 = 1)) := by
  obtain ⟨h₁, h₂, h₃⟩ := D.orientation_triangle c h.arcs
  obtain ⟨-, -, -, hacyc⟩ := (hasReidemeisterThreeTriangle_iff D.toPDCode c).mp h
  cases hb₀ : D.overPair (c 0) <;> cases hb₁ : D.overPair (c 1) <;>
    cases hb₂ : D.overPair (c 2) <;> simp [hb₀, hb₁, hb₂] at hacyc
  -- The first strand is on top.
  any_goals
    refine .inl ⟨D.alexanderWeight_zero_of_overPair_false _ hb₀,
      D.alexanderWeight_zero_of_overPair_false _ hb₁, ?_,
      D.alexanderWeight_zero_eq_one_or_three_eq_one _⟩
    rw [D.alexanderWeight_three_of_overPair_false _ hb₀,
      D.alexanderWeight_three_of_overPair_false _ hb₁, h₁]
  -- The third strand is on top.
  any_goals
    refine .inr <| .inl ⟨D.alexanderWeight_three_of_overPair_true _ hb₁,
      D.alexanderWeight_three_of_overPair_true _ hb₂, ?_,
      D.alexanderWeight_zero_eq_one_or_three_eq_one _⟩
    rw [D.alexanderWeight_zero_of_overPair_true _ hb₁,
      D.alexanderWeight_zero_of_overPair_true _ hb₂, h₃]
  -- The second strand is on top.
  all_goals
    refine .inr <| .inr ⟨D.alexanderWeight_three_of_overPair_true _ hb₀,
      D.alexanderWeight_zero_of_overPair_false _ hb₂, ?_,
      D.alexanderWeight_zero_eq_one_or_three_eq_one _⟩
    rw [D.alexanderWeight_zero_of_overPair_true _ hb₀,
      D.alexanderWeight_three_of_overPair_false _ hb₂, h₂, ← T_add]
    cases D.orientation (D.crossing (c 0) 3) <;> simp

end Triangle

/-! ### Values on the arcs of a triangle -/

section ArcValue

variable {M : Type*} (k₁ k₁' k₂ k₂' k₃ k₃' : Fin (4 * n)) (m₁ m₂ m₃ : M) (f : Fin (4 * n) → M)

/-- The family of values taking the value `m₁` on the arc `{k₁, k₁'}`, `m₂` on `{k₂, k₂'}`, `m₃` on
`{k₃, k₃'}`, and agreeing with `f` on every other half-edge. -/
private def arcValue (x : Fin (4 * n)) : M :=
  if x = k₁ ∨ x = k₁' then m₁ else if x = k₂ ∨ x = k₂' then m₂
  else if x = k₃ ∨ x = k₃' then m₃ else f x

private theorem arcValue_of_left₁ {x : Fin (4 * n)} (hx : x = k₁ ∨ x = k₁') :
    arcValue k₁ k₁' k₂ k₂' k₃ k₃' m₁ m₂ m₃ f x = m₁ := by
  rw [arcValue, ite_eq_left hx]

private theorem arcValue_of_left₂ {x : Fin (4 * n)} (hx₁ : ¬(x = k₁ ∨ x = k₁'))
    (hx : x = k₂ ∨ x = k₂') : arcValue k₁ k₁' k₂ k₂' k₃ k₃' m₁ m₂ m₃ f x = m₂ := by
  rw [arcValue, ite_eq_right hx₁, ite_eq_left hx]

private theorem arcValue_of_left₃ {x : Fin (4 * n)} (hx₁ : ¬(x = k₁ ∨ x = k₁'))
    (hx₂ : ¬(x = k₂ ∨ x = k₂')) (hx : x = k₃ ∨ x = k₃') :
    arcValue k₁ k₁' k₂ k₂' k₃ k₃' m₁ m₂ m₃ f x = m₃ := by
  rw [arcValue, ite_eq_right hx₁, ite_eq_right hx₂, ite_eq_left hx]

private theorem arcValue_of_not {x : Fin (4 * n)} (hx₁ : ¬(x = k₁ ∨ x = k₁'))
    (hx₂ : ¬(x = k₂ ∨ x = k₂')) (hx₃ : ¬(x = k₃ ∨ x = k₃')) :
    arcValue k₁ k₁' k₂ k₂' k₃ k₃' m₁ m₂ m₃ f x = f x := by
  rw [arcValue, ite_eq_right hx₁, ite_eq_right hx₂, ite_eq_right hx₃]

/-- If the three arcs are arcs of a perfect matching `e` and `f` is constant on the arcs of `e`,
then so is the family of values. -/
private theorem arcValue_val (e : PerfectMatching (Fin (4 * n))) (h₁ : e.val k₁ = k₁')
    (h₂ : e.val k₂ = k₂') (h₃ : e.val k₃ = k₃') (hf : ∀ x, f (e.val x) = f x) (x : Fin (4 * n)) :
    arcValue k₁ k₁' k₂ k₂' k₃ k₃' m₁ m₂ m₃ f (e.val x) =
      arcValue k₁ k₁' k₂ k₂' k₃ k₃' m₁ m₂ m₃ f x := by
  have key (k : Fin (4 * n)) : (e.val x = k ∨ e.val x = e.val k) ↔ (x = k ∨ x = e.val k) := by
    rw [Equiv.apply_eq_iff_eq]
    constructor <;> rintro (hx | hx)
    · exact .inr (by rw [← hx, e.apply_apply])
    · exact .inl hx
    · exact .inr hx
    · exact .inl (by rw [hx, e.apply_apply])
  subst h₁ h₂ h₃
  simp only [arcValue, key, hf]

end ArcValue

/-! ### The Alexander module under the third Reidemeister move -/

section ReidemeisterThree

variable (D : OrientedPDCode n) (c : Fin 3 ↪ Fin n)

private theorem reidemeisterThreePerm_crossing_eq {j k : Fin 3} {s t : Fin 4}
    (h : reidemeisterThreeSlots (j, s) = (k, t)) :
    D.reidemeisterThreePerm c (D.crossing (c j) s) = D.crossing (c k) t := by
  rw [reidemeisterThreePerm_apply_crossing, h]

private theorem reidemeisterThreePerm_symm_crossing_eq {j k : Fin 3} {s t : Fin 4}
    (h : reidemeisterThreeSlots (k, t) = (j, s)) :
    (D.reidemeisterThreePerm c).symm (D.crossing (c j) s) = D.crossing (c k) t := by
  rw [Equiv.symm_apply_eq, reidemeisterThreePerm_crossing_eq D c h]

private theorem edgePair_reidemeisterThree (x : Fin (4 * n)) :
    (D.reidemeisterThree c).edgePair.val (D.reidemeisterThreePerm c x) =
      D.reidemeisterThreePerm c (D.edgePair.val x) := by
  rw [toPDCode_reidemeisterThree]
  exact reidemeisterThree_edgePair_transport D.toPDCode c x

/-- The three arcs inside the new triangle. -/
private theorem edgePair_reidemeisterThree_triangle (h : D.HasReidemeisterThreeTriangleArcs c) :
    (D.reidemeisterThree c).edgePair.val (D.crossing (c 0) 1) = D.crossing (c 1) 3 ∧
    (D.reidemeisterThree c).edgePair.val (D.crossing (c 1) 2) = D.crossing (c 2) 0 ∧
    (D.reidemeisterThree c).edgePair.val (D.crossing (c 0) 2) = D.crossing (c 2) 3 := by
  rw [toPDCode_reidemeisterThree]
  exact reidemeisterThree_triangleArcs D.toPDCode c h

/-- The generator of the new code at the image of a half-edge only depends on the arc of the
half-edge. -/
private theorem alexanderGenerator_reidemeisterThreePerm_edgePair (x : Fin (4 * n)) :
    (D.reidemeisterThree c).alexanderGenerator
        (.inl (D.reidemeisterThreePerm c (D.edgePair.val x))) =
      (D.reidemeisterThree c).alexanderGenerator (.inl (D.reidemeisterThreePerm c x)) := by
  rw [← edgePair_reidemeisterThree, alexanderGenerator_edgePair]

/-! #### From the old code to the new one -/

/-- The value of the arc of the first strand inside the old triangle, in the new code. -/
private def fwdMid₀ : (D.reidemeisterThree c).AlexanderModule :=
  D.alexanderWeight (c 0) 0 •
      (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 1) 0)) +
    (1 - D.alexanderWeight (c 0) 0) •
      (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 0) 0))

/-- The value of the arc of the second strand inside the old triangle, in the new code. -/
private def fwdMid₁ : (D.reidemeisterThree c).AlexanderModule :=
  D.alexanderWeight (c 0) 3 •
      (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 0) 0)) +
    (1 - D.alexanderWeight (c 0) 3) •
      (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 1) 0))

/-- The value of the arc of the third strand inside the old triangle, in the new code. -/
private def fwdMid₂ : (D.reidemeisterThree c).AlexanderModule :=
  D.alexanderWeight (c 1) 3 •
      (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 0) 3)) +
    (1 - D.alexanderWeight (c 1) 3) • fwdMid₀ D c

/-- The image of the generator of each half-edge of the old code in the Alexander module of the new
code: the generator of the half-edge it is moved to, except on the three arcs inside the
triangle. -/
private def fwdValue (x : Fin (4 * n)) : (D.reidemeisterThree c).AlexanderModule :=
  arcValue (D.crossing (c 0) 2) (D.crossing (c 1) 0) (D.crossing (c 0) 1) (D.crossing (c 2) 0)
    (D.crossing (c 1) 1) (D.crossing (c 2) 3) (fwdMid₀ D c) (fwdMid₁ D c) (fwdMid₂ D c)
    (fun y ↦ (D.reidemeisterThree c).alexanderGenerator (.inl (D.reidemeisterThreePerm c y))) x

/-- The weights of the crossings of the new triangle are those of the old crossings formed by the
same two strands. -/
private theorem alexanderWeight_reidemeisterThree_triangle
    (h : D.HasReidemeisterThreeTriangleArcs c) (slot : Fin 4) :
    (D.reidemeisterThree c).alexanderWeight (c 0) slot = D.alexanderWeight (c 2) slot ∧
    (D.reidemeisterThree c).alexanderWeight (c 1) slot = D.alexanderWeight (c 1) slot ∧
    (D.reidemeisterThree c).alexanderWeight (c 2) slot = D.alexanderWeight (c 0) slot := by
  rw [alexanderWeight_reidemeisterThree D c h, alexanderWeight_reidemeisterThree D c h,
    alexanderWeight_reidemeisterThree D c h, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne (c.injective.ne (by decide)) (c.injective.ne (by decide))]
  exact ⟨rfl, rfl, rfl⟩

/-- The relations of the new code at its triangle, with the old weights: the three crossings of the
new triangle meet the strands in the order opposite to the old one. -/
private theorem fwd_braid (h : D.HasReidemeisterThreeTriangle c) :
    (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 2) 2)) =
        D.alexanderWeight (c 1) 0 • fwdMid₀ D c + (1 - D.alexanderWeight (c 1) 0) •
          (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 0) 3)) ∧
      (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 2) 1)) =
        D.alexanderWeight (c 2) 0 • fwdMid₁ D c + (1 - D.alexanderWeight (c 2) 0) • fwdMid₂ D c ∧
      (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 1) 1)) =
        D.alexanderWeight (c 2) 3 • fwdMid₂ D c +
          (1 - D.alexanderWeight (c 2) 3) • fwdMid₁ D c := by
  obtain ⟨h01, h12, h02⟩ := edgePair_reidemeisterThree_triangle D c h.arcs
  have w₀ := alexanderWeight_reidemeisterThree_triangle D c h.arcs 0
  have w₃ := alexanderWeight_reidemeisterThree_triangle D c h.arcs 3
  have r0₂ := (D.reidemeisterThree c).alexanderGenerator_crossing_two (c 0)
  have r0₁ := (D.reidemeisterThree c).alexanderGenerator_crossing_add_two (c 0) 3
  have r1₂ := (D.reidemeisterThree c).alexanderGenerator_crossing_two (c 1)
  have r1₁ := (D.reidemeisterThree c).alexanderGenerator_crossing_add_two (c 1) 3
  have r2₂ := (D.reidemeisterThree c).alexanderGenerator_crossing_two (c 2)
  have r2₁ := (D.reidemeisterThree c).alexanderGenerator_crossing_add_two (c 2) 3
  simp only [crossing_reidemeisterThree, w₀, w₃, Fin.reduceAdd] at r0₂ r0₁ r1₂ r1₁ r2₂ r2₁
  -- The arcs inside the new triangle identify the generators at their two ends.
  rw [← h01, alexanderGenerator_edgePair] at r1₂ r1₁
  rw [← h12, alexanderGenerator_edgePair, ← h02, alexanderGenerator_edgePair] at r2₂ r2₁
  obtain ⟨k₁, k₂, k₃⟩ := smul_add_one_sub_smul_braid_relation (D.alexanderWeight_triangle c h)
    (a := (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 1) 0)))
    (b := (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 0) 0)))
    (c := (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 0) 3)))
    (x₁ := fwdMid₀ D c) (y₁ := fwdMid₁ D c) (z₁ := fwdMid₂ D c) rfl rfl rfl r0₂ r0₁ r1₂
  exact ⟨r2₂.trans k₁.symm, r2₁.trans k₂.symm, r1₁.trans k₃.symm⟩

private theorem fwdValue_edgePair (h : D.HasReidemeisterThreeTriangleArcs c) (x : Fin (4 * n)) :
    fwdValue D c (D.edgePair.val x) = fwdValue D c x := by
  obtain ⟨ha, hb, hc⟩ := (hasReidemeisterThreeTriangleArcs_iff D.toPDCode c).mp h
  exact arcValue_val _ _ _ _ _ _ _ _ _ _ D.edgePair ha hc hb
    (alexanderGenerator_reidemeisterThreePerm_edgePair D c) x

private theorem fwdValue_of_notMem {i : Fin n} (hi : i ∉ Set.range c) (s : Fin 4) :
    fwdValue D c (D.crossing i s) =
      (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing i s)) := by
  have h₀ : i ≠ c 0 := fun h ↦ hi ⟨0, h.symm⟩
  have h₁ : i ≠ c 1 := fun h ↦ hi ⟨1, h.symm⟩
  have h₂ : i ≠ c 2 := fun h ↦ hi ⟨2, h.symm⟩
  rw [fwdValue, arcValue_of_not _ _ _ _ _ _ _ _ _ _ (by simp [h₀, h₁]) (by simp [h₀, h₂])
    (by simp [h₁, h₂]), reidemeisterThreePerm_crossing_of_notMem _ _ hi]

private theorem fwdValue_boundary {j k : Fin 3} {s t : Fin 4}
    (hst : reidemeisterThreeSlots (j, s) = (k, t))
    (h₁ : ¬(D.crossing (c j) s = D.crossing (c 0) 2 ∨ D.crossing (c j) s = D.crossing (c 1) 0))
    (h₂ : ¬(D.crossing (c j) s = D.crossing (c 0) 1 ∨ D.crossing (c j) s = D.crossing (c 2) 0))
    (h₃ : ¬(D.crossing (c j) s = D.crossing (c 1) 1 ∨ D.crossing (c j) s = D.crossing (c 2) 3)) :
    fwdValue D c (D.crossing (c j) s) =
      (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c k) t)) := by
  rw [fwdValue, arcValue_of_not _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃,
    reidemeisterThreePerm_crossing_eq D c hst]

/-- The values `fwdValue` satisfy the relations of the old code at the three crossings of its
triangle. -/
private theorem fwdValue_downward (h : D.HasReidemeisterThreeTriangle c) (j : Fin 3) :
    fwdValue D c (D.crossing (c j) 2) =
        D.alexanderWeight (c j) 0 • fwdValue D c (D.crossing (c j) 0) +
          (1 - D.alexanderWeight (c j) 0) • fwdValue D c (D.crossing (c j) 3) ∧
      fwdValue D c (D.crossing (c j) 1) =
        D.alexanderWeight (c j) 3 • fwdValue D c (D.crossing (c j) 3) +
          (1 - D.alexanderWeight (c j) 3) • fwdValue D c (D.crossing (c j) 0) := by
  obtain ⟨k₁, k₂, k₃⟩ := fwd_braid D c h
  have v₀₂ : fwdValue D c (D.crossing (c 0) 2) = fwdMid₀ D c :=
    arcValue_of_left₁ _ _ _ _ _ _ _ _ _ _ (.inl rfl)
  have v₁₀ : fwdValue D c (D.crossing (c 1) 0) = fwdMid₀ D c :=
    arcValue_of_left₁ _ _ _ _ _ _ _ _ _ _ (.inr rfl)
  have v₀₁ : fwdValue D c (D.crossing (c 0) 1) = fwdMid₁ D c :=
    arcValue_of_left₂ _ _ _ _ _ _ _ _ _ _ (by simp) (.inl rfl)
  have v₂₀ : fwdValue D c (D.crossing (c 2) 0) = fwdMid₁ D c :=
    arcValue_of_left₂ _ _ _ _ _ _ _ _ _ _ (by simp) (.inr rfl)
  have v₁₁ : fwdValue D c (D.crossing (c 1) 1) = fwdMid₂ D c :=
    arcValue_of_left₃ _ _ _ _ _ _ _ _ _ _ (by simp) (by simp) (.inl rfl)
  have v₂₃ : fwdValue D c (D.crossing (c 2) 3) = fwdMid₂ D c :=
    arcValue_of_left₃ _ _ _ _ _ _ _ _ _ _ (by simp) (by simp) (.inr rfl)
  have v₀₀ : fwdValue D c (D.crossing (c 0) 0) =
      (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 1) 0)) :=
    fwdValue_boundary D c (by simp [reidemeisterThreeSlots_apply]) (by simp) (by simp) (by simp)
  have v₀₃ : fwdValue D c (D.crossing (c 0) 3) =
      (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 0) 0)) :=
    fwdValue_boundary D c (by simp [reidemeisterThreeSlots_apply]) (by simp) (by simp) (by simp)
  have v₁₃ : fwdValue D c (D.crossing (c 1) 3) =
      (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 0) 3)) :=
    fwdValue_boundary D c (by simp [reidemeisterThreeSlots_apply]) (by simp) (by simp) (by simp)
  have v₁₂ : fwdValue D c (D.crossing (c 1) 2) =
      (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 2) 2)) :=
    fwdValue_boundary D c (by simp [reidemeisterThreeSlots_apply]) (by simp) (by simp) (by simp)
  have v₂₂ : fwdValue D c (D.crossing (c 2) 2) =
      (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 2) 1)) :=
    fwdValue_boundary D c (by simp [reidemeisterThreeSlots_apply]) (by simp) (by simp) (by simp)
  have v₂₁ : fwdValue D c (D.crossing (c 2) 1) =
      (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 1) 1)) :=
    fwdValue_boundary D c (by simp [reidemeisterThreeSlots_apply]) (by simp) (by simp) (by simp)
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
  · exact ⟨by rw [v₀₂, v₀₀, v₀₃]; rfl, by rw [v₀₁, v₀₃, v₀₀]; rfl⟩
  · exact ⟨by rw [v₁₂, v₁₀, v₁₃, k₁], by rw [v₁₁, v₁₃, v₁₀]; rfl⟩
  · exact ⟨by rw [v₂₂, v₂₀, v₂₃, k₂], by rw [v₂₁, v₂₃, v₂₀, k₃]⟩

/-- The map from the Alexander module of the old code to that of the new code. -/
private def fwdHom (h : D.HasReidemeisterThreeTriangle c) :
    D.AlexanderModule →ₗ[ℤ[T;T⁻¹]] (D.reidemeisterThree c).AlexanderModule :=
  D.alexanderLift
    (Sum.elim (fwdValue D c)
      fun k ↦ (D.reidemeisterThree c).alexanderGenerator (.inr (Fin.cast (by simp) k)))
    (fun x ↦ by simpa only [Sum.elim_inl] using fwdValue_edgePair D c h.arcs x)
    (fun i slot ↦ by
      simp only [Sum.elim_inl]
      by_cases hi : i ∈ Set.range c
      · obtain ⟨j, rfl⟩ := hi
        exact apply_crossing_add_two_of_two_of_one D (fwdValue D c) (c j)
          (fwdValue_downward D c h j).1 (fwdValue_downward D c h j).2 slot
      · have := (D.reidemeisterThree c).alexanderGenerator_crossing_add_two i slot
        rwa [crossing_reidemeisterThree, crossing_reidemeisterThree, crossing_reidemeisterThree,
          alexanderWeight_reidemeisterThree D c h.arcs, Equiv.swap_apply_of_ne_of_ne
            (fun h ↦ hi ⟨0, h.symm⟩) (fun h ↦ hi ⟨2, h.symm⟩), ← fwdValue_of_notMem D c hi,
          ← fwdValue_of_notMem D c hi, ← fwdValue_of_notMem D c hi] at this)

/-! #### From the new code to the old one -/

/-- The value of the arc of the second strand inside the new triangle, in the old code. -/
private def bwdMid₁ : D.AlexanderModule :=
  D.alexanderWeight (c 2) 0 • D.alexanderGenerator (.inl (D.crossing (c 0) 3)) +
    (1 - D.alexanderWeight (c 2) 0) • D.alexanderGenerator (.inl (D.crossing (c 1) 3))

/-- The value of the arc of the third strand inside the new triangle, in the old code. -/
private def bwdMid₂ : D.AlexanderModule :=
  D.alexanderWeight (c 2) 3 • D.alexanderGenerator (.inl (D.crossing (c 1) 3)) +
    (1 - D.alexanderWeight (c 2) 3) • D.alexanderGenerator (.inl (D.crossing (c 0) 3))

/-- The value of the arc of the first strand inside the new triangle, in the old code. -/
private def bwdMid₀ : D.AlexanderModule :=
  D.alexanderWeight (c 1) 0 • D.alexanderGenerator (.inl (D.crossing (c 0) 0)) +
    (1 - D.alexanderWeight (c 1) 0) • bwdMid₂ D c

/-- The image of the generator of each half-edge of the new code in the Alexander module of the old
code: the generator of the half-edge it is moved from, except on the three arcs inside the
triangle. -/
private def bwdValue (x : Fin (4 * n)) : D.AlexanderModule :=
  arcValue (D.crossing (c 1) 2) (D.crossing (c 2) 0) (D.crossing (c 0) 2) (D.crossing (c 2) 3)
    (D.crossing (c 0) 1) (D.crossing (c 1) 3) (bwdMid₀ D c) (bwdMid₁ D c) (bwdMid₂ D c)
    (fun y ↦ D.alexanderGenerator (.inl ((D.reidemeisterThreePerm c).symm y))) x

/-- The relations of the old code at its triangle, read in the order of the new triangle. -/
private theorem bwd_braid (h : D.HasReidemeisterThreeTriangle c) :
    D.alexanderGenerator (.inl (D.crossing (c 2) 1)) =
        D.alexanderWeight (c 1) 3 • bwdMid₂ D c +
          (1 - D.alexanderWeight (c 1) 3) • D.alexanderGenerator (.inl (D.crossing (c 0) 0)) ∧
      D.alexanderGenerator (.inl (D.crossing (c 1) 2)) =
        D.alexanderWeight (c 0) 0 • bwdMid₀ D c + (1 - D.alexanderWeight (c 0) 0) • bwdMid₁ D c ∧
      D.alexanderGenerator (.inl (D.crossing (c 2) 2)) =
        D.alexanderWeight (c 0) 3 • bwdMid₁ D c +
          (1 - D.alexanderWeight (c 0) 3) • bwdMid₀ D c := by
  obtain ⟨ha, hb, hc⟩ := (hasReidemeisterThreeTriangleArcs_iff D.toPDCode c).mp h.arcs
  have r0₂ := D.alexanderGenerator_crossing_two (c 0)
  have r0₁ := D.alexanderGenerator_crossing_add_two (c 0) 3
  have r1₂ := D.alexanderGenerator_crossing_two (c 1)
  have r1₁ := D.alexanderGenerator_crossing_add_two (c 1) 3
  have r2₂ := D.alexanderGenerator_crossing_two (c 2)
  have r2₁ := D.alexanderGenerator_crossing_add_two (c 2) 3
  simp only [Fin.reduceAdd] at r0₁ r1₁ r2₁
  -- The arcs inside the old triangle identify the generators at their two ends.
  rw [← ha, alexanderGenerator_edgePair] at r1₂ r1₁
  rw [← hb, alexanderGenerator_edgePair, ← hc, alexanderGenerator_edgePair] at r2₂ r2₁
  obtain ⟨k₁, k₂, k₃⟩ := smul_add_one_sub_smul_braid_relation (D.alexanderWeight_triangle c h)
    (x₁' := bwdMid₀ D c) (y₁' := bwdMid₁ D c) (z₁' := bwdMid₂ D c) r0₂ r0₁ r1₁ rfl rfl rfl
  exact ⟨r2₁.trans k₃, r1₂.trans k₁, r2₂.trans k₂⟩

private theorem bwdValue_edgePair (h : D.HasReidemeisterThreeTriangleArcs c) (x : Fin (4 * n)) :
    bwdValue D c ((D.reidemeisterThree c).edgePair.val x) = bwdValue D c x := by
  obtain ⟨h01, h12, h02⟩ := edgePair_reidemeisterThree_triangle D c h
  refine arcValue_val _ _ _ _ _ _ _ _ _ _ (D.reidemeisterThree c).edgePair h12 h02 h01
    (fun y ↦ ?_) x
  obtain ⟨z, rfl⟩ := (D.reidemeisterThreePerm c).surjective y
  rw [edgePair_reidemeisterThree, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    alexanderGenerator_edgePair]

private theorem bwdValue_of_notMem {i : Fin n} (hi : i ∉ Set.range c) (s : Fin 4) :
    bwdValue D c (D.crossing i s) = D.alexanderGenerator (.inl (D.crossing i s)) := by
  have h₀ : i ≠ c 0 := fun h ↦ hi ⟨0, h.symm⟩
  have h₁ : i ≠ c 1 := fun h ↦ hi ⟨1, h.symm⟩
  have h₂ : i ≠ c 2 := fun h ↦ hi ⟨2, h.symm⟩
  rw [bwdValue, arcValue_of_not _ _ _ _ _ _ _ _ _ _ (by simp [h₁, h₂]) (by simp [h₀, h₂])
    (by simp [h₀, h₁])]
  congr 2
  rw [Equiv.symm_apply_eq, reidemeisterThreePerm_crossing_of_notMem _ _ hi]

private theorem bwdValue_boundary {j k : Fin 3} {s t : Fin 4}
    (hst : reidemeisterThreeSlots (k, t) = (j, s))
    (h₁ : ¬(D.crossing (c j) s = D.crossing (c 1) 2 ∨ D.crossing (c j) s = D.crossing (c 2) 0))
    (h₂ : ¬(D.crossing (c j) s = D.crossing (c 0) 2 ∨ D.crossing (c j) s = D.crossing (c 2) 3))
    (h₃ : ¬(D.crossing (c j) s = D.crossing (c 0) 1 ∨ D.crossing (c j) s = D.crossing (c 1) 3)) :
    bwdValue D c (D.crossing (c j) s) = D.alexanderGenerator (.inl (D.crossing (c k) t)) := by
  rw [bwdValue, arcValue_of_not _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃,
    reidemeisterThreePerm_symm_crossing_eq D c hst]

/-- The values `bwdValue` satisfy the relations of the new code at the three crossings of its
triangle. -/
private theorem bwdValue_downward (h : D.HasReidemeisterThreeTriangle c) (j : Fin 3) :
    bwdValue D c (D.crossing (c j) 2) =
        (D.reidemeisterThree c).alexanderWeight (c j) 0 • bwdValue D c (D.crossing (c j) 0) +
          (1 - (D.reidemeisterThree c).alexanderWeight (c j) 0) •
            bwdValue D c (D.crossing (c j) 3) ∧
      bwdValue D c (D.crossing (c j) 1) =
        (D.reidemeisterThree c).alexanderWeight (c j) 3 • bwdValue D c (D.crossing (c j) 3) +
          (1 - (D.reidemeisterThree c).alexanderWeight (c j) 3) •
            bwdValue D c (D.crossing (c j) 0) := by
  obtain ⟨k₁, k₂, k₃⟩ := bwd_braid D c h
  obtain ⟨w₀₀, w₁₀, w₂₀⟩ := alexanderWeight_reidemeisterThree_triangle D c h.arcs 0
  obtain ⟨w₀₃, w₁₃, w₂₃⟩ := alexanderWeight_reidemeisterThree_triangle D c h.arcs 3
  have v₁₂ : bwdValue D c (D.crossing (c 1) 2) = bwdMid₀ D c :=
    arcValue_of_left₁ _ _ _ _ _ _ _ _ _ _ (.inl rfl)
  have v₂₀ : bwdValue D c (D.crossing (c 2) 0) = bwdMid₀ D c :=
    arcValue_of_left₁ _ _ _ _ _ _ _ _ _ _ (.inr rfl)
  have v₀₂ : bwdValue D c (D.crossing (c 0) 2) = bwdMid₁ D c :=
    arcValue_of_left₂ _ _ _ _ _ _ _ _ _ _ (by simp) (.inl rfl)
  have v₂₃ : bwdValue D c (D.crossing (c 2) 3) = bwdMid₁ D c :=
    arcValue_of_left₂ _ _ _ _ _ _ _ _ _ _ (by simp) (.inr rfl)
  have v₀₁ : bwdValue D c (D.crossing (c 0) 1) = bwdMid₂ D c :=
    arcValue_of_left₃ _ _ _ _ _ _ _ _ _ _ (by simp) (by simp) (.inl rfl)
  have v₁₃ : bwdValue D c (D.crossing (c 1) 3) = bwdMid₂ D c :=
    arcValue_of_left₃ _ _ _ _ _ _ _ _ _ _ (by simp) (by simp) (.inr rfl)
  have v₀₀ : bwdValue D c (D.crossing (c 0) 0) = D.alexanderGenerator (.inl (D.crossing (c 0) 3)) :=
    bwdValue_boundary D c (by simp [reidemeisterThreeSlots_apply]) (by simp) (by simp) (by simp)
  have v₀₃ : bwdValue D c (D.crossing (c 0) 3) = D.alexanderGenerator (.inl (D.crossing (c 1) 3)) :=
    bwdValue_boundary D c (by simp [reidemeisterThreeSlots_apply]) (by simp) (by simp) (by simp)
  have v₁₀ : bwdValue D c (D.crossing (c 1) 0) = D.alexanderGenerator (.inl (D.crossing (c 0) 0)) :=
    bwdValue_boundary D c (by simp [reidemeisterThreeSlots_apply]) (by simp) (by simp) (by simp)
  have v₁₁ : bwdValue D c (D.crossing (c 1) 1) = D.alexanderGenerator (.inl (D.crossing (c 2) 1)) :=
    bwdValue_boundary D c (by simp [reidemeisterThreeSlots_apply]) (by simp) (by simp) (by simp)
  have v₂₂ : bwdValue D c (D.crossing (c 2) 2) = D.alexanderGenerator (.inl (D.crossing (c 1) 2)) :=
    bwdValue_boundary D c (by simp [reidemeisterThreeSlots_apply]) (by simp) (by simp) (by simp)
  have v₂₁ : bwdValue D c (D.crossing (c 2) 1) = D.alexanderGenerator (.inl (D.crossing (c 2) 2)) :=
    bwdValue_boundary D c (by simp [reidemeisterThreeSlots_apply]) (by simp) (by simp) (by simp)
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
  · exact ⟨by rw [v₀₂, v₀₀, v₀₃, w₀₀]; rfl, by rw [v₀₁, v₀₃, v₀₀, w₀₃]; rfl⟩
  · exact ⟨by rw [v₁₂, v₁₀, v₁₃, w₁₀]; rfl, by rw [v₁₁, v₁₃, v₁₀, w₁₃, k₁]⟩
  · exact ⟨by rw [v₂₂, v₂₀, v₂₃, w₂₀, k₂], by rw [v₂₁, v₂₃, v₂₀, w₂₃, k₃]⟩

/-- The map from the Alexander module of the new code to that of the old code. -/
private def bwdHom (h : D.HasReidemeisterThreeTriangle c) :
    (D.reidemeisterThree c).AlexanderModule →ₗ[ℤ[T;T⁻¹]] D.AlexanderModule :=
  (D.reidemeisterThree c).alexanderLift
    (Sum.elim (bwdValue D c) fun k ↦ D.alexanderGenerator (.inr (Fin.cast (by simp) k)))
    (fun x ↦ by simpa only [Sum.elim_inl] using bwdValue_edgePair D c h.arcs x)
    (fun i slot ↦ by
      simp only [Sum.elim_inl]
      by_cases hi : i ∈ Set.range c
      · obtain ⟨j, rfl⟩ := hi
        have := apply_crossing_add_two_of_two_of_one (D.reidemeisterThree c) (bwdValue D c) (c j)
          (by simpa only [crossing_reidemeisterThree] using (bwdValue_downward D c h j).1)
          (by simpa only [crossing_reidemeisterThree] using (bwdValue_downward D c h j).2) slot
        simpa only [crossing_reidemeisterThree] using this
      · rw [crossing_reidemeisterThree, crossing_reidemeisterThree, crossing_reidemeisterThree,
          alexanderWeight_reidemeisterThree D c h.arcs, Equiv.swap_apply_of_ne_of_ne
            (fun h ↦ hi ⟨0, h.symm⟩) (fun h ↦ hi ⟨2, h.symm⟩), bwdValue_of_notMem D c hi,
          bwdValue_of_notMem D c hi, bwdValue_of_notMem D c hi]
        exact D.alexanderGenerator_crossing_add_two i slot)

/-! #### The two maps are inverse to each other -/

private theorem fwdHom_inl (h : D.HasReidemeisterThreeTriangle c) (x : Fin (4 * n)) :
    fwdHom D c h (D.alexanderGenerator (.inl x)) = fwdValue D c x :=
  alexanderLift_alexanderGenerator _ _ _ _ _

private theorem bwdHom_inl (h : D.HasReidemeisterThreeTriangle c) (x : Fin (4 * n)) :
    bwdHom D c h ((D.reidemeisterThree c).alexanderGenerator (.inl x)) = bwdValue D c x :=
  alexanderLift_alexanderGenerator _ _ _ _ _

/-- Off the three arcs inside the old triangle, `bwdValue` undoes the move of half-edges. -/
private theorem bwdValue_reidemeisterThreePerm {x : Fin (4 * n)}
    (h₁ : ¬(x = D.crossing (c 0) 2 ∨ x = D.crossing (c 1) 0))
    (h₂ : ¬(x = D.crossing (c 0) 1 ∨ x = D.crossing (c 2) 0))
    (h₃ : ¬(x = D.crossing (c 1) 1 ∨ x = D.crossing (c 2) 3)) :
    bwdValue D c (D.reidemeisterThreePerm c x) = D.alexanderGenerator (.inl x) := by
  have e (j k : Fin 3) (s t : Fin 4) (hst : reidemeisterThreeSlots (k, t) = (j, s)) :
      D.reidemeisterThreePerm c x = D.crossing (c j) s ↔ x = D.crossing (c k) t := by
    rw [← Equiv.eq_symm_apply, reidemeisterThreePerm_symm_crossing_eq D c hst]
  rw [bwdValue, arcValue_of_not, Equiv.symm_apply_apply]
  · rwa [e 1 0 2 2 (by simp [reidemeisterThreeSlots_apply]),
      e 2 1 0 0 (by simp [reidemeisterThreeSlots_apply])]
  · rwa [e 0 0 2 1 (by simp [reidemeisterThreeSlots_apply]),
      e 2 2 3 0 (by simp [reidemeisterThreeSlots_apply])]
  · rwa [e 0 1 1 1 (by simp [reidemeisterThreeSlots_apply]),
      e 1 2 3 3 (by simp [reidemeisterThreeSlots_apply])]

/-- Off the three arcs inside the new triangle, `fwdValue` undoes the inverse move of
half-edges. -/
private theorem fwdValue_reidemeisterThreePerm_symm {y : Fin (4 * n)}
    (h₁ : ¬(y = D.crossing (c 1) 2 ∨ y = D.crossing (c 2) 0))
    (h₂ : ¬(y = D.crossing (c 0) 2 ∨ y = D.crossing (c 2) 3))
    (h₃ : ¬(y = D.crossing (c 0) 1 ∨ y = D.crossing (c 1) 3)) :
    fwdValue D c ((D.reidemeisterThreePerm c).symm y) =
      (D.reidemeisterThree c).alexanderGenerator (.inl y) := by
  have e (j k : Fin 3) (s t : Fin 4) (hst : reidemeisterThreeSlots (j, s) = (k, t)) :
      (D.reidemeisterThreePerm c).symm y = D.crossing (c j) s ↔ y = D.crossing (c k) t := by
    rw [Equiv.symm_apply_eq, reidemeisterThreePerm_crossing_eq D c hst, eq_comm]
  rw [fwdValue, arcValue_of_not, Equiv.apply_symm_apply]
  · rwa [e 0 1 2 2 (by simp [reidemeisterThreeSlots_apply]),
      e 1 2 0 0 (by simp [reidemeisterThreeSlots_apply])]
  · rwa [e 0 0 1 2 (by simp [reidemeisterThreeSlots_apply]),
      e 2 2 0 3 (by simp [reidemeisterThreeSlots_apply])]
  · rwa [e 1 0 1 1 (by simp [reidemeisterThreeSlots_apply]),
      e 2 1 3 3 (by simp [reidemeisterThreeSlots_apply])]

private theorem bwdHom_fwdValue (h : D.HasReidemeisterThreeTriangle c) (x : Fin (4 * n)) :
    bwdHom D c h (fwdValue D c x) = D.alexanderGenerator (.inl x) := by
  obtain ⟨ha, hb, hc⟩ := (hasReidemeisterThreeTriangleArcs_iff D.toPDCode c).mp h.arcs
  have b₁₀ : bwdValue D c (D.crossing (c 1) 0) = D.alexanderGenerator (.inl (D.crossing (c 0) 0)) :=
    bwdValue_boundary D c (by simp [reidemeisterThreeSlots_apply]) (by simp) (by simp) (by simp)
  have b₀₀ : bwdValue D c (D.crossing (c 0) 0) = D.alexanderGenerator (.inl (D.crossing (c 0) 3)) :=
    bwdValue_boundary D c (by simp [reidemeisterThreeSlots_apply]) (by simp) (by simp) (by simp)
  have b₀₃ : bwdValue D c (D.crossing (c 0) 3) = D.alexanderGenerator (.inl (D.crossing (c 1) 3)) :=
    bwdValue_boundary D c (by simp [reidemeisterThreeSlots_apply]) (by simp) (by simp) (by simp)
  have r0₁ := D.alexanderGenerator_crossing_add_two (c 0) 3
  have r1₁ := D.alexanderGenerator_crossing_add_two (c 1) 3
  simp only [Fin.reduceAdd] at r0₁ r1₁
  have m₀ : bwdHom D c h (fwdMid₀ D c) = D.alexanderGenerator (.inl (D.crossing (c 0) 2)) := by
    rw [fwdMid₀, map_add, map_smul, map_smul, bwdHom_inl, bwdHom_inl, b₁₀, b₀₀,
      alexanderGenerator_crossing_two]
  have m₁ : bwdHom D c h (fwdMid₁ D c) = D.alexanderGenerator (.inl (D.crossing (c 0) 1)) := by
    rw [fwdMid₁, map_add, map_smul, map_smul, bwdHom_inl, bwdHom_inl, b₁₀, b₀₀, r0₁]
  have m₂ : bwdHom D c h (fwdMid₂ D c) = D.alexanderGenerator (.inl (D.crossing (c 1) 1)) := by
    rw [fwdMid₂, map_add, map_smul, map_smul, bwdHom_inl, b₀₃, m₀, r1₁, ← ha,
      alexanderGenerator_edgePair]
  by_cases h₁ : x = D.crossing (c 0) 2 ∨ x = D.crossing (c 1) 0
  · rw [fwdValue, arcValue_of_left₁ _ _ _ _ _ _ _ _ _ _ h₁, m₀]
    rcases h₁ with rfl | rfl
    · rfl
    · rw [← ha, alexanderGenerator_edgePair]
  by_cases h₂ : x = D.crossing (c 0) 1 ∨ x = D.crossing (c 2) 0
  · rw [fwdValue, arcValue_of_left₂ _ _ _ _ _ _ _ _ _ _ h₁ h₂, m₁]
    rcases h₂ with rfl | rfl
    · rfl
    · rw [← hc, alexanderGenerator_edgePair]
  by_cases h₃ : x = D.crossing (c 1) 1 ∨ x = D.crossing (c 2) 3
  · rw [fwdValue, arcValue_of_left₃ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃, m₂]
    rcases h₃ with rfl | rfl
    · rfl
    · rw [← hb, alexanderGenerator_edgePair]
  rw [fwdValue, arcValue_of_not _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃, bwdHom_inl,
    bwdValue_reidemeisterThreePerm D c h₁ h₂ h₃]

private theorem fwdHom_bwdValue (h : D.HasReidemeisterThreeTriangle c) (y : Fin (4 * n)) :
    fwdHom D c h (bwdValue D c y) = (D.reidemeisterThree c).alexanderGenerator (.inl y) := by
  obtain ⟨h01, h12, h02⟩ := edgePair_reidemeisterThree_triangle D c h.arcs
  obtain ⟨w₀₀, w₁₀, -⟩ := alexanderWeight_reidemeisterThree_triangle D c h.arcs 0
  obtain ⟨w₀₃, -, -⟩ := alexanderWeight_reidemeisterThree_triangle D c h.arcs 3
  have f₀₀ : fwdValue D c (D.crossing (c 0) 0) =
      (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 1) 0)) :=
    fwdValue_boundary D c (by simp [reidemeisterThreeSlots_apply]) (by simp) (by simp) (by simp)
  have f₀₃ : fwdValue D c (D.crossing (c 0) 3) =
      (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 0) 0)) :=
    fwdValue_boundary D c (by simp [reidemeisterThreeSlots_apply]) (by simp) (by simp) (by simp)
  have f₁₃ : fwdValue D c (D.crossing (c 1) 3) =
      (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 0) 3)) :=
    fwdValue_boundary D c (by simp [reidemeisterThreeSlots_apply]) (by simp) (by simp) (by simp)
  have r0₂ := (D.reidemeisterThree c).alexanderGenerator_crossing_two (c 0)
  have r0₁ := (D.reidemeisterThree c).alexanderGenerator_crossing_add_two (c 0) 3
  have r1₂ := (D.reidemeisterThree c).alexanderGenerator_crossing_two (c 1)
  simp only [crossing_reidemeisterThree, w₀₀, w₁₀, w₀₃, Fin.reduceAdd] at r0₂ r0₁ r1₂
  rw [← h01, alexanderGenerator_edgePair] at r1₂
  have m₂ : fwdHom D c h (bwdMid₂ D c) =
      (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 0) 1)) := by
    rw [bwdMid₂, map_add, map_smul, map_smul, fwdHom_inl, fwdHom_inl, f₁₃, f₀₃, r0₁]
  have m₁ : fwdHom D c h (bwdMid₁ D c) =
      (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 0) 2)) := by
    rw [bwdMid₁, map_add, map_smul, map_smul, fwdHom_inl, fwdHom_inl, f₀₃, f₁₃, r0₂]
  have m₀ : fwdHom D c h (bwdMid₀ D c) =
      (D.reidemeisterThree c).alexanderGenerator (.inl (D.crossing (c 1) 2)) := by
    rw [bwdMid₀, map_add, map_smul, map_smul, m₂, fwdHom_inl, f₀₀, r1₂]
  by_cases h₁ : y = D.crossing (c 1) 2 ∨ y = D.crossing (c 2) 0
  · rw [bwdValue, arcValue_of_left₁ _ _ _ _ _ _ _ _ _ _ h₁, m₀]
    rcases h₁ with rfl | rfl
    · rfl
    · rw [← h12, alexanderGenerator_edgePair]
  by_cases h₂ : y = D.crossing (c 0) 2 ∨ y = D.crossing (c 2) 3
  · rw [bwdValue, arcValue_of_left₂ _ _ _ _ _ _ _ _ _ _ h₁ h₂, m₁]
    rcases h₂ with rfl | rfl
    · rfl
    · rw [← h02, alexanderGenerator_edgePair]
  by_cases h₃ : y = D.crossing (c 0) 1 ∨ y = D.crossing (c 1) 3
  · rw [bwdValue, arcValue_of_left₃ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃, m₂]
    rcases h₃ with rfl | rfl
    · rfl
    · rw [← h01, alexanderGenerator_edgePair]
  rw [bwdValue, arcValue_of_not _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃, fwdHom_inl,
    fwdValue_reidemeisterThreePerm_symm D c h₁ h₂ h₃]

/-- **The third Reidemeister move keeps the Alexander module**: for three crossings forming a
Reidemeister triangle, with any of the six height orders of its strands and any orientations, the
Alexander modules of the code before and after the move are linearly equivalent over
`ℤ[T;T⁻¹]`. The equivalence sends the generator of each half-edge outside the three arcs inside the
triangle to the generator of the half-edge it is moved from
(`TauCeti.OrientedPDCode.alexanderModuleReidemeisterThreeEquiv_apply_alexanderGenerator`). -/
def alexanderModuleReidemeisterThreeEquiv (h : D.HasReidemeisterThreeTriangle c) :
    (D.reidemeisterThree c).AlexanderModule ≃ₗ[ℤ[T;T⁻¹]] D.AlexanderModule :=
  LinearEquiv.ofLinearMap (bwdHom D c h) (fwdHom D c h)
    (by
      ext (x | k)
      · simp [fwdHom_inl, bwdHom_fwdValue]
      · simp [fwdHom, bwdHom])
    (by
      ext (y | k)
      · simp [bwdHom_inl, fwdHom_bwdValue]
      · simp [fwdHom, bwdHom])

/-- The equivalence sends the generator of the half-edge that a half-edge `x` is moved to, for `x`
outside the three arcs inside the old triangle, to the generator of `x`. -/
theorem alexanderModuleReidemeisterThreeEquiv_apply_alexanderGenerator
    (h : D.HasReidemeisterThreeTriangle c) {x : Fin (4 * n)}
    (h₁ : ¬(x = D.crossing (c 0) 2 ∨ x = D.crossing (c 1) 0))
    (h₂ : ¬(x = D.crossing (c 0) 1 ∨ x = D.crossing (c 2) 0))
    (h₃ : ¬(x = D.crossing (c 1) 1 ∨ x = D.crossing (c 2) 3)) :
    D.alexanderModuleReidemeisterThreeEquiv c h
        ((D.reidemeisterThree c).alexanderGenerator (.inl (D.reidemeisterThreePerm c x))) =
      D.alexanderGenerator (.inl x) :=
  (bwdHom_inl D c h _).trans (bwdValue_reidemeisterThreePerm D c h₁ h₂ h₃)

/-- The inverse equivalence sends the generator of a half-edge `x` outside the three arcs inside the
old triangle to the generator of the half-edge it is moved to. -/
theorem alexanderModuleReidemeisterThreeEquiv_symm_apply_alexanderGenerator
    (h : D.HasReidemeisterThreeTriangle c) {x : Fin (4 * n)}
    (h₁ : ¬(x = D.crossing (c 0) 2 ∨ x = D.crossing (c 1) 0))
    (h₂ : ¬(x = D.crossing (c 0) 1 ∨ x = D.crossing (c 2) 0))
    (h₃ : ¬(x = D.crossing (c 1) 1 ∨ x = D.crossing (c 2) 3)) :
    (D.alexanderModuleReidemeisterThreeEquiv c h).symm (D.alexanderGenerator (.inl x)) =
      (D.reidemeisterThree c).alexanderGenerator (.inl (D.reidemeisterThreePerm c x)) := by
  rw [LinearEquiv.symm_apply_eq,
    alexanderModuleReidemeisterThreeEquiv_apply_alexanderGenerator D c h h₁ h₂ h₃]

/-- The equivalence sends the generator of each crossing-free component to the generator of the
same component. -/
@[simp]
theorem alexanderModuleReidemeisterThreeEquiv_apply_alexanderGenerator_inr
    (h : D.HasReidemeisterThreeTriangle c)
    (k : Fin (D.reidemeisterThree c).crossinglessComponentCount) :
    D.alexanderModuleReidemeisterThreeEquiv c h
        ((D.reidemeisterThree c).alexanderGenerator (.inr k)) =
      D.alexanderGenerator (.inr (Fin.cast (by simp) k)) :=
  alexanderLift_alexanderGenerator _ _ _ _ _

/-- The inverse equivalence sends the generator of each crossing-free component to the generator of
the same component. -/
@[simp]
theorem alexanderModuleReidemeisterThreeEquiv_symm_apply_alexanderGenerator_inr
    (h : D.HasReidemeisterThreeTriangle c) (k : Fin D.crossinglessComponentCount) :
    (D.alexanderModuleReidemeisterThreeEquiv c h).symm (D.alexanderGenerator (.inr k)) =
      (D.reidemeisterThree c).alexanderGenerator (.inr (Fin.cast (by simp) k)) :=
  alexanderLift_alexanderGenerator _ _ _ _ _

/-- **The third Reidemeister move keeps the elementary ideals**, for every height order of the
three strands of its triangle. -/
@[simp]
theorem elementaryIdeal_reidemeisterThree (h : D.HasReidemeisterThreeTriangle c) (k : ℕ) :
    (D.reidemeisterThree c).elementaryIdeal k = D.elementaryIdeal k := by
  rw [elementaryIdeal_def, elementaryIdeal_def]
  exact fittingIdeal_congr (D.alexanderModuleReidemeisterThreeEquiv c h) k

end ReidemeisterThree

end OrientedPDCode

end TauCeti
