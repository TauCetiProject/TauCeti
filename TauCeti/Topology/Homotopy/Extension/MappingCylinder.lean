/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Basic
public import TauCeti.Topology.Homotopy.MappingCylinder

/-!
# The source of a map is a cofibration in its mapping cylinder

The bottom face of the mapping cylinder of `f : C(X, Y)` has the homotopy extension property
inside the mapping cylinder, so `TauCeti.MappingCylinder.incl` is a closed cofibration.  Together
with `TauCeti.MappingCylinder.proj_comp_incl` and
`TauCeti.MappingCylinder.homotopyEquiv` this factors an arbitrary continuous map as a closed
cofibration followed by a homotopy equivalence.

The retraction proving the property is assembled from a single retraction of the square
`I × I`, in which the first coordinate is the height in the cylinder and the second is the time
of the homotopy: the square is projected from the point `(1, 2)` onto the union of the side
`{0} × I` with the bottom `I × {0}`.  Projecting from a point on the line of height `1` is what
makes the retraction compatible with the gluing, since it keeps the whole top face at height `1`
and merely resets its time to `0`, which is how the base of the mapping cylinder must move.  It
is this last property that an abstract retraction, such as the one behind
`TauCeti.hasHomotopyExtensionProperty_sphere_closedBall`, does not supply, so the square
retraction is written out.

## Main results

* `TauCeti.MappingCylinder.hasHomotopyExtensionProperty_range_incl`: **the source of `f` is a
  closed cofibration in the mapping cylinder of `f`.**

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, the section "The Homotopy Extension Property", where the mapping cylinder is used
  to replace a map by a cofibration.
* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I.
-/

public section

noncomputable section

namespace TauCeti

open Set unitInterval

universe u v

variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y] {f : C(X, Y)}

namespace MappingCylinder

/-- The height coordinate of the retraction of the square onto the union of the side of height
`0` and the bottom face of time `0`, by projection from the point of height `1` and time `2`.
The first coordinate of the argument is the height, the second is the time. -/
private def squareFst : I × I → ℝ := fun p =>
  if (p.2 : ℝ) ≤ 2 * (p.1 : ℝ) then (2 * (p.1 : ℝ) - p.2) / (2 - (p.2 : ℝ)) else 0

/-- The time coordinate of the retraction described at `TauCeti.MappingCylinder.squareFst`.  The
denominator is `1 - p.1` wherever this branch is used, and is truncated below at `1 / 2` only so
that the formula is continuous on the whole square. -/
private def squareSnd : I × I → ℝ := fun p =>
  if (p.2 : ℝ) ≤ 2 * (p.1 : ℝ) then 0
  else ((p.2 : ℝ) - 2 * (p.1 : ℝ)) / max (1 - (p.1 : ℝ)) (1 / 2)

private lemma squareFst_def (p : I × I) :
    squareFst p =
      if (p.2 : ℝ) ≤ 2 * (p.1 : ℝ) then (2 * (p.1 : ℝ) - p.2) / (2 - (p.2 : ℝ)) else 0 := (rfl)

private lemma squareSnd_def (p : I × I) :
    squareSnd p =
      if (p.2 : ℝ) ≤ 2 * (p.1 : ℝ) then 0
      else ((p.2 : ℝ) - 2 * (p.1 : ℝ)) / max (1 - (p.1 : ℝ)) (1 / 2) := (rfl)

private lemma squareFst_mem (p : I × I) : squareFst p ∈ I := by
  have h2 : (p.1 : ℝ) ≤ 1 := p.1.2.2
  have _ : (0 : ℝ) ≤ (p.2 : ℝ) := p.2.2.1
  have h4 : (p.2 : ℝ) ≤ 1 := p.2.2.2
  have hd : (0 : ℝ) < 2 - (p.2 : ℝ) := by linarith
  rw [squareFst_def]
  split_ifs with h
  · exact ⟨div_nonneg (by linarith) hd.le, (div_le_one hd).2 (by linarith)⟩
  · exact ⟨le_rfl, zero_le_one⟩

private lemma squareSnd_mem (p : I × I) : squareSnd p ∈ I := by
  have h1 : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.2.1
  have h4 : (p.2 : ℝ) ≤ 1 := p.2.2.2
  rw [squareSnd_def]
  split_ifs with h
  · exact ⟨le_rfl, zero_le_one⟩
  · have _ : 2 * (p.1 : ℝ) < (p.2 : ℝ) := not_le.1 h
    rw [max_eq_left (by linarith : (1 : ℝ) / 2 ≤ 1 - (p.1 : ℝ))]
    exact ⟨div_nonneg (by linarith) (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩

private lemma continuous_squareFst : Continuous fun p : I × I => squareFst p := by
  have hd : Continuous fun p : I × I => (2 * (p.1 : ℝ) - p.2) / (2 - (p.2 : ℝ)) := by
    refine Continuous.div (by fun_prop) (by fun_prop) fun p => ?_
    have : (p.2 : ℝ) ≤ 1 := p.2.2.2
    linarith
  simp only [squareFst_def]
  exact hd.if_le continuous_const (by fun_prop) (by fun_prop) fun p hp => by
    rw [← hp, sub_self, zero_div]

private lemma continuous_squareSnd : Continuous fun p : I × I => squareSnd p := by
  have hd : Continuous fun p : I × I =>
      ((p.2 : ℝ) - 2 * (p.1 : ℝ)) / max (1 - (p.1 : ℝ)) (1 / 2) := by
    refine Continuous.div (by fun_prop) (by fun_prop) fun p => ?_
    have : (1 : ℝ) / 2 ≤ max (1 - (p.1 : ℝ)) (1 / 2) := le_max_right _ _
    linarith
  simp only [squareSnd_def]
  exact continuous_const.if_le hd (by fun_prop) (by fun_prop) fun p hp => by
    rw [← hp, sub_self, zero_div]

/-- The retraction of the square `I × I` onto the union of the side of height `0` with the
bottom face of time `0`, by projection from the point of height `1` and time `2`. -/
private def squareRetract (p : I × I) : I × I :=
  (⟨squareFst p, squareFst_mem p⟩, ⟨squareSnd p, squareSnd_mem p⟩)

private lemma squareRetract_fst (p : I × I) : ((squareRetract p).1 : ℝ) = squareFst p := (rfl)

private lemma squareRetract_snd (p : I × I) : ((squareRetract p).2 : ℝ) = squareSnd p := (rfl)

private lemma continuous_squareRetract : Continuous squareRetract :=
  (continuous_squareFst.subtype_mk _).prodMk (continuous_squareSnd.subtype_mk _)

/-- The retracted point lies on the side of height `0` or on the bottom face of time `0`. -/
private lemma squareRetract_mem (p : I × I) :
    (squareRetract p).2 = 0 ∨ (squareRetract p).1 = 0 := by
  by_cases h : (p.2 : ℝ) ≤ 2 * (p.1 : ℝ)
  · refine Or.inl (Subtype.ext ?_)
    rw [squareRetract_snd, squareSnd_def, ite_eq_left h, Set.Icc.coe_zero]
  · refine Or.inr (Subtype.ext ?_)
    rw [squareRetract_fst, squareFst_def, ite_eq_right h, Set.Icc.coe_zero]

/-- The projection point lies on the line of height `1`, so the whole top face keeps its height
and only has its time reset to `0`. -/
private lemma squareRetract_top (t : I) : squareRetract (1, t) = (1, 0) := by
  have h4 : (t : ℝ) ≤ 1 := t.2.2
  have hle : ((((1 : I), t) : I × I).2 : ℝ) ≤ 2 * ((((1 : I), t) : I × I).1 : ℝ) := by
    simp only [Set.Icc.coe_one]
    linarith
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · rw [squareRetract_fst, squareFst_def, ite_eq_left hle, Set.Icc.coe_one, mul_one]
    exact div_self (by linarith)
  · rw [squareRetract_snd, squareSnd_def, ite_eq_left hle, Set.Icc.coe_zero]

private lemma squareRetract_time_zero (s : I) : squareRetract (s, 0) = (s, 0) := by
  have h1 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
  have hle : (((s, (0 : I)) : I × I).2 : ℝ) ≤ 2 * (((s, (0 : I)) : I × I).1 : ℝ) := by
    simp only [Set.Icc.coe_zero]
    linarith
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · rw [squareRetract_fst, squareFst_def, ite_eq_left hle]
    simp only [Set.Icc.coe_zero, sub_zero]
    ring
  · rw [squareRetract_snd, squareSnd_def, ite_eq_left hle, Set.Icc.coe_zero]

private lemma squareRetract_height_zero (t : I) : squareRetract (0, t) = (0, t) := by
  have h3 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · simp only [squareRetract_fst, squareFst_def, Set.Icc.coe_zero, mul_zero]
    split_ifs with h
    · rw [le_antisymm h h3]
      norm_num
    · rfl
  · simp only [squareRetract_snd, squareSnd_def, Set.Icc.coe_zero, mul_zero]
    split_ifs with h
    · exact (le_antisymm h h3).symm
    · rw [sub_zero, sub_zero, max_eq_left (by norm_num : (1 : ℝ) / 2 ≤ 1), div_one]

/-- The retraction of the cylinder over the mapping cylinder at time `t`: a point of the
cylinder of `f` moves inside its own vertical square, while the base only has its time reset. -/
private def retractMap (f : C(X, Y)) (t : I) :
    C(MappingCylinder f, I × MappingCylinder f) :=
  lift ⟨fun q => ((squareRetract (q.1, t)).2, mkCyl f ((squareRetract (q.1, t)).1, q.2)),
      by
        have h : Continuous fun q : I × X => squareRetract (q.1, t) :=
          continuous_squareRetract.comp (continuous_fst.prodMk continuous_const)
        exact h.snd.prodMk ((mkCyl f).continuous.comp (h.fst.prodMk continuous_snd))⟩
    ⟨fun y => (0, mkBase f y), by fun_prop⟩ fun x => by
      simp [squareRetract_top]

private lemma retractMap_mkCyl (t : I) (q : I × X) :
    retractMap f t (mkCyl f q) =
      ((squareRetract (q.1, t)).2, mkCyl f ((squareRetract (q.1, t)).1, q.2)) :=
  lift_mkCyl _ q

private lemma retractMap_mkBase (t : I) (y : Y) :
    retractMap f t (mkBase f y) = (0, mkBase f y) :=
  lift_mkBase _ y

private lemma continuous_retractMap :
    Continuous fun p : I × MappingCylinder f => retractMap f p.1 p.2 := by
  rw [continuous_prod_iff]
  refine ⟨?_, ?_⟩
  · simp only [retractMap_mkCyl]
    have h : Continuous fun q : I × (I × X) => squareRetract (q.2.1, q.1) :=
      continuous_squareRetract.comp ((continuous_fst.comp continuous_snd).prodMk continuous_fst)
    exact h.snd.prodMk ((mkCyl f).continuous.comp
      (h.fst.prodMk (continuous_snd.comp continuous_snd)))
  · simp only [retractMap_mkBase]
    exact continuous_const.prodMk ((mkBase f).continuous.comp continuous_snd)

/-- **The source of `f` is a closed cofibration in the mapping cylinder of `f`**: the bottom face
of the cylinder has the homotopy extension property inside the mapping cylinder. -/
theorem hasHomotopyExtensionProperty_range_incl :
    HasHomotopyExtensionProperty (Set.range (incl f)) := by
  refine hasHomotopyExtensionProperty_of_retraction isClosed_range_incl
    (r := ⟨fun p => retractMap f p.1 p.2, continuous_retractMap⟩) (fun p => ?_) fun p hp => ?_
  · obtain ⟨t, m⟩ := p
    simp only [ContinuousMap.coe_mk, mem_cylinderExtensionDomain_iff]
    induction m using ind with
    | cyl q =>
      rw [retractMap_mkCyl]
      exact (squareRetract_mem (q.1, t)).imp id fun h => mkCyl_mem_range_incl_iff.2 h
    | base y => exact Or.inl (by rw [retractMap_mkBase])
  · obtain ⟨t, m⟩ := p
    simp only [ContinuousMap.coe_mk]
    obtain h0 | hm := mem_cylinderExtensionDomain_iff.1 hp
    · obtain rfl : t = 0 := h0
      induction m using ind with
      | cyl q => simp [retractMap_mkCyl, squareRetract_time_zero]
      | base y => rw [retractMap_mkBase]
    · obtain ⟨x, rfl⟩ : ∃ x, incl f x = m := hm
      simp [retractMap_mkCyl, squareRetract_height_zero]

end MappingCylinder

end TauCeti
