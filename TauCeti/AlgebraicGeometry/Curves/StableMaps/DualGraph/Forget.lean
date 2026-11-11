/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Forget
public import TauCeti.AlgebraicGeometry.Curves.StableMaps.DualGraph.Contraction

/-!
# Forgetting one marking of a stable degree-decorated graph

After forgetting one marking of a stable map, the bundle
`ω(Σ retained markings) ⊗ F^*(L^⊗3)` has nonnegative degree on every component. Only the
component carrying the forgotten marking can have degree zero. Such a component has map degree
zero; in the numerical stable range it is a rational tail with one retained marking or an
unmarked rational bridge. Contracting it preserves the weighted degrees of all other components
and makes the decorated graph stable. Thus stabilization takes at most one step, even when the
pointed source graph is not stable.

This file proves these numerical assertions for dual graphs. It does not construct the
contraction of a curve or the line bundle on its target.

## Main results

* `TauCeti.DualGraph.DegreeDecoration.weightedLogCanonicalDegree_forgetMarking`:
  forgetting one marking decreases the weighted degree by one precisely at its vertex.
* `isRationalTail_or_isRationalBridge_of_weightedLogCanonicalDegree_eq_zero`, in the namespace
  `TauCeti.DualGraph.DegreeDecoration` (from `Basic`): classification of the component to be
  contracted, applied to the decoration after forgetting.
* `IsStable.exists_reflGen_stabilizationStep_forgetMarking_isStable`, in the namespace
  `TauCeti.DualGraph.DegreeDecoration`: at most one map-aware stabilization step is needed.

## References

* K. Behrend and Yu. Manin, *Stacks of stable maps and Gromov--Witten invariants*,
  Duke Math. J. 85 (1996), 1--60, Proposition 3.10 and Lemmas 3.11--3.12.
-/

public section

namespace TauCeti.DualGraph.DegreeDecoration

open Finset

universe u v

variable {ι : Type v} {G : DualGraph.{u} (Option ι)} (D : G.DegreeDecoration)

/-- Forget the marking `none`, retaining the degree on every vertex. -/
def forgetMarking : (G.reindex some).DegreeDecoration :=
  ⟨D.componentDegree⟩

@[simp]
lemma componentDegree_forgetMarking (x : G.Vertex) :
    D.forgetMarking.componentDegree x = D.componentDegree x :=
  (rfl)

/-- Forgetting a marking does not change the total map degree. -/
@[simp]
theorem totalDegree_forgetMarking : D.forgetMarking.totalDegree = D.totalDegree := by
  simp only [totalDegree_def, componentDegree_forgetMarking]

@[simp]
lemma forgetMarking_zero : (0 : G.DegreeDecoration).forgetMarking = 0 :=
  DegreeDecoration.ext rfl

@[simp]
lemma forgetMarking_add (E : G.DegreeDecoration) :
    (D + E).forgetMarking = D.forgetMarking + E.forgetMarking :=
  DegreeDecoration.ext rfl

@[simp]
lemma forgetMarking_smul (m : ℕ) : (m • D).forgetMarking = m • D.forgetMarking :=
  DegreeDecoration.ext rfl

/-- Forgetting a marking is injective on degree decorations. -/
@[simp]
theorem forgetMarking_inj {E : G.DegreeDecoration} :
    D.forgetMarking = E.forgetMarking ↔ D = E := by
  simp only [DegreeDecoration.ext_iff, funext_iff, componentDegree_forgetMarking]

variable (G) in
/-- Forgetting a marking identifies degree decorations additively, since vertices do not change. -/
def forgetMarkingAddEquiv : G.DegreeDecoration ≃+ (G.reindex some).DegreeDecoration where
  toFun D := D.forgetMarking
  invFun D := ⟨D.componentDegree⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' := forgetMarking_add

@[simp]
lemma forgetMarkingAddEquiv_apply : forgetMarkingAddEquiv G D = D.forgetMarking :=
  (rfl)

@[simp]
lemma componentDegree_forgetMarkingAddEquiv_symm_apply (E : (G.reindex some).DegreeDecoration)
    (x : G.Vertex) :
    ((forgetMarkingAddEquiv G).symm E).componentDegree x = E.componentDegree x :=
  (rfl)

variable [Fintype ι]

/-- Forgetting `none` decreases the weighted degree by one at its vertex and leaves it unchanged
elsewhere. -/
@[simp]
theorem weightedLogCanonicalDegree_forgetMarking (x : G.Vertex) :
    D.forgetMarking.weightedLogCanonicalDegree x =
      D.weightedLogCanonicalDegree x - if G.marking none = x then 1 else 0 := by
  rw [weightedLogCanonicalDegree_def, weightedLogCanonicalDegree_def,
    logCanonicalDegree_reindex_some, componentDegree_forgetMarking]
  exact sub_add_eq_add_sub _ _ _

variable {D}

/-- The weighted log-canonical bundle remains numerically nef after forgetting one marking. -/
theorem IsStable.weightedLogCanonicalDegree_forgetMarking_nonneg (hD : D.IsStable)
    (x : G.Vertex) : 0 ≤ D.forgetMarking.weightedLogCanonicalDegree x := by
  have hpos := D.isStable_iff_weightedLogCanonicalDegree_pos.mp hD x
  rw [weightedLogCanonicalDegree_forgetMarking]
  split_ifs <;> omega

/-- A vertex has weighted degree zero after forgetting precisely when it carries the forgotten
marking and had weighted degree one. -/
theorem IsStable.weightedLogCanonicalDegree_forgetMarking_eq_zero_iff (hD : D.IsStable)
    {x : G.Vertex} :
    D.forgetMarking.weightedLogCanonicalDegree x = 0 ↔
      G.marking none = x ∧ D.weightedLogCanonicalDegree x = 1 := by
  have hpos := D.isStable_iff_weightedLogCanonicalDegree_pos.mp hD x
  rw [weightedLogCanonicalDegree_forgetMarking]
  by_cases h : G.marking none = x
  · rw [ite_eq_left h, and_iff_right h]
    omega
  · rw [ite_eq_right h]
    exact iff_of_false (by omega) (fun hx ↦ h hx.1)

/-- Forgetting preserves stability exactly when the original weighted degree at the forgotten
marking is at least two. -/
theorem IsStable.isStable_forgetMarking_iff (hD : D.IsStable) :
    D.forgetMarking.IsStable ↔ 1 < D.weightedLogCanonicalDegree (G.marking none) := by
  rw [isStable_iff_weightedLogCanonicalDegree_pos]
  constructor
  · intro h
    have hx := h (G.marking none)
    simpa only [weightedLogCanonicalDegree_forgetMarking, ite_true,
      sub_pos, eq_self] using hx
  · intro h x
    have hpos := D.isStable_iff_weightedLogCanonicalDegree_pos.mp hD x
    rw [weightedLogCanonicalDegree_forgetMarking]
    by_cases hx : G.marking none = x
    · rw [← hx]
      simpa only [ite_true, eq_self, sub_pos] using h
    · simpa only [ite_eq_right hx, sub_zero] using hpos

/-- At most one component has weighted degree zero after forgetting a marking of a stable map. -/
theorem IsStable.subsingleton_weightedLogCanonicalDegree_forgetMarking_eq_zero
    (hD : D.IsStable) :
    {x : G.Vertex | D.forgetMarking.weightedLogCanonicalDegree x = 0}.Subsingleton :=
  fun _ hx _ hy ↦
    (hD.weightedLogCanonicalDegree_forgetMarking_eq_zero_iff.mp hx).1.symm.trans
      (hD.weightedLogCanonicalDegree_forgetMarking_eq_zero_iff.mp hy).1

/-- If a vertex `x` has nonpositive weighted degree after forgetting a marking of a stable map,
every vertex `y ≠ x` has positive weighted degree. -/
theorem IsStable.weightedLogCanonicalDegree_forgetMarking_pos_of_ne (hD : D.IsStable)
    {x y : G.Vertex} (hx : D.forgetMarking.weightedLogCanonicalDegree x ≤ 0) (hy : y ≠ x) :
    0 < D.forgetMarking.weightedLogCanonicalDegree y := by
  have hx₀ := le_antisymm hx (hD.weightedLogCanonicalDegree_forgetMarking_nonneg x)
  have hmx := (hD.weightedLogCanonicalDegree_forgetMarking_eq_zero_iff.mp hx₀).1
  have hpos := D.isStable_iff_weightedLogCanonicalDegree_pos.mp hD y
  rw [weightedLogCanonicalDegree_forgetMarking, ite_eq_right (hmx.trans_ne hy.symm)]
  omega

/-- Any stabilization step after forgetting one marking of a stable map gives a stable decorated
graph. -/
theorem IsStable.isStable_of_stabilizationStep_forgetMarking (hD : D.IsStable)
    {y : Σ H : DualGraph.{u} ι, H.DegreeDecoration}
    (h : StabilizationStep ⟨G.reindex some, D.forgetMarking⟩ y) : y.2.IsStable := by
  cases h with
  | @contractTail _ _ x hx hm hd =>
    have htail := hx.logCanonicalDegree_eq
    have hnef := hD.weightedLogCanonicalDegree_forgetMarking_nonneg x
    have hweight : D.forgetMarking.weightedLogCanonicalDegree x =
        -1 + (G.reindex some).numMarkings x := by
      rw [weightedLogCanonicalDegree_eq_of_componentDegree_eq_zero _ hd, htail]
    have hm₁ : (G.reindex some).numMarkings x = 1 := by omega
    refine (isStable_iff_weightedLogCanonicalDegree_pos _).mpr fun ⟨z, hz⟩ ↦ ?_
    rw [weightedLogCanonicalDegree_contractTail]
    have hpos := hD.weightedLogCanonicalDegree_forgetMarking_pos_of_ne (by omega) hz
    simpa only [hm₁, Nat.cast_one, sub_self, ite_self, add_zero] using hpos
  | @contractBridge _ _ x hx hm hd =>
    have hbridge := hx.logCanonicalDegree_eq
    have hm₀ := (G.reindex some).numMarkings_eq_zero_iff.mpr hm
    have hweight : D.forgetMarking.weightedLogCanonicalDegree x = 0 := by
      simp [weightedLogCanonicalDegree_eq_of_componentDegree_eq_zero _ hd, hbridge, hm₀]
    refine (isStable_iff_weightedLogCanonicalDegree_pos _).mpr fun ⟨z, hz⟩ ↦ ?_
    rw [weightedLogCanonicalDegree_contractBridge]
    exact hD.weightedLogCanonicalDegree_forgetMarking_pos_of_ne hweight.le hz

/-- **Forgetting one marking requires at most one contraction.** In the numerical stable range,
the resulting graph is stable or becomes stable after one degree-zero tail or bridge contraction.
The step preserves the arithmetic genus and total degree by the stabilization-step API. -/
theorem IsStable.exists_reflGen_stabilizationStep_forgetMarking_isStable (hD : D.IsStable)
    (hrange : 0 < 2 * (G.arithmeticGenus : ℤ) - 2 + Fintype.card ι + 3 * D.totalDegree) :
    ∃ y, Relation.ReflGen StabilizationStep ⟨G.reindex some, D.forgetMarking⟩ y ∧
      y.2.IsStable := by
  by_cases hs : D.forgetMarking.IsStable
  · exact ⟨_, .refl, hs⟩
  · obtain ⟨y, hy⟩ := D.forgetMarking.exists_stabilizationStep_of_not_isStable
      (by simpa only [arithmeticGenus_reindex, totalDegree_forgetMarking] using hrange) hs
    exact ⟨y, .single hy, hD.isStable_of_stabilizationStep_forgetMarking hy⟩

end TauCeti.DualGraph.DegreeDecoration
