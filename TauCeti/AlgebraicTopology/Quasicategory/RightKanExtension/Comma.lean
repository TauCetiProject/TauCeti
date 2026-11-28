/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.Limit
public import TauCeti.AlgebraicTopology.Quasicategory.Slice

/-!
# The pointwise cones for right Kan extensions

For `i : A ⟶ B` and `b : B _⦋0⦌`, the comma diagram is the projection
`SSet.comma.π i b : A ×_B B_{b/} ⟶ A`. If `B` is a quasicategory this is a
left fibration, and its source is a quasicategory whenever `A` is one.

The tautological join cone is a vertex `SSet.comma.cone i b` of the slice over
the comma diagram in `B`. A strict extension `G : B ⟶ C` of `F : A ⟶ C`
transports it to `SSet.comma.pointwiseCone i b G h`, a cone in `C` on the
comma diagram followed by `F`, with apex `G b`. Its being a limit cone is the
pointwise condition for a right Kan extension. For an empty comma diagram, this
condition is exactly terminality of `G b`.

The tautological cone lives in `SimplicialSet/Comma`, and the fibration and
total-space instances live in `Quasicategory/Slice`. The cone constructions
do not require quasicategory hypotheses.

## References

* J. Lurie, *Higher Topos Theory*, §§4.3.2–4.3.3, with right Kan extensions
  obtained by the duality of Remark 4.3.2.18.
-/

public section

universe u

open CategoryTheory Limits Simplicial

namespace SSet.comma

variable {A B C D : SSet.{u}} (i : A ⟶ B) (b : B _⦋0⦌)

variable {F : A ⟶ C}

/-- The pointwise cone induced by a strict extension `G` of `F` along `i`.
Its diagram is the comma projection followed by `F`. -/
noncomputable def pointwiseCone (G : B ⟶ C) (h : i ≫ G = F) :
    (slice (π i b ≫ F)) _⦋0⦌ :=
  (slice.map (𝟙 _) G (by simp [h]) : slice (π i b ≫ i) ⟶ _).app _ (cone i b)

/-- The join map underlying the pointwise cone is the tautological cone followed by `G`. -/
@[simp]
lemma objEquiv_pointwiseCone_coe (G : B ⟶ C) (h : i ≫ G = F) :
    (slice.objEquiv (pointwiseCone i b G h)).val = coneMap i b ≫ G := by
  -- The target diagram must be explicit for rewriting through the opaque slice object.
  simpa only [pointwiseCone, join.map_id, Category.id_comp, objEquiv_cone_coe i b] using
    (slice.objEquiv_map_app_coe (q := π i b ≫ F) (𝟙 _) G (by simp [h]) (cone i b))

/-- The apex of the pointwise cone is the image of `b` under the extension. -/
-- Not `@[simp]`: `SSet.slice.π_app` rewrites the left-hand side.
lemma π_pointwiseCone (G : B ⟶ C) (h : i ≫ G = F) :
    (slice.π (π i b ≫ F)).app _ (pointwiseCone i b G h) = G.app _ b := by
  have hπ := ConcreteCategory.congr_hom
    (congr_app (slice.map_π (p := π i b ≫ i) (q := π i b ≫ F)
      (𝟙 _) G (by simp [h])) _) (cone i b)
  simpa only [pointwiseCone, comp_app, ConcreteCategory.comp_apply, π_cone] using hπ

@[simp]
lemma pointwiseCone_id : pointwiseCone i b (𝟙 B) (Category.comp_id i) = cone i b := by
  simp [pointwiseCone]

/-- Transporting a pointwise cone along `H` is the pointwise cone for `G ≫ H`. -/
@[simp]
lemma pointwiseCone_comp (G : B ⟶ C) (h : i ≫ G = F) (H : C ⟶ D) :
    (slice.map (𝟙 _) H (by simp) : slice (π i b ≫ F) ⟶ slice (π i b ≫ F ≫ H)).app _
      (pointwiseCone i b G h) = pointwiseCone i b (G ≫ H) (by simp [← h]) := by
  simp only [pointwiseCone, ← NatTrans.comp_app_apply, slice.map_comp, Category.id_comp]

/-- For an empty comma diagram, the pointwise limit condition is terminality of the
value of the extension. In particular, this applies to an empty source via `comma.π`. -/
theorem isLimit_pointwiseCone_iff_of_not_nonempty (hK : ¬ (comma i b).Nonempty)
    (G : B ⟶ C) (h : i ≫ G = F) :
    slice.IsLimit (π i b ≫ F) (pointwiseCone i b G h) ↔ C.IsTerminalVertex (G.app _ b) := by
  rw [slice.isLimit_iff_isTerminalVertex_π _ hK, π_pointwiseCone]

end SSet.comma
