/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.Limit
public import TauCeti.AlgebraicTopology.Quasicategory.Slice
public import TauCeti.AlgebraicTopology.SimplicialSet.Comma

/-!
# The pointwise cones for right Kan extensions

For `i : A ⟶ B` and `b : B _⦋0⦌`, the comma diagram is the projection
`SSet.comma.π i b : A ×_B B_{b/} ⟶ A`. If `B` is a quasicategory this is a
left fibration, and its source is a quasicategory whenever `A` is one.

The tautological join cone is a vertex `SSet.comma.cone i b` of the slice over
the comma diagram in `B`. A strict extension `G : B ⟶ C` of `F : A ⟶ C`
transports it to `SSet.comma.pointwiseCone i b G h`, a cone in `C` on the
comma diagram followed by `F`, with apex `G b`. Its being a limit cone is the
pointwise condition for a right Kan extension. For empty `A`, this condition
is exactly terminality of `G b`.

The cone constructions do not require quasicategory hypotheses; only the
fibration and total-space instances do.

## References

* J. Lurie, *Higher Topos Theory*, §§4.3.2–4.3.3, with right Kan extensions
  obtained by the duality of Remark 4.3.2.18.
-/

public section

universe u

open CategoryTheory Limits Simplicial

namespace SSet.comma

variable {A B C D : SSet.{u}} (i : A ⟶ B) (b : B _⦋0⦌)

/-- The comma projection is a left fibration when its codomain diagram lands in
a quasicategory. -/
instance leftFibration_π [Quasicategory B] : LeftFibration (π i b) :=
  LeftFibration.of_isPullback (isPullback i b).flip

/-- The comma simplicial set is a quasicategory when both `A` and `B` are. -/
instance quasicategory [Quasicategory A] [Quasicategory B] : Quasicategory (comma i b) :=
  quasicategory_of_innerFibration (π i b)

/-- The tautological cone over the comma diagram in `B`, as a vertex of its slice. -/
noncomputable def cone : (slice (π i b ≫ i)) _⦋0⦌ :=
  slice.objEquiv.symm ⟨coneMap i b, inr_coneMap i b⟩

@[simp]
lemma objEquiv_cone_coe : (slice.objEquiv (cone i b)).val = coneMap i b := by
  simp [cone]

/-- The apex of the tautological comma cone is `b`. -/
-- Not `@[simp]`: `SSet.slice.π_app` rewrites the left-hand side.
lemma π_cone : (slice.π (π i b ≫ i)).app _ (cone i b) = b := by
  rw [slice.π_app, objEquiv_cone_coe, inl_coneMap, yonedaEquiv_const]

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
  calc
    _ = join.map (𝟙 Δ[0]) (𝟙 (comma i b)) ≫ (slice.objEquiv (cone i b)).val ≫ G :=
      slice.objEquiv_map_app_coe (q := π i b ≫ F) (𝟙 _) G (by simp [h]) (cone i b)
    _ = (slice.objEquiv (cone i b)).val ≫ G := by simp
    _ = _ := congrArg (· ≫ G) (objEquiv_cone_coe i b)

/-- The apex of the pointwise cone is the image of `b` under the extension. -/
-- Not `@[simp]`: `SSet.slice.π_app` rewrites the left-hand side.
lemma π_pointwiseCone (G : B ⟶ C) (h : i ≫ G = F) :
    (slice.π (π i b ≫ F)).app _ (pointwiseCone i b G h) = G.app _ b := by
  rw [slice.π_app, objEquiv_pointwiseCone_coe, inl_coneMap_assoc,
    yonedaEquiv_comp, yonedaEquiv_const]

@[simp]
lemma pointwiseCone_id : pointwiseCone i b (𝟙 B) (Category.comp_id i) = cone i b := by
  apply slice.objEquiv.injective
  apply Subtype.ext
  exact (objEquiv_pointwiseCone_coe i b (𝟙 B) (Category.comp_id i)).trans
    ((Category.comp_id _).trans (objEquiv_cone_coe i b).symm)

/-- Transporting a pointwise cone along `H` is the pointwise cone for `G ≫ H`. -/
@[simp]
lemma pointwiseCone_comp (G : B ⟶ C) (h : i ≫ G = F) (H : C ⟶ D) :
    (slice.map (𝟙 _) H (by simp) : slice (π i b ≫ F) ⟶ slice (π i b ≫ F ≫ H)).app _
      (pointwiseCone i b G h) = pointwiseCone i b (G ≫ H) (by simp [← h]) := by
  apply slice.objEquiv.injective
  apply Subtype.ext
  calc
    _ = join.map (𝟙 Δ[0]) (𝟙 (comma i b)) ≫
        (slice.objEquiv (pointwiseCone i b G h)).val ≫ H :=
      slice.objEquiv_map_app_coe (q := π i b ≫ F ≫ H) (𝟙 _) H
        (by simp) (pointwiseCone i b G h)
    _ = (slice.objEquiv (pointwiseCone i b G h)).val ≫ H := by simp
    _ = (coneMap i b ≫ G) ≫ H := congrArg (· ≫ H) (objEquiv_pointwiseCone_coe i b G h)
    _ = coneMap i b ≫ G ≫ H := Category.assoc _ _ _
    _ = _ := (objEquiv_pointwiseCone_coe i b (G ≫ H) _).symm

/-- For an empty source, the pointwise limit condition is terminality of the value
of the extension. -/
theorem isLimit_pointwiseCone_iff_of_not_nonempty (hA : ¬ A.Nonempty)
    (G : B ⟶ C) (h : i ≫ G = F) :
    slice.IsLimit (π i b ≫ F) (pointwiseCone i b G h) ↔ C.IsTerminalVertex (G.app _ b) := by
  have hK : ¬ (comma i b).Nonempty := fun hK ↦ hA (nonempty_of_hom (π i b))
  rw [slice.isLimit_iff_isTerminalVertex_π _ hK, π_pointwiseCone]

end SSet.comma
