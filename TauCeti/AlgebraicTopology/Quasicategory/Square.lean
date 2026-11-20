/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.Limit
public import TauCeti.AlgebraicTopology.SimplicialSet.Join.Square

/-!
# Pullback and pushout squares

A *square* in a simplicial set `C` is a map `σ : Δ[1] ⊗ Δ[1] ⟶ C`. Through the isomorphisms
`Δ[0] ⋆ Λ[2, 2] ≅ Δ[1] ⊗ Δ[1]` (`SSet.join.coneHornIso`) and `Λ[2, 0] ⋆ Δ[0] ≅ Δ[1] ⊗ Δ[1]`
(`SSet.join.hornConeIso`), a square is a cone over its cospan `(1, 0) ⟶ (1, 1) ⟵ (0, 1)`
(`SSet.squareCospan`, `SSet.squareCone`) and a cocone under its span
`(1, 0) ⟵ (0, 0) ⟶ (0, 1)` (`SSet.squareSpan`, `SSet.squareCocone`). It is a *pullback square*
(`SSet.IsPullbackSquare`) if this cone is a limit cone, and a *pushout square*
(`SSet.IsPushoutSquare`) if this cocone is a colimit cocone. Both isomorphisms send the vertices
of the horns to the same vertices of the square, so that the cone point `(0, 0)` of the cone is the
initial vertex of the span, and the cone point `(1, 1)` of the cocone is the final vertex of the
cospan.

## Main results

* `SSet.isPullbackSquare_iff_isLimit`, `SSet.isPushoutSquare_iff_isColimit`: a square is a pullback
  (pushout) square exactly when the corresponding cone (cocone) is a limit (colimit), for any
  presentation of its cospan (span).
* `SSet.exists_isPullbackSquare_of_isLimit`, `SSet.exists_isPushoutSquare_of_isColimit`: every
  limit cone over a cospan is a pullback square, and every colimit cocone under a span is a pushout
  square.

## References

* J. Lurie, *Higher Topos Theory*, §4.4.2 (pullback and pushout squares as limits of cospans and
  colimits of spans).
-/

public section

universe u

open CategoryTheory MonoidalCategory Simplicial

namespace SSet

variable {C : SSet.{u}}

/-- The cospan `(1, 0) ⟶ (1, 1) ⟵ (0, 1)` of a square `σ : Δ[1] ⊗ Δ[1] ⟶ C`: the restriction of `σ`
to the horn `Λ[2, 2]` through `Δ[0] ⋆ Λ[2, 2] ≅ Δ[1] ⊗ Δ[1]`. -/
noncomputable def squareCospan (σ : Δ[1] ⊗ Δ[1] ⟶ C) : (Λ[2, 2] : SSet.{u}) ⟶ C :=
  join.inr _ _ ≫ join.coneHornIso.hom ≫ σ

lemma squareCospan_def (σ : Δ[1] ⊗ Δ[1] ⟶ C) :
    squareCospan σ = join.inr _ _ ≫ join.coneHornIso.hom ≫ σ :=
  (rfl)

/-- A square `σ : Δ[1] ⊗ Δ[1] ⟶ C` as a cone over its cospan, with cone point `(0, 0)`. -/
noncomputable def squareCone (σ : Δ[1] ⊗ Δ[1] ⟶ C) : (slice (squareCospan σ)) _⦋0⦌ :=
  slice.objEquiv.symm ⟨join.coneHornIso.hom ≫ σ, rfl⟩

@[simp]
lemma objEquiv_squareCone_coe (σ : Δ[1] ⊗ Δ[1] ⟶ C) :
    (slice.objEquiv (squareCone σ)).1 = join.coneHornIso.hom ≫ σ := by
  rw [squareCone, Equiv.apply_symm_apply]

/-- The span `(1, 0) ⟵ (0, 0) ⟶ (0, 1)` of a square `σ : Δ[1] ⊗ Δ[1] ⟶ C`: the restriction of `σ`
to the horn `Λ[2, 0]` through `Λ[2, 0] ⋆ Δ[0] ≅ Δ[1] ⊗ Δ[1]`. -/
noncomputable def squareSpan (σ : Δ[1] ⊗ Δ[1] ⟶ C) : (Λ[2, 0] : SSet.{u}) ⟶ C :=
  join.inl _ _ ≫ join.hornConeIso.hom ≫ σ

lemma squareSpan_def (σ : Δ[1] ⊗ Δ[1] ⟶ C) :
    squareSpan σ = join.inl _ _ ≫ join.hornConeIso.hom ≫ σ :=
  (rfl)

/-- A square `σ : Δ[1] ⊗ Δ[1] ⟶ C` as a cocone under its span, with cone point `(1, 1)`. -/
noncomputable def squareCocone (σ : Δ[1] ⊗ Δ[1] ⟶ C) : (coslice (squareSpan σ)) _⦋0⦌ :=
  coslice.objEquiv.symm ⟨join.hornConeIso.hom ≫ σ, rfl⟩

@[simp]
lemma objEquiv_squareCocone_coe (σ : Δ[1] ⊗ Δ[1] ⟶ C) :
    (coslice.objEquiv (squareCocone σ)).1 = join.hornConeIso.hom ≫ σ := by
  rw [squareCocone, Equiv.apply_symm_apply]

/-- A square `σ : Δ[1] ⊗ Δ[1] ⟶ C` is a *pullback square* if, as a cone over its cospan
`(1, 0) ⟶ (1, 1) ⟵ (0, 1)`, it is a limit cone. -/
def IsPullbackSquare (σ : Δ[1] ⊗ Δ[1] ⟶ C) : Prop :=
  slice.IsLimit (squareCospan σ) (squareCone σ)

lemma isPullbackSquare_iff (σ : Δ[1] ⊗ Δ[1] ⟶ C) :
    IsPullbackSquare σ ↔ slice.IsLimit (squareCospan σ) (squareCone σ) :=
  Iff.rfl

/-- A square `σ : Δ[1] ⊗ Δ[1] ⟶ C` is a *pushout square* if, as a cocone under its span
`(1, 0) ⟵ (0, 0) ⟶ (0, 1)`, it is a colimit cocone. -/
def IsPushoutSquare (σ : Δ[1] ⊗ Δ[1] ⟶ C) : Prop :=
  coslice.IsColimit (squareSpan σ) (squareCocone σ)

lemma isPushoutSquare_iff (σ : Δ[1] ⊗ Δ[1] ⟶ C) :
    IsPushoutSquare σ ↔ coslice.IsColimit (squareSpan σ) (squareCocone σ) :=
  Iff.rfl

/-- A square `σ` is a pullback square exactly when the cone `Δ[0] ⋆ Λ[2, 2] ⟶ C` it defines is a
limit cone over `q`, for any diagram `q` equal to the cospan of `σ`. -/
lemma isPullbackSquare_iff_isLimit {σ : Δ[1] ⊗ Δ[1] ⟶ C} {q : (Λ[2, 2] : SSet.{u}) ⟶ C}
    (h : squareCospan σ = q) :
    IsPullbackSquare σ ↔ slice.IsLimit q
      (slice.objEquiv.symm ⟨join.coneHornIso.hom ≫ σ, (squareCospan_def σ).symm.trans h⟩) := by
  subst h
  rfl

/-- A square `σ` is a pushout square exactly when the cocone `Λ[2, 0] ⋆ Δ[0] ⟶ C` it defines is a
colimit cocone under `q`, for any diagram `q` equal to the span of `σ`. -/
lemma isPushoutSquare_iff_isColimit {σ : Δ[1] ⊗ Δ[1] ⟶ C} {q : (Λ[2, 0] : SSet.{u}) ⟶ C}
    (h : squareSpan σ = q) :
    IsPushoutSquare σ ↔
      coslice.IsColimit q
        (coslice.objEquiv.symm ⟨join.hornConeIso.hom ≫ σ, (squareSpan_def σ).symm.trans h⟩) := by
  subst h
  rfl

/-- Every limit cone over a cospan `q : Λ[2, 2] ⟶ C` is a pullback square with cospan `q`. -/
lemma exists_isPullbackSquare_of_isLimit {q : (Λ[2, 2] : SSet.{u}) ⟶ C} {c : (slice q) _⦋0⦌}
    (hc : slice.IsLimit q c) : ∃ σ : Δ[1] ⊗ Δ[1] ⟶ C, squareCospan σ = q ∧ IsPullbackSquare σ := by
  have h : squareCospan (join.coneHornIso.inv ≫ (slice.objEquiv c).1) = q := by
    rw [squareCospan_def, Iso.hom_inv_id_assoc, (slice.objEquiv c).2]
  -- The cone defined by this square is `c` itself.
  have hc' : slice.objEquiv.symm ⟨_, (squareCospan_def _).symm.trans h⟩ = c :=
    (Equiv.symm_apply_eq _).2 (Subtype.ext (Iso.hom_inv_id_assoc _ _))
  exact ⟨_, h, (isPullbackSquare_iff_isLimit h).2 (by rw [hc']; exact hc)⟩

/-- Every colimit cocone under a span `q : Λ[2, 0] ⟶ C` is a pushout square with span `q`. -/
lemma exists_isPushoutSquare_of_isColimit {q : (Λ[2, 0] : SSet.{u}) ⟶ C} {c : (coslice q) _⦋0⦌}
    (hc : coslice.IsColimit q c) :
    ∃ σ : Δ[1] ⊗ Δ[1] ⟶ C, squareSpan σ = q ∧ IsPushoutSquare σ := by
  have h : squareSpan (join.hornConeIso.inv ≫ (coslice.objEquiv c).1) = q := by
    rw [squareSpan_def, Iso.hom_inv_id_assoc, (coslice.objEquiv c).2]
  -- The cocone defined by this square is `c` itself.
  have hc' : coslice.objEquiv.symm ⟨_, (squareSpan_def _).symm.trans h⟩ = c :=
    (Equiv.symm_apply_eq _).2 (Subtype.ext (Iso.hom_inv_id_assoc _ _))
  exact ⟨_, h, (isPushoutSquare_iff_isColimit h).2 (by rw [hc']; exact hc)⟩

end SSet
