/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import TauCeti.AlgebraicTopology.Quasicategory.Limit
public import TauCeti.AlgebraicTopology.SimplicialSet.Join.Square

/-!
# Stable quasicategories

A *zero vertex* of a simplicial set `C` (`SSet.IsZeroVertex`) is a vertex which is both initial and
terminal. A *square* in `C` is a map `σ : Δ[1] ⊗ Δ[1] ⟶ C`. Through the isomorphisms
`Δ[0] ⋆ Λ[2, 2] ≅ Δ[1] ⊗ Δ[1]` (`SSet.join.coneHornIso`) and `Λ[2, 0] ⋆ Δ[0] ≅ Δ[1] ⊗ Δ[1]`
(`SSet.join.hornConeIso`), a square is a cone over its cospan `(1, 0) ⟶ (1, 1) ⟵ (0, 1)`
(`SSet.squareCospan`, `SSet.squareCone`) and a cocone under its span
`(1, 0) ⟵ (0, 0) ⟶ (0, 1)` (`SSet.squareSpan`, `SSet.squareCocone`). It is a *pullback square*
(`SSet.IsPullbackSquare`) if this cone is a limit cone, and a *pushout square*
(`SSet.IsPushoutSquare`) if this cocone is a colimit cocone. Both isomorphisms send the vertices
of the horns to the same vertices of the square, so that the cone point `(0, 0)` of the cone is the
initial vertex of the span, and the cone point `(1, 1)` of the cocone is the final vertex of the
cospan.

Following Lurie, a quasicategory `C` is *stable* (`SSet.IsStable`) if it has a zero vertex, every
diagram `K ⟶ C` indexed by a finite simplicial set `K` has a limit cone and a colimit cocone, and a
square in `C` is a pullback square exactly when it is a pushout square.

## Main results

* `SSet.isPullbackSquare_iff_isLimit`, `SSet.isPushoutSquare_iff_isColimit`: a square is a pullback
  (pushout) square exactly when the corresponding cone (cocone) is a limit (colimit), for any
  presentation of its cospan (span).
* `SSet.IsStable.exists_isPullbackSquare`, `SSet.IsStable.exists_isPushoutSquare`: in a stable
  quasicategory every cospan is the cospan of a pullback square, and every span is the span of a
  pushout square; by stability these squares are both pullback and pushout squares.
* `SSet.isStable_stdSimplex_zero`: the point `Δ[0]` is stable.
* `SSet.not_isStable_of_not_nonempty`: the empty simplicial set is not stable, for want of a zero
  vertex.

## References

* J. Lurie, *Higher Algebra*, Definitions 1.1.1.1 and 1.1.1.9 (pointed and stable
  `∞`-categories).
* J. Lurie, *Higher Topos Theory*, §4.4.2 (pullback and pushout squares as limits of cospans and
  colimits of spans).
-/

public section

universe u

open CategoryTheory MonoidalCategory Simplicial

namespace SSet

variable {C : SSet.{u}}

/-! ### Zero vertices -/

/-- A vertex of a simplicial set is a *zero vertex* if it is both initial and terminal. In a
quasicategory this is a zero object. -/
def IsZeroVertex (x : C _⦋0⦌) : Prop :=
  C.IsInitialVertex x ∧ C.IsTerminalVertex x

lemma isZeroVertex_iff (x : C _⦋0⦌) :
    C.IsZeroVertex x ↔ C.IsInitialVertex x ∧ C.IsTerminalVertex x :=
  Iff.rfl

namespace IsZeroVertex

variable {x : C _⦋0⦌}

/-- A zero vertex is initial. -/
lemma isInitialVertex (hx : C.IsZeroVertex x) : C.IsInitialVertex x :=
  hx.1

/-- A zero vertex is terminal. -/
lemma isTerminalVertex (hx : C.IsZeroVertex x) : C.IsTerminalVertex x :=
  hx.2

/-- Zero vertices are preserved by isomorphisms of simplicial sets. -/
lemma map_iso {D : SSet.{u}} (hx : C.IsZeroVertex x) (e : C ≅ D) :
    D.IsZeroVertex (e.hom.app _ x) :=
  ⟨hx.1.map_iso e, hx.2.map_iso e⟩

end IsZeroVertex

/-- Zero vertices correspond under isomorphisms of simplicial sets. -/
lemma isZeroVertex_iff_of_iso {D : SSet.{u}} (e : C ≅ D) (x : C _⦋0⦌) :
    D.IsZeroVertex (e.hom.app _ x) ↔ C.IsZeroVertex x :=
  and_congr (isInitialVertex_iff_of_iso e x) (isTerminalVertex_iff_of_iso e x)

/-! ### Pullback and pushout squares -/

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

/-! ### Stable quasicategories -/

/-- A quasicategory `C` is *stable* if it has a zero vertex, every diagram in `C` indexed by a
finite simplicial set has a limit cone and a colimit cocone, and a square in `C` is a pullback
square exactly when it is a pushout square. -/
class IsStable (C : SSet.{u}) : Prop extends C.Quasicategory where
  /-- A stable quasicategory has a zero vertex. -/
  exists_isZeroVertex : ∃ x : C _⦋0⦌, C.IsZeroVertex x
  /-- A stable quasicategory has the limits of all finite diagrams. -/
  exists_isLimit (K : SSet.{u}) [K.Finite] (p : K ⟶ C) : ∃ c, slice.IsLimit p c
  /-- A stable quasicategory has the colimits of all finite diagrams. -/
  exists_isColimit (K : SSet.{u}) [K.Finite] (p : K ⟶ C) : ∃ c, coslice.IsColimit p c
  /-- In a stable quasicategory, the pullback squares are the pushout squares. -/
  isPullbackSquare_iff_isPushoutSquare (σ : Δ[1] ⊗ Δ[1] ⟶ C) :
    IsPullbackSquare σ ↔ IsPushoutSquare σ

namespace IsStable

variable [C.IsStable]

/-- In a stable quasicategory, every cospan `q : Λ[2, 2] ⟶ C` is the cospan of a pullback square,
which is also a pushout square. -/
theorem exists_isPullbackSquare (q : (Λ[2, 2] : SSet.{u}) ⟶ C) :
    ∃ σ : Δ[1] ⊗ Δ[1] ⟶ C, squareCospan σ = q ∧ IsPullbackSquare σ ∧ IsPushoutSquare σ := by
  obtain ⟨c, hc⟩ := exists_isLimit _ q
  obtain ⟨σ, hσ, h⟩ := exists_isPullbackSquare_of_isLimit hc
  exact ⟨σ, hσ, h, (isPullbackSquare_iff_isPushoutSquare σ).1 h⟩

/-- In a stable quasicategory, every span `q : Λ[2, 0] ⟶ C` is the span of a pushout square, which
is also a pullback square. -/
theorem exists_isPushoutSquare (q : (Λ[2, 0] : SSet.{u}) ⟶ C) :
    ∃ σ : Δ[1] ⊗ Δ[1] ⟶ C, squareSpan σ = q ∧ IsPullbackSquare σ ∧ IsPushoutSquare σ := by
  obtain ⟨c, hc⟩ := exists_isColimit _ q
  obtain ⟨σ, hσ, h⟩ := exists_isPushoutSquare_of_isColimit hc
  exact ⟨σ, hσ, (isPullbackSquare_iff_isPushoutSquare σ).2 h, h⟩

/-- A stable quasicategory is nonempty: it has a zero vertex. -/
lemma nonempty : C.Nonempty :=
  let ⟨x, _⟩ := exists_isZeroVertex (C := C)
  ⟨x⟩

end IsStable

/-- The empty simplicial set is not stable, since it has no zero vertex. -/
theorem not_isStable_of_not_nonempty (hC : ¬ C.Nonempty) : ¬ C.IsStable :=
  fun _ ↦ hC IsStable.nonempty

/-! ### The point is stable -/

/-- **The point is stable**: in `Δ[0]` its vertex is a zero vertex, every diagram has a limit cone
and a colimit cocone, and every cone and every cocone is a limit and a colimit. -/
instance isStable_stdSimplex_zero : (Δ[0] : SSet.{u}).IsStable where
  exists_isZeroVertex := ⟨stdSimplex.obj₀Equiv.symm 0, stdSimplex.isInitialVertex_zero 0,
    stdSimplex.isTerminalVertex_last 0⟩
  exists_isLimit _ _ _ := ⟨slice.objEquiv.symm ⟨stdSimplex.isTerminalObj₀.from _,
    stdSimplex.isTerminalObj₀.hom_ext _ _⟩, slice.isLimit_of_stdSimplex_zero _ _⟩
  exists_isColimit _ _ _ := ⟨coslice.objEquiv.symm ⟨stdSimplex.isTerminalObj₀.from _,
    stdSimplex.isTerminalObj₀.hom_ext _ _⟩, coslice.isColimit_of_stdSimplex_zero _ _⟩
  isPullbackSquare_iff_isPushoutSquare σ :=
    iff_of_true ((isPullbackSquare_iff σ).2 (slice.isLimit_of_stdSimplex_zero _ _))
      ((isPushoutSquare_iff σ).2 (coslice.isColimit_of_stdSimplex_zero _ _))

end SSet
