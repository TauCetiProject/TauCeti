/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import TauCeti.AlgebraicTopology.Quasicategory.Limit.Basic
public import TauCeti.AlgebraicTopology.Quasicategory.ZeroVertex
public import TauCeti.AlgebraicTopology.SimplicialSet.Join.Square

/-!
# Pullback squares, pushout squares and stable quasicategories

A *square* in a simplicial set `X` is a map `σ : Δ[1] ⊗ Δ[1] ⟶ X`. Through the identification of
`Δ[1] ⊗ Δ[1]` with the cone `Δ[0] ⋆ Λ[2, 2]` (`SSet.square.coneIso`), the square is a cone
(`SSet.square.cone σ`) over its cospan `σ(1, 0) ⟶ σ(1, 1) ⟵ σ(0, 1)` (`SSet.square.cospan σ`), with
cone point `σ(0, 0)`, and it is a *pullback square* (`SSet.IsPullbackSquare`) if this is a limit
cone. Dually, through `Δ[1] ⊗ Δ[1] ≅ Λ[2, 0] ⋆ Δ[0]` (`SSet.square.coconeIso`), the square is a
cocone (`SSet.square.cocone σ`) under its span `σ(1, 0) ⟵ σ(0, 0) ⟶ σ(0, 1)`
(`SSet.square.span σ`), with cone point `σ(1, 1)`, and it is a *pushout square*
(`SSet.IsPushoutSquare`) if this is a colimit cocone. The edges of the cospan and the span are
edges of the square (`SSet.square.ι_zero_comp_cospan`, `SSet.square.ι_one_comp_cospan`,
`SSet.square.ι_two_comp_span`, `SSet.square.ι_one_comp_span`). Every limit cone over a cospan
`Λ[2, 2] ⟶ X` is a pullback square with that cospan (`SSet.exists_isPullbackSquare_of_isLimit`),
and every colimit cocone under a span `Λ[2, 0] ⟶ X` a pushout square with that span
(`SSet.exists_isPushoutSquare_of_isColimit`).

A quasicategory is *stable* (`SSet.IsStable`) if it is pointed (`SSet.HasZeroVertex`), has
limits and colimits of all diagrams indexed by finite simplicial sets, and a square in it is a
pullback square exactly when it is a pushout square. This is the characterization of Lurie's
stable ∞-categories in *Higher Algebra*, Proposition 1.1.3.4; the conditions of Definition 1.1.1.9
(fibres, cofibres, and the agreement of fibre and cofibre sequences) are its special cases with a
zero corner. In a stable quasicategory every cospan is the cospan of a square that is both a
pullback and a pushout square (`SSet.IsStable.exists_isPullbackSquare`), and dually every span
(`SSet.IsStable.exists_isPushoutSquare`). The motivating example, not treated here, is the dg
nerve of cochain complexes, whose suspension and cofibres are the shift and the mapping cone
(Lurie, *Higher Algebra*, §1.3.2). Its homotopy category is the homotopy category of complexes; the
derived ∞-category is obtained from it by restricting to fibrant (for instance K-injective)
complexes.

The point `Δ[0]` is stable (`SSet.stdSimplex.isStable_zero`), since every cone and cocone in it is
a limit; the interval `Δ[1]` is not (`SSet.stdSimplex.not_isStable_one`), since it has no zero
vertex, and neither is an empty simplicial set (`SSet.not_isStable_of_not_nonempty`). In `Δ[1]`,
the square sending `(0, 0)` to `0` and the other vertices to `1` is not a pullback square
(`SSet.stdSimplex.not_isPullbackSquare_coneIso_inv_comp_π`): the limit of its cospan, constant at
`1`, is `1`. Dually, the square sending `(1, 1)` to `1` and the other vertices to `0` is not a
pushout square (`SSet.stdSimplex.not_isPushoutSquare_coconeIso_inv_comp_π`).

## References

* J. Lurie, *Higher Algebra*, Definition 1.1.1.9, Proposition 1.1.3.4 and §1.3.2.
* J. Lurie, *Higher Topos Theory*, §1.2.13 and §4.4.2.
-/

public section

universe u

open CategoryTheory Limits MonoidalCategory Simplicial

namespace SSet

variable {X : SSet.{u}}

namespace square

/-- The cospan `σ(1, 0) ⟶ σ(1, 1) ⟵ σ(0, 1)` of a square `σ` in a simplicial set: its restriction
to the base of the cone `Δ[0] ⋆ Λ[2, 2] ≅ Δ[1] ⊗ Δ[1]`. -/
noncomputable def cospan (σ : Δ[1] ⊗ Δ[1] ⟶ X) : (Λ[2, 2] : SSet.{u}) ⟶ X :=
  join.inr _ _ ≫ coneIso.hom ≫ σ

/-- The cospan of a square is its restriction to the base of the cone `Δ[0] ⋆ Λ[2, 2]`. -/
lemma cospan_def (σ : Δ[1] ⊗ Δ[1] ⟶ X) : cospan σ = join.inr _ _ ≫ coneIso.hom ≫ σ := by
  rw [cospan]

/-- The edge of the cospan of `σ` from `1` to `2` is the edge of `σ` from `(0, 1)` to `(1, 1)`. -/
@[reassoc (attr := simp)]
lemma ι_zero_comp_cospan (σ : Δ[1] ⊗ Δ[1] ⟶ X) :
    horn.ι 2 0 (by decide) ≫ cospan σ =
      CartesianMonoidalCategory.lift (𝟙 Δ[1]) (const (stdSimplex.const 1 1 _)) ≫ σ := by
  rw [cospan_def, ι_zero_comp_inr_comp_coneIso_hom_assoc]

/-- The edge of the cospan of `σ` from `0` to `2` is the edge of `σ` from `(1, 0)` to `(1, 1)`. -/
@[reassoc (attr := simp)]
lemma ι_one_comp_cospan (σ : Δ[1] ⊗ Δ[1] ⟶ X) :
    horn.ι 2 1 (by decide) ≫ cospan σ =
      CartesianMonoidalCategory.lift (const (stdSimplex.const 1 1 _)) (𝟙 Δ[1]) ≫ σ := by
  rw [cospan_def, ι_one_comp_inr_comp_coneIso_hom_assoc]

/-- A square `σ`, as a cone over its cospan with cone point `σ(0, 0)`: a vertex of the slice over
`SSet.square.cospan σ`. -/
noncomputable def cone (σ : Δ[1] ⊗ Δ[1] ⟶ X) : (slice (cospan σ)) _⦋0⦌ :=
  slice.objEquiv.symm ⟨coneIso.hom ≫ σ, rfl⟩

/-- The cone of a square is the square, read on `Δ[0] ⋆ Λ[2, 2] ≅ Δ[1] ⊗ Δ[1]`. -/
@[simp]
lemma objEquiv_cone (σ : Δ[1] ⊗ Δ[1] ⟶ X) : (slice.objEquiv (cone σ)).val = coneIso.hom ≫ σ := by
  rw [cone, Equiv.apply_symm_apply]

/-- The span `σ(1, 0) ⟵ σ(0, 0) ⟶ σ(0, 1)` of a square `σ` in a simplicial set: its restriction to
the base of the cocone `Λ[2, 0] ⋆ Δ[0] ≅ Δ[1] ⊗ Δ[1]`. -/
noncomputable def span (σ : Δ[1] ⊗ Δ[1] ⟶ X) : (Λ[2, 0] : SSet.{u}) ⟶ X :=
  join.inl _ _ ≫ coconeIso.hom ≫ σ

/-- The span of a square is its restriction to the base of the cocone `Λ[2, 0] ⋆ Δ[0]`. -/
lemma span_def (σ : Δ[1] ⊗ Δ[1] ⟶ X) : span σ = join.inl _ _ ≫ coconeIso.hom ≫ σ := by
  rw [span]

/-- The edge of the span of `σ` from `0` to `1` is the edge of `σ` from `(0, 0)` to `(1, 0)`. -/
@[reassoc (attr := simp)]
lemma ι_two_comp_span (σ : Δ[1] ⊗ Δ[1] ⟶ X) :
    horn.ι 0 2 (by decide) ≫ span σ =
      CartesianMonoidalCategory.lift (𝟙 Δ[1]) (const (stdSimplex.const 1 0 _)) ≫ σ := by
  rw [span_def, ι_two_comp_inl_comp_coconeIso_hom_assoc]

/-- The edge of the span of `σ` from `0` to `2` is the edge of `σ` from `(0, 0)` to `(0, 1)`. -/
@[reassoc (attr := simp)]
lemma ι_one_comp_span (σ : Δ[1] ⊗ Δ[1] ⟶ X) :
    horn.ι 0 1 (by decide) ≫ span σ =
      CartesianMonoidalCategory.lift (const (stdSimplex.const 1 0 _)) (𝟙 Δ[1]) ≫ σ := by
  rw [span_def, ι_one_comp_inl_comp_coconeIso_hom_assoc]

/-- A square `σ`, as a cocone under its span with cone point `σ(1, 1)`: a vertex of the coslice
under `SSet.square.span σ`. -/
noncomputable def cocone (σ : Δ[1] ⊗ Δ[1] ⟶ X) : (coslice (span σ)) _⦋0⦌ :=
  coslice.objEquiv.symm ⟨coconeIso.hom ≫ σ, rfl⟩

/-- The cocone of a square is the square, read on `Λ[2, 0] ⋆ Δ[0] ≅ Δ[1] ⊗ Δ[1]`. -/
@[simp]
lemma objEquiv_cocone (σ : Δ[1] ⊗ Δ[1] ⟶ X) :
    (coslice.objEquiv (cocone σ)).val = coconeIso.hom ≫ σ := by
  rw [cocone, Equiv.apply_symm_apply]

end square

/-- A square `σ : Δ[1] ⊗ Δ[1] ⟶ X` is a *pullback square* if, read as a cone over its cospan
`σ(1, 0) ⟶ σ(1, 1) ⟵ σ(0, 1)`, it is a limit cone. -/
def IsPullbackSquare (σ : Δ[1] ⊗ Δ[1] ⟶ X) : Prop :=
  slice.IsLimit (square.cospan σ) (square.cone σ)

lemma isPullbackSquare_iff (σ : Δ[1] ⊗ Δ[1] ⟶ X) :
    IsPullbackSquare σ ↔ slice.IsLimit (square.cospan σ) (square.cone σ) :=
  Iff.rfl

/-- A square `σ : Δ[1] ⊗ Δ[1] ⟶ X` is a *pushout square* if, read as a cocone under its span
`σ(1, 0) ⟵ σ(0, 0) ⟶ σ(0, 1)`, it is a colimit cocone. -/
def IsPushoutSquare (σ : Δ[1] ⊗ Δ[1] ⟶ X) : Prop :=
  coslice.IsColimit (square.span σ) (square.cocone σ)

lemma isPushoutSquare_iff (σ : Δ[1] ⊗ Δ[1] ⟶ X) :
    IsPushoutSquare σ ↔ coslice.IsColimit (square.span σ) (square.cocone σ) :=
  Iff.rfl

/-- A square `σ` is a pullback square exactly when the cone `Δ[0] ⋆ Λ[2, 2] ⟶ X` it defines is a
limit cone over `q`, for any diagram `q` equal to the cospan of `σ`. -/
lemma isPullbackSquare_iff_isLimit {σ : Δ[1] ⊗ Δ[1] ⟶ X} {q : (Λ[2, 2] : SSet.{u}) ⟶ X}
    (h : square.cospan σ = q) :
    IsPullbackSquare σ ↔ slice.IsLimit q
      (slice.objEquiv.symm ⟨square.coneIso.hom ≫ σ, (square.cospan_def σ).symm.trans h⟩) := by
  subst h
  rfl

/-- A square `σ` is a pushout square exactly when the cocone `Λ[2, 0] ⋆ Δ[0] ⟶ X` it defines is a
colimit cocone under `q`, for any diagram `q` equal to the span of `σ`. -/
lemma isPushoutSquare_iff_isColimit {σ : Δ[1] ⊗ Δ[1] ⟶ X} {q : (Λ[2, 0] : SSet.{u}) ⟶ X}
    (h : square.span σ = q) :
    IsPushoutSquare σ ↔ coslice.IsColimit q
      (coslice.objEquiv.symm ⟨square.coconeIso.hom ≫ σ, (square.span_def σ).symm.trans h⟩) := by
  subst h
  rfl

/-- Every limit cone over a cospan `q : Λ[2, 2] ⟶ X` is a pullback square with cospan `q`. -/
lemma exists_isPullbackSquare_of_isLimit {q : (Λ[2, 2] : SSet.{u}) ⟶ X} {c : (slice q) _⦋0⦌}
    (hc : slice.IsLimit q c) :
    ∃ σ : Δ[1] ⊗ Δ[1] ⟶ X, square.cospan σ = q ∧ IsPullbackSquare σ := by
  have h : square.cospan (square.coneIso.inv ≫ (slice.objEquiv c).val) = q := by
    rw [square.cospan_def, Iso.hom_inv_id_assoc, (slice.objEquiv c).property]
  -- The cone defined by this square is `c` itself.
  have hc' : slice.objEquiv.symm ⟨_, (square.cospan_def _).symm.trans h⟩ = c :=
    (Equiv.symm_apply_eq _).2 (Subtype.ext (Iso.hom_inv_id_assoc _ _))
  exact ⟨_, h, (isPullbackSquare_iff_isLimit h).2 (by rw [hc']; exact hc)⟩

/-- Every colimit cocone under a span `q : Λ[2, 0] ⟶ X` is a pushout square with span `q`. -/
lemma exists_isPushoutSquare_of_isColimit {q : (Λ[2, 0] : SSet.{u}) ⟶ X} {c : (coslice q) _⦋0⦌}
    (hc : coslice.IsColimit q c) :
    ∃ σ : Δ[1] ⊗ Δ[1] ⟶ X, square.span σ = q ∧ IsPushoutSquare σ := by
  have h : square.span (square.coconeIso.inv ≫ (coslice.objEquiv c).val) = q := by
    rw [square.span_def, Iso.hom_inv_id_assoc, (coslice.objEquiv c).property]
  -- The cocone defined by this square is `c` itself.
  have hc' : coslice.objEquiv.symm ⟨_, (square.span_def _).symm.trans h⟩ = c :=
    (Equiv.symm_apply_eq _).2 (Subtype.ext (Iso.hom_inv_id_assoc _ _))
  exact ⟨_, h, (isPushoutSquare_iff_isColimit h).2 (by rw [hc']; exact hc)⟩

/-- In a terminal simplicial set, such as `Δ[0]`, every square is a pullback square. -/
lemma isPullbackSquare_of_isTerminal (hX : IsTerminal X) (σ : Δ[1] ⊗ Δ[1] ⟶ X) :
    IsPullbackSquare σ :=
  slice.isLimit_of_isTerminal _ hX _

/-- In a terminal simplicial set, such as `Δ[0]`, every square is a pushout square. -/
lemma isPushoutSquare_of_isTerminal (hX : IsTerminal X) (σ : Δ[1] ⊗ Δ[1] ⟶ X) :
    IsPushoutSquare σ :=
  coslice.isColimit_of_isTerminal _ hX _

variable (X) in
/-- A quasicategory `X` is *stable* if it is pointed (has a zero vertex), every diagram in `X`
indexed by a finite simplicial set has a limit and a colimit, and a square in `X` is a pullback
square exactly when it is a pushout square (Lurie, *Higher Algebra*, Proposition 1.1.3.4). -/
class IsStable [X.Quasicategory] : Prop where
  /-- A stable quasicategory has a zero object. -/
  hasZeroVertex : X.HasZeroVertex
  /-- Every diagram indexed by a finite simplicial set has a limit. -/
  exists_isLimit {K : SSet.{u}} [K.Finite] (p : K ⟶ X) : ∃ c, slice.IsLimit p c
  /-- Every diagram indexed by a finite simplicial set has a colimit. -/
  exists_isColimit {K : SSet.{u}} [K.Finite] (p : K ⟶ X) : ∃ c, coslice.IsColimit p c
  /-- A square is a pullback square exactly when it is a pushout square. -/
  isPullbackSquare_iff_isPushoutSquare (σ : Δ[1] ⊗ Δ[1] ⟶ X) :
    IsPullbackSquare σ ↔ IsPushoutSquare σ

namespace IsStable

variable [X.Quasicategory] [X.IsStable]

/-- In a stable quasicategory, every cospan `q : Λ[2, 2] ⟶ X` is the cospan of a pullback square,
which is also a pushout square. -/
theorem exists_isPullbackSquare (q : (Λ[2, 2] : SSet.{u}) ⟶ X) :
    ∃ σ : Δ[1] ⊗ Δ[1] ⟶ X, square.cospan σ = q ∧ IsPullbackSquare σ ∧ IsPushoutSquare σ := by
  obtain ⟨c, hc⟩ := exists_isLimit q
  obtain ⟨σ, hσ, h⟩ := exists_isPullbackSquare_of_isLimit hc
  exact ⟨σ, hσ, h, (isPullbackSquare_iff_isPushoutSquare σ).1 h⟩

/-- In a stable quasicategory, every span `q : Λ[2, 0] ⟶ X` is the span of a pushout square, which
is also a pullback square. -/
theorem exists_isPushoutSquare (q : (Λ[2, 0] : SSet.{u}) ⟶ X) :
    ∃ σ : Δ[1] ⊗ Δ[1] ⟶ X, square.span σ = q ∧ IsPullbackSquare σ ∧ IsPushoutSquare σ := by
  obtain ⟨c, hc⟩ := exists_isColimit q
  obtain ⟨σ, hσ, h⟩ := exists_isPushoutSquare_of_isColimit hc
  exact ⟨σ, hσ, (isPullbackSquare_iff_isPushoutSquare σ).2 h, h⟩

/-- A stable quasicategory is nonempty: it has a zero vertex. -/
lemma nonempty : X.Nonempty :=
  let ⟨x, _⟩ := (hasZeroVertex_iff (X := X)).1 hasZeroVertex
  ⟨x⟩

end IsStable

/-- An empty simplicial set is not stable, since it has no zero vertex. -/
theorem not_isStable_of_not_nonempty [X.Quasicategory] (hX : ¬ X.Nonempty) : ¬ X.IsStable :=
  fun _ ↦ hX IsStable.nonempty

/-- The point `Δ[0]` is a stable quasicategory: its unique vertex is a zero vertex, and every cone
and every cocone in it is a limit. -/
instance stdSimplex.isStable_zero : (Δ[0] : SSet.{u}).IsStable where
  hasZeroVertex := stdSimplex.hasZeroVertex_zero
  exists_isLimit _ := ⟨slice.objEquiv.symm ⟨stdSimplex.isTerminalObj₀.from _,
    stdSimplex.isTerminalObj₀.hom_ext _ _⟩,
    slice.isLimit_of_isTerminal _ stdSimplex.isTerminalObj₀ _⟩
  exists_isColimit _ := ⟨coslice.objEquiv.symm ⟨stdSimplex.isTerminalObj₀.from _,
    stdSimplex.isTerminalObj₀.hom_ext _ _⟩,
    coslice.isColimit_of_isTerminal _ stdSimplex.isTerminalObj₀ _⟩
  isPullbackSquare_iff_isPushoutSquare σ :=
    iff_of_true (isPullbackSquare_of_isTerminal stdSimplex.isTerminalObj₀ σ)
      (isPushoutSquare_of_isTerminal stdSimplex.isTerminalObj₀ σ)

/-- The interval `Δ[1]` is not a stable quasicategory, since it has no zero vertex. -/
lemma stdSimplex.not_isStable_one : ¬ (Δ[1] : SSet.{u}).IsStable :=
  fun h ↦ stdSimplex.not_hasZeroVertex_one h.hasZeroVertex

/-- The square in `Δ[1]` sending `(0, 0)` to `0` and the other three vertices to `1` is not a
pullback square: its cospan is constant at `1`, and the cone over it with cone point `1` has no
morphism to the square, whose cone point is `0`. -/
lemma stdSimplex.not_isPullbackSquare_coneIso_inv_comp_π :
    ¬ IsPullbackSquare (square.coneIso.{u}.inv ≫ join.π _ _) := by
  intro h
  have hd : join.inr _ _ ≫
      (SSet.const (stdSimplex.const 1 1 _) : join Δ[0] (Λ[2, 2] : SSet.{u}) ⟶ _) =
      square.cospan (square.coneIso.{u}.inv ≫ join.π _ _) := by
    rw [square.cospan_def, Iso.hom_inv_id_assoc, join.inr_π, comp_const]
  obtain ⟨e⟩ := ((isPullbackSquare_iff _).1 h).nonempty_edge (slice.objEquiv.symm ⟨_, hd⟩)
  have key := Nonempty.intro (e.map (slice.π _))
  have h₁ : (slice.π _).app _ (slice.objEquiv.symm ⟨_, hd⟩) =
      stdSimplex.obj₀Equiv.{u}.symm 1 := by
    rw [slice.π_app, Equiv.apply_symm_apply, comp_const, yonedaEquiv_const,
      stdSimplex.obj₀Equiv_symm_apply]
  have h₀ : (slice.π _).app _ (square.cone (square.coneIso.{u}.inv ≫ join.π _ _)) =
      stdSimplex.obj₀Equiv.{u}.symm 0 := by
    rw [slice.π_app, square.objEquiv_cone, Iso.hom_inv_id_assoc, join.inl_π, yonedaEquiv_const,
      stdSimplex.obj₀Equiv_symm_apply]
  rw [h₁, h₀, stdSimplex.nonempty_edge_iff] at key
  exact absurd key (by decide)

/-- The square in `Δ[1]` sending `(1, 1)` to `1` and the other three vertices to `0` is not a
pushout square: its span is constant at `0`, and the cocone under it with cone point `0` has no
morphism from the square, whose cone point is `1`. -/
lemma stdSimplex.not_isPushoutSquare_coconeIso_inv_comp_π :
    ¬ IsPushoutSquare (square.coconeIso.{u}.inv ≫ join.π _ _) := by
  intro h
  have hd : join.inl _ _ ≫
      (SSet.const (stdSimplex.const 1 0 _) : join (Λ[2, 0] : SSet.{u}) Δ[0] ⟶ _) =
      square.span (square.coconeIso.{u}.inv ≫ join.π _ _) := by
    rw [square.span_def, Iso.hom_inv_id_assoc, join.inl_π, comp_const]
  obtain ⟨e⟩ := ((isPushoutSquare_iff _).1 h).nonempty_edge (coslice.objEquiv.symm ⟨_, hd⟩)
  have key := Nonempty.intro (e.map (coslice.π _))
  have h₁ : (coslice.π _).app _ (square.cocone (square.coconeIso.{u}.inv ≫ join.π _ _)) =
      stdSimplex.obj₀Equiv.{u}.symm 1 := by
    rw [coslice.π_app, square.objEquiv_cocone, Iso.hom_inv_id_assoc, join.inr_π,
      yonedaEquiv_const, stdSimplex.obj₀Equiv_symm_apply]
  have h₀ : (coslice.π _).app _ (coslice.objEquiv.symm ⟨_, hd⟩) =
      stdSimplex.obj₀Equiv.{u}.symm 0 := by
    rw [coslice.π_app, Equiv.apply_symm_apply, comp_const, yonedaEquiv_const,
      stdSimplex.obj₀Equiv_symm_apply]
  rw [h₁, h₀, stdSimplex.nonempty_edge_iff] at key
  exact absurd key (by decide)

end SSet
