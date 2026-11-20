/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import TauCeti.AlgebraicTopology.Quasicategory.Square
public import TauCeti.AlgebraicTopology.Quasicategory.ZeroVertex

/-!
# Stable quasicategories

Following Lurie, a quasicategory `C` is *stable* (`SSet.IsStable`) if it has a zero vertex
(`SSet.IsZeroVertex`), every diagram `K ⟶ C` indexed by a finite simplicial set `K` has a limit
cone and a colimit cocone, and a square `Δ[1] ⊗ Δ[1] ⟶ C` is a pullback square
(`SSet.IsPullbackSquare`) exactly when it is a pushout square (`SSet.IsPushoutSquare`).

## Main results

* `SSet.IsStable.exists_isPullbackSquare`, `SSet.IsStable.exists_isPushoutSquare`: in a stable
  quasicategory every cospan is the cospan of a pullback square, and every span is the span of a
  pushout square; by stability these squares are both pullback and pushout squares.
* `SSet.isStable_stdSimplex_zero`: the point `Δ[0]` is stable.
* `SSet.not_isStable_of_not_nonempty`: the empty simplicial set is not stable, for want of a zero
  vertex.

## References

* J. Lurie, *Higher Algebra*, Definitions 1.1.1.1 and 1.1.1.9 (pointed and stable
  `∞`-categories).
-/

public section

universe u

open CategoryTheory MonoidalCategory Simplicial

namespace SSet

variable {C : SSet.{u}}

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
  exists_isZeroVertex := ⟨stdSimplex.obj₀Equiv.symm 0, (isZeroVertex_iff _).2
    ⟨stdSimplex.isInitialVertex_zero 0, stdSimplex.isTerminalVertex_last 0⟩⟩
  exists_isLimit _ _ _ := ⟨slice.objEquiv.symm ⟨stdSimplex.isTerminalObj₀.from _,
    stdSimplex.isTerminalObj₀.hom_ext _ _⟩, slice.isLimit_of_stdSimplex_zero _ _⟩
  exists_isColimit _ _ _ := ⟨coslice.objEquiv.symm ⟨stdSimplex.isTerminalObj₀.from _,
    stdSimplex.isTerminalObj₀.hom_ext _ _⟩, coslice.isColimit_of_stdSimplex_zero _ _⟩
  isPullbackSquare_iff_isPushoutSquare σ :=
    iff_of_true ((isPullbackSquare_iff σ).2 (slice.isLimit_of_stdSimplex_zero _ _))
      ((isPushoutSquare_iff σ).2 (coslice.isColimit_of_stdSimplex_zero _ _))

end SSet
