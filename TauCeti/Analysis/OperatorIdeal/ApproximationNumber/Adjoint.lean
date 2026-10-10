/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.CompactHilbert
public import TauCeti.LinearAlgebra.Dimension.RankComp

/-!
# Adjoint invariance of approximation numbers

This module proves that approximation numbers of bounded operators between
Hilbert spaces are invariant under adjoint. It is separated from the elementary
normed-operator API so the foundational definition does not require
inner-product-space imports.

## Namespace note

These declarations still sit in the **root** Mathlib namespace `ContinuousLinearMap`,
which is no longer the convention: Tau Ceti mirrors Mathlib type namespaces *inside*
`namespace TauCeti`, and `ForTauCeti/README.md` § "Final namespaces from day one"
now says so.

The justification previously recorded here was that field projection binds `T.foo`
only to a literal `ContinuousLinearMap.foo`, so nesting would break dot notation.
That is only half true — it does not consult the *enclosing namespace*, but it does
consult `open`s, so `open TauCeti` restores it. Nesting costs an `open` per consuming
file and nothing else.

This module is on the migration list, not an exception to the rule.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib/Analysis/Normed/Operator/ApproximationNumberAdjoint.lean`
  at Davis--Kahan commit `fc38eb48b9b49f2e1d87fe0c7022dc5e262820a7`.
* Original declarations: `ContinuousLinearMap.approximationNumber_adjoint` and
  the private helpers in the same namespace.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss,
  Arnav Mehta, Rawad Kansoh; Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* Extraction class: **copied**, converted to the Tau Ceti module system.
  Declaration names are unchanged (they already extend the canonical Mathlib
  namespace).  No mathematical change.
* Spectra influence: **none** — this module has no Spectra dependency and never
  did; it imports only Mathlib and the sibling `Basic` staging module.
-/

public section

noncomputable section

universe u v w

namespace ContinuousLinearMap

open Cardinal

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} {F : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- A finite-rank bounded operator has an adjoint obeying the same
natural-number rank bound.

The proof factors the operator through its finite-dimensional range.  After
 taking adjoints, the adjoint still factors through that same range.

The two ranks live in different universes once the domain and codomain are
allowed to move independently, so the conclusion is stated against the
natural-number bound, which `Cardinal.lift` fixes. -/
theorem rank_adjoint_le_natCast_of_rank_le
    (R : E →L[𝕜] F) {n : ℕ} (hR : R.rank ≤ (n : Cardinal)) :
    R.adjoint.rank ≤ (n : Cardinal) := by
  have hlt : R.rank < Cardinal.aleph0 :=
    hR.trans_lt Cardinal.natCast_lt_aleph0
  have hrank_eq : R.rank = (R.rank.toNat : Cardinal) := by
    exact (Cardinal.cast_toNat_of_lt_aleph0 hlt).symm
  let : FiniteDimensional 𝕜 R.range :=
    Module.finite_of_rank_eq_nat hrank_eq
  let : CompleteSpace R.range := FiniteDimensional.complete 𝕜 R.range
  have hadj : R.adjoint =
      R.rangeRestrict.adjoint ∘L R.range.subtypeL.adjoint := by
    rw [← ContinuousLinearMap.adjoint_comp]
    congr 1
  have hrestrict : R.rangeRestrict.adjoint.rank ≤ (n : Cardinal) :=
    Cardinal.lift_le_natCast.mp
      ((lift_rank_range_le R.rangeRestrict.adjoint.toLinearMap).trans
        (Cardinal.lift_le_natCast.mpr hR))
  rw [hadj]
  exact (rank_comp_le_left _ _).trans hrestrict

/-- Finite rank is preserved by the adjoint.

Unlike a plain rank equality this is universe-safe: the two ranks are cardinals
in different universes when the domain and codomain move independently, but
finiteness transfers through the natural-number bound. -/
theorem rank_adjoint_lt_aleph0 (R : E →L[𝕜] F) (hR : R.rank < Cardinal.aleph0) :
    R.adjoint.rank < Cardinal.aleph0 := by
  have hle : R.rank ≤ (R.rank.toNat : Cardinal) :=
    le_of_eq (Cardinal.cast_toNat_of_lt_aleph0 hR).symm
  exact (rank_adjoint_le_natCast_of_rank_le R hle).trans_lt Cardinal.natCast_lt_aleph0

/-- One half of adjoint invariance for approximation numbers. -/
private theorem approximationNumber_adjoint_le
    (T : E →L[𝕜] F) (n : ℕ) :
    T.adjoint.approximationNumber n ≤ T.approximationNumber n := by
  refine T.le_approximationNumber_iff.mpr ?_
  intro R hR
  calc
    T.adjoint.approximationNumber n ≤ ‖T.adjoint - R.adjoint‖ :=
      T.adjoint.approximationNumber_le_norm_sub
        (rank_adjoint_le_natCast_of_rank_le R hR)
    _ = ‖T - R‖ := by
      simpa only [← map_sub] using
        (ContinuousLinearMap.adjoint.norm_map (T - R))

/-- Approximation numbers of bounded operators between Hilbert spaces are
invariant under adjoint.

Marked `@[simp]` because it eliminates `adjoint` outright: the left-hand side is
strictly larger than the right, so it cannot loop, and `T.adjoint` is never the
normal form when an approximation number is what is being computed. -/
@[simp]
theorem approximationNumber_adjoint (T : E →L[𝕜] F) (n : ℕ) :
    T.adjoint.approximationNumber n = T.approximationNumber n := by
  apply le_antisymm
  · exact approximationNumber_adjoint_le T n
  · simpa only [ContinuousLinearMap.adjoint_adjoint] using
      (approximationNumber_adjoint_le T.adjoint n)

/-- Adjoint invariance as an equality of sequences, which is the form the
compactness transfer below needs: `Tendsto` sees the whole function, not a
pointwise value, so the `@[simp]` lemma above cannot be applied under it. -/
theorem approximationNumber_adjoint_eq (T : E →L[𝕜] F) :
    T.adjoint.approximationNumber = T.approximationNumber :=
  funext fun n => approximationNumber_adjoint T n

/-- **Schauder's theorem for Hilbert spaces: the adjoint of a compact operator is
compact.**

The usual proof is the Arzelà--Ascoli argument on the unit ball of the dual, and
that is what pinned Mathlib lacks for this setting.  Here it is a corollary of
material this directory already has, and the reason it is cheap is worth stating:
compactness on a complete Hilbert target *is* the vanishing of the approximation
numbers (`isCompactOperator_iff_tendsto_approximationNumber`), and the
approximation numbers are adjoint-invariant (`approximationNumber_adjoint`).  So
the two operators have the *same* sequence, not merely comparable ones, and the
transfer is an equality rewrite rather than an estimate.

Recorded downstream as an open obligation -- "Schauder's theorem for
Hilbert-space adjoints, which the pinned Mathlib does not yet provide" --
blocking the adjoint-invariance field of the compact-operator ideal family;
`TauCeti.compactOperatorFamily` is what that obligation became. -/
theorem isCompactOperator_adjoint {T : E →L[𝕜] F} (hT : IsCompactOperator T) :
    IsCompactOperator T.adjoint := by
  rw [isCompactOperator_iff_tendsto_approximationNumber, approximationNumber_adjoint_eq]
  exact (isCompactOperator_iff_tendsto_approximationNumber T).1 hT

/-- Schauder's theorem in both directions.  `T.adjoint.adjoint = T` makes the
converse immediate, so the equivalence costs nothing beyond the statement. -/
@[simp]
theorem isCompactOperator_adjoint_iff {T : E →L[𝕜] F} :
    IsCompactOperator T.adjoint ↔ IsCompactOperator T :=
  ⟨fun h => by
      simpa only [ContinuousLinearMap.adjoint_adjoint] using isCompactOperator_adjoint h,
    isCompactOperator_adjoint⟩

end ContinuousLinearMap

end

end
