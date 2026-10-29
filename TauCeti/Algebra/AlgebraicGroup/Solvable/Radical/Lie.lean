/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Basic
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Tangent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Zero
public import Mathlib.Algebra.Lie.Semisimple.Defs

/-!
# The Lie algebra of a solvable-radical candidate

The tangent Lie ideal of a smooth geometrically connected solvable normal closed subgroup
lies in the solvable radical of the ambient Lie algebra. This applies in particular to the
group's solvable radical, using
`FiniteTypeCommHopfAlgCat.isSolvableRadicalCandidate_solvableRadicalDefiningIdeal`.

Normality makes the tangent image an ideal. Its solvability follows from
`geometricallySolvablePointsCommHopfAlgProperty.isSolvable_lieAlgebra`, and the universal
property of the Lie radical gives the containment. No characteristic assumption or
smoothness of the ambient group is needed. If the ambient Lie radical vanishes, every such
subgroup is trivial: its Lie algebra is zero and its coordinate algebra is connected.
Equality with the Lie radical is not asserted.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 16.
-/

public section

namespace TauCeti.HopfIdeal.IsSolvableRadicalCandidate

universe u

/-- The tangent Lie ideal of a connected smooth solvable normal closed subgroup is contained
in the radical of the ambient tangent Lie algebra, in every characteristic. -/
theorem lieIdeal_le_radical {k : Type u} [Field k]
    {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H}
    (hI : IsSolvableRadicalCandidate H I) :
    hI.isNormal.lieIdeal (B := k) ≤
      LieAlgebra.radical k (Derivation k H (Bialgebra.CounitAlgebra k H k)) := by
  let Q := FiniteTypeCommHopfAlgCat.quotient H I
  let _ : Algebra.Smooth k Q := hI.smooth
  let _ : Algebra.IsGeometricallyReduced k Q := isGeometricallyReduced_of_smooth k Q
  have hQ := hI.geometricallySolvable.isSolvable_lieAlgebra hI.geometricallyConnected
  have hsub : LieAlgebra.IsSolvable
      (LieIdeal.toLieSubalgebra k _ (hI.isNormal.lieIdeal (B := k))) := by
    rw [hI.isNormal.lieIdeal_toLieSubalgebra]
    exact (LieAlgebra.solvable_iff_equiv_solvable (I.quotientLieEquiv (B := k))).mp hQ
  exact (LieAlgebra.LieIdeal.solvable_iff_le_radical k _ _).mp hsub

/-- A connected smooth solvable normal closed subgroup is trivial if the ambient Lie algebra
has trivial solvable radical. The ambient group need not be smooth or connected, and the
field may have any characteristic. -/
theorem eq_augmentation_of_hasTrivialRadical {k : Type u} [Field k]
    {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H}
    (hI : IsSolvableRadicalCandidate H I)
    [LieAlgebra.HasTrivialRadical k
      (Derivation k H (Bialgebra.CounitAlgebra k H k))] :
    I = augmentation k H := by
  have hlie : I.lieSubalgebra (B := k) = ⊥ := by
    have hle := hI.lieIdeal_le_radical
    rw [LieAlgebra.radical_eq_bot] at hle
    have heq := le_bot_iff.mp hle
    rw [← hI.isNormal.lieIdeal_toLieSubalgebra, heq]
    rfl
  have hdim : Module.finrank k
      (Derivation k (H ⧸ I.toIdeal) (Bialgebra.CounitAlgebra k (H ⧸ I.toIdeal) k)) = 0 := by
    rw [(I.quotientLieEquiv (B := k)).toLinearEquiv.finrank_eq, hlie]
    let _ : Subsingleton (⊥ : LieSubalgebra k
      (Derivation k H (Bialgebra.CounitAlgebra k H k))) := LieSubalgebra.subsingleton_bot
    exact Module.finrank_zero_of_subsingleton
  have hbot := hI.geometricallyConnected.augmentation_eq_bot_of_finrank_lie_eq_zero hdim
  have h := comapOfSurjective_augmentation
    (Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal)
    (Bialgebra.Quotient.mkBialgHom_surjective I.toIdeal)
  rw [hbot, comapOfSurjective_bot, kerOfSurjective_mkBialgHom] at h
  exact h

end TauCeti.HopfIdeal.IsSolvableRadicalCandidate
