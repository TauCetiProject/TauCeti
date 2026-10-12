/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.CharacterLattice
public import TauCeti.Algebra.HopfAlgebra.GroupLike.FiniteExtension

/-!
# Finite algebraic splitting fields for groups of multiplicative type

Every finite-type affine group of multiplicative type becomes diagonalizable over a finite
intermediate field of an algebraic closure. This is a field of definition for all of its geometric
characters, obtained from finitely many character generators. The result does not assert that
the extension is separable, and requires neither perfectness nor smoothness.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12.
-/

public section

namespace TauCeti.multiplicativeTypeCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- Every finite-type group of multiplicative type is diagonalizable over a finite algebraic
extension. -/
theorem exists_finiteDimensional_groupLikeSpanned_baseChange
    (hH : multiplicativeTypeCommHopfAlgProperty k H) :
    ∃ L : IntermediateField k (AlgebraicClosure k), FiniteDimensional k L ∧
      DiagonalizableGroup.groupLikeSpannedProperty L
        (FiniteTypeCommHopfAlgCat.baseChange (K := L) H) := by
  let _ := CommHopfAlgCat.geometricCharacterGroup_fg_of_multiplicativeType H hH
  have hspan := (Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top
    (R := AlgebraicClosure k)
    (C := CommHopfAlgCat.baseChange (K := AlgebraicClosure k) H.obj)).mp
      ((DiagonalizableGroup.groupLikeSpannedProperty_iff _ _).mp
        ((multiplicativeTypeCommHopfAlgProperty_iff k H).mp hH))
  obtain ⟨L, hL, hspanL⟩ := exists_finiteDimensional_span_groupLike_eq_top hspan
  refine ⟨L, hL, (DiagonalizableGroup.groupLikeSpannedProperty_iff _ _).mpr ?_⟩
  exact Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top.mpr hspanL

end TauCeti.multiplicativeTypeCommHopfAlgProperty
