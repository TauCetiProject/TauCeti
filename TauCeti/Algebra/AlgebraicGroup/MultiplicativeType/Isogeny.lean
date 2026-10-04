/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.GroupLike.Isogeny
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Descent
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterLattice.Functoriality

/-!
# Geometric character criterion for isogenies of multiplicative-type groups

On the geometric fibre of a group of multiplicative type, the coordinate Hopf algebra is
spanned by its group-like elements. Thus a morphism of two such groups is a central
isogeny exactly when its map on geometric characters is injective with finite cokernel.
Field-extension descent detects the isogeny over the original field. This applies over an
arbitrary ground field and includes nonsmooth groups.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.9.
-/

public section

namespace TauCeti.multiplicativeTypeCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] {H K : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- A morphism of multiplicative-type groups is a central isogeny
exactly when the induced geometric character map is injective with finite cokernel. -/
theorem isCentralIsogeny_iff_geometricCharacterMap_injective_and_finite_quotient
    (hH : multiplicativeTypeCommHopfAlgProperty k H)
    (hK : multiplicativeTypeCommHopfAlgProperty k K) (f : H.obj ⟶ K.obj) :
    CommHopfAlgCat.IsCentralIsogeny f ↔
      Function.Injective (CommHopfAlgCat.geometricCharacterMap f) ∧
        Finite (CommHopfAlgCat.geometricCharacterGroup K.obj ⧸
          (CommHopfAlgCat.geometricCharacterMap f).range) := by
  rw [← CommHopfAlgCat.isCentralIsogeny_baseChangeMap_iff (L := AlgebraicClosure k) f]
  simpa only [CommHopfAlgCat.geometricCharacterMap_eq_groupLikeMap] using
    (DiagonalizableGroup.isCentralIsogeny_iff_groupLikeMap_injective_and_finite_quotient
    ((Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top).mp
      ((DiagonalizableGroup.groupLikeSpannedProperty_iff _ _).mp
        ((multiplicativeTypeCommHopfAlgProperty_iff k H).mp hH)))
    ((Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top).mp
      ((DiagonalizableGroup.groupLikeSpannedProperty_iff _ _).mp
        ((multiplicativeTypeCommHopfAlgProperty_iff k K).mp hK)))
    (CommHopfAlgCat.baseChangeMap (K := AlgebraicClosure k) f))

end TauCeti.multiplicativeTypeCommHopfAlgProperty
