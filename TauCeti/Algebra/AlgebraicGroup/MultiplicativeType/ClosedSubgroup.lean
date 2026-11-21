/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.ClosedSubgroup
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Basic

/-!
# Closed subgroups of groups of multiplicative type

Every closed subgroup of a group of multiplicative type is again of multiplicative type.
On coordinate Hopf algebras, this means that the property passes through a surjective
morphism, in particular to a quotient by any Hopf ideal. This also applies to
scheme-theoretic kernels, without requiring the target group to be of multiplicative type.

The proof extends scalars to an algebraic closure. Surjectivity survives scalar extension,
and the group-like spanning property passes to the resulting quotient. No perfectness,
smoothness, or reducedness assumption is needed.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12.
-/

public section

open CategoryTheory

namespace TauCeti.multiplicativeTypeCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] {H K : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- A surjective coordinate morphism preserves the multiplicative-type property.
Contravariantly, a closed subgroup of a group of multiplicative type is of multiplicative type. -/
theorem of_surjective (hH : multiplicativeTypeCommHopfAlgProperty k H) (f : H ⟶ K)
    (hf : Function.Surjective (FiniteTypeCommHopfAlgCat.toBialgHom f)) :
    multiplicativeTypeCommHopfAlgProperty k K := by
  rw [multiplicativeTypeCommHopfAlgProperty_iff] at hH ⊢
  exact DiagonalizableGroup.groupLikeSpannedProperty.of_surjective
    (AlgebraicClosure k) _ _
    ((FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := AlgebraicClosure k)).map f)
    (CommHopfAlgCat.baseChangeMap_surjective f.hom hf) hH

/-- Every Hopf-ideal quotient of a multiplicative-type coordinate algebra is again of
multiplicative type. This includes the coordinate algebras of its closed subgroup schemes. -/
theorem quotient (hH : multiplicativeTypeCommHopfAlgProperty k H) (I : HopfIdeal k H) :
    multiplicativeTypeCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient H I) :=
  hH.of_surjective (FiniteTypeCommHopfAlgCat.mkQuotient H I)
    (CommHopfAlgCat.mkQuotient_surjective H.obj I)

end TauCeti.multiplicativeTypeCommHopfAlgProperty
