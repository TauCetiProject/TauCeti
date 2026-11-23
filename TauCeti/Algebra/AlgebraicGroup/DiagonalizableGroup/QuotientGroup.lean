/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.EssentialImage
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Quotient
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Central.Basic
import TauCeti.Algebra.Coalgebra.Comodule.Weight.Regular

/-!
# Quotient groups of diagonalizable affine groups

A finite-type commutative Hopf algebra over a field is the coordinate algebra of a
diagonalizable group exactly when its group-like elements span it. This condition is reflected
by injective morphisms: a Hopf algebra that embeds in a group algebra is a subcoalgebra of it,
hence is spanned by the group-like elements it contains.

Contravariantly, an injective coordinate morphism `O(Q) → O(G)` presents `Q` as a quotient group
of `G`, so the main result is the coordinate-algebra form of the fact that every quotient group
of a diagonalizable affine group is diagonalizable. It applies in particular to the quotient
`G ⧸ N` by a closed subgroup, whose coordinate algebra is the Hopf subalgebra of coinvariants.
Every closed subgroup `N` is normal, since `G` is commutative
(`TauCeti.HopfIdeal.isNormal_of_groupLikeSetSpan_eq_top`), and the functions on `G` invariant
under `N` are spanned by the characters of `G` that are trivial on `N`
(`TauCeti.HopfIdeal.toSubmodule_coinvariants_eq_span_groupLike`).

The group `G` need not be reduced, so the finite generation of the coinvariants is part of the
statement: it comes from the group-like elements, not from the general quotient theory of
geometrically reduced groups.

## Main declarations

* `TauCeti.DiagonalizableGroup.groupLikeSpannedProperty.of_injective`: an injective morphism of
  finite-type commutative Hopf algebras reflects the diagonalizable coordinate property.
* `TauCeti.DiagonalizableGroup.groupLikeSpannedProperty.finiteType_coinvariants`: the
  coinvariants of a Hopf ideal in a diagonalizable coordinate algebra are of finite type.
* `TauCeti.DiagonalizableGroup.groupLikeSpannedProperty.coinvariants`: the quotient of a
  diagonalizable group by a closed subgroup is diagonalizable.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.9(c).
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace DiagonalizableGroup.groupLikeSpannedProperty

variable (k : Type u) [Field k]

/-- An injective morphism of finite-type commutative Hopf algebras reflects spanning by
group-like elements. Contravariantly, this is closure of diagonalizable affine groups under
quotient groups presented by an injective coordinate morphism. -/
theorem of_injective (H K : FiniteTypeCommHopfAlgCat.{u, u} k) (f : H ⟶ K)
    (hf : Function.Injective (FiniteTypeCommHopfAlgCat.toBialgHom f))
    (hK : DiagonalizableGroup.groupLikeSpannedProperty k K) :
    DiagonalizableGroup.groupLikeSpannedProperty k H := by
  rw [DiagonalizableGroup.groupLikeSpannedProperty_iff] at hK ⊢
  exact CoalgHom.groupLikeSetSpan_eq_top_of_injective
    (FiniteTypeCommHopfAlgCat.toBialgHom f).toCoalgHom hf hK

variable {k} {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- The coinvariants of a Hopf ideal in a finite-type commutative Hopf algebra spanned by its
group-like elements are finitely generated as an algebra. The Hopf algebra need not be reduced. -/
theorem finiteType_coinvariants (hH : DiagonalizableGroup.groupLikeSpannedProperty k H)
    (I : HopfIdeal k H) : Algebra.FiniteType k I.coinvariants :=
  have hH' := (DiagonalizableGroup.groupLikeSpannedProperty_iff k H).mp hH
  have hI := HopfIdeal.isNormal_of_groupLikeSetSpan_eq_top hH' I
  letI : HopfAlgebra k I.coinvariants := hI.isHopfSubalgebra_coinvariants.hopfAlgebra
  (CommHopfAlgCat.coinvariantsι hI).hom.finiteType_of_injective_of_groupLikeSetSpan_eq_top
    (CommHopfAlgCat.hopfSubalgebraι_injective hI.isHopfSubalgebra_coinvariants) hH'

/-- **Quotient groups of diagonalizable groups are diagonalizable.** The coinvariants of a Hopf
ideal in a finite-type commutative Hopf algebra spanned by its group-like elements are again
spanned by their group-like elements. Contravariantly, the quotient `G ⧸ N` of a diagonalizable
affine group by a closed subgroup is diagonalizable. Every Hopf ideal `I` is normal here, by
`TauCeti.HopfIdeal.isNormal_of_groupLikeSetSpan_eq_top`; the statement holds for any proof `hI`
of that fact. -/
theorem coinvariants (hH : DiagonalizableGroup.groupLikeSpannedProperty k H)
    {I : HopfIdeal k H} (hI : I.IsNormal) :
    DiagonalizableGroup.groupLikeSpannedProperty k
      ⟨CommHopfAlgCat.coinvariants hI,
        (finiteTypeCommHopfAlgProperty_iff _).mpr (finiteType_coinvariants hH I)⟩ :=
  of_injective k _ H (ObjectProperty.homMk (CommHopfAlgCat.coinvariantsι hI))
    (CommHopfAlgCat.hopfSubalgebraι_injective hI.isHopfSubalgebra_coinvariants) hH

end DiagonalizableGroup.groupLikeSpannedProperty

end TauCeti
