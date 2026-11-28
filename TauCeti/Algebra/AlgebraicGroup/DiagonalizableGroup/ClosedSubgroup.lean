/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.EssentialImage
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.Bialgebra.GroupLike.Map
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Kernel
import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation

/-!
# Closed subgroups of diagonalizable affine groups

A finite-type commutative Hopf algebra over a field is the coordinate algebra of a
diagonalizable group exactly when its group-like elements span it. This condition passes to a
Hopf quotient: the quotient morphism is surjective and sends every group-like element to a
group-like element, so the images of the original spanning family span the quotient.

Contravariantly, a Hopf ideal cuts out a closed subgroup of the represented affine group. Thus
the main result is the coordinate-algebra form of the fact that every closed subgroup of a
diagonalizable affine group is diagonalizable.

## Main declarations

* `TauCeti.DiagonalizableGroup.groupLikeSpannedProperty.of_surjective`: a surjective morphism of
  finite-type commutative Hopf algebras preserves the diagonalizable coordinate property.
* `TauCeti.DiagonalizableGroup.groupLikeSpannedProperty.quotient`: every Hopf quotient of a
  diagonalizable coordinate algebra is again diagonalizable.
* `TauCeti.DiagonalizableGroup.groupLikeSpannedProperty.exists_kerOfSurjective_eq`: a closed
  subgroup with diagonalizable coordinate algebra is cut out by the kernel of a surjective
  coordinate map onto a group algebra.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.9.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace DiagonalizableGroup.groupLikeSpannedProperty

variable (k : Type u) [Field k]

/-- A surjective morphism of finite-type commutative Hopf algebras preserves spanning by
group-like elements. Contravariantly, this is closure of diagonalizable affine groups under
closed subgroups presented by a surjective coordinate morphism. -/
theorem of_surjective (H K : FiniteTypeCommHopfAlgCat.{u, u} k) (f : H ⟶ K)
    (hf : Function.Surjective (FiniteTypeCommHopfAlgCat.toBialgHom f))
    (hH : DiagonalizableGroup.groupLikeSpannedProperty k H) :
    DiagonalizableGroup.groupLikeSpannedProperty k K := by
  rw [DiagonalizableGroup.groupLikeSpannedProperty_iff] at hH ⊢
  exact CoalgHom.groupLikeSetSpan_eq_top_of_surjective
    (FiniteTypeCommHopfAlgCat.toBialgHom f).toCoalgHom hf hH

/-- Every Hopf quotient of a finite-type diagonalizable coordinate algebra is again a
diagonalizable coordinate algebra. Contravariantly, every closed subgroup cut out by a Hopf ideal
in a diagonalizable affine group is diagonalizable. -/
theorem quotient (H : FiniteTypeCommHopfAlgCat.{u, u} k) (I : HopfIdeal k H)
    (hH : DiagonalizableGroup.groupLikeSpannedProperty k H) :
    DiagonalizableGroup.groupLikeSpannedProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I) := by
  apply of_surjective k H (FiniteTypeCommHopfAlgCat.quotient H I)
    (FiniteTypeCommHopfAlgCat.mkQuotient H I) _ hH
  exact CommHopfAlgCat.mkQuotient_surjective H.obj I

/-- **A diagonalizable closed subgroup is the diagonalizable group of a commutative group.** If
the Hopf ideal `J` cuts out a closed subgroup whose coordinate algebra is spanned by its
group-like elements, then `J` is the kernel of a surjective coordinate map onto the group algebra
`k[X]` of a commutative group `X`, namely the group of group-like elements of the quotient. -/
theorem exists_kerOfSurjective_eq {H : FiniteTypeCommHopfAlgCat.{u, u} k} {J : HopfIdeal k H}
    (hJ : DiagonalizableGroup.groupLikeSpannedProperty k (FiniteTypeCommHopfAlgCat.quotient H J)) :
    ∃ (X : Type u) (_ : CommGroup X) (π : H →ₐc[k] MonoidAlgebra k X)
      (hπ : Function.Surjective π), HopfIdeal.kerOfSurjective π hπ = J := by
  have hspan := (Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top (R := k)
    (C := H ⧸ J.toIdeal)).mp ((DiagonalizableGroup.groupLikeSpannedProperty_iff k _).mp hJ)
  let e := GroupLike.evaluationBialgEquiv k (H ⧸ J.toIdeal) hspan
  let π : H →ₐc[k] MonoidAlgebra k (_root_.GroupLike k (H ⧸ J.toIdeal)) :=
    (e.symm : H ⧸ J.toIdeal →ₐc[k] _).comp (Bialgebra.Quotient.mkBialgHom J.toIdeal)
  have hπ : Function.Surjective π :=
    e.symm.surjective.comp Ideal.Quotient.mk_surjective
  refine ⟨_, inferInstance, π, hπ, HopfIdeal.ext fun x ↦ ?_⟩
  simp [π, Ideal.Quotient.eq_zero_iff_mem]

end DiagonalizableGroup.groupLikeSpannedProperty

end TauCeti
