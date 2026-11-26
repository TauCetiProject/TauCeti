/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Comodule
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.GroupLike

/-!
# Quotients of unipotent groups and homomorphisms to diagonalizable groups

Let `H` be the coordinate Hopf algebra of a unipotent affine group `G` over a field `k`, in the
comodule sense `TauCeti.unipotentCommHopfAlgProperty`: every nonzero finite-dimensional
representation has a nonzero fixed vector.

A quotient `G → Q` is represented by an injective morphism of Hopf algebras `k[Q] → k[G]`. A
representation of `Q` is a representation of `G` by corestricting the coaction, and a vector fixed
by `G` is fixed by `Q`, since tensoring with `M` over a field preserves the injectivity of
`k[Q] → k[G]`. So **quotients of unipotent groups are unipotent**
(`TauCeti.unipotentCommHopfAlgProperty.of_injective`; Milne, Corollary 14.7).

A character of `G` is a group-like element of `H`, and a nontrivial one excludes unipotence, so
the only character of a unipotent group is trivial
(`TauCeti.unipotentCommHopfAlgProperty.eq_one_of_isGroupLikeElem`). A homomorphism `G → D` to a
diagonalizable group, whose coordinate Hopf algebra `A` is spanned by its group-like elements, is
given by a morphism `A → H` of bialgebras; it sends each group-like element to a character of `G`,
hence to `1`. So **every homomorphism from a unipotent group to a diagonalizable group is
trivial**: the morphism is `algebraMap k H ∘ counit`
(`TauCeti.unipotentCommHopfAlgProperty.apply_eq_algebraMap_counit_of_groupLikeSetSpan_eq_top`;
Milne, Corollary 14.18, for diagonalizable targets). This only uses that `A` is a coalgebra and
that the morphism preserves the coalgebra structure.

## Main declarations

* `TauCeti.unipotentCommHopfAlgProperty.of_injective`: a quotient of a unipotent group is
  unipotent.
* `TauCeti.unipotentCommHopfAlgProperty.apply_eq_algebraMap_counit_of_groupLikeSetSpan_eq_top`:
  homomorphisms from a unipotent group to a diagonalizable group are trivial.

## References

* J. S. Milne, *Algebraic Groups* (2017), Corollary 14.7, p. 282, and Corollary 14.18, p. 284.
-/

public section

open scoped TensorProduct

namespace TauCeti

open Comodule

universe u v w

variable {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H]

namespace unipotentCommHopfAlgProperty

variable (hH : unipotentCommHopfAlgProperty k (CommHopfAlgCat.of k H))
include hH

/-- **A quotient of a unipotent group is unipotent.** If `f : A → H` is an injective morphism of
Hopf algebras, representing a quotient of the group of `H`, and `H` is unipotent, then so is
`A`. -/
theorem of_injective {A : Type w} [CommRing A] [HopfAlgebra k A] (f : A →ₐc[k] H)
    (hf : Function.Injective f) : unipotentCommHopfAlgProperty k (CommHopfAlgCat.of k A) := by
  refine (unipotentCommHopfAlgProperty_iff k _).mpr fun M _ _ _ _ _ ↦ ?_
  let _ : Comodule k H M := Corestrict (f : A →ₐc[k] H).toCoalgHom
  obtain ⟨v, hv, hvc⟩ :=
    hasNonzeroFixedVector_iff.mp ((unipotentCommHopfAlgProperty_iff k _).mp hH M)
  rw [corestrict_coact_apply] at hvc
  refine hasNonzeroFixedVector_iff.mpr ⟨v, hv, ?_⟩
  have hinj : Function.Injective ((f : A →ₐc[k] H).toCoalgHom.toLinearMap.lTensor M) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hf
  apply hinj
  rw [LinearMap.lTensor_def, hvc]
  simp [BialgHom.toCoalgHom_apply]

/-- **Every homomorphism from a unipotent group to a diagonalizable group is trivial.** If the
coalgebra `A` is spanned by its group-like elements, in the sense of
`TauCeti.DiagonalizableGroup.groupLikeSpannedProperty`, and `H` is unipotent, then every coalgebra
morphism `f : A → H`, in particular every bialgebra morphism, is `algebraMap k H ∘ counit`. -/
theorem apply_eq_algebraMap_counit_of_groupLikeSetSpan_eq_top {A : Type w} [AddCommGroup A]
    [Module k A] [Coalgebra k A] (hA : Subcoalgebra.groupLikeSetSpan (R := k) (C := A) Set.univ = ⊤)
    {F : Type*} [FunLike F A H] [CoalgHomClass F k A H] (f : F) (a : A) :
    f a = algebraMap k H (Coalgebra.counit a) :=
  LinearMap.congr_fun ((Subcoalgebra.groupLikeBasis hA).ext (f₁ := (f : A →ₗ[k] H))
    (f₂ := (Algebra.linearMap k H).comp Coalgebra.counit) fun g ↦ by
      simp [Subcoalgebra.groupLikeBasis_apply, hH.eq_one_of_isGroupLikeElem
        (g.isGroupLikeElem_val.map f), g.isGroupLikeElem_val.counit_eq_one]) a

end unipotentCommHopfAlgProperty

end TauCeti
