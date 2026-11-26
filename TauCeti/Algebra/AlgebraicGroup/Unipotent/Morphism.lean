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

A character of `G` is a group-like element of `H`, and a nontrivial one excludes unipotence
(`TauCeti.not_unipotentCommHopfAlgProperty_of_isGroupLikeElem`), so **a unipotent group has no
nontrivial characters** (`TauCeti.unipotentCommHopfAlgProperty.eq_one_of_isGroupLikeElem`). A
homomorphism `G → D` to a diagonalizable group, whose coordinate Hopf algebra `A` is spanned by its
group-like elements, is given by a morphism `A → H` of bialgebras; it sends each group-like element
to a character of `G`, hence to `1`. So **every homomorphism from a unipotent group to a
diagonalizable group is trivial**: the bialgebra morphism is the counit
(`TauCeti.unipotentCommHopfAlgProperty.apply_eq_algebraMap_counit`; Milne, Corollary 14.18, for
diagonalizable targets).

## Main declarations

* `TauCeti.unipotentCommHopfAlgProperty.of_injective`: a quotient of a unipotent group is
  unipotent.
* `TauCeti.unipotentCommHopfAlgProperty.eq_one_of_isGroupLikeElem`: the only character of a
  unipotent group is trivial.
* `TauCeti.unipotentCommHopfAlgProperty.apply_eq_algebraMap_counit` and
  `TauCeti.unipotentCommHopfAlgProperty.apply_eq_algebraMap_counit_of_groupLikeSetSpan_eq_top`:
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
Hopf algebras, representing a quotient of the group of `H`, and `H` is unipotent, then so is `A`:
corestrict an `A`-comodule along `f`, take a vector fixed by `H`, and cancel `id ⊗ f`, injective
over a field. -/
theorem of_injective {A : Type w} [CommRing A] [HopfAlgebra k A] (f : A →ₐc[k] H)
    (hf : Function.Injective f) : unipotentCommHopfAlgProperty k (CommHopfAlgCat.of k A) := by
  refine (unipotentCommHopfAlgProperty_iff k _).mpr fun M _ _ _ _ _ ↦ ?_
  let _ : Comodule k H M := Corestrict (f : A →ₐc[k] H).toCoalgHom
  obtain ⟨v, hv, hvc⟩ :=
    hasNonzeroFixedVector_iff.mp ((unipotentCommHopfAlgProperty_iff k _).mp hH M)
  refine hasNonzeroFixedVector_iff.mpr ⟨v, hv, ?_⟩
  have hinj : Function.Injective ((f : A →ₐc[k] H).toCoalgHom.toLinearMap.lTensor M) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hf
  apply hinj
  rw [← LinearMap.comp_apply, ← corestrictCoact_eq_lTensor, LinearMap.lTensor_tmul]
  exact hvc.trans (congrArg (v ⊗ₜ[k] ·) (map_one f).symm)

/-- **A unipotent group has no nontrivial characters**: its only group-like element is `1`. -/
theorem eq_one_of_isGroupLikeElem {c : H} (hc : IsGroupLikeElem k c) : c = 1 :=
  not_not.mp fun hc1 ↦ not_unipotentCommHopfAlgProperty_of_isGroupLikeElem hc hc1 hH

/-- **Every homomorphism from a unipotent group to a diagonalizable group is trivial.** If the
Hopf algebra `A` is spanned by its group-like elements and `H` is unipotent, then every morphism
of bialgebras `f : A → H` is the counit of `A`: it sends each group-like element of `A` to a
group-like element of `H`, which is `1`. -/
theorem apply_eq_algebraMap_counit {A : Type w} [CommRing A] [HopfAlgebra k A]
    (hA : Submodule.span k {a : A | IsGroupLikeElem k a} = ⊤) (f : A →ₐc[k] H) (a : A) :
    f a = algebraMap k H (Coalgebra.counit a) := by
  have ha : a ∈ Submodule.span k {a : A | IsGroupLikeElem k a} := hA ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem x hx => rw [eq_one_of_isGroupLikeElem hH (hx.map f), hx.counit_eq_one, map_one]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul r x _ hx => rw [map_smul, hx, map_smul, smul_eq_mul, map_mul, Algebra.smul_def]

/-- **Every homomorphism from a unipotent group to a diagonalizable group is trivial**, for the
diagonalizability condition of `TauCeti.DiagonalizableGroup.groupLikeSpannedProperty`: the
subcoalgebra spanned by all group-like elements of `A` is everything. -/
theorem apply_eq_algebraMap_counit_of_groupLikeSetSpan_eq_top {A : Type w} [CommRing A]
    [HopfAlgebra k A] (hA : Subcoalgebra.groupLikeSetSpan (R := k) (C := A) Set.univ = ⊤)
    (f : A →ₐc[k] H) (a : A) : f a = algebraMap k H (Coalgebra.counit a) := by
  refine apply_eq_algebraMap_counit hH (eq_top_iff.mpr fun x _ ↦ ?_) f a
  have hx : x ∈ Subcoalgebra.groupLikeSetSpan (R := k) (C := A) Set.univ := hA ▸ trivial
  rw [Subcoalgebra.mem_groupLikeSetSpan] at hx
  refine Submodule.span_mono ?_ hx
  rintro _ ⟨g, -, rfl⟩
  exact g.isGroupLikeElem_val

end unipotentCommHopfAlgProperty

end TauCeti
