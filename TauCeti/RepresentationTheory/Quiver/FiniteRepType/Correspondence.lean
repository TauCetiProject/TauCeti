/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.PosDef
public import TauCeti.RepresentationTheory.Quiver.Reflection.Existence

/-!
# The Gabriel correspondence for positive definite quivers

For a finite quiver with positive definite Tits form, the dimension vector gives a bijection
between the isomorphism classes of finite-dimensional indecomposable representations and the
nonnegative integral vectors of Tits norm one.

The injective half is `TauCeti.isoClassDimVectorEmbedding`: an indecomposable is determined up to
isomorphism by its dimension vector. The surjective half is
`TauCeti.exists_indecomposable_dimVector_eq`: every positive root is realized by an
indecomposable. This file assembles the two halves into an equivalence, and therefore identifies
the number of indecomposable isomorphism classes with the number of positive roots.

No algebraic-closedness hypothesis is needed: the reflection-functor construction works over an
arbitrary field.

## Main definitions

* `TauCeti.gabrielIndecomposableEquivPositiveRoot`: the Gabriel correspondence for a quiver with
  positive definite Tits form.

## Main results

* `TauCeti.coe_gabrielIndecomposableEquivPositiveRoot_apply` and
  `TauCeti.isoClassDimVector_gabrielIndecomposableEquivPositiveRoot_symm_apply`: both directions of
  the correspondence are computed by the dimension vector.
* `TauCeti.card_skeleton_indecomposable_eq_card_positiveRoots`: the two sides of the
  correspondence have the same cardinality.

## References

* I. N. Bernstein, I. M. Gelfand, V. A. Ponomarev, *Coxeter functors and Gabriel's theorem*.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Volume I, Chapter VII.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w x

variable {k : Type u} {V : Type v} [Field k] [Quiver.{w} V]
  [Fintype V] [∀ a b : V, Fintype (a ⟶ b)]

/-- **The dimension-vector embedding is onto the positive roots.** Every nonnegative integral
vector of Tits norm one is realized by a finite-dimensional indecomposable representation, whose
class maps back to that vector. -/
theorem isoClassDimVectorEmbedding_surjective (hpd : (titsForm V).PosDef) :
    Function.Surjective
      (isoClassDimVectorEmbedding.{u, v, w, max u x} (k := k) hpd) := by
  rintro ⟨d, hd, hroot⟩
  obtain ⟨M, hM, hfd, hdim⟩ :=
    exists_indecomposable_dimVector_eq k V hpd hd hroot
  let X : Skeleton (ObjectProperty.FullSubcategory
      (fun N : QuiverRep.{u, v, w, max u v w x} k V ↦
        IsFinDim k V N ∧ Indecomposable N)) :=
    toSkeleton ⟨M, hfd, hM⟩
  refine ⟨X, Subtype.ext ?_⟩
  rw [coe_isoClassDimVectorEmbedding_apply, isoClassDimVector_toSkeleton M
    (isFinDim_iff.mp hfd) hM, hdim]

/-- **Gabriel's correspondence for a positive definite quiver.** The dimension vector is an
equivalence from the isomorphism classes of finite-dimensional indecomposable representations to
the nonnegative integral vectors of Tits norm one. -/
noncomputable def gabrielIndecomposableEquivPositiveRoot (hpd : (titsForm V).PosDef) :
    Skeleton (ObjectProperty.FullSubcategory
        (fun M : QuiverRep.{u, v, w, max u v w x} k V ↦
          IsFinDim k V M ∧ Indecomposable M)) ≃
      {d : V → ℤ // 0 ≤ d ∧ titsForm V d = 1} :=
  (isoClassDimVectorEmbedding hpd).equivOfSurjective
    (isoClassDimVectorEmbedding_surjective hpd)

/-- Gabriel's correspondence sends an indecomposable class to its dimension vector. -/
@[simp]
theorem coe_gabrielIndecomposableEquivPositiveRoot_apply (hpd : (titsForm V).PosDef)
    (X : Skeleton (ObjectProperty.FullSubcategory
      (fun M : QuiverRep.{u, v, w, max u v w x} k V ↦
        IsFinDim k V M ∧ Indecomposable M))) :
    ((gabrielIndecomposableEquivPositiveRoot.{u, v, w, x} (k := k) hpd X :
      {d : V → ℤ // 0 ≤ d ∧ titsForm V d = 1}) : V → ℤ) =
        isoClassDimVector.{u, v, w, max u x} X :=
  coe_isoClassDimVectorEmbedding_apply.{u, v, w, max u x} hpd X

/-- The class that Gabriel's correspondence assigns to a positive root has that root as its
dimension vector. -/
@[simp]
theorem isoClassDimVector_gabrielIndecomposableEquivPositiveRoot_symm_apply
    (hpd : (titsForm V).PosDef) (d : {d : V → ℤ // 0 ≤ d ∧ titsForm V d = 1}) :
    isoClassDimVector.{u, v, w, max u x}
        ((gabrielIndecomposableEquivPositiveRoot.{u, v, w, x} (k := k) hpd).symm d) =
      (d : V → ℤ) := by
  rw [← coe_gabrielIndecomposableEquivPositiveRoot_apply hpd, Equiv.apply_symm_apply]

/-- **A positive definite quiver has as many indecomposable isomorphism classes as positive
roots.** -/
theorem card_skeleton_indecomposable_eq_card_positiveRoots (hpd : (titsForm V).PosDef) :
    Nat.card (Skeleton (ObjectProperty.FullSubcategory
        (fun M : QuiverRep.{u, v, w, max u v w x} k V ↦
          IsFinDim k V M ∧ Indecomposable M))) =
      Nat.card {d : V → ℤ // 0 ≤ d ∧ titsForm V d = 1} :=
  Nat.card_congr (gabrielIndecomposableEquivPositiveRoot hpd)

end TauCeti
