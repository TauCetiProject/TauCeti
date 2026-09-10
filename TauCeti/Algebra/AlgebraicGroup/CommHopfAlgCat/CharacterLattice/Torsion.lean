/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterLattice.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Torsion
public import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
public import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation

/-!
# The characters of a connected affine group are torsion free

A character of an affine group `Spec H` is a group-like element of its coordinate Hopf algebra
`H`. This file proves that when `H` is reduced with connected prime spectrum, no character has
finite order. It also gives the corresponding result for smooth geometrically connected affine
groups of finite type.

The argument is a reduction to the diagonalizable case. Group-like elements of a Hopf algebra over
a field are linearly independent, so evaluation embeds the group algebra on them into `H`. A
subring of a reduced ring is reduced, and connectedness of a prime spectrum descends along an
injective ring homomorphism, so both hypotheses pass to that group algebra, where
`TauCeti.isMulTorsionFree_of_isReduced_monoidAlgebra_of_connectedSpace` already rules out torsion.

Neither hypothesis can be dropped. Connectedness alone fails in characteristic `p`, where the
coordinate Hopf algebra of `μ_p` is connected, non-reduced, and carries a character of order `p`.
Reducedness alone fails for the constant group `ℤ/n` over a field containing a primitive `n`-th
root of unity: its coordinate algebra is reduced but disconnected, and it has characters of
order `n`.

Contravariantly, a homomorphism from `Spec H` to the diagonalizable group `D(M)` is a morphism of
coordinate bialgebras `k[M] ⟶ H`. Torsion-freeness therefore says that a smooth connected affine
group admits no nontrivial homomorphism to a diagonalizable group on a torsion group, so in
particular no nontrivial `μ_n`-quotient.

## Main declarations

* `TauCeti.isMulTorsionFree_groupLike_of_isReduced_of_connectedSpace`: **the characters of a
  reduced affine group with connected coordinate spectrum form a torsion-free group.**
* `TauCeti.eq_one_of_isGroupLikeElem_of_pow_eq_one`: the elementwise form.
* `TauCeti.monoidAlgebra_bialgHom_single_eq_one` and
  `TauCeti.monoidAlgebra_bialgHom_eq_algebraMap_counit`: a homomorphism to a diagonalizable group
  on a torsion group is trivial.
* `TauCeti.isMulTorsionFree_geometricCharacterGroup` and
  `TauCeti.isMulTorsionFree_geometricCharacterGroup_of_smooth`: **the character lattice of a
  smooth geometrically connected affine group of finite type is torsion free.**
* `TauCeti.isAddTorsionFree_additiveCharacterGroup` and
  `TauCeti.isAddTorsionFree_additiveCharacterGroup_of_smooth`: their additive forms.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
* T. A. Springer, *Linear Algebraic Groups*, Theorem 6.3.1.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

section Absolute

variable (k : Type u) [Field k] (H : Type v) [CommRing H] [HopfAlgebra k H]

/-- **The characters of a reduced affine group with connected coordinate spectrum form a
torsion-free group.** -/
theorem isMulTorsionFree_groupLike_of_isReduced_of_connectedSpace
    [IsReduced H] [ConnectedSpace (PrimeSpectrum H)] :
    IsMulTorsionFree (GroupLike k H) := by
  -- Group-like elements over a field are linearly independent, so evaluation embeds the group
  -- algebra on them into `H`, and both hypotheses are inherited by a subring.
  have hf : Function.Injective
      ((GroupLike.evaluationBialgHom k H).toAlgHom.toRingHom :
        MonoidAlgebra k (GroupLike k H) →+* H) :=
    GroupLike.evaluationBialgHom_injective k H
  have _ : IsReduced (MonoidAlgebra k (GroupLike k H)) := isReduced_of_injective _ hf
  have _ : ConnectedSpace (PrimeSpectrum (MonoidAlgebra k (GroupLike k H))) :=
    connectedSpace_primeSpectrum_of_injective _ hf
  exact isMulTorsionFree_of_isReduced_monoidAlgebra_of_connectedSpace k (GroupLike k H)

variable {k H}

/-- A character of finite order of a reduced affine group with connected coordinate spectrum is
trivial. -/
theorem eq_one_of_isGroupLikeElem_of_pow_eq_one
    [IsReduced H] [ConnectedSpace (PrimeSpectrum H)] {a : H} (ha : IsGroupLikeElem k a)
    {n : ℕ} (hn : n ≠ 0) (hpow : a ^ n = 1) : a = 1 := by
  have _ := isMulTorsionFree_groupLike_of_isReduced_of_connectedSpace k H
  have hg : (⟨a, ha⟩ : GroupLike k H) ^ n = 1 := by
    ext
    simpa using hpow
  exact congrArg GroupLike.val ((pow_eq_one_iff.mp hg).resolve_right hn)

/-- **A homomorphism from a reduced connected affine group to a diagonalizable group kills every
torsion character of the target.** Contravariantly, a homomorphism `Spec H ⟶ D(M)` is a morphism
of coordinate bialgebras `k[M] ⟶ H`, and `single m 1` is the coordinate of the character `m` of
`D(M)`. -/
theorem monoidAlgebra_bialgHom_single_eq_one
    [IsReduced H] [ConnectedSpace (PrimeSpectrum H)]
    {M : Type w} [CommGroup M] (f : MonoidAlgebra k M →ₐc[k] H) {m : M} (hm : IsOfFinOrder m) :
    f (MonoidAlgebra.single m 1) = 1 := by
  refine eq_one_of_isGroupLikeElem_of_pow_eq_one
    ((MonoidAlgebra.isGroupLikeElem_single_one m).map f)
    (n := orderOf m) (orderOf_ne_zero_iff.mpr hm) ?_
  rw [← map_pow, MonoidAlgebra.single_pow, one_pow, pow_orderOf_eq_one,
    ← MonoidAlgebra.one_def, map_one]

/-- **A homomorphism from a reduced connected affine group to a diagonalizable group on a torsion
group is trivial**: its coordinate morphism factors through the counit of `k[M]`. -/
theorem monoidAlgebra_bialgHom_eq_algebraMap_counit
    [IsReduced H] [ConnectedSpace (PrimeSpectrum H)]
    {M : Type w} [CommGroup M] (hM : IsMulTorsion M) (f : MonoidAlgebra k M →ₐc[k] H) :
    (f : MonoidAlgebra k M →ₐ[k] H) =
      (Algebra.ofId k H).comp (Bialgebra.counitAlgHom k (MonoidAlgebra k M)) := by
  refine MonoidAlgebra.algHom_ext (fun m ↦ ?_) (Subsingleton.elim _ _)
  rw [AlgHom.comp_apply, BialgHom.coe_toAlgHom, monoidAlgebra_bialgHom_single_eq_one f (hM m)]
  simp [Bialgebra.counitAlgHom, Algebra.ofId]

end Absolute

section Geometric

variable {k : Type u} [Field k] (H : CommHopfAlgCat.{u} k)

/-- **The geometric character group of a geometrically reduced, geometrically connected
commutative Hopf algebra is torsion free.** -/
theorem isMulTorsionFree_geometricCharacterGroup
    (hred : geometricallyReducedCommHopfAlgProperty k H)
    (hconn : geometricallyConnectedCommHopfAlgProperty k H) :
    IsMulTorsionFree (CommHopfAlgCat.geometricCharacterGroup H) := by
  have _ := hred.isReduced_algebraicClosureBaseChange
  have _ := hconn.connectedSpace_algebraicClosureBaseChange
  exact isMulTorsionFree_groupLike_of_isReduced_of_connectedSpace (AlgebraicClosure k)
    (AlgebraicClosure k ⊗[k] (H : Type u))

/-- The additive character group of a geometrically reduced, geometrically connected commutative
Hopf algebra has no additive torsion. -/
theorem isAddTorsionFree_additiveCharacterGroup
    (hred : geometricallyReducedCommHopfAlgProperty k H)
    (hconn : geometricallyConnectedCommHopfAlgProperty k H) :
    IsAddTorsionFree (CommHopfAlgCat.additiveCharacterGroup H) := by
  have _ := isMulTorsionFree_geometricCharacterGroup H hred hconn
  infer_instance

/-- **The character lattice of a smooth geometrically connected affine group of finite type is
torsion free.** Over a field, smoothness of an affine group of finite type is equivalent to
geometric reducedness of its coordinate algebra. -/
theorem isMulTorsionFree_geometricCharacterGroup_of_smooth [Algebra.FiniteType k H]
    (hsmooth : smoothCommHopfAlgProperty k H)
    (hconn : geometricallyConnectedCommHopfAlgProperty k H) :
    IsMulTorsionFree (CommHopfAlgCat.geometricCharacterGroup H) :=
  isMulTorsionFree_geometricCharacterGroup H
    ((smoothCommHopfAlgProperty_iff_geometricallyReduced k H).mp hsmooth) hconn

/-- The additive character lattice of a smooth geometrically connected affine group of finite type
has no additive torsion. -/
theorem isAddTorsionFree_additiveCharacterGroup_of_smooth [Algebra.FiniteType k H]
    (hsmooth : smoothCommHopfAlgProperty k H)
    (hconn : geometricallyConnectedCommHopfAlgProperty k H) :
    IsAddTorsionFree (CommHopfAlgCat.additiveCharacterGroup H) :=
  isAddTorsionFree_additiveCharacterGroup H
    ((smoothCommHopfAlgProperty_iff_geometricallyReduced k H).mp hsmooth) hconn

end Geometric

end TauCeti
