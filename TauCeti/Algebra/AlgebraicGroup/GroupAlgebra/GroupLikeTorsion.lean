/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Torsion
public import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation

/-!
# Torsion in groups of group-like elements

Group-like elements of a Hopf algebra over a field are linearly independent, so evaluation embeds
their group algebra into the Hopf algebra. Consequently, reducedness and connectedness of the
Hopf algebra pass to this group algebra and force its group of group-like elements to be
torsion-free.

Contravariantly, a bialgebra homomorphism from a group algebra into such a Hopf algebra kills every
torsion element of the indexing group. If the indexing group is torsion, the homomorphism factors
through the counit.

## Main declarations

* `TauCeti.isMulTorsionFree_groupLike_of_isReduced_of_connectedSpace`: group-like elements of a
  reduced Hopf algebra with connected spectrum form a torsion-free group.
* `IsGroupLikeElem.eq_one_of_pow_eq_one`: the elementwise form.
* `BialgHom.monoidAlgebra_single_eq_one`: a bialgebra homomorphism kills torsion basis
  elements.
* `BialgHom.monoidAlgebra_eq_algebraMap_counit`: a bialgebra homomorphism from the group
  algebra of a torsion group factors through the counit.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
-/

public section

namespace TauCeti

universe u v w

variable (k : Type u) [Field k] (H : Type v) [CommRing H] [HopfAlgebra k H]

/-- **The group-like elements of a reduced Hopf algebra with connected spectrum form a
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

/-- A group-like element of finite order in a reduced Hopf algebra with connected spectrum is
trivial. -/
theorem _root_.IsGroupLikeElem.eq_one_of_pow_eq_one
    [IsReduced H] [ConnectedSpace (PrimeSpectrum H)] {a : H} (ha : IsGroupLikeElem k a)
    {n : ℕ} (hn : n ≠ 0) (hpow : a ^ n = 1) : a = 1 := by
  have _ := isMulTorsionFree_groupLike_of_isReduced_of_connectedSpace k H
  have hg : (⟨a, ha⟩ : GroupLike k H) ^ n = 1 := by
    ext
    simpa using hpow
  exact congrArg GroupLike.val ((pow_eq_one_iff.mp hg).resolve_right hn)

/-- **A bialgebra homomorphism into a reduced Hopf algebra with connected spectrum kills every
torsion basis element of a group algebra.** -/
@[simp]
theorem _root_.BialgHom.monoidAlgebra_single_eq_one
    [IsReduced H] [ConnectedSpace (PrimeSpectrum H)]
    {M : Type w} [Monoid M] (f : MonoidAlgebra k M →ₐc[k] H) {m : M} (hm : IsOfFinOrder m) :
    f (MonoidAlgebra.single m 1) = 1 := by
  refine ((MonoidAlgebra.isGroupLikeElem_single_one m).map f).eq_one_of_pow_eq_one
    (n := orderOf m) (orderOf_ne_zero_iff.mpr hm) ?_
  rw [← map_pow, MonoidAlgebra.single_pow, one_pow, pow_orderOf_eq_one,
    ← MonoidAlgebra.one_def, map_one]

/-- **A bialgebra homomorphism from the group algebra of a torsion group into a reduced Hopf
algebra with connected spectrum factors through the counit.** -/
theorem _root_.BialgHom.monoidAlgebra_eq_algebraMap_counit
    [IsReduced H] [ConnectedSpace (PrimeSpectrum H)]
    {M : Type w} [Monoid M] (f : MonoidAlgebra k M →ₐc[k] H) (hM : IsMulTorsion M) :
    (f : MonoidAlgebra k M →ₐ[k] H) =
      (Algebra.ofId k H).comp (Bialgebra.counitAlgHom k (MonoidAlgebra k M)) := by
  refine MonoidAlgebra.algHom_ext (fun m ↦ ?_) (Subsingleton.elim _ _)
  rw [AlgHom.comp_apply, BialgHom.coe_toAlgHom, f.monoidAlgebra_single_eq_one (hM m)]
  simp [Bialgebra.counitAlgHom, Algebra.ofId]

end TauCeti
