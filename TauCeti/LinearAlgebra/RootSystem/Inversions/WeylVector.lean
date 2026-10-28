/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Inversions.Basic
public import TauCeti.LinearAlgebra.RootSystem.Weyl.DotAction

/-!
# The Weyl vector moved by a Weyl-group element

For a base of a root pairing with Weyl vector `ρ`, every Weyl-group element `w` moves `ρ` by
minus the sum of the positive roots that `w⁻¹` makes negative:

`w ρ - ρ = -∑_{α > 0, w⁻¹ α < 0} α`.

The positive roots fall into those that `w` keeps positive and those it inverts. The first are
carried by `w` onto the positive roots that `w⁻¹` keeps positive, and the second, negated after
applying `w`, onto the positive roots that `w⁻¹` inverts. So `w` applied to the sum `2ρ` of the
positive roots keeps the first part of `2ρ` and negates the second.

The identity is stated first for `2ρ`, where it needs nothing beyond the characteristic-zero
hypothesis under which positivity is defined, and then halved. Its point is that `w ρ - ρ` is a
sum of roots although `ρ` itself need not be: it lies in every lattice containing the roots. Hence
the dot action `w ⬝ x = w (x + ρ) - ρ` is the linear action followed by a translation by a sum of
roots, and it preserves every Weyl-stable lattice that contains the roots, whether or not that
lattice contains `ρ`.

## Main results

* `TauCeti.smul_twoWeylVector_sub_twoWeylVector`: `w (2ρ) - 2ρ = -2 ∑_{α > 0, w⁻¹ α < 0} α`.
* `TauCeti.smul_weylVector_sub_weylVector`: `w ρ - ρ = -∑_{α > 0, w⁻¹ α < 0} α`.
* `TauCeti.dotAction_eq_smul_sub_sum`: `w ⬝ x = w x - ∑_{α > 0, w⁻¹ α < 0} α`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. III,
  §10.3.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4–6, Ch. VI, §1, no. 10.
-/

public section

namespace TauCeti

open RootPairing

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [CharZero R] (b : P.Base) [Finite ι] (w : P.weylGroup)

/-- **A Weyl-group element moves the sum of the positive roots by twice the inversions of its
inverse**: `w (2ρ) - 2ρ = -2 ∑_{α > 0, w⁻¹ α < 0} α`. -/
theorem smul_twoWeylVector_sub_twoWeylVector :
    w • twoWeylVector P b - twoWeylVector P b =
      -(2 : R) • ∑ i ∈ inversionsFinset P b w⁻¹, P.root i := by
  classical
  let := P.indexNeg
  -- `w` keeps the part of `2ρ` over the roots it keeps positive, and negates the rest.
  have hw : w • twoWeylVector P b =
      ∑ i ∈ posRootsFinset P b \ inversionsFinset P b w⁻¹, P.root i -
        ∑ i ∈ inversionsFinset P b w⁻¹, P.root i := by
    rw [twoWeylVector_def, Finset.smul_sum,
      ← Finset.sum_sdiff (inversionsFinset_subset_posRootsFinset P b w)]
    simp_rw [weylGroup_apply_root]
    rw [sum_posRootsFinset_sdiff_inversionsFinset_comp_weylGroupToPerm, sub_eq_add_neg,
      ← sum_inversionsFinset_comp_neg_weylGroupToPerm P b w P.root, ← Finset.sum_neg_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
    rw [indexNeg_neg, root_reflectionPerm, reflection_apply_self, neg_neg]
  rw [hw, twoWeylVector_def,
    ← Finset.sum_sdiff (inversionsFinset_subset_posRootsFinset P b w⁻¹)]
  module

variable [Invertible (2 : R)]

/-- **A Weyl-group element moves the Weyl vector by minus the inversions of its inverse**:
`w ρ - ρ = -∑_{α > 0, w⁻¹ α < 0} α`. In particular `w ρ - ρ` is a sum of roots, whether or not
`ρ` is. -/
theorem smul_weylVector_sub_weylVector :
    w • weylVector P b - weylVector P b = -∑ i ∈ inversionsFinset P b w⁻¹, P.root i := by
  rw [weylVector_def, smul_comm, ← smul_sub, smul_twoWeylVector_sub_twoWeylVector, smul_smul,
    mul_neg, invOf_mul_self, neg_one_smul]

/-- **The dot action is the linear action followed by a translation by a sum of roots**:
`w ⬝ x = w x - ∑_{α > 0, w⁻¹ α < 0} α`. -/
theorem dotAction_eq_smul_sub_sum (x : M) :
    dotAction P b w x = w • x - ∑ i ∈ inversionsFinset P b w⁻¹, P.root i := by
  rw [dotAction_def, smul_add, add_sub_assoc, smul_weylVector_sub_weylVector, sub_eq_add_neg]

end TauCeti
