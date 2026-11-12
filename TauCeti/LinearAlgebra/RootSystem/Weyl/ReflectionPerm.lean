/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Comparing Weyl groups through their reflection permutations

Two root pairings on the same root index type have canonically isomorphic Weyl groups
if their reflection permutations agree and both Weyl groups act faithfully on root
indices. This comparison does not require an equivalence of weight lattices: it applies,
for example, to the full coordinate-difference (GLₙ) datum and the adjoint datum
of type A, whose character lattices have different ranks.

The construction compares the ranges of Mathlib's `RootPairing.weylGroupToPerm`,
using `RootPairing.range_weylGroupToPerm`. The resulting equivalence preserves the
root-index action and each indexed reflection.
-/

public section

namespace RootPairing

noncomputable section

variable {ι R S M N M' N' : Type*} [CommRing R] [CommRing S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module S M'] [AddCommGroup N'] [Module S N']
  (P : RootPairing ι R M N) (Q : RootPairing ι S M' N')
  (h : P.reflectionPerm = Q.reflectionPerm)
  (hP : Function.Injective P.weylGroupToPerm)
  (hQ : Function.Injective Q.weylGroupToPerm)

/-- Root pairings with the same reflection permutations and faithful Weyl actions on
root indices have canonically isomorphic Weyl groups. -/
def weylGroupEquivOfReflectionPermEq : P.weylGroup ≃* Q.weylGroup :=
  (MonoidHom.ofInjective hP).trans
    ((MulEquiv.subgroupCongr (by
      rw [range_weylGroupToPerm, range_weylGroupToPerm, h])).trans
      (MonoidHom.ofInjective hQ).symm)

/-- The reflection-permutation comparison preserves the entire action on root indices.
Use this with `rw`; simplification unfolds `weylGroupToPerm` to `indexEquiv`. -/
theorem weylGroupToPerm_weylGroupEquivOfReflectionPermEq (w : P.weylGroup) :
    Q.weylGroupToPerm (weylGroupEquivOfReflectionPermEq P Q h hP hQ w) =
      P.weylGroupToPerm w := by
  simp only [weylGroupEquivOfReflectionPermEq, MulEquiv.trans_apply,
    MonoidHom.apply_ofInjective_symm, MulEquiv.subgroupCongr_apply,
    MonoidHom.ofInjective_apply]

/-- The reflection-permutation comparison sends an indexed reflection to the
reflection with the same root index. -/
@[simp]
theorem weylGroupEquivOfReflectionPermEq_ofIdx (i : ι) :
    weylGroupEquivOfReflectionPermEq P Q h hP hQ (weylGroup.ofIdx P i) =
      weylGroup.ofIdx Q i := by
  apply hQ
  rw [weylGroupToPerm_weylGroupEquivOfReflectionPermEq]
  ext j
  simp only [weylGroupToPerm_ofIdx_apply, h]

/-- The inverse comparison also preserves indexed reflections. -/
@[simp]
theorem weylGroupEquivOfReflectionPermEq_symm_ofIdx (i : ι) :
    (weylGroupEquivOfReflectionPermEq P Q h hP hQ).symm (weylGroup.ofIdx Q i) =
      weylGroup.ofIdx P i := by
  rw [← weylGroupEquivOfReflectionPermEq_ofIdx P Q h hP hQ,
    MulEquiv.symm_apply_apply]

end

end RootPairing
