/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Component.DirectSum
public import TauCeti.LinearAlgebra.RootSystem.DirectSum.Weyl

/-!
# Weyl group splitting under the irreducible component decomposition

The Weyl group of a finite root system `P` over a field with `2 ≠ 0` splits canonically as the
product of the Weyl groups of its irreducible component pairings `P.componentPairing` along
`RootPairing.equivInternalDirectSumComponentPairing`.

## Main definitions

* `RootPairing.componentWeylGroupEquiv`: canonical multiplicative isomorphism between
  `P.weylGroup` and `∀ C : P.Component, (P.componentPairing C).weylGroup`.

## Main results

* `RootPairing.componentProj_smul_eq_componentWeylGroupEquiv`,
  `RootPairing.componentWeylGroupEquiv_ofIdx_self`,
  `RootPairing.componentWeylGroupEquiv_ofIdx_ne`: equivariance and generator formulas for
  `RootPairing.componentWeylGroupEquiv`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §1, no. 2, Proposition 5.
-/

public section

open TauCeti

namespace RootPairing

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] (P : RootPairing ι K M N)

/-- **The Weyl group of a finite root system splits canonically as the product of the Weyl groups
of its irreducible components** (Bourbaki, Lie VI §1, no. 2, Proposition 5). -/
noncomputable def componentWeylGroupEquiv [NeZero (2 : K)] [Finite ι] [P.IsRootSystem] :
    P.weylGroup ≃* ∀ C : P.Component, (P.componentPairing C).weylGroup :=
  (P.equivInternalDirectSumComponentPairing).weylGroupEquiv.trans
    (internalDirectSumWeylGroupEquiv P.iSupIndep_componentSpace
      (P.iSup_componentSpace.trans IsRootSystem.span_root_eq_top) P.componentPairing)

/-- The component Weyl-group isomorphism intertwines the action on `M` with the component actions
along `RootPairing.componentProj`. -/
@[simp]
theorem componentProj_smul_eq_componentWeylGroupEquiv [NeZero (2 : K)] [Finite ι]
    [P.IsRootSystem] (w : P.weylGroup) (C : P.Component) (x : M) :
    P.componentProj C (w • x) = P.componentWeylGroupEquiv w C • P.componentProj C x := by
  have h1 := P.equivInternalDirectSumComponentPairing.weylGroupEquiv_smul w x
  have hw : (P.equivInternalDirectSumComponentPairing.weylGroupEquiv w) • x = w • x := by
    simpa [Equiv.weightEquiv_apply] using h1
  rw [← internalProjection_componentSpace_eq_componentProj, ← hw,
    internalProjection_smul_internalDirectSum, internalProjection_componentSpace_eq_componentProj]
  rfl

@[simp]
theorem componentWeylGroupEquiv_ofIdx_self [NeZero (2 : K)] [Finite ι] [P.IsRootSystem] (i : ι) :
    P.componentWeylGroupEquiv (weylGroup.ofIdx P i) (P.componentOf i) =
      weylGroup.ofIdx (P.componentPairing (P.componentOf i)) ⟨i, rfl⟩ := by
  simp [componentWeylGroupEquiv]

@[simp]
theorem componentWeylGroupEquiv_ofIdx_ne [NeZero (2 : K)] [Finite ι] [P.IsRootSystem]
    {C : P.Component} {i : ι} (hC : C ≠ P.componentOf i) :
    P.componentWeylGroupEquiv (weylGroup.ofIdx P i) C = 1 := by
  simp [componentWeylGroupEquiv, hC]

end RootPairing
