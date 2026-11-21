/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Component.Base
public import TauCeti.LinearAlgebra.RootSystem.DirectSum.Weyl

/-!
# Irreducible component decomposition as an internal direct sum

A finite root system `P : RootPairing ι K M N` over a field with `2 ≠ 0` is canonically
equivalent to the internal direct sum of its irreducible component pairings
`P.componentPairing : ∀ C : P.Component, RootPairing C.supp K (P.componentSpace C) _`. This file
constructs that equivalence `RootPairing.equivInternalDirectSumComponentPairing`, shows that
assembling `RootPairing.Base.componentBase` recovers the transported base, and derives the
canonical splitting of `P.weylGroup` into the product of the component Weyl groups.

## Main definitions

* `RootPairing.equivInternalDirectSumComponentPairing`: canonical equivalence between `P` and the
  internal direct sum of `P.componentPairing`.
* `RootPairing.componentWeylGroupEquiv`: canonical multiplicative isomorphism between
  `P.weylGroup` and `∀ C : P.Component, (P.componentPairing C).weylGroup`.

## Main results

* `RootPairing.equivInternalDirectSumComponentPairing_weightMap`,
  `RootPairing.equivInternalDirectSumComponentPairing_coweightMap`,
  `RootPairing.equivInternalDirectSumComponentPairing_indexEquiv`: formulas for the maps of
  `RootPairing.equivInternalDirectSumComponentPairing`.
* `RootPairing.Base.internalDirectSum_componentBase`: assembling `Base.componentBase` across all
  components recovers the base transported along `equivInternalDirectSumComponentPairing`.
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

/-- **Canonical decomposition of a finite root system into the internal direct sum of its
irreducible component pairings** (Bourbaki, Lie VI §1, no. 2). -/
noncomputable def equivInternalDirectSumComponentPairing [NeZero (2 : K)] [Finite ι]
    [P.IsRootSystem] :
    P.Equiv (internalDirectSum P.iSupIndep_componentSpace
      (P.iSup_componentSpace.trans IsRootSystem.span_root_eq_top) P.componentPairing) where
  weightMap := LinearMap.id
  coweightMap := P.flip.toPerfPair.symm.toLinearMap
  indexEquiv := (_root_.Equiv.sigmaFiberEquiv P.componentOf).symm
  weight_coweight_transpose := by
    refine LinearMap.ext fun f ↦ LinearMap.ext fun x ↦ ?_
    simp
  root_weightMap := by
    ext i
    exact (coe_componentPairing_root P (P.componentOf i) ⟨i, rfl⟩).symm.trans
      (internalDirectSum_root P.iSupIndep_componentSpace
        (P.iSup_componentSpace.trans IsRootSystem.span_root_eq_top)
        P.componentPairing (P.componentOf i) ⟨i, rfl⟩).symm
  coroot_coweightMap := by
    ext ⟨C, ⟨i, hi⟩⟩
    apply P.flip.toPerfPair.injective
    refine LinearMap.ext fun x ↦ ?_
    simp only [Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, internalDirectSum_coroot, LinearMap.comp_apply,
      internalProjection_componentSpace_eq_componentProj]
    exact componentPairing_coroot'_componentProj P C ⟨i, hi⟩ x
  bijective_weightMap := Function.bijective_id
  bijective_coweightMap := LinearEquiv.bijective _

@[simp]
theorem equivInternalDirectSumComponentPairing_weightMap [NeZero (2 : K)] [Finite ι]
    [P.IsRootSystem] :
    (P.equivInternalDirectSumComponentPairing).weightMap = LinearMap.id :=
  (rfl)

@[simp]
theorem equivInternalDirectSumComponentPairing_coweightMap [NeZero (2 : K)] [Finite ι]
    [P.IsRootSystem] :
    (P.equivInternalDirectSumComponentPairing).coweightMap = P.flip.toPerfPair.symm.toLinearMap :=
  (rfl)

@[simp]
theorem equivInternalDirectSumComponentPairing_indexEquiv [NeZero (2 : K)] [Finite ι]
    [P.IsRootSystem] (i : ι) :
    (P.equivInternalDirectSumComponentPairing).indexEquiv i = ⟨P.componentOf i, ⟨i, rfl⟩⟩ :=
  (rfl)

/-- **Assembling the component bases `Base.componentBase` recovers the original base** under
`RootPairing.equivInternalDirectSumComponentPairing`. -/
@[simp]
theorem Base.internalDirectSum_componentBase [NeZero (2 : K)] [Finite ι] [P.IsRootSystem]
    (b : P.Base) :
    Base.internalDirectSum P.iSupIndep_componentSpace
        (P.iSup_componentSpace.trans IsRootSystem.span_root_eq_top)
        (fun C ↦ b.componentBase C) =
      b.map P.equivInternalDirectSumComponentPairing := by
  classical
  ext ⟨C, ⟨i, hi⟩⟩
  simp only [Base.mem_support_internalDirectSum, Base.mem_support_componentBase,
    Base.support_map_eq, Finset.mem_image, equivInternalDirectSumComponentPairing_indexEquiv]
  constructor
  · intro h
    exact ⟨i, h, by subst hi; rfl⟩
  · rintro ⟨j, hj, heq⟩
    rcases Sigma.ext_iff.mp heq with ⟨hC, hij⟩
    subst hC
    rw [heq_eq_eq] at hij
    cases hij
    exact hj

/-- **The Weyl group of a finite root system splits canonically as the product of the Weyl groups
of its irreducible components** (Bourbaki, Lie VI §1, no. 2, Proposition 5). -/
noncomputable def componentWeylGroupEquiv [NeZero (2 : K)] [Finite ι] [P.IsRootSystem] :
    P.weylGroup ≃* ∀ C : P.Component, (P.componentPairing C).weylGroup :=
  (P.equivInternalDirectSumComponentPairing).weylGroupEquiv.trans
    (internalDirectSumWeylGroupEquiv P.iSupIndep_componentSpace
      (P.iSup_componentSpace.trans IsRootSystem.span_root_eq_top) P.componentPairing)

/-- The component Weyl-group isomorphism intertwines the action on `M` with the component actions
along `RootPairing.componentProj`. -/
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
