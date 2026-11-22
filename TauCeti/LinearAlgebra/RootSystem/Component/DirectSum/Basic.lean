/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Component.Pairing
public import TauCeti.LinearAlgebra.RootSystem.DirectSum.Internal

/-!
# Irreducible component decomposition as an internal direct sum

A finite root system `P : RootPairing ι K M N` over a field with `2 ≠ 0` is canonically
equivalent to the internal direct sum of its irreducible component pairings
`P.componentPairing : ∀ C : P.Component, RootPairing C.supp K (P.componentSpace C) _`. This file
constructs that equivalence `RootPairing.equivInternalDirectSumComponentPairing` and records the
formulas for its maps.

## Main definitions

* `RootPairing.equivInternalDirectSumComponentPairing`: canonical equivalence between `P` and the
  internal direct sum of `P.componentPairing`.

## Main results

* `RootPairing.internalProjection_componentSpace_eq_componentProj`: `TauCeti.internalProjection`
  onto a component space agrees with `RootPairing.componentProj`.
* `RootPairing.equivInternalDirectSumComponentPairing_weightMap`,
  `RootPairing.equivInternalDirectSumComponentPairing_coweightMap`,
  `RootPairing.equivInternalDirectSumComponentPairing_indexEquiv`: formulas for the maps of
  `RootPairing.equivInternalDirectSumComponentPairing`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §1, no. 2, Proposition 5.
-/

public section

open TauCeti

namespace RootPairing

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] (P : RootPairing ι K M N)

/-- The internal projection onto a component space agrees with `RootPairing.componentProj`. -/
@[simp]
theorem internalProjection_componentSpace_eq_componentProj [P.IsRootSystem] (C : P.Component)
    (x : M) :
    TauCeti.internalProjection P.iSupIndep_componentSpace
        (P.iSup_componentSpace.trans IsRootSystem.span_root_eq_top) C x =
      P.componentProj C x := by
  have hx : x ∈ ⨆ D, P.componentSpace D :=
    (P.iSup_componentSpace.trans IsRootSystem.span_root_eq_top).symm ▸ Submodule.mem_top
  induction hx using Submodule.iSup_induction' with
  | mem D y hy =>
    rcases eq_or_ne D C with rfl | hDC
    · rw [TauCeti.internalProjection_apply_of_mem _ _ hy, P.componentProj_apply_of_mem hy]
    · rw [TauCeti.internalProjection_apply_eq_zero_of_mem_of_ne _ _ hDC hy,
        P.componentProj_apply_of_ne hDC hy]
  | zero => simp
  | add u v _ _ hu hv => simp only [map_add, hu, hv]

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

end RootPairing
