/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Hom
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Pi
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Transport

/-!
# Weyl groups under entrywise base change

A root pairing on standard lattices, with dot-product pairing,
has the same Weyl group after an injective extension of coefficients. The comparison
preserves the root-index permutation and sends each indexed reflection to the corresponding
reflection. It also intertwines the weight-space actions along the entrywise algebra map.

This applies to simply connected integral root data, whose roots need not span the character
lattice. In particular, it connects their explicit Weyl-group computations to those on the
rational root systems, where classification by Cartan matrices applies. Neither finiteness
of the root index set nor reducedness or crystallographicity is required.

No spanning hypothesis on the roots or coroots is required.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter VI, §1.
-/

public section

namespace TauCeti

open RootPairing Function Matrix TensorProduct

section

variable {κ R : Type*} (S : Type*) [Fintype κ] [DecidableEq κ]
  [CommRing R] [CommRing S] [Algebra R S]

private theorem piScalarRight_tmul (a : S) (x : κ → R) :
    TensorProduct.piScalarRight R S S κ (a ⊗ₜ[R] x) = fun j ↦ x j • a := by
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]

private theorem piScalarRight_one_tmul (x : κ → R) :
    TensorProduct.piScalarRight R S S κ (1 ⊗ₜ[R] x) = Pi.algebraMap κ R S x := by
  rw [piScalarRight_tmul]
  ext j
  simp [Pi.algebraMap, Algebra.smul_def]

end

variable {ι κ R : Type*} (S : Type*) [Fintype κ] [CommRing R] [CommRing S] [Algebra R S]
  [FaithfulSMul R S] (P : RootPairing ι R (κ → R) (κ → R))
  (hP : ∀ x y, P.toLinearMap x y = x ⬝ᵥ y)

local notation "Q" => rootPairingBaseChange S P hP
local notation "A" => Pi.algebraMap κ R S

open Classical in
private noncomputable def piEquiv : (P.baseChange S).Equiv Q :=
  let e : S ⊗[R] (κ → R) ≃ₗ[S] (κ → S) := TensorProduct.piScalarRight R S S κ
  { weightMap := e.toLinearMap
    coweightMap := e.symm.toLinearMap
    indexEquiv := _root_.Equiv.refl ι
    weight_coweight_transpose := LinearMap.ext fun n ↦ by
      have hcomp :
          (e.toLinearMap.dualMap ∘ₗ (Q).flip.toPerfPair.toLinearMap) ∘ₗ e.toLinearMap =
            (P.baseChange S).flip.toPerfPair.toLinearMap := by
        refine AlgebraTensorModule.ext fun a y ↦ AlgebraTensorModule.ext fun b x ↦ ?_
        simp only [LinearMap.comp_apply, LinearMap.dualMap_apply, LinearEquiv.coe_coe,
          LinearMap.toPerfPair_apply, flip_toLinearMap, LinearMap.flip_apply,
          toLinearMap_rootPairingBaseChange, baseChange_toLinearMap,
          LinearMap.baseChangePairing_tmul_tmul, e, piScalarRight_tmul, dotProduct,
          Algebra.smul_def, Finset.mul_sum, map_sum, map_mul, hP]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        ring
      simpa using congr($hcomp (e.symm n))
    root_weightMap := by
      ext i j
      simp only [Function.comp_apply, root_rootPairingBaseChange, baseChange_root,
        _root_.Equiv.refl_apply, LinearEquiv.coe_coe]
      exact congrFun (piScalarRight_one_tmul S (P.root i)) j
    coroot_coweightMap := by
      ext i
      simp only [Function.comp_apply, baseChange_coroot, coroot_rootPairingBaseChange,
        LinearEquiv.coe_coe]
      exact (congrArg e.symm (piScalarRight_one_tmul S (P.coroot i)).symm).trans
        (e.symm_apply_apply _)
    bijective_weightMap := e.bijective
    bijective_coweightMap := e.symm.bijective }

private theorem piEquiv_weightEquiv_one_tmul (x : κ → R) :
    (piEquiv S P hP).weightEquiv (1 ⊗ₜ[R] x) = A x := by
  classical exact piScalarRight_one_tmul S x

/-- Entrywise extension of coefficients identifies Weyl groups.
The identification preserves the permutation of root indices. -/
noncomputable def weylGroupBaseChangeEquiv : P.weylGroup ≃* (Q).weylGroup :=
  (P.weylGroupBaseChangeMulEquiv S).trans (piEquiv S P hP).weylGroupEquiv

/-- Entrywise scalar extension intertwines the Weyl-group actions on weight vectors. -/
@[simp]
theorem weylGroupBaseChangeEquiv_smul (w : P.weylGroup) (x : κ → R) :
    weylGroupBaseChangeEquiv S P hP w • A x = A (w • x) := by
  rw [weylGroupBaseChangeEquiv, MulEquiv.trans_apply, ← piEquiv_weightEquiv_one_tmul S P hP x,
    (piEquiv S P hP).weylGroupEquiv_smul, P.weylGroupBaseChangeMulEquiv_smul_tmul S,
    piEquiv_weightEquiv_one_tmul]

/-- The inverse comparison intertwines the Weyl-group actions on weight vectors. -/
@[simp low]
theorem weylGroupBaseChangeEquiv_symm_smul (w : (Q).weylGroup) (x : κ → R) :
    w • A x = A ((weylGroupBaseChangeEquiv S P hP).symm w • x) := by
  simpa only [MulEquiv.apply_symm_apply] using
    weylGroupBaseChangeEquiv_smul S P hP ((weylGroupBaseChangeEquiv S P hP).symm w) x

/-- The base-change comparison leaves the root-index permutation unchanged.
This is a rewrite rule, not a simp rule: `weylGroupToPerm` simplifies to `indexEquiv`. -/
theorem weylGroupToPerm_weylGroupBaseChangeEquiv (w : P.weylGroup) :
    (Q).weylGroupToPerm (weylGroupBaseChangeEquiv S P hP w) = P.weylGroupToPerm w := by
  ext i
  apply (Q).root.injective
  rw [← weylGroup_apply_root, root_rootPairingBaseChange, weylGroupBaseChangeEquiv_smul,
    weylGroup_apply_root, root_rootPairingBaseChange]

/-- The inverse comparison also leaves the root-index permutation unchanged.
As in the forward direction, use this with `rw` rather than `simp`. -/
theorem weylGroupToPerm_weylGroupBaseChangeEquiv_symm (w : (Q).weylGroup) :
    P.weylGroupToPerm ((weylGroupBaseChangeEquiv S P hP).symm w) =
      (Q).weylGroupToPerm w := by
  rw [← weylGroupToPerm_weylGroupBaseChangeEquiv S P hP, MulEquiv.apply_symm_apply]

/-- Base change sends each indexed reflection to the reflection with the same index. -/
@[simp]
theorem weylGroupBaseChangeEquiv_ofIdx (i : ι) :
    weylGroupBaseChangeEquiv S P hP (weylGroup.ofIdx P i) = weylGroup.ofIdx Q i := by
  simp [weylGroupBaseChangeEquiv]
  rfl

/-- The inverse base-change comparison preserves indexed reflections. -/
@[simp]
theorem weylGroupBaseChangeEquiv_symm_ofIdx (i : ι) :
    (weylGroupBaseChangeEquiv S P hP).symm (weylGroup.ofIdx Q i) =
      weylGroup.ofIdx P i := by
  rw [← weylGroupBaseChangeEquiv_ofIdx S P hP, MulEquiv.symm_apply_apply]

end TauCeti
