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

variable {ι κ R : Type*} (S : Type*) [Fintype κ] [CommRing R] [CommRing S] [Algebra R S]
  [FaithfulSMul R S] (P : RootPairing ι R (κ → R) (κ → R))
  (hP : ∀ x y, P.toLinearMap x y = x ⬝ᵥ y)

local notation "Q" => rootPairingBaseChange S P hP
local notation "A" => Pi.algebraMap κ R S

/-- Entrywise extension of coefficients identifies Weyl groups.
The identification preserves the permutation of root indices. -/
noncomputable def weylGroupBaseChangeEquiv : P.weylGroup ≃* (Q).weylGroup :=
  (P.weylGroupBaseChangeMulEquiv S).trans (rootPairingBaseChangeEquiv S P hP).weylGroupEquiv

/-- Entrywise scalar extension intertwines the Weyl-group actions on weight vectors. -/
@[simp]
theorem weylGroupBaseChangeEquiv_smul (w : P.weylGroup) (x : κ → R) :
    weylGroupBaseChangeEquiv S P hP w • A x = A (w • x) := by
  classical
  rw [weylGroupBaseChangeEquiv, MulEquiv.trans_apply,
    ← rootPairingBaseChangeEquiv_weightEquiv_one_tmul S P hP x,
    (rootPairingBaseChangeEquiv S P hP).weylGroupEquiv_smul,
    P.weylGroupBaseChangeMulEquiv_smul_tmul S,
    rootPairingBaseChangeEquiv_weightEquiv_one_tmul]

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

/-- The inverse base-change comparison preserves indexed reflections. -/
@[simp]
theorem weylGroupBaseChangeEquiv_symm_ofIdx (i : ι) :
    (weylGroupBaseChangeEquiv S P hP).symm (weylGroup.ofIdx Q i) =
      weylGroup.ofIdx P i := by
  rw [← weylGroupBaseChangeEquiv_ofIdx S P hP, MulEquiv.symm_apply_apply]

end TauCeti
