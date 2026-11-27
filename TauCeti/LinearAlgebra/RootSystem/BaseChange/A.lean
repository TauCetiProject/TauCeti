/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Pi
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A.Basic
import TauCeti.Algebra.Algebra.Pi
import TauCeti.LinearAlgebra.RootSystem.BaseChange.CartanType
import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# Entrywise base change of the simply connected root datum of type `Aₘ`

This file extends `typeASimplyConnectedRootDatum m` and `typeASimplyConnectedBase m` entrywise to
an arbitrary characteristic-zero field `K` via `TauCeti.rootPairingBaseChange`, producing the
reduced crystallographic root system `typeABaseChangeRootSystem K m` on `Fin m → K`, its Bourbaki
base `typeABaseChangeBase K m` of Cartan type `A m`, and its coordinate-reversal graph automorphism
`typeABaseChangeGraphAut K m`.

## References
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate I.
-/

public section

namespace TauCeti.DynkinType

variable (K : Type*) [Field K] [CharZero K]

/-- Entrywise base-changed root system of type `Aₘ` on `Fin m → K`. -/
def typeABaseChangeRootSystem (m : ℕ) :
    RootPairing (Fin (m * (m + 1))) K (Fin m → K) (Fin m → K) :=
  rootPairingBaseChange K (typeASimplyConnectedRootDatum m)
    (fun x y ↦ toLinearMap_typeASimplyConnectedRootDatum x y)

/-- The Bourbaki-numbered base of `typeABaseChangeRootSystem K m`. -/
def typeABaseChangeBase (m : ℕ) : (typeABaseChangeRootSystem K m).Base :=
  rootPairingBaseChangeBase K (typeASimplyConnectedRootDatum m)
    (fun x y ↦ toLinearMap_typeASimplyConnectedRootDatum x y) (typeASimplyConnectedBase m)

/-- Base change preserves crystallographicity for `typeABaseChangeRootSystem K m`. -/
instance instIsCrystallographicTypeABaseChangeRootSystem (m : ℕ) :
    (typeABaseChangeRootSystem K m).IsCrystallographic :=
  isCrystallographic_rootPairingBaseChange ..

/-- Base change preserves reducedness for `typeABaseChangeRootSystem K m`. -/
instance instIsReducedTypeABaseChangeRootSystem (m : ℕ) :
    (typeABaseChangeRootSystem K m).IsReduced :=
  let _ : (typeASimplyConnectedRootDatum m).IsReduced :=
    RootPairing.isReduced_of_pairing_comm _ pairing_typeASimplyConnectedRootDatum_comm
  isReduced_rootPairingBaseChange K _ _

/-- Over a characteristic-zero field, the roots and coroots of `typeABaseChangeRootSystem K m`
span `Fin m → K`. -/
instance instIsRootSystemTypeABaseChangeRootSystem (m : ℕ) :
    (typeABaseChangeRootSystem K m).IsRootSystem :=
  (hasCartanType_typeASimplyConnectedRootDatum m).isRootSystem_rootPairingBaseChange K _
    (by rw [DynkinType.rank_A, Fintype.card_fin])
    (corootSpan_typeASimplyConnectedRootDatum_eq_top m)

/-- `typeABaseChangeBase K m` has Cartan type `A m`. -/
theorem hasCartanType_typeABaseChangeBase (m : ℕ) :
    HasCartanType (typeABaseChangeRootSystem K m) (typeABaseChangeBase K m) (.A m) :=
  (hasCartanType_typeASimplyConnectedRootDatum m).rootPairingBaseChange K _

/-- The bilinear pairing of `typeABaseChangeRootSystem K m` is `dotProduct`. -/
@[simp] theorem toLinearMap_typeABaseChangeRootSystem (m : ℕ) (x y : Fin m → K) :
    (typeABaseChangeRootSystem K m).toLinearMap x y = x ⬝ᵥ y :=
  toLinearMap_rootPairingBaseChange K (typeASimplyConnectedRootDatum m) _ x y

/-- Each root of `typeABaseChangeRootSystem K m` is the entrywise cast of the integral root. -/
@[simp] theorem root_typeABaseChangeRootSystem (m : ℕ) (i : Fin (m * (m + 1))) :
    (typeABaseChangeRootSystem K m).root i =
      Pi.algebraMap (Fin m) ℤ K ((typeASimplyConnectedRootDatum m).root i) :=
  root_rootPairingBaseChange K (typeASimplyConnectedRootDatum m) _ i

/-- Each coroot of `typeABaseChangeRootSystem K m` is the entrywise cast of the integral coroot. -/
@[simp] theorem coroot_typeABaseChangeRootSystem (m : ℕ) (i : Fin (m * (m + 1))) :
    (typeABaseChangeRootSystem K m).coroot i =
      Pi.algebraMap (Fin m) ℤ K ((typeASimplyConnectedRootDatum m).coroot i) :=
  coroot_rootPairingBaseChange K (typeASimplyConnectedRootDatum m) _ i

/-- The reflection permutation of `typeABaseChangeRootSystem K m` agrees with the integral datum. -/
@[simp] theorem reflectionPerm_typeABaseChangeRootSystem (m : ℕ) :
    (typeABaseChangeRootSystem K m).reflectionPerm =
      (typeASimplyConnectedRootDatum m).reflectionPerm :=
  reflectionPerm_rootPairingBaseChange K (typeASimplyConnectedRootDatum m) _

/-- `k ∈ (typeABaseChangeBase K m).support` iff `(k : ℕ) < m`. -/
@[simp] theorem mem_support_typeABaseChangeBase_iff (m : ℕ) (k : Fin (m * (m + 1))) :
    k ∈ (typeABaseChangeBase K m).support ↔ (k : ℕ) < m := by
  rw [typeABaseChangeBase, support_rootPairingBaseChangeBase, mem_typeASimplyConnectedBase_support]

/-- The graph automorphism of `typeABaseChangeRootSystem K m`, reversing `Fin m → K`. -/
noncomputable def typeABaseChangeGraphAut (m : ℕ) :
    RootPairing.Aut (typeABaseChangeRootSystem K m) :=
  RootPairing.Equiv.mk' (typeABaseChangeRootSystem K m) (typeABaseChangeRootSystem K m)
    (LinearEquiv.funCongrLeft K K (Fin.revPerm : Equiv.Perm (Fin m)))
    (typeAGraphAut m).indexEquiv fun i ↦ funext fun k ↦ by
      have h := congrFun (RootPairing.Hom.root_weightMap_apply _ _ i (typeAGraphAut m).toHom) k
      rw [weightMap_typeAGraphAut_apply] at h
      simpa [root_typeABaseChangeRootSystem, piAlgebraMap_apply] using congrArg (algebraMap ℤ K) h

/-- The index permutation of `typeABaseChangeGraphAut K m` agrees with `typeAGraphAut m`. -/
@[simp] theorem indexEquiv_typeABaseChangeGraphAut (m : ℕ) :
    (typeABaseChangeGraphAut K m).indexEquiv = (typeAGraphAut m).indexEquiv := (rfl)

/-- `typeABaseChangeGraphAut K m` reverses weight coordinates. -/
@[simp] theorem weightMap_typeABaseChangeGraphAut_apply (m : ℕ) (x : Fin m → K) (k : Fin m) :
    (typeABaseChangeGraphAut K m).weightMap x k = x k.rev := (rfl)

end TauCeti.DynkinType
