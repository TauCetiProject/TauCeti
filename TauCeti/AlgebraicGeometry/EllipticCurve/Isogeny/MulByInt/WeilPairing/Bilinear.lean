/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Torsion.Structure
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Basic
public import TauCeti.RingTheory.RootsOfUnity.ZMod

/-!
# The Weil pairing as a `ZMod N`-bilinear form

Let `W` be an elliptic curve over a separably closed field `F` and `N` a positive integer
invertible in `F`. Both `E[N]` and `μ_N`, written additively, are killed by `N`, so they are
`ZMod N`-modules, and the Weil pairing `e_N`, being additive in each variable, is `ZMod N`-linear
in each variable. This file records that linearity and packages `e_N` as a `ZMod N`-bilinear form
on `E[N]`, which is alternating and left-separating. This is the form in which linear algebra over
`ZMod N` applies to the Weil pairing.

The pairing is defined on `Submodule.torsionBy ℤ`, while the `ZMod N`-module structure is on
`AddSubgroup.torsionBy`, the same subtype of points. The statements here are made on the latter,
so that `c • S` is the `ZMod N`-action.

## Main definitions

* `TauCeti.Isogeny.weilPairingBilin`: the Weil pairing as a `ZMod N`-bilinear form on `E[N]`.

## Main results

* `TauCeti.Isogeny.weilPairing_zmod_smul_left` and `TauCeti.Isogeny.weilPairing_zmod_smul_right`:
  `e_N` is `ZMod N`-linear in each variable.
* `TauCeti.Isogeny.isAlt_weilPairingBilin`: the form is alternating.
* `TauCeti.Isogeny.separatingLeft_weilPairingBilin`: the form is left-separating.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1.
-/

public section

open WeierstrassCurve

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] [DecidableEq F] [IsSepClosed F] (W : WeierstrassCurve F)
  [W.IsElliptic] (N : ℕ) [NeZero N] (hN : (N : F) ≠ 0)

/-- **The Weil pairing is `ZMod N`-linear in its first variable.** -/
theorem weilPairing_zmod_smul_left (c : ZMod N)
    (S T : AddSubgroup.torsionBy W.toAffine.Point (N : ℤ)) :
    weilPairing W N hN (c • S) T = c • weilPairing W N hN S T := by
  rw [← AddMonoidHom.flip_apply, ZMod.map_smul (M := AddSubgroup.torsionBy W.toAffine.Point _),
    AddMonoidHom.flip_apply]

/-- **The Weil pairing is `ZMod N`-linear in its second variable.** -/
theorem weilPairing_zmod_smul_right (c : ZMod N)
    (S T : AddSubgroup.torsionBy W.toAffine.Point (N : ℤ)) :
    weilPairing W N hN S (c • T) = c • weilPairing W N hN S T :=
  ZMod.map_smul (M := AddSubgroup.torsionBy W.toAffine.Point _) _ c T

/-- **The Weil pairing as a `ZMod N`-bilinear form** on `E[N]`, over a separably closed field in
which `N` is invertible. -/
noncomputable def weilPairingBilin :
    AddSubgroup.torsionBy W.toAffine.Point (N : ℤ) →ₗ[ZMod N]
      AddSubgroup.torsionBy W.toAffine.Point (N : ℤ) →ₗ[ZMod N] Additive (rootsOfUnity N F) :=
  LinearMap.mk₂ (ZMod N) (fun S T ↦ weilPairing W N hN S T) (fun _ _ _ ↦ by simp)
    (weilPairing_zmod_smul_left W N hN) (fun _ _ _ ↦ map_add _ _ _)
    (weilPairing_zmod_smul_right W N hN)

/-- The bilinear form `weilPairingBilin` evaluates to the Weil pairing. -/
@[simp]
theorem weilPairingBilin_apply (S T : AddSubgroup.torsionBy W.toAffine.Point (N : ℤ)) :
    weilPairingBilin W N hN S T = weilPairing W N hN S T := by
  rw [weilPairingBilin, LinearMap.mk₂_apply]

/-- The Weil pairing, as a `ZMod N`-bilinear form, is alternating. -/
theorem isAlt_weilPairingBilin : (weilPairingBilin W N hN).IsAlt :=
  weilPairing_self W N hN

/-- The Weil pairing, as a `ZMod N`-bilinear form, is left-separating. -/
theorem separatingLeft_weilPairingBilin : (weilPairingBilin W N hN).SeparatingLeft :=
  fun _ hS ↦ weilPairing_nondegenerate W N hN hS

end TauCeti.Isogeny

end
