/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.TateModule
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.IsSepClosed

/-!
# The Tate module of an elliptic curve

The torsion levels of an elliptic curve are finite.  Consequently the inverse-limit topology on
its Tate module is compact, Hausdorff, and totally disconnected.  Hausdorffness and total
disconnectedness hold for every `TauCeti.TateModule`; this file supplies the elliptic-curve input
needed for compactness.

Over a separably closed field in which the prime `ℓ` is invertible, the level `E[ℓ ^ n]` has
`(ℓ ^ n) ^ 2` elements, so the Tate module `T_ℓ E` is a free `ℤ_ℓ`-module of rank `2`
(Silverman III.7.1).  This is the module on which the `ℓ`-adic Galois representation and the
`ℓ`-adic Weil pairing of an elliptic curve live.

## Main results

* `WeierstrassCurve.natCard_tateModuleLevel`: `E[ℓ ^ n]` has `(ℓ ^ n) ^ 2` elements.
* `WeierstrassCurve.nonempty_linearEquiv_tateModule`: `T_ℓ E ≃ ℤ_ℓ²`.
* `WeierstrassCurve.free_tateModule`, `WeierstrassCurve.finite_tateModule`,
  `WeierstrassCurve.finrank_tateModule`: `T_ℓ E` is free and finitely generated of rank `2`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

public section

noncomputable section

open TauCeti

namespace WeierstrassCurve

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

open scoped Classical in
/-- The Tate module of an elliptic curve at a nonzero natural number is compact.  It is a closed
subgroup of the product of the finite torsion groups `E[p^n]`. -/
noncomputable instance instCompactSpaceTateModule (p : ℕ) [NeZero p] :
    CompactSpace (TateModule p W.toAffine.Point) := by
  let _ (n : ℕ) : Finite (TateModuleLevel p W.toAffine.Point n) :=
    W.finite_torsionBy (by exact_mod_cast pow_ne_zero n (NeZero.ne p))
  infer_instance

section IsSepClosed

variable [IsSepClosed K] {ℓ : ℕ}

open scoped Classical in
/-- Over a separably closed field in which `ℓ` is invertible, the `ℓ ^ n`-torsion of an elliptic
curve has `(ℓ ^ n) ^ 2` elements. -/
theorem natCard_tateModuleLevel (hℓ : (ℓ : K) ≠ 0) (n : ℕ) :
    Nat.card (TateModuleLevel ℓ W.toAffine.Point n) = (ℓ ^ n) ^ 2 := by
  have h := W.natCard_torsionBy (n := ((ℓ ^ n : ℕ) : ℤ)) (by simpa using pow_ne_zero n hℓ)
  rwa [Int.natAbs_natCast] at h

variable [Fact ℓ.Prime]

open scoped Classical in
/-- **The Tate module `T_ℓ E` is free of rank `2` over `ℤ_ℓ`**, over a separably closed field in
which the prime `ℓ` is invertible. The isomorphism is noncanonical, so the result asserts its
existence. -/
theorem nonempty_linearEquiv_tateModule (hℓ : (ℓ : K) ≠ 0) :
    Nonempty (TateModule ℓ W.toAffine.Point ≃ₗ[ℤ_[ℓ]] (Fin 2 → ℤ_[ℓ])) :=
  TateModule.nonempty_linearEquiv_of_natCard (W.natCard_tateModuleLevel hℓ)

open scoped Classical in
/-- The Tate module `T_ℓ E` is a free `ℤ_ℓ`-module, over a separably closed field in which the
prime `ℓ` is invertible. -/
theorem free_tateModule (hℓ : (ℓ : K) ≠ 0) :
    Module.Free ℤ_[ℓ] (TateModule ℓ W.toAffine.Point) :=
  TateModule.free_of_natCard (W.natCard_tateModuleLevel hℓ)

open scoped Classical in
/-- The Tate module `T_ℓ E` is a finitely generated `ℤ_ℓ`-module, over a separably closed field in
which the prime `ℓ` is invertible. -/
theorem finite_tateModule (hℓ : (ℓ : K) ≠ 0) :
    Module.Finite ℤ_[ℓ] (TateModule ℓ W.toAffine.Point) :=
  TateModule.finite_of_natCard (W.natCard_tateModuleLevel hℓ)

open scoped Classical in
/-- The Tate module `T_ℓ E` has rank `2` over `ℤ_ℓ`, over a separably closed field in which the
prime `ℓ` is invertible. -/
theorem finrank_tateModule (hℓ : (ℓ : K) ≠ 0) :
    Module.finrank ℤ_[ℓ] (TateModule ℓ W.toAffine.Point) = 2 :=
  TateModule.finrank_eq_of_natCard (W.natCard_tateModuleLevel hℓ)

end IsSepClosed

end WeierstrassCurve

end
