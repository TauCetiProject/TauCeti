/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Decomposition
public import TauCeti.Algebra.Lie.Solvable.Basic
import TauCeti.Algebra.Lie.Reductive.Decomposition

/-!
# Reductive splitting of the Cartan `-1`-eigenspace

When the centre `Z(L)` and derived ideal `[L, L]` of a Lie algebra `L` are complementary, any
automorphism `θ` restricts to automorphisms `θ.centerCongr` on `Z(L)` and
`θ.derivedSeriesCongr 1` on `[L, L]`. Addition identifies the product of their `-1`-eigenspaces
with `θ.cartanP`, independently of any Cartan-involution predicate.

## Main definitions

* `LieEquiv.cartanPCenterDerivedEquiv`: linear splitting of `θ.cartanP` into its central and
  derived components when `L = Z(L) ⊕ [L, L]`.

## Main results

* `LieEquiv.coe_cartanPCenterDerivedEquiv_apply`: `cartanPCenterDerivedEquiv` acts by addition
  in `L`.
-/

public section

open LieAlgebra

namespace LieEquiv

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- When `L = Z(L) ⊕ [L, L]`, addition identifies the product of the `-1`-eigenspaces on `Z(L)` and
`[L, L]` with `θ.cartanP`. -/
noncomputable def cartanPCenterDerivedEquiv (θ : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1)) :
    (θ.centerCongr.cartanP × (θ.derivedSeriesCongr 1).cartanP) ≃ₗ[R] θ.cartanP :=
  (((LinearEquiv.ofEq _ _ (cartanP_eq_eigenspace θ.centerCongr)).prodCongr
      (LinearEquiv.ofEq _ _ (cartanP_eq_eigenspace (θ.derivedSeriesCongr 1)))).trans
    (θ.eigenspaceCenterDerivedEquiv h (-1))).trans
    (LinearEquiv.ofEq _ _ (cartanP_eq_eigenspace θ).symm)

/-- `cartanPCenterDerivedEquiv` acts by addition in `L`. -/
@[simp]
theorem coe_cartanPCenterDerivedEquiv_apply (θ : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1))
    (p : θ.centerCongr.cartanP × (θ.derivedSeriesCongr 1).cartanP) :
    (θ.cartanPCenterDerivedEquiv h p : L) = (p.1.val : L) + (p.2.val : L) := by
  unfold cartanPCenterDerivedEquiv
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    coe_eigenspaceCenterDerivedEquiv_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.coe_ofEq_apply, LinearEquiv.coe_ofEq_apply]

end LieEquiv
