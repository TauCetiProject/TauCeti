/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.PowIterate
public import Mathlib.Topology.Homeomorph.Defs
import TauCeti.GroupTheory.Perm.Basic

/-!
# Semiconjugacy of homeomorphisms

This file records that the group operations on `X ≃ₜ X` act on points as the identity and
composition (the `IsOneApplyEqSelf` and `IsMulApplyEqComp` instances), so that natural powers of
homeomorphisms are iterates, and relates integer powers of homeomorphisms to integer powers of
their underlying permutations. In particular, a map
intertwining two homeomorphisms also intertwines all of their integer powers.

## Main declarations

* The `IsOneApplyEqSelf` and `IsMulApplyEqComp` instances for `X ≃ₜ X`: the unit acts as the
  identity and the product as composition.
* `Homeomorph.coe_pow`: the underlying function of a natural power of a homeomorphism is the
  corresponding iterate.
* `Homeomorph.coe_zpow`: the underlying function of a power of a homeomorphism is the underlying
  function of the corresponding power of its underlying equivalence.
* `Function.Semiconj.homeomorph_zpow_right`: semiconjugacy of homeomorphisms is preserved by
  integer powers.
-/

public section

namespace Homeomorph

variable {X : Type*} [TopologicalSpace X]

instance : IsOneApplyEqSelf (X ≃ₜ X) where

instance : IsMulApplyEqComp (X ≃ₜ X) where

/-- The underlying function of the `n`-th power of a homeomorphism is its `n`-th iterate. -/
@[simp]
theorem coe_pow (f : X ≃ₜ X) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  FunLike.coe_pow_eq_iterate f n

/-- The underlying function of an integer power of a homeomorphism is the underlying function of
the corresponding power of its underlying equivalence. -/
theorem coe_zpow (f : X ≃ₜ X) (n : ℤ) : ⇑(f ^ n) = ⇑(f.toEquiv ^ n) :=
  congrArg DFunLike.coe
    (map_zpow (MonoidHom.mk' (Homeomorph.toEquiv (X := X) (Y := X)) fun _ _ ↦ rfl) f n)

end Homeomorph

namespace Function.Semiconj

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A map intertwining two homeomorphisms also intertwines all of their integer powers. -/
theorem homeomorph_zpow_right {f : X ≃ₜ X} {g : Y ≃ₜ Y} {u : X → Y}
    (h : Function.Semiconj u f g) (n : ℤ) :
    Function.Semiconj u ⇑(f ^ n) ⇑(g ^ n) := by
  rw [Homeomorph.coe_zpow, Homeomorph.coe_zpow]
  exact h.perm_zpow_right n

end Function.Semiconj
