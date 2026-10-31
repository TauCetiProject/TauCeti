/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FormalGroup.Basic

/-!
# Base change of formal group laws

Mathlib constructs the base change `F.map f` of a formal group law by applying `f` to every
coefficient. This file supplies its basic functorial API: identity and composition laws,
preservation of commutativity, and compatibility with the additive and multiplicative formal
group laws.

## Main results

* `FormalGroup.map_id` and `FormalGroup.map_comp`: base change is functorial.
* `FormalGroup.isComm_map`: base change preserves commutativity.
* `FormalGroup.map_𝔾ₐ` and `FormalGroup.map_𝔾ₘ`: the standard laws are stable under base change.
* `FormalGroup.subst_map_toPowerSeries_map`: a power series additive along `F` stays additive along
  `F` after base change.
-/

public section

open MvPowerSeries

namespace FormalGroup

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- Base-changing a formal group law along the identity homomorphism changes nothing. -/
@[simp]
theorem map_id (F : FormalGroup R) : F.map (RingHom.id R) = F := by
  ext
  simp

/-- Successive base changes of a formal group law agree with base change along the composite. -/
@[simp]
theorem map_comp (F : FormalGroup R) (f : R →+* S) (g : S →+* T) :
    (F.map f).map g = F.map (g.comp f) := by
  ext
  simp

/-- A base change of a commutative formal group law is commutative. -/
instance isComm_map (F : FormalGroup R) [F.IsComm] (f : R →+* S) : (F.map f).IsComm where
  comm := by
    have h := congrArg (MvPowerSeries.map f) (IsComm.comm (F := F))
    rw [MvPowerSeries.map_subst HasSubst.X_X] at h
    rw [map_toPowerSeries]
    calc
      _ = subst (fun i ↦ MvPowerSeries.map f (![X 1, X 0] i))
          (MvPowerSeries.map f F.toPowerSeries) := h
      _ = _ := by
        congr 1
        funext i
        fin_cases i <;> simp

/-- The additive formal group law is unchanged by base change. -/
@[simp]
theorem map_𝔾ₐ (f : R →+* S) : (𝔾ₐ (R := R)).map f = 𝔾ₐ := by
  ext
  simp [FormalGroup.𝔾ₐ]

/-- The multiplicative formal group law is unchanged by base change. -/
@[simp]
theorem map_𝔾ₘ (f : R →+* S) : (𝔾ₘ (R := R)).map f = 𝔾ₘ := by
  ext
  simp [FormalGroup.𝔾ₘ]

/-- A power series additive along `F` stays additive along `F` after base change. -/
theorem subst_map_toPowerSeries_map (F : FormalGroup R) (f : R →+* S) {g : PowerSeries R}
    (hg : PowerSeries.subst F.toPowerSeries g =
      PowerSeries.subst (X 0) g + PowerSeries.subst (X 1) g) :
    PowerSeries.subst (F.map f).toPowerSeries (g.map f) =
      PowerSeries.subst (X 0) (g.map f) + PowerSeries.subst (X 1) (g.map f) := by
  have := congrArg (MvPowerSeries.map f) hg
  rwa [map_add, PowerSeries.map_subst (.of_constantCoeff_zero F.zero_constantCoeff),
    PowerSeries.map_subst (.X 0), PowerSeries.map_subst (.X 1), map_X, map_X,
    ← map_toPowerSeries] at this

end FormalGroup
