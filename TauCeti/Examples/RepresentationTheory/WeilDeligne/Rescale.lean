/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.WeilDeligne.Rescale

import Mathlib.Tactic.LinearCombination

/-!
# Checks for rescaling the monodromy

* `Sp(2)` is isomorphic to its rescaling by `2`, through `diag(1, 2)`.
* For `q = 1`, the parameter of `W = ℤ` on `E²` with `r(Φ) = 1 + N`, `N² = 0 ≠ N`, is not
  isomorphic to its rescaling by `2`: an automorphism commuting with `r` commutes with `N`.
-/

public section

namespace TauCeti.WeilDeligneParameter.RescaleChecks

open Module

variable {E W : Type*} [Field E] [Group W] [TopologicalSpace W] {deg : W →* Multiplicative ℤ}
  {q : ℕ}

/-- `Sp(2)` is isomorphic to its rescaling by `2` when `2 ≠ 0` in `E`. -/
noncomputable example (hdeg : Continuous deg) (hq : (q : E) ≠ 0) (h2 : (2 : E) ≠ 0) :
    Iso (special q 2 hdeg hq) ((special q 2 hdeg hq).rescale 2) :=
  specialRescaleIso q hdeg hq 2 (Units.mk0 2 h2)

/-- The unit `1 + N` of `End(E²)`, for the nilpotent shift `N`. -/
noncomputable def onePlusShift (E : Type*) [Field E] : (Module.End E (Fin 2 → E))ˣ :=
  (isNilpotent_finShift (R := E) 2).isUnit_one_add.unit

/-- The parameter of the discrete group `W = ℤ`, with `q = 1` and `deg = id`, on `E²`:
`r(m) = (1 + N) ^ m` and `N` the shift. -/
noncomputable def unipotentParameter (E : Type*) [Field E] :
    WeilDeligneParameter E (Multiplicative ℤ) (Fin 2 → E) (MonoidHom.id _) 1 where
  r := (Units.coeHom (Module.End E (Fin 2 → E))).comp (zpowersHom _ (onePlusShift E))
  isOpen_ker := isOpen_discrete _
  N := finShift E 2
  isNilpotent_N := isNilpotent_finShift 2
  conj_N w := by
    have hc : Commute ((onePlusShift E : (Module.End E (Fin 2 → E))ˣ) : Module.End E _)
        (finShift E 2) := by
      simp only [onePlusShift, IsUnit.unit_spec]
      exact (Commute.one_left _).add_left (Commute.refl _)
    simp only [MonoidHom.coe_comp, Function.comp_apply, zpowersHom_apply, Units.coeHom_apply,
      MonoidHom.id_apply, toAdd_inv, Nat.cast_one, one_zpow, one_smul]
    rw [(hc.units_zpow_left _).eq]
    simp [mul_assoc, ← Units.val_mul]

/-- For `q = 1`, `r(Φ) = 1 + N` with `N ≠ 0`: the parameter is not isomorphic to its rescaling
by `2`. -/
example : IsEmpty (Iso (unipotentParameter E) ((unipotentParameter E).rescale 2)) := by
  refine ⟨fun f ↦ ?_⟩
  have hN : (unipotentParameter E).N ≠ 0 := by
    intro h
    have := congr_fun (LinearMap.congr_fun h (Pi.single 0 1)) 1
    simp [unipotentParameter] at this
  have h1 := eq_one_of_iso_rescale (unipotentParameter E) (w := Multiplicative.ofAdd 1)
    (by simp [unipotentParameter, onePlusShift]) hN f
  exact one_ne_zero (by linear_combination h1 : (1 : E) = 0)

end TauCeti.WeilDeligneParameter.RescaleChecks
