/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.GaloisRepresentation.Unramified.WeilCharacter
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Checks: unramified characters of the Weil group

The unramified Weil character is defined for every `α`: on `W_K` there is a continuous character
sending an arithmetic Frobenius lift to `p ∈ ℚ_pˣ`, although no continuous character of `G_K`
into `ℚ_pˣ` does, since a continuous character of a compact group into `ℚ_pˣ` has values of
norm `1`. It is trivial on inertia.
-/

open TauCeti TauCeti.GaloisRep TauCeti.ClassFieldTheory ValuativeRel

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Some arithmetic Frobenius lift in `W_K` is sent to `p` by the unramified Weil character of
`p ∈ ℚ_pˣ`. -/
example (p : ℕ) [Fact p.Prime] (hp : (p : ℚ_[p]) ≠ 0) :
    ∃ w : WeilGroup K, IsArithFrobeniusLift K (weilToAbsolute K w) ∧
      weilUnramifiedCharacter K (Units.mk0 (p : ℚ_[p]) hp) w = Units.mk0 (p : ℚ_[p]) hp := by
  obtain ⟨w, hw⟩ := surjective_weilDegree K (Multiplicative.ofAdd 1)
  have hw' := weilDegree_eq_ofAdd_one_iff.1 hw
  exact ⟨w, hw', weilUnramifiedCharacter_apply_of_isArithFrobeniusLift _ hw'⟩

/-- The unramified Weil character is trivial on inertia. -/
example (p : ℕ) [Fact p.Prime] (hp : (p : ℚ_[p]) ≠ 0) (w : WeilGroup K)
    (hw : weilToAbsolute K w ∈ inertiaSubgroup K) :
    weilUnramifiedCharacter K (Units.mk0 (p : ℚ_[p]) hp) w = 1 :=
  weilUnramifiedCharacter_apply_of_mem_inertiaSubgroup _ hw
