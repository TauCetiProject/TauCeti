/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Coordinatewise reduction modulo `k`

The reduction `ℤ ^ ι → (ℤ / k) ^ ι` of every coordinate modulo `k`, as a homomorphism of
additive groups. It is surjective, and its kernel consists of the multiples of `k`.

## Main definitions

* `TauCeti.ZMod.piReduction ι k`: the coordinatewise reduction `ℤ ^ ι → (ℤ / k) ^ ι`.

## Main results

* `TauCeti.ZMod.piReduction_surjective`: the reduction is surjective.
* `TauCeti.ZMod.mem_ker_piReduction_iff`: its kernel consists of the multiples of `k`.
-/

public section

namespace TauCeti

namespace ZMod

variable (ι : Type*) (k : ℕ)

/-- The coordinatewise reduction `ℤ ^ ι → (ℤ / k) ^ ι`. -/
def piReduction : (ι → ℤ) →+ (ι → ZMod k) :=
  (Int.castAddHom (ZMod k)).compLeft ι

/-- The reduction `ℤ ^ ι → (ℤ / k) ^ ι` reduces each coordinate modulo `k`. -/
@[simp]
theorem piReduction_apply (x : ι → ℤ) (i : ι) : piReduction ι k x i = (x i : ZMod k) :=
  (rfl)

/-- The reduction `ℤ ^ ι → (ℤ / k) ^ ι` is surjective. -/
theorem piReduction_surjective : Function.Surjective (piReduction ι k) :=
  Function.Surjective.piMap fun _ ↦ _root_.ZMod.intCast_surjective

/-- The kernel of the reduction `ℤ ^ ι → (ℤ / k) ^ ι` consists exactly of the multiples
of `k`. -/
theorem mem_ker_piReduction_iff (x : ι → ℤ) :
    x ∈ (piReduction ι k).ker ↔ ∃ y : ι → ℤ, x = (k : ℤ) • y := by
  rw [AddMonoidHom.mem_ker, funext_iff]
  simp only [piReduction_apply, Pi.zero_apply, _root_.ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro h
    choose y hy using h
    exact ⟨y, funext fun i ↦ by simpa using hy i⟩
  · rintro ⟨y, rfl⟩ i
    exact ⟨y i, by simp⟩

end ZMod

end TauCeti
