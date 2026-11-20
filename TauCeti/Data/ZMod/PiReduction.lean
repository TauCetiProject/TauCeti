/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Coordinatewise reduction modulo `k`

The reduction `ℤ ^ ι → (ℤ / k) ^ ι` of every coordinate modulo `k`, written multiplicatively so
that it is a homomorphism of commutative groups `Multiplicative (ι → ℤ) →* Multiplicative
(ι → ZMod k)`. It is surjective, and its kernel consists of `k`-th powers.

## Main definitions

* `TauCeti.ZMod.piReduction ι k`: the coordinatewise reduction `ℤ ^ ι → (ℤ / k) ^ ι`.

## Main results

* `TauCeti.ZMod.piReduction_surjective`: the reduction is surjective.
* `TauCeti.ZMod.ker_piReduction_le`: its kernel consists of `k`-th powers.
-/

public section

namespace TauCeti

namespace ZMod

variable (ι : Type*) (k : ℕ)

/-- The coordinatewise reduction `ℤ ^ ι → (ℤ / k) ^ ι`, written multiplicatively. -/
def piReduction : Multiplicative (ι → ℤ) →* Multiplicative (ι → ZMod k) :=
  AddMonoidHom.toMultiplicative ((Int.castAddHom (ZMod k)).compLeft ι)

/-- The reduction `ℤ ^ ι → (ℤ / k) ^ ι` reduces each coordinate modulo `k`. -/
@[simp]
theorem piReduction_apply (x : Multiplicative (ι → ℤ)) (i : ι) :
    (piReduction ι k x).toAdd i = (x.toAdd i : ZMod k) :=
  (rfl)

/-- The reduction `ℤ ^ ι → (ℤ / k) ^ ι` is surjective. -/
theorem piReduction_surjective : Function.Surjective (piReduction ι k) :=
  Function.Surjective.piMap fun _ ↦ _root_.ZMod.intCast_surjective

/-- The kernel of the reduction `ℤ ^ ι → (ℤ / k) ^ ι` consists of the `k`-th powers. -/
theorem ker_piReduction_le :
    (piReduction ι k).ker ≤ (powMonoidHom k : Multiplicative (ι → ℤ) →* _).range := by
  intro x hx
  have hdvd (i : ι) : (k : ℤ) ∣ x.toAdd i := by
    rw [← _root_.ZMod.intCast_zmod_eq_zero_iff_dvd, ← piReduction_apply]
    exact congrFun (congrArg Multiplicative.toAdd hx) i
  choose y hy using hdvd
  refine ⟨Multiplicative.ofAdd y, ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  simp [hy i]

end ZMod

end TauCeti
