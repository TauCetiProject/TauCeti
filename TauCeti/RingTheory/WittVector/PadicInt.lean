/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Compare

/-!
# The `p`-adic integers in Witt vectors of characteristic `p` rings

For a commutative ring `k` of characteristic `p`, the unique ring map `𝔽ₚ → k` induces on Witt
vectors a ring map `ℤₚ ≅ W(𝔽ₚ) → W(k)`. It is injective, so `W(k)` has characteristic zero.

## Main definitions

* `WittVector.padicIntToWitt`: the ring map `ℤₚ → W(k)` induced by `𝔽ₚ → k`.

## Main results

* `WittVector.padicIntToWitt_injective`: the ring map `ℤₚ → W(k)` is injective.
* `WittVector.instCharZero`: Witt vectors of a ring of characteristic `p` have characteristic
  zero.
-/

public section

namespace WittVector

variable (p : ℕ) [Fact p.Prime] (k : Type*) [CommRing k] [CharP k p]

/-- The ring map `ℤₚ ≅ W(𝔽ₚ) → W(k)` to the Witt vectors of a ring `k` of characteristic `p`,
induced on Witt vectors by the ring map `𝔽ₚ → k`. -/
noncomputable def padicIntToWitt : ℤ_[p] →+* WittVector p k :=
  (map (ZMod.castHom dvd_rfl k)).comp (fromPadicInt p)

/-- The ring map `ℤₚ → W(k)` to the Witt vectors of a ring `k` of characteristic `p` is
injective. -/
theorem padicIntToWitt_injective : Function.Injective (padicIntToWitt p k) :=
  have := CharP.nontrivial_of_char_ne_one (R := k) (Fact.out : p.Prime).one_lt.ne'
  (map_injective _ (ZMod.castHom dvd_rfl k).injective).comp (WittVector.equiv p).symm.injective

/-- The Witt vectors of a ring of characteristic `p` have characteristic zero, since `ℤₚ` injects
into them. -/
instance instCharZero : CharZero (WittVector p k) :=
  charZero_of_injective_ringHom (padicIntToWitt_injective p k)

end WittVector
