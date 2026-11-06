/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.Data.ZMod.Units
public import Mathlib.Topology.Instances.ZMod
import TauCeti.NumberTheory.Cyclotomic.FixingSubgroup
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Compatibility of finite cyclotomic characters

The action on roots of unity is compatible with reduction of the exponent modulo a divisor
of the level. On a Galois group, each finite cyclotomic character is continuous for the Krull
topology. Together these facts allow the finite characters to be assembled into a continuous
character with values in the units of the profinite integers.

The finite characters and their characterizing power equations are Mathlib's
`modularCyclotomicCharacter` and `IsPrimitiveRoot.autToPow`.
-/

public section

namespace modularCyclotomicCharacter

variable {L : Type*} [CommRing L] [IsDomain L] {m n : ℕ} [NeZero m] [NeZero n]

/-- Reducing a cyclotomic character modulo a divisor gives the character at that level. -/
theorem unitsMap (h : m ∣ n)
    (hm : Nat.card (rootsOfUnity m L) = m) (hn : Nat.card (rootsOfUnity n L) = n)
    (g : L ≃+* L) :
    ZMod.unitsMap h (modularCyclotomicCharacter L hn g) =
      modularCyclotomicCharacter L hm g := by
  apply Units.ext
  apply modularCyclotomicCharacter.unique L hm g
  intro t ht
  have htn : t ∈ rootsOfUnity n L := by
    rcases h with ⟨k, rfl⟩
    rw [mem_rootsOfUnity] at ht ⊢
    rw [pow_mul, ht, one_pow]
  rw [modularCyclotomicCharacter.spec L hn g htn]
  apply pow_eq_pow_of_modEq (n := m) ?_ ((mem_rootsOfUnity' _ _).mp ht)
  apply (ZMod.natCast_eq_natCast_iff _ _ m).mp
  simp only [ZMod.natCast_zmod_val, ZMod.unitsMap_val]
  exact (ZMod.cast_eq_val _).symm

/-- The finite cyclotomic character on a Galois group is continuous in the Krull topology. -/
theorem continuous {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ} [NeZero n]
    (hn : Nat.card (rootsOfUnity n L) = n) :
    Continuous ((modularCyclotomicCharacter L hn).comp
      (MulSemiringAction.toRingAut Gal(L/K) L)) := by
  obtain ⟨ζ, hζ⟩ := card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot.mp hn
  have heq : (modularCyclotomicCharacter L hn).comp
      (MulSemiringAction.toRingAut Gal(L/K) L) = hζ.autToPow K := by
    ext g
    exact congrArg Units.val (hζ.autToPow_eq_modularCyclotomicCharacter n K g).symm
  rw [heq]
  exact (hζ.autToPow K).continuous_of_isOpen_ker hζ.isOpen_ker_autToPow

end modularCyclotomicCharacter
