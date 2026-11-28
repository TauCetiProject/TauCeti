/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Tame
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Norm-one twists with varying modulus

A family of theta lifts indexed by twists uses one common index type, even though the finite
modulus of the character varies. The first `m` positive powers of an `m`-fold twist retain the
same residue support. In particular the primes allowed for testing integrality are unchanged
when passing from a twist to any of those powers.

The modulus and power conventions follow `New.Data.MFoldTwist` and
`New.Data.MFoldTwist.powTwist` in `New/Reduction/Data/LevelAndTwists.lean` of lsernau/grh-lean
(commit `72fead1`).
-/

public section

open IsDedekindDomain NumberField

namespace TauCeti.GlobalNumberFields

/-- An `m`-fold norm-one twist at level `M`, with its own finite modulus. The datum includes
both the global character and the local residue characters on that modulus. -/
@[ext]
structure MFoldTwist (L : Type*) [Field L] [NumberField L] [IsCMField L] (M m : ℕ) where
  /-- The finite places at which the residue characters are specified. -/
  modulus : Finset (HeightOneSpectrum (𝓞 L))
  /-- The weight-zero automorphic character and its residue characters. -/
  toTameCharacter : NormOneTameCharacter (maximalRealSubfield L) L modulus
  /-- The modulus is permitted at level `M`, and the first `m` positive powers are nontrivial
  at every place in the modulus. -/
  isMFoldTwist : toTameCharacter.IsMFoldTwist M m

namespace MFoldTwist

variable {L : Type*} [Field L] [NumberField L] [IsCMField L] {M m : ℕ}

/-- The norm of the twist modulus, the product of the residue-field sizes. -/
noncomputable def modulusNorm (ξ : MFoldTwist L M m) : ℕ :=
  ∏ w ∈ ξ.modulus, w.asIdeal.absNorm

/-- Compute the modulus norm by multiplying the norms of its places. -/
theorem modulusNorm_def (ξ : MFoldTwist L M m) :
    ξ.modulusNorm = ∏ w ∈ ξ.modulus, w.asIdeal.absNorm := (rfl)

/-- The modulus norm is positive, including for the empty modulus. -/
theorem modulusNorm_pos (ξ : MFoldTwist L M m) : 0 < ξ.modulusNorm := by
  rw [ξ.modulusNorm_def]
  exact Finset.prod_pos fun w _ ↦ Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr w.ne_bot)

/-- The modulus norm is prime to the level. -/
theorem coprime_modulusNorm_level (ξ : MFoldTwist L M m) : ξ.modulusNorm.Coprime M := by
  rw [ξ.modulusNorm_def]
  have hQ := (NormOneTameCharacter.isMFoldTwist_iff.mp ξ.isMFoldTwist).1
  exact ((isTwistModulus_iff M).mp hQ).2

/-- The twist is allowed in an integrality test at `ℓ` if its modulus norm is prime to `ℓ`. -/
def AllowedAt (ξ : MFoldTwist L M m) (ℓ : ℕ) : Prop := ξ.modulusNorm.Coprime ℓ

/-- An allowed twist has modulus norm coprime to the testing integer, and conversely. -/
theorem allowedAt_iff_coprime (ξ : MFoldTwist L M m) (ℓ : ℕ) :
    ξ.AllowedAt ℓ ↔ ξ.modulusNorm.Coprime ℓ := (Iff.rfl)

/-- A twist is allowed precisely when each residue-field size in its modulus is prime to `ℓ`. -/
theorem allowedAt_iff (ξ : MFoldTwist L M m) (ℓ : ℕ) :
    ξ.AllowedAt ℓ ↔ ∀ w ∈ ξ.modulus, w.asIdeal.absNorm.Coprime ℓ := by
  rw [ξ.allowedAt_iff_coprime, ξ.modulusNorm_def, Nat.coprime_prod_left_iff]

/-- The trivial twist has empty modulus, trivial character, and arbitrary chain length. -/
noncomputable instance : One (MFoldTwist L M m) :=
  ⟨⟨∅, 1, NormOneTameCharacter.isMFoldTwist_one_empty M m⟩⟩

/-- The trivial twist has empty modulus. -/
@[simp] theorem modulus_one : (1 : MFoldTwist L M m).modulus = ∅ := (rfl)

/-- The underlying tame character of the trivial twist is trivial. -/
@[simp] theorem toTameCharacter_one :
    (1 : MFoldTwist L M m).toTameCharacter = 1 := (rfl)

/-- The trivial twist has modulus norm one. -/
@[simp] theorem modulusNorm_one : (1 : MFoldTwist L M m).modulusNorm = 1 := by
  simp [modulusNorm_def]

/-- The trivial twist is allowed at every testing integer. -/
@[simp] theorem allowedAt_one (ℓ : ℕ) : (1 : MFoldTwist L M m).AllowedAt ℓ := by
  simp [allowedAt_iff]

/-- The `j`-th positive power is a `k`-fold twist at the same modulus if `j * k ≤ m`. In
particular it is a twist when `1 ≤ j ≤ m`, by taking `k = 1`. -/
noncomputable def pow (ξ : MFoldTwist L M m) (j : ℕ) {k : ℕ}
    (hj : 0 < j) (hjk : j * k ≤ m) : MFoldTwist L M k where
  modulus := ξ.modulus
  toTameCharacter := ξ.toTameCharacter ^ j
  isMFoldTwist := by
    obtain ⟨hQ, hξ⟩ := NormOneTameCharacter.isMFoldTwist_iff.mp ξ.isMFoldTwist
    refine NormOneTameCharacter.isMFoldTwist_iff.mpr ⟨hQ, fun w n hn ↦ ?_⟩
    obtain ⟨hn₁, hn₂⟩ := Finset.mem_Icc.mp hn
    simpa only [NormOneTameCharacter.residueCharacter_pow, ← pow_mul] using
      hξ w (j * n) (Finset.mem_Icc.mpr
        ⟨Nat.mul_pos hj hn₁, (Nat.mul_le_mul_left j hn₂).trans hjk⟩)

/-- A permitted power retains the original twist modulus. -/
@[simp] theorem modulus_pow (ξ : MFoldTwist L M m) (j : ℕ) {k : ℕ}
    (hj : 0 < j) (hjk : j * k ≤ m) : (ξ.pow j hj hjk).modulus = ξ.modulus := (rfl)

/-- The global character of a permitted power is the pointwise power. -/
@[simp] theorem toContinuousMonoidHom_pow (ξ : MFoldTwist L M m) (j : ℕ) {k : ℕ}
    (hj : 0 < j) (hjk : j * k ≤ m) :
    (ξ.pow j hj hjk).toTameCharacter.toContinuousMonoidHom =
      ξ.toTameCharacter.toContinuousMonoidHom ^ j := by
  simp [pow]

/-- At every finite place, the residue character of a permitted power is the pointwise power. -/
@[simp] theorem residueCharacterAt_pow (ξ : MFoldTwist L M m) (j : ℕ) {k : ℕ}
    (hj : 0 < j) (hjk : j * k ≤ m) (w : HeightOneSpectrum (𝓞 L)) :
    (ξ.pow j hj hjk).toTameCharacter.residueCharacterAt w =
      ξ.toTameCharacter.residueCharacterAt w ^ j := by
  simp [pow]

/-- A permitted power retains the modulus norm. -/
@[simp] theorem modulusNorm_pow (ξ : MFoldTwist L M m) (j : ℕ) {k : ℕ}
    (hj : 0 < j) (hjk : j * k ≤ m) : (ξ.pow j hj hjk).modulusNorm = ξ.modulusNorm := by
  simp [modulusNorm_def]

/-- Testing integrality at `ℓ` allows a permitted power exactly when it allows the original
 twist. -/
@[simp] theorem allowedAt_pow (ξ : MFoldTwist L M m) (j : ℕ) {k ℓ : ℕ}
    (hj : 0 < j) (hjk : j * k ≤ m) : (ξ.pow j hj hjk).AllowedAt ℓ ↔ ξ.AllowedAt ℓ := by
  simp [allowedAt_iff_coprime]

/-- At each of the first `m` positive powers the nontrivial residue characters have support
exactly the specified modulus. -/
theorem mem_modulus_iff_residueCharacterAt_pow_ne_one (ξ : MFoldTwist L M m)
    (w : HeightOneSpectrum (𝓞 L)) {j : ℕ} (hj : j ∈ Finset.Icc 1 m) :
    w ∈ ξ.modulus ↔ ξ.toTameCharacter.residueCharacterAt w ^ j ≠ 1 := by
  by_cases hw : w ∈ ξ.modulus
  · simp only [hw, NormOneTameCharacter.residueCharacterAt_of_mem, true_iff]
    exact (NormOneTameCharacter.isMFoldTwist_iff.mp ξ.isMFoldTwist).2 ⟨w, hw⟩ j hj
  · simp [hw]

end MFoldTwist

end TauCeti.GlobalNumberFields
