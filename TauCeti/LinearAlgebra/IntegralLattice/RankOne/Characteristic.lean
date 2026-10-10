/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.RankOne.Basic
import Mathlib.Algebra.Ring.Int.Parity

/-!
# Characteristic vectors of two rank-one lattices

In the odd unimodular lattice `⟨1⟩`, characteristic vectors are exactly the odd integers
in its actual carrier, and their integral norms are one modulo eight. In `⟨2⟩`, every
vector is characteristic but every integral norm is even, so the characteristic-norm
congruence with the signature fails for every vector. The latter example shows why
unimodularity is required in van der Blij's theorem.

## References

* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Appendix 4.
-/

public section

namespace TauCeti.IntegralLattice

/-- The characteristic vectors of `⟨1⟩` are exactly its odd integer vectors. -/
theorem isCharacteristicVector_rankOne_one_iff (w : rankOne 1) :
    (rankOne 1).IsCharacteristicVector w ↔ ∃ k : ℤ, Odd k ∧ (k : ℚ) = w := by
  rw [(rankOne 1).isCharacteristicVector_iff]
  obtain ⟨k, hk⟩ := (mem_rankOne_carrier_iff 1 (w : ℚ)).mp w.property
  constructor
  · intro hw
    refine ⟨k, ?_, hk⟩
    let x : rankOne 1 := ⟨1, (mem_rankOne_carrier_iff 1 1).mpr ⟨1, by norm_num⟩⟩
    have hx : (x : ℚ) = (1 : ℤ) := rfl
    have h := hw x
    rw [integralForm_rankOne_eq w x hk.symm hx, integralNorm_rankOne_eq x hx] at h
    simp only [one_mul, mul_one, one_pow] at h
    rw [Int.modEq_iff_dvd] at h
    apply Int.odd_iff.mpr
    omega
  · rintro ⟨k, hk, hkw⟩ x
    obtain ⟨l, hl⟩ := (mem_rankOne_carrier_iff 1 (x : ℚ)).mp x.property
    rw [integralForm_rankOne_eq w x hkw.symm hl.symm, integralNorm_rankOne_eq x hl.symm]
    simp only [one_mul]
    rw [Int.modEq_iff_dvd]
    obtain ⟨m, rfl⟩ := hk
    obtain ⟨c, hc⟩ := Int.two_dvd_mul_add_one l
    refine ⟨c - (m + 1) * l, ?_⟩
    nlinarith

/-- A characteristic vector of the odd unimodular lattice `⟨1⟩` has norm one modulo eight. -/
theorem integralNorm_rankOne_one_modEq_one (w : rankOne 1)
    (hw : (rankOne 1).IsCharacteristicVector w) :
    (rankOne 1).integralNorm w ≡ 1 [ZMOD 8] := by
  obtain ⟨k, hk, hkw⟩ := (isCharacteristicVector_rankOne_one_iff w).mp hw
  rw [integralNorm_rankOne_eq w hkw.symm, one_mul, Int.modEq_iff_dvd]
  simpa only [neg_sub] using dvd_neg.mpr (Int.eight_dvd_sq_sub_one_of_odd hk)

/-- Every vector of `⟨2⟩` is characteristic, since all its integral pairings are even. -/
@[simp]
theorem isCharacteristicVector_rankOne_two (w : rankOne 2) :
    (rankOne 2).IsCharacteristicVector w := by
  rw [(rankOne 2).isCharacteristicVector_iff]
  obtain ⟨k, hk⟩ := (mem_rankOne_carrier_iff 2 (w : ℚ)).mp w.property
  intro x
  obtain ⟨l, hl⟩ := (mem_rankOne_carrier_iff 2 (x : ℚ)).mp x.property
  rw [integralForm_rankOne_eq w x hk.symm hl.symm, integralNorm_rankOne_eq x hl.symm,
    Int.modEq_iff_dvd]
  exact ⟨l ^ 2 - k * l, by ring⟩

/-- No vector of `⟨2⟩` satisfies van der Blij's signature congruence: every norm is even,
whereas the signature difference is one. This includes every characteristic vector. -/
@[simp]
theorem not_integralNorm_rankOne_two_modEq_signature (w : rankOne 2) :
    ¬ (rankOne 2).integralNorm w ≡
      ((rankOne 2).sigPos : ℤ) - (rankOne 2).sigNeg [ZMOD 8] := by
  obtain ⟨k, hk⟩ := (mem_rankOne_carrier_iff 2 (w : ℚ)).mp w.property
  have hs := rankOne_signature_of_pos (by norm_num : (0 : ℤ) < 2)
  simp only [signature, Prod.mk.injEq] at hs
  rw [integralNorm_rankOne_eq w hk.symm, hs.1, hs.2.2]
  simp only [Nat.cast_one, Nat.cast_zero, sub_zero, Int.modEq_iff_dvd]
  omega

end TauCeti.IntegralLattice
