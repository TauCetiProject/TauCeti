/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.WittVector.Primitive.Torsion

/-!
# Checks for `p`-power torsion modulo a distinguished Witt vector

Let `S` be a perfect ring of characteristic `p`.

* For `ξ = p`, whose first Witt coordinate is `1`, the divisibility statement reads
  `p ^ 2 ∣ p g → p ∣ g`, and every element of `𝕎 S ⧸ (p)` is `p`-power torsion.
* The hypothesis that `ξ₁` is a unit cannot be dropped: in `𝕎 𝔽₂ ⧸ (4)` the class of `1` is killed
  by `4` but not by `2`, and the first Witt coordinate of `4` is `0`.
-/

open Ideal WittVector

namespace TauCeti.Examples

section Perfect

variable {p : ℕ} [hp : Fact p.Prime] {S : Type*} [CommRing S] [CharP S p] [PerfectRing S p]

-- For `ξ = p`: `p ^ 2 ∣ p g` implies `p ∣ g`.
example (g : WittVector p S) (h : (p : WittVector p S) ^ 2 ∣ p * g) : (p : WittVector p S) ∣ g :=
  isDistinguished_p.p_dvd_of_p_sq_dvd_mul h

-- For `ξ = p`: every element of `𝕎 S ⧸ (p)` is `p`-power torsion.
example (x : WittVector p S ⧸ span {(p : WittVector p S)}) :
    x ∈ Submodule.torsion' (WittVector p S ⧸ span {(p : WittVector p S)})
      (WittVector p S ⧸ span {(p : WittVector p S)})
      (Submonoid.powers (p : WittVector p S ⧸ span {(p : WittVector p S)})) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [isDistinguished_p.torsion'_powers_eq_torsionBy, Submodule.mem_torsionBy_iff, smul_eq_mul,
    ← map_natCast (Ideal.Quotient.mk _) p, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact mul_mem_right _ _ (mem_span_singleton_self _)

end Perfect

-- The generator `4` of `𝕎 𝔽₂` is not distinguished: it lies in `(2 ^ 2)`.
example : ¬ (4 : WittVector 2 (ZMod 2)).IsDistinguished :=
  not_isDistinguished_of_mem_span_p_sq (mem_span_singleton.mpr ⟨1, by norm_num⟩)

-- In `𝕎 𝔽₂ ⧸ (4)` the class of `1` is killed by `4` but not by `2`.
example : (4 : WittVector 2 (ZMod 2) ⧸ span {(4 : WittVector 2 (ZMod 2))}) * 1 = 0 ∧
    (2 : WittVector 2 (ZMod 2) ⧸ span {(4 : WittVector 2 (ZMod 2))}) * 1 ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rw [mul_one, ← map_ofNat (Ideal.Quotient.mk _) 4, Ideal.Quotient.eq_zero_iff_mem]
    exact mem_span_singleton_self _
  · rw [mul_one, ← map_ofNat (Ideal.Quotient.mk _) 2, Ne, Ideal.Quotient.eq_zero_iff_mem,
      show (4 : WittVector 2 (ZMod 2)) = ((2 : ℕ) : WittVector 2 (ZMod 2)) ^ 2 by norm_num,
      show (2 : WittVector 2 (ZMod 2)) = ((2 : ℕ) : WittVector 2 (ZMod 2)) by norm_num,
      mem_span_p_pow_iff_le_coeff_eq_zero]
    intro h
    exact one_ne_zero (coeff_p_one (p := 2) (R := ZMod 2) ▸ h 1 one_lt_two)

end TauCeti.Examples
