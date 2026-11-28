/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.NumberTheory.NumberField.Cyclotomic.RealSubfield
import TauCeti.Algebra.Group.Subgroup.ZPowers
import TauCeti.Data.ZMod.DyadicOrder
import TauCeti.Data.ZMod.Units
import TauCeti.NumberTheory.Harmonic.SignClasses

/-!
# Logarithmic prime weight of short signed Frobenius orbits

When a cyclotomic subextension contains the real part of a large dyadic layer,
short signed Frobenius orbits restrict the eligible primes to two sparse residue
classes at a lower layer. The resulting logarithmic harmonic bound supplies the
cost of discarding these short orbits in a theta-chain loss estimate. The restriction
argument is the dyadic cyclotomic one (Washington, *Introduction to Cyclotomic Fields*,
Chapter 3).
-/

public section

open IntermediateField NumberField _root_.IsCyclotomicExtension.Rat

namespace TauCeti.IsCyclotomicExtension.Rat

variable {N : ℕ} [NeZero N] {L : Type*} [Field L] [NumberField L]
  [_root_.IsCyclotomicExtension {N} ℚ L]

/-- If the Artin image of `-p` on `E` has order less than `2^(k+1)` and `E` contains
the real cyclotomic subfield of level `2^(n+k+2)`, then `p ≡ ±1` modulo `2^(n+2)`.
For a prime coprime to `N`, this is the signed Frobenius orbit length on `Gal(E/ℚ)`. -/
theorem natCast_eq_one_or_neg_one_of_orderOf_restrictNormal_lt {n k p : ℕ}
    (h : 2 ^ (n + k + 2) ∣ N) (hp : p.Coprime N)
    (E : IntermediateField ℚ L) [Normal ℚ E] (hE : realCyclotomicSubfield h ≤ E)
    (hord : orderOf (((galEquivZMod N L).symm (-ZMod.unitOfCoprime p hp)).restrictNormal E) <
      2 ^ (k + 1)) :
    (p : ZMod (2 ^ (n + 2))) = 1 ∨ (p : ZMod (2 ^ (n + 2))) = -1 := by
  let σ := (galEquivZMod N L).symm (-ZMod.unitOfCoprime p hp)
  let r := orderOf (σ.restrictNormal E)
  have hfix : σ ^ r ∈ E.fixingSubgroup := by
    rw [← restrictNormalHom_ker, MonoidHom.mem_ker, map_pow]
    exact pow_orderOf_eq_one (σ.restrictNormal E)
  have hs := (realCyclotomicSubfield_le_iff h E).mp hE _ hfix
  have hu : (ZMod.unitsMap h (galEquivZMod N L σ)) ^ r ∈ Subgroup.zpowers (-1) := by
    simpa only [Subgroup.mem_zpowers_neg_one_iff, map_pow] using hs
  have hsign := ZMod.unitsMap_eq_one_or_neg_one_of_pow_mem_zpowers_neg_one
    _ (orderOf_pos (σ.restrictNormal E)) hord hu
  simp only [σ, ZMod.unitsMap_neg, neg_eq_iff_eq_neg, neg_neg, MulEquiv.apply_symm_apply,
    ZMod.unitsMap_unitOfCoprime] at hsign
  rw [Units.ext_iff, Units.ext_iff] at hsign
  simpa only [ZMod.coe_unitOfCoprime, Units.val_neg, Units.val_one, or_comm] using hsign

/-- The logarithmic harmonic weight of a finite set of primes with signed Frobenius
orbit length less than `2^(k+1)` is at most `log X (1 + log X) / 2^n`, if the host contains
the real cyclotomic subfield of level `2^(n+k+2)`. The sum applies to arbitrary subsets
of the eligible primes up to `X`, so it does not need a splitting or density assumption. -/
theorem sum_log_div_le_of_short_signed_frobenius {n k : ℕ} (h : 2 ^ (n + k + 2) ∣ N)
    (E : IntermediateField ℚ L) [Normal ℚ E] (hE : realCyclotomicSubfield h ≤ E)
    {s : Finset ℕ} {X : ℝ} (hX : 1 ≤ X)
    (hs : ∀ p ∈ s, (p : ℝ) ≤ X ∧ ∃ hp : p.Coprime N,
      orderOf (((galEquivZMod N L).symm (-ZMod.unitOfCoprime p hp)).restrictNormal E) <
        2 ^ (k + 1)) :
    ∑ p ∈ s, Real.log p / (p : ℝ) ≤ Real.log X * (1 + Real.log X) / (2 : ℝ) ^ n := by
  have hsum := sum_log_div_le_of_natCast_eq_one_or_neg_one (q := 2 ^ (n + 2)) hX fun p hp ↦ by
    obtain ⟨hpX, hcop, horder⟩ := hs p hp
    exact ⟨hpX, natCast_eq_one_or_neg_one_of_orderOf_restrictNormal_lt h hcop E hE horder⟩
  calc
    _ ≤ _ := hsum
    _ = _ := by push_cast; rw [pow_add]; ring

end TauCeti.IsCyclotomicExtension.Rat
