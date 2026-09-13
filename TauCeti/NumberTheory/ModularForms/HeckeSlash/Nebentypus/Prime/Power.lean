/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Prime.Basic
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Prime.Recurrence
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Recurrence
import TauCeti.Algebra.BigOperators.Finset.Range

/-!
# Fourier coefficients of the Hecke operators at a prime power on `M_k(N, χ)`

The `Γ₀(N)` Hecke ring acts on `M_k(N, χ)` through `heckeRingHomCharSpace`; at a prime `p`
the generator acts as the classical `Tₚ` (`HeckeSlash/Nebentypus/Prime/Basic.lean`), whose Fourier
coefficients are `a_m(Tₚ F) = a_{pm}(F) + χ(p) p^{k−1} a_{m/p}(F)`
(`HeckeSlash/Recurrence.lean`). Along the powers of a good prime `p ∤ N` the ring elements
`T_{p^r}` are the recurrence family `heckeTGeneratorRecGamma0`, with
`T_{p^{r+2}} = Tₚ T_{p^{r+1}} − p S_p T_{p^r}`, which on the character space reads
`T_{p^{r+2}} = Tₚ ∘ T_{p^{r+1}} − χ(p) p^{k−1} • T_{p^r}`
(`HeckeSlash/Nebentypus/Prime/Recurrence.lean`). Unwinding that recurrence on
coefficients gives the classical formula: writing `c = χ(p) p^{k−1}`, for every index `m` prime
to `p`,

`a_{p^j m}(T_{p^r} F) = ∑_{i ≤ min j r} c^i · a_{p^{j+r−2i} m}(F)`,

the two-step recurrence between such sums being `TauCeti.sum_range_min_add_two` and its base
case `TauCeti.sum_range_min_zero` (`Algebra/BigOperators/Finset/Range.lean`),

the prime-power case of Diamond–Shurman Proposition 5.3.1, and in particular
`a_m(T_{p^r} F) = a_{p^r m}(F)`. The composite operators are ordered products of these blocks
(`heckeTCompositeGamma0`), so this is the input for the coefficient formula at a general index
coprime to the level.

## Main results

* `HeckeRing.GL2.qExpansion_coeff_prime_pow_mul_heckeRingHomCharSpace_heckeTGeneratorRecGamma0`:
  the formula above.
* `HeckeRing.GL2.qExpansion_coeff_heckeRingHomCharSpace_heckeTGeneratorRecGamma0_of_not_dvd`:
  `a_m(T_{p^r} F) = a_{p^r m}(F)` at an index `m` prime to `p`.
* `qExpansion_coeff_prime_pow_succ_mul_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0`: the
  divisible-index `Tₚ` recurrence on `S_k(N, χ)`, with no hypothesis on the index.
* their cusp-form specialisations, named after the modular statements with
  `heckeRingHomCharSpace` replaced by `heckeRingHomCuspCharSpace`, transported along the
  inclusion of character spaces `cuspToModFormCharSpace`.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `2baa76f742bdb4fb8ee323fabba41203bd390e08`),
`projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/FourierHecke.lean` —
`fourierCoeff_heckeT_ppow_period_one` and `fourierCoeff_heckeT_p_period_one`, which state the
divisor-sum form `a_m(T_{p^v} f) = ∑_{d ∣ gcd(m, p^v)} d^{k−1} χ(d) a_{m p^v / d²}(f)` for the
source's concretely-defined `heckeT_ppow`. Here the operator is the Hecke ring's own recurrence
family acting through `heckeRingHomCharSpace`, so the formula is proved from the ring
recurrence and the prime case rather than from coset representatives, and it is stated at the
indices `p^j m` with `m` prime to `p`, where the divisor sum is the `min` sum above.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.3.1.
* [T. Miyake, *Modular forms*][miyake1989], §4.5.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups

namespace HeckeRing.GL2

variable {N p : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- **`Tₚ` at an index prime to `p`** reads the coefficient at `p m`: the `p ∣ m` term of the
recurrence is absent. -/
theorem qExpansion_coeff_heckeRingHomCharSpace_heckeTGeneratorGamma0_of_not_dvd (hp : p.Prime)
    (hpN : Nat.Coprime p N) (G : modFormCharSpace k χ) {m : ℕ} (hpm : ¬ p ∣ m) :
    (qExpansion 1 (heckeRingHomCharSpace k χ (heckeTGeneratorGamma0 N p) G :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m =
      (qExpansion 1 (G : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p * m) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [coe_heckeRingHomCharSpace_heckeTGeneratorGamma0 k χ hp G, heckeTNat_def,
    qExpansion_coeff_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_mem_modFormCharSpace k hp
      hpN χ G.2, ite_eq_right hpm, add_zero]

/-- **`Tₚ` at an index divisible by `p`**: `a_{p^{j+1} m}(Tₚ G) = a_{p^{j+2} m}(G) +
χ(p) p^{k−1} a_{p^j m}(G)`, the recurrence with both terms present. -/
theorem qExpansion_coeff_prime_pow_succ_mul_heckeRingHomCharSpace_heckeTGeneratorGamma0
    (hp : p.Prime) (hpN : Nat.Coprime p N) (G : modFormCharSpace k χ) (m j : ℕ) :
    (qExpansion 1 (heckeRingHomCharSpace k χ (heckeTGeneratorGamma0 N p) G :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ (j + 1) * m) =
      (qExpansion 1 (G : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ (j + 2) * m) +
        (χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1) *
          (qExpansion 1 (G : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ j * m) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hdvd : p ∣ p ^ (j + 1) * m := dvd_mul_of_dvd_left (dvd_pow_self p j.succ_ne_zero) m
  have hdiv : p ^ (j + 1) * m / p = p ^ j * m := by
    rw [pow_succ', mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
  rw [coe_heckeRingHomCharSpace_heckeTGeneratorGamma0 k χ hp G, heckeTNat_def,
    qExpansion_coeff_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_mem_modFormCharSpace k hp
      hpN χ G.2, ite_eq_left hdvd, hdiv, ← mul_assoc, ← pow_succ']

/-- The formula at `r = 1`, where the ring element is the generator `Tₚ` itself: one term at an
index prime to `p`, two at a multiple of `p`. -/
private theorem qExpansion_coeff_prime_pow_mul_heckeRingHomCharSpace_heckeTGeneratorGamma0
    (hp : p.Prime) (hpN : Nat.Coprime p N)
    (F : modFormCharSpace k χ) {m : ℕ} (hpm : ¬ p ∣ m) (j : ℕ) :
    (qExpansion 1 (heckeRingHomCharSpace k χ (heckeTGeneratorGamma0 N p) F :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ j * m) =
      ∑ i ∈ Finset.range (min j 1 + 1),
        ((χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1)) ^ i *
          (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff
            (p ^ (j + 1 - 2 * i) * m) := by
  rcases j with _ | j
  · -- `p ∤ m`: one term, at the index `p m`
    have hidx : p * m = p ^ (0 + 1 - 2 * 0) * m := by simp
    rw [pow_zero, one_mul,
      qExpansion_coeff_heckeRingHomCharSpace_heckeTGeneratorGamma0_of_not_dvd hp hpN F hpm, hidx]
    simp
  · -- `p ∣ p^{j+1} m`: two terms, at `p^{j+2} m` and `p^j m`
    have hmin : min (j + 1) 1 + 1 = 2 := by omega
    have hidx₁ : j + 1 + 1 - 2 * 0 = j + 2 := by omega
    have hidx₂ : j + 1 + 1 - 2 * 1 = j := by omega
    rw [qExpansion_coeff_prime_pow_succ_mul_heckeRingHomCharSpace_heckeTGeneratorGamma0 hp hpN F
        m j, hmin,
      Finset.sum_range_succ, Finset.sum_range_one, hidx₁, hidx₂]
    simp

/-- **The prime-power coefficient formula on `M_k(N, χ)`.** For a good prime `p ∤ N`, an index `m`
prime to `p` and all `j`, `r`, writing `c = χ(p) p^{k−1}`,
`a_{p^j m}(T_{p^r} F) = ∑_{i ≤ min j r} c^i · a_{p^{j+r−2i} m}(F)`
(Diamond–Shurman Proposition 5.3.1 at a prime power). -/
theorem qExpansion_coeff_prime_pow_mul_heckeRingHomCharSpace_heckeTGeneratorRecGamma0 (hp : p.Prime)
    (hpN : Nat.Coprime p N) (F : modFormCharSpace k χ) {m : ℕ} (hpm : ¬ p ∣ m) (r j : ℕ) :
    (qExpansion 1 (heckeRingHomCharSpace k χ (heckeTGeneratorRecGamma0 N p r) F :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ j * m) =
      ∑ i ∈ Finset.range (min j r + 1),
        ((χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1)) ^ i *
          (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff
            (p ^ (j + r - 2 * i) * m) := by
  induction r using Nat.twoStepInduction generalizing j with
  | zero =>
    rw [heckeTGeneratorRecGamma0_zero, map_one, Module.End.one_apply]
    simp
  | one =>
    rw [heckeTGeneratorRecGamma0_one]
    exact qExpansion_coeff_prime_pow_mul_heckeRingHomCharSpace_heckeTGeneratorGamma0 hp hpN F hpm j
  | more r ih1 ih2 =>
    rw [heckeRingHomCharSpace_heckeTGeneratorRecGamma0_succ_succ_apply k χ hp.pos hpN F r,
      Submodule.coe_sub, Submodule.coe_smul,
      ← TauCeti.ModularForm.qExpansionLinearMap_apply one_pos
        (TauCeti.one_mem_strictPeriods_Gamma1_map _), map_sub, map_smul,
      TauCeti.ModularForm.qExpansionLinearMap_apply,
      TauCeti.ModularForm.qExpansionLinearMap_apply]
    simp only [map_sub, map_smul, smul_eq_mul]
    rcases j with _ | j
    · -- `p ∤ m`: the recurrence reads the coefficient at `p m`, which is the `j = 1` instance
      have h1 := ih1 0
      have h2 := ih2 1
      rw [pow_zero, one_mul] at h1
      rw [pow_one] at h2
      rw [pow_zero, one_mul,
        qExpansion_coeff_heckeRingHomCharSpace_heckeTGeneratorGamma0_of_not_dvd hp hpN _ hpm, h2,
        h1]
      -- at `j = 0` the sums recombine by `TauCeti.sum_range_min_zero`
      have h := TauCeti.sum_range_min_zero
        (fun t ↦ (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ t * m))
        ((χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1)) r
      linear_combination -h
    · -- both terms of the recurrence are present, and the four sums recombine by
      -- `TauCeti.sum_range_min_add_two`
      rw [qExpansion_coeff_prime_pow_succ_mul_heckeRingHomCharSpace_heckeTGeneratorGamma0 hp hpN _
          m j, ih2 (j + 2),
        ih2 j, ih1 (j + 1)]
      have h := TauCeti.sum_range_min_add_two
        (fun t ↦ (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ t * m))
        ((χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1)) j r
      linear_combination h

/-- **At an index prime to `p`, `T_{p^r}` reads the coefficient at `p^r m`**:
`a_m(T_{p^r} F) = a_{p^r m}(F)`, the `j = 0` case of the prime-power formula. -/
theorem qExpansion_coeff_heckeRingHomCharSpace_heckeTGeneratorRecGamma0_of_not_dvd (hp : p.Prime)
    (hpN : Nat.Coprime p N) (F : modFormCharSpace k χ) {m : ℕ} (hpm : ¬ p ∣ m) (r : ℕ) :
    (qExpansion 1 (heckeRingHomCharSpace k χ (heckeTGeneratorRecGamma0 N p r) F :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m =
      (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ r * m) := by
  have h :=
    qExpansion_coeff_prime_pow_mul_heckeRingHomCharSpace_heckeTGeneratorRecGamma0 hp hpN F hpm r 0
  simpa using h


/-! ### The cusp-form specialisations -/

/-- **The prime-power coefficient formula on `S_k(N, χ)`**: the case of
`qExpansion_coeff_prime_pow_mul_heckeRingHomCharSpace_heckeTGeneratorRecGamma0` at a cusp form,
whose `q`-expansion is that of the modular form underlying it. -/
theorem qExpansion_coeff_prime_pow_mul_heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0
    (hp : p.Prime) (hpN : Nat.Coprime p N) (F : cuspFormCharSpace k χ) {m : ℕ} (hpm : ¬ p ∣ m)
    (r j : ℕ) :
    (qExpansion 1 (heckeRingHomCuspCharSpace k χ (heckeTGeneratorRecGamma0 N p r) F :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ j * m) =
      ∑ i ∈ Finset.range (min j r + 1),
        ((χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1)) ^ i *
          (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff
            (p ^ (j + r - 2 * i) * m) := by
  have h := qExpansion_coeff_prime_pow_mul_heckeRingHomCharSpace_heckeTGeneratorRecGamma0 hp hpN
    (cuspToModFormCharSpace k χ F) hpm r j
  rw [heckeRingHomCharSpace_apply, ← cuspToModFormCharSpace_twistedHeckeSlashCuspFormCharLinearMap,
    ← heckeRingHomCuspCharSpace_apply] at h
  simp only [coe_cuspToModFormCharSpace, ModularFormClass.coe_modularForm] at h
  exact h

/-- **The divisible-index recurrence for `Tₚ` on `S_k(N, χ)`**: the cusp-form counterpart of
`qExpansion_coeff_prime_pow_succ_mul_heckeRingHomCharSpace_heckeTGeneratorGamma0`, with no
hypothesis on `m`. Stated so that consumers on `cuspFormCharSpace` need neither a coercion nor
the full prime-power theorem's `¬ p ∣ m`. -/
theorem qExpansion_coeff_prime_pow_succ_mul_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0
    (hp : p.Prime) (hpN : Nat.Coprime p N) (F : cuspFormCharSpace k χ) (m j : ℕ) :
    (qExpansion 1 (heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) F :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ (j + 1) * m) =
      (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ (j + 2) * m) +
        (χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1) *
          (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ j * m) := by
  have h := qExpansion_coeff_prime_pow_succ_mul_heckeRingHomCharSpace_heckeTGeneratorGamma0 hp hpN
    (cuspToModFormCharSpace k χ F) m j
  rw [heckeRingHomCharSpace_apply, ← cuspToModFormCharSpace_twistedHeckeSlashCuspFormCharLinearMap,
    ← heckeRingHomCuspCharSpace_apply] at h
  simp only [coe_cuspToModFormCharSpace, ModularFormClass.coe_modularForm] at h
  exact h

/-- **At an index prime to `p`, `T_{p^r}` reads the coefficient at `p^r m`**, on `S_k(N, χ)`. -/
theorem qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0_of_not_dvd
    (hp : p.Prime) (hpN : Nat.Coprime p N) (F : cuspFormCharSpace k χ) {m : ℕ} (hpm : ¬ p ∣ m)
    (r : ℕ) :
    (qExpansion 1 (heckeRingHomCuspCharSpace k χ (heckeTGeneratorRecGamma0 N p r) F :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m =
      (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ r * m) := by
  have h :=
    qExpansion_coeff_prime_pow_mul_heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0 hp hpN F hpm
      r 0
  simpa only [heckeRingHomCuspCharSpace_apply, coe_twistedHeckeSlashCuspFormCharLinearMap,
    pow_zero, one_mul, zero_le, inf_of_le_left, zero_add, Finset.range_one, Finset.sum_singleton,
    mul_zero, tsub_zero] using h

end HeckeRing.GL2
