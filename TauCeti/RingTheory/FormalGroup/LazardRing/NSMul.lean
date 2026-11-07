/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.LazardRing.Hurewicz
-- Proof-only: primes of `ℕ` are prime in `ℤ`, multiplication series under base change, and
-- evaluation in the dual numbers.
import Mathlib.Data.Nat.Prime.Int
import TauCeti.RingTheory.FormalGroup.NSMul.BaseChange
import TauCeti.RingTheory.MvPolynomial.DualNumber

/-!
# The multiplication series of the universal formal group law modulo decomposables

Let `[k](X) = ∑ₘ aₘ X^m` be multiplication by `k` on the universal formal group law over the
Lazard ring `L`, and let `I` be the augmentation ideal of `L`. The coefficient `aₘ` has degree
`2 (m - 1)`. For `m ≥ 2` it lies in `I`, and this file computes its class in the indecomposables
`I ⧸ I²`, which are free over `ℤ` on the classes of the generators `xₙ ∈ L₂ₙ`
(`TauCeti.LazardRing.cotangentBasis`):

  `a_(n+1) ≡ ((k^(n + 1) - k) / d_(n+1)) • xₙ  (mod I²)`,

where `d_(n+1)` is `p` if `n + 1` is a power of a prime `p` and `1` otherwise
(`TauCeti.lazardGcd`). The class is read off with the Hurewicz homomorphism
`L →+* ℤ[b₁, b₂, …]`, whose coefficient of `bₙ` is `d_(n+1)` times the `n`-th coordinate in
`I ⧸ I²`. Evaluated at `bₙ = ε`, `ε² = 0`, the Hurewicz image of the universal law is the additive
law transported along `X + ε X^(n + 1)`, on which multiplication by `k` is
`k X + ε (k^(n + 1) - k) X^(n + 1)` (`FormalGroup.nsmulSeries_ofStrictCoeffs_single_smul_𝔾ₐ`).

For a prime `p`, the coefficient `vⱼ` of `X^(pʲ)` in the `p`-series generates the height ideal
`I_(j+1) = (p, v₁, …, vⱼ)` over `I_j` (`FormalGroup.heightIdeal_succ`). With `k = p` and
`n + 1 = pʲ` the formula reads `vⱼ ≡ (p^n - 1) • xₙ` modulo `I²`, so modulo `p` and decomposables
`vⱼ ≡ -x_(pʲ - 1)`: Landweber's element `vⱼ` is, up to sign, the generator `x_(pʲ - 1)` of the
polynomial ring `L ⧸ p = 𝔽ₚ[x₁, x₂, …]` modulo decomposables. In all other degrees `m ≥ 2` the
coefficient `aₘ` of the `p`-series lies in `(p) + I²`. Hence, coefficientwise, in
`(L ⧸ ((p) + I²))⟦X⟧`

  `[p](X) = -∑_(j ≥ 1) x_(pʲ - 1) X^(pʲ)`.

This is the input for replacing the generators `x_(pʲ - 1)` by the `vⱼ`, from which the sequence
`p, v₁, v₂, …` is regular in `L` and the ideals `I_n` are prime, as used in Landweber's exact
functor theorem.

## Main results

* `TauCeti.LazardRing.coeff_nsmulSeries_mem_grading`: the coefficient of `X^m` in `[k]` has degree
  `2 (m - 1)`.
* `TauCeti.LazardRing.coeff_nsmulSeries_mem_augmentationIdeal`: the coefficients of `[k]` other
  than the linear one lie in the augmentation ideal.
* `TauCeti.LazardRing.coeff_single_hurewicz_coeff_nsmulSeries`: the coefficient of `bₙ` in the
  Hurewicz image of `aₘ` is `k^m - k` if `m = n + 1`, and `0` otherwise.
* `TauCeti.LazardRing.lazardGcd_dvd_pow_succ_sub`: `d_(n+1)` divides `k^(n + 1) - k`.
* `TauCeti.LazardRing.cotangentBasis_repr_toCotangent_coeff_nsmulSeries`: the class of `a_(n+1)`
  in `I ⧸ I²` is `((k^(n + 1) - k) / d_(n+1)) • xₙ`.
* `TauCeti.LazardRing.coeff_nsmulSeries_sub_smul_generator_mem_sq`: the same congruence in `L`.
* `TauCeti.LazardRing.coeff_prime_pow_nsmulSeries_sub_smul_generator_mem_sq`:
  `vⱼ ≡ (p^n - 1) • xₙ` modulo `I²`, where `n + 1 = pʲ`.
* `TauCeti.LazardRing.coeff_prime_pow_nsmulSeries_add_generator_mem`: `vⱼ ≡ -xₙ` modulo `p` and
  decomposables.
* `TauCeti.LazardRing.coeff_nsmulSeries_mem_of_ne_prime_pow`: the other nonlinear coefficients of
  the `p`-series vanish modulo `p` and decomposables.

## References

* P. S. Landweber, *Annihilator ideals and primitive elements in complex bordism*, Illinois J.
  Math. 17 (1973), 273–284.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1 and
  Chapter 4.
* J. F. Adams, *Stable Homotopy and Generalised Homology*, Part II, §§6–7.
-/

public section

noncomputable section

open Finsupp

namespace TauCeti.LazardRing

/-- The coefficients of multiplication by `k` on the universal formal group law, other than the
linear one, lie in the augmentation ideal: the augmentation sends `[k](X)` to `k X`. -/
theorem coeff_nsmulSeries_mem_augmentationIdeal (k : ℕ) {m : ℕ} (hm : m ≠ 1) :
    PowerSeries.coeff m (formalGroup.nsmulSeries k) ∈ augmentationIdeal := by
  rw [mem_augmentationIdeal, ← FormalGroup.coeff_nsmulSeries_map, map_augmentation,
    FormalGroup.nsmulSeries_𝔾ₐ]
  simp [PowerSeries.coeff_X, hm]

/-- The coefficient of `X^m` in multiplication by `k` on the universal formal group law has degree
`2 (m - 1)`. In particular Landweber's `vⱼ`, the coefficient of `X^(pʲ)` in the `p`-series, has
degree `2 (pʲ - 1)`. -/
theorem coeff_nsmulSeries_mem_grading (k m : ℕ) :
    PowerSeries.coeff m (formalGroup.nsmulSeries k) ∈ grading (2 * (m - 1)) :=
  FormalGroup.coeff_nsmulSeries_mem formalGroup coeff_formalGroup_mem_grading k m

/-- **The Hurewicz image of multiplication by `k`, to first order.** The coefficient of `bₙ` in the
image under the Hurewicz homomorphism of the coefficient of `X^m` in `[k](X)` is `k^m - k` when
`m = n + 1`, and `0` otherwise. -/
theorem coeff_single_hurewicz_coeff_nsmulSeries (k m : ℕ) (n : ℕ+) :
    (hurewicz (PowerSeries.coeff m (formalGroup.nsmulSeries k))).coeff (single n 1) =
      if m = n + 1 then (k : ℤ) ^ m - k else 0 := by
  -- Evaluate at `bₙ = ε`, `bᵢ = 0` for `i ≠ n`: this reads off the coefficient of `bₙ`, and turns
  -- the Hurewicz image of the universal law into `X + Y` transported along `X + ε X^(n + 1)`.
  have hmap : formalGroup.map
      ((MvPolynomial.aeval (Pi.single n (DualNumber.eps : DualNumber ℤ))).toRingHom.comp hurewicz) =
      FormalCoordinate.ofStrictCoeffs (Pi.single n (DualNumber.eps : DualNumber ℤ)) •
        FormalGroup.𝔾ₐ := by
    rw [← FormalGroup.map_comp, map_hurewicz, FormalGroup.map_ofStrictCoeffs_smul_𝔾ₐ]
    simp [Function.comp_def]
  have hval : MvPolynomial.aeval (Pi.single n (DualNumber.eps : DualNumber ℤ))
      (hurewicz (PowerSeries.coeff m (formalGroup.nsmulSeries k))) =
      PowerSeries.coeff m ((FormalCoordinate.ofStrictCoeffs
        (Pi.single n (DualNumber.eps : DualNumber ℤ)) • FormalGroup.𝔾ₐ).nsmulSeries k) := by
    rw [← hmap, FormalGroup.coeff_nsmulSeries_map, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
  have h := MvPolynomial.aeval_single_eps n
    (hurewicz (PowerSeries.coeff m (formalGroup.nsmulSeries k)))
  rw [hval, FormalGroup.nsmulSeries_ofStrictCoeffs_single_smul_𝔾ₐ n DualNumber.eps_mul_eps] at h
  rw [map_add, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_C_mul, PowerSeries.coeff_X] at h
  -- The `ε`-components: `ε (k^(n + 1) - k)` in degree `n + 1` against the coefficient of `bₙ`.
  have h' := congrArg TrivSqZeroExt.snd h
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_smul, smul_eq_mul, DualNumber.snd_eps,
    mul_one, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl, zero_add] at h'
  rw [← h']
  split_ifs with hm₁ hm₂ hm₂
  · exact absurd (hm₁.symm.trans hm₂) (by simp)
  · simp
  · subst hm₂
    simp
  · simp

/-- `d_(n+1)` divides `k^(n + 1) - k` for every `k`: by the Hurewicz homomorphism, this is the
coefficient of `bₙ` in the image of the coefficient of `X^(n + 1)` in `[k](X)`. -/
theorem lazardGcd_dvd_pow_succ_sub (k : ℕ) (n : ℕ+) :
    (lazardGcd ((n : ℕ) + 1) : ℤ) ∣ (k : ℤ) ^ ((n : ℕ) + 1) - k := by
  have h := lazardGcd_dvd_coeff_single_hurewicz n
    (PowerSeries.coeff ((n : ℕ) + 1) (formalGroup.nsmulSeries k))
  simpa only [coeff_single_hurewicz_coeff_nsmulSeries, ↓reduceIte] using h

/-- The coefficient of `X^(n + 1)` in `[k](X)`, as an element of the augmentation ideal. -/
private abbrev coeffNSMul (k : ℕ) (n : ℕ+) : augmentationIdeal :=
  ⟨PowerSeries.coeff (n + 1) (formalGroup.nsmulSeries k),
    coeff_nsmulSeries_mem_augmentationIdeal k (by simp)⟩

/-- The `n`-th coordinate of the class of `a_(n+1)` in `I ⧸ I²`, multiplied by `d_(n+1)`, is
`k^(n + 1) - k`; all other coordinates vanish. -/
private theorem lazardGcd_mul_cotangentBasis_repr_coeffNSMul (k : ℕ) (n m : ℕ+) :
    lazardGcd (m + 1) * cotangentBasis.repr (augmentationIdeal.toCotangent (coeffNSMul k n)) m =
      if m = n then (k : ℤ) ^ ((n : ℕ) + 1) - k else 0 := by
  rw [← coeff_single_hurewicz m (coeffNSMul k n).2, coeff_single_hurewicz_coeff_nsmulSeries]
  simp only [add_left_inj, PNat.coe_inj, eq_comm (a := n)]

/-- **The class of `[k](X)` in the indecomposables.** The coefficient `a_(n+1)` of `X^(n + 1)` in
multiplication by `k` on the universal formal group law has class
`((k^(n + 1) - k) / d_(n+1)) • xₙ` in `I ⧸ I²`, where the division is exact. -/
theorem cotangentBasis_repr_toCotangent_coeff_nsmulSeries (k : ℕ) (n : ℕ+) :
    cotangentBasis.repr (augmentationIdeal.toCotangent
        ⟨PowerSeries.coeff (n + 1) (formalGroup.nsmulSeries k),
          coeff_nsmulSeries_mem_augmentationIdeal k (by simp)⟩) =
      single n (((k : ℤ) ^ ((n : ℕ) + 1) - k) / lazardGcd ((n : ℕ) + 1)) := by
  ext m
  have h := lazardGcd_mul_cotangentBasis_repr_coeffNSMul k n m
  have hd : (lazardGcd ((m : ℕ) + 1) : ℤ) ≠ 0 :=
    Nat.cast_ne_zero.2 (lazardGcd_succ_ne_zero m.ne_zero)
  by_cases hmn : m = n
  · subst hmn
    simp only [↓reduceIte] at h
    rw [single_eq_same, ← h, Int.mul_ediv_cancel_left _ hd]
  · simp only [hmn, ↓reduceIte] at h
    rw [single_eq_of_ne hmn]
    exact (mul_eq_zero.1 h).resolve_left hd

/-- **`[k](X)` modulo decomposables.** The coefficient of `X^(n + 1)` in multiplication by `k` on
the universal formal group law is `((k^(n + 1) - k) / d_(n+1)) • xₙ` modulo the square of the
augmentation ideal, where the division is exact. -/
theorem coeff_nsmulSeries_sub_smul_generator_mem_sq (k : ℕ) (n : ℕ+) :
    PowerSeries.coeff (n + 1) (formalGroup.nsmulSeries k) -
        (((k : ℤ) ^ ((n : ℕ) + 1) - k) / lazardGcd ((n : ℕ) + 1)) • generator n ∈
      augmentationIdeal ^ 2 := by
  have h := sub_sum_generator_mem_sq (coeffNSMul k n).2
  rwa [cotangentBasis_repr_toCotangent_coeff_nsmulSeries, sum_single_index (by simp)] at h

variable {p : ℕ} (hp : p.Prime)
include hp

/-- **Landweber's `vⱼ` modulo decomposables.** For a prime `p` and `n + 1 = pʲ` with `j ≥ 1`, the
coefficient `vⱼ` of `X^(pʲ)` in the `p`-series of the universal formal group law is
`(p^n - 1) • xₙ` modulo the square of the augmentation ideal. -/
theorem coeff_prime_pow_nsmulSeries_sub_smul_generator_mem_sq {j : ℕ} (hj : j ≠ 0) {n : ℕ+}
    (hn : (n : ℕ) + 1 = p ^ j) :
    PowerSeries.coeff (p ^ j) (formalGroup.nsmulSeries p) - ((p : ℤ) ^ (n : ℕ) - 1) • generator n ∈
      augmentationIdeal ^ 2 := by
  have h := coeff_nsmulSeries_sub_smul_generator_mem_sq p n
  -- `d_(pʲ) = p`, and `(p^(n + 1) - p) / p = p^n - 1`.
  have hq : ((p : ℤ) ^ ((n : ℕ) + 1) - p) / lazardGcd ((n : ℕ) + 1) = (p : ℤ) ^ (n : ℕ) - 1 := by
    rw [hn, lazardGcd_prime_pow hp hj, ← hn,
      show (p : ℤ) ^ ((n : ℕ) + 1) - p = ((p : ℤ) ^ (n : ℕ) - 1) * p by ring,
      Int.mul_ediv_cancel _ (Nat.cast_ne_zero.2 hp.ne_zero)]
  rwa [hq, hn] at h

/-- **Landweber's `vⱼ` is `-x_(pʲ - 1)` modulo `p` and decomposables.** For a prime `p` and
`n + 1 = pʲ` with `j ≥ 1`, the coefficient `vⱼ` of `X^(pʲ)` in the `p`-series of the universal
formal group law satisfies `vⱼ ≡ -xₙ` modulo `p L + I²`. -/
theorem coeff_prime_pow_nsmulSeries_add_generator_mem {j : ℕ} (hj : j ≠ 0) {n : ℕ+}
    (hn : (n : ℕ) + 1 = p ^ j) :
    PowerSeries.coeff (p ^ j) (formalGroup.nsmulSeries p) + generator n ∈
      Ideal.span {(p : LazardRing)} ⊔ augmentationIdeal ^ 2 := by
  -- `vⱼ + xₙ = (vⱼ - (p^n - 1) xₙ) + p (p^(n - 1) xₙ)`.
  have hp' : (p : LazardRing) ∣ ((p : ℤ) ^ (n : ℕ) : ℤ) • generator n :=
    ⟨(p : LazardRing) ^ ((n : ℕ) - 1) * generator n, by
      rw [zsmul_eq_mul, Int.cast_pow, Int.cast_natCast, ← mul_assoc, ← pow_succ',
        Nat.sub_add_cancel n.pos]⟩
  have h := Ideal.add_mem _
    (Ideal.mem_sup_right (coeff_prime_pow_nsmulSeries_sub_smul_generator_mem_sq hp hj hn))
    (Ideal.mem_sup_left (Ideal.mem_span_singleton.2 hp'))
  convert h using 1
  rw [sub_smul, one_smul]
  abel

/-- **The `p`-series modulo `p` and decomposables away from the powers of `p`.** For a prime `p`
and `m ≥ 2` not a power of `p`, the coefficient of `X^m` in the `p`-series of the universal formal
group law lies in `p L + I²`. -/
theorem coeff_nsmulSeries_mem_of_ne_prime_pow {m : ℕ} (hm : 2 ≤ m) (hpm : ∀ j, m ≠ p ^ j) :
    PowerSeries.coeff m (formalGroup.nsmulSeries p) ∈
      Ideal.span {(p : LazardRing)} ⊔ augmentationIdeal ^ 2 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ+, (n : ℕ) + 1 = m := ⟨⟨m - 1, by omega⟩, by simp; omega⟩
  set d : ℤ := ((lazardGcd ((n : ℕ) + 1) : ℕ) : ℤ)
  set c : ℤ := ((p : ℤ) ^ ((n : ℕ) + 1) - p) / d
  -- `p` is prime to `d_m`, which is `1` or a prime other than `p`, and `d_m c = p (p^n - 1)`.
  have hpd : ¬ (p : ℤ) ∣ d := by
    rw [Int.natCast_dvd_natCast, prime_dvd_lazardGcd_iff hp (by omega)]
    rintro ⟨j, hj⟩
    exact hpm j hj
  have hdc : d * c = p * ((p : ℤ) ^ (n : ℕ) - 1) := by
    rw [Int.mul_ediv_cancel' (lazardGcd_dvd_pow_succ_sub p n)]
    ring
  obtain ⟨c', hc'⟩ : (p : ℤ) ∣ c :=
    ((Nat.prime_iff_prime_int.1 hp).dvd_or_dvd (hdc ▸ dvd_mul_right _ _)).resolve_left hpd
  have hp' : (p : LazardRing) ∣ c • generator n :=
    ⟨c' • generator n, by rw [hc', mul_smul, zsmul_eq_mul, Int.cast_natCast]⟩
  have h := Ideal.add_mem _
    (Ideal.mem_sup_right (coeff_nsmulSeries_sub_smul_generator_mem_sq p n))
    (Ideal.mem_sup_left (Ideal.mem_span_singleton.2 hp'))
  rwa [sub_add_cancel] at h

end TauCeti.LazardRing
