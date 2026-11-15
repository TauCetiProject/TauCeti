/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm

/-!
# Comparing smoothings of ring seminorms

The smoothing `smoothingFun μ x = lim_n μ (x ^ n) ^ (1 / n)` of a ring seminorm `μ` with
`μ 1 ≤ 1` only sees the growth rate of `μ` along powers. This file records three consequences.

* A bound `ν ∘ φ ≤ C μ` through a ring homomorphism `φ`, for any constant `C`, gives
  `smoothingFun ν ∘ φ ≤ smoothingFun μ`: the constant disappears in the limit. In particular two
  bounded-equivalent seminorms have the same smoothing.
* If multiplication by `c` scales `μ` exactly by `s ≥ 0`, it scales `smoothingFun μ` by `s`.
* If `ν = μ ^ t` for some `t > 0`, then `smoothingFun ν = (smoothingFun μ) ^ t`.

These are the facts needed to show that the spectral seminorm of a Tate ring does not depend on
the ring of definition used to define its norm, and transforms in the expected way under change
of the pseudouniformiser's radius.

## References

* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §1.3.2.
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  Definition 2.1.9.
-/

public section

open Filter Topology

variable {R S : Type*} [CommRing R] [CommRing S]

namespace RingHom

/-- **Smoothing absorbs multiplicative constants.** If `ν (φ x) ≤ C * μ x` for a ring
homomorphism `φ : R →+* S` and every `x`, then the smoothing of `ν` at `φ x` is at most the
smoothing of `μ` at `x`, whatever the constant `C`. Only `μ` needs `μ 1 ≤ 1`, so that its
smoothing is a limit. -/
theorem smoothingFun_map_le_of_le_mul {μ : RingSeminorm R} {ν : RingSeminorm S} (φ : R →+* S)
    (hμ1 : μ 1 ≤ 1) {C : ℝ} (h : ∀ x, ν (φ x) ≤ C * μ x) (x : R) :
    smoothingFun ν (φ x) ≤ smoothingFun μ x := by
  -- Replace `C` by a positive constant `D`, so that `D ^ (1 / n) → 1`.
  set D := max C 1
  have hD : 0 < D := zero_lt_one.trans_le (le_max_right _ _)
  have hlim : Tendsto (fun n : ℕ ↦ D ^ (1 / n : ℝ) * smoothingSeminormSeq μ x n) atTop
      (𝓝 (smoothingFun μ x)) := by
    have hD1 : Tendsto (fun n : ℕ ↦ D ^ (1 / n : ℝ)) atTop (𝓝 1) := by
      simpa [Function.comp_def] using ((Real.continuousAt_const_rpow hD.ne').tendsto).comp
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using hD1.mul (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x)
  refine ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩)
  calc smoothingFun ν (φ x) ≤ ν (φ x ^ n) ^ (1 / n : ℝ) :=
        smoothingFun_le ν (φ x) ⟨n, hn⟩
    _ ≤ (D * μ (x ^ n)) ^ (1 / n : ℝ) := by
        rw [← map_pow]
        gcongr
        exact (h _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (apply_nonneg μ _))
    _ = D ^ (1 / n : ℝ) * smoothingSeminormSeq μ x n :=
        Real.mul_rpow hD.le (apply_nonneg μ _)

end RingHom

namespace TauCeti

/-- **Exact scaling passes to the smoothing.** If multiplication by `c` scales `μ` by the factor
`s ≥ 0`, then it scales the smoothing of `μ` by the same factor. -/
theorem smoothingFun_mul_eq_mul_of_forall {μ : RingSeminorm R} (hμ1 : μ 1 ≤ 1) {c : R} {s : ℝ}
    (hs : 0 ≤ s) (h : ∀ y, μ (c * y) = s * μ y) (x : R) :
    smoothingFun μ (c * x) = s * smoothingFun μ x := by
  have hpow (n : ℕ) (y : R) : μ (c ^ n * y) = s ^ n * μ y := by
    induction n generalizing y with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_assoc, h, ih, ← mul_assoc, pow_succ']
  refine tendsto_nhds_unique_of_eventuallyEq
    (tendsto_smoothingFun_of_map_one_le_one μ hμ1 (c * x))
    ((tendsto_smoothingFun_of_map_one_le_one μ hμ1 x).const_mul s)
    (eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩)
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  simp only [smoothingSeminormSeq, mul_pow, hpow, one_div]
  rw [Real.mul_rpow (pow_nonneg hs n) (apply_nonneg μ _), Real.pow_rpow_inv_natCast hs hn0]

/-- **The smoothing of a power of a seminorm is the power of the smoothing.** If `ν x = μ x ^ t`
for every `x`, with `t > 0`, then `smoothingFun ν x = smoothingFun μ x ^ t`. -/
theorem smoothingFun_eq_rpow_of_forall {μ ν : RingSeminorm R} (hμ1 : μ 1 ≤ 1) {t : ℝ}
    (ht : 0 < t) (h : ∀ x, ν x = μ x ^ t) (x : R) :
    smoothingFun ν x = smoothingFun μ x ^ t := by
  have hν1 : ν 1 ≤ 1 := by
    rw [h]
    exact Real.rpow_le_one (apply_nonneg μ _) hμ1 ht.le
  refine tendsto_nhds_unique_of_eventuallyEq
    (tendsto_smoothingFun_of_map_one_le_one ν hν1 x)
    ((tendsto_smoothingFun_of_map_one_le_one μ hμ1 x).rpow_const (Or.inr ht.le))
    (Eventually.of_forall fun n ↦ ?_)
  simp only [smoothingSeminormSeq, h, ← Real.rpow_mul (apply_nonneg μ _), mul_comm t]

end TauCeti
