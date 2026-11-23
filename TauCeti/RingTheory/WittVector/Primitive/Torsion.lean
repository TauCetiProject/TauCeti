/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import TauCeti.RingTheory.Perfect.Basic
public import TauCeti.RingTheory.WittVector.Primitive.Basic

/-!
# `p`-power torsion modulo a distinguished Witt vector

Let `S` be a perfect ring of characteristic `p` and let `ξ : 𝕎 S` be distinguished, that is, its
first Witt coordinate `ξ₁` is a unit. This file shows that every `p`-power torsion element of
`𝕎 S ⧸ (ξ)` is killed by `p`. Nothing else is assumed: `S` may have zero divisors (a product of
perfect fields, say), and `ξ` need not be a nonzerodivisor of `𝕎 S`.

The key step is that if `p ^ 2` divides `ξ g`, then `p` divides `g`. Indeed the zeroth and first
Witt coordinates of `ξ g` then vanish, that is `ξ₀ g₀ = 0` and `ξ₀ ^ p g₁ + g₀ ^ p ξ₁ = 0`
(`WittVector.mul_coeff_one_charP`); multiplying the second relation by `g₀ ^ p` gives
`g₀ ^ (2 p) ξ₁ = 0`, so `g₀` is nilpotent, hence zero because `S` is reduced, and an element of
`𝕎 S` with vanishing zeroth Witt coordinate is divisible by `p`. Since `p` is a nonzerodivisor of
`𝕎 S`, induction shows that `p ^ (n + 1) ∣ ξ g` implies `p ^ n ∣ g`, and therefore that
`ξ ∣ p ^ n f` implies `ξ ∣ p f`.

For a nonzero integral perfectoid ring `R`, the generators `ξ` of the kernel of Fontaine's map
`θ : 𝕎 R♭ → R` are distinguished (Bhatt–Morrow–Scholze, *Integral p-adic Hodge theory*,
Remark 3.11), and `θ` is surjective, so `R ≃ 𝕎 R♭ ⧸ (ξ)`. These results are the Witt-vector
input to the fact that the `p`-power torsion of an integral perfectoid ring is killed by `p`.

The hypothesis on `ξ₁` cannot be dropped: in `𝕎 𝔽₂ ⧸ (4)`, the class of `1` is killed by `4` but
not by `2`, and the first Witt coordinate of `4` is `0`.

## Main results

* `WittVector.IsDistinguished.p_dvd_of_p_sq_dvd_mul`: if `p ^ 2 ∣ ξ g`, then `p ∣ g`.
* `WittVector.IsDistinguished.p_pow_dvd_of_p_pow_succ_dvd_mul`: if `p ^ (n + 1) ∣ ξ g`, then
  `p ^ n ∣ g`.
* `WittVector.IsDistinguished.dvd_p_mul_of_dvd_p_pow_mul`: if `ξ ∣ p ^ n f`, then `ξ ∣ p f`.
* `WittVector.IsDistinguished.p_mul_eq_zero_of_p_pow_mul_eq_zero`: in `𝕎 S ⧸ (ξ)`, if
  `p ^ n x = 0`, then `p x = 0`.
* `WittVector.IsDistinguished.torsion'_powers_eq_torsionBy`: the `p`-power torsion of
  `𝕎 S ⧸ (ξ)` is its `p`-torsion.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Topological Hochschild homology and integral p-adic Hodge
  theory*, Proposition 4.19(3) and its proof.
* B. Bhatt, M. Morrow, P. Scholze, *Integral p-adic Hodge theory*, Remark 3.11.
-/

public section

namespace WittVector

open Ideal

variable {p : ℕ} [hp : Fact p.Prime] {S : Type*} [CommRing S] [CharP S p] [PerfectRing S p]
  {ξ : WittVector p S}

local notation "𝕎" => WittVector p

namespace IsDistinguished

/-- Over a perfect ring of characteristic `p`, let `ξ` be distinguished. If `p ^ 2` divides
`ξ g`, then `p` divides `g` (Bhatt–Morrow–Scholze, *Topological Hochschild homology and integral
p-adic Hodge theory*, proof of Proposition 4.19(3)). -/
theorem p_dvd_of_p_sq_dvd_mul (hξ : ξ.IsDistinguished) {g : 𝕎 S}
    (h : (p : 𝕎 S) ^ 2 ∣ ξ * g) : (p : 𝕎 S) ∣ g := by
  have := TauCeti.isReduced_of_perfectRing S p
  obtain ⟨c, hc⟩ := h
  -- The zeroth and first Witt coordinates of `ξ g = p ^ 2 c` vanish.
  have h₀ : (ξ.coeff 0 * g.coeff 0) ^ p = 0 := by
    rw [← mul_coeff_zero, hc, mul_comm, mul_pow_charP_coeff_zero c two_pos,
      zero_pow hp.out.ne_zero]
  have h₁ : ξ.coeff 0 ^ p * g.coeff 1 + g.coeff 0 ^ p * ξ.coeff 1 = 0 := by
    rw [← mul_coeff_one_charP, hc, mul_comm, mul_pow_charP_coeff_zero c one_lt_two]
  -- Multiplying the second relation by `g₀ ^ p` and using the first gives `g₀ ^ (2 p) ξ₁ = 0`.
  have h₂ : (g.coeff 0 ^ p) ^ 2 * ξ.coeff 1 = 0 := by
    linear_combination g.coeff 0 ^ p * h₁ - g.coeff 1 * h₀
  rw [isDistinguished_iff.mp hξ |>.mul_left_eq_zero, ← pow_mul] at h₂
  have hg : g.coeff 0 = 0 := IsReduced.eq_zero _ ⟨_, h₂⟩
  exact mem_span_singleton.mp ((mem_span_p_iff_coeff_zero_eq_zero g).mpr hg)

/-- Over a perfect ring of characteristic `p`, let `ξ` be distinguished. If `p ^ (n + 1)` divides
`ξ g`, then `p ^ n` divides `g`. -/
theorem p_pow_dvd_of_p_pow_succ_dvd_mul (hξ : ξ.IsDistinguished) {g : 𝕎 S} {n : ℕ}
    (h : (p : 𝕎 S) ^ (n + 1) ∣ ξ * g) : (p : 𝕎 S) ^ n ∣ g := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    obtain ⟨g, rfl⟩ := hξ.p_dvd_of_p_sq_dvd_mul ((pow_dvd_pow _ (by omega)).trans h)
    -- Cancel `p` from `p ^ (n + 2) ∣ ξ (p g)`: it is a nonzerodivisor of `𝕎 S`.
    obtain ⟨c, hc⟩ := h
    rw [pow_succ']
    refine mul_dvd_mul_left _
      (ih ⟨c, (mul_cancel_left_mem_nonZeroDivisors p_mem_nonZeroDivisors).mp ?_⟩)
    linear_combination hc

/-- **`p`-power torsion modulo a distinguished element.** Over a perfect ring of characteristic
`p`, let `ξ` be distinguished. If `ξ` divides `p ^ n f`, then `ξ` divides `p f`
(Bhatt–Morrow–Scholze, *Topological Hochschild homology and integral p-adic Hodge theory*, proof of
Proposition 4.19(3)). -/
theorem dvd_p_mul_of_dvd_p_pow_mul (hξ : ξ.IsDistinguished) {f : 𝕎 S} {n : ℕ}
    (h : ξ ∣ (p : 𝕎 S) ^ n * f) : ξ ∣ (p : 𝕎 S) * f := by
  cases n with
  | zero =>
    rw [pow_zero, one_mul] at h
    exact h.mul_left _
  | succ n =>
    obtain ⟨g, hg⟩ := h
    obtain ⟨c, rfl⟩ := hξ.p_pow_dvd_of_p_pow_succ_dvd_mul ⟨f, hg.symm⟩
    -- Cancel `p ^ n` from `p ^ (n + 1) f = ξ (p ^ n c)`.
    refine ⟨c, (mul_cancel_left_mem_nonZeroDivisors (pow_mem p_mem_nonZeroDivisors n)).mp ?_⟩
    linear_combination hg

/-- **The `p`-power torsion of `𝕎 S ⧸ (ξ)` is killed by `p`.** Over a perfect ring `S` of
characteristic `p`, let `ξ` be distinguished. If `p ^ n x = 0` in `𝕎 S ⧸ (ξ)`, then `p x = 0`
(Bhatt–Morrow–Scholze, *Topological Hochschild homology and integral p-adic Hodge theory*,
Proposition 4.19(3)). -/
theorem p_mul_eq_zero_of_p_pow_mul_eq_zero (hξ : ξ.IsDistinguished)
    {x : 𝕎 S ⧸ span {ξ}} {n : ℕ} (h : (p : 𝕎 S ⧸ span {ξ}) ^ n * x = 0) :
    (p : 𝕎 S ⧸ span {ξ}) * x = 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [← map_natCast (Ideal.Quotient.mk (span {ξ})) p, ← map_pow, ← map_mul,
    Ideal.Quotient.eq_zero_iff_dvd] at h ⊢
  exact hξ.dvd_p_mul_of_dvd_p_pow_mul h

/-- **The `p`-power torsion of `𝕎 S ⧸ (ξ)` is its `p`-torsion.** Over a perfect ring `S` of
characteristic `p`, let `ξ` be distinguished. The submodule of `𝕎 S ⧸ (ξ)` of elements killed by
some power of `p` is the submodule of elements killed by `p`. -/
theorem torsion'_powers_eq_torsionBy (hξ : ξ.IsDistinguished) :
    Submodule.torsion' (𝕎 S ⧸ span {ξ}) (𝕎 S ⧸ span {ξ})
        (Submonoid.powers (p : 𝕎 S ⧸ span {ξ})) =
      Submodule.torsionBy (𝕎 S ⧸ span {ξ}) (𝕎 S ⧸ span {ξ}) (p : 𝕎 S ⧸ span {ξ}) := by
  ext x
  simp only [Submodule.mem_torsion'_iff, Submodule.mem_torsionBy_iff, smul_eq_mul]
  refine ⟨fun ⟨⟨_, n, rfl⟩, hx⟩ ↦ hξ.p_mul_eq_zero_of_p_pow_mul_eq_zero hx,
    fun hx ↦ ⟨⟨p, 1, pow_one _⟩, hx⟩⟩

end IsDistinguished

end WittVector
