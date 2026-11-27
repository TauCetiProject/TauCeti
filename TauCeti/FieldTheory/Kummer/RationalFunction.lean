/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.RationalRoot
import TauCeti.FieldTheory.Kummer.Capelli

/-!
# Binomials over a rational function field

Let `F` be a field and `K = F(X)` the fraction field of `F[X]`. For `c ∈ F` with `c ≠ 0` and
`f ∈ F[X]`, the binomial `Tᵉ - c / f` is irreducible over `K` when `f` is not of the form
`C b * hˡ` for any `ℓ > 1` dividing `e` (`Polynomial.irreducible_X_pow_sub_C_div`).

The proof applies Capelli's theorem (`TauCeti.X_pow_sub_C_irreducible_of_forall_prime`). If
`bˡ = d / f` for some `b ∈ K` and a nonzero constant `d`, then `b⁻¹` is a root of the monic
polynomial `Tˡ - C d⁻¹ * f` over `F[X]`, so `b⁻¹` lies in `F[X]` because `F[X]` is integrally
closed, and `f = C d * (b⁻¹)ˡ`. The case `-4 b⁴ = c / f` with `4 ∣ e` is the case `ℓ = 4`,
`d = c / -4`.

This is the irreducibility of `Y^e - f(X)` over `F(X)` that Stepanov's method for `y^e = f(x)`
uses.
-/

public section

open Polynomial

namespace Polynomial

variable {F : Type*} [Field F]

/-- Over the fraction field of `F[X]`, the binomial `Tᵉ - c / f` is irreducible when `c ≠ 0` and
`f` is not of the form `C b * hˡ` for any `ℓ > 1` dividing `e`. -/
theorem irreducible_X_pow_sub_C_div {e : ℕ} (he : e ≠ 0) {f : F[X]} {c : F} (hc : c ≠ 0)
    (hf : ∀ (b : F) (h : F[X]) (ℓ : ℕ), 1 < ℓ → ℓ ∣ e → f ≠ C b * h ^ ℓ) :
    Irreducible (X ^ e - C (algebraMap F[X] (FractionRing F[X]) (C c) /
      algebraMap F[X] (FractionRing F[X]) f)) := by
  -- For `f = 0`, the hypothesis forces `e = 1`, and `T - 0` is irreducible.
  rcases eq_or_ne f 0 with rfl | hf₀
  · obtain rfl : e = 1 := by
      by_contra he1
      exact hf 0 0 e (by lia) dvd_rfl (by simp [he])
    rw [pow_one]
    exact irreducible_X_sub_C _
  set K := FractionRing F[X]
  have hinj := IsFractionRing.injective F[X] K
  have hfK : algebraMap F[X] K f ≠ 0 := (map_ne_zero_iff _ hinj).2 hf₀
  -- If `b ^ ℓ = d / f` with `d` a nonzero constant, then `b⁻¹ ^ ℓ` is the polynomial
  -- `C d⁻¹ * f`, so `b⁻¹` is a polynomial `g` since `F[X]` is integrally closed, and
  -- `f = C d * g ^ ℓ`.
  have key : ∀ (ℓ : ℕ) (d : F), 1 < ℓ → ℓ ∣ e → d ≠ 0 → ∀ b : K,
      b ^ ℓ ≠ algebraMap F[X] K (C d) / algebraMap F[X] K f := by
    intro ℓ d hℓ hℓe hd b hb
    have hCinv : algebraMap F[X] K (C d⁻¹) = (algebraMap F[X] K (C d))⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← map_mul, ← C_mul, inv_mul_cancel₀ hd, C_1, map_one])
    have hpow : b⁻¹ ^ ℓ = algebraMap F[X] K (C d⁻¹ * f) := by
      rw [inv_pow, hb, inv_div, map_mul, hCinv, div_eq_inv_mul]
    have hint : IsIntegral F[X] b⁻¹ :=
      IsIntegral.of_pow (by lia) (hpow ▸ isIntegral_algebraMap)
    obtain ⟨g, hg⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
    have hgf : g ^ ℓ = C d⁻¹ * f := hinj (by rw [map_pow, hg, hpow])
    refine hf d g ℓ hℓ hℓe ?_
    rw [hgf, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hd, C_1, one_mul]
  refine TauCeti.X_pow_sub_C_irreducible_of_forall_prime he
    (fun ℓ hℓ hℓe b ↦ key ℓ c hℓ.one_lt hℓe hc b) fun h4 b hb ↦ ?_
  have h4K : (-4 : K) = algebraMap F[X] K (C (-4)) := by simp only [map_neg, map_ofNat]
  have h4F : (-4 : F) ≠ 0 := by
    intro h4F
    rw [h4K, h4F, C_0, map_zero, zero_mul, eq_comm, div_eq_zero_iff] at hb
    exact hb.elim ((map_ne_zero_iff _ hinj).2 (C_ne_zero.2 hc)) hfK
  refine key 4 (c / -4) (by norm_num) h4 (div_ne_zero hc h4F) b ?_
  have h4K0 : (-4 : K) ≠ 0 := by
    rw [h4K]
    exact (map_ne_zero_iff _ hinj).2 (C_ne_zero.2 h4F)
  have hinv : algebraMap F[X] K (C (-4)⁻¹) = (-4 : K)⁻¹ := by
    rw [h4K]
    exact map_inv₀ ((algebraMap F[X] K).comp C) (-4)
  rw [div_eq_mul_inv c, C_mul, map_mul, hinv, mul_comm (algebraMap F[X] K (C c)), mul_div_assoc,
    ← hb, ← mul_assoc, inv_mul_cancel₀ h4K0, one_mul]

end Polynomial
