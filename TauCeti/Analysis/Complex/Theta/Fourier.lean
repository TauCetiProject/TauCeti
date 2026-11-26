/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.QuasiPeriodic.Fourier
public import TauCeti.Analysis.Complex.Theta.Sections
import TauCeti.Analysis.Fourier.Decay

/-!
# Twisted Fourier recurrence for theta sections

For an entire function `s : ℂ → ℂ` satisfying `s (z + 1) = exp (2πiα) * s z`, moving the line of
integration from `ℝ` to `ℝ + τ` (`Function.Periodic.intervalIntegral_comp_add_eq_of_differentiable`)
shows that the `τ`-automorphy law `s (z + τ) = exp (2πiβ - πikτ - 2πikz) * s z` for an integer
level `k : ℤ` is equivalent to the shift-by-`k` recurrence
`c (m + k) = exp (2πi(m + α)τ - 2πiβ + πikτ) * c m` on the twisted Fourier coefficients
`thetaFourierCoeff α s m`. In particular, vanishing of `thetaFourierCoeff α s` is periodic modulo
`k`.

## Main results

* `TauCeti.thetaFourierCoeff_eq_mul_thetaFourierCoeff_add`: shift-by-`k` coefficient recurrence
  from `τ`-automorphy at integer level `k : ℤ`.
* `TauCeti.forall_add_tau_iff_forall_thetaFourierCoeff_add`: exact equivalence between
  `τ`-automorphy and the Fourier coefficient recurrence.
* `TauCeti.thetaFourierCoeff_add_of_mem_thetaSections`: specialization to `thetaSections`.
* `TauCeti.thetaFourierCoeff_add_eq_zero_iff` and
  `TauCeti.thetaFourierCoeff_add_int_mul_eq_zero_iff`: propagation of vanishing along residue
  classes modulo `k`.

## References

* David Mumford, *Tata Lectures on Theta I*, Progress in Mathematics 28, Birkhäuser, 1983,
  Chapter I, §1–§4.
* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, 2nd edition, Grundlehren
  der mathematischen Wissenschaften 302, Springer, 2004, Chapter 2 and Chapter 3.
-/

public section

open Complex
open scoped Real

namespace TauCeti

/-- Moving the line of integration from `ℝ` to `ℝ + τ` turns the second automorphy law at integer
level `k : ℤ` into the shift-by-`k` recurrence
`c m = exp (2πiβ - πikτ - 2πi(m + α)τ) * c (m + k)` for the twisted Fourier coefficients. -/
theorem thetaFourierCoeff_eq_mul_thetaFourierCoeff_add {k : ℤ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : Differentiable ℂ s) (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z)
    (hτ : ∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z)
    (m : ℤ) :
    thetaFourierCoeff α s m =
      cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * (m + α) * τ) *
        thetaFourierCoeff α s (m + k) := by
  let h : ℂ → ℂ := fun z => cexp (-2 * π * I * (m + α) * z) * s z
  have hper : Function.Periodic h ((1 : ℝ) : ℂ) := by
    simpa only [ofReal_one] using periodic_cexp_mul_of_add_one h1 m
  have key := hper.intervalIntegral_comp_add_eq_of_differentiable
    ((by fun_prop : Differentiable ℂ fun z : ℂ => cexp (-2 * π * I * (m + α) * z)).mul hs) τ
  rw [thetaFourierCoeff_eq_integral, thetaFourierCoeff_eq_integral,
    ← intervalIntegral.integral_const_mul, ← key]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [h, hτ, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private lemma thetaFourierCoeff_add_of_add_tau {k : ℤ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : Differentiable ℂ s) (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z)
    (hτ : ∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z)
    (m : ℤ) :
    thetaFourierCoeff α s (m + k) =
      cexp (2 * π * I * (m + α) * τ - 2 * π * I * β + π * I * k * τ) *
        thetaFourierCoeff α s m := by
  rw [thetaFourierCoeff_eq_mul_thetaFourierCoeff_add hs h1 hτ m, ← mul_assoc, ← Complex.exp_add]
  have h0 : 2 * π * I * (m + α) * τ - 2 * π * I * β + π * I * k * τ +
      (2 * π * I * β - π * I * k * τ - 2 * π * I * (m + α) * τ) = 0 := by ring
  rw [h0, Complex.exp_zero, one_mul]

/-- **Fourier recurrence characterization.** For an entire function `s` satisfying
`s (z + 1) = exp (2πiα) * s z` and any integer level `k : ℤ`, the second automorphy relation
`s (z + τ) = exp (2πiβ - πikτ - 2πikz) * s z` holds for all `z ∈ ℂ` if and only if its twisted
Fourier coefficients satisfy `c (m + k) = exp (2πi(m + α)τ - 2πiβ + πikτ) * c m` for all
`m ∈ ℤ`. -/
theorem forall_add_tau_iff_forall_thetaFourierCoeff_add {k : ℤ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : Differentiable ℂ s) (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) :
    (∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z) ↔
      ∀ m : ℤ, thetaFourierCoeff α s (m + k) =
        cexp (2 * π * I * (m + α) * τ - 2 * π * I * β + π * I * k * τ) *
          thetaFourierCoeff α s m := by
  refine ⟨fun hτ m => thetaFourierCoeff_add_of_add_tau hs h1 hτ m, fun hrec z => ?_⟩
  have hL := hasSum_thetaFourierCoeff hs h1 (z + τ)
  have hR := (hasSum_thetaFourierCoeff hs h1 z).mul_left
    (cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z))
  rw [← (Equiv.addRight k).hasSum_iff] at hR
  have hR' : HasSum
      (fun m : ℤ => thetaFourierCoeff α s m * cexp (2 * π * I * (m + α) * (z + τ)))
      (cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z) := by
    refine hR.congr_fun fun m => ?_
    simp only [Function.comp_def, Equiv.coe_addRight, hrec m]
    calc
      thetaFourierCoeff α s m * cexp (2 * π * I * (m + α) * (z + τ)) =
          thetaFourierCoeff α s m *
            (cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) *
              cexp (2 * π * I * (m + α) * τ - 2 * π * I * β + π * I * k * τ) *
              cexp (2 * π * I * ((m + k : ℤ) + α) * z)) := by
        simp only [← Complex.exp_add]
        congr 2
        push_cast
        ring
      _ = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) *
            (cexp (2 * π * I * (m + α) * τ - 2 * π * I * β + π * I * k * τ) *
              thetaFourierCoeff α s m * cexp (2 * π * I * ((m + k : ℤ) + α) * z)) := by ring
  exact hL.unique hR'

/-- The twisted Fourier coefficients of a level-`k` theta section satisfy the shift-by-`k`
recurrence `c (m + k) = exp (2πi(m + α)τ - 2πiβ + πikτ) * c m`. -/
theorem thetaFourierCoeff_add_of_mem_thetaSections {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (m : ℤ) :
    thetaFourierCoeff α s (m + k) =
      cexp (2 * π * I * (m + α) * τ - 2 * π * I * β + π * I * k * τ) *
        thetaFourierCoeff α s m := by
  rcases mem_thetaSections_iff.mp hs with ⟨hd, h1, hτ⟩
  exact thetaFourierCoeff_add_of_add_tau (k := (k : ℤ)) hd h1
    (by simpa only [Int.cast_natCast] using hτ) m

/-- For a level-`k` theta section, vanishing of the `m`-th twisted Fourier coefficient is
equivalent to vanishing of the `(m + k)`-th coefficient. -/
theorem thetaFourierCoeff_add_eq_zero_iff {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (m : ℤ) :
    thetaFourierCoeff α s (m + k) = 0 ↔ thetaFourierCoeff α s m = 0 := by
  rw [thetaFourierCoeff_add_of_mem_thetaSections hs m, mul_eq_zero,
    or_iff_right (Complex.exp_ne_zero _)]

/-- For a level-`k` theta section, vanishing of twisted Fourier coefficients is invariant under
shifting the index by multiples of `k`. -/
theorem thetaFourierCoeff_add_int_mul_eq_zero_iff {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (n q : ℤ) :
    thetaFourierCoeff α s (n + q * k) = 0 ↔ thetaFourierCoeff α s n = 0 := by
  have hper : Function.Periodic (fun m : ℤ => thetaFourierCoeff α s m = 0) (k : ℤ) :=
    fun m => propext (thetaFourierCoeff_add_eq_zero_iff hs m)
  exact iff_of_eq (hper.int_mul q n)

end TauCeti
