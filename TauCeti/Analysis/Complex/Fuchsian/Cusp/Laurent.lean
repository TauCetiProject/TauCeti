/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Growth
public import Mathlib.RingTheory.LaurentSeries

/-!
# Laurent expansions at a Fuchsian cusp

Let `D` be normalized cusp data of width `w`, and suppose that an invariant holomorphic function
`f` grows no faster than `exp (2 * π * k * y / w)` in the scaling coordinate. Multiplication by
the `k`-th power of the q-coordinate gives a bounded holomorphic function. Its Taylor series at
zero, shifted down by `k`, is the Laurent expansion of `f` at the cusp.

This file packages that construction as a formal `LaurentSeries ℂ`. It proves that all
coefficients below exponent `-k` vanish and, more importantly, that the resulting Laurent series
converges to the descended function throughout the punctured unit disc. Thus the formal series is
connected to the actual quotient function rather than merely recording its coefficients.

## Main declarations

* `TauCeti.Subgroup.CuspDatum.laurentNumerator`: the Taylor series of the bounded twisted
  extension.
* `TauCeti.Subgroup.CuspDatum.laurentQExpansion`: that power series shifted by `-k`, as a formal
  Laurent series.
* `TauCeti.Subgroup.CuspDatum.hasSum_laurentQExpansion`: convergence of the Laurent expansion on
  the punctured q-disc.
* `TauCeti.Subgroup.CuspDatum.hasSum_laurentQExpansion_coordinate`: the corresponding expansion
  of the original function on the upper half-plane.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §2.4.
* Otto Forster, *Lectures on Riemann Surfaces*, §19.
-/

public noncomputable section

open Asymptotics Filter Function Matrix.ProjectiveSpecialLinearGroup MulAction UpperHalfPlane
open scoped Complex.UnitDisc ContDiff Manifold MatrixGroups Topology

namespace TauCeti.Subgroup.CuspDatum

variable {Γ : Subgroup PSL(2, ℝ)}

/-- The Taylor series at zero of the q-extension obtained after twisting by `q^k`. Under the
growth hypothesis of `hasSum_laurentNumerator`, this series converges on the open unit disc to
`twistedExtension D k f`. -/
def laurentNumerator (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ) : PowerSeries ℂ :=
  UpperHalfPlane.qExpansion D.width fun z ↦ cuspTwist D k f (D.scaling⁻¹ • z)

/-- The coefficients of the Laurent numerator are the Taylor coefficients of the twisted
extension at the cusp. -/
@[simp]
theorem laurentNumerator_coeff (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ) (n : ℕ) :
    (laurentNumerator D k f).coeff n =
      (n.factorial : ℂ)⁻¹ * iteratedDeriv n (twistedExtension D k f) 0 := by
  rw [laurentNumerator, UpperHalfPlane.qExpansion_coeff]
  rw [twistedExtension_def, cuspExtension_def]

/-- The Laurent q-expansion with lower exponent `-k`: shift the Taylor series of the bounded
twisted extension by the monomial `X⁻ᵏ`. -/
def laurentQExpansion (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ) : LaurentSeries ℂ :=
  HahnSeries.single (-k) 1 * (laurentNumerator D k f : LaurentSeries ℂ)

/-- The coefficient of exponent `n - k` in the Laurent expansion is the `n`-th coefficient of
the Taylor series of the twisted extension. -/
@[simp]
theorem laurentQExpansion_coeff_sub (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ) (n : ℕ) :
    (laurentQExpansion D k f).coeff ((n : ℤ) - k) =
      (laurentNumerator D k f).coeff n := by
  rw [laurentQExpansion, HahnSeries.coeff_single_mul]
  have hindex : (n : ℤ) - k - -k = (n : ℤ) := by omega
  rw [hindex]
  simp [PowerSeries.coeff_coe]

/-- There are no Laurent coefficients below the prescribed lower exponent `-k`. -/
theorem laurentQExpansion_coeff_eq_zero_of_lt (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    {j : ℤ} (hj : j < -k) :
    (laurentQExpansion D k f).coeff j = 0 := by
  rw [laurentQExpansion, HahnSeries.coeff_single_mul, one_mul, PowerSeries.coeff_coe]
  rw [ite_eq_left]
  omega

/-- Under the exponential bound corresponding to `k`, the Taylor series of the twisted extension
converges to that extension at every point of the open unit disc. -/
theorem hasSum_laurentNumerator (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width))
    {q : ℂ} (hq_norm : ‖q‖ < 1) :
    HasSum (fun n : ℕ ↦ (laurentNumerator D k f).coeff n * q ^ n)
      (twistedExtension D k f q) := by
  rw [twistedExtension_def, cuspExtension_def]
  simpa only [laurentNumerator, smul_eq_mul] using
    UpperHalfPlane.hasSum_qExpansion_of_norm_lt D.width_pos
      (periodic_comp_ofComplex_inv_smul D (cuspTwist D k f) (cuspTwist_smul D k f hf))
      (mdifferentiable_inv_smul D (cuspTwist D k f)
        (mdifferentiable_cuspTwist D k f hhol))
      (isBoundedAtImInfty_cuspTwist_inv_smul D k f hbound) hq_norm

/-- The coefficient at the lowest permitted exponent `-k` is the limiting value of the twisted
function in the scaling coordinate. -/
theorem laurentQExpansion_coeff_neg_k (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width)) :
    (laurentQExpansion D k f).coeff (-k) =
      valueAtInfty (fun z : ℍ ↦ cuspTwist D k f (D.scaling⁻¹ • z)) := by
  have hindex : -k = ((0 : ℕ) : ℤ) - k := by omega
  rw [hindex, laurentQExpansion_coeff_sub]
  apply UpperHalfPlane.qExpansion_coeff_zero D.width_pos
  · rw [← cuspExtension_def, ← twistedExtension_def]
    exact analyticAt_twistedExtension_zero D k f hf hhol hbound
  · exact periodic_comp_ofComplex_inv_smul D (cuspTwist D k f) (cuspTwist_smul D k f hf)

/-- The Laurent q-expansion converges to the cusp extension throughout the punctured unit disc.
The summation is indexed by `n : ℕ`; its exponent is the corresponding Laurent exponent
`n - k`. -/
theorem hasSum_laurentQExpansion (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width))
    {q : ℂ} (hq : q ≠ 0) (hq_norm : ‖q‖ < 1) :
    HasSum (fun n : ℕ ↦
      (laurentQExpansion D k f).coeff ((n : ℤ) - k) * q ^ ((n : ℤ) - k))
      (cuspExtension D f q) := by
  have hsum := (hasSum_laurentNumerator D k f hf hhol hbound hq_norm).mul_left (q ^ (-k))
  rw [cuspExtension_eq_zpow_mul_twistedExtension_of_ne_zero_of_norm_lt_one
    D k f hf hq hq_norm]
  have hterms :
      (fun n : ℕ ↦ (laurentQExpansion D k f).coeff ((n : ℤ) - k) *
        q ^ ((n : ℤ) - k)) =
      fun n : ℕ ↦ q ^ (-k) * ((laurentNumerator D k f).coeff n * q ^ n) := by
    funext n
    rw [laurentQExpansion_coeff_sub]
    have hindex : (n : ℤ) - k = -k + (n : ℤ) := by omega
    rw [hindex, zpow_add₀ hq, zpow_natCast]
    ring
  rw [hterms]
  exact hsum

/-- Pulling the Laurent q-expansion back by the normalized cusp coordinate gives the original
function on the upper half-plane. -/
theorem hasSum_laurentQExpansion_coordinate (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width))
    (z : ℍ) :
    HasSum (fun n : ℕ ↦
      (laurentQExpansion D k f).coeff ((n : ℤ) - k) *
        coordinate D z ^ ((n : ℤ) - k)) (f z) := by
  simpa only [cuspExtension_coordinate D f hf] using
    hasSum_laurentQExpansion D k f hf hhol hbound (coordinate_ne_zero D z)
      (norm_coordinate_lt_one D z)

end TauCeti.Subgroup.CuspDatum
