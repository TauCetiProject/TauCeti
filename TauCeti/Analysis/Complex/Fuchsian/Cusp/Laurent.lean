/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Growth
public import TauCeti.Topology.Algebra.InfiniteSum.NatInt
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
connected to the actual quotient function rather than merely recording its coefficients. The
coefficients are uniquely characterized by this convergence, so the resulting series is
independent of the valid growth bound `k` used to construct it.

## Main declarations

* `TauCeti.Subgroup.CuspDatum.twistedQExpansion`: the Taylor series of the bounded twisted
  extension.
* `TauCeti.Subgroup.CuspDatum.laurentQExpansion`: that power series shifted by `-k`, as a formal
  Laurent series.
* `TauCeti.Subgroup.CuspDatum.hasSum_laurentQExpansion`: convergence of the Laurent expansion on
  the punctured q-disc.
* `TauCeti.Subgroup.CuspDatum.hasSum_laurentQExpansion_coordinate`: the corresponding expansion
  of the original function on the upper half-plane.
* `TauCeti.Subgroup.CuspDatum.laurentQExpansion_coeff_unique`: any convergent Laurent expansion
  supported in the prescribed range has these coefficients.
* `TauCeti.Subgroup.CuspDatum.laurentQExpansion_eq`: the expansion is independent of the valid
  growth bound used in its construction.

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
hypotheses of `hasSum_twistedQExpansion` (invariance, holomorphy, and the growth bound for `k`),
this series converges on the open unit disc to `twistedExtension D k f`. -/
def twistedQExpansion (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ) : PowerSeries ℂ :=
  UpperHalfPlane.qExpansion D.width fun z ↦ cuspTwist D k f (D.scaling⁻¹ • z)

/-- The twisted q-expansion is Mathlib's q-expansion of the twist in the scaling coordinate. -/
theorem twistedQExpansion_def (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ) :
    twistedQExpansion D k f =
      UpperHalfPlane.qExpansion D.width fun z ↦ cuspTwist D k f (D.scaling⁻¹ • z) := (rfl)

/-- The coefficients of the twisted q-expansion are the Taylor coefficients of the twisted
extension at the cusp. -/
theorem twistedQExpansion_coeff (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ) (n : ℕ) :
    (twistedQExpansion D k f).coeff n =
      (n.factorial : ℂ)⁻¹ * iteratedDeriv n (twistedExtension D k f) 0 := by
  rw [twistedQExpansion, UpperHalfPlane.qExpansion_coeff]
  rw [twistedExtension_def, cuspExtension_def]

/-- The constant coefficient of the twisted q-expansion is the value of the twisted extension
at the cusp. -/
@[simp]
theorem twistedQExpansion_coeff_zero (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ) :
    (twistedQExpansion D k f).coeff 0 = twistedExtension D k f 0 := by
  rw [twistedQExpansion_coeff]
  simp

/-- The Taylor series of the twisted extension, shifted by `X⁻ᵏ`, so that it is supported in
exponents at least `-k`. Under the growth bound for `k`, it is independent of `k` by
`laurentQExpansion_eq`. -/
def laurentQExpansion (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ) : LaurentSeries ℂ :=
  HahnSeries.single (-k) 1 * (twistedQExpansion D k f : LaurentSeries ℂ)

/-- The Laurent q-expansion is the twisted q-expansion shifted down by `k`. -/
theorem laurentQExpansion_def (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ) :
    laurentQExpansion D k f =
      HahnSeries.single (-k) 1 * (twistedQExpansion D k f : LaurentSeries ℂ) := (rfl)

/-- The coefficient of the Laurent q-expansion at an arbitrary integer exponent. -/
theorem laurentQExpansion_coeff (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ) (j : ℤ) :
    (laurentQExpansion D k f).coeff j = if 0 ≤ j + k then
      (twistedQExpansion D k f).coeff (j + k).toNat else 0 := by
  rw [laurentQExpansion_def, HahnSeries.coeff_single_mul, one_mul, PowerSeries.coeff_coe]
  split_ifs <;> congr <;> omega

/-- The coefficient of exponent `n - k` in the Laurent expansion is the `n`-th coefficient of
the Taylor series of the twisted extension. -/
@[simp]
theorem laurentQExpansion_coeff_natCast_sub (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ) (n : ℕ) :
    (laurentQExpansion D k f).coeff ((n : ℤ) - k) =
      (twistedQExpansion D k f).coeff n := by
  rw [laurentQExpansion_coeff]
  simp

/-- There are no Laurent coefficients below the prescribed lower exponent `-k`. -/
theorem laurentQExpansion_coeff_eq_zero_of_lt_neg (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    {j : ℤ} (hj : j < -k) :
    (laurentQExpansion D k f).coeff j = 0 := by
  rw [laurentQExpansion_coeff, ite_eq_right]
  exact fun h ↦ by omega

/-- The coefficient at the lowest permitted exponent is the value of the twisted extension at
the cusp. -/
@[simp]
theorem laurentQExpansion_coeff_neg (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ) :
    (laurentQExpansion D k f).coeff (-k) = twistedExtension D k f 0 := by
  simpa using (laurentQExpansion_coeff_natCast_sub D k f 0).trans
    (twistedQExpansion_coeff_zero D k f)

/-- Under the exponential bound corresponding to `k`, the Taylor series of the twisted extension
converges to that extension at every point of the open unit disc. -/
theorem hasSum_twistedQExpansion (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width))
    {q : ℂ} (hq_norm : ‖q‖ < 1) :
    HasSum (fun n : ℕ ↦ (twistedQExpansion D k f).coeff n * q ^ n)
      (twistedExtension D k f q) := by
  rw [twistedExtension_def, cuspExtension_def]
  simpa only [twistedQExpansion, smul_eq_mul] using
    UpperHalfPlane.hasSum_qExpansion_of_norm_lt D.width_pos
      (periodic_comp_ofComplex_inv_smul D (cuspTwist D k f) (cuspTwist_smul D k f hf))
      (mdifferentiable_inv_smul D (cuspTwist D k f)
        (mdifferentiable_cuspTwist D k f hhol))
      (isBoundedAtImInfty_cuspTwist_inv_smul D k f hbound) hq_norm

/-- The coefficient at the lowest permitted exponent `-k` is the limiting value of the twisted
function in the scaling coordinate. -/
theorem laurentQExpansion_coeff_neg_eq_valueAtInfty (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width)) :
    (laurentQExpansion D k f).coeff (-k) =
      valueAtInfty (fun z : ℍ ↦
        Function.Periodic.qParam D.width z ^ k * f (D.scaling⁻¹ • z)) := by
  rw [laurentQExpansion_coeff_neg,
    twistedExtension_zero_eq_valueAtInfty D k f hf hhol hbound]

/-- The Laurent q-expansion converges to the cusp extension throughout the punctured unit disc,
when reindexed over its potentially nonzero coefficients. -/
theorem hasSum_laurentQExpansion_natCast_sub (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width))
    {q : ℂ} (hq : q ≠ 0) (hq_norm : ‖q‖ < 1) :
    HasSum (fun n : ℕ ↦
      (laurentQExpansion D k f).coeff ((n : ℤ) - k) * q ^ ((n : ℤ) - k))
      (cuspExtension D f q) := by
  rw [cuspExtension_eq_zpow_mul_twistedExtension_of_ne_zero_of_norm_lt_one
    D k f hf hq hq_norm]
  simp_rw [laurentQExpansion_coeff_natCast_sub]
  apply (hasSum_mul_zpow_natCast_sub_iff hq k).2
  simpa only [zpow_neg, mul_inv_cancel_left₀ (zpow_ne_zero k hq)] using
    hasSum_twistedQExpansion D k f hf hhol hbound hq_norm

/-- Reindex a Laurent q-expansion supported in exponents at least `-k` by `n - k'`, for any
`k'` at least `k`. -/
theorem hasSum_laurentQExpansion_natCast_sub_iff (D : Γ.CuspDatum) {k k' : ℤ}
    (hkk' : k ≤ k') (f : ℍ → ℂ) {q s : ℂ} :
    HasSum (fun j : ℤ ↦ (laurentQExpansion D k f).coeff j * q ^ j) s ↔
      HasSum (fun n : ℕ ↦
        (laurentQExpansion D k f).coeff ((n : ℤ) - k') * q ^ ((n : ℤ) - k')) s :=
  hasSum_int_iff_natCast_sub fun j hj ↦ by
    rw [laurentQExpansion_coeff_eq_zero_of_lt_neg D k f (lt_of_lt_of_le hj (by omega)),
      zero_mul]

/-- The Laurent q-expansion, summed over all integer exponents, converges to the cusp extension
throughout the punctured unit disc. -/
theorem hasSum_laurentQExpansion (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width))
    {q : ℂ} (hq : q ≠ 0) (hq_norm : ‖q‖ < 1) :
    HasSum (fun j : ℤ ↦ (laurentQExpansion D k f).coeff j * q ^ j)
      (cuspExtension D f q) := by
  apply (hasSum_laurentQExpansion_natCast_sub_iff D (le_refl k) f).mpr
  exact hasSum_laurentQExpansion_natCast_sub D k f hf hhol hbound hq hq_norm

/-- Pulling the Laurent q-expansion back by the normalized cusp coordinate gives the original
function on the upper half-plane, when reindexed over its potentially nonzero coefficients. -/
theorem hasSum_laurentQExpansion_coordinate_natCast_sub (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width))
    (z : ℍ) :
    HasSum (fun n : ℕ ↦
      (laurentQExpansion D k f).coeff ((n : ℤ) - k) *
        coordinate D z ^ ((n : ℤ) - k)) (f z) := by
  simpa only [cuspExtension_coordinate D f hf] using
    hasSum_laurentQExpansion_natCast_sub D k f hf hhol hbound (coordinate_ne_zero D z)
      (norm_coordinate_lt_one D z)

/-- Summing the Laurent q-expansion over every integer exponent after pullback by the normalized
cusp coordinate gives the original function on the upper half-plane. -/
theorem hasSum_laurentQExpansion_coordinate (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width))
    (z : ℍ) :
    HasSum (fun j : ℤ ↦
      (laurentQExpansion D k f).coeff j * coordinate D z ^ j) (f z) := by
  simpa only [cuspExtension_coordinate D f hf] using
    hasSum_laurentQExpansion D k f hf hhol hbound (coordinate_ne_zero D z)
      (norm_coordinate_lt_one D z)

/-- A Laurent series supported in exponents at least `-k` and converging to `f` in the cusp
coordinate has the coefficients of `laurentQExpansion D k f`. -/
theorem laurentQExpansion_coeff_unique (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width))
    {c : ℤ → ℂ} (hc : ∀ j < -k, c j = 0)
    (hsum : ∀ z, HasSum (fun j : ℤ ↦ c j * coordinate D z ^ j) (f z)) (j : ℤ) :
    c j = (laurentQExpansion D k f).coeff j := by
  by_cases hj : j < -k
  · rw [hc j hj, laurentQExpansion_coeff_eq_zero_of_lt_neg D k f hj]
  · let n := (j + k).toNat
    have hn : (n : ℤ) - k = j := by
      simp only [n]
      omega
    rw [← hn, laurentQExpansion_coeff_natCast_sub, twistedQExpansion_def]
    -- Keep the generic Fuchsian layer independent of the modular-forms layer containing the
    -- raw-function variant; Mathlib's theorem instead accepts this continuous-map wrapper.
    let F : C(ℍ, ℂ) := ⟨fun z ↦ cuspTwist D k f (D.scaling⁻¹ • z),
      (mdifferentiable_inv_smul D (cuspTwist D k f)
        (mdifferentiable_cuspTwist D k f hhol)).continuous⟩
    refine UpperHalfPlane.qExpansion_coeff_unique F
      (c := fun m ↦ c ((m : ℤ) - k)) D.width_pos ?_ ?_ n
    · simpa only [F, ContinuousMap.coe_mk, twistedExtension_def, cuspExtension_def] using
        analyticAt_twistedExtension_zero D k f hf hhol hbound
    · intro z
      have hsum' := hsum (D.scaling⁻¹ • z)
      rw [coordinate_inv_smul] at hsum'
      have hreindexed := (hasSum_int_iff_natCast_sub fun j hj ↦ by
        rw [hc j hj, zero_mul]).mp hsum'
      simp only [F, ContinuousMap.coe_mk]
      rw [cuspTwist_inv_smul D k f z]
      simp only [smul_eq_mul]
      exact (hasSum_mul_zpow_natCast_sub_iff
        (Function.Periodic.qParam_ne_zero z) k).mp hreindexed

/-- Increasing a valid exponential growth rate does not change the Laurent q-expansion. -/
theorem laurentQExpansion_eq_of_le (D : Γ.CuspDatum) {k k' : ℤ} (f : ℍ → ℂ)
    (hkk' : k ≤ k')
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width)) :
    laurentQExpansion D k f = laurentQExpansion D k' f := by
  apply HahnSeries.ext
  funext j
  exact laurentQExpansion_coeff_unique D k' f hf hhol
    (TauCeti.UpperHalfPlane.isBigO_exp_of_le D.width D.width_pos
      (k := (k : ℝ)) (k' := (k' : ℝ)) (by exact_mod_cast hkk') hbound)
    (fun j hj ↦ laurentQExpansion_coeff_eq_zero_of_lt_neg D k f (by omega))
    (hasSum_laurentQExpansion_coordinate D k f hf hhol hbound) j

/-- If `k ≤ k'`, the coefficients of the Laurent expansion constructed using the `k`-bound,
reindexed by `n - k'`, are the Taylor coefficients of the `k'`-twisted extension. -/
theorem laurentQExpansion_coeff_natCast_sub_of_le (D : Γ.CuspDatum) {k k' : ℤ}
    (hkk' : k ≤ k') (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width)) (n : ℕ) :
    (laurentQExpansion D k f).coeff ((n : ℤ) - k') =
      (twistedQExpansion D k' f).coeff n := by
  rw [laurentQExpansion_eq_of_le D f hkk' hf hhol hbound,
    laurentQExpansion_coeff_natCast_sub]

/-- The Laurent q-expansion is independent of which valid exponential growth bound is used to
construct it. -/
theorem laurentQExpansion_eq (D : Γ.CuspDatum) (k k' : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width))
    (hbound' : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k' : ℝ) * z.im / D.width)) :
    laurentQExpansion D k f = laurentQExpansion D k' f := by
  rcases le_total k k' with hkk' | hk'k
  · exact laurentQExpansion_eq_of_le D f hkk' hf hhol hbound
  · exact (laurentQExpansion_eq_of_le D f hk'k hf hhol hbound').symm

end TauCeti.Subgroup.CuspDatum
