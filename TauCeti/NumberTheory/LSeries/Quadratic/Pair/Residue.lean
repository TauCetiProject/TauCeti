/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.Quadratic.Pair.Basic
public import TauCeti.Analysis.Contour.Residue.Basic

/-!
# Poles of the four-factor Dirichlet L-function product

For nonprincipal characters `χ` and `ψ`, the product
`F(s) = ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)` has a simple pole at `1` if the product
character is nonprincipal, and a double pole otherwise. This includes characters of different
levels: the product character is taken at their least common multiple, exactly as in
`DirichletCharacter.zetaMulPairCoeffs`.

We compute the leading Laurent coefficients and the residues after multiplication by an
arbitrary function analytic at `1`. In the double-pole case the residue is the derivative of
the analytic regularization, not its value. The missing Euler factors of the principal
character remain in `LFunctionTrivChar₁ (Nat.lcm M N)`; its value at `1` is
`∏ p ∈ (Nat.lcm M N).primeFactors, (1 - p⁻¹)`.

The pole calculations use nonvanishing of nonprincipal L-functions at `1`, and so do not
require the characters to be quadratic. For quadratic characters these are the pole terms
in the two-character contour argument. In particular, equal quadratic characters give the
double-pole case, not the simple-pole formula.

## References

* H. Davenport, *Multiplicative Number Theory*, chapter on Siegel's theorem.
-/

public section

open Complex Filter
open scoped Topology

namespace DirichletCharacter

variable {M N : ℕ} [NeZero M] [NeZero N]
variable (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N)

private theorem pair_simple_factorization :
    (fun s ↦ riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s)
      =ᶠ[𝓝[≠] 1] fun s ↦ (s - 1) ^ (-1 : ℤ) •
        (LFunctionTrivChar₁ 1 s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s) := by
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s ≠ 1 := hs
  rw [LFunctionTrivChar₁, Function.update_of_ne hs1, LFunctionTrivChar, LFunction_modOne_eq]
  simp only [smul_eq_mul, zpow_neg_one]
  field_simp

private theorem pair_double_factorization (hχψ : χ.mul ψ = 1) :
    (fun s ↦ riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s)
      =ᶠ[𝓝[≠] 1] fun s ↦ (s - 1) ^ (-2 : ℤ) •
        (LFunctionTrivChar₁ 1 s * χ.LFunction s * ψ.LFunction s *
          LFunctionTrivChar₁ (Nat.lcm M N) s) := by
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s ≠ 1 := hs
  rw [hχψ, LFunctionTrivChar₁, Function.update_of_ne hs1, LFunctionTrivChar, LFunction_modOne_eq,
    LFunctionTrivChar₁, Function.update_of_ne hs1]
  simp only [smul_eq_mul, zpow_neg, zpow_ofNat]
  field_simp

private theorem analyticAt_pair_simple_regularization (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hχψ : χ.mul ψ ≠ 1) :
    AnalyticAt ℂ (fun s ↦ LFunctionTrivChar₁ 1 s * χ.LFunction s * ψ.LFunction s *
      (χ.mul ψ).LFunction s) 1 :=
  ((((differentiable_LFunctionTrivChar₁ 1).mul (differentiable_LFunction hχ)).mul
    (differentiable_LFunction hψ)).mul (differentiable_LFunction hχψ)).analyticAt 1

private theorem analyticAt_pair_double_regularization (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    AnalyticAt ℂ (fun s ↦ LFunctionTrivChar₁ 1 s * χ.LFunction s * ψ.LFunction s *
      LFunctionTrivChar₁ (Nat.lcm M N) s) 1 :=
  ((((differentiable_LFunctionTrivChar₁ 1).mul (differentiable_LFunction hχ)).mul
    (differentiable_LFunction hψ)).mul
      (differentiable_LFunctionTrivChar₁ (Nat.lcm M N))).analyticAt 1

/-- The four-factor product of nonprincipal characters has an exactly simple pole at `1`
when the product character is nonprincipal. -/
theorem meromorphicOrderAt_pair_eq_neg_one (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hχψ : χ.mul ψ ≠ 1) :
    meromorphicOrderAt
      (fun s ↦ riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s) 1 = -1 := by
  have ha := analyticAt_pair_simple_regularization χ ψ hχ hψ hχψ
  have he := pair_simple_factorization χ ψ
  have hm := MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr ⟨-1, _, ha, he⟩
  exact (meromorphicOrderAt_eq_int_iff hm).mpr ⟨_, ha,
    by simpa [LFunctionTrivChar₁] using
      mul_ne_zero (mul_ne_zero (LFunction_apply_one_ne_zero hχ)
        (LFunction_apply_one_ne_zero hψ)) (LFunction_apply_one_ne_zero hχψ), he⟩

/-- The four-factor product of nonprincipal characters has an exactly double pole at `1`
when their product at the common level is principal. -/
theorem meromorphicOrderAt_pair_eq_neg_two (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hχψ : χ.mul ψ = 1) :
    meromorphicOrderAt
      (fun s ↦ riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s) 1 = -2 := by
  have ha := analyticAt_pair_double_regularization χ ψ hχ hψ
  have he := pair_double_factorization χ ψ hχψ
  have hm := MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr ⟨-2, _, ha, he⟩
  exact (meromorphicOrderAt_eq_int_iff hm).mpr ⟨_, ha,
    mul_ne_zero (mul_ne_zero (mul_ne_zero (LFunctionTrivChar₁_apply_one_ne_zero 1)
      (LFunction_apply_one_ne_zero hχ)) (LFunction_apply_one_ne_zero hψ))
        (LFunctionTrivChar₁_apply_one_ne_zero _), he⟩

/-- The residue at `1` of the four-factor product, with an analytic weight, in the simple-pole
case. The weight may vanish at `1`. -/
theorem residue_pair_mul_of_mul_ne_one (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hχψ : χ.mul ψ ≠ 1) {w : ℂ → ℂ} (hw : AnalyticAt ℂ w 1) :
    TauCeti.Contour.residue
      (fun s ↦ riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s * w s) 1 =
        χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1 * w 1 := by
  have he : (fun s ↦ riemannZeta s * χ.LFunction s * ψ.LFunction s *
      (χ.mul ψ).LFunction s * w s) =ᶠ[𝓝[≠] 1] fun s ↦ (s - 1) ^ (-1 : ℤ) •
        (LFunctionTrivChar₁ 1 s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s * w s) := by
    filter_upwards [pair_simple_factorization χ ψ] with s hs
    rw [hs, smul_eq_mul, smul_eq_mul, mul_assoc]
  have hr := TauCeti.Contour.residue_eq_of_eventuallyEq_zpow_smul (by norm_num : (-1 : ℤ) ≤ -1)
    ((analyticAt_pair_simple_regularization χ ψ hχ hψ hχψ).mul hw) he
  simpa [LFunctionTrivChar₁, iteratedDeriv_zero] using hr

/-- The residue at `1` of the four-factor product, with an analytic weight, in the double-pole
case. Differentiating the regularization retains both the derivative of the weight and the
Euler factors of the principal product character. -/
theorem residue_pair_mul_of_mul_eq_one (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hχψ : χ.mul ψ = 1) {w : ℂ → ℂ} (hw : AnalyticAt ℂ w 1) :
    TauCeti.Contour.residue
      (fun s ↦ riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s * w s) 1 =
        deriv (fun s ↦ LFunctionTrivChar₁ 1 s * χ.LFunction s * ψ.LFunction s *
          LFunctionTrivChar₁ (Nat.lcm M N) s * w s) 1 := by
  have he : (fun s ↦ riemannZeta s * χ.LFunction s * ψ.LFunction s *
      (χ.mul ψ).LFunction s * w s) =ᶠ[𝓝[≠] 1] fun s ↦ (s - 1) ^ (-2 : ℤ) •
        (LFunctionTrivChar₁ 1 s * χ.LFunction s * ψ.LFunction s *
          LFunctionTrivChar₁ (Nat.lcm M N) s * w s) := by
    filter_upwards [pair_double_factorization χ ψ hχψ] with s hs
    rw [hs, smul_eq_mul, smul_eq_mul, mul_assoc]
  have hr := TauCeti.Contour.residue_eq_of_eventuallyEq_zpow_smul (by norm_num : (-2 : ℤ) ≤ -1)
    ((analyticAt_pair_double_regularization χ ψ hχ hψ).mul hw) he
  simpa [iteratedDeriv_one, Pi.mul_def] using hr

/-- The leading coefficient at the double pole includes the Euler factors at all primes
of the common level, even if those primes divide only one of the original levels. -/
theorem tendsto_sub_one_sq_mul_pair_of_mul_eq_one (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hχψ : χ.mul ψ = 1) :
    Tendsto (fun s ↦ (s - 1) ^ 2 *
      (riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s))
      (𝓝[≠] 1) (𝓝 (χ.LFunction 1 * ψ.LFunction 1 *
        ∏ p ∈ (Nat.lcm M N).primeFactors, (1 - (p : ℂ)⁻¹))) := by
  have hχt : Tendsto χ.LFunction (𝓝[≠] 1) (𝓝 (χ.LFunction 1)) :=
    (differentiable_LFunction hχ).continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hψt : Tendsto ψ.LFunction (𝓝[≠] 1) (𝓝 (ψ.LFunction 1)) :=
    (differentiable_LFunction hψ).continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ht := (((riemannZeta_residue_one.mul hχt).mul hψt).mul
    (LFunctionTrivChar_residue_one (N := Nat.lcm M N)))
  simp only [one_mul] at ht
  convert ht using 1
  funext s
  rw [hχψ]
  ring

/-- The coefficient series has the same simple-pole coefficient when approached through
real arguments greater than `1`; its junk values outside convergence are never used. -/
theorem tendsto_sub_one_mul_LSeries_zetaMulPairCoeffs (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hχψ : χ.mul ψ ≠ 1) :
    Tendsto (fun x : ℝ ↦ ((x : ℂ) - 1) * LSeries (χ.zetaMulPairCoeffs ψ) x)
      (𝓝[>] 1) (𝓝 (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1)) := by
  have hcast : Tendsto (fun x : ℝ ↦ (x : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) :=
    continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
      (fun x hx ↦ by simpa using hx.ne')
  have hχt : Tendsto χ.LFunction (𝓝[≠] 1) (𝓝 (χ.LFunction 1)) :=
    (differentiable_LFunction hχ).continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hψt : Tendsto ψ.LFunction (𝓝[≠] 1) (𝓝 (ψ.LFunction 1)) :=
    (differentiable_LFunction hψ).continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hχψt : Tendsto (χ.mul ψ).LFunction (𝓝[≠] 1) (𝓝 ((χ.mul ψ).LFunction 1)) :=
    (differentiable_LFunction hχψ).continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ht := (((riemannZeta_residue_one.mul hχt).mul hψt).mul hχψt).comp hcast
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [(LSeriesHasSum_zetaMulPairCoeffs χ ψ (by simpa using hx)).LSeries_eq,
    Function.comp_apply]
  ring

/-- For a principal product character, the coefficient series has a double pole from the
right, with the principal character's missing Euler factors in its leading coefficient. -/
theorem tendsto_sub_one_sq_mul_LSeries_zetaMulPairCoeffs (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hχψ : χ.mul ψ = 1) :
    Tendsto (fun x : ℝ ↦ ((x : ℂ) - 1) ^ 2 * LSeries (χ.zetaMulPairCoeffs ψ) x)
      (𝓝[>] 1) (𝓝 (χ.LFunction 1 * ψ.LFunction 1 *
        ∏ p ∈ (Nat.lcm M N).primeFactors, (1 - (p : ℂ)⁻¹))) := by
  have hcast : Tendsto (fun x : ℝ ↦ (x : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) :=
    continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
      (fun x hx ↦ by simpa using hx.ne')
  apply ((tendsto_sub_one_sq_mul_pair_of_mul_eq_one χ ψ hχ hψ hχψ).comp hcast).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [(LSeriesHasSum_zetaMulPairCoeffs χ ψ (by simpa using hx)).LSeries_eq,
    Function.comp_apply]

end DirichletCharacter
