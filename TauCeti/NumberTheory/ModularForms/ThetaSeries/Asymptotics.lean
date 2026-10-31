/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import TauCeti.Algebra.Module.ZLattice.GaussSum
public import TauCeti.Algebra.Module.ZLattice.Scaling
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Inversion
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
import TauCeti.NumberTheory.ModularForms.ThetaSeries.Cusp

/-!
# Theta series near the cusps `0` and `a / c`

Let `L` be a full lattice in a real inner product space `E` of even dimension `n = 2k`. This file
computes the leading behaviour of the theta series of `L` and of its translates as the variable
approaches a rational point of the boundary of `ℍ`.

**The cusp `0`.** Let `ε → 0` in `ℍ` in such a way that `im (-1/ε) = im ε / |ε|² → ∞`; this is the
filter `comap (S • ·) atImInfty`, the preimage of `atImInfty` under the involution
`S : τ ↦ -1/τ`. The real part of `ε` may vary along the way. Then for every `v : E`,

`ε^k θ_{v+L}(ε) → i^k (covol L)⁻¹`.

This is the inversion law `ZLattice.thetaCoset_S_smul` read at `τ = -1/ε`: since `ε τ = -1`,
`ε^k θ_{v+L}(ε) = i^k (covol L)⁻¹ ∑_{m ∈ L^∨} e(⟪v, m⟫) exp (π i ‖m‖² τ)`, and as `im τ → ∞` every
term of the sum tends to `0`, except the term `1` of `m = 0`.

**The cusps `a / c`.** Let `L` be even, `a ∈ ℤ` and `c` a positive integer. Splitting `L` into its
classes `y + cL`, the factor `exp (π i ‖x‖² a / c)` is the same for all `x ∈ y + cL`, namely the
Gauss summand `e(a ‖y‖² / (2c))` of `ZLattice.gaussTerm`, so

`Θ_L(a/c + τ) = ∑_{y ∈ L/cL} e(a ‖y‖² / (2c)) θ_{y+cL}(τ)`.

Since `covol (cL) = c^{2k} covol L`, the asymptotic at the cusp `0` applied to each lattice coset
`y + cL` gives `ε^k Θ_L(a/c + ε) → i^k G_L(a, c) / (c^{2k} covol L)`, where `G_L(a, c)` is the
Gauss sum `ZLattice.gaussSum`. Along the imaginary axis `ε = i t` this reads

`t^k Θ_L(a/c + i t) → G_L(a, c) / (c^{2k} covol L)` as `t → 0⁺`.

Comparing this limit with the one obtained from the inversion law at `a/c + i t` is the analytic
proof of the reciprocity law for the Gauss sums of an even lattice. The statement is additive,
not multiplicative: `G_L(a, c)` may vanish while `Θ_L(a/c + i t)` does not.

## Main statements

* `ZLattice.tendsto_pow_mul_thetaCoset_comap_S`, `ZLattice.tendsto_pow_mul_thetaSeries_comap_S`:
  `ε^k θ_{v+L}(ε) → i^k (covol L)⁻¹` as `ε` tends to the cusp `0`.
* `ZLattice.IsEven.thetaSeries_vadd_eq_sum`: the splitting of `Θ_L(a/c + τ)` into theta series of
  translates of `cL`, weighted by Gauss summands.
* `ZLattice.IsEven.tendsto_pow_mul_thetaSeries_vadd_comap_S`,
  `ZLattice.IsEven.tendsto_pow_mul_thetaSeries_nhdsGT`: the asymptotic of `Θ_L` at the cusp
  `a / c`.

## References

* B. Schoeneberg, *Elliptic Modular Functions*, Springer, 1974, Chapter IX.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Springer, 1973, Appendix 4.
-/

public section

open Complex Filter Module
open UpperHalfPlane (atImInfty coe_vadd modular_S_smul ofComplex ofComplex_apply_of_im_pos)
open scoped Pointwise Real RealInnerProductSpace Topology UpperHalfPlane

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  {k : ℕ}

/-- **Theta series of a translate near the cusp `0`**: if `dim E = 2k`, then for `v : E`,
`ε^k θ_{v+L}(ε) → i^k (covol L)⁻¹` as `ε → 0` with `im (-1/ε) → ∞`. -/
theorem tendsto_pow_mul_thetaCoset_comap_S (hk : finrank ℝ E = 2 * k) (v : E) :
    Tendsto (fun ε : ℍ ↦ (ε : ℂ) ^ k * thetaCoset L v ε)
      (comap (ModularGroup.S • ·) atImInfty) (𝓝 (I ^ k * (covolume L : ℂ)⁻¹)) := by
  set F : ℍ → ℂ := fun τ ↦ ∑' m : dual L, cexp (2 * π * I * (⟪v, (m : E)⟫ : ℝ)) *
      cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ)
  -- The character `e(⟪v, m⟫)` has norm `1`, so `F τ` tends at `i∞` to its term `1` at `m = 0`.
  have hF : Tendsto F atImInfty (𝓝 1) := by
    classical
    have h := tendsto_tsum_mul_thetaTerm_atImInfty (dual L) 0
      (fun m ↦ cexp (2 * π * I * (⟪v, (m : E)⟫ : ℝ))) fun m ↦ by simp [Complex.norm_exp]
    simpa only [zero_add, ZeroMemClass.coe_eq_zero, tsum_ite_eq, ZeroMemClass.coe_zero,
      inner_zero_right, ofReal_zero, mul_zero, exp_zero] using h
  -- With `τ = -1/ε`, the inversion law gives `ε^k θ_{v+L}(ε) = i^k (covol L)⁻¹ F τ`.
  have key (ε : ℍ) : (ε : ℂ) ^ k * thetaCoset L v ε =
      I ^ k * (covolume L : ℂ)⁻¹ * F (ModularGroup.S • ε) := by
    have hθ := thetaCoset_S_smul L hk v (ModularGroup.S • ε)
    rw [ModularGroup.S_smul_S_smul] at hθ
    have hετ : (ε : ℂ) * ((ModularGroup.S • ε : ℍ) : ℂ) = -1 := by
      simp only [modular_S_smul, UpperHalfPlane.coe_mk]
      rw [inv_neg, mul_neg, mul_inv_cancel₀ ε.ne_zero]
    rw [hθ]
    calc _ = (covolume L : ℂ)⁻¹ * ((-I) ^ k * ((ε : ℂ) * ((ModularGroup.S • ε : ℍ) : ℂ)) ^ k) *
            F (ModularGroup.S • ε) := by rw [mul_pow]; ring
      _ = _ := by rw [hετ, ← mul_pow, neg_mul_neg, mul_one]; ring
  have h := (hF.comp (tendsto_comap (f := (ModularGroup.S • · : ℍ → ℍ)))).const_mul
    (I ^ k * (covolume L : ℂ)⁻¹)
  rw [mul_one] at h
  exact h.congr fun ε ↦ (key ε).symm

/-- **Theta series near the cusp `0`**: if `dim E = 2k`, then `ε^k Θ_L(ε) → i^k (covol L)⁻¹` as
`ε → 0` with `im (-1/ε) → ∞`. -/
theorem tendsto_pow_mul_thetaSeries_comap_S (hk : finrank ℝ E = 2 * k) :
    Tendsto (fun ε : ℍ ↦ (ε : ℂ) ^ k * thetaSeries L ε)
      (comap (ModularGroup.S • ·) atImInfty) (𝓝 (I ^ k * (covolume L : ℂ)⁻¹)) := by
  simpa using tendsto_pow_mul_thetaCoset_comap_S L hk 0

namespace IsEven

variable {L}

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Splitting a theta series at the cusp `a / c`.** For an even lattice `L`, `a ∈ ℤ` and a
positive integer `c`, `Θ_L(a/c + τ) = ∑_{y ∈ L/cL} e(a ‖y‖² / (2c)) θ_{y+cL}(τ)`: on each class
`y + cL` the factor `exp (π i ‖x‖² a / c)` is the Gauss summand of `y`. -/
theorem thetaSeries_vadd_eq_sum (hL : IsEven L) (a : ℤ) (c : ℕ) [NeZero c] (τ : ℍ) :
    thetaSeries L (((a : ℝ) / c) +ᵥ τ) = ∑ y : L ⧸ ((c : ℝ) • L).submoduleOf L,
      gaussTerm L hL a c 0 y * thetaCoset ((c : ℝ) • L) ((Quotient.out y : L) : E) τ := by
  have hle : (c : ℝ) • L ≤ L := fun x hx ↦ by
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp hx
    rw [Nat.cast_smul_eq_nsmul]
    exact L.nsmul_mem hu c
  rw [← (hasSum_thetaCoset_out L hle _).tsum_eq, tsum_fintype]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  have hc : (c : ℝ) ≠ 0 := NeZero.ne _
  rw [thetaCoset_vadd_eq_mul _ _ (fun w hw ↦ ?_)]
  · congr 1
    conv_rhs => rw [← Submodule.Quotient.mk_out y]
    rw [gaussTerm_mk, ZeroMemClass.coe_zero, inner_zero_right, add_zero]
    congr 1
    push_cast
    field_simp
  · -- For `w = c u`, `(‖γ + w‖² - ‖γ‖²) a / c = 2 a ⟪γ, u⟫ + a c ‖u‖²`, an even integer.
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp hw
    obtain ⟨i, hi⟩ := isIntegral_iff.mp hL.isIntegral _ (Quotient.out y).2 _ hu
    obtain ⟨j, hj⟩ := isEven_iff.mp hL _ hu
    refine ⟨a * i + a * c * j, ?_⟩
    rw [norm_add_sq_real, norm_smul, inner_smul_right, hi, mul_pow, hj, Real.norm_natCast]
    push_cast
    field_simp
    ring

variable (hL : IsEven L)
include hL

/-- **Theta series of an even lattice near the cusp `a / c`**: if `dim E = 2k`, then for `a ∈ ℤ`
and a positive integer `c`, `ε^k Θ_L(a/c + ε) → i^k G_L(a, c) / (c^{2k} covol L)` as `ε → 0` with
`im (-1/ε) → ∞`, where `G_L(a, c)` is the Gauss sum of `L`. -/
theorem tendsto_pow_mul_thetaSeries_vadd_comap_S (hk : finrank ℝ E = 2 * k) (a : ℤ) (c : ℕ)
    [NeZero c] :
    Tendsto (fun ε : ℍ ↦ (ε : ℂ) ^ k * thetaSeries L (((a : ℝ) / c) +ᵥ ε))
      (comap (ModularGroup.S • ·) atImInfty)
      (𝓝 (I ^ k * gaussSum L hL a c / ((c : ℂ) ^ (2 * k) * covolume L))) := by
  have hcov : covolume ((c : ℝ) • L) = (c : ℝ) ^ (2 * k) * covolume L := by
    have h := covolume_smul L (NeZero.ne (c : ℝ))
    rw [Nat.abs_cast, hk] at h
    exact h
  have h := tendsto_finsetSum (Finset.univ (α := L ⧸ ((c : ℝ) • L).submoduleOf L)) fun y _ ↦
    (tendsto_pow_mul_thetaCoset_comap_S ((c : ℝ) • L) hk ((Quotient.out y : L) : E)).const_mul
      (gaussTerm L hL a c 0 y)
  simp_rw [thetaSeries_vadd_eq_sum hL a c, Finset.mul_sum]
  convert h using 2 with ε
  · exact Finset.sum_congr rfl fun y _ ↦ by ring
  · rw [gaussSum_def, ← Finset.sum_mul, hcov]
    push_cast
    field_simp

/-- **Theta series of an even lattice on a vertical line**: if `dim E = 2k`, then for `a ∈ ℤ` and a
positive integer `c`, `t^k Θ_L(a/c + i t) → G_L(a, c) / (c^{2k} covol L)` as `t → 0⁺`, where
`G_L(a, c)` is the Gauss sum of `L`. -/
theorem tendsto_pow_mul_thetaSeries_nhdsGT (hk : finrank ℝ E = 2 * k) (a : ℤ) (c : ℕ)
    [NeZero c] :
    Tendsto (fun t : ℝ ↦ (t : ℂ) ^ k * thetaSeries L (ofComplex (a / c + I * t)))
      (𝓝[>] 0) (𝓝 (gaussSum L hL a c / ((c : ℂ) ^ (2 * k) * covolume L))) := by
  -- The path `t ↦ i t` tends to the cusp `0`: `im (-1/(i t)) = 1/t`.
  have hpath : Tendsto (fun t : ℝ ↦ ofComplex (I * t)) (𝓝[>] 0)
      (comap (ModularGroup.S • ·) atImInfty) := by
    rw [tendsto_comap_iff, UpperHalfPlane.atImInfty, tendsto_comap_iff]
    refine tendsto_inv_nhdsGT_zero.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [Function.comp_apply, Function.comp_apply, modular_S_smul, UpperHalfPlane.mk_im,
      ofComplex_apply_of_im_pos (by simpa using ht)]
    simp [Complex.inv_im, Complex.normSq_apply]
  have h := ((tendsto_pow_mul_thetaSeries_vadd_comap_S hL hk a c).comp hpath).const_mul
    (I ^ k)⁻¹
  have hlim : gaussSum L hL a c / ((c : ℂ) ^ (2 * k) * covolume L) =
      (I ^ k)⁻¹ * (I ^ k * gaussSum L hL a c / ((c : ℂ) ^ (2 * k) * covolume L)) := by
    field_simp [pow_ne_zero k I_ne_zero]
  rw [hlim]
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have him : 0 < (I * t).im := by simpa using ht
  have hvadd : ofComplex (a / c + I * t) = ((a : ℝ) / c) +ᵥ ofComplex (I * t) := by
    have him' : 0 < (a / c + I * t : ℂ).im := by simpa using ht
    ext
    rw [coe_vadd, ofComplex_apply_of_im_pos him', ofComplex_apply_of_im_pos him]
    push_cast
    rfl
  rw [Function.comp_apply, hvadd, ofComplex_apply_of_im_pos him, mul_pow]
  field_simp [pow_ne_zero k I_ne_zero]

end IsEven

end ZLattice
