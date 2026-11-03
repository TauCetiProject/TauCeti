/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.GaussSum
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Inversion
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
import TauCeti.NumberTheory.ModularForms.ThetaSeries.Functoriality
import TauCeti.NumberTheory.ModularForms.ThetaSeries.Asymptotics

/-!
# The theta series of an even lattice under `SL(2, ℤ)`: the coset splitting

Let `L` be an even full lattice of rank `n = 2k` in a real inner product space `E`, and write
`e(x) = exp (2 π i x)`. For `A = !![a, b; c, d] ∈ SL(2, ℤ)` with `c > 0` the Möbius action is
`A τ = a / c - 1 / (c (c τ + d))`. Splitting `L` into its classes `y + c L` and applying the
inversion law of theta series at the translate `y / c` and the point `σ = τ + d / c` to each class
expresses `Θ_L(A τ)` through the twisted Gauss sums `G_L(a, c; m)` of `L`:

`Θ_L(A τ) = (covol L)⁻¹ ((c τ + d) / (i c))^k ∑_{m ∈ L^∨} G_L(a, c; m) e(d ‖m‖² / (2c)) q_m(τ)`,

with `q_m(τ) = exp (π i ‖m‖² τ)`. No condition relating `c` to `L` is needed here. When the level
`N` of `L` divides `c`, the twisted Gauss sums vanish off `L` and are multiples of the untwisted one
on `L`, and the identity collapses to a transformation law of `Θ_L` itself:

`Θ_L ∣[k] A = (-i)^k c^{-k} (covol L)⁻¹ G_L(a, c) Θ_L`.

The evaluation of `G_L(a, c)` by a Jacobi symbol turns this into the transformation law of `Θ_L`
under `Γ₀(N)` with a quadratic nebentypus (Hecke, Schoeneberg).

## Main statements

* `ZLattice.IsEven.thetaSeries_smul_eq_tsum_gaussSumTwisted`: the coset splitting of `Θ_L(A τ)`.
* `ZLattice.IsEven.thetaSeries_slash_eq_gaussSum_smul`: for `N ∣ c`,
  `Θ_L ∣[k] A = (-i)^k c^{-k} (covol L)⁻¹ G_L(a, c) Θ_L`.

## References

* B. Schoeneberg, *Elliptic Modular Functions*, Springer, 1974, Chapter IX.
* T. Miyake, *Modular Forms*, Springer, 1989, §4.9.
-/

public section

open Complex Module
open UpperHalfPlane (coe_vadd)
open scoped Pointwise Real RealInnerProductSpace ModularForm UpperHalfPlane MatrixGroups

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
  {k : ℕ}

namespace IsEven

variable (hL : IsEven L)
include hL

/-- **The coset splitting of a theta series.** Let `L` be an even full lattice of rank `2k` and
`A = !![a, b; c, d] ∈ SL(2, ℤ)` with `c > 0`. Then
`Θ_L(A τ) = (covol L)⁻¹ ((c τ + d) / (i c))^k ∑_{m ∈ L^∨} G_L(a, c; m) e(d ‖m‖² / (2c)) q_m(τ)`
with `q_m(τ) = exp (π i ‖m‖² τ)`, where `G_L(a, c; m)` is the twisted Gauss sum and
`e(x) = exp (2 π i x)`. -/
theorem thetaSeries_smul_eq_tsum_gaussSumTwisted (hk : finrank ℝ E = 2 * k) (A : SL(2, ℤ))
    {c : ℕ} [NeZero c] [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (hc : A 1 0 = c) (τ : ℍ) :
    thetaSeries L (A • τ) = (covolume L : ℂ)⁻¹ * ((c * τ + A 1 1) / (I * c)) ^ k *
      ∑' m : dual L, gaussSumTwisted L hL (A 0 0) c m *
        cexp (2 * π * I * ((A 1 1 * ‖(m : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)) *
          cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ) := by
  have hc0 : c ≠ 0 := NeZero.ne c
  have hcR : (c : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hc0
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc0
  set σ : ℍ := ((A 1 1 : ℝ) / c) +ᵥ τ with hσ
  set τ' : ℍ := (⟨((c : ℝ) ^ 2)⁻¹, inv_pos.mpr (sq_pos_of_ne_zero hcR)⟩ : {r : ℝ // 0 < r}) •
    (ModularGroup.S • σ) with hτ'
  -- Since `c² • A τ = a c +ᵥ S σ`, the point `A τ` is the translate by `a / c` of `c⁻² • S σ`.
  have hAτ : A • τ = ((A 0 0 : ℝ) / c) +ᵥ τ' := by
    have hA := congrArg UpperHalfPlane.coe
      (ModularGroup.sq_smul_smul_eq_vadd_S_smul_vadd A (by rw [hc]; exact_mod_cast hc0) τ)
    simp only [hc, Int.cast_natCast, UpperHalfPlane.coe_pos_real_smul, coe_vadd,
      Complex.real_smul] at hA
    rw [UpperHalfPlane.ext_iff, coe_vadd, hτ', UpperHalfPlane.coe_pos_real_smul, Complex.real_smul]
    push_cast at hA ⊢
    field_simp
    linear_combination hA
  -- Rescaling each class `y + c L` onto `y / c + L` takes `c⁻² • S σ` back to `S σ`.
  have hclass (v : E) : thetaCoset ((c : ℝ) • L) v τ' =
      thetaCoset L ((c : ℝ)⁻¹ • v) (ModularGroup.S • σ) := by
    conv_lhs => rw [← smul_inv_smul₀ hcR v]
    rw [thetaCoset_smul L hcR]
    congr 1
    rw [UpperHalfPlane.ext_iff, UpperHalfPlane.coe_pos_real_smul, hτ',
      UpperHalfPlane.coe_pos_real_smul, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hcR), one_smul]
  -- The dual series of each class converges, its terms being bounded by those of `Θ_{L^∨}(σ)`.
  have hsum (v : E) : Summable fun m : dual L =>
      cexp (2 * π * I * ⟪v, (m : E)⟫) * cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * σ) := by
    refine (summable_thetaSeries (dual L) σ).norm.of_norm_bounded fun m => ?_
    rw [norm_mul, Complex.norm_exp]
    simp
  -- The factor `(-i)^k σ^k` of the inversion law is `((c τ + d) / (i c))^k`.
  have hfac : (-I) ^ k * (σ : ℂ) ^ k = ((c * τ + A 1 1) / (I * c)) ^ k := by
    rw [← mul_pow, hσ, coe_vadd]
    congr 1
    field_simp
    push_cast
    rw [I_sq]
    field_simp
    ring
  -- Termwise, the twisted Gauss sum collects the Gauss factors of the classes.
  have hterm (m : dual L) : gaussSumTwisted L hL (A 0 0) c m *
      cexp (2 * π * I * ((A 1 1 * ‖(m : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)) *
        cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ) =
      ∑ y : L ⧸ ((c : ℝ) • L).submoduleOf L, gaussTerm L hL (A 0 0) c 0 y *
          (cexp (2 * π * I * ⟪(c : ℝ)⁻¹ • ((Quotient.out y : L) : E), (m : E)⟫) *
            cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * σ)) := by
    rw [gaussSumTwisted_def, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    generalize hv : Quotient.out y = v
    rw [← Submodule.Quotient.mk_out y, hv, gaussTerm_mk, gaussTerm_mk, ZeroMemClass.coe_zero,
      inner_zero_right, add_zero, hσ, coe_vadd, inner_smul_left, conj_trivial]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [hAτ, thetaSeries_vadd_eq_sum hL]
  simp_rw [hclass, thetaCoset_S_smul L hk, hterm,
    Summable.tsum_finsetSum fun y _ => (hsum _).mul_left _, ← hfac, tsum_mul_left, Finset.mul_sum]
  -- `thetaSeries_vadd_eq_sum` sums over its own `Fintype` instance on `L / c L`.
  refine Finset.sum_congr (by congr; exact Subsingleton.elim _ _) fun y _ => ?_
  ring

/-- **The theta series of an even lattice under `Γ₀(N)`, with the Gauss sum unevaluated.** Let
`L` be an even full lattice of rank `2k` and level `N`, and `A = !![a, b; c, d] ∈ SL(2, ℤ)` with
`c > 0` and `N ∣ c`. Then `Θ_L ∣[k] A = (-i)^k c^{-k} (covol L)⁻¹ G_L(a, c) Θ_L`. -/
theorem thetaSeries_slash_eq_gaussSum_smul (hk : finrank ℝ E = 2 * k) (A : SL(2, ℤ)) {c : ℕ}
    [NeZero c] [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (hc : A 1 0 = c)
    (hN : level L ∣ c) :
    thetaSeries L ∣[(k : ℤ)] A =
      ((-I) ^ k * ((c : ℂ) ^ k)⁻¹ * (covolume L : ℂ)⁻¹ * gaussSum L hL (A 0 0) c) •
        thetaSeries L := by
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne c)
  have hdet : A 0 0 * A 1 1 - A 0 1 * c = 1 := by
    have h := A.det_coe
    rwa [Matrix.det_fin_two, hc] at h
  have had : A 0 0 * A 1 1 ≡ 1 [ZMOD c] :=
    Int.modEq_iff_dvd.mpr ⟨-A 0 1, by linear_combination -hdet⟩
  have hLd : L ≤ dual L := isIntegral_iff_le_dual.mp hL.isIntegral
  -- Only the classes `m ∈ L` contribute to the coset splitting, each with the factor `G_L(a, c)`.
  have htsum (τ : ℍ) : ∑' m : dual L, gaussSumTwisted L hL (A 0 0) c m *
      cexp (2 * π * I * ((A 1 1 * ‖(m : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)) *
        cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ) = gaussSum L hL (A 0 0) c * thetaSeries L τ := by
    rw [← (Submodule.inclusion_injective hLd).tsum_eq, thetaSeries_apply, ← tsum_mul_left]
    · refine tsum_congr fun ℓ => ?_
      obtain ⟨j, hj⟩ := isEven_iff.mp hL _ ℓ.2
      rw [gaussSumTwisted_eq_of_mem hL had ℓ.2]
      simp only [Submodule.coe_inclusion]
      -- The two Gauss factors combine to `e(-b d ‖ℓ‖² / 2) = 1`.
      have h1 : cexp (-(2 * π * I * ((A 0 0 * A 1 1 ^ 2 * ‖(ℓ : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ))) *
          cexp (2 * π * I * ((A 1 1 * ‖(ℓ : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)) = 1 := by
        rw [← exp_add, ← exp_int_mul_two_pi_mul_I (-(A 0 1 * A 1 1 * j)), hj]
        congr 1
        push_cast
        field_simp
        linear_combination (-(A 1 1 * j : ℂ)) * (by exact_mod_cast hdet :
          (A 0 0 : ℂ) * A 1 1 - A 0 1 * c = 1)
      linear_combination (gaussSum L hL (A 0 0) c * cexp (π * I * (‖(ℓ : E)‖ ^ 2 : ℝ) * τ)) * h1
    · intro m hm
      by_contra h
      apply Function.mem_support.mp hm
      rw [gaussSumTwisted_eq_zero hL _ hN fun hmL => h ⟨⟨m, hmL⟩, by ext; simp⟩, zero_mul,
        zero_mul]
  ext τ
  have hden : (c : ℂ) * τ + A 1 1 ≠ 0 := by
    simpa [ModularGroup.denom_apply, hc] using UpperHalfPlane.denom_ne_zero A τ
  rw [ModularForm.SL_slash_apply, thetaSeries_smul_eq_tsum_gaussSumTwisted hL hk A hc, htsum,
    ModularGroup.denom_apply, hc, Pi.smul_apply, smul_eq_mul, zpow_neg, zpow_natCast]
  push_cast
  have hI : (-I) ^ k * I ^ k = 1 := by rw [← mul_pow, neg_mul, I_mul_I, neg_neg, one_pow]
  rw [div_pow, mul_pow]
  field_simp
  linear_combination
    (-(gaussSum L hL (A 0 0) c * thetaSeries L τ / (covolume L : ℂ))) * hI

end IsEven

end ZLattice
