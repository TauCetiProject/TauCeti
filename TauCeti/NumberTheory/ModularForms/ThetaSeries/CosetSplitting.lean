/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Asymptotics
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
import TauCeti.NumberTheory.ModularForms.ThetaSeries.Functoriality

/-!
# The theta series of an even lattice under `SL(2, ℤ)`

Let `L` be an even full lattice in a real inner product space `E` of even dimension `n = 2k`, and
let `A = !![a, b; c, d] ∈ SL(2, ℤ)` with `c > 0`. Write `e(x) = exp (2 π i x)`. This file proves
Schoeneberg's coset splitting of the theta series of `L` at `A τ`:

`Θ_L(A τ) = (covol L)⁻¹ ((c τ + d) / (i c))^k ∑_{m ∈ L^∨} G_L(a, c; m) e_{c,d}(m) q_m(τ)`,

where `G_L(a, c; m)` is the twisted Gauss sum `ZLattice.gaussSumTwisted`,
`e_{c,d}(m) = e(d ‖m‖² / (2c))` and `q_m(τ) = exp (π i ‖m‖² τ)`; in weight `k` this reads

`(Θ_L ∣[k] A)(τ) = (covol L)⁻¹ (-i / c)^k ∑_{m ∈ L^∨} G_L(a, c; m) e_{c,d}(m) q_m(τ)`.

No condition relating `c` to the level of `L` is needed. When the level divides `c`, the twisted
Gauss sums vanish off `L` (`ZLattice.gaussSumTwisted_eq_zero`) and reduce on `L` to the untwisted
Gauss sum times the phase `e(-a d² ‖m‖² / (2c))` (`ZLattice.gaussSumTwisted_eq_of_mem`), which
cancels `e_{c,d}(m)` because `a d ≡ 1 mod c`. The right-hand side then becomes a multiple of
`Θ_L`; this is the input to the transformation law of `Θ_L` under `Γ₀(N)`.

The proof follows Schoeneberg. Since `ad - bc = 1`, `A τ = a / c - 1 / (c (c τ + d))`
(`ModularGroup.smul_eq_vadd_smul_S_smul_vadd`). Splitting
`L` into its classes `y + cL` (`ZLattice.IsEven.thetaSeries_vadd_eq_sum`) gives
`Θ_L(A τ) = ∑_{y ∈ L/cL} e(a ‖y‖² / (2c)) θ_{y+cL}(-1 / (c (c τ + d)))`. Rescaling by `c`,
`θ_{y+cL}(-1 / (c (c τ + d))) = θ_{y/c+L}(-1/σ)` with `σ = τ + d/c`, and the inversion law at a
general translate (`ZLattice.thetaCoset_S_smul`) expands this as a sum over `L^∨` with phases
`e(⟪y, m⟫ / c)`. Exchanging the finite sum over `L/cL` with the sum over `L^∨` collects these
phases into the twisted Gauss sums, and `exp (π i ‖m‖² σ) = e(d ‖m‖² / (2c)) exp (π i ‖m‖² τ)`.

## Main statements

* `ZLattice.IsEven.summable_norm_gaussSumTwisted_mul_thetaTerm`: the sum over `L^∨` converges
  absolutely.
* `ZLattice.IsEven.thetaSeries_SL_smul`: the coset splitting of `Θ_L(A τ)`.
* `ZLattice.IsEven.thetaSeries_SL_slash_apply`: the same identity in slash form.

## References

* B. Schoeneberg, *Elliptic Modular Functions*, Springer, 1974, Chapter IX.
-/

public section

open Complex Module
open UpperHalfPlane (coe_vadd)
open scoped MatrixGroups Pointwise Real RealInnerProductSpace ModularForm UpperHalfPlane

namespace ZLattice

namespace IsEven

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {L : Submodule ℤ E}

/-- Rescaling by `c` turns the inversion law of `L` at the translate `y / c` into the inversion
law of `cL` at the translate `y`: at `w = c⁻² (-1/σ)`,
`θ_{y+cL}(w) = (covol L)⁻¹ (-i)^k σ^k ∑_{m ∈ L^∨} e(⟪y, m⟫ / c) exp (π i ‖m‖² σ)`. -/
private theorem thetaCoset_smul_eq_tsum [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [DiscreteTopology L] [IsZLattice ℝ L] {k : ℕ} (hk : finrank ℝ E = 2 * k)
    {c : ℝ} (hc : c ≠ 0) (y : E) (σ : ℍ) :
    thetaCoset (c • L) y
        ((⟨(c ^ 2)⁻¹, inv_pos.2 (sq_pos_of_ne_zero hc)⟩ : {r : ℝ // 0 < r}) •
          (ModularGroup.S • σ)) =
      (covolume L : ℂ)⁻¹ * ((-I) ^ k * (σ : ℂ) ^ k) *
        ∑' m : dual L, cexp (2 * π * I * ⟪c⁻¹ • y, (m : E)⟫) *
          cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * σ) := by
  have h : (⟨c ^ 2, sq_pos_of_ne_zero hc⟩ : {r : ℝ // 0 < r}) *
      ⟨(c ^ 2)⁻¹, inv_pos.2 (sq_pos_of_ne_zero hc)⟩ = 1 :=
    Subtype.ext (mul_inv_cancel₀ (pow_ne_zero 2 hc))
  rw [← smul_inv_smul₀ hc y, thetaCoset_smul L hc, ← mul_smul, h, one_smul,
    thetaCoset_S_smul L hk, inv_smul_smul₀ hc]

variable (hL : IsEven L)
include hL

variable [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L]

/-- The sum `∑_{m ∈ L^∨} G_L(a, c; m) e(d ‖m‖² / (2c)) exp (π i ‖m‖² τ)` of the coset splitting
converges absolutely: the twisted Gauss sums are bounded and the phases have absolute value `1`. -/
theorem summable_norm_gaussSumTwisted_mul_thetaTerm (a d : ℤ) (c : ℕ) [NeZero c] (τ : ℍ) :
    Summable fun m : dual L ↦ ‖gaussSumTwisted L hL a c m *
      cexp (2 * π * I * ((d * ‖(m : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)) *
        cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ)‖ := by
  refine .of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun m ↦ ?_)
    (((summable_thetaSeries (dual L) τ).norm).mul_left
      (Fintype.card (L ⧸ ((c : ℝ) • L).submoduleOf L) : ℝ))
  rw [norm_mul, norm_mul, norm_exp_two_pi_mul_I_mul_ofReal, mul_one]
  gcongr
  exact norm_gaussSumTwisted_le hL a c m

variable [MeasurableSpace E] [BorelSpace E] {k : ℕ}

/-- **The coset splitting of a theta series.** Let `L` be an even lattice with `dim E = 2k`, and
`A = !![a, b; c, d] ∈ SL(2, ℤ)` with `c > 0`. Then
`Θ_L(A τ) = (covol L)⁻¹ ((c τ + d) / (i c))^k ∑_{m ∈ L^∨} G_L(a, c; m) e_{c,d}(m) q_m(τ)`,
where `G_L(a, c; m)` is the twisted Gauss sum, `e_{c,d}(m) = e(d ‖m‖² / (2c))` and
`q_m(τ) = exp (π i ‖m‖² τ)`. -/
theorem thetaSeries_SL_smul (hk : finrank ℝ E = 2 * k) (A : SL(2, ℤ)) {c : ℕ} [NeZero c]
    (hc : A 1 0 = c) (τ : ℍ) :
    thetaSeries L (A • τ) =
      (covolume L : ℂ)⁻¹ * ((c * (τ : ℂ) + A 1 1) / (I * c)) ^ k *
        ∑' m : dual L, gaussSumTwisted L hL (A 0 0) c m *
          cexp (2 * π * I * ((A 1 1 * ‖(m : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)) *
            cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ) := by
  have hc₀ : (c : ℝ) ≠ 0 := NeZero.ne _
  have hcC : (c : ℂ) ≠ 0 := NeZero.ne _
  -- `A τ = a/c + w` with `w = c⁻² (-1/σ)` for `σ = τ + d/c`.
  have hA := ModularGroup.smul_eq_vadd_smul_S_smul_vadd A (by rw [hc]; exact_mod_cast hc₀) τ
  simp only [hc, Int.cast_natCast] at hA
  set σ : ℍ := ((A 1 1 : ℝ) / c) +ᵥ τ
  -- The terms of the inner sums over `L^∨`, one for each class `y ∈ L / cL`.
  let F : (L ⧸ ((c : ℝ) • L).submoduleOf L) → dual L → ℂ := fun y m ↦
    gaussTerm L hL (A 0 0) c 0 y *
      (cexp (2 * π * I * ⟪(c : ℝ)⁻¹ • ((Quotient.out y : L) : E), (m : E)⟫) *
        cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * σ))
  have hF (y) : Summable (F y) := by
    refine .mul_left _ (.of_norm_bounded (summable_thetaSeries (dual L) σ).norm fun m ↦ ?_)
    rw [norm_mul, norm_exp_two_pi_mul_I_mul_ofReal, one_mul]
  -- `exp (π i ‖m‖² σ) = e(d ‖m‖² / (2c)) exp (π i ‖m‖² τ)`.
  have hσm (m : dual L) : cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * σ) =
      cexp (2 * π * I * ((A 1 1 * ‖(m : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)) *
        cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ) := by
    rw [← exp_add, coe_vadd]
    congr 1
    push_cast
    field_simp
  -- The twisted Gauss summand of the class `y`, read off at its representative.
  have hterm (m : dual L) (y : L ⧸ ((c : ℝ) • L).submoduleOf L) : gaussTerm L hL (A 0 0) c 0 y *
      cexp (2 * π * I * ⟪(c : ℝ)⁻¹ • ((Quotient.out y : L) : E), (m : E)⟫) =
        gaussTerm L hL (A 0 0) c m y := by
    conv_rhs => rw [← Submodule.Quotient.mk_out y]
    rw [gaussTerm_mk_eq_gaussTerm_zero_mul, Submodule.Quotient.mk_out]
  have hfac : (-I) ^ k * (σ : ℂ) ^ k = ((c * (τ : ℂ) + A 1 1) / (I * c)) ^ k := by
    rw [← mul_pow, coe_vadd]
    congr 1
    rw [eq_div_iff (mul_ne_zero I_ne_zero hcC)]
    push_cast
    calc -I * ((A 1 1 : ℂ) / c + τ) * (I * c) = -I ^ 2 * ((A 1 1 : ℂ) / c * c + c * τ) := by ring
      _ = c * τ + A 1 1 := by rw [I_sq, div_mul_cancel₀ _ hcC]; ring
  calc thetaSeries L (A • τ)
      = ∑ y, gaussTerm L hL (A 0 0) c 0 y *
          thetaCoset ((c : ℝ) • L) ((Quotient.out y : L) : E)
            ((⟨((c : ℝ) ^ 2)⁻¹, inv_pos.2 (sq_pos_of_ne_zero hc₀)⟩ : {r : ℝ // 0 < r}) •
              (ModularGroup.S • σ)) := by
        rw [hA, thetaSeries_vadd_eq_sum hL]
    _ = (covolume L : ℂ)⁻¹ * ((-I) ^ k * (σ : ℂ) ^ k) * ∑ y, ∑' m, F y m := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ ↦ ?_
        rw [thetaCoset_smul_eq_tsum hk hc₀, tsum_mul_left]
        ring
    _ = _ := by
        rw [hfac, ← Summable.tsum_finsetSum fun y _ ↦ hF y]
        congr 1
        refine tsum_congr fun m ↦ ?_
        simp only [F, ← mul_assoc, hterm, ← Finset.sum_mul, hσm]
        rw [gaussSumTwisted_def]

/-- **The coset splitting in slash form.** Let `L` be an even lattice with `dim E = 2k`, and
`A = !![a, b; c, d] ∈ SL(2, ℤ)` with `c > 0`. Then in weight `k`,
`(Θ_L ∣[k] A)(τ) = (covol L)⁻¹ (-i / c)^k ∑_{m ∈ L^∨} G_L(a, c; m) e_{c,d}(m) q_m(τ)`,
where `G_L(a, c; m)` is the twisted Gauss sum, `e_{c,d}(m) = e(d ‖m‖² / (2c))` and
`q_m(τ) = exp (π i ‖m‖² τ)`. -/
theorem thetaSeries_SL_slash_apply (hk : finrank ℝ E = 2 * k) (A : SL(2, ℤ)) {c : ℕ} [NeZero c]
    (hc : A 1 0 = c) (τ : ℍ) :
    (thetaSeries L ∣[(k : ℤ)] A) τ =
      (covolume L : ℂ)⁻¹ * (-I / c) ^ k *
        ∑' m : dual L, gaussSumTwisted L hL (A 0 0) c m *
          cexp (2 * π * I * ((A 1 1 * ‖(m : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)) *
            cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ) := by
  have hden : UpperHalfPlane.denom A τ = c * (τ : ℂ) + A 1 1 := by
    rw [ModularGroup.denom_apply, hc]
    push_cast
    ring
  have hden₀ : (c : ℂ) * τ + A 1 1 ≠ 0 := hden ▸ UpperHalfPlane.denom_ne_zero _ τ
  have hcC : (c : ℂ) ≠ 0 := NeZero.ne _
  rw [ModularForm.SL_slash_apply, thetaSeries_SL_smul hL hk A hc, hden, zpow_neg, zpow_natCast]
  have h : ((c * (τ : ℂ) + A 1 1) / (I * c)) ^ k * ((c * (τ : ℂ) + A 1 1) ^ k)⁻¹ =
      (-I / c) ^ k := by
    rw [← inv_pow, ← mul_pow]
    congr 1
    rw [div_mul_eq_mul_div, mul_inv_cancel₀ hden₀, div_eq_div_iff (mul_ne_zero I_ne_zero hcC) hcC]
    linear_combination (c : ℂ) * I_sq
  rw [← h]
  ring

end IsEven

end ZLattice
