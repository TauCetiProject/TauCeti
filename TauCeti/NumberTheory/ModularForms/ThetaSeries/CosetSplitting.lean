/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.GaussSum
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Inversion
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
import TauCeti.NumberTheory.ModularForms.ThetaSeries.Functoriality
import TauCeti.NumberTheory.ModularForms.ThetaSeries.Asymptotics

/-!
# Theta series of an even lattice under `SL(2, ℤ)`: the coset splitting

Let `L` be an even full lattice of rank `n = 2k` in a real inner product space `E`, and write
`e(x) = exp (2 π i x)` and `q_m(τ) = exp (π i ‖m‖² τ)`. For `A = !![a, b; c, d] ∈ SL(2, ℤ)` with
`c > 0` the Möbius action is `A τ = a / c - 1 / (c (c τ + d))`. Splitting `L` into its classes
`y + c L` and applying the inversion law of theta series at the translate `y / c` and the point
`σ = τ + d / c` to each class expresses `Θ_L(A τ)` through the twisted Gauss sums `G_L(a, c; m)`
of `L`:

`Θ_L(A τ) = (covol L)⁻¹ ((c τ + d) / (i c))^k ∑_{m ∈ L^∨} G_L(a, c; m) e(d ‖m‖² / (2c)) q_m(τ)`.

The same splitting applies to the theta series `θ_{γ+L}` of a coset of `L` in its dual, `γ ∈ L^∨`,
with the classes `γ + y + c L`. Expanding `‖γ + y‖²`, the Gauss sum over the coset `γ + L` is
`e((a ‖γ‖² / 2 + ⟪γ, m⟫) / c) G_L(a, c; a γ + m)`, so

`θ_{γ+L}(A τ) = (covol L)⁻¹ ((c τ + d) / (i c))^k ∑_{m ∈ L^∨} e((a ‖γ‖² / 2 + ⟪γ, m⟫) / c)
G_L(a, c; a γ + m) e(d ‖m‖² / (2c)) q_m(τ)`.

No condition relating `c` to `L` is needed here. When the level `N` of `L` divides `c`, the twisted
Gauss sums vanish off `L` and are multiples of the untwisted one on `L`. Only the classes
`m ∈ -a γ + L` survive, and the identity collapses to

`θ_{γ+L} ∣[k] A = (-i)^k c^{-k} (covol L)⁻¹ G_L(a, c) e(a b ‖γ‖² / 2) θ_{aγ+L}`,

which for `γ = 0` is the transformation law `Θ_L ∣[k] A = (-i)^k c^{-k} (covol L)⁻¹ G_L(a, c) Θ_L`
of `Θ_L` itself. The evaluation of `G_L(a, c)` by a Jacobi symbol turns the latter into the
transformation law of `Θ_L` under `Γ₀(N)` with a quadratic nebentypus (Hecke, Schoeneberg). For
`A ∈ Γ(N)`, where `a ≡ 1` and `b ≡ 0` modulo `N`, the coset `a γ + L` is `γ + L` and the phase is
`1`, so every coset theta series is an eigenfunction of the slash action of `A`, with the same
eigenvalue `(-i)^k c^{-k} (covol L)⁻¹ G_L(a, c)` for every `γ`.

## Main statements

* `ZLattice.IsEven.summable_norm_gaussSumTwisted_mul_thetaTerm`: the sum over `L^∨` converges
  absolutely.
* `ZLattice.IsEven.thetaCoset_smul_eq_tsum_gaussSumTwisted`,
  `ZLattice.IsEven.thetaSeries_smul_eq_tsum_gaussSumTwisted`: the coset splitting of
  `θ_{γ+L}(A τ)` and of `Θ_L(A τ)`.
* `ZLattice.IsEven.thetaSeries_slash_apply_eq_tsum_gaussSumTwisted`: the same identity in slash
  form, `(Θ_L ∣[k] A)(τ) = (covol L)⁻¹ (-i / c)^k ∑_{m ∈ L^∨} G_L(a, c; m) e(d ‖m‖² / (2c)) q_m(τ)`.
* `ZLattice.IsEven.thetaCoset_slash_eq_gaussSum_smul`: for `N ∣ c`,
  `θ_{γ+L} ∣[k] A = (-i)^k c^{-k} (covol L)⁻¹ G_L(a, c) e(a b ‖γ‖² / 2) θ_{aγ+L}`.
* `ZLattice.IsEven.thetaSeries_slash_eq_gaussSum_smul`: for `N ∣ c`,
  `Θ_L ∣[k] A = (-i)^k c^{-k} (covol L)⁻¹ G_L(a, c) Θ_L`.
* `ZLattice.IsEven.thetaCoset_slash_eq_gaussSum_smul_of_mem_Gamma`: for `A ∈ Γ(N)` with `c > 0`,
  `θ_{γ+L} ∣[k] A = (-i)^k c^{-k} (covol L)⁻¹ G_L(a, c) θ_{γ+L}`.

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

omit [MeasurableSpace E] [BorelSpace E] in
/-- The sum `∑_{m ∈ L^∨} G_L(a, c; m) e(d ‖m‖² / (2c)) exp (π i ‖m‖² τ)` of the coset splitting
converges absolutely: the twisted Gauss sums are bounded and the phases have absolute value `1`. -/
theorem summable_norm_gaussSumTwisted_mul_thetaTerm (a d : ℤ) (c : ℕ)
    [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (τ : ℍ) :
    Summable fun m : dual L ↦ ‖gaussSumTwisted L hL a c m *
      cexp (2 * π * I * ((d * ‖(m : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)) *
        cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ)‖ := by
  refine .of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun m ↦ ?_)
    (((summable_thetaSeries (dual L) τ).norm).mul_left
      (Fintype.card (L ⧸ ((c : ℝ) • L).submoduleOf L) : ℝ))
  rw [norm_mul, norm_mul, norm_exp_two_pi_mul_I_mul_ofReal, mul_one]
  gcongr
  exact norm_gaussSumTwisted_le hL a c m

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [DiscreteTopology L]
  [IsZLattice ℝ L] in
/-- Termwise in the coset splitting of `θ_{γ+L}(A τ)`, the twisted Gauss sum at `a γ + m` collects
the Gauss factors of the classes `y ∈ L / c L`, with `σ = τ + d / c`. -/
private theorem term_eq_sum_gaussTerm (A : SL(2, ℤ)) {c : ℕ} [NeZero c]
    [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (γ : dual L) (τ σ : ℍ)
    (hσ : σ = ((A 1 1 : ℝ) / c) +ᵥ τ) (m : dual L) :
    cexp (2 * π * I * (((A 0 0 * ‖(γ : E)‖ ^ 2 / 2 + ⟪(γ : E), (m : E)⟫) / c : ℝ) : ℂ)) *
        gaussSumTwisted L hL (A 0 0) c (A 0 0 • γ + m) *
        cexp (2 * π * I * ((A 1 1 * ‖(m : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)) *
          cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ) =
      ∑ y : L ⧸ ((c : ℝ) • L).submoduleOf L,
        cexp (2 * π * I * ((A 0 0 * ‖(γ : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)) *
          gaussTerm L hL (A 0 0) c (A 0 0 • γ) y *
          (cexp (2 * π * I * ⟪(c : ℝ)⁻¹ • ((γ : E) + (Quotient.out y : L)), (m : E)⟫) *
            cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * σ)) := by
  rw [gaussSumTwisted_def, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  generalize hv : Quotient.out y = v
  rw [← Submodule.Quotient.mk_out y, hv, gaussTerm_mk, gaussTerm_mk, Submodule.coe_add,
    inner_add_right, hσ, coe_vadd, inner_smul_left, inner_add_left, conj_trivial]
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/-- **The coset splitting of a coset theta series.** Let `L` be an even full lattice of rank `2k`,
`γ ∈ L^∨` and `A = !![a, b; c, d] ∈ SL(2, ℤ)` with `c > 0`. Then
`θ_{γ+L}(A τ) = (covol L)⁻¹ ((c τ + d) / (i c))^k ∑_{m ∈ L^∨} e((a ‖γ‖² / 2 + ⟪γ, m⟫) / c)
G_L(a, c; a γ + m) e(d ‖m‖² / (2c)) q_m(τ)` with `q_m(τ) = exp (π i ‖m‖² τ)`, where
`G_L(a, c; m)` is the twisted Gauss sum and `e(x) = exp (2 π i x)`. The factor
`e((a ‖γ‖² / 2 + ⟪γ, m⟫) / c) G_L(a, c; a γ + m)` is the Gauss sum
`∑_{x ∈ (γ + L) / cL} e(a ‖x‖² / (2c) + ⟪x, m⟫ / c)` over the coset `γ + L`. -/
theorem thetaCoset_smul_eq_tsum_gaussSumTwisted (hk : finrank ℝ E = 2 * k) (A : SL(2, ℤ))
    {c : ℕ} [NeZero c] [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (hc : A 1 0 = c)
    (γ : dual L) (τ : ℍ) :
    thetaCoset L γ (A • τ) = (covolume L : ℂ)⁻¹ * ((c * τ + A 1 1) / (I * c)) ^ k *
      ∑' m : dual L,
        cexp (2 * π * I * (((A 0 0 * ‖(γ : E)‖ ^ 2 / 2 + ⟪(γ : E), (m : E)⟫) / c : ℝ) : ℂ)) *
          gaussSumTwisted L hL (A 0 0) c (A 0 0 • γ + m) *
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
  -- Rescaling each class `x + c L` onto `x / c + L` takes `c⁻² • S σ` back to `S σ`.
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
  -- Termwise, the twisted Gauss sum at `a γ + m` collects the Gauss factors of the classes.
  have hterm := term_eq_sum_gaussTerm hL A γ τ σ hσ
  rw [hAτ, thetaCoset_vadd_eq_sum hL]
  simp_rw [hclass, thetaCoset_S_smul L hk, hterm,
    Summable.tsum_finsetSum fun y _ => (hsum _).mul_left _, ← hfac, tsum_mul_left, Finset.mul_sum]
  -- `thetaCoset_vadd_eq_sum` sums over its own `Fintype` instance on `L / c L`.
  refine Finset.sum_congr (by congr; exact Subsingleton.elim _ _) fun y _ => ?_
  ring

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
  simpa using thetaCoset_smul_eq_tsum_gaussSumTwisted hL hk A hc 0 τ

/-- **The coset splitting in slash form.** Let `L` be an even full lattice of rank `2k` and
`A = !![a, b; c, d] ∈ SL(2, ℤ)` with `c > 0`. Then in weight `k`,
`(Θ_L ∣[k] A)(τ) = (covol L)⁻¹ (-i / c)^k ∑_{m ∈ L^∨} G_L(a, c; m) e(d ‖m‖² / (2c)) q_m(τ)`
with `q_m(τ) = exp (π i ‖m‖² τ)`, where `G_L(a, c; m)` is the twisted Gauss sum and
`e(x) = exp (2 π i x)`. -/
theorem thetaSeries_slash_apply_eq_tsum_gaussSumTwisted (hk : finrank ℝ E = 2 * k)
    (A : SL(2, ℤ)) {c : ℕ} [NeZero c] [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)]
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
  rw [ModularForm.SL_slash_apply, thetaSeries_smul_eq_tsum_gaussSumTwisted hL hk A hc, hden,
    zpow_neg, zpow_natCast]
  have h : ((c * (τ : ℂ) + A 1 1) / (I * c)) ^ k * ((c * (τ : ℂ) + A 1 1) ^ k)⁻¹ =
      (-I / c) ^ k := by
    rw [← inv_pow, ← mul_pow]
    congr 1
    rw [div_mul_eq_mul_div, mul_inv_cancel₀ hden₀, div_eq_div_iff (mul_ne_zero I_ne_zero hcC) hcC]
    linear_combination (c : ℂ) * I_sq
  rw [← h]
  ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- When the level of `L` divides `c`, the dual sum in the coset splitting of `θ_{γ+L}(A τ)`
collapses: only the classes `m ∈ -a γ + L` contribute, each with the factor
`G_L(a, c) e(a b ‖γ‖² / 2)`, and they sum to that factor times `θ_{aγ+L}(τ)`. -/
private theorem tsum_gaussSumTwisted_coset_eq (A : SL(2, ℤ)) {c : ℕ} [NeZero c]
    [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (hc : A 1 0 = c) (hN : level L ∣ c)
    (γ : dual L) (τ : ℍ) :
    ∑' m : dual L,
      cexp (2 * π * I * (((A 0 0 * ‖(γ : E)‖ ^ 2 / 2 + ⟪(γ : E), (m : E)⟫) / c : ℝ) : ℂ)) *
          gaussSumTwisted L hL (A 0 0) c (A 0 0 • γ + m) *
          cexp (2 * π * I * ((A 1 1 * ‖(m : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)) *
            cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ) =
      gaussSum L hL (A 0 0) c * cexp (2 * π * I * ((A 0 0 * A 0 1 * ‖(γ : E)‖ ^ 2 / 2 : ℝ) : ℂ)) *
        thetaCoset L (A 0 0 • (γ : E)) τ := by
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne c)
  have hdet : A 0 0 * A 1 1 - A 0 1 * c = 1 := by
    have h := A.det_coe
    rwa [Matrix.det_fin_two, hc] at h
  have had : A 0 0 * A 1 1 ≡ 1 [ZMOD c] :=
    Int.modEq_iff_dvd.mpr ⟨-A 0 1, by linear_combination -hdet⟩
  have hLd : L ≤ dual L := isIntegral_iff_le_dual.mp hL.isIntegral
  -- The classes `m ∈ -a γ + L` are the image of `ℓ ↦ ℓ - a γ`.
  let f : L → dual L := fun ℓ => Submodule.inclusion hLd ℓ - A 0 0 • γ
  have hf : Function.Injective f := fun ℓ₁ ℓ₂ h =>
    Submodule.inclusion_injective hLd (sub_left_injective h)
  rw [← hf.tsum_eq, ← thetaCoset_neg, thetaCoset_apply, ← tsum_mul_left]
  · refine tsum_congr fun ℓ => ?_
    have hfℓ : A 0 0 • γ + f ℓ = Submodule.inclusion hLd ℓ := add_sub_cancel _ _
    have hfℓE : ((f ℓ : dual L) : E) = -(A 0 0 • (γ : E)) + ℓ := by
      simp [f, neg_add_eq_sub]
    obtain ⟨i, hi⟩ := mem_dual.mp γ.2 _ ℓ.2
    obtain ⟨j, hj⟩ := isEven_iff.mp hL _ ℓ.2
    rw [hfℓ, gaussSumTwisted_eq_of_mem hL had ℓ.2, hfℓE]
    simp only [Submodule.coe_inclusion]
    -- The three Gauss factors combine to `e(a b ‖γ‖² / 2 - b ⟪γ, ℓ⟫ - b d ‖ℓ‖² / 2)`.
    have h1 : cexp (2 * π * I * ((((A 0 0 : ℝ) * ‖(γ : E)‖ ^ 2 / 2 +
          ⟪(γ : E), -(A 0 0 • (γ : E)) + ℓ⟫) / c : ℝ) : ℂ)) *
        cexp (-(2 * π * I * ((A 0 0 * A 1 1 ^ 2 * ‖(ℓ : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ))) *
        cexp (2 * π * I * ((A 1 1 * ‖-(A 0 0 • (γ : E)) + ℓ‖ ^ 2 / (2 * c) : ℝ) : ℂ)) =
        cexp (2 * π * I * ((A 0 0 * A 0 1 * ‖(γ : E)‖ ^ 2 / 2 : ℝ) : ℂ)) := by
      rw [← exp_add, ← exp_add, Complex.exp_eq_exp_iff_exists_int]
      refine ⟨-(A 0 1 * i + A 0 1 * A 1 1 * j), ?_⟩
      simp only [← Int.cast_smul_eq_zsmul ℝ, inner_add_right, inner_neg_right,
        inner_smul_right, real_inner_self_eq_norm_sq, norm_add_sq_real, norm_neg, norm_smul,
        inner_neg_left, inner_smul_left, conj_trivial, Real.norm_eq_abs, mul_pow, sq_abs]
      rw [hi, hj]
      push_cast
      -- The difference of the two sides is `π i (a d - b c - 1) (a ‖γ‖² - 2 i - 2 d j) / c`.
      linear_combination (norm := (field_simp; ring))
        (π * I * (A 0 0 * ‖(γ : E)‖ ^ 2 - 2 * i - 2 * A 1 1 * j) / c) *
          (by exact_mod_cast hdet : (A 0 0 : ℂ) * A 1 1 - A 0 1 * c = 1)
    linear_combination (gaussSum L hL (A 0 0) c *
      cexp (π * I * (‖-(A 0 0 • (γ : E)) + ℓ‖ ^ 2 : ℝ) * τ)) * h1
  · intro m hm
    by_contra h
    apply Function.mem_support.mp hm
    rw [gaussSumTwisted_eq_zero hL _ hN fun hmL => h ⟨⟨_, hmL⟩, ?_⟩, mul_zero, zero_mul,
      zero_mul]
    ext
    simp [f]

/-- **A coset theta series of an even lattice under `Γ₀(N)`, with the Gauss sum unevaluated.**
Let `L` be an even full lattice of rank `2k` and level `N`, `γ ∈ L^∨`, and
`A = !![a, b; c, d] ∈ SL(2, ℤ)` with `c > 0` and `N ∣ c`. Then
`θ_{γ+L} ∣[k] A = (-i)^k c^{-k} (covol L)⁻¹ G_L(a, c) e(a b ‖γ‖² / 2) θ_{aγ+L}`. -/
theorem thetaCoset_slash_eq_gaussSum_smul (hk : finrank ℝ E = 2 * k) (A : SL(2, ℤ)) {c : ℕ}
    [NeZero c] [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (hc : A 1 0 = c)
    (hN : level L ∣ c) (γ : dual L) :
    thetaCoset L γ ∣[(k : ℤ)] A =
      ((-I) ^ k * ((c : ℂ) ^ k)⁻¹ * (covolume L : ℂ)⁻¹ * gaussSum L hL (A 0 0) c *
        cexp (2 * π * I * ((A 0 0 * A 0 1 * ‖(γ : E)‖ ^ 2 / 2 : ℝ) : ℂ))) •
        thetaCoset L (A 0 0 • (γ : E)) := by
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne c)
  ext τ
  have hden : (c : ℂ) * τ + A 1 1 ≠ 0 := by
    simpa [ModularGroup.denom_apply, hc] using UpperHalfPlane.denom_ne_zero A τ
  rw [ModularForm.SL_slash_apply, thetaCoset_smul_eq_tsum_gaussSumTwisted hL hk A hc,
    tsum_gaussSumTwisted_coset_eq hL A hc hN,
    ModularGroup.denom_apply, hc, Pi.smul_apply, smul_eq_mul, zpow_neg, zpow_natCast]
  push_cast
  have hI : (-I) ^ k * I ^ k = 1 := by rw [← mul_pow, neg_mul, I_mul_I, neg_neg, one_pow]
  rw [div_pow, mul_pow]
  field_simp
  linear_combination
    (-(gaussSum L hL (A 0 0) c * thetaCoset L (A 0 0 • (γ : E)) τ / (covolume L : ℂ))) * hI

/-- **The theta series of an even lattice under `Γ₀(N)`, with the Gauss sum unevaluated.** Let
`L` be an even full lattice of rank `2k` and level `N`, and `A = !![a, b; c, d] ∈ SL(2, ℤ)` with
`c > 0` and `N ∣ c`. Then `Θ_L ∣[k] A = (-i)^k c^{-k} (covol L)⁻¹ G_L(a, c) Θ_L`. -/
theorem thetaSeries_slash_eq_gaussSum_smul (hk : finrank ℝ E = 2 * k) (A : SL(2, ℤ)) {c : ℕ}
    [NeZero c] [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (hc : A 1 0 = c)
    (hN : level L ∣ c) :
    thetaSeries L ∣[(k : ℤ)] A =
      ((-I) ^ k * ((c : ℂ) ^ k)⁻¹ * (covolume L : ℂ)⁻¹ * gaussSum L hL (A 0 0) c) •
        thetaSeries L := by
  simpa using thetaCoset_slash_eq_gaussSum_smul hL hk A hc hN 0

/-- **A coset theta series of an even lattice under `Γ(N)`, with the Gauss sum unevaluated.** Let
`L` be an even full lattice of rank `2k` and level `N`, `γ ∈ L^∨`, and
`A = !![a, b; c, d] ∈ Γ(N)` with `c > 0`. Then
`θ_{γ+L} ∣[k] A = (-i)^k c^{-k} (covol L)⁻¹ G_L(a, c) θ_{γ+L}`: since `a ≡ 1` and `b ≡ 0` modulo
`N`, the coset `a γ + L` is `γ + L` and the factor `e(a b ‖γ‖² / 2)` is `1`. -/
theorem thetaCoset_slash_eq_gaussSum_smul_of_mem_Gamma (hk : finrank ℝ E = 2 * k)
    {A : SL(2, ℤ)} (hA : A ∈ CongruenceSubgroup.Gamma (level L)) {c : ℕ} [NeZero c]
    [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (hc : A 1 0 = c) (γ : dual L) :
    thetaCoset L γ ∣[(k : ℤ)] A =
      ((-I) ^ k * ((c : ℂ) ^ k)⁻¹ * (covolume L : ℂ)⁻¹ * gaussSum L hL (A 0 0) c) •
        thetaCoset L γ := by
  obtain ⟨ha, hb, hc0, -⟩ := CongruenceSubgroup.Gamma_mem.mp hA
  obtain ⟨t, ht⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (A 0 0) (level L)).mp
    (by simpa using ha.symm)
  obtain ⟨s, hs⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb
  have hN : level L ∣ c := by
    rw [hc] at hc0
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc0
  rw [thetaCoset_slash_eq_gaussSum_smul hL hk A hc hN γ]
  -- `a γ - γ = t (N γ) ∈ L` and `a b ‖γ‖² / 2 = a s (N ‖γ‖² / 2) ∈ ℤ`.
  have hθ : thetaCoset L (A 0 0 • (γ : E)) = thetaCoset L γ := by
    refine thetaCoset_eq_of_sub_mem L ?_
    have h : A 0 0 • (γ : E) - γ = t • (level L • (γ : E)) := by
      rw [show A 0 0 = 1 + level L * t by linear_combination ht, add_smul, one_smul,
        add_sub_cancel_left, mul_comm, mul_smul, natCast_zsmul]
    rw [h]
    exact L.smul_mem t (level_nsmul_mem γ.2)
  obtain ⟨n, hn⟩ := exists_level_mul_norm_sq_eq γ.2
  have he : cexp (2 * π * I * ((A 0 0 * A 0 1 * ‖(γ : E)‖ ^ 2 / 2 : ℝ) : ℂ)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    refine ⟨A 0 0 * s * n, ?_⟩
    rw [hs]
    push_cast
    linear_combination (π * I * A 0 0 * s) * (by exact_mod_cast hn :
      (level L : ℂ) * (‖(γ : E)‖ : ℂ) ^ 2 = 2 * n)
  rw [hθ, he, mul_one]

end IsEven

end ZLattice
