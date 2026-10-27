/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import TauCeti.Analysis.SpecialFunctions.Elliptic.WeierstrassZeta
import TauCeti.Analysis.Complex.UpperHalfPlane.Manifold

/-!
# The period lattice of a point of the upper half-plane

A point `z` of the upper half-plane determines the period pair `(z, 1)`
(`UpperHalfPlane.periodPair`), whose lattice is `ℤ z + ℤ`. This file records the Weierstrass
function `℘(x; ℤ z + ℤ)` of Mathlib's `PeriodPair.weierstrassP` in the coordinates of modular
forms:

* as a series over integer pairs `y`,
  `℘(x; ℤ z + ℤ) = ∑_y ((x - (y₀ z + y₁))⁻² - (y₀ z + y₁)⁻²)`;
* under `γ ∈ SL(2, ℤ)` the lattice of `γ z` is `(c z + d)⁻¹ (ℤ z + ℤ)`, so
  `℘(x / (c z + d); ℤ γz + ℤ) = (c z + d)² ℘(x; ℤ z + ℤ)`;
* summing first along the rows `y₀ = m`,
  `℘(x; ℤ z + ℤ) = ∑_m (P(x - m z) - P(m z))` with `P(w) = ∑_n (w + n)⁻²`
  (`TauCeti.UpperHalfPlane.rowSum`), and `P(w)` decays like `e^(-2π |Im w|)` as `|Im w| → ∞`
  (`TauCeti.UpperHalfPlane.norm_rowSum_le`,
  `TauCeti.UpperHalfPlane.norm_rowSum_le_of_le_abs_im`).

These are the inputs that make the values of `℘` at the `N`-division points of `ℤ z + ℤ` weight-two
modular forms of level `Γ(N)`.

For the Weierstrass `ζ` function `PeriodPair.weierstrassZeta` and its quasi-periods
`PeriodPair.quasiPeriod`, the same rescaling of the lattice gives the weight-one transformation
laws `ζ(x / (c z + d); ℤ γz + ℤ) = (c z + d) ζ(x; ℤ z + ℤ)` and
`η(l / (c z + d); ℤ γz + ℤ) = (c z + d) η(l; ℤ z + ℤ)`, the inputs for weight one. The lattice
series of `ζ` at a division point `(b₀ z + b₁) / M` converges locally uniformly in `z`, so these
division values are holomorphic on `ℍ`.

Finally, `ℂˣ` acts on period pairs by rescaling, `c • (ω₁, ω₂) = (c ω₁, c ω₂)`, with lattice `c Λ`;
this multiplies the lattice sums `G n` by `c⁻ⁿ`, `℘(c z)` by `c⁻²` and `℘'(c z)` by `c⁻³`, and
every lattice is a rescaling of `ℤ τ + ℤ` for some `τ` in the upper half-plane.

## Main definitions

* `UpperHalfPlane.periodPair`: the period pair `(z, 1)`.
* `TauCeti.UpperHalfPlane.rowSum`: a row `∑_n (w + n)⁻²` of the lattice series.
* `PeriodPair.instMulActionUnitsComplex`: the rescaling action `c • (ω₁, ω₂) = (c ω₁, c ω₂)`.
* `PeriodPair.latticeSMulEquiv`: multiplication by `c` from the lattice of `L` to that of `c • L`.

## Main results

* `UpperHalfPlane.hasSum_weierstrassP_periodPair`: the series over integer pairs.
* `UpperHalfPlane.intCast_mul_smul_add_intCast`: the lattice points of `γ z` in terms of those
  of `z`.
* `UpperHalfPlane.weierstrassP_periodPair_smul`: the modular transformation law.
* `UpperHalfPlane.div_denom_mem_lattice_periodPair_smul_iff`: the lattice of `γ z` is
  `(c z + d)⁻¹` times that of `z`.
* `UpperHalfPlane.hasSum_weierstrassZeta_periodPair`: the series of `ζ` over integer pairs.
* `UpperHalfPlane.weierstrassZeta_periodPair_smul`,
  `UpperHalfPlane.quasiPeriod_periodPair_smul`: the modular transformation laws of `ζ` and of its
  quasi-periods.
* `UpperHalfPlane.hasSum_weierstrassP_periodPair_rows`: the sum along rows.
* `TauCeti.UpperHalfPlane.norm_rowSum_le`, `TauCeti.UpperHalfPlane.norm_rowSum_le_of_le_abs_im`:
  the exponential decay of the rows.
* `TauCeti.UpperHalfPlane.tendsto_rowSum_atImInfty`: rows whose imaginary part grows linearly in
  `Im z` vanish at `i∞`.
* `TauCeti.UpperHalfPlane.rowSum_zero`: the row at `0` is `2 ζ(2)`.
* `TauCeti.UpperHalfPlane.tendstoLocallyUniformly_weierstrassZeta_periodPair_div`,
  `TauCeti.UpperHalfPlane.mdifferentiable_weierstrassZeta_periodPair_div`: the division values
  `z ↦ ζ((b₀ z + b₁) / M; ℤ z + ℤ)` are locally uniform limits of their partial sums, hence
  holomorphic on `ℍ`.
* `PeriodPair.lattice_smul`: the lattice of `c • L` is `c Λ`.
* `PeriodPair.G_smul`, `PeriodPair.g₂_smul`, `PeriodPair.g₃_smul`,
  `PeriodPair.weierstrassP_smul`, `PeriodPair.derivWeierstrassP_smul`: rescaling the lattice by
  `c` rescales `G n` by `c⁻ⁿ`, `℘` by `c⁻²` and `℘'` by `c⁻³`.
* `PeriodPair.G_eq_of_lattice_eq`: the lattice sums depend only on the lattice.
* `PeriodPair.exists_lattice_eq_smul_periodPair`: every lattice is homothetic to `ℤ τ + ℤ`.
-/

public section

noncomputable section

open Complex PeriodPair Matrix UpperHalfPlane
open scoped MatrixGroups Real

namespace UpperHalfPlane

/-- The period pair `(z, 1)` of a point `z` of the upper half-plane; its lattice is `ℤ z + ℤ`. -/
def periodPair (z : ℍ) : PeriodPair where
  ω₁ := z
  ω₂ := 1
  indep := by
    refine LinearIndependent.pair_iff.mpr fun s t h ↦ ?_
    have hs : s = 0 := by
      have him := congrArg Complex.im h
      simp only [Complex.real_smul, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, mul_one, Complex.zero_im] at him
      exact (mul_eq_zero.mp him).resolve_right z.im_pos.ne'
    subst hs
    simpa using h

@[simp]
lemma periodPair_ω₁ (z : ℍ) : z.periodPair.ω₁ = z := (rfl)

@[simp]
lemma periodPair_ω₂ (z : ℍ) : z.periodPair.ω₂ = 1 := (rfl)

/-- The points `m z + n` with `m n : ℤ` lie in the lattice of `z.periodPair`. -/
lemma intCast_mul_add_intCast_mem_lattice_periodPair (z : ℍ) (m n : ℤ) :
    (m : ℂ) * z + n ∈ z.periodPair.lattice :=
  mem_lattice.mpr ⟨m, n, by simp⟩

/-- A division point `(b₀ z + b₁) / N` lies in the lattice `ℤ z + ℤ` only if `b ≡ 0 mod N`. -/
lemma intCast_comp_eq_zero_of_div_mem_lattice_periodPair {N : ℕ} [NeZero N] {b : Fin 2 → ℤ}
    {z : ℍ} (h : ((b 0 : ℂ) * z + b 1) / N ∈ z.periodPair.lattice) :
    ((↑) : ℤ → ZMod N) ∘ b = 0 := by
  have hN : (N : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne N)
  have h' : (((b 0 / (N : ℤ) : ℚ) : ℂ) * z.periodPair.ω₁ +
      ((b 1 / (N : ℤ) : ℚ) : ℂ) * z.periodPair.ω₂) ∈ z.periodPair.lattice := by
    convert h using 1
    push_cast
    simp only [periodPair_ω₁, periodPair_ω₂]
    ring
  obtain ⟨h0, h1⟩ := mul_ω₁_add_mul_ω₂_mem_lattice.mp h'
  rw [Rat.den_div_intCast_eq_one_iff _ _ hN] at h0 h1
  ext i
  fin_cases i <;> simpa [ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The integer pairs parametrize the lattice of `z.periodPair` by `y ↦ y₀ z + y₁`. -/
private def latticeEquiv (z : ℍ) : (Fin 2 → ℤ) ≃ z.periodPair.lattice :=
  (finTwoArrowEquiv ℤ).trans z.periodPair.latticeEquivProd.symm.toEquiv

private lemma coe_latticeEquiv (z : ℍ) (y : Fin 2 → ℤ) :
    (latticeEquiv z y : ℂ) = y 0 * z + y 1 := by
  simp [latticeEquiv, latticeEquiv_symm_apply]

/-- **The Weierstrass function of `ℤ z + ℤ` as a series over integer pairs**:
`℘(x; ℤ z + ℤ) = ∑_y ((x - (y₀ z + y₁))⁻² - (y₀ z + y₁)⁻²)`, the series converging absolutely. -/
theorem hasSum_weierstrassP_periodPair (z : ℍ) (x : ℂ) :
    HasSum (fun y : Fin 2 → ℤ ↦ 1 / (x - (y 0 * z + y 1)) ^ 2 - 1 / ((y 0 : ℂ) * z + y 1) ^ 2)
      (℘[z.periodPair] x) := by
  have h := z.periodPair.hasSum_weierstrassP x
  rw [← (latticeEquiv z).hasSum_iff] at h
  simpa only [Function.comp_def, coe_latticeEquiv] using h

/-- In the coordinates of `γ z`, the lattice point `y₀ γz + y₁` is `(y γ)₀ z + (y γ)₁` divided by
`c z + d`. -/
lemma intCast_mul_smul_add_intCast (γ : SL(2, ℤ)) (z : ℍ) (y : Fin 2 → ℤ) :
    (y 0 : ℂ) * ↑(γ • z) + y 1 =
      (((y ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) 0 : ℂ) * z +
        (y ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) 1) / denom γ z := by
  simpa [EisensteinSeries.eisSummand, div_eq_inv_mul] using
    EisensteinSeries.eisSummand_SL2_apply (-1) y γ z

/-- **The modular transformation of `℘`.** For `γ ∈ SL(2, ℤ)` the lattice of `γ z` is
`(c z + d)⁻¹ (ℤ z + ℤ)`, so `℘(x / (c z + d); ℤ γz + ℤ) = (c z + d)² ℘(x; ℤ z + ℤ)`. -/
theorem weierstrassP_periodPair_smul (γ : SL(2, ℤ)) (z : ℍ) (x : ℂ) :
    ℘[(γ • z).periodPair] (x / denom γ z) = denom γ z ^ 2 * ℘[z.periodPair] x := by
  have hD := denom_ne_zero γ z
  -- reindex the integer pairs by `y ↦ y γ`
  let e : (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
    Matrix.toLinearEquivRight'OfInv
      (M := ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
      (M' := (γ : Matrix (Fin 2) (Fin 2) ℤ))
      (by simp [Matrix.adjugate_mul]) (by simp [Matrix.mul_adjugate])
  have h := (hasSum_weierstrassP_periodPair z x).mul_left (denom γ z ^ 2)
  rw [← e.toEquiv.hasSum_iff] at h
  refine (hasSum_weierstrassP_periodPair (γ • z) (x / denom γ z)).unique (h.congr_fun fun y ↦ ?_)
  simp only [Function.comp_apply, LinearEquiv.coe_toEquiv, e,
    Matrix.toLinearEquivRight'OfInv_apply, Matrix.toLinearMapRight'_apply,
    intCast_mul_smul_add_intCast γ z y]
  rw [← sub_div, div_pow, div_pow, one_div_div, one_div_div]
  ring

/-- The lattice of `γ z` is `(c z + d)⁻¹` times that of `z`. -/
lemma div_denom_mem_lattice_periodPair_smul_iff (γ : SL(2, ℤ)) (z : ℍ) (x : ℂ) :
    x / denom γ z ∈ (γ • z).periodPair.lattice ↔ x ∈ z.periodPair.lattice := by
  have hD := denom_ne_zero γ z
  constructor
  · intro h
    obtain ⟨m, n, hmn⟩ := mem_lattice.mp h
    have h' := intCast_mul_smul_add_intCast γ z ![m, n]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, periodPair_ω₁, periodPair_ω₂,
      mul_one] at h' hmn
    rw [hmn, div_left_inj' hD] at h'
    rw [h']
    exact intCast_mul_add_intCast_mem_lattice_periodPair z _ _
  · intro h
    obtain ⟨m, n, rfl⟩ := mem_lattice.mp h
    -- the integer pair `y = (m, n) γ⁻¹` has `y γ = (m, n)`
    set y : Fin 2 → ℤ := ![m, n] ᵥ* ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
    have hy : y ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ) = ![m, n] := by
      rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
    have h' := intCast_mul_smul_add_intCast γ z y
    rw [hy] at h'
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, periodPair_ω₁, periodPair_ω₂,
      mul_one] at h' ⊢
    rw [← h']
    exact intCast_mul_add_intCast_mem_lattice_periodPair (γ • z) _ _

/-- **The Weierstrass `ζ` function of `ℤ z + ℤ` as a series over integer pairs**:
`ζ(x; ℤ z + ℤ) = ∑_y (1 / (x - (y₀ z + y₁)) + 1 / (y₀ z + y₁) + x / (y₀ z + y₁)²)`, the series
converging absolutely. -/
theorem hasSum_weierstrassZeta_periodPair (z : ℍ) (x : ℂ) :
    HasSum (fun y : Fin 2 → ℤ ↦ 1 / (x - (y 0 * z + y 1)) + 1 / ((y 0 : ℂ) * z + y 1) +
      x / ((y 0 : ℂ) * z + y 1) ^ 2) (z.periodPair.weierstrassZeta x) := by
  have h := z.periodPair.hasSum_weierstrassZeta x
  rw [← (latticeEquiv z).hasSum_iff] at h
  simpa only [Function.comp_def, coe_latticeEquiv] using h

/-- **The modular transformation of `ζ`.** For `γ ∈ SL(2, ℤ)` the lattice of `γ z` is
`(c z + d)⁻¹ (ℤ z + ℤ)`, so `ζ(x / (c z + d); ℤ γz + ℤ) = (c z + d) ζ(x; ℤ z + ℤ)`. -/
theorem weierstrassZeta_periodPair_smul (γ : SL(2, ℤ)) (z : ℍ) (x : ℂ) :
    (γ • z).periodPair.weierstrassZeta (x / denom γ z) =
      denom γ z * z.periodPair.weierstrassZeta x := by
  have hD := denom_ne_zero γ z
  -- reindex the integer pairs by `y ↦ y γ`
  let e : (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
    Matrix.toLinearEquivRight'OfInv
      (M := ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
      (M' := (γ : Matrix (Fin 2) (Fin 2) ℤ))
      (by simp [Matrix.adjugate_mul]) (by simp [Matrix.mul_adjugate])
  have h := (hasSum_weierstrassZeta_periodPair z x).mul_left (denom γ z)
  rw [← e.toEquiv.hasSum_iff] at h
  refine (hasSum_weierstrassZeta_periodPair (γ • z) (x / denom γ z)).unique
    (h.congr_fun fun y ↦ ?_)
  simp only [Function.comp_apply, LinearEquiv.coe_toEquiv, e,
    Matrix.toLinearEquivRight'OfInv_apply, Matrix.toLinearMapRight'_apply,
    intCast_mul_smul_add_intCast γ z y]
  rw [← sub_div, one_div_div, one_div_div, div_pow, div_div_div_eq, pow_two (denom γ z),
    ← mul_assoc, mul_comm (denom γ z) (_ ^ 2), mul_div_mul_right _ _ hD]
  ring

/-- **The modular transformation of the quasi-periods.** The quasi-period of the lattice
point `l / (c z + d)` of `ℤ γz + ℤ` is `(c z + d)` times that of `l` in `ℤ z + ℤ`. -/
theorem quasiPeriod_periodPair_smul (γ : SL(2, ℤ)) (z : ℍ) (l : z.periodPair.lattice) :
    (γ • z).periodPair.quasiPeriod
        ⟨l / denom γ z, (div_denom_mem_lattice_periodPair_smul_iff γ z l).mpr l.2⟩ =
      denom γ z * z.periodPair.quasiPeriod l := by
  set x := z.periodPair.ω₁ / 2
  have hx : x ∉ z.periodPair.lattice := z.periodPair.ω₁_div_two_notMem_lattice
  have hx' : x / denom γ z ∉ (γ • z).periodPair.lattice :=
    (div_denom_mem_lattice_periodPair_smul_iff γ z x).not.mpr hx
  have h := (γ • z).periodPair.weierstrassZeta_add_coe hx'
    ⟨l / denom γ z, (div_denom_mem_lattice_periodPair_smul_iff γ z l).mpr l.2⟩
  rw [← add_div, weierstrassZeta_periodPair_smul, weierstrassZeta_periodPair_smul,
    z.periodPair.weierstrassZeta_add_coe hx, mul_add] at h
  exact (add_left_cancel h).symm

end UpperHalfPlane

namespace TauCeti.UpperHalfPlane

/-- A row `P(w) = ∑_n (w + n)⁻²` of the lattice series of `ℤ z + ℤ`: the row `y₀ = m` of
`℘(x; ℤ z + ℤ)` is `P(x - m z) - P(m z)`. -/
def rowSum (w : ℂ) : ℂ := ∑' n : ℤ, 1 / (w + n) ^ 2

lemma rowSum_def (w : ℂ) : rowSum w = ∑' n : ℤ, 1 / (w + n) ^ 2 := (rfl)

/-- The rows `∑_n (w + n)⁻²` of the lattice series are absolutely convergent. -/
lemma summable_one_div_add_intCast_sq (w : ℂ) :
    Summable fun n : ℤ ↦ 1 / (w + n) ^ 2 := by
  simpa [one_div] using EisensteinSeries.linear_right_summable w 1 (k := 2) le_rfl

/-- The row `∑_n (w + n)⁻²` converges to `rowSum w`. -/
lemma hasSum_rowSum (w : ℂ) : HasSum (fun n : ℤ ↦ 1 / (w + n) ^ 2) (rowSum w) := by
  rw [rowSum_def]
  exact (summable_one_div_add_intCast_sq w).hasSum

/-- The rows are even functions. -/
lemma rowSum_neg (w : ℂ) : rowSum (-w) = rowSum w := by
  rw [rowSum_def, rowSum_def, ← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n ↦ ?_
  simp only [Equiv.neg_apply, Int.cast_neg]
  ring

/-- **The rows decay exponentially**: for `w` in the upper half-plane and `q = e^(2π i w)`,
`‖∑_n (w + n)⁻²‖ ≤ 4 π² ‖q‖ / (1 - ‖q‖)²`. -/
theorem norm_rowSum_le (w : ℍ) :
    ‖rowSum w‖ ≤
      4 * π ^ 2 * ‖cexp (2 * π * Complex.I * w)‖ /
        (1 - ‖cexp (2 * π * Complex.I * w)‖) ^ 2 := by
  have H := EisensteinSeries.qExpansion_identity (k := 1) le_rfl w
  simp only [Nat.reduceAdd, pow_one, Nat.factorial_one, Nat.cast_one, div_one] at H
  set q := cexp (2 * π * Complex.I * w)
  have hq : ‖q‖ < 1 := norm_exp_two_pi_I_lt_one w
  have hq' : 0 < 1 - ‖q‖ := by linarith
  have h1 : 1 - ‖q‖ ≤ ‖1 - q‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) q
  have h2 : ‖(-2 * π * Complex.I : ℂ)‖ ^ 2 = 4 * π ^ 2 := by
    simp [abs_of_pos Real.pi_pos]
    ring
  rw [rowSum_def, H, tsum_coe_mul_geometric_of_norm_lt_one hq, norm_mul, norm_div, norm_pow,
    norm_pow, h2, mul_div_assoc]
  gcongr

/-- **The rows decay exponentially away from the real axis**: if `0 < t ≤ |Im w|`, then
`‖∑_n (w + n)⁻²‖ ≤ 4 π² e^(-2π |Im w|) / (1 - e^(-2π t))²`. -/
theorem norm_rowSum_le_of_le_abs_im {w : ℂ} {t : ℝ} (ht : 0 < t) (hw : t ≤ |w.im|) :
    ‖rowSum w‖ ≤ 4 * π ^ 2 / (1 - Real.exp (-2 * π * t)) ^ 2 * Real.exp (-2 * π * |w.im|) := by
  have hθ : Real.exp (-2 * π * t) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  -- reduce to `0 < Im w` by evenness
  wlog hpos : 0 < w.im generalizing w
  · have hne : w.im ≠ 0 := by
      intro h
      rw [h, abs_zero] at hw
      linarith
    have := this (w := -w) (by simpa using hw)
      (by simpa using lt_of_le_of_ne (not_lt.mp hpos) hne)
    rwa [rowSum_neg, Complex.neg_im, abs_neg] at this
  rw [abs_of_pos hpos] at hw ⊢
  have hq : ‖cexp (2 * π * Complex.I * w)‖ = Real.exp (-2 * π * w.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have h := norm_rowSum_le (UpperHalfPlane.mk w hpos)
  simp only [hq] at h
  have hle : Real.exp (-2 * π * w.im) ≤ Real.exp (-2 * π * t) := by
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_pos]
  refine h.trans ?_
  rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_assoc]
  gcongr

/-- The row at `0` is `P(0) = ∑_{n ≠ 0} n⁻² = 2 ζ(2)`, the value at `i∞` of Mathlib's
`EisensteinSeries.G2`. -/
@[simp]
lemma rowSum_zero : rowSum 0 = 2 * riemannZeta 2 := by
  have h := two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (k := 2) le_rfl even_two
  push_cast at h
  rw [h, rowSum_def]
  exact tsum_congr fun n ↦ by simp

open Filter Topology in
/-- **The rows vanish at `i∞`**: if the imaginary part of `w(z)` grows at least like `c Im z` for
some `c > 0`, then `P(w(z)) → 0` as `Im z → ∞`. -/
theorem tendsto_rowSum_atImInfty {w : ℍ → ℂ} {c : ℝ} (hc : 0 < c)
    (hw : ∀ z, c * z.im ≤ |(w z).im|) :
    Tendsto (fun z ↦ rowSum (w z)) atImInfty (𝓝 0) := by
  have him : Tendsto (fun z : ℍ ↦ z.im) atImInfty atTop := tendsto_comap
  have hexp : Tendsto (fun z : ℍ ↦ 4 * π ^ 2 / (1 - Real.exp (-2 * π * 1)) ^ 2 *
      Real.exp (-(2 * π * c * z.im))) atImInfty (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (him.const_mul_atTop (by positivity : 0 < 2 * π * c))).const_mul
        (4 * π ^ 2 / (1 - Real.exp (-2 * π * 1)) ^ 2)
  refine squeeze_zero_norm' ?_ hexp
  filter_upwards [him.eventually_ge_atTop (1 / c)] with z hz
  have hw1 : 1 ≤ |(w z).im| := by
    refine le_trans ?_ (hw z)
    rwa [div_le_iff₀' hc] at hz
  refine (norm_rowSum_le_of_le_abs_im one_pos hw1).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [hw z, Real.pi_pos]))
      (div_nonneg (by positivity) (sq_nonneg _)))

end TauCeti.UpperHalfPlane

namespace UpperHalfPlane

open TauCeti.UpperHalfPlane

/-- **The Weierstrass function of `ℤ z + ℤ` summed along rows**:
`℘(x; ℤ z + ℤ) = ∑_m (∑_n (x - m z + n)⁻² - ∑_n (m z + n)⁻²)`. -/
theorem hasSum_weierstrassP_periodPair_rows (z : ℍ) (x : ℂ) :
    HasSum (fun m : ℤ ↦ rowSum (x - m * z) - rowSum (m * z)) (℘[z.periodPair] x) := by
  have h := hasSum_weierstrassP_periodPair z x
  rw [← (finTwoArrowEquiv ℤ).symm.hasSum_iff] at h
  refine h.prod_fiberwise fun m ↦ ?_
  have h₁ : HasSum (fun n : ℤ ↦ 1 / (x - (m * z + n)) ^ 2) (rowSum (x - m * z)) := by
    rw [← rowSum_neg]
    convert hasSum_rowSum (-(x - m * z)) using 2 with n
    ring
  simpa [Function.comp_def] using h₁.sub (hasSum_rowSum ((m : ℂ) * z))

end UpperHalfPlane

namespace TauCeti.UpperHalfPlane

open EisensteinSeries Filter
open scoped Topology Manifold

/-- The lattice series of `ζ` at the division point `(b₀ z + b₁) / M` converges locally uniformly
in `z`. -/
theorem tendstoLocallyUniformly_weierstrassZeta_periodPair_div (M : ℕ) [NeZero M] (b : Fin 2 → ℤ) :
    TendstoLocallyUniformly
      (fun (s : Finset (Fin 2 → ℤ)) (z : ℍ) ↦ ∑ y ∈ s,
        (1 / (((b 0 : ℂ) * z + b 1) / M - (y 0 * z + y 1)) + 1 / ((y 0 : ℂ) * z + y 1) +
          ((b 0 : ℂ) * z + b 1) / M / ((y 0 : ℂ) * z + y 1) ^ 2))
      (fun z : ℍ ↦ z.periodPair.weierstrassZeta (((b 0 : ℂ) * z + b 1) / M)) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨A, B, hB, HABK⟩ := subset_verticalStrip_of_isCompact hK
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun z : ℍ ↦ (z : ℂ))
    continuous_coe.continuousOn
  set r₀ := r ⟨⟨A, B⟩, hB⟩
  have hr₀ : 0 < r₀ := r_pos _
  set R : ℝ := |(b 0 : ℝ)| * |C| + |(b 1 : ℝ)| + 1
  have hR : 0 < R := by positivity
  have hlim : (fun z : ℍ ↦ z.periodPair.weierstrassZeta (((b 0 : ℂ) * z + b 1) / M)) =
      fun z : ℍ ↦ ∑' y : Fin 2 → ℤ, (1 / (((b 0 : ℂ) * z + b 1) / M - (y 0 * z + y 1)) +
        1 / ((y 0 : ℂ) * z + y 1) + ((b 0 : ℂ) * z + b 1) / M / ((y 0 : ℂ) * z + y 1) ^ 2) :=
    funext fun z ↦ (hasSum_weierstrassZeta_periodPair z _).tsum_eq.symm
  rw [hlim]
  refine tendstoUniformlyOn_tsum_of_cofinite_eventually
    (u := fun y ↦ 2 * R ^ 2 * r₀ ^ (-3 : ℝ) * ‖y‖ ^ (-3 : ℝ))
    ((summable_one_div_norm_rpow (by norm_num)).mul_left _) ?_
  have hev : ∀ᶠ y : Fin 2 → ℤ in cofinite, 2 * R / r₀ ≤ ‖y‖ := by
    rw [← cocompact_eq_cofinite]
    exact tendsto_norm_cocompact_atTop.eventually_ge_atTop _
  filter_upwards [hev] with y hy z hz
  have hy' : 2 * R ≤ r₀ * ‖y‖ := by
    rwa [div_le_iff₀' hr₀] at hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp only [norm_zero, mul_zero] at hy'
    linarith
  have hl : r₀ * ‖y‖ ≤ ‖(y 0 : ℂ) * z + y 1‖ :=
    (mul_le_mul_of_nonneg_right (r_lower_bound_on_verticalStrip z hB (HABK hz))
      (norm_nonneg _)).trans (r_mul_max_le z hy0)
  have hx : ‖((b 0 : ℂ) * z + b 1) / M‖ < R := by
    have hM : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.one_le
    have hz' : ‖(z : ℂ)‖ ≤ |C| := (hC z hz).trans (le_abs_self C)
    rw [norm_div, Complex.norm_natCast]
    refine (div_le_self (norm_nonneg _) hM).trans_lt ?_
    refine (norm_add_le _ _).trans_lt ?_
    rw [norm_mul, Complex.norm_intCast, Complex.norm_intCast]
    have := mul_le_mul_of_nonneg_left hz' (abs_nonneg (b 0 : ℝ))
    linarith
  refine (weierstrassZeta_bound hR hx (hy'.trans hl)).trans ?_
  rw [mul_assoc (2 * R ^ 2), ← Real.mul_rpow hr₀.le (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (by positivity) hl (by norm_num)) (by positivity)

/-- The partial sums of the lattice series of `ζ` at a division point are holomorphic: in
Eisenstein summands, the terms are `M (b - M y)⁻¹ + y⁻¹ + x y⁻²` with `x = (b₀ z + b₁) / M`. -/
private lemma mdifferentiable_weierstrassZeta_periodPair_div_term (M : ℕ) [NeZero M]
    (b y : Fin 2 → ℤ) :
    MDiff fun z : ℍ ↦ (1 / (((b 0 : ℂ) * z + b 1) / M - (y 0 * z + y 1)) +
      1 / ((y 0 : ℂ) * z + y 1) + ((b 0 : ℂ) * z + b 1) / M / ((y 0 : ℂ) * z + y 1) ^ 2 : ℂ) := by
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hS (k : ℤ) (v : Fin 2 → ℤ) : MDiff (eisSummand k v) :=
    UpperHalfPlane.mdifferentiable_iff.mpr (eisSummand_extension_differentiableOn k v)
  have hx : MDiff fun z : ℍ ↦ ((b 0 : ℂ) * z + b 1) / M :=
    ((mdifferentiable_const.mul mdifferentiable_coe).add mdifferentiable_const).mul
      mdifferentiable_const
  have h : (fun z : ℍ ↦ 1 / (((b 0 : ℂ) * z + b 1) / M - (y 0 * z + y 1)) +
      1 / ((y 0 : ℂ) * z + y 1) + ((b 0 : ℂ) * z + b 1) / M / ((y 0 : ℂ) * z + y 1) ^ 2) =
      fun z ↦ M * eisSummand 1 (b - M • y) z + eisSummand 1 y z +
        ((b 0 : ℂ) * z + b 1) / M * eisSummand 2 y z := by
    ext z
    have he : ((b - M • y) 0 : ℂ) * z + (b - M • y) 1 =
        M * (((b 0 : ℂ) * z + b 1) / M - (y 0 * z + y 1)) := by
      simp only [Pi.sub_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, Int.cast_sub,
        Int.cast_mul, Int.cast_natCast]
      field_simp
      ring
    rw [eisSummand, eisSummand, eisSummand, he, _root_.zpow_neg_one, _root_.zpow_neg_one,
      _root_.zpow_neg, zpow_ofNat, mul_inv, mul_inv_cancel_left₀ hM]
    simp only [div_eq_mul_inv, one_mul]
  rw [h]
  exact ((mdifferentiable_const.mul (hS 1 _)).add (hS 1 y)).add (hx.mul (hS 2 y))

/-- Each division value of `ζ` is holomorphic on `ℍ`. -/
theorem mdifferentiable_weierstrassZeta_periodPair_div (M : ℕ) [NeZero M] (b : Fin 2 → ℤ) :
    MDiff fun z : ℍ ↦ z.periodPair.weierstrassZeta (((b 0 : ℂ) * z + b 1) / M) :=
  mdifferentiable_of_tendstoLocallyUniformly
    (tendstoLocallyUniformly_weierstrassZeta_periodPair_div M b) (Eventually.of_forall fun s ↦ by
      convert MDifferentiable.sum (t := s)
        fun y _ ↦ mdifferentiable_weierstrassZeta_periodPair_div_term M b y using 1
      ext z
      simp [Finset.sum_apply])

end TauCeti.UpperHalfPlane

/-! ### Rescaling a period pair -/

namespace PeriodPair

@[ext]
lemma ext {L L' : PeriodPair} (h₁ : L.ω₁ = L'.ω₁) (h₂ : L.ω₂ = L'.ω₂) : L = L' := by
  cases L
  cases L'
  congr

/-- Multiplying a period pair by a nonzero complex number: `c • (ω₁, ω₂) = (c ω₁, c ω₂)`. Its
lattice is `c Λ` (`PeriodPair.lattice_smul`). -/
instance instSMulUnitsComplex : SMul ℂˣ PeriodPair where
  smul c L :=
    { ω₁ := c * L.ω₁
      ω₂ := c * L.ω₂
      indep := by
        convert L.indep.map' (LinearMap.mulLeft ℝ (c : ℂ))
          (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ c.ne_zero)) using 1
        ext i
        fin_cases i <;> rfl }

variable (L : PeriodPair) (c : ℂˣ)

@[simp]
lemma smul_ω₁ : (c • L).ω₁ = c * L.ω₁ := rfl

@[simp]
lemma smul_ω₂ : (c • L).ω₂ = c * L.ω₂ := rfl

/-- The rescaling action of `ℂˣ` on period pairs. -/
instance instMulActionUnitsComplex : MulAction ℂˣ PeriodPair where
  one_smul L := by ext <;> simp
  mul_smul c d L := by ext <;> simp [mul_assoc]

/-- The lattice of `c • L` is the image of the lattice of `L` under multiplication by `c`. -/
lemma lattice_smul : (c • L).lattice = L.lattice.map (LinearMap.mulLeft ℤ (c : ℂ)) := by
  simp [lattice, Submodule.map_span]

/-- Multiplication by `c` identifies the lattices of `L` and of `c • L`. -/
def latticeSMulEquiv : L.lattice ≃ₗ[ℤ] (c • L).lattice :=
  (Submodule.equivMapOfInjective _ (mul_right_injective₀ c.ne_zero) L.lattice).trans
    (LinearEquiv.ofEq _ _ (L.lattice_smul c).symm)

@[simp]
lemma coe_latticeSMulEquiv (l : L.lattice) : (L.latticeSMulEquiv c l : ℂ) = c * l := by
  simp only [latticeSMulEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
  exact Submodule.coe_equivMapOfInjective_apply ..

@[simp]
lemma mul_mem_lattice_smul_iff {x : ℂ} : (c : ℂ) * x ∈ (c • L).lattice ↔ x ∈ L.lattice := by
  rw [lattice_smul, Submodule.mem_map]
  exact ⟨fun ⟨y, hy, hyx⟩ ↦ mul_right_injective₀ c.ne_zero hyx ▸ hy, fun h ↦ ⟨x, h, rfl⟩⟩

/-- The lattice sums `G n` are homogeneous of degree `-n` in the lattice. -/
@[simp]
lemma G_smul (n : ℕ) : (c • L).G n = L.G n / (c : ℂ) ^ n := by
  rw [G, G, ← (L.latticeSMulEquiv c).toEquiv.tsum_eq, div_eq_mul_inv, ← tsum_mul_right]
  simp [mul_pow, mul_comm]

@[simp]
lemma g₂_smul : (c • L).g₂ = L.g₂ / (c : ℂ) ^ 4 := by
  rw [g₂, g₂, G_smul, mul_div_assoc]

@[simp]
lemma g₃_smul : (c • L).g₃ = L.g₃ / (c : ℂ) ^ 6 := by
  rw [g₃, g₃, G_smul, mul_div_assoc]

/-- `℘(c z; c Λ) = c⁻² ℘(z; Λ)`. -/
@[simp]
lemma weierstrassP_smul (z : ℂ) : ℘[c • L] (c * z) = ℘[L] z / (c : ℂ) ^ 2 := by
  rw [weierstrassP, weierstrassP, ← (L.latticeSMulEquiv c).toEquiv.tsum_eq, div_eq_mul_inv,
    ← tsum_mul_right]
  congr 1 with l
  simp only [LinearEquiv.coe_toEquiv, coe_latticeSMulEquiv, ← mul_sub, mul_pow, one_div, mul_inv]
  ring

/-- `℘'(c z; c Λ) = c⁻³ ℘'(z; Λ)`. -/
@[simp]
lemma derivWeierstrassP_smul (z : ℂ) : ℘'[c • L] (c * z) = ℘'[L] z / (c : ℂ) ^ 3 := by
  rw [derivWeierstrassP, derivWeierstrassP, ← (L.latticeSMulEquiv c).toEquiv.tsum_eq,
    neg_div, div_eq_mul_inv, ← tsum_mul_right]
  congr 2 with l
  simp only [LinearEquiv.coe_toEquiv, coe_latticeSMulEquiv, ← mul_sub, mul_pow, div_eq_mul_inv,
    mul_inv]
  ring

/-- The lattice sums `G n` depend only on the lattice, not on the chosen basis. -/
lemma G_eq_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) : L.G = L'.G := by
  ext n
  rw [G, G, h]

lemma ω₁_ne_zero : L.ω₁ ≠ 0 := by
  simpa using L.indep.ne_zero 0

lemma ω₂_ne_zero : L.ω₂ ≠ 0 := by
  simpa using L.indep.ne_zero 1

/-- The ratio of the two periods is not real. -/
lemma im_ω₁_div_ω₂_ne_zero : (L.ω₁ / L.ω₂).im ≠ 0 := by
  intro h
  have hr : ((L.ω₁ / L.ω₂).re : ℂ) = L.ω₁ / L.ω₂ := Complex.ext (by simp) (by simp [h])
  obtain ⟨hs, -⟩ := LinearIndependent.pair_iff.mp L.indep 1 (-(L.ω₁ / L.ω₂).re) (by
    rw [one_smul, Complex.real_smul, Complex.ofReal_neg, hr, neg_mul,
      div_mul_cancel₀ _ L.ω₂_ne_zero, add_neg_cancel])
  exact one_ne_zero hs

/-- **Every lattice is homothetic to `ℤ τ + ℤ`** for some `τ` in the upper half-plane: take
`τ = ω₁ / ω₂` or `τ = ω₂ / ω₁`, whichever has positive imaginary part. -/
lemma exists_lattice_eq_smul_periodPair :
    ∃ (c : ℂˣ) (τ : ℍ), L.lattice = (c • τ.periodPair).lattice := by
  rcases L.im_ω₁_div_ω₂_ne_zero.lt_or_gt with h | h
  · have h' : 0 < (L.ω₂ / L.ω₁).im := by
      rw [← inv_div, Complex.inv_im]
      exact div_pos (neg_pos.mpr h) (Complex.normSq_pos.mpr (div_ne_zero L.ω₁_ne_zero L.ω₂_ne_zero))
    refine ⟨Units.mk0 L.ω₁ L.ω₁_ne_zero, .mk _ h', ?_⟩
    simp only [lattice, smul_ω₁, smul_ω₂, periodPair_ω₁, periodPair_ω₂, Units.val_mk0,
      mul_div_cancel₀ _ L.ω₁_ne_zero, mul_one, Set.pair_comm]
  · refine ⟨Units.mk0 L.ω₂ L.ω₂_ne_zero, .mk _ h, ?_⟩
    simp only [lattice, smul_ω₁, smul_ω₂, periodPair_ω₁, periodPair_ω₂, Units.val_mk0,
      mul_div_cancel₀ _ L.ω₂_ne_zero, mul_one]

end PeriodPair
