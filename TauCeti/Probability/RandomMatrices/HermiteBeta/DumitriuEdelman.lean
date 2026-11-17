/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import TauCeti.Analysis.Matrix.Jacobi.Moments
public import TauCeti.Probability.Distributions.Chi.Basic
public import TauCeti.Probability.RandomMatrices.HermiteBeta.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Matrix.Jacobi.Jacobian
import TauCeti.MeasureTheory.Measure.PiWithDensity
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# The Dumitriu–Edelman tridiagonal model and the Mehta–Selberg integral

For any `β > 0` and `n : ℕ`, the `(n + 1) × (n + 1)` Dumitriu–Edelman Hermite beta matrix is the
symmetric tridiagonal Jacobi matrix `TauCeti.jacobiMatrix a b` with independent `N(0, 2)` diagonal
entries `a i` and independent `χ_{β (n - k)}` subdiagonal entries `b k` (`k : Fin n`).

Combining the spectral change-of-variables theorem `TauCeti.map_jacobiSpectralChart_withDensity`
with the Dirichlet simplex chart density
`TauCeti.Probability.dirichletMeasure_eq_map_withDensity_dirichletChartPDF`, this file proves:

* the Dumitriu–Edelman joint spectral law (both at canonical confinement `c = 1 / 2` and, by
  rescaling by `(√(2 * c))⁻¹`, at arbitrary confinement `c > 0`): the ordered eigenvalues follow
  `TauCeti.Probability.gaussianBetaOrderedMeasure β c (n + 1)`, the spectral weights follow
  `TauCeti.Probability.dirichletMeasure (fun _ => β / 2)`, and the two are independent;
* exact normalization (`∫⁻ = 1`) and `IsProbabilityMeasure` for both the ordered and unordered
  Gaussian beta measures for every `n : ℕ`, `β > 0`, and `c > 0`, together with the Mehta–Selberg
  Bochner integral identity and the `n = 1` Gaussian specialization.

## Main definitions

* `TauCeti.Probability.hermiteBetaTridiagonalLaw`: the independent `N(0, 2)` / `χ_{β (n - k)}`
  parameter law on `(Fin (n + 1) → ℝ) × (Fin n → ℝ)`.

## Main results

* `TauCeti.Probability.map_jacobiSpectralChart_hermiteBetaTridiagonalLaw`: joint pushforward into
  spectral chart coordinates.
* `TauCeti.Probability.map_jacobiSpectral_hermiteBetaTridiagonalLaw` and
  `TauCeti.Probability.map_jacobiSpectral_smul_hermiteBetaTridiagonalLaw`: Dumitriu–Edelman joint
  law of ordered eigenvalues and spectral weights (at `c = 1 / 2` and general `c > 0`).
* `TauCeti.Probability.indepFun_jacobiEigenvalues_jacobiSpectralWeight_hermiteBetaTridiagonalLaw`:
  independence of eigenvalues and spectral weights.
* `TauCeti.Probability.lintegral_gaussianBetaOrderedPDF_eq_one`,
  `TauCeti.Probability.isProbabilityMeasure_gaussianBetaOrderedMeasure`,
  `TauCeti.Probability.lintegral_gaussianBetaPDF_eq_one`, and
  `TauCeti.Probability.isProbabilityMeasure_gaussianBetaMeasure`: exact normalization of the
  ordered and unordered Gaussian beta laws.
* `TauCeti.Probability.integral_exp_mul_vandermondeProd_rpow`: the Mehta–Selberg integral formula.
* `TauCeti.Probability.gaussianBetaMeasure_one_eq_gaussianReal`: `n = 1` specialization to
  `N(0, c⁻¹)`.

## References

* I. Dumitriu and A. Edelman, *Matrix models for beta ensembles*, J. Math. Phys. 43 (2002),
  5830–5847.
* G. W. Anderson, A. Guionnet, and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010, §4.5.1.
* P. J. Forrester, *Log-Gases and Random Matrices*, Princeton University Press, 2010, §1.9 and §4.7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set TauCeti
open scoped ENNReal

namespace TauCeti

namespace Probability

/-! ### The Dumitriu–Edelman tridiagonal matrix model -/

/-- The parameter law of the `(n + 1) × (n + 1)` Dumitriu–Edelman Hermite beta tridiagonal matrix:
independent `N(0, 2)` diagonal entries and `χ_{β (n - k)}` subdiagonal entries (`k : Fin n`). -/
def hermiteBetaTridiagonalLaw (β : ℝ) (n : ℕ) : Measure ((Fin (n + 1) → ℝ) × (Fin n → ℝ)) :=
  (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 2).prod
    (Measure.pi fun k : Fin n => chiMeasure (β * (n - k.val : ℝ)) 1)

/-- For `β ≥ 0`, `hermiteBetaTridiagonalLaw β n` is a probability measure. -/
theorem isProbabilityMeasure_hermiteBetaTridiagonalLaw {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    IsProbabilityMeasure (hermiteBetaTridiagonalLaw β n) := by
  have : ∀ k : Fin n, IsProbabilityMeasure (chiMeasure (β * (n - k.val : ℝ)) 1) := fun k =>
    isProbabilityMeasure_chiMeasure (mul_nonneg hβ (sub_nonneg.mpr (Nat.cast_le.mpr k.isLt.le)))
      one_pos
  unfold hermiteBetaTridiagonalLaw
  infer_instance

/-- For `β > 0`, `hermiteBetaTridiagonalLaw β n` has explicit product Lebesgue density. -/
theorem hermiteBetaTridiagonalLaw_eq_withDensity {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    hermiteBetaTridiagonalLaw β n =
      (volume.prod volume).withDensity fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) =>
        (∏ i : Fin (n + 1), gaussianPDF 0 2 (p.1 i)) *
          ∏ k : Fin n, chiPDF (β * (n - k.val : ℝ)) 1 (p.2 k) := by
  have h2 : (2 : NNReal) ≠ 0 := by norm_num
  have hgauss : (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 2) =
      volume.withDensity fun a : Fin (n + 1) → ℝ => ∏ i : Fin (n + 1), gaussianPDF 0 2 (a i) := by
    have : SigmaFinite (volume.withDensity (gaussianPDF 0 2)) := by
      rw [← gaussianReal_of_var_ne_zero 0 h2]; infer_instance
    simp_rw [gaussianReal_of_var_ne_zero 0 h2]
    exact TauCeti.pi_withDensity (fun _ : Fin (n + 1) => (volume : Measure ℝ))
      (fun _ => measurable_gaussianPDF 0 2)
  have hchi : (Measure.pi fun k : Fin n => chiMeasure (β * (n - k.val : ℝ)) 1) =
      volume.withDensity fun b : Fin n → ℝ =>
        ∏ k : Fin n, chiPDF (β * (n - k.val : ℝ)) 1 (b k) := by
    have hdeg : ∀ k : Fin n, 0 < β * (n - k.val : ℝ) := fun k =>
      mul_pos hβ (sub_pos.mpr (Nat.cast_lt.mpr k.isLt))
    have : ∀ k : Fin n,
        SigmaFinite (volume.withDensity (chiPDF (β * (n - k.val : ℝ)) 1)) := fun k => by
      rw [← chiMeasure_eq_withDensity (hdeg k)]
      have := isProbabilityMeasure_chiMeasure (hdeg k).le one_pos
      infer_instance
    have hmeas : ∀ k : Fin n, Measurable (chiPDF (β * (n - k.val : ℝ)) 1) := fun k =>
      measurable_chiPDF _ _
    have hrew : (fun k : Fin n => chiMeasure (β * (n - k.val : ℝ)) 1) =
        fun k : Fin n => volume.withDensity (chiPDF (β * (n - k.val : ℝ)) 1) :=
      funext fun k => chiMeasure_eq_withDensity (hdeg k)
    rw [hrew]
    exact TauCeti.pi_withDensity (fun _ : Fin n => (volume : Measure ℝ)) hmeas
  rw [hermiteBetaTridiagonalLaw, hgauss, hchi]
  exact prod_withDensity (by fun_prop) (by fun_prop)

/-! ### Algebraic helpers for the Dumitriu–Edelman density factorization -/

/-- Gamma-product cancellation relating the Mehta–Selberg constant, Dirichlet constant, and chi
normalizations. -/
private theorem prod_gamma_mehta_cancellation {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    ((n + 1).factorial : ℝ) /
        (∏ j ∈ Finset.Icc 1 (n + 1),
          (Real.Gamma (1 + (j : ℝ) * β / 2) / Real.Gamma (1 + β / 2))) *
      (Real.Gamma (∑ _ : Fin (n + 1), β / 2) / ∏ _ : Fin (n + 1), Real.Gamma (β / 2)) =
      (∏ k : Fin n, Real.Gamma (β * (n - k.val : ℝ) / 2))⁻¹ := by
  have hGβ : Real.Gamma (β / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hterm : ∀ j ∈ Finset.Icc 1 (n + 1),
      Real.Gamma (1 + (j : ℝ) * β / 2) / Real.Gamma (1 + β / 2) =
        (j : ℝ) * Real.Gamma ((j : ℝ) * β / 2) / Real.Gamma (β / 2) := fun j hj => by
    have hjpos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hj).1
    rw [add_comm (1 : ℝ), Real.Gamma_add_one (by positivity),
      add_comm (1 : ℝ), Real.Gamma_add_one (by positivity)]
    field_simp [hGβ, hβ.ne']
  rw [Finset.prod_congr rfl hterm, Finset.prod_div_distrib, Finset.prod_mul_distrib]
  have hfac : ∏ j ∈ Finset.Icc 1 (n + 1), (j : ℝ) = ((n + 1).factorial : ℝ) := by
    have hnat : ∏ j ∈ Finset.Icc 1 (n + 1), j = (n + 1).factorial := by
      clear hβ hGβ hterm
      induction n with
      | zero => simp
      | succ m ih =>
          have hIcc : Finset.Icc 1 (m + 2) = insert (m + 2) (Finset.Icc 1 (m + 1)) := by
            ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hIcc, Finset.prod_insert (by simp), ih]
          exact (Nat.factorial_succ (m + 1)).symm
    rw [← Nat.cast_prod, hnat]
  have hIcc_split : ∏ j ∈ Finset.Icc 1 (n + 1), Real.Gamma ((j : ℝ) * β / 2) =
      Real.Gamma (((n + 1 : ℕ) : ℝ) * β / 2) *
        ∏ j ∈ Finset.Icc 1 n, Real.Gamma ((j : ℝ) * β / 2) := by
    have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.prod_insert (by simp)]
  have hbij : ∏ j ∈ Finset.Icc 1 n, Real.Gamma ((j : ℝ) * β / 2) =
      ∏ k : Fin n, Real.Gamma (β * (n - k.val : ℝ) / 2) := by
    refine Finset.prod_bij (fun j hj => ⟨n - j, by have := Finset.mem_Icc.mp hj; omega⟩)
      (fun _ _ => Finset.mem_univ _)
      (fun j₁ hj₁ j₂ hj₂ h => by
        have h1 := Finset.mem_Icc.mp hj₁
        have h2 := Finset.mem_Icc.mp hj₂
        have hv : n - j₁ = n - j₂ := congrArg Fin.val h
        omega)
      (fun k _ => ⟨n - k.val, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
        Fin.ext (by dsimp only; omega)⟩)
      (fun j hj => by
        have hj' := Finset.mem_Icc.mp hj
        congr 1
        have hcast : ((n - j : ℕ) : ℝ) = (n : ℝ) - (j : ℝ) := Nat.cast_sub hj'.2
        rw [hcast]; ring)
  have hsum : ∑ _ : Fin (n + 1), β / 2 = ((n + 1 : ℕ) : ℝ) * β / 2 := by
    simp [mul_div_assoc]
  have hconst : ∏ _ ∈ Finset.Icc 1 (n + 1), Real.Gamma (β / 2) =
      ∏ _ : Fin (n + 1), Real.Gamma (β / 2) := by
    simp
  have hfac_ne : ((n + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hGn_ne : Real.Gamma (((n + 1 : ℕ) : ℝ) * β / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hprod_ne : ∏ k : Fin n, Real.Gamma (β * (n - k.val : ℝ) / 2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ =>
      (Real.Gamma_pos_of_pos (mul_pos (mul_pos hβ (sub_pos.mpr (Nat.cast_lt.mpr k.isLt)))
        (by norm_num : (0 : ℝ) < 1 / 2) |>.trans_eq (by ring))).ne'
  have hGprod_ne : ∏ _ : Fin (n + 1), Real.Gamma (β / 2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun _ _ => hGβ
  rw [hfac, hIcc_split, hbij, hsum, hconst]
  field_simp [hfac_ne, hGn_ne, hprod_ne, hGprod_ne]

/-- Sum of `n - k.val` over `k : Fin n` equals `(n + 1) * n / 2` in `ℝ`. -/
private theorem sum_sub_fin_real (n : ℕ) :
    ∑ k : Fin n, ((n : ℝ) - (k.val : ℝ)) = ((n + 1 : ℝ) * n) / 2 := by
  have hnat : ∑ k : Fin n, (n - k.val) = n * (n + 1) / 2 := by
    induction n with
    | zero => simp
    | succ m ih =>
        rw [Fin.sum_univ_succ]
        have hstep : ∑ k : Fin m, (m + 1 - k.succ.val) = ∑ k : Fin m, (m - k.val) :=
          Finset.sum_congr rfl fun k _ => by simp
        rw [hstep, ih]
        simp only [Fin.val_zero, Nat.sub_zero]
        have heven : 2 ∣ m * (m + 1) := by
          rcases Nat.even_or_odd m with ⟨t, rfl⟩ | ⟨t, rfl⟩
          · exact ⟨t * (2 * t + 1), by ring⟩
          · exact ⟨(2 * t + 1) * (t + 1), by ring⟩
        obtain ⟨q, hq⟩ := heven
        have hq2 : (m + 1) * (m + 1 + 1) = 2 * ((m + 1) + q) := by linarith
        rw [hq, hq2, Nat.mul_div_cancel_left _ two_pos, Nat.mul_div_cancel_left _ two_pos]
  have hcast : (∑ k : Fin n, ((n - k.val : ℕ) : ℝ)) = ((n * (n + 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hterm : ∀ k : Fin n, ((n - k.val : ℕ) : ℝ) = (n : ℝ) - (k.val : ℝ) := fun k =>
    Nat.cast_sub k.isLt.le
  simp_rw [hterm] at hcast
  rw [hcast]
  have heven : 2 ∣ n * (n + 1) := by
    rcases Nat.even_or_odd n with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact ⟨t * (2 * t + 1), by ring⟩
    · exact ⟨(2 * t + 1) * (t + 1), by ring⟩
  obtain ⟨q, hq⟩ := heven
  have hqR : (n : ℝ) * ((n : ℝ) + 1) = 2 * (q : ℝ) := by exact_mod_cast hq
  rw [hq, Nat.mul_div_cancel_left _ two_pos]
  linarith

/-- Powers-of-2 and `π` cancellation in the Dumitriu–Edelman density identity. -/
private theorem dumitriu_edelman_const_2pi (β : ℝ) (n : ℕ) :
    (2 : ℝ) ^ n *
        (((1 / 2 : ℝ) ^ (-(((n + 1 : ℕ) : ℝ) / 2 + β * ((n + 1 : ℕ) : ℝ) *
          (((n + 1 : ℕ) : ℝ) - 1) / 4)) *
          (2 * Real.pi) ^ (((n + 1 : ℕ) : ℝ) / 2))⁻¹) =
      ((Real.sqrt (2 * Real.pi * 2))⁻¹) ^ (n + 1) *
        (2 : ℝ) ^ ((n : ℝ) - β * ((n + 1 : ℝ) * n) / 4) := by
  have hhalf : ((1 / 2 : ℝ) ^ (-(((n + 1 : ℕ) : ℝ) / 2 + β * ((n + 1 : ℕ) : ℝ) *
      (((n + 1 : ℕ) : ℝ) - 1) / 4)))⁻¹ =
      (2 : ℝ) ^ (-(((n + 1 : ℕ) : ℝ) / 2 + β * ((n + 1 : ℕ) : ℝ) *
        (((n + 1 : ℕ) : ℝ) - 1) / 4)) := by
    rw [one_div, Real.inv_rpow two_pos.le, inv_inv]
  have hsq : ((Real.sqrt (2 * Real.pi * 2))⁻¹) ^ (n + 1) =
      (2 : ℝ) ^ (-(((n + 1 : ℕ) : ℝ) / 2)) * (2 * Real.pi) ^ (-(((n + 1 : ℕ) : ℝ) / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity),
      ← Real.rpow_natCast _ (n + 1), ← Real.rpow_mul (by positivity),
      Real.mul_rpow (by positivity) two_pos.le, mul_comm]
    have hexp1 : -(1 / 2 : ℝ) * ((n + 1 : ℕ) : ℝ) = -(((n + 1 : ℕ) : ℝ) / 2) := by ring
    rw [hexp1]
  rw [mul_inv, hhalf, ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
    ← Real.rpow_natCast (2 : ℝ) n, hsq]
  have h2combine : (2 : ℝ) ^ (n : ℝ) *
      (2 : ℝ) ^ (-(((n + 1 : ℕ) : ℝ) / 2 + β * ((n + 1 : ℕ) : ℝ) *
        (((n + 1 : ℕ) : ℝ) - 1) / 4)) =
      (2 : ℝ) ^ (-(((n + 1 : ℕ) : ℝ) / 2)) *
        (2 : ℝ) ^ ((n : ℝ) - β * ((n + 1 : ℝ) * n) / 4) := by
    rw [← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
    congr 1; push_cast; ring
  calc (2 : ℝ) ^ (n : ℝ) *
        ((2 : ℝ) ^ (-(((n + 1 : ℕ) : ℝ) / 2 + β * ((n + 1 : ℕ) : ℝ) *
          (((n + 1 : ℕ) : ℝ) - 1) / 4)) *
          (2 * Real.pi) ^ (-(((n + 1 : ℕ) : ℝ) / 2)))
      = ((2 : ℝ) ^ (n : ℝ) *
          (2 : ℝ) ^ (-(((n + 1 : ℕ) : ℝ) / 2 + β * ((n + 1 : ℕ) : ℝ) *
            (((n + 1 : ℕ) : ℝ) - 1) / 4))) *
          (2 * Real.pi) ^ (-(((n + 1 : ℕ) : ℝ) / 2)) := by ring
    _ = ((2 : ℝ) ^ (-(((n + 1 : ℕ) : ℝ) / 2)) *
          (2 : ℝ) ^ ((n : ℝ) - β * ((n + 1 : ℝ) * n) / 4)) *
          (2 * Real.pi) ^ (-(((n + 1 : ℕ) : ℝ) / 2)) := by rw [h2combine]
    _ = _ := by ring

/-- Subdiagonal power identity relating `∏ k, b k ^ (β * (n - k) - 1)` to spectral weights and
the Vandermonde product. -/
private theorem dumitriu_edelman_subdiag_pow (β : ℝ) {n : ℕ}
    {p : (Fin (n + 1) → ℝ) × (Fin n → ℝ)} (hp : p ∈ jacobiDomain n) :
    ∏ k : Fin n, p.2 k ^ (β * (n - k.val : ℝ) - 1) =
      (∏ i : Fin (n + 1), jacobiSpectralWeight p.1 p.2 i ^ (β / 2)) *
        vandermondeProd (jacobiEigenvalues p.1 p.2) ^ β / ∏ j : Fin n, p.2 j := by
  have hb : ∀ j : Fin n, 0 < p.2 j := mem_jacobiDomain_iff.mp hp
  have hbne : ∀ j : Fin n, p.2 j ≠ 0 := fun j => (hb j).ne'
  have hq_pos : ∀ k : Fin (n + 1), 0 < jacobiSpectralWeight p.1 p.2 k :=
    jacobiSpectralWeight_pos hbne
  have hsplit : ∏ k : Fin n, p.2 k ^ (β * (n - k.val : ℝ) - 1) =
      (∏ k : Fin n, p.2 k ^ (n - k.val)) ^ β / ∏ j : Fin n, p.2 j := by
    rw [← Real.finsetProd_rpow _ _ (fun k _ => pow_nonneg (hb k).le _), div_eq_mul_inv,
      ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← Real.rpow_natCast (p.2 k) (n - k.val), ← Real.rpow_mul (hb k).le,
      Nat.cast_sub k.isLt.le, ← Real.rpow_neg_one (p.2 k), ← Real.rpow_add (hb k)]
    congr 1; ring
  have hvw := prod_pow_eq_prod_sqrt_jacobiSpectralWeight_mul_vandermonde (a := p.1) hb
  rw [← vandermondeProd_of_strictAnti (strictAnti_jacobiEigenvalues hbne)] at hvw
  rw [hsplit, hvw, Real.mul_rpow (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _)
    (vandermondeProd_nonneg _), ← Real.finsetProd_rpow _ _ (fun _ _ => Real.sqrt_nonneg _)]
  congr 2
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (hq_pos i).le]
  congr 1; ring

/-- Combining spectral-weight factors from the Jacobian and the Dirichlet chart density. -/
private theorem dumitriu_edelman_weight_factor (β : ℝ) {n : ℕ}
    {p : (Fin (n + 1) → ℝ) × (Fin n → ℝ)} (hp : p ∈ jacobiDomain n) :
    (∏ k : Fin (n + 1), jacobiSpectralWeight p.1 p.2 k) *
      ((∏ j : {i : Fin (n + 1) // i ≠ Fin.last n}, (jacobiSpectralChart n p).2 j ^ (β / 2 - 1)) *
        (1 - ∑ j : {i : Fin (n + 1) // i ≠ Fin.last n}, (jacobiSpectralChart n p).2 j) ^
          (β / 2 - 1)) =
      ∏ k : Fin (n + 1), jacobiSpectralWeight p.1 p.2 k ^ (β / 2) := by
  have hbne : ∀ j : Fin n, p.2 j ≠ 0 := fun j => (mem_jacobiDomain_iff.mp hp j).ne'
  have hq_pos : ∀ k : Fin (n + 1), 0 < jacobiSpectralWeight p.1 p.2 k :=
    jacobiSpectralWeight_pos hbne
  have hdir : (∏ j : {i : Fin (n + 1) // i ≠ Fin.last n},
        (jacobiSpectralChart n p).2 j ^ (β / 2 - 1)) *
      (1 - ∑ j : {i : Fin (n + 1) // i ≠ Fin.last n}, (jacobiSpectralChart n p).2 j) ^
        (β / 2 - 1) =
      ∏ k : Fin (n + 1), jacobiSpectralWeight p.1 p.2 k ^ (β / 2 - 1) := by
    rw [mul_comm, Fintype.prod_eq_mul_prod_subtype_ne _ (Fin.last n)]
    congr 1
    · have hlast := dirichletChart_jacobiSpectralChart_snd hp (Fin.last n)
      rw [dirichletChart_apply_self] at hlast
      rw [hlast]
    · refine Finset.prod_congr rfl fun j _ => ?_
      rw [jacobiSpectralChart_snd]
  rw [hdir, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  conv_lhs => arg 1; rw [← Real.rpow_one (jacobiSpectralWeight p.1 p.2 k)]
  rw [← Real.rpow_add (hq_pos k)]
  congr 1; ring

/-- Pointwise Dumitriu–Edelman density factorization on `jacobiDomain n`: multiplying the spectral
change-of-variables Jacobian by the ordered Gaussian beta (`c = 1 / 2`) and Dirichlet (`β / 2`)
chart densities reproduces the independent `N(0, 2)` / `χ_{β (n - k)}` tridiagonal density. -/
private theorem dumitriu_edelman_density_factorization {β : ℝ} (hβ : 0 < β) {n : ℕ}
    {p : (Fin (n + 1) → ℝ) × (Fin n → ℝ)} (hp : p ∈ jacobiDomain n) :
    (2 ^ n * (∏ k : Fin (n + 1), jacobiSpectralWeight p.1 p.2 k) / ∏ j : Fin n, p.2 j) *
      (gaussianBetaOrderedPDFReal β (1 / 2) (jacobiSpectralChart n p).1 *
        dirichletChartPDFReal (fun _ : Fin (n + 1) => β / 2) (Fin.last n)
          (jacobiSpectralChart n p).2) =
      (∏ i : Fin (n + 1), gaussianPDFReal 0 2 (p.1 i)) *
        ∏ k : Fin n, chiPDFReal (β * (n - k.val : ℝ)) 1 (p.2 k) := by
  have hb : ∀ j : Fin n, 0 < p.2 j := mem_jacobiDomain_iff.mp hp
  have hs : jacobiSpectralChart n p ∈ spectralDomain n := by
    rw [← jacobiSpectralChart_image_domain n]; exact ⟨p, hp, rfl⟩
  obtain ⟨hlam_anti, hq'_mem⟩ := mem_spectralDomain_iff.mp hs
  have hgauss : ∏ i : Fin (n + 1), gaussianPDFReal 0 2 (p.1 i) =
      ((Real.sqrt (2 * Real.pi * 2))⁻¹) ^ (n + 1) *
        Real.exp (-(1 / 4 : ℝ) * ∑ i : Fin (n + 1), p.1 i ^ 2) := by
    have hpt : ∀ i : Fin (n + 1), gaussianPDFReal 0 2 (p.1 i) =
        (Real.sqrt (2 * Real.pi * 2))⁻¹ * Real.exp (-(1 / 4 : ℝ) * p.1 i ^ 2) := fun i => by
      rw [gaussianPDFReal_def]
      simp only [NNReal.coe_ofNat, sub_zero]
      congr 2; ring
    simp_rw [hpt, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin, ← Real.exp_sum,
      ← Finset.mul_sum]
  have hchi : ∏ k : Fin n, chiPDFReal (β * (n - k.val : ℝ)) 1 (p.2 k) =
      (2 : ℝ) ^ ((n : ℝ) - β * ((n + 1 : ℝ) * n) / 4) *
        (∏ k : Fin n, Real.Gamma (β * (n - k.val : ℝ) / 2))⁻¹ *
        (∏ k : Fin n, p.2 k ^ (β * (n - k.val : ℝ) - 1)) *
        Real.exp (-(1 / 2 : ℝ) * ∑ k : Fin n, p.2 k ^ 2) := by
    have hpt : ∀ k : Fin n, chiPDFReal (β * (n - k.val : ℝ)) 1 (p.2 k) =
        (2 : ℝ) ^ (1 - β * (n - k.val : ℝ) / 2) *
          (Real.Gamma (β * (n - k.val : ℝ) / 2))⁻¹ *
          p.2 k ^ (β * (n - k.val : ℝ) - 1) *
          Real.exp (-(1 / 2 : ℝ) * p.2 k ^ 2) := fun k => by
      have hdeg : 0 < β * (n - k.val : ℝ) := mul_pos hβ (sub_pos.mpr (Nat.cast_lt.mpr k.isLt))
      rw [chiPDFReal_of_pos hdeg one_pos (hb k)]
      simp only [div_one]
      rw [div_eq_mul_inv]
      congr 2; ring
    simp_rw [hpt, Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← Real.exp_sum,
      ← Finset.mul_sum, ← Real.rpow_sum_of_pos two_pos]
    congr 3
    have hsum : ∑ k : Fin n, (1 - β * ((n : ℝ) - (k.val : ℝ)) / 2) =
        (n : ℝ) - β * ((n + 1 : ℝ) * n) / 4 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]
      simp_rw [mul_div_assoc, ← Finset.mul_sum, ← Finset.sum_div, sum_sub_fin_real]
      ring
    rw [hsum]
  have hexp : Real.exp (-(1 / 4 : ℝ) * ∑ i : Fin (n + 1), p.1 i ^ 2) *
      Real.exp (-(1 / 2 : ℝ) * ∑ k : Fin n, p.2 k ^ 2) =
      Real.exp (-((1 / 2 : ℝ) / 2) * ∑ i : Fin (n + 1), jacobiEigenvalues p.1 p.2 i ^ 2) := by
    rw [← Real.exp_add, sum_jacobiEigenvalues_sq]
    congr 1; ring
  rw [hgauss, hchi, gaussianBetaOrderedPDFReal_of_strictAnti _ _ hlam_anti,
    gaussianBetaPDFReal_of_pos hβ (by norm_num : (0 : ℝ) < 1 / 2),
    dirichletChartPDFReal_of_mem _ hq'_mem, jacobiSpectralChart_fst,
    gaussianBetaNormConst_def, mul_inv]
  set C2pi := (1 / 2 : ℝ) ^ (-(((n + 1 : ℕ) : ℝ) / 2 + β * ((n + 1 : ℕ) : ℝ) *
      (((n + 1 : ℕ) : ℝ) - 1) / 4)) * (2 * Real.pi) ^ (((n + 1 : ℕ) : ℝ) / 2)
  set CGam := ∏ j ∈ Finset.Icc 1 (n + 1),
      (Real.Gamma (1 + (j : ℝ) * β / 2) / Real.Gamma (1 + β / 2))
  set CDir := Real.Gamma (∑ _ : Fin (n + 1), β / 2) / ∏ _ : Fin (n + 1), Real.Gamma (β / 2)
  set Qdir := (∏ j : {i : Fin (n + 1) // i ≠ Fin.last n},
      (jacobiSpectralChart n p).2 j ^ (β / 2 - 1)) *
    (1 - ∑ j : {i : Fin (n + 1) // i ≠ Fin.last n},
      (jacobiSpectralChart n p).2 j) ^ (β / 2 - 1)
  calc (2 ^ n * (∏ k : Fin (n + 1), jacobiSpectralWeight p.1 p.2 k) / ∏ j : Fin n, p.2 j) *
        (((n + 1).factorial : ℝ) * (C2pi⁻¹ * CGam⁻¹ *
          Real.exp (-((1 / 2 : ℝ) / 2) * ∑ i : Fin (n + 1), jacobiEigenvalues p.1 p.2 i ^ 2) *
          vandermondeProd (jacobiEigenvalues p.1 p.2) ^ β) *
          (CDir * (∏ j : {i : Fin (n + 1) // i ≠ Fin.last n},
              (jacobiSpectralChart n p).2 j ^ (β / 2 - 1)) *
            (1 - ∑ j : {i : Fin (n + 1) // i ≠ Fin.last n},
              (jacobiSpectralChart n p).2 j) ^ (β / 2 - 1)))
      = (2 ^ n * C2pi⁻¹) * (((n + 1).factorial : ℝ) / CGam * CDir) *
          (((∏ k : Fin (n + 1), jacobiSpectralWeight p.1 p.2 k) * Qdir) *
            vandermondeProd (jacobiEigenvalues p.1 p.2) ^ β / ∏ j : Fin n, p.2 j) *
          Real.exp (-((1 / 2 : ℝ) / 2) * ∑ i : Fin (n + 1), jacobiEigenvalues p.1 p.2 i ^ 2) := by
        dsimp only [Qdir]; ring
    _ = (((Real.sqrt (2 * Real.pi * 2))⁻¹) ^ (n + 1) *
          (2 : ℝ) ^ ((n : ℝ) - β * ((n + 1 : ℝ) * n) / 4)) *
          (∏ k : Fin n, Real.Gamma (β * (n - k.val : ℝ) / 2))⁻¹ *
          (∏ k : Fin n, p.2 k ^ (β * (n - k.val : ℝ) - 1)) *
          (Real.exp (-(1 / 4 : ℝ) * ∑ i : Fin (n + 1), p.1 i ^ 2) *
            Real.exp (-(1 / 2 : ℝ) * ∑ k : Fin n, p.2 k ^ 2)) := by
        rw [dumitriu_edelman_const_2pi β n, prod_gamma_mehta_cancellation hβ n,
          dumitriu_edelman_weight_factor β hp, ← dumitriu_edelman_subdiag_pow β hp, ← hexp]
    _ = _ := by ring

/-- **Dumitriu–Edelman chart theorem**: pushing `hermiteBetaTridiagonalLaw β n` forward along
`jacobiSpectralChart n` produces the product of `gaussianBetaOrderedMeasure β (1 / 2) (n + 1)`
and the Dirichlet chart density `dirichletChartPDF (fun _ => β / 2) (Fin.last n)`. -/
theorem map_jacobiSpectralChart_hermiteBetaTridiagonalLaw {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    (hermiteBetaTridiagonalLaw β n).map (jacobiSpectralChart n) =
      (gaussianBetaOrderedMeasure β (1 / 2) (n + 1)).prod
        (volume.withDensity (dirichletChartPDF (fun _ : Fin (n + 1) => β / 2) (Fin.last n))) := by
  let h : (Fin (n + 1) → ℝ) × (Fin n → ℝ) → ℝ≥0∞ := fun p =>
    (∏ i : Fin (n + 1), gaussianPDF 0 2 (p.1 i)) *
      ∏ k : Fin n, chiPDF (β * (n - k.val : ℝ)) 1 (p.2 k)
  let g : (Fin (n + 1) → ℝ) × ({i : Fin (n + 1) // i ≠ Fin.last n} → ℝ) → ℝ≥0∞ := fun s =>
    gaussianBetaOrderedPDF β (1 / 2) s.1 *
      dirichletChartPDF (fun _ : Fin (n + 1) => β / 2) (Fin.last n) s.2
  let jac : (Fin (n + 1) → ℝ) × (Fin n → ℝ) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (2 ^ n * (∏ k : Fin (n + 1), jacobiSpectralWeight p.1 p.2 k) /
      ∏ j : Fin n, p.2 j)
  have hLHS : hermiteBetaTridiagonalLaw β n =
      ((volume.prod volume).restrict (jacobiDomain n)).withDensity h := by
    rw [hermiteBetaTridiagonalLaw_eq_withDensity hβ n,
      ← withDensity_indicator (measurableSet_jacobiDomain n)]
    congr 1
    funext p
    by_cases hp : p ∈ jacobiDomain n
    · rw [Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp]
      obtain ⟨k, hk⟩ := not_forall.mp (mt mem_jacobiDomain_iff.mpr hp)
      have hzero : chiPDF (β * (n - k.val : ℝ)) 1 (p.2 k) = 0 :=
        chiPDF_of_nonpos (le_of_not_gt hk)
      rw [Finset.prod_eq_zero (Finset.mem_univ k) hzero, mul_zero]
  have hRHS : (gaussianBetaOrderedMeasure β (1 / 2) (n + 1)).prod
        (volume.withDensity (dirichletChartPDF (fun _ : Fin (n + 1) => β / 2) (Fin.last n))) =
      ((volume.prod volume).restrict (spectralDomain n)).withDensity g := by
    rw [gaussianBetaOrderedMeasure_eq_withDensity,
      prod_withDensity (measurable_gaussianBetaOrderedPDF _ _ _)
        (measurable_dirichletChartPDF _ _),
      ← withDensity_indicator (measurableSet_spectralDomain n)]
    congr 1
    funext s
    by_cases hs : s ∈ spectralDomain n
    · rw [Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs]
      rw [mem_spectralDomain_iff, not_and_or] at hs
      rcases hs with h1 | h2
      · rw [gaussianBetaOrderedPDF_of_not_strictAnti _ _ h1, zero_mul]
      · rw [dirichletChartPDF_of_notMem _ h2, mul_zero]
  have hmeas_jac : Measurable jac := by
    unfold jac
    refine Measurable.ennreal_ofReal (Measurable.div (Measurable.const_mul ?_ _) ?_)
    · exact Finset.measurable_prod _ fun k _ =>
        (measurable_pi_apply k).comp measurable_jacobiSpectralWeight
    · exact Finset.measurable_prod _ fun j _ => (measurable_pi_apply j).comp measurable_snd
  have hmeas_g : Measurable g :=
    ((measurable_gaussianBetaOrderedPDF _ _ _).comp measurable_fst).mul
      ((measurable_dirichletChartPDF _ _).comp measurable_snd)
  rw [hLHS, hRHS]
  refine Measure.map_withDensity_eq_withDensity (measurable_jacobiSpectralChart n) hmeas_jac
    hmeas_g (map_jacobiSpectralChart_withDensity n) ?_
  filter_upwards [ae_restrict_mem (measurableSet_jacobiDomain n)] with p hp
  have hb : ∀ j : Fin n, 0 < p.2 j := mem_jacobiDomain_iff.mp hp
  have hjac_nn : 0 ≤ 2 ^ n * (∏ k : Fin (n + 1), jacobiSpectralWeight p.1 p.2 k) /
      ∏ j : Fin n, p.2 j :=
    div_nonneg (mul_nonneg (by positivity) (Finset.prod_nonneg fun k _ =>
      (jacobiSpectralWeight_pos (fun j => (hb j).ne') k).le))
      (Finset.prod_nonneg fun j _ => (hb j).le)
  have hg1_nn : 0 ≤ gaussianBetaOrderedPDFReal β (1 / 2) (jacobiSpectralChart n p).1 :=
    gaussianBetaOrderedPDFReal_nonneg _ _ _
  have hprod_g : ∏ i : Fin (n + 1), gaussianPDF 0 2 (p.1 i) =
      ENNReal.ofReal (∏ i : Fin (n + 1), gaussianPDFReal 0 2 (p.1 i)) := by
    simp only [gaussianPDF_def]
    exact (ENNReal.ofReal_prod_of_nonneg fun i _ => gaussianPDFReal_nonneg 0 2 (p.1 i)).symm
  have hprod_c : ∏ k : Fin n, chiPDF (β * (n - k.val : ℝ)) 1 (p.2 k) =
      ENNReal.ofReal (∏ k : Fin n, chiPDFReal (β * (n - k.val : ℝ)) 1 (p.2 k)) := by
    simp_rw [chiPDF_eq_ofReal]
    exact (ENNReal.ofReal_prod_of_nonneg fun k _ => chiPDFReal_nonneg _ _ _).symm
  dsimp only [jac, g, h]
  rw [gaussianBetaOrderedPDF_eq_ofReal, dirichletChartPDF_eq_ofReal,
    ← ENNReal.ofReal_mul hg1_nn, ← ENNReal.ofReal_mul hjac_nn,
    hprod_g, hprod_c,
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => gaussianPDFReal_nonneg _ _ _),
    dumitriu_edelman_density_factorization hβ hp]

/-! ### Exact normalization and the Mehta–Selberg integral -/

/-- The ordered Gaussian beta density integrates to `1` for all `n : ℕ`, `β > 0`, and `c > 0`. -/
theorem lintegral_gaussianBetaOrderedPDF_eq_one {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (n : ℕ) :
    ∫⁻ x : Fin n → ℝ, gaussianBetaOrderedPDF β c x = 1 := by
  cases n with
  | zero =>
      have hconst : ∀ x : Fin 0 → ℝ, gaussianBetaOrderedPDF β c x = 1 := fun x => by
        rw [gaussianBetaOrderedPDF_eq_ofReal,
          gaussianBetaOrderedPDFReal_of_strictAnti β c (fun i => i.elim0),
          gaussianBetaPDFReal_of_pos hβ hc]
        simp
      simp_rw [hconst, lintegral_const, one_mul]
      change (Measure.pi fun _ : Fin 0 => (volume : Measure ℝ)) Set.univ = 1
      rw [Measure.pi_univ]
      simp
  | succ m =>
      have hhalf : ∫⁻ x : Fin (m + 1) → ℝ, gaussianBetaOrderedPDF β (1 / 2) x = 1 := by
        have := isProbabilityMeasure_hermiteBetaTridiagonalLaw hβ.le m
        have huniv := congrArg (fun μ => μ Set.univ)
          (map_jacobiSpectralChart_hermiteBetaTridiagonalLaw hβ m)
        rw [Measure.map_apply (measurable_jacobiSpectralChart m) MeasurableSet.univ,
          Set.preimage_univ, measure_univ, ← Set.univ_prod_univ, Measure.prod_prod,
          gaussianBetaOrderedMeasure_eq_withDensity, withDensity_apply _ MeasurableSet.univ,
          withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, Measure.restrict_univ,
          lintegral_dirichletChartPDF_eq_one (fun _ => half_pos hβ) (Fin.last m), mul_one] at huniv
        exact huniv.symm
      let s : ℝ := (Real.sqrt (2 * c))⁻¹
      have hs : 0 < s := inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))
      have hc_eq : (1 / 2 : ℝ) / s ^ 2 = c := by
        dsimp only [s]
        rw [inv_pow, Real.sq_sqrt (by positivity), div_inv_eq_mul]; ring
      have hmap := congrArg (fun μ => μ Set.univ)
        (map_smul_gaussianBetaOrderedMeasure hβ (by norm_num : (0 : ℝ) < 1 / 2) hs (m + 1))
      rw [hc_eq, Measure.map_apply (continuous_const_smul s).measurable MeasurableSet.univ,
        Set.preimage_univ, gaussianBetaOrderedMeasure_eq_withDensity,
        gaussianBetaOrderedMeasure_eq_withDensity, withDensity_apply _ MeasurableSet.univ,
        withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hhalf] at hmap
      exact hmap.symm

/-- For `β > 0` and `c > 0`, `gaussianBetaOrderedMeasure β c n` is a probability measure. -/
theorem isProbabilityMeasure_gaussianBetaOrderedMeasure {β c : ℝ} (hβ : 0 < β) (hc : 0 < c)
    (n : ℕ) : IsProbabilityMeasure (gaussianBetaOrderedMeasure β c n) := by
  constructor
  rw [gaussianBetaOrderedMeasure_eq_withDensity, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact lintegral_gaussianBetaOrderedPDF_eq_one hβ hc n

/-- The complement of the injective tuples `{x : Fin n → ℝ | Function.Injective x}` has Lebesgue
measure zero. -/
private theorem volume_compl_injective_eq_zero (n : ℕ) :
    (volume : Measure (Fin n → ℝ)) {x : Fin n → ℝ | Function.Injective x}ᶜ = 0 := by
  have hsub : {x : Fin n → ℝ | Function.Injective x}ᶜ ⊆
      ⋃ i : Fin n, ⋃ j ∈ Finset.Ioi i, {x : Fin n → ℝ | x i = x j} := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Function.Injective, not_forall] at hx
    obtain ⟨i, j, hij, hne⟩ := hx
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨i, j, Finset.mem_Ioi.mpr hlt, hij⟩
    · exact ⟨j, i, Finset.mem_Ioi.mpr hgt, hij.symm⟩
  refine measure_mono_null hsub (measure_iUnion_null fun i => measure_iUnion_null fun j =>
    measure_iUnion_null fun hj => ?_)
  have hne : i ≠ j := (Finset.mem_Ioi.mp hj).ne
  let L : Submodule ℝ (Fin n → ℝ) :=
    LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i -
      LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j)
  have hLset : {x : Fin n → ℝ | x i = x j} = (L : Set (Fin n → ℝ)) := by
    ext x
    simp [L, sub_eq_zero]
  have hLne : L ≠ ⊤ := by
    intro htop
    have hmem : Pi.single i (1 : ℝ) ∈ L := by rw [htop]; trivial
    simp [L, Pi.single_eq_same, Pi.single_eq_of_ne hne.symm] at hmem
  rw [hLset]
  exact Measure.addHaar_submodule volume L hLne

/-- Pairwise disjointness of the Weyl chambers `{x : Fin n → ℝ | StrictAnti (x ∘ σ)}`. -/
private theorem pairwise_disjoint_weylChambers (n : ℕ) :
    Pairwise fun σ τ : Equiv.Perm (Fin n) =>
      Disjoint {x : Fin n → ℝ | StrictAnti (x ∘ σ)} {x : Fin n → ℝ | StrictAnti (x ∘ τ)} := by
  intro σ τ hne
  rw [Set.disjoint_left]
  intro x hσ hτ
  have hmono : StrictMono (τ.trans σ.symm) := fun i j hij => by
    have hlt : (x ∘ σ) (σ.symm (τ j)) < (x ∘ σ) (σ.symm (τ i)) := by simpa using hτ hij
    exact hσ.lt_iff_gt.mp hlt
  have he : (⟨τ.trans σ.symm, fun {a b} => hmono.le_iff_le⟩ : Fin n ≃o Fin n) = OrderIso.refl _ :=
    Subsingleton.elim _ _
  exact hne (Equiv.ext fun k => by
    have hk := congrArg (fun f : Fin n ≃o Fin n => σ (f k)) he
    simpa using hk.symm)

/-- **Mehta–Selberg normalization**: the unordered Gaussian beta density integrates to `1` for all
`n : ℕ`, `β > 0`, and `c > 0`. -/
theorem lintegral_gaussianBetaPDF_eq_one {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (n : ℕ) :
    ∫⁻ x : Fin n → ℝ, gaussianBetaPDF β c x = 1 := by
  let W : Equiv.Perm (Fin n) → Set (Fin n → ℝ) := fun σ => {x | StrictAnti (x ∘ σ)}
  have hWmeas : ∀ σ, MeasurableSet (W σ) := fun σ => by
    have hpre : W σ = (fun x : Fin n → ℝ => fun i => x (σ i)) ⁻¹' {x | StrictAnti x} := rfl
    rw [hpre]
    exact ((isOpen_strictAnti_fin n).preimage
      (continuous_pi fun i => continuous_apply (σ i))).measurableSet
  have hunion : (⋃ σ : Equiv.Perm (Fin n), W σ) = {x : Fin n → ℝ | Function.Injective x} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, W]
    constructor
    · rintro ⟨σ, hσ⟩ i j hij
      exact σ.symm.injective (hσ.injective (by simpa using hij))
    · intro hx
      refine ⟨Tuple.sortDesc x, (Tuple.antitone_sortDesc x).strictAnti_of_injective ?_⟩
      exact hx.comp (Tuple.sortDesc x).injective
  have hae : (⋃ σ : Equiv.Perm (Fin n), W σ) =ᵐ[volume] (Set.univ : Set (Fin n → ℝ)) := by
    rw [hunion, ae_eq_univ]
    exact volume_compl_injective_eq_zero n
  have hperm_int : ∀ σ : Equiv.Perm (Fin n),
      ∫⁻ x in W σ, gaussianBetaPDF β c x =
        ∫⁻ x in {x : Fin n → ℝ | StrictAnti x}, gaussianBetaPDF β c x := fun σ => by
    let e : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) := MeasurableEquiv.piCongrLeft (fun _ => ℝ) σ.symm
    have he : (e : (Fin n → ℝ) → (Fin n → ℝ)) = fun x => x ∘ σ := by
      funext x i; simp [e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
    have hmp : MeasurePreserving e volume volume :=
      measurePreserving_piCongrLeft (fun _ : Fin n => (volume : Measure ℝ)) σ.symm
    have hpre : W σ = e ⁻¹' {x : Fin n → ℝ | StrictAnti x} := by
      ext x; simp [W, he]
    have hcomp : ∀ x, gaussianBetaPDF β c x = gaussianBetaPDF β c (e x) := fun x => by
      rw [he, gaussianBetaPDF_comp_perm]
    rw [hpre]
    calc ∫⁻ x in e ⁻¹' {x | StrictAnti x}, gaussianBetaPDF β c x
        = ∫⁻ x in e ⁻¹' {x | StrictAnti x}, gaussianBetaPDF β c (e x) :=
          setLIntegral_congr_fun (e.measurable (isOpen_strictAnti_fin n).measurableSet)
            fun x _ => hcomp x
      _ = ∫⁻ x in {x | StrictAnti x}, gaussianBetaPDF β c x :=
          hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding _ _
  have hord : (n.factorial : ℝ≥0∞) *
      ∫⁻ x in {x : Fin n → ℝ | StrictAnti x}, gaussianBetaPDF β c x = 1 := by
    rw [← lintegral_gaussianBetaOrderedPDF_eq_one hβ hc n,
      ← lintegral_const_mul _ (measurable_gaussianBetaPDF β c n),
      ← lintegral_indicator (isOpen_strictAnti_fin n).measurableSet]
    refine lintegral_congr fun x => ?_
    by_cases hx : StrictAnti x
    · rw [Set.indicator_of_mem hx, gaussianBetaOrderedPDF_eq_ofReal,
        gaussianBetaOrderedPDFReal_of_strictAnti β c hx, gaussianBetaPDF_eq_ofReal,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    · rw [Set.indicator_of_notMem hx, gaussianBetaOrderedPDF_of_not_strictAnti β c hx]
  calc ∫⁻ x : Fin n → ℝ, gaussianBetaPDF β c x
      = ∫⁻ x in (Set.univ : Set (Fin n → ℝ)), gaussianBetaPDF β c x := by rw [setLIntegral_univ]
    _ = ∫⁻ x in ⋃ σ : Equiv.Perm (Fin n), W σ, gaussianBetaPDF β c x :=
        setLIntegral_congr hae.symm
    _ = ∑' σ : Equiv.Perm (Fin n), ∫⁻ x in W σ, gaussianBetaPDF β c x :=
        lintegral_iUnion hWmeas (pairwise_disjoint_weylChambers n) _
    _ = ∑ σ : Equiv.Perm (Fin n), ∫⁻ x in W σ, gaussianBetaPDF β c x := tsum_fintype _
    _ = ∑ _σ : Equiv.Perm (Fin n),
          ∫⁻ x in {x : Fin n → ℝ | StrictAnti x}, gaussianBetaPDF β c x :=
        Finset.sum_congr rfl fun σ _ => hperm_int σ
    _ = (n.factorial : ℝ≥0∞) *
          ∫⁻ x in {x : Fin n → ℝ | StrictAnti x}, gaussianBetaPDF β c x := by
        simp [Fintype.card_perm]
    _ = 1 := hord

/-- For `β > 0` and `c > 0`, `gaussianBetaMeasure β c n` is a probability measure. -/
theorem isProbabilityMeasure_gaussianBetaMeasure {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (n : ℕ) :
    IsProbabilityMeasure (gaussianBetaMeasure β c n) := by
  constructor
  rw [gaussianBetaMeasure_eq_withDensity, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact lintegral_gaussianBetaPDF_eq_one hβ hc n

/-- The real Gaussian beta density is Lebesgue integrable for `β > 0` and `c > 0`. -/
theorem integrable_gaussianBetaPDFReal {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (n : ℕ) :
    Integrable (gaussianBetaPDFReal β c (n := n)) := by
  refine ⟨(measurable_gaussianBetaPDFReal β c n).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (gaussianBetaPDFReal_nonneg β c))]
  simpa only [← gaussianBetaPDF_eq_ofReal, lintegral_gaussianBetaPDF_eq_one hβ hc n] using
    (ENNReal.one_lt_top : (1 : ℝ≥0∞) < ∞)

/-- **Mehta–Selberg integral**: for every `n : ℕ`, `β > 0`, and `c > 0`,
`∫ x : Fin n → ℝ, exp (-(c / 2) * ∑ i, x i ^ 2) * (∏ i < j, |x i - x j|) ^ β =
  gaussianBetaNormConst β c n`. -/
theorem integral_exp_mul_vandermondeProd_rpow {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (n : ℕ) :
    ∫ x : Fin n → ℝ,
        Real.exp (-(c / 2) * ∑ i : Fin n, x i ^ 2) * vandermondeProd x ^ β =
      gaussianBetaNormConst β c n := by
  have hZpos := gaussianBetaNormConst_pos hβ hc n
  have hint : ∫ x : Fin n → ℝ, gaussianBetaPDFReal β c x = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (gaussianBetaPDFReal_nonneg β c))
      (measurable_gaussianBetaPDFReal β c n).aestronglyMeasurable]
    simp_rw [← gaussianBetaPDF_eq_ofReal]
    rw [lintegral_gaussianBetaPDF_eq_one hβ hc n, ENNReal.toReal_one]
  have heq : (fun x : Fin n → ℝ =>
      Real.exp (-(c / 2) * ∑ i : Fin n, x i ^ 2) * vandermondeProd x ^ β) =
      fun x => gaussianBetaNormConst β c n * gaussianBetaPDFReal β c x := by
    funext x
    rw [gaussianBetaPDFReal_of_pos hβ hc]
    field_simp [hZpos.ne']
  rw [heq, integral_const_mul, hint, mul_one]

/-- Concrete `n = 1` specialization: pushing `gaussianBetaMeasure β c 1` along `x ↦ x 0` gives
the centered Gaussian `N(0, c⁻¹)`. -/
theorem gaussianBetaMeasure_one_eq_gaussianReal {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    (gaussianBetaMeasure β c 1).map (fun x : Fin 1 → ℝ => x 0) =
      gaussianReal 0 ⟨c⁻¹, inv_nonneg.mpr hc.le⟩ := by
  set v : NNReal := ⟨c⁻¹, inv_nonneg.mpr hc.le⟩
  have hv : v ≠ 0 := NNReal.coe_ne_zero.mp (inv_ne_zero hc.ne')
  let e : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique (Fin 1) ℝ
  have he : (e : (Fin 1 → ℝ) → ℝ) = fun x => x 0 := rfl
  have hmp : (volume : Measure (Fin 1 → ℝ)).map e = volume :=
    (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)).map_eq
  rw [gaussianBetaMeasure_eq_withDensity, ← he, MeasurableEquiv.map_withDensity, hmp,
    gaussianReal_of_var_ne_zero 0 hv]
  congr 1
  funext t
  rw [gaussianBetaPDF_eq_ofReal, gaussianBetaPDFReal_of_pos hβ hc, gaussianPDF_def,
    gaussianPDFReal_def, gaussianBetaNormConst_one hβ hc]
  have ht : e.symm t 0 = t := by simp [e]
  have hvcoe : (v : ℝ) = c⁻¹ := rfl
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, ht,
    vandermondeProd_one, Real.one_rpow, mul_one, sub_zero, hvcoe]
  congr 3
  field_simp [hc.ne']

/-! ### Dumitriu–Edelman joint spectral law and independence -/

/-- Almost surely under `hermiteBetaTridiagonalLaw β n` (`β > 0`), all subdiagonal entries are
strictly positive. -/
private theorem ae_mem_jacobiDomain_hermiteBetaTridiagonalLaw {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    ∀ᵐ p ∂hermiteBetaTridiagonalLaw β n, p ∈ jacobiDomain n := by
  rw [hermiteBetaTridiagonalLaw_eq_withDensity hβ n, ae_withDensity_iff (by fun_prop)]
  refine ae_of_all _ fun p hp => ?_
  by_contra hnot
  obtain ⟨k, hk⟩ := not_forall.mp (mt mem_jacobiDomain_iff.mpr hnot)
  have hzero : chiPDF (β * (n - k.val : ℝ)) 1 (p.2 k) = 0 := chiPDF_of_nonpos (le_of_not_gt hk)
  exact hp (by rw [Finset.prod_eq_zero (Finset.mem_univ k) hzero, mul_zero])

/-- **Dumitriu–Edelman joint spectral law** (at canonical scaling `c = 1 / 2`): for the
`(n + 1) × (n + 1)` symmetric tridiagonal matrix with independent `N(0, 2)` diagonal entries and
`χ_{β (n - k)}` subdiagonal entries, the ordered eigenvalues and the spectral weight vector are
distributed as `gaussianBetaOrderedMeasure β (1 / 2) (n + 1)` times
`dirichletMeasure (fun _ => β / 2)`. -/
theorem map_jacobiSpectral_hermiteBetaTridiagonalLaw {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    (hermiteBetaTridiagonalLaw β n).map
        (fun p => (jacobiEigenvalues p.1 p.2,
          (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (jacobiSpectralWeight p.1 p.2))) =
      (gaussianBetaOrderedMeasure β (1 / 2) (n + 1)).prod
        (dirichletMeasure fun _ : Fin (n + 1) => β / 2) := by
  have := isProbabilityMeasure_gaussianBetaOrderedMeasure hβ (by norm_num : (0 : ℝ) < 1 / 2) (n + 1)
  have : IsProbabilityMeasure
      (volume.withDensity (dirichletChartPDF (fun _ : Fin (n + 1) => β / 2) (Fin.last n))) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact lintegral_dirichletChartPDF_eq_one (fun _ => half_pos hβ) (Fin.last n)
  have hae : (fun p => (jacobiEigenvalues p.1 p.2,
        (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (jacobiSpectralWeight p.1 p.2))) =ᵐ[
        hermiteBetaTridiagonalLaw β n]
      Prod.map id (dirichletChart (Fin.last n)) ∘ jacobiSpectralChart n := by
    filter_upwards [ae_mem_jacobiDomain_hermiteBetaTridiagonalLaw hβ n] with p hp
    refine Prod.ext (jacobiSpectralChart_fst n p).symm ?_
    ext k
    exact (dirichletChart_jacobiSpectralChart_snd hp k).symm
  rw [Measure.map_congr hae,
    ← Measure.map_map (measurable_id.prodMap measurable_dirichletChart)
      (measurable_jacobiSpectralChart n),
    map_jacobiSpectralChart_hermiteBetaTridiagonalLaw hβ n,
    ← Measure.map_prod_map _ _ measurable_id measurable_dirichletChart,
    Measure.map_id,
    dirichletMeasure_eq_map_withDensity_dirichletChartPDF (fun _ => half_pos hβ) (Fin.last n)]

/-- **Dumitriu–Edelman joint spectral law at arbitrary quadratic confinement `c > 0`**: rescaling
the tridiagonal matrix by `(√(2 * c))⁻¹` gives ordered eigenvalues distributed as
`gaussianBetaOrderedMeasure β c (n + 1)` and independent `Dirichlet(β / 2, …, β / 2)` spectral
weights. -/
theorem map_jacobiSpectral_smul_hermiteBetaTridiagonalLaw {β c : ℝ} (hβ : 0 < β) (hc : 0 < c)
    (n : ℕ) :
    let s : ℝ := (Real.sqrt (2 * c))⁻¹
    (hermiteBetaTridiagonalLaw β n).map
        (fun p => (jacobiEigenvalues (s • p.1) (s • p.2),
          (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (jacobiSpectralWeight (s • p.1) (s • p.2)))) =
      (gaussianBetaOrderedMeasure β c (n + 1)).prod
        (dirichletMeasure fun _ : Fin (n + 1) => β / 2) := by
  intro s
  have hs : 0 < s := inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  have hc_eq : (1 / 2 : ℝ) / s ^ 2 = c := by
    dsimp only [s]
    rw [inv_pow, Real.sq_sqrt (by positivity), div_inv_eq_mul]; ring
  have := isProbabilityMeasure_gaussianBetaOrderedMeasure hβ (by norm_num : (0 : ℝ) < 1 / 2) (n + 1)
  have := isProbabilityMeasure_dirichletMeasure (a := fun _ : Fin (n + 1) => β / 2)
    (fun _ => half_pos hβ)
  have hae : (fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) =>
        (jacobiEigenvalues (s • p.1) (s • p.2),
          (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (jacobiSpectralWeight (s • p.1) (s • p.2))))
      =ᵐ[hermiteBetaTridiagonalLaw β n]
      Prod.map (fun x => s • x) id ∘
        fun p => (jacobiEigenvalues p.1 p.2,
          (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (jacobiSpectralWeight p.1 p.2)) := by
    filter_upwards [ae_mem_jacobiDomain_hermiteBetaTridiagonalLaw hβ n] with p hp
    have hbne : ∀ j, p.2 j ≠ 0 := fun j => (mem_jacobiDomain_iff.mp hp j).ne'
    refine Prod.ext (jacobiEigenvalues_smul hs.le p.1 p.2) ?_
    ext k
    exact congrFun (jacobiSpectralWeight_smul hs hbne) k
  have hmeas_base : Measurable (fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) =>
      (jacobiEigenvalues p.1 p.2,
        (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (jacobiSpectralWeight p.1 p.2))) :=
    measurable_jacobiEigenvalues.prodMk
      ((EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.measurable.comp
        measurable_jacobiSpectralWeight)
  rw [Measure.map_congr hae,
    ← Measure.map_map ((continuous_const_smul s).measurable.prodMap measurable_id) hmeas_base,
    map_jacobiSpectral_hermiteBetaTridiagonalLaw hβ n,
    ← Measure.map_prod_map _ _ (continuous_const_smul s).measurable measurable_id,
    Measure.map_id,
    map_smul_gaussianBetaOrderedMeasure hβ (by norm_num : (0 : ℝ) < 1 / 2) hs (n + 1), hc_eq]

/-- Marginal eigenvalue law of the Dumitriu–Edelman tridiagonal matrix at `c = 1 / 2`. -/
theorem map_jacobiEigenvalues_hermiteBetaTridiagonalLaw {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    (hermiteBetaTridiagonalLaw β n).map (fun p => jacobiEigenvalues p.1 p.2) =
      gaussianBetaOrderedMeasure β (1 / 2) (n + 1) := by
  have := isProbabilityMeasure_dirichletMeasure (a := fun _ : Fin (n + 1) => β / 2)
    (fun _ => half_pos hβ)
  have hmeas : Measurable (fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) =>
      (jacobiEigenvalues p.1 p.2,
        (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (jacobiSpectralWeight p.1 p.2))) :=
    measurable_jacobiEigenvalues.prodMk
      ((EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.measurable.comp
        measurable_jacobiSpectralWeight)
  have hfst := congrArg (Measure.map Prod.fst) (map_jacobiSpectral_hermiteBetaTridiagonalLaw hβ n)
  rw [Measure.map_map measurable_fst hmeas, Measure.map_fst_prod, measure_univ, one_smul] at hfst
  exact hfst

/-- Marginal eigenvalue law of the rescaled Dumitriu–Edelman tridiagonal matrix at arbitrary
confinement `c > 0`. -/
theorem map_jacobiEigenvalues_smul_hermiteBetaTridiagonalLaw {β c : ℝ} (hβ : 0 < β) (hc : 0 < c)
    (n : ℕ) :
    let s : ℝ := (Real.sqrt (2 * c))⁻¹
    (hermiteBetaTridiagonalLaw β n).map (fun p => jacobiEigenvalues (s • p.1) (s • p.2)) =
      gaussianBetaOrderedMeasure β c (n + 1) := by
  intro s
  have := isProbabilityMeasure_dirichletMeasure (a := fun _ : Fin (n + 1) => β / 2)
    (fun _ => half_pos hβ)
  have hsmul : Measurable (fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) => (s • p.1, s • p.2)) :=
    ((continuous_const_smul s).measurable.comp measurable_fst).prodMk
      ((continuous_const_smul s).measurable.comp measurable_snd)
  have hmeas : Measurable (fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) =>
      (jacobiEigenvalues (s • p.1) (s • p.2),
        (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (jacobiSpectralWeight (s • p.1) (s • p.2)))) :=
    (measurable_jacobiEigenvalues.comp hsmul).prodMk
      (((EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.measurable.comp
        measurable_jacobiSpectralWeight).comp hsmul)
  have hfst := congrArg (Measure.map Prod.fst)
    (map_jacobiSpectral_smul_hermiteBetaTridiagonalLaw hβ hc n)
  rw [Measure.map_map measurable_fst hmeas, Measure.map_fst_prod, measure_univ, one_smul] at hfst
  exact hfst

/-- Marginal spectral-weight law of the Dumitriu–Edelman tridiagonal matrix:
`Dirichlet(β / 2, …, β / 2)`. -/
theorem map_jacobiSpectralWeight_hermiteBetaTridiagonalLaw {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    (hermiteBetaTridiagonalLaw β n).map
        (fun p => (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (jacobiSpectralWeight p.1 p.2)) =
      dirichletMeasure fun _ : Fin (n + 1) => β / 2 := by
  have := isProbabilityMeasure_gaussianBetaOrderedMeasure hβ (by norm_num : (0 : ℝ) < 1 / 2) (n + 1)
  have := isProbabilityMeasure_dirichletMeasure (a := fun _ : Fin (n + 1) => β / 2)
    (fun _ => half_pos hβ)
  have hmeas : Measurable (fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) =>
      (jacobiEigenvalues p.1 p.2,
        (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (jacobiSpectralWeight p.1 p.2))) :=
    measurable_jacobiEigenvalues.prodMk
      ((EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.measurable.comp
        measurable_jacobiSpectralWeight)
  have hsnd := congrArg (Measure.map Prod.snd) (map_jacobiSpectral_hermiteBetaTridiagonalLaw hβ n)
  rw [Measure.map_map measurable_snd hmeas, Measure.map_snd_prod, measure_univ, one_smul] at hsnd
  exact hsnd

/-- Under `hermiteBetaTridiagonalLaw β n` (`β > 0`), the ordered eigenvalues and the spectral
weights are independent. -/
theorem indepFun_jacobiEigenvalues_jacobiSpectralWeight_hermiteBetaTridiagonalLaw {β : ℝ}
    (hβ : 0 < β) (n : ℕ) :
    IndepFun
      (fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) => jacobiEigenvalues p.1 p.2)
      (fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) =>
        (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (jacobiSpectralWeight p.1 p.2))
      (hermiteBetaTridiagonalLaw β n) := by
  have := isProbabilityMeasure_hermiteBetaTridiagonalLaw hβ.le n
  have hmeas2 : Measurable (fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) =>
      (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (jacobiSpectralWeight p.1 p.2)) :=
    (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.measurable.comp
      measurable_jacobiSpectralWeight
  rw [indepFun_iff_map_prod_eq_prod_map_map measurable_jacobiEigenvalues.aemeasurable
    hmeas2.aemeasurable, map_jacobiEigenvalues_hermiteBetaTridiagonalLaw hβ n,
    map_jacobiSpectralWeight_hermiteBetaTridiagonalLaw hβ n]
  exact map_jacobiSpectral_hermiteBetaTridiagonalLaw hβ n

end Probability

end TauCeti
