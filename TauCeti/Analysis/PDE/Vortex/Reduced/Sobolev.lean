/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.PDE.Vortex.Background
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.PDE.Vortex.Asymptotics
import TauCeti.Analysis.Polynomial.AtInfinity
import TauCeti.Analysis.Polynomial.Sobolev
import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
import TauCeti.Analysis.Sobolev.BesselPotential.Laplacian
import TauCeti.Analysis.Sobolev.BesselPotential.PowerSeries

/-!
# Sobolev regularity of solutions of the reduced vortex equation

Let `P` be a complex polynomial of degree `m ≥ 1`. Taubes's plane vortex with zero divisor `P`
has amplitude `u₀ + w`, where `u₀ = -log (1 + ‖P‖²) / 2` is the background amplitude and the
correction `w` solves the reduced equation

`Δw = (exp (2w) h - 1) / 8 + g`,    `h = ‖P‖² / (1 + ‖P‖²)`,    `g = 2 ‖P'‖² / (1 + ‖P‖²)²`.

Taubes's variational construction produces a smooth solution `w ∈ L²(ℂ)`
(`TauCeti.Vortex.exists_contDiff_memLp_laplacian_eq_reduced`). This file shows that every `C²`
square-integrable solution lies in the Bessel-potential space `H^s(ℂ)` for every `s`
(`TauCeti.Vortex.mem_realSobolevFunctions_of_laplacian_eq_reduced`), so the correction is a
Sobolev function of every order, not only a square-integrable one.

Write `φ = 1 - h = (1 + ‖P‖²)⁻¹` and `E = exp (2w) - 1`, so that the right-hand side is

`E / 8 - φ E / 8 - φ / 8 + g`.

The coefficients `φ` and `g` lie in every `H^k(ℂ)`
(`Polynomial.inv_one_add_norm_eval_sq_mem_realSobolevFunctions`,
`Polynomial.norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq_mem_realSobolevFunctions`). The
proof is a bootstrap:

* a `C²` solution `w ∈ L²` tends to zero at infinity
  (`TauCeti.Vortex.tendsto_cocompact_of_memLp_of_laplacian_eq`), hence is bounded, and then
  `|E| ≤ 2 exp (2 M) |w|` is square integrable, so the right-hand side is square integrable and
  elliptic regularity (`TemperedDistribution.mem_realSobolevFunctions_add_two_of_laplacian`) puts
  `w` in `H²(ℂ)`;
* if `w ∈ H^k(ℂ)` with `k ≥ 2`, then `H^k(ℂ)` is an algebra, `E ∈ H^k(ℂ)` by the exponential
  series (`TemperedDistribution.exists_memSobolev_ae_eq_exp_mul_sub_one`), so the right-hand side
  lies in `H^k(ℂ)` and `w ∈ H^(k+2)(ℂ)`.

## Main results

* `TauCeti.Vortex.mem_realSobolevFunctions_of_laplacian_eq_reduced`: a `C²` square-integrable
  solution of the reduced equation lies in `H^s(ℂ)` for every `s`.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

open Filter MeasureTheory TemperedDistribution Topology InnerProductSpace Laplacian Module
open scoped ContDiff ZeroAtInfty

namespace TauCeti.Vortex

variable {P : Polynomial ℂ}

/-- The right-hand side of the reduced equation in terms of `φ = (1 + ‖P‖²)⁻¹` and
`E = exp (2w) - 1`. -/
private theorem reduced_eq (w : ℂ → ℝ) (z : ℂ) :
    (Real.exp (2 * w z) * backgroundWeight P.eval z - 1) / 8 +
        2 * ‖deriv P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 =
      (1 / 8 : ℝ) * (Real.exp (2 * w z) - 1) -
          (1 / 8 : ℝ) * ((1 + ‖P.eval z‖ ^ 2)⁻¹ * (Real.exp (2 * w z) - 1)) -
        (1 / 8 : ℝ) * (1 + ‖P.eval z‖ ^ 2)⁻¹ +
      2 * (‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) := by
  rw [backgroundWeight_def, Polynomial.deriv]
  have hN : (1 + ‖P.eval z‖ ^ 2) ≠ 0 := by positivity
  field_simp
  ring

/-- The right-hand side of the reduced equation lies in `H^k(ℂ)`, for `k = 0` or `k ≥ 2`, as soon
as `exp (2w) - 1` does. -/
private theorem laplacian_mem_realSobolevFunctions (hm : 0 < P.natDegree) {w : ℂ → ℝ}
    (hΔ : ∀ z, Δ w z = (Real.exp (2 * w z) * backgroundWeight P.eval z - 1) / 8 +
      2 * ‖deriv P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) {k : ℕ} (hk : 2 ≤ k ∨ k = 0)
    (hE : (fun z ↦ Real.exp (2 * w z) - 1) ∈ realSobolevFunctions ℂ k 2) :
    Δ w ∈ realSobolevFunctions ℂ k 2 := by
  set E : ℂ → ℝ := fun z ↦ Real.exp (2 * w z) - 1
  set φ : ℂ → ℝ := fun z ↦ (1 + ‖P.eval z‖ ^ 2)⁻¹
  set g : ℂ → ℝ := fun z ↦ ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2
  have hΔeq : Δ w = (1 / 8 : ℝ) • E - (1 / 8 : ℝ) • (φ * E) - (1 / 8 : ℝ) • φ + (2 : ℝ) • g := by
    ext z
    rw [hΔ z, reduced_eq]
    rfl
  have hφ := Polynomial.inv_one_add_norm_eval_sq_mem_realSobolevFunctions hm k
  have hg :=
    Polynomial.norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq_mem_realSobolevFunctions P k
  have hφE : φ * E ∈ realSobolevFunctions ℂ k 2 := by
    rcases hk with hk | rfl
    · exact mul_mem_realSobolevFunctions (by
        rw [Complex.finrank_real_complex]; exact_mod_cast (by omega : 2 < 2 * k)) hφ hE
    · -- In `L²`, `0 ≤ φ ≤ 1` multiplies `E` boundedly.
      rw [Nat.cast_zero, mem_realSobolevFunctions_zero_iff] at hE ⊢
      refine hE.of_le ((Polynomial.memLp_inv_one_add_norm_eval_sq hm).aestronglyMeasurable.mul
        hE.aestronglyMeasurable) (Eventually.of_forall fun z ↦ ?_)
      have h0 : 0 ≤ φ z := by positivity
      have h1 : φ z ≤ 1 :=
        inv_le_one_of_one_le₀ (by simp only [le_add_iff_nonneg_right]; positivity)
      rw [Pi.mul_apply, norm_mul, Real.norm_of_nonneg h0]
      exact mul_le_of_le_one_left (norm_nonneg _) h1
  rw [hΔeq]
  exact add_mem (sub_mem (sub_mem (Submodule.smul_mem _ _ hE) (Submodule.smul_mem _ _ hφE))
    (Submodule.smul_mem _ _ hφ)) (Submodule.smul_mem _ _ hg)

/-- For a continuous square-integrable `w` with `|w| ≤ M`, `exp (2w) - 1` is square integrable,
since `|exp (2w) - 1| ≤ 2 exp (2M) |w|`. -/
private theorem memLp_exp_two_mul_sub_one {w : ℂ → ℝ} (hw : Continuous w) (hw2 : MemLp w 2)
    {M : ℝ} (hM : ∀ z, |w z| ≤ M) : MemLp (fun z ↦ Real.exp (2 * w z) - 1) 2 := by
  refine (hw2.const_mul (2 * Real.exp (2 * M))).of_le
    ((hw.const_mul 2).rexp.sub continuous_const).aestronglyMeasurable
    (Eventually.of_forall fun z ↦ ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_two,
    abs_of_pos (Real.exp_pos _)]
  -- `|exp y - 1| ≤ exp |y| |y|`: from `1 + y ≤ exp y` and `1 - y ≤ exp (-y)`.
  have hexp (y : ℝ) : |Real.exp y - 1| ≤ Real.exp |y| * |y| := by
    rcases le_total 0 y with hy | hy
    · have h1 := Real.add_one_le_exp (-y)
      have h2 : Real.exp (-y) * Real.exp y = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      rw [abs_of_nonneg (by linarith [Real.add_one_le_exp y]), abs_of_nonneg hy]
      nlinarith [Real.exp_pos y]
    · have h1 := Real.add_one_le_exp y
      rw [abs_of_nonpos (by linarith [Real.exp_le_one_iff.2 hy]), abs_of_nonpos hy]
      nlinarith [Real.one_le_exp (neg_nonneg.2 hy)]
  calc |Real.exp (2 * w z) - 1| ≤ Real.exp |2 * w z| * |2 * w z| := hexp _
    _ ≤ Real.exp (2 * M) * (2 * |w z|) := by
        rw [abs_mul, abs_two]
        gcongr
        exact hM z
    _ = 2 * Real.exp (2 * M) * |w z| := by ring

/-- **Sobolev regularity of the reduced vortex equation.** Let `P` be a polynomial of positive
degree and let `w` be a `C²` square-integrable solution of
`Δw = (exp (2w) h - 1) / 8 + 2 ‖P'‖² / (1 + ‖P‖²)²`, `h = ‖P‖² / (1 + ‖P‖²)`. Then `w` lies in the
Bessel-potential space `H^s(ℂ)` for every real `s`. -/
theorem mem_realSobolevFunctions_of_laplacian_eq_reduced (hm : 0 < P.natDegree) {w : ℂ → ℝ}
    (hw : ContDiff ℝ 2 w) (hw2 : MemLp w 2)
    (hΔ : ∀ z, Δ w z = (Real.exp (2 * w z) * backgroundWeight P.eval z - 1) / 8 +
      2 * ‖deriv P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) (s : ℝ) :
    w ∈ realSobolevFunctions ℂ s 2 := by
  -- `w` tends to zero at infinity, hence is bounded, so `exp (2w) - 1 ∈ L²` and `w ∈ H²`.
  have h0 : Tendsto w (cocompact ℂ) (𝓝 0) :=
    tendsto_cocompact_of_memLp_of_laplacian_eq (.of_forall fun _ ↦ hw.contDiffAt) hw2
      one_le_two ENNReal.ofNat_ne_top (.of_forall hΔ)
  let F : C₀(ℂ, ℝ) := ⟨⟨w, hw.continuous⟩, h0⟩
  have hE0 := memLp_exp_two_mul_sub_one hw.continuous hw2 fun z ↦ F.toBCF.norm_coe_le_norm z
  have hΔ0 : Δ w ∈ realSobolevFunctions ℂ ((0 : ℕ) : ℝ) 2 :=
    laplacian_mem_realSobolevFunctions hm hΔ (Or.inr rfl) (by simpa using hE0)
  have hH2 : w ∈ realSobolevFunctions ℂ (0 + 2) 2 :=
    mem_realSobolevFunctions_add_two_of_laplacian hw (mem_realSobolevFunctions_zero_iff.2 hw2)
      (by simpa using hΔ0)
  -- The bootstrap: `w ∈ H^(2j + 2)` for every `j`, since `H^(2j + 2)(ℂ)` is an algebra.
  have hboot (j : ℕ) : w ∈ realSobolevFunctions ℂ ((2 * j + 2 : ℕ) : ℝ) 2 := by
    induction j with
    | zero => simpa using hH2
    | succ j ih =>
      set k := 2 * j + 2
      have hs : (finrank ℝ ℂ : ℝ) < 2 * (k : ℝ) := by
        rw [Complex.finrank_real_complex]; push_cast [k]; linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
      obtain ⟨v, hv, hvs⟩ := exists_memSobolev_ae_eq_exp_mul_sub_one hs ih 2
      have hE : (fun z ↦ Real.exp (2 * w z) - 1) ∈ realSobolevFunctions ℂ k 2 :=
        mem_realSobolevFunctions_of_ae_eq_ofReal hvs (hv.mono fun z hz ↦ by rw [hz]; push_cast; rfl)
      have h := mem_realSobolevFunctions_add_two_of_laplacian hw ih
        (laplacian_mem_realSobolevFunctions hm hΔ (Or.inl (by omega)) hE)
      rwa [show (k : ℝ) + 2 = ((2 * (j + 1) + 2 : ℕ) : ℝ) by push_cast [k]; ring] at h
  obtain ⟨j, hj⟩ := exists_nat_ge s
  refine realSobolevFunctions_mono (by norm_num) (by norm_num) ?_ (hboot j)
  push_cast
  linarith

end TauCeti.Vortex
