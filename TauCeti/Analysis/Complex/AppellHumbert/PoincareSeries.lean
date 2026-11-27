/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.AppellHumbert.Positive
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.Complex.UniformLimit
import TauCeti.Analysis.Fourier.Torus.FourierCoeff
import TauCeti.Analysis.Fourier.Torus.Periodic

/-!
# Positive Appell–Humbert data have nonzero theta functions

Let `D = (B, χ)` be an Appell–Humbert datum for a full lattice `L` in a finite-dimensional complex
normed space `V`, with Riemann form `E` (`TauCeti.AppellHumbertData`). This file shows that the
theta functions of a datum with positive Riemann form (`TauCeti.AppellHumbertData.IsPositive`) do
not all vanish (`TauCeti.AppellHumbertData.IsPositive.exists_mem_thetaSpace_ne_zero`), the first
step of Frobenius' dimension formula. It uses the decomposition of `B` into its complex bilinear
part `B₁` (`TauCeti.AppellHumbertData.symmetricPart`) and the rest `B - B₁`
(`TauCeti.AppellHumbertData.hermitianPart`), whose real part on the diagonal is
`π E (i u, u)`; for a positive datum this grows like `‖u‖²`.

**Poincaré series.** For a linear form `ξ`, the series
`P_ξ (y) = ∑_{l ∈ L} e_l (y)⁻¹ exp (B₁ (y + l, y + l) / 2 + ξ (y + l))`, with `e` the factor of
automorphy, converges normally on compact sets (its terms decay like `exp (-c ‖l‖²)`) and is a
theta function of `D` by the cocycle law
(`TauCeti.AppellHumbertData.poincareSeries_mem_thetaSpace`). On the diagonal `ξ = (B - B₁) (y, ·)`
it is, up to a nowhere vanishing factor, the Fourier series
`∑_{l ∈ L} χ (l)⁻¹ exp (-(B - B₁) (l, l) / 2) exp (2πi E (l, y))` on the torus `V ⧸ L`, whose
constant coefficient is `1`; so it is not identically zero.

## Main declarations

* `TauCeti.AppellHumbertData.poincareSeries`: the Poincaré series `P_ξ`.
* `TauCeti.AppellHumbertData.poincareSeries_mem_thetaSpace`: `P_ξ` is a theta function.
* `TauCeti.AppellHumbertData.IsPositive.exists_mem_thetaSpace_ne_zero`: a positive datum has a
  nonzero theta function.

## Provenance

The construction is adapted from `New.IsAppellHumbert.summable_and_analyticAt_tsum`,
`New.IsAppellHumbert.poincareSeries_mem_thetaSpace_and_quotMean` and
`New.IsAppellHumbert.exists_mem_thetaSpace_ne_zero`
(file `src/Lib/Shimura/ComplexTheta/DimensionFormula.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0, Copyright 2026 Anthropic, PBC).
There the series is summed for the Hermitian form `B - B₁` and carried to `B` by an exponential
factor, and the constant Fourier coefficient is read off with a mean over the torus `V ⧸ L`; here
the factor `exp (B₁ (y, y) / 2)` is built into the series, which is then a theta function of `D`
directly, and the coefficient is read off with Mathlib's Fourier analysis on `ℝᵈ / ℤᵈ` in the
coordinates of a basis of `L`.

## References

* C. Birkenhake, H. Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Springer, 2004,
  Chapter 3 (classical factors) and Section 4.1.
* D. Mumford, *Abelian Varieties*, Tata Institute of Fundamental Research, 1970, Chapter I, §3.
-/

public section

open Complex Filter Metric Topology
open scoped Real ComplexConjugate

namespace TauCeti.AppellHumbertData

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {L : Submodule ℤ V}
  (D : AppellHumbertData L)

/-! ### Poincaré series -/

/-- The **Poincaré series** `P_ξ (y) = ∑_{l ∈ L} e_l (y)⁻¹ exp (B₁ (y + l, y + l) / 2 + ξ (y + l))`
of an Appell–Humbert datum, for a linear form `ξ`, where `e` is the factor of automorphy and `B₁`
the complex bilinear part of `B`. For a positive datum it converges and is a theta function
(`TauCeti.AppellHumbertData.poincareSeries_mem_thetaSpace`). -/
noncomputable def poincareSeries (ξ : V →L[ℂ] ℂ) (y : V) : ℂ :=
  ∑' l : L, (D.factor l y)⁻¹ * exp (D.symmetricPart (y + l) (y + l) / 2 + ξ (y + l))

/-- The Poincaré series as its sum. -/
theorem poincareSeries_def (ξ : V →L[ℂ] ℂ) (y : V) :
    D.poincareSeries ξ y =
      ∑' l : L, (D.factor l y)⁻¹ * exp (D.symmetricPart (y + l) (y + l) / 2 + ξ (y + l)) :=
  (rfl)

/-- The terms of the Poincaré series, rearranged: the exponent is
`B₁ (y, y) / 2 + ξ y - (B - B₁) (l, y) - (B - B₁) (l, l) / 2 + ξ l`. -/
theorem factor_inv_mul_exp_eq (ξ : V →L[ℂ] ℂ) (y : V) (l : L) :
    (D.factor l y)⁻¹ * exp (D.symmetricPart (y + l) (y + l) / 2 + ξ (y + l)) =
      (D.semichar l : ℂ)⁻¹ * exp (D.symmetricPart y y / 2 + ξ y +
        (-D.hermitianPart l y - D.hermitianPart l l / 2 + ξ l)) := by
  rw [factor_def, mul_inv, mul_assoc, ← exp_neg, ← exp_add]
  congr 2
  simp only [map_add, _root_.add_apply, hermitianPart_apply,
    D.symmetricPart_comm y (l : V)]
  ring

variable {D}

/-- The terms of the Poincaré series are dominated, uniformly for `y` in a ball, by a Gaussian in
`l`. -/
theorem IsPositive.exists_norm_factor_inv_mul_exp_le [FiniteDimensional ℂ V] (hD : D.IsPositive)
    (ξ : V →L[ℂ] ℂ) (R : ℝ) :
    ∃ c > 0, ∃ K : ℝ, ∀ y ∈ closedBall (0 : V) R, ∀ l : L,
      ‖(D.factor l y)⁻¹ * exp (D.symmetricPart (y + l) (y + l) / 2 + ξ (y + l))‖ ≤
        K * Real.exp (-c * ‖(l : V)‖ ^ 2) := by
  obtain ⟨c, hc, hle⟩ := hD.exists_pos_mul_sq_le
  set A := ‖D.hermitianPart‖ * R + ‖ξ‖
  set c' := π * c / 4
  have hc' : 0 < c' := by positivity
  refine ⟨c', hc', Real.exp (‖D.symmetricPart‖ * R ^ 2 / 2 + ‖ξ‖ * R + A ^ 2 / c'),
    fun y hy l ↦ ?_⟩
  have hy' : ‖y‖ ≤ R := by simpa using hy
  have hR : 0 ≤ R := (norm_nonneg y).trans hy'
  set t := ‖(l : V)‖
  rw [factor_inv_mul_exp_eq, norm_mul, norm_inv, Circle.norm_coe, inv_one, one_mul, norm_exp,
    ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  -- Bound each piece of the real part of the exponent.
  have h1 : (D.symmetricPart y y / 2).re ≤ ‖D.symmetricPart‖ * R ^ 2 / 2 := by
    have := (D.symmetricPart y y).re_le_norm.trans (D.symmetricPart.le_opNorm₂ y y)
    rw [div_ofNat_re]
    nlinarith [norm_nonneg y, norm_nonneg D.symmetricPart, mul_le_mul hy' hy' (norm_nonneg y) hR]
  have h2 : (ξ y).re ≤ ‖ξ‖ * R :=
    (ξ y).re_le_norm.trans ((ξ.le_opNorm y).trans (by gcongr))
  have h3 : (-D.hermitianPart l y).re ≤ ‖D.hermitianPart‖ * R * t := by
    have h0 := (abs_le.mp (abs_re_le_norm (D.hermitianPart l y))).1
    have h1 := (D.hermitianPart l).le_opNorm y
    have h2 := D.hermitianPart.le_opNorm (l : V)
    rw [neg_re]
    calc -(D.hermitianPart l y).re ≤ ‖D.hermitianPart l‖ * ‖y‖ := by linarith
      _ ≤ (‖D.hermitianPart‖ * t) * R := by gcongr
      _ = _ := by ring
  have h4 : (ξ l).re ≤ ‖ξ‖ * t := (ξ l).re_le_norm.trans (ξ.le_opNorm _)
  have h5 : (D.hermitianPart l l / 2).re ≥ π * c * t ^ 2 / 2 := by
    rw [div_ofNat_re, re_hermitianPart_self]
    have := hle l
    nlinarith [Real.pi_pos]
  have h6 : A * t ≤ c' * t ^ 2 + A ^ 2 / c' := by
    have : 0 ≤ (c' * t - A / 2) ^ 2 / c' := by positivity
    field_simp at this ⊢
    nlinarith [sq_nonneg (c' * t - A / 2)]
  have hA : A * t = ‖D.hermitianPart‖ * R * t + ‖ξ‖ * t := by simp only [A]; ring
  have key : π * c * t ^ 2 / 2 = 2 * (c' * t ^ 2) := by simp only [c']; ring
  simp only [add_re, sub_re]
  linarith [hA, key]


/-- A term of the Poincaré series is an entire function of `y`. -/
theorem differentiable_factor_inv_mul_exp (ξ : V →L[ℂ] ℂ) (l : L) :
    Differentiable ℂ fun y : V ↦
      (D.factor l y)⁻¹ * exp (D.symmetricPart (y + l) (y + l) / 2 + ξ (y + l)) := by
  have h : (fun y : V ↦ (D.factor l y)⁻¹ * exp (D.symmetricPart (y + l) (y + l) / 2 + ξ (y + l)))
      = fun y ↦ (D.semichar l : ℂ)⁻¹ * exp (-(D.form l y + D.form l l / 2) +
        (D.symmetricPart (y + l) (y + l) / 2 + ξ (y + l))) := by
    funext y
    rw [factor_def, mul_inv, ← exp_neg, mul_assoc, ← exp_add]
  have hB₁ : Differentiable ℂ fun y : V ↦ D.symmetricPart (y + l) (y + l) :=
    D.symmetricPart.differentiable_apply_self.comp (differentiable_id.add_const _)
  rw [h]
  fun_prop

/-- On the diagonal `ξ = (B - B₁) (y, ·)`, the Poincaré series is a nowhere vanishing factor times
the Fourier series `∑_{l ∈ L} χ (l)⁻¹ exp (-(B - B₁) (l, l) / 2) exp (2πi E (l, y))`. -/
theorem poincareSeries_hermitianPart (y : V) :
    D.poincareSeries (D.hermitianPart y) y =
      exp (D.symmetricPart y y / 2 + D.hermitianPart y y) *
        ∑' l : L, (D.semichar l : ℂ)⁻¹ * exp (-(D.hermitianPart l l / 2)) *
          exp (2 * π * I * D.riemannForm l y) := by
  rw [poincareSeries_def, ← tsum_mul_left]
  refine tsum_congr fun l ↦ ?_
  rw [factor_inv_mul_exp_eq, ← mul_assoc, mul_comm (exp _), mul_assoc, mul_assoc, ← exp_add,
    ← exp_add]
  congr 2
  linear_combination D.hermitianPart_sub_hermitianPart l y

variable [FiniteDimensional ℂ V] [DiscreteTopology L]

/-- For a positive datum the terms of the Poincaré series are summable. -/
theorem IsPositive.summable_factor_inv_mul_exp (hD : D.IsPositive) (ξ : V →L[ℂ] ℂ) (y : V) :
    Summable fun l : L ↦
      (D.factor l y)⁻¹ * exp (D.symmetricPart (y + l) (y + l) / 2 + ξ (y + l)) := by
  obtain ⟨c, hc, K, hK⟩ := hD.exists_norm_factor_inv_mul_exp_le ξ ‖y‖
  refine Summable.of_norm_bounded ((ZLattice.summable_exp_neg_mul_norm_add_sq L hc 0).mul_left K)
    fun l ↦ ?_
  simpa using hK y (by simp) l

/-- **The Poincaré series is a theta function.** For a positive datum and every linear form `ξ`,
the series `P_ξ` converges to an entire function with `P_ξ (y + l) = e_l (y) P_ξ (y)`. -/
theorem IsPositive.poincareSeries_mem_thetaSpace (hD : D.IsPositive) (ξ : V →L[ℂ] ℂ) :
    D.poincareSeries ξ ∈ D.thetaSpace := by
  refine (mem_thetaSpace_iff _).mpr ⟨fun y₀ ↦ ?_, fun m y ↦ ?_⟩
  · -- On a ball round `y₀` the series converges uniformly, by the Gaussian bound.
    obtain ⟨c, hc, K, hK⟩ := hD.exists_norm_factor_inv_mul_exp_le ξ (‖y₀‖ + 1)
    have hu : Summable fun l : L ↦ K * Real.exp (-c * ‖(l : V)‖ ^ 2) := by
      simpa using (ZLattice.summable_exp_neg_mul_norm_add_sq L hc 0).mul_left K
    have htend := tendstoUniformlyOn_tsum hu (s := ball (0 : V) (‖y₀‖ + 1))
      (f := fun l y ↦ (D.factor l y)⁻¹ * exp (D.symmetricPart (y + l) (y + l) / 2 + ξ (y + l)))
      fun l y hy ↦ hK y (ball_subset_closedBall hy) l
    have hdiff : DifferentiableOn ℂ (D.poincareSeries ξ) (ball (0 : V) (‖y₀‖ + 1)) :=
      htend.differentiableOn (.of_forall fun t ↦ (Differentiable.fun_sum fun l _ ↦
        D.differentiable_factor_inv_mul_exp ξ l).differentiableOn) isOpen_ball
    exact hdiff.differentiableAt (isOpen_ball.mem_nhds (by simp))
  · -- The cocycle law shifts the summation index by `m`.
    have h (l : L) : (D.factor l (y + m))⁻¹ *
        exp (D.symmetricPart (y + m + l) (y + m + l) / 2 + ξ (y + m + l)) =
          D.factor m y * ((D.factor (l + m) y)⁻¹ *
            exp (D.symmetricPart (y + ↑(l + m)) (y + ↑(l + m)) / 2 + ξ (y + ↑(l + m)))) := by
      rw [D.factor_cocycle l m y, Submodule.coe_add, add_comm (l : V) m, ← add_assoc]
      field_simp [D.factor_ne_zero]
    simp only [poincareSeries_def, h, tsum_mul_left]
    congr 1
    exact (Equiv.addRight m).tsum_eq fun l ↦
      (D.factor l y)⁻¹ * exp (D.symmetricPart (y + l) (y + l) / 2 + ξ (y + l))

/-- For a positive datum the Fourier coefficients `χ (l)⁻¹ exp (-(B - B₁) (l, l) / 2)` of the
Poincaré series on the diagonal are absolutely summable. -/
private theorem IsPositive.summable_norm_semichar_inv_mul_exp (hD : D.IsPositive) :
    Summable fun l : L ↦ ‖(D.semichar l : ℂ)⁻¹ * exp (-(D.hermitianPart l l / 2))‖ := by
  obtain ⟨c₀, hc₀, hle⟩ := hD.exists_pos_mul_sq_le
  have hg := ZLattice.summable_exp_neg_mul_norm_add_sq L (show 0 < π * c₀ / 2 by positivity) 0
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun l ↦ ?_) (by simpa using hg)
  simp only [norm_mul, norm_inv, Circle.norm_coe, inv_one, one_mul, norm_exp, neg_re,
    div_ofNat_re, re_hermitianPart_self]
  exact Real.exp_le_exp.mpr (by nlinarith [hle l, Real.pi_pos])

/-- **A positive datum has a nonzero theta function.** If the Riemann form of `D` is positive, some
theta function of `D` does not vanish identically. -/
theorem IsPositive.exists_mem_thetaSpace_ne_zero [IsZLattice ℝ L] (hD : D.IsPositive) :
    ∃ f ∈ D.thetaSpace, f ≠ 0 := by
  -- The Poincaré series `P_ξ` at `ξ = (B - B₁) (y, ·)` is, on the diagonal, a Fourier series on
  -- the torus `V ⧸ L` with constant coefficient `1`, so it does not vanish at some `y`.
  -- It suffices that `P_ξ (y) ≠ 0` for some `y`, with `ξ = (B - B₁) (y, ·)`.
  suffices ∃ y : V, D.poincareSeries (D.hermitianPart y) y ≠ 0 by
    obtain ⟨y, hy⟩ := this
    exact ⟨_, hD.poincareSeries_mem_thetaSpace _, fun h ↦ hy (congrFun h y)⟩
  by_contra! h_zero
  set a : L → ℂ := fun l ↦ (D.semichar l : ℂ)⁻¹ * exp (-(D.hermitianPart l l / 2))
  have h_sum (y : V) : ∑' l : L, a l * exp (2 * π * I * D.riemannForm l y) = 0 := by
    simpa [poincareSeries_hermitianPart, exp_ne_zero] using h_zero y
  -- In the coordinates of a basis `b` of `L`, the characters `exp (2πi E (l, ·))` are the
  -- monomials `mFourier (n l)` of the torus, with `n l i = E (l, b i)`.
  let b := Module.Free.chooseBasis ℤ L
  let bR := b.ofZLatticeBasis ℝ L
  have h_int (l : L) (i : Module.Free.ChooseBasisIndex ℤ L) :
      ∃ k : ℤ, D.riemannForm l (bR i) = k := by
    simpa [bR] using D.exists_riemannForm_eq_intCast l (b i)
  choose n hn using h_int
  have h_char (l : L) (φ : Module.Free.ChooseBasisIndex ℤ L → ℝ) :=
    UnitAddTorus.exp_two_pi_I_mul_equivFun_symm_eq_mFourier bR (D.riemannForm l) (hn l) φ
  have hn_inj : Function.Injective n := by
    intro l l' h
    have h_zero : ∀ i, D.riemannForm ((l : V) - l') (bR i) = 0 := fun i ↦ by
      rw [map_sub, LinearMap.sub_apply, hn, hn, h]
      simp
    have : D.riemannForm ((l : V) - l') = 0 := bR.ext fun i ↦ by simpa using h_zero i
    exact Subtype.ext (sub_eq_zero.mp (hD.nondegenerate.1 _ fun v ↦ by simp [this]))
  have hn_zero : n 0 = 0 := by
    funext i
    have := hn 0 i
    simp only [ZeroMemClass.coe_zero, map_zero, LinearMap.zero_apply] at this
    exact_mod_cast this.symm
  -- The coefficients, extended by zero to all of `ℤ^ι`, are absolutely summable.
  set c : (Module.Free.ChooseBasisIndex ℤ L → ℤ) → ℂ := Function.extend n a 0
  have hc_n (l : L) : c (n l) = a l := hn_inj.extend_apply a 0 l
  have hc_out {m} (hm : m ∉ Set.range n) : c m = 0 := by
    simp [c, Function.extend_apply' _ _ _ hm]
  have hc_sum : Summable fun m ↦ ‖c m‖ :=
    (hn_inj.summable_iff fun m hm ↦ by simp [hc_out hm]).mp
      (by simpa only [Function.comp_def, hc_n] using hD.summable_norm_semichar_inv_mul_exp)
  -- The trigonometric series with coefficients `c` vanishes on the torus.
  have hF (θ : UnitAddTorus (Module.Free.ChooseBasisIndex ℤ L)) :
      ∑' m, c m • UnitAddTorus.mFourier m θ = 0 := by
    choose φ hφ using fun i ↦ QuotientAddGroup.mk_surjective (θ i)
    have hθ : θ = fun i ↦ (φ i : UnitAddCircle) := funext fun i ↦ (hφ i).symm
    rw [← hn_inj.tsum_eq fun m hm ↦ by_contra fun h ↦ hm (by simp [hc_out h])]
    simpa [hc_n, hθ, ← h_char] using h_sum (bR.equivFun.symm φ)
  -- But its constant Fourier coefficient is `c 0 = a 0 = 1`.
  have h_coeff := UnitAddTorus.mFourierCoeff_tsum_smul_mFourier hc_sum 0
  rw [show (fun z ↦ ∑' m, c m • UnitAddTorus.mFourier m z) = 0 from funext hF,
    UnitAddTorus.mFourierCoeff_zero, ← hn_zero, hc_n] at h_coeff
  simp [a] at h_coeff

end TauCeti.AppellHumbertData
