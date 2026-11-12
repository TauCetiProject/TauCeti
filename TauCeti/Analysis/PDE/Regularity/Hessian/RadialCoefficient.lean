/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Ellipticity.RadialCoefficient
public import TauCeti.Analysis.Sobolev.Wkp.NormRpow
public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation

/-!
# Without vanishing mean oscillation there is no `W^{2,p}` regularity for large `p`

The `W^{2,p}` theory of non-divergence-form equations `aⁱʲ ∂ᵢ∂ⱼu = f` for `1 < p < ∞` needs
some continuity of the coefficients, for instance vanishing mean oscillation. This file records
the standard example showing that bounded measurable, uniformly elliptic, symmetric coefficients
are not enough in any dimension `n ≥ 2`.

For `b ≥ 0` let `a = TauCeti.PDE.radialCoefficient 1 b` be the coefficient field on `ℝⁿ`

`a(x) = I + b x̂ x̂ᵀ`, where `x̂ = x / ‖x‖`,

with eigenvalue `1 + b` in the radial direction and `1` in the tangential directions. It is
symmetric, measurable and uniformly elliptic with constants `1` and `1 + b`
(`TauCeti.PDE.uniformlyEllipticOn_radialCoefficient`), homogeneous of degree `0` and
discontinuous at the origin. For `b ≠ 0` the diagonal entries of every radial coefficient
`α I + b x̂ x̂ᵀ` do not have vanishing mean oscillation
(`TauCeti.PDE.not_memVMO_radialCoefficient_apply`): on every ball centred at the origin their
mean oscillation is at least `|b| / (10 · 8ⁿ)`.

Away from the origin, for `u(x) = ‖x‖ ^ γ` and `a = TauCeti.PDE.radialCoefficient α b`,

`aⁱʲ ∂ᵢ∂ⱼu = γ ‖x‖ ^ (γ - 2) (α (n + γ - 2) + b (γ - 1))`

(`TauCeti.PDE.sum_radialCoefficient_mul_iteratedGradientChain_norm_rpow`), which for `α = 1`
vanishes when `0 < γ < 1` and `b = (n + γ - 2) / (1 - γ) > 0`. With this choice, on a bounded
open set `Ω ∋ 0`, `u` lies in `W^{2,p}(Ω)` and solves `aⁱʲ ∂ᵢ∂ⱼu = 0` almost everywhere with its
weak Hessian exactly when `p < n / (2 - γ)`
(`TauCeti.PDE.exists_wkp_two_value_ae_eq_norm_rpow_and_sum_radialCoefficient_eq_zero_iff`). Since
`n / 2 < n / (2 - γ) < n`, the function `u` is a continuous `W^{2,p}` strong solution of the
homogeneous equation for some `p > n / 2`, but it is not in `W^{2,n}`: for bounded measurable
coefficients with ellipticity ratio `1 + b`, no theorem upgrading a `W^{2,p₀}` solution of the
homogeneous equation, `p₀ < n / (2 - γ)`, to `W^{2,p}` with `p ≥ n / (2 - γ)` can hold. As
`γ ↓ 0` the exponent `n / (2 - γ)` decreases to `n / 2`, while the ellipticity ratio `1 + b` tends
to `n - 1`.

## Main declarations

* `TauCeti.PDE.not_memVMO_radialCoefficient_apply`: the diagonal entries of a radial coefficient
  are not in VMO.
* `TauCeti.PDE.sum_radialCoefficient_mul_iteratedGradientChain_norm_rpow`: the operator applied
  to `‖x‖ ^ γ` away from the origin.
* `TauCeti.PDE.ae_sum_radialCoefficient_mul_iteratedGradient_eq`: the same identity almost
  everywhere for the weak Hessian of every `W^{2,p}` function equal to `‖x‖ ^ γ`.
* `TauCeti.PDE.exists_wkp_two_value_ae_eq_norm_rpow_and_sum_radialCoefficient_eq_zero_iff`:
  `‖x‖ ^ γ` is a `W^{2,p}` strong solution exactly for `p < n / (2 - γ)`.

## References

* D. Gilbarg and J. Serrin, *On isolated singularities of solutions of second order elliptic
  differential equations*, J. Analyse Math. 4 (1955/56), 309–340, for the coefficient field
  `δᵢⱼ + b xᵢ xⱼ / ‖x‖²` and its power solutions.
* N. G. Meyers, *An `Lᵖ`-estimate for the gradient of solutions of second order elliptic
  divergence equations*, Ann. Scuola Norm. Sup. Pisa (3) 17 (1963), 189–206, §5, for the
  analogous radial example in divergence form.
* F. Chiarenza, M. Frasca and P. Longo, *Interior `W^{2,p}` estimates for non divergence elliptic
  equations with discontinuous coefficients*, Ricerche Mat. 40 (1991), 149–168.
-/

public section

noncomputable section

open MeasureTheory Metric Set Module TopologicalSpace
open scoped NNReal ENNReal InnerProductSpace Matrix

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α b : ℝ}

/-! ### The coefficient does not have vanishing mean oscillation -/

omit [DecidableEq ι] in
/-- For every constant `m` and `r > 0`, the ball `B(0, r)` contains a ball of radius `r / 8` on
which `xᵢ² / ‖x‖²` stays at distance at least `1 / 10` from `m`: around `(r / 2) eᵢ` it is at
least `9 / 25`, and around `(r / 2) eⱼ`, `j ≠ i`, at most `1 / 9`. -/
private theorem exists_ball_le_abs_sq_div_norm_sq_sub [Nontrivial ι] (i : ι) (m : ℝ) {r : ℝ}
    (hr : 0 < r) : ∃ z : EuclideanSpace ℝ ι, ball z (r / 8) ⊆ ball 0 r ∧
      ∀ y ∈ ball z (r / 8), 1 / 10 ≤ |y i ^ 2 / ‖y‖ ^ 2 - m| := by
  classical
  obtain ⟨j, hji⟩ := exists_ne i
  set c : ι → EuclideanSpace ℝ ι := fun k => (r / 2) • EuclideanSpace.single k 1
  have hc : ∀ k, ‖c k‖ = r / 2 := fun k => by
    simp [c, norm_smul, abs_of_pos hr]
  have hnorm : ∀ k, ∀ y ∈ ball (c k) (r / 8), 3 * r / 8 < ‖y‖ ∧ ‖y‖ < 5 * r / 8 :=
    fun k y hy => by
      have hy' := mem_ball_iff_norm.1 hy
      constructor
      · linarith [norm_sub_norm_le (c k) y, norm_sub_rev (c k) y, hc k]
      · linarith [norm_le_insert' y (c k), hc k]
  have hcoord : ∀ k, ∀ y ∈ ball (c k) (r / 8), |y i - (if i = k then r / 2 else 0)| < r / 8 :=
    fun k y hy => by
      have := (PiLp.norm_apply_le (y - c k) i).trans_lt (mem_ball_iff_norm.1 hy)
      simpa [c, PiLp.single_apply, Real.norm_eq_abs, apply_ite] using this
  have hsub : ∀ k, ball (c k) (r / 8) ⊆ ball 0 r :=
    fun k y hy => mem_ball_zero_iff.2 (by linarith [(hnorm k y hy).2])
  rcases le_or_gt m (1 / 4) with hm | hm
  · refine ⟨c i, hsub i, fun y hy => ?_⟩
    obtain ⟨h1, h2⟩ := hnorm i y hy
    have hyi := (abs_lt.1 (hcoord i y hy)).1
    simp only [↓reduceIte] at hyi
    have hq : 9 / 25 ≤ y i ^ 2 / ‖y‖ ^ 2 := by
      rw [le_div_iff₀ (by nlinarith)]
      nlinarith [mul_self_lt_mul_self (norm_nonneg y) h2,
        mul_self_lt_mul_self (by positivity : (0 : ℝ) ≤ 3 * r / 8) (by linarith : 3 * r / 8 < y i)]
    rw [abs_of_nonneg (by linarith)]
    linarith
  · refine ⟨c j, hsub j, fun y hy => ?_⟩
    have h1 := (hnorm j y hy).1
    have hyi := abs_lt.1 (hcoord j y hy)
    simp only [hji.symm, ↓reduceIte, sub_zero] at hyi
    have hq : y i ^ 2 / ‖y‖ ^ 2 ≤ 1 / 9 := by
      rw [div_le_iff₀ (by nlinarith)]
      nlinarith [sq_lt_sq' hyi.1 hyi.2,
        mul_self_lt_mul_self (by positivity : (0 : ℝ) ≤ 3 * r / 8) h1]
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- **The radial coefficient is not in VMO.** For `b ≠ 0` and `n ≥ 2`, each diagonal entry
`α + b xᵢ² / ‖x‖²` of `TauCeti.PDE.radialCoefficient α b` has mean oscillation at least
`|b| / (10 · 8ⁿ)` on every ball centred at the origin, however small, so it does not have
vanishing mean oscillation. -/
theorem not_memVMO_radialCoefficient_apply [Nontrivial ι] (hb : b ≠ 0) (i : ι) :
    ¬ MemVMO (fun x : EuclideanSpace ℝ ι => radialCoefficient α b x i i) volume := by
  intro h
  set δ := ENNReal.ofReal (|b| / 10 * (1 / 8) ^ finrank ℝ (EuclideanSpace ℝ ι))
  have hδ : δ ≠ 0 := by
    simp only [δ, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have := abs_pos.2 hb
    positivity
  obtain ⟨r, hr, hle⟩ := (memVMO_iff.1 h).2 (δ / 2) (ENNReal.half_pos hδ)
  set a := ⨍ z in ball (0 : EuclideanSpace ℝ ι) r, radialCoefficient α b z i i
  obtain ⟨z, hsub, hz⟩ := exists_ball_le_abs_sq_div_norm_sq_sub i ((a - α) / b) hr
  -- On the small ball, `|a(y)ᵢᵢ - a| = |b| |yᵢ² / ‖y‖² - (a - α) / b| ≥ |b| / 10`.
  have hfar : ∀ y ∈ ball z (r / 8),
      ENNReal.ofReal (|b| / 10) ≤ ‖radialCoefficient α b y i i - a‖ₑ := fun y hy => by
    have heq : radialCoefficient α b y i i - a = b * (y i ^ 2 / ‖y‖ ^ 2 - (a - α) / b) := by
      simp only [radialCoefficient_apply, ↓reduceIte]
      rw [mul_sub, mul_div_cancel₀ _ hb]
      ring
    rw [Real.enorm_eq_ofReal_abs, heq, abs_mul]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [hz y hy, abs_nonneg b])
  have hlow := ofReal_mul_div_pow_le_setLAverage_enorm_sub (μ := volume)
    (by positivity : (0 : ℝ) < r / 8) hsub hfar
  rw [show r / 8 / r = 1 / 8 by field_simp] at hlow
  exact (ENNReal.half_lt_self hδ ENNReal.ofReal_ne_top).not_ge
    (hlow.trans ((setLAverage_enorm_sub_setAverage_le_vmoModulus _ volume 0 le_rfl).trans hle))

/-! ### The equation for a norm power -/

/-- Contracting the radial coefficient against a linear map `H` gives `α` times the trace of `H`
plus `b` times its radial value: `aⁱʲ(x) Hᵢⱼ = α tr H + b ⟪H x, x⟫ / ‖x‖²`. -/
private theorem sum_radialCoefficient_mul_apply_single (x : EuclideanSpace ℝ ι)
    (H : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    ∑ i, ∑ j, radialCoefficient α b x i j * H (EuclideanSpace.single j 1) i =
      α * ∑ i, ⟪H (EuclideanSpace.single i 1), EuclideanSpace.single i 1⟫_ℝ +
        b / ‖x‖ ^ 2 * ⟪H x, x⟫_ℝ := by
  have hH : ∀ i, H x i = ∑ j, x j * H (EuclideanSpace.single j 1) i := fun i => by
    conv_lhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr x]
    simp
  have hin : ⟪H x, x⟫_ℝ = ∑ i, x i * H x i := by
    simp [PiLp.inner_apply]
  simp only [radialCoefficient_apply, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, EuclideanSpace.inner_single_right, conj_trivial,
    hin, hH, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The radial operator on a norm power.** Away from the origin, for
`a = TauCeti.PDE.radialCoefficient α b` and `u(x) = ‖x‖ ^ γ`,
`aⁱʲ ∂ᵢ∂ⱼu = γ ‖x‖ ^ (γ - 2) (α (n + γ - 2) + b (γ - 1))`: the trace of the Hessian contributes
`γ (n + γ - 2) ‖x‖ ^ (γ - 2)` and its radial value `γ (γ - 1) ‖x‖ ^ γ`. -/
theorem sum_radialCoefficient_mul_iteratedGradientChain_norm_rpow (γ : ℝ)
    {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) :
    ∑ i, ∑ j, radialCoefficient α b x i j *
        iteratedGradientChain (fun y : EuclideanSpace ℝ ι => ‖y‖ ^ γ) 1 x
          (EuclideanSpace.single j 1) i =
      γ * ‖x‖ ^ (γ - 2) * (α * (Fintype.card ι + γ - 2) + b * (γ - 1)) := by
  have htr := sum_inner_iteratedGradientChain_one_norm_rpow_apply (γ := γ) hx
    (EuclideanSpace.basisFun ι ℝ)
  simp only [EuclideanSpace.basisFun_apply, finrank_euclideanSpace] at htr
  rw [sum_radialCoefficient_mul_apply_single, htr,
    inner_iteratedGradientChain_one_norm_rpow_apply_self hx, Real.rpow_sub (norm_pos_iff.2 hx)]
  norm_cast
  field_simp

/-- Every element of `W^{2,p}(Ω)` equal to `‖x‖ ^ γ`, for `n + γ > 2`, satisfies
`aⁱʲ ∂ᵢ∂ⱼu = γ ‖x‖ ^ (γ - 2) (α (n + γ - 2) + b (γ - 1))` almost everywhere with its weak Hessian,
for `a = TauCeti.PDE.radialCoefficient α b`. -/
theorem ae_sum_radialCoefficient_mul_iteratedGradient_eq {γ : ℝ} (hn : 2 < Fintype.card ι + γ)
    {Ω : Opens (EuclideanSpace ℝ ι)} {p : ℝ≥0∞} [Fact (1 ≤ p)] (w : Wkp volume Ω p 2)
    (hw : (Wkp.value 2 w : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict Ω] fun y => ‖y‖ ^ γ) :
    ∀ᵐ y ∂volume.restrict (Ω : Set (EuclideanSpace ℝ ι)),
      ∑ i, ∑ j, radialCoefficient α b y i j *
          Wkp.iteratedGradient 1 w y (EuclideanSpace.single j 1) i =
        γ * ‖y‖ ^ (γ - 2) * (α * (Fintype.card ι + γ - 2) + b * (γ - 1)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- On the zero space `γ > 2`, so both sides vanish.
    have hγ : 2 < γ := by simpa using hn
    exact ae_of_all _ fun y => by
      simp [Subsingleton.elim y 0, Real.zero_rpow (by linarith : γ - 2 ≠ 0)]
  have hn' : 2 < finrank ℝ (EuclideanSpace ℝ ι) + γ := by rwa [finrank_euclideanSpace]
  filter_upwards [Wkp.iteratedGradient_one_ae_eq_iteratedGradientChain_norm_rpow hn' w hw,
    ae_restrict_of_ae (volume.ae_ne 0)] with y hy h0
  rw [hy]
  exact sum_radialCoefficient_mul_iteratedGradientChain_norm_rpow γ h0

/-- **The VMO hypothesis is load-bearing for `W^{2,p}` regularity.** Let `n ≥ 2`, `0 < γ < 1`,
and let `a = TauCeti.PDE.radialCoefficient 1 b` with `b = (n + γ - 2) / (1 - γ) > 0`: a symmetric,
measurable coefficient field, uniformly elliptic with constants `1` and `1 + b`
(`TauCeti.PDE.uniformlyEllipticOn_radialCoefficient`) and not in VMO
(`TauCeti.PDE.not_memVMO_radialCoefficient_apply`). On a bounded open set `Ω` containing the
origin, `‖x‖ ^ γ` is a `W^{2,p}(Ω)` strong solution of `aⁱʲ ∂ᵢ∂ⱼu = 0` exactly when
`p < n / (2 - γ)`. Since `n / 2 < n / (2 - γ) < n`, it is a continuous `W^{2,p}` solution for some
`p > n / 2`, but not a `W^{2,n}` solution. -/
theorem exists_wkp_two_value_ae_eq_norm_rpow_and_sum_radialCoefficient_eq_zero_iff
    [Nontrivial ι] {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {Ω : Opens (EuclideanSpace ℝ ι)}
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) (h0 : (0 : EuclideanSpace ℝ ι) ∈ Ω)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    (∃ w : Wkp volume Ω p 2,
      (Wkp.value 2 w : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict Ω] (fun y => ‖y‖ ^ γ) ∧
      ∀ᵐ y ∂volume.restrict (Ω : Set (EuclideanSpace ℝ ι)),
        ∑ i, ∑ j, radialCoefficient 1 ((Fintype.card ι + γ - 2) / (1 - γ)) y i j *
          Wkp.iteratedGradient 1 w y (EuclideanSpace.single j 1) i = 0) ↔
      p < ENNReal.ofReal (Fintype.card ι / (2 - γ)) := by
  have hcard : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.one_lt_card
  have hn : 2 < finrank ℝ (EuclideanSpace ℝ ι) + γ := by
    rw [finrank_euclideanSpace]
    linarith
  have key := exists_wkp_two_value_ae_eq_norm_rpow_iff (μ := volume) (p := p) hγ0.ne'
    (by linarith) hn hb h0
  rw [finrank_euclideanSpace] at key
  rw [← key]
  refine exists_congr fun w => and_iff_left_of_imp fun hw => ?_
  have hzero :
      1 * (Fintype.card ι + γ - 2 : ℝ) + (Fintype.card ι + γ - 2) / (1 - γ) * (γ - 1) = 0 := by
    field_simp [(by linarith : (1 - γ) ≠ 0)]
    ring
  filter_upwards [ae_sum_radialCoefficient_mul_iteratedGradient_eq
    (α := 1) (b := (Fintype.card ι + γ - 2) / (1 - γ)) (by linarith) w hw] with y hy
  rw [hy, hzero, mul_zero]

end PDE

end TauCeti
