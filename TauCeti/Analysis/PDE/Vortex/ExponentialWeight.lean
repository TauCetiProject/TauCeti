/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.RightInverse
public import TauCeti.Analysis.PDE.Vortex.WeightedEstimate
public import TauCeti.Analysis.Distribution.TestFunction.SmulLp

/-!
# Exponential decay of the least-norm weak solution at a plane vortex

At a plane vortex `x` with `|α| → 1` at infinity, the gauge-fixed operator `L_x = d₀* ⊕ d₁` has
a bounded weak right inverse `Q` on `L²(ℂ; ℝ⁴)`, and `Q f` is the weak solution of `L_x y = f`
orthogonal to the weak kernel of `L_x`
(`TauCeti.Vortex.exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`). This file
proves that this solution decays exponentially whenever `f` does, at every rate below `1/2`. With
`ρ(z) = √(1 + |z|²)` and `0 ≤ c < 1/2`, there is a constant `K`, depending only on `x` and `c`,
such that

`‖exp(c ρ) y‖₂ ≤ K ‖exp(c ρ) f‖₂`

for every weak solution `y ∈ L²` of `L_x y = f` orthogonal to the weak kernel
(`TauCeti.Vortex.exists_eLpNorm_exp_smul_le_mul_eLpNorm_exp_smul`), in particular for `y = Q f`
(`exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_and_eLpNorm_exp_smul_le`).
The threshold `1/2` is the mass of the vacuum operator, `L₀* L₀ = -Δ + 1/4`. These are the
weighted estimates for the inverse of `L_x` on exponentially decaying inputs that the gluing of
vortices into four-dimensional fields uses.

The argument is the weighted-energy method of Agmon and of Combes and Thomas. Such a `y` is the
`L²` limit of `L_x* η_n` for compactly supported test fields `η_n`, and the spectral gap of
`L_x L_x*` makes the `η_n` converge in `L²` to some `u`, with `‖u‖₂ ≤ ‖f‖₂ / c₀`. For a bounded
weight `φ` with bounded derivative, the localization identity
`‖L_x* (φ η)‖² = ⟪L_x* (φ² η), L_x* η⟫ + ‖|dφ| η‖²`
(`TauCeti.Vortex.norm_sq_gaugeFixedAdjoint_fun_smul`) and the weak equation pass to the limit.
Outside a large disc `L_x*` has squared mass `a` for any `a < 1/4`
(`TauCeti.Vortex.mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint`), which absorbs the
weight gradient `c² < a`; on the disc the weight is bounded and the unweighted bound applies.
The exponential weight is approximated from below by the bounded weights
`exp(c ρ) / (1 + ε exp(c ρ))` (`TauCeti.boundedExpWeight`), whose logarithmic gradient is still at
most `c`, and Fatou's lemma removes the regularization.

These are `L²` statements. The `H^k` versions, the derivatives in the vortex parameters and the
kernel projections are not treated here.

## References

* S. Agmon, *Lectures on exponential decay of solutions of second-order elliptic equations*,
  Mathematical Notes 29, Princeton University Press, 1982.
* J.-M. Combes and L. Thomas, *Asymptotic behaviour of eigenfunctions for multiparticle
  Schrödinger operators*, Comm. Math. Phys. 34 (1973), 251–270.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory Filter
open scoped RealInnerProductSpace Topology ENNReal NNReal BoundedContinuousFunction
open BoundedContinuousFunction (smulLp coeFn_smulLp norm_smulLp_apply_le
  norm_smulLp_apply_le_of_abs_le smulLp_add smulLp_smul smulLp_const smulLp_zero smulLp_one
  inner_smulLp_apply_left)
open ENNReal (ofNat_ne_top)
open TestFunction (ambientToLp ambientToLp_smulLeftCLM coeFn_ambientToLp inner_ambientToLp
  norm_ambientToLp_sq smulLeftCLM smulLeftCLM_apply)

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure] {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-! ### Test fields -/

/-- The commutator of `L_x*` with multiplication by `φ` is the principal symbol at `dφ`, whose
pointwise norm is `|dφ| |η|`. -/
private theorem norm_adjoint_smulLeftCLM_sub_le (hx : Continuous x) (φ ψ : ℂ →ᵇ ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ∀ z, ‖fderiv ℝ φ z‖ ≤ ψ z) (η : TestField) :
    ‖gaugeFixedAdjointToLp μ hx (smulLeftCLM hφ η) -
        smulLp μ 2 ofNat_ne_top φ (gaugeFixedAdjointToLp μ hx η)‖ ≤
      ‖smulLp μ 2 ofNat_ne_top ψ (ambientToLp 2 μ η)‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [Lp.coeFn_sub (gaugeFixedAdjointToLp μ hx (smulLeftCLM hφ η))
      (smulLp μ 2 ofNat_ne_top φ (gaugeFixedAdjointToLp μ hx η)),
    coeFn_gaugeFixedAdjointToLp (μ := μ) hx (smulLeftCLM hφ η),
    coeFn_smulLp ofNat_ne_top φ (gaugeFixedAdjointToLp μ hx η),
    coeFn_gaugeFixedAdjointToLp (μ := μ) hx η, coeFn_smulLp ofNat_ne_top ψ (ambientToLp 2 μ η),
    coeFn_ambientToLp (p := 2) (ν := μ) η] with z h₁ h₂ h₃ h₄ h₅ h₆
  have hψ₀ : 0 ≤ ψ z := (norm_nonneg _).trans (hψ z)
  rw [h₁, Pi.sub_apply, h₂, h₃, h₄, h₅, h₆,
    funext (smulLeftCLM_apply hφ η),
    gaugeFixedAdjoint_fun_smul x (hφ.differentiable (by norm_num) z)
      (η.contDiff.differentiable (by norm_num) z), add_sub_cancel_left,
    ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_gaugeFixedAdjointSymbol]
  simp only [norm_smul, mul_pow, Real.norm_of_nonneg hψ₀]
  gcongr
  exact hψ z

/-- The pointwise norm `|dφ|` of the derivative of a `C²` function `φ` with `|dφ| ≤ C`, as a
bounded continuous function. -/
private def normFDeriv {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) {C : ℝ}
    (hC : ∀ z, ‖fderiv ℝ φ z‖ ≤ C) : ℂ →ᵇ ℝ :=
  .ofNormedAddCommGroup (fun z ↦ ‖fderiv ℝ φ z‖) (hφ.continuous_fderiv (by norm_num)).norm C
    fun z ↦ (norm_norm _).trans_le (hC z)

@[simp]
private theorem normFDeriv_apply {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) {C : ℝ}
    (hC : ∀ z, ‖fderiv ℝ φ z‖ ≤ C) (z : ℂ) : normFDeriv hφ hC z = ‖fderiv ℝ φ z‖ :=
  (rfl)

/-- The localization identity `‖L_x* (φ η)‖² = ⟪L_x* (φ² η), L_x* η⟫ + ‖|dφ| η‖²` in `L²`. -/
private theorem norm_sq_adjoint_smulLeftCLM (hx : Continuous x) (φ dφ : ℂ →ᵇ ℝ)
    (hφ : ContDiff ℝ 2 φ) (hdφ : ∀ z, dφ z = ‖fderiv ℝ φ z‖) (η : TestField) :
    ‖gaugeFixedAdjointToLp μ hx (smulLeftCLM hφ η)‖ ^ 2 =
      ⟪gaugeFixedAdjointToLp μ hx (smulLeftCLM hφ (smulLeftCLM hφ η)),
          gaugeFixedAdjointToLp μ hx η⟫ +
        ‖smulLp μ 2 ofNat_ne_top dφ (ambientToLp 2 μ η)‖ ^ 2 := by
  have hφφ : ⇑(smulLeftCLM hφ (smulLeftCLM hφ η)) = fun t ↦ φ t ^ 2 • η t :=
    funext fun t ↦ by rw [smulLeftCLM_apply, smulLeftCLM_apply, smul_smul, sq]
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def,
    L2.inner_def, ← integral_add (L2.integrable_inner _ _) (L2.integrable_inner _ _)]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_gaugeFixedAdjointToLp (μ := μ) hx (smulLeftCLM hφ η),
    coeFn_gaugeFixedAdjointToLp (μ := μ) hx (smulLeftCLM hφ (smulLeftCLM hφ η)),
    coeFn_gaugeFixedAdjointToLp (μ := μ) hx η, coeFn_smulLp ofNat_ne_top dφ (ambientToLp 2 μ η),
    coeFn_ambientToLp (p := 2) (ν := μ) η] with z h₁ h₂ h₃ h₄ h₅
  rw [h₁, h₂, h₃, h₄, h₅, hφφ, funext (smulLeftCLM_apply hφ η), real_inner_self_eq_norm_sq,
    norm_sq_gaugeFixedAdjoint_fun_smul x (hφ.differentiable (by norm_num) z)
      (η.contDiff.differentiable (by norm_num) z)]
  simp only [real_inner_self_eq_norm_sq, hdφ, norm_smul, norm_norm, mul_pow]

/-- The exterior estimate for `L_x*` applied to `φ η`, for `φ` vanishing on the disc of radius
`R` outside which `|α|² / 4 ≥ a`. -/
private theorem mul_norm_sq_smulLeftCLM_le (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0) {a R : ℝ} (ha : a ≤ 1 / 4)
    (hR : ∀ z, R < ‖z‖ → a ≤ x z 2 ^ 2 + x z 3 ^ 2) (φ : ℂ →ᵇ ℝ) (hφ : ContDiff ℝ 2 φ)
    (hφR : ∀ z, ‖z‖ ≤ R → φ z = 0) (η : TestField) :
    a * ‖ambientToLp 2 μ (smulLeftCLM hφ η)‖ ^ 2 ≤
      ‖gaugeFixedAdjointToLp μ hx.continuous (smulLeftCLM hφ η)‖ ^ 2 := by
  set ζ := smulLeftCLM hφ η
  have hint := mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint (μ := μ) hx ζ.contDiff
    ζ.hasCompactSupport (fun z _ ↦ hsol z) ha fun z hz ↦ hR z <| lt_of_not_ge fun h ↦
      hz (by rw [smulLeftCLM_apply, hφR z h, zero_smul])
  rw [norm_ambientToLp_sq, norm_sq_gaugeFixedAdjointToLp]
  exact hint

/-! ### Approximation of the least-norm weak solution -/

/-- A weak solution orthogonal to the weak kernel of `L_x` is an `L²` limit of `L_x* η_n` for
test fields `η_n`. Under a lower bound for `L_x*`, the `η_n` themselves converge in `L²`. -/
private theorem exists_tendsto_testField (hx : Continuous x) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      c * ∫ z, ‖η z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ)
    {y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (horth : ∀ u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
      ∫ z, ⟪y z, u z⟫ ∂μ = 0) :
    ∃ (η : ℕ → TestField) (u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ),
      Tendsto (fun n ↦ ambientToLp 2 μ (η n)) atTop (𝓝 u) ∧
        Tendsto (fun n ↦ gaugeFixedAdjointToLp μ hx (η n)) atTop (𝓝 y) := by
  set S := gaugeFixedAdjointToLp μ hx
  -- `y` lies in `(range S)ᗮᗮ`, the closure of the range of `S`.
  have hy : y ∈ (LinearMap.range S)ᗮᗮ := by
    refine (Submodule.mem_orthogonal _ _).2 fun u hu ↦ ?_
    rw [real_inner_comm, L2.inner_def]
    exact horth u ((mem_orthogonal_range_gaugeFixedAdjointToLp_iff hx u).1 hu)
  rw [Submodule.orthogonal_orthogonal_eq_closure, ← SetLike.mem_coe,
    Submodule.topologicalClosure_coe] at hy
  obtain ⟨v, hv, hvy⟩ := mem_closure_iff_seq_limit.1 hy
  choose η hη using hv
  have hSη : Tendsto (fun n ↦ S (η n)) atTop (𝓝 y) := by simpa only [hη] using hvy
  -- The lower bound makes `ambientToLp 2 μ (η n)` a Cauchy sequence.
  have hcau : CauchySeq fun n ↦ ambientToLp 2 μ (η n) := by
    refine Metric.cauchySeq_iff.2 fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hSη.cauchySeq (√c * ε) (by positivity)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have h := sqrt_mul_norm_ambientToLp_le hx hc.le hgap (η m - η n)
    rw [map_sub, map_sub, ← dist_eq_norm, ← dist_eq_norm] at h
    exact lt_of_mul_lt_mul_left (h.trans_lt (hN m hm n hn)) (Real.sqrt_nonneg c)
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hcau
  exact ⟨η, u, hu, hSη⟩

/-! ### Limits of the multiplier identities -/

/-- Along the approximating test fields, `‖L_x* (φ η_n)‖²` converges to
`⟪φ f, φ u⟫ + ‖|dφ| u‖²`. -/
private theorem tendsto_norm_sq_adjoint_smulLeftCLM (hx : Continuous x)
    {f y u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} {η : ℕ → TestField}
    (hT : Tendsto (fun n ↦ ambientToLp 2 μ (η n)) atTop (𝓝 u))
    (hS : Tendsto (fun n ↦ gaugeFixedAdjointToLp μ hx (η n)) atTop (𝓝 y))
    (hweak : ∀ ζ : TestField, ⟪y, gaugeFixedAdjointToLp μ hx ζ⟫ = ⟪f, ambientToLp 2 μ ζ⟫)
    (φ dφ : ℂ →ᵇ ℝ)
    (hφ : ContDiff ℝ 2 φ) (hdφ : ∀ z, dφ z = ‖fderiv ℝ φ z‖) :
    Tendsto (fun n ↦ ‖gaugeFixedAdjointToLp μ hx (smulLeftCLM hφ (η n))‖ ^ 2) atTop
      (𝓝 (⟪smulLp μ 2 ofNat_ne_top φ f, smulLp μ 2 ofNat_ne_top φ u⟫ +
        ‖smulLp μ 2 ofNat_ne_top dφ u‖ ^ 2)) := by
  refine Tendsto.congr (fun n ↦ (norm_sq_adjoint_smulLeftCLM hx φ dφ hφ hdφ (η n)).symm) ?_
  refine Tendsto.add ?_ ((((smulLp μ 2 ofNat_ne_top dφ).continuous.tendsto u).comp hT).norm.pow 2)
  set Φ := smulLp μ 2 ofNat_ne_top φ (E := EuclideanSpace ℝ (Fin 4))
  set S := gaugeFixedAdjointToLp μ hx
  -- Split `⟪S (φ² η_n), S η_n⟫` into the weak pairing with `y` and an error term.
  have hsplit (n : ℕ) : ⟪f, Φ (Φ (ambientToLp 2 μ (η n)))⟫ +
      ⟪S (smulLeftCLM hφ (smulLeftCLM hφ (η n))), S (η n) - y⟫ =
        ⟪S (smulLeftCLM hφ (smulLeftCLM hφ (η n))), S (η n)⟫ := by
    rw [inner_sub_right, real_inner_comm y, hweak, ambientToLp_smulLeftCLM (p := 2) ofNat_ne_top,
      ambientToLp_smulLeftCLM (p := 2) ofNat_ne_top]
    ring
  refine Tendsto.congr hsplit ?_
  have hφφ : ⟪Φ f, Φ u⟫ = ⟪f, Φ (Φ u)⟫ := by
    have hstar : star φ = φ := by
      ext z
      simp
    rw [inner_smulLp_apply_left, hstar]
  rw [← add_zero ⟪Φ f, Φ u⟫, hφφ]
  refine Tendsto.add (tendsto_const_nhds.inner
    ((Φ.continuous.tendsto _).comp ((Φ.continuous.tendsto u).comp hT))) ?_
  -- The error term tends to zero, since `S (φ² η_n)` stays bounded.
  have hbound (ζ : TestField) :
      ‖S (smulLeftCLM hφ ζ)‖ ≤ ‖φ‖ * ‖S ζ‖ + ‖dφ‖ * ‖ambientToLp 2 μ ζ‖ := by
    calc ‖S (smulLeftCLM hφ ζ)‖ ≤ ‖Φ (S ζ)‖ + ‖S (smulLeftCLM hφ ζ) - Φ (S ζ)‖ :=
          norm_le_insert' _ _
      _ ≤ ‖φ‖ * ‖S ζ‖ + ‖dφ‖ * ‖ambientToLp 2 μ ζ‖ :=
          add_le_add (norm_smulLp_apply_le _ _)
            ((norm_adjoint_smulLeftCLM_sub_le hx φ dφ hφ (fun z ↦ (hdφ z).ge) ζ).trans
            (norm_smulLp_apply_le _ _))
  have hbound₂ (n : ℕ) : ‖S (smulLeftCLM hφ (smulLeftCLM hφ (η n)))‖ ≤
      ‖φ‖ * (‖φ‖ * ‖S (η n)‖ + ‖dφ‖ * ‖ambientToLp 2 μ (η n)‖) +
        ‖dφ‖ * (‖φ‖ * ‖ambientToLp 2 μ (η n)‖) := by
    refine (hbound _).trans (add_le_add (mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)))
    rw [ambientToLp_smulLeftCLM (p := 2) ofNat_ne_top]
    exact norm_smulLp_apply_le _ _
  refine squeeze_zero_norm (fun n ↦ (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (hbound₂ n) (norm_nonneg _))) ?_
  have h0 : Tendsto (fun n ↦ ‖S (η n) - y‖) atTop (𝓝 0) := by
    simpa using (tendsto_sub_nhds_zero_iff.2 hS).norm
  simpa using (((((hS.norm.const_mul ‖φ‖).add (hT.norm.const_mul ‖dφ‖)).const_mul ‖φ‖).add
    ((hT.norm.const_mul ‖φ‖).const_mul ‖dφ‖)).mul h0)

/-- **The exterior multiplier inequality.** For `φ` vanishing on the disc of radius `R` outside
which `|α|² / 4 ≥ a`, `a ‖φ u‖² ≤ ⟪φ f, φ u⟫ + ‖|dφ| u‖²`. -/
private theorem mul_norm_sq_smulLp_le (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    {a R : ℝ} (ha : a ≤ 1 / 4) (hR : ∀ z, R < ‖z‖ → a ≤ x z 2 ^ 2 + x z 3 ^ 2)
    {f y u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} {η : ℕ → TestField}
    (hT : Tendsto (fun n ↦ ambientToLp 2 μ (η n)) atTop (𝓝 u))
    (hS : Tendsto (fun n ↦ gaugeFixedAdjointToLp μ hx.continuous (η n)) atTop (𝓝 y))
    (hweak : ∀ ζ : TestField, ⟪y, gaugeFixedAdjointToLp μ hx.continuous ζ⟫ = ⟪f, ambientToLp 2 μ ζ⟫)
    (φ dφ : ℂ →ᵇ ℝ)
    (hφ : ContDiff ℝ 2 φ) (hdφ : ∀ z, dφ z = ‖fderiv ℝ φ z‖) (hφR : ∀ z, ‖z‖ ≤ R → φ z = 0) :
    a * ‖smulLp μ 2 ofNat_ne_top φ u‖ ^ 2 ≤
      ⟪smulLp μ 2 ofNat_ne_top φ f, smulLp μ 2 ofNat_ne_top φ u⟫ +
        ‖smulLp μ 2 ofNat_ne_top dφ u‖ ^ 2 := by
  have hl : Tendsto (fun n ↦ a * ‖ambientToLp 2 μ (smulLeftCLM hφ (η n))‖ ^ 2) atTop
      (𝓝 (a * ‖smulLp μ 2 ofNat_ne_top φ u‖ ^ 2)) := by
    refine Tendsto.congr (fun n ↦ ?_)
      (((((smulLp μ 2 ofNat_ne_top φ).continuous.tendsto u).comp hT).norm.pow 2).const_mul a)
    rw [Function.comp_apply, ambientToLp_smulLeftCLM (p := 2) ofNat_ne_top]
  exact le_of_tendsto_of_tendsto' hl
    (tendsto_norm_sq_adjoint_smulLeftCLM hx.continuous hT hS hweak φ dφ hφ hdφ) fun n ↦
      mul_norm_sq_smulLeftCLM_le hx hsol ha hR φ hφ hφR (η n)

/-- The weighted norm of `y`: `‖φ y‖ ≤ (⟪φ f, φ u⟫ + ‖|dφ| u‖²)^(1/2) + ‖|dφ| u‖`. -/
private theorem norm_smulLp_le_sqrt_add (hx : Continuous x)
    {f y u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} {η : ℕ → TestField}
    (hT : Tendsto (fun n ↦ ambientToLp 2 μ (η n)) atTop (𝓝 u))
    (hS : Tendsto (fun n ↦ gaugeFixedAdjointToLp μ hx (η n)) atTop (𝓝 y))
    (hweak : ∀ ζ : TestField, ⟪y, gaugeFixedAdjointToLp μ hx ζ⟫ = ⟪f, ambientToLp 2 μ ζ⟫)
    (φ dφ : ℂ →ᵇ ℝ)
    (hφ : ContDiff ℝ 2 φ) (hdφ : ∀ z, dφ z = ‖fderiv ℝ φ z‖) :
    ‖smulLp μ 2 ofNat_ne_top φ y‖ ≤
      √(⟪smulLp μ 2 ofNat_ne_top φ f, smulLp μ 2 ofNat_ne_top φ u⟫ +
        ‖smulLp μ 2 ofNat_ne_top dφ u‖ ^ 2) + ‖smulLp μ 2 ofNat_ne_top dφ u‖ := by
  have hl : Tendsto (fun n ↦ ‖smulLp μ 2 ofNat_ne_top φ (gaugeFixedAdjointToLp μ hx (η n))‖) atTop
      (𝓝 ‖smulLp μ 2 ofNat_ne_top φ y‖) :=
    (((smulLp μ 2 ofNat_ne_top φ).continuous.tendsto y).comp hS).norm
  have hΛ := tendsto_norm_sq_adjoint_smulLeftCLM hx hT hS hweak φ dφ hφ hdφ
  have hd : Tendsto (fun n ↦ ‖smulLp μ 2 ofNat_ne_top dφ (ambientToLp 2 μ (η n))‖) atTop
      (𝓝 ‖smulLp μ 2 ofNat_ne_top dφ u‖) :=
    (((smulLp μ 2 ofNat_ne_top dφ).continuous.tendsto u).comp hT).norm
  have hr := hΛ.sqrt.add hd
  refine le_of_tendsto_of_tendsto' hl hr fun n ↦ ?_
  have hsq : √(‖gaugeFixedAdjointToLp μ hx (smulLeftCLM hφ (η n))‖ ^ 2) =
      ‖gaugeFixedAdjointToLp μ hx (smulLeftCLM hφ (η n))‖ := Real.sqrt_sq (norm_nonneg _)
  have hc := norm_adjoint_smulLeftCLM_sub_le (μ := μ) hx φ dφ hφ (fun z ↦ (hdφ z).ge) (η n)
  have hi := norm_le_insert (gaugeFixedAdjointToLp μ hx (smulLeftCLM hφ (η n)))
    (smulLp μ 2 ofNat_ne_top φ (gaugeFixedAdjointToLp μ hx (η n)))
  rw [hsq]
  linarith

/-- Testing with `φ = 1`: `‖y‖² = ⟪f, u⟫`. -/
private theorem norm_sq_eq_inner_of_tendsto (hx : Continuous x)
    {f y u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} {η : ℕ → TestField}
    (hT : Tendsto (fun n ↦ ambientToLp 2 μ (η n)) atTop (𝓝 u))
    (hS : Tendsto (fun n ↦ gaugeFixedAdjointToLp μ hx (η n)) atTop (𝓝 y))
    (hweak : ∀ ζ : TestField, ⟪y, gaugeFixedAdjointToLp μ hx ζ⟫ = ⟪f, ambientToLp 2 μ ζ⟫) :
    ‖y‖ ^ 2 = ⟪f, u⟫ := by
  have h1 : ContDiff ℝ 2 ⇑(1 : ℂ →ᵇ ℝ) := by
    rw [FunLike.coe_one]
    exact contDiff_const
  have hd (z : ℂ) : (0 : ℂ →ᵇ ℝ) z = ‖fderiv ℝ ⇑(1 : ℂ →ᵇ ℝ) z‖ := by
    simp [FunLike.coe_one, Pi.one_def]
  have h := tendsto_norm_sq_adjoint_smulLeftCLM hx hT hS hweak _ _ h1 hd
  have hη (ζ : TestField) : smulLeftCLM h1 ζ = ζ :=
    TestFunction.ext fun z ↦ by rw [smulLeftCLM_apply, FunLike.coe_one, Pi.one_apply, one_smul]
  simp only [hη, smulLp_one, smulLp_zero, one_apply_eq_self, zero_apply, norm_zero] at h
  rw [tendsto_nhds_unique (hS.norm.pow 2) h]
  ring

/-! ### The estimate at a fixed bounded weight -/

/-- Absorption: `α X² ≤ A F X + B F²` with `α > 0` gives `X ≤ (A / α + B / α + 1) F`. -/
private theorem le_mul_of_mul_sq_le {X F α A B : ℝ} (hF : 0 ≤ F) (hα : 0 < α) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (h : α * X ^ 2 ≤ A * F * X + B * F ^ 2) : X ≤ (A / α + B / α + 1) * F := by
  have hA' : 0 ≤ A / α := div_nonneg hA hα.le
  have hB' : 0 ≤ B / α := div_nonneg hB hα.le
  have h' : X ^ 2 ≤ A / α * F * X + B / α * F ^ 2 := by
    have e : A / α * F * X + B / α * F ^ 2 = (A * F * X + B * F ^ 2) / α := by
      field_simp
    rw [e, le_div_iff₀ hα]
    linarith
  rcases le_or_gt X F with hXF | hXF
  · nlinarith
  · have hX0 : 0 < X := hF.trans_lt hXF
    have h2 : X * X ≤ X * ((A / α + B / α) * F) := by
      have : B / α * F ^ 2 ≤ B / α * F * X := by
        rw [sq, ← mul_assoc]; exact mul_le_mul_of_nonneg_left hXF.le (by positivity)
      nlinarith
    have := le_of_mul_le_mul_left h2 hX0
    nlinarith

/-- The constant in the weighted bound for the `L²` limit `u` of the approximating test fields
(`norm_smulLp_weight_le`). -/
private def limitConst (a c c₀ M₀ M₁ : ℝ) : ℝ :=
  (1 + 2 * c * (M₁ / c₀)) / (a - c ^ 2) + (M₁ / c₀) ^ 2 / (a - c ^ 2) + 1 + M₀ / c₀

private theorem limitConst_nonneg {a c c₀ M₀ M₁ : ℝ} (hc : 0 ≤ c) (hca : c ^ 2 < a)
    (hc₀ : 0 < c₀) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) : 0 ≤ limitConst a c c₀ M₀ M₁ := by
  have := sub_pos.2 hca
  unfold limitConst
  positivity

/-- The constant in the weighted bound for `y`, given the constant `K` of the weighted bound for
the limit `u` (`norm_smulLp_weight_le_of_norm_smulLp_le`). -/
private def solutionConst (c K : ℝ) : ℝ :=
  √(K + c ^ 2 * K ^ 2) + c * K

private theorem solutionConst_nonneg {c K : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K) :
    0 ≤ solutionConst c K := by
  unfold solutionConst
  positivity

/-- **The exterior bound for the `L²` limit `u` of the approximating test fields.** Let `w` be a
bounded `C²` weight with `|dw| ≤ c w`, `c² < a`, and let `β` be a cutoff equal to `1` on the
disc of radius `R`, outside which `|α|² / 4 ≥ a`. If `|dβ| w ≤ M₁`, then `‖(1 - β) w u‖` is
bounded by a constant multiple of any `F ≥ ‖f‖, ‖w f‖`. -/
private theorem norm_smulLp_one_sub_mul_le (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    {a R c c₀ M₁ F : ℝ} (ha : a ≤ 1 / 4) (hR : ∀ z, R < ‖z‖ → a ≤ x z 2 ^ 2 + x z 3 ^ 2)
    (hc : 0 ≤ c) (hca : c ^ 2 < a) (hc₀ : 0 < c₀) (hM₁ : 0 ≤ M₁)
    {f y u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} {η : ℕ → TestField}
    (hT : Tendsto (fun n ↦ ambientToLp 2 μ (η n)) atTop (𝓝 u))
    (hS : Tendsto (fun n ↦ gaugeFixedAdjointToLp μ hx.continuous (η n)) atTop (𝓝 y))
    (hweak : ∀ ζ : TestField, ⟪y, gaugeFixedAdjointToLp μ hx.continuous ζ⟫ = ⟪f, ambientToLp 2 μ ζ⟫)
    (hu : ‖u‖ ≤ ‖f‖ / c₀) (β w : ℂ →ᵇ ℝ) (hβ : ContDiff ℝ 2 β) (hβ₀ : ∀ z, 0 ≤ β z)
    (hβ₁ : ∀ z, β z ≤ 1) (hβR : ∀ z, ‖z‖ ≤ R → β z = 1) (hw : ContDiff ℝ 2 w)
    (hw₀ : ∀ z, 0 ≤ w z) (hdw : ∀ z, ‖fderiv ℝ w z‖ ≤ c * w z)
    (hdβw : ∀ z, ‖fderiv ℝ β z‖ * w z ≤ M₁) (hFf : ‖f‖ ≤ F)
    (hFw : ‖smulLp μ 2 ofNat_ne_top w f‖ ≤ F) :
    ‖smulLp μ 2 ofNat_ne_top ((1 - β) * w) u‖ ≤
      ((1 + 2 * c * (M₁ / c₀)) / (a - c ^ 2) + (M₁ / c₀) ^ 2 / (a - c ^ 2) + 1) * F := by
  have hF : 0 ≤ F := (norm_nonneg _).trans hFf
  -- The cut-off weight `φ = (1 - β) w` and the norm of its derivative.
  set φ : ℂ →ᵇ ℝ := (1 - β) * w
  have hφe : (φ : ℂ → ℝ) = fun t ↦ (1 - β t) * w t := by
    ext t
    simp [φ]
  have hφ : ContDiff ℝ 2 φ := hφe ▸ (contDiff_const.sub hβ).mul hw
  -- `|dφ| ≤ c (1 - β) w + |dβ| w`, using `|dw| ≤ c w`.
  have hdφ (z : ℂ) : ‖fderiv ℝ φ z‖ ≤ c * φ z + M₁ := by
    rw [hφe, fderiv_fun_mul (((hβ.differentiable (by norm_num)) z).const_sub 1)
      (hw.differentiable (by norm_num) z), fderiv_const_sub]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, norm_neg, Real.norm_of_nonneg (sub_nonneg.2 (hβ₁ z)),
      Real.norm_of_nonneg (hw₀ z)]
    nlinarith [mul_le_mul_of_nonneg_left (hdw z) (sub_nonneg.2 (hβ₁ z)), hdβw z]
  have hφw (z : ℂ) : |φ z| ≤ w z := by
    rw [hφe, abs_of_nonneg (mul_nonneg (sub_nonneg.2 (hβ₁ z)) (hw₀ z))]
    nlinarith [hβ₀ z, hw₀ z]
  have hdφb (z : ℂ) : ‖fderiv ℝ φ z‖ ≤ c * ‖w‖ + M₁ := by
    have h1 := w.norm_coe_le_norm z
    rw [Real.norm_of_nonneg (hw₀ z)] at h1
    exact (hdφ z).trans (by nlinarith [hφw z, le_abs_self (φ z)])
  set dφ : ℂ →ᵇ ℝ := normFDeriv hφ hdφb
  -- The exterior multiplier inequality for `φ`.
  set X := ‖smulLp μ 2 ofNat_ne_top φ u‖
  have hB := mul_norm_sq_smulLp_le hx hsol ha hR hT hS hweak φ dφ hφ (normFDeriv_apply hφ hdφb)
      fun z hz ↦ by rw [hφe]; simp [hβR z hz]
  have hin : ⟪smulLp μ 2 ofNat_ne_top φ f, smulLp μ 2 ofNat_ne_top φ u⟫ ≤ F * X :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      ((norm_smulLp_apply_le_of_abs_le hφw f).trans hFw) (norm_nonneg _))
  have hdu : ‖smulLp μ 2 ofNat_ne_top dφ u‖ ≤ c * X + M₁ * ‖u‖ := by
    refine (norm_smulLp_apply_le_of_abs_le (ψ := c • φ + .const ℂ M₁) (fun z ↦ ?_) u).trans ?_
    · simpa [dφ] using hdφ z
    · rw [smulLp_add, smulLp_smul, smulLp_const, _root_.add_apply, _root_.smul_apply,
        _root_.smul_apply, one_apply_eq_self]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hc, Real.norm_of_nonneg hM₁]
  have hD : M₁ * ‖u‖ ≤ M₁ / c₀ * F :=
    (mul_le_mul_of_nonneg_left (hu.trans (div_le_div_of_nonneg_right hFf hc₀.le)) hM₁).trans_eq
      (by ring)
  refine le_mul_of_mul_sq_le hF (by linarith) (by positivity) (by positivity) ?_
  have hX0 : 0 ≤ X := norm_nonneg _
  have hdu0 : 0 ≤ ‖smulLp μ 2 ofNat_ne_top dφ u‖ := norm_nonneg _
  have hu0 : 0 ≤ M₁ * ‖u‖ := by positivity
  nlinarith [mul_le_mul hdu hdu hdu0 (by positivity), mul_le_mul_of_nonneg_left hD hX0,
    mul_le_mul hD hD hu0 (by positivity)]

/-- **The weighted bound for the `L²` limit `u` of the approximating test fields.** Let `w` be a
bounded `C²` weight with `|dw| ≤ c w`, `c² < a`, and let `β` be a cutoff equal to `1` on the
disc of radius `R`, outside which `|α|² / 4 ≥ a`. If `β w ≤ M₀` and `|dβ| w ≤ M₁`, then `‖w u‖`
is bounded by a constant multiple of any `F ≥ ‖f‖, ‖w f‖`. -/
private theorem norm_smulLp_weight_le (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    {a R c c₀ M₀ M₁ F : ℝ} (ha : a ≤ 1 / 4) (hR : ∀ z, R < ‖z‖ → a ≤ x z 2 ^ 2 + x z 3 ^ 2)
    (hc : 0 ≤ c) (hca : c ^ 2 < a) (hc₀ : 0 < c₀) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    {f y u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} {η : ℕ → TestField}
    (hT : Tendsto (fun n ↦ ambientToLp 2 μ (η n)) atTop (𝓝 u))
    (hS : Tendsto (fun n ↦ gaugeFixedAdjointToLp μ hx.continuous (η n)) atTop (𝓝 y))
    (hweak : ∀ ζ : TestField, ⟪y, gaugeFixedAdjointToLp μ hx.continuous ζ⟫ = ⟪f, ambientToLp 2 μ ζ⟫)
    (hu : ‖u‖ ≤ ‖f‖ / c₀) (β w : ℂ →ᵇ ℝ) (hβ : ContDiff ℝ 2 β) (hβ₀ : ∀ z, 0 ≤ β z)
    (hβ₁ : ∀ z, β z ≤ 1) (hβR : ∀ z, ‖z‖ ≤ R → β z = 1) (hw : ContDiff ℝ 2 w)
    (hw₀ : ∀ z, 0 ≤ w z) (hdw : ∀ z, ‖fderiv ℝ w z‖ ≤ c * w z) (hβw : ∀ z, β z * w z ≤ M₀)
    (hdβw : ∀ z, ‖fderiv ℝ β z‖ * w z ≤ M₁) (hFf : ‖f‖ ≤ F)
    (hFw : ‖smulLp μ 2 ofNat_ne_top w f‖ ≤ F) :
    ‖smulLp μ 2 ofNat_ne_top w u‖ ≤ limitConst a c c₀ M₀ M₁ * F := by
  have hX := norm_smulLp_one_sub_mul_le hx hsol ha hR hc hca hc₀ hM₁ hT hS hweak hu β w hβ hβ₀
    hβ₁ hβR hw hw₀ hdw hdβw hFf hFw
  -- Split `w = (1 - β) w + β w`; the second part is bounded by `M₀` and supported in the core.
  have hsplit : smulLp μ 2 ofNat_ne_top w u =
      smulLp μ 2 ofNat_ne_top ((1 - β) * w) u + smulLp μ 2 ofNat_ne_top (β * w) u := by
    rw [← _root_.add_apply, ← smulLp_add, ← add_mul, sub_add_cancel, one_mul]
  have hβu : ‖smulLp μ 2 ofNat_ne_top (β * w) u‖ ≤ M₀ * ‖u‖ := by
    refine (norm_smulLp_apply_le_of_abs_le (ψ := .const ℂ M₀) (fun z ↦ ?_) u).trans ?_
    · simpa [abs_of_nonneg (mul_nonneg (hβ₀ z) (hw₀ z))] using hβw z
    · rw [smulLp_const, _root_.smul_apply, one_apply_eq_self, norm_smul,
        Real.norm_of_nonneg hM₀]
  have hM₀u : M₀ * ‖u‖ ≤ M₀ / c₀ * F :=
    (mul_le_mul_of_nonneg_left (hu.trans (div_le_div_of_nonneg_right hFf hc₀.le)) hM₀).trans_eq
      (by ring)
  rw [hsplit, limitConst]
  refine (norm_add_le _ _).trans ?_
  nlinarith

/-- **The weighted bound for `y`** at a bounded `C²` weight `w` with `|dw| ≤ c w`, from the
weighted bound `‖w u‖ ≤ K F` for the `L²` limit `u` of the approximating test fields. -/
private theorem norm_smulLp_weight_le_of_norm_smulLp_le (hx : Continuous x) {c K F : ℝ}
    (hc : 0 ≤ c) {f y u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} {η : ℕ → TestField}
    (hT : Tendsto (fun n ↦ ambientToLp 2 μ (η n)) atTop (𝓝 u))
    (hS : Tendsto (fun n ↦ gaugeFixedAdjointToLp μ hx (η n)) atTop (𝓝 y))
    (hweak : ∀ ζ : TestField, ⟪y, gaugeFixedAdjointToLp μ hx ζ⟫ = ⟪f, ambientToLp 2 μ ζ⟫)
    (w : ℂ →ᵇ ℝ)
    (hw : ContDiff ℝ 2 w) (hw₀ : ∀ z, 0 ≤ w z) (hdw : ∀ z, ‖fderiv ℝ w z‖ ≤ c * w z)
    (hF : 0 ≤ F) (hK : 0 ≤ K) (hFw : ‖smulLp μ 2 ofNat_ne_top w f‖ ≤ F)
    (hWu : ‖smulLp μ 2 ofNat_ne_top w u‖ ≤ K * F) :
    ‖smulLp μ 2 ofNat_ne_top w y‖ ≤ solutionConst c K * F := by
  have hdwb (z : ℂ) : ‖fderiv ℝ w z‖ ≤ c * ‖w‖ := by
    have h1 := w.norm_coe_le_norm z
    rw [Real.norm_of_nonneg (hw₀ z)] at h1
    exact (hdw z).trans (mul_le_mul_of_nonneg_left h1 hc)
  set dw : ℂ →ᵇ ℝ := normFDeriv hw hdwb
  have hdu : ‖smulLp μ 2 ofNat_ne_top dw u‖ ≤ c * (K * F) := by
    refine (norm_smulLp_apply_le_of_abs_le (ψ := c • w) (fun z ↦ ?_) u).trans ?_
    · simpa [dw] using hdw z
    · rw [smulLp_smul, _root_.smul_apply, norm_smul, Real.norm_of_nonneg hc]
      exact mul_le_mul_of_nonneg_left hWu hc
  have hin : ⟪smulLp μ 2 ofNat_ne_top w f, smulLp μ 2 ofNat_ne_top w u⟫ ≤ F * (K * F) :=
    (real_inner_le_norm _ _).trans (mul_le_mul hFw hWu (norm_nonneg _) hF)
  have hsq : √(⟪smulLp μ 2 ofNat_ne_top w f, smulLp μ 2 ofNat_ne_top w u⟫ +
      ‖smulLp μ 2 ofNat_ne_top dw u‖ ^ 2) ≤ √(K + c ^ 2 * K ^ 2) * F := by
    rw [← Real.sqrt_sq hF, ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    nlinarith [mul_le_mul hdu hdu (norm_nonneg _) (by positivity)]
  refine (norm_smulLp_le_sqrt_add hx hT hS hweak w dw hw (normFDeriv_apply hw hdwb)).trans ?_
  rw [solutionConst]
  nlinarith

/-! ### The weighted estimate -/

/-- The unweighted bound `‖u‖ ≤ ‖f‖ / c₀` from `‖y‖² = ⟪f, u⟫` and the lower bound
`√c₀ ‖u‖ ≤ ‖y‖`. -/
private theorem norm_le_div_of_tendsto (hx : Continuous x) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hgap : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      c₀ * ∫ z, ‖η z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ)
    {f y u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} {η : ℕ → TestField}
    (hT : Tendsto (fun n ↦ ambientToLp 2 μ (η n)) atTop (𝓝 u))
    (hS : Tendsto (fun n ↦ gaugeFixedAdjointToLp μ hx (η n)) atTop (𝓝 y))
    (hweak : ∀ ζ : TestField, ⟪y, gaugeFixedAdjointToLp μ hx ζ⟫ = ⟪f, ambientToLp 2 μ ζ⟫) :
    ‖u‖ ≤ ‖f‖ / c₀ := by
  have hy : ‖y‖ ^ 2 ≤ ‖f‖ * ‖u‖ :=
    (norm_sq_eq_inner_of_tendsto hx hT hS hweak).trans_le (real_inner_le_norm f u)
  have hg : √c₀ * ‖u‖ ≤ ‖y‖ := le_of_tendsto_of_tendsto' (hT.norm.const_mul _) hS.norm
    fun n ↦ sqrt_mul_norm_ambientToLp_le hx hc₀.le hgap (η n)
  have hs : √c₀ ^ 2 = c₀ := Real.sq_sqrt hc₀.le
  rw [le_div_iff₀ hc₀]
  rcases (norm_nonneg u).eq_or_lt with h0 | h0
  · rw [← h0, zero_mul]
    exact norm_nonneg f
  · have h2 : (√c₀ * ‖u‖) ^ 2 ≤ ‖f‖ * ‖u‖ :=
      (pow_le_pow_left₀ (by positivity) hg 2).trans hy
    rw [mul_pow, hs] at h2
    nlinarith [Real.sqrt_nonneg c₀]

/-- The estimate at the regularized weight `E / (1 + ε E)`, uniformly in `ε > 0`. -/
private theorem eLpNorm_boundedExpWeight_smul_le (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    {a R c c₀ M₀ M₁ ε : ℝ} (ha : a ≤ 1 / 4) (hR : ∀ z, R < ‖z‖ → a ≤ x z 2 ^ 2 + x z 3 ^ 2)
    (hc : 0 ≤ c) (hca : c ^ 2 < a) (hc₀ : 0 < c₀) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hε : 0 < ε)
    {f y u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} {η : ℕ → TestField}
    (hT : Tendsto (fun n ↦ ambientToLp 2 μ (η n)) atTop (𝓝 u))
    (hS : Tendsto (fun n ↦ gaugeFixedAdjointToLp μ hx.continuous (η n)) atTop (𝓝 y))
    (hweak : ∀ ζ : TestField, ⟪y, gaugeFixedAdjointToLp μ hx.continuous ζ⟫ = ⟪f, ambientToLp 2 μ ζ⟫)
    (hu : ‖u‖ ≤ ‖f‖ / c₀) (β : ℂ →ᵇ ℝ) (hβ : ContDiff ℝ 2 β) (hβ₀ : ∀ z, 0 ≤ β z)
    (hβ₁ : ∀ z, β z ≤ 1) (hβR : ∀ z, ‖z‖ ≤ R → β z = 1)
    (hβE : ∀ z, β z * Real.exp (c * √(1 + ‖z‖ ^ 2)) ≤ M₀)
    (hdβE : ∀ z, ‖fderiv ℝ β z‖ * Real.exp (c * √(1 + ‖z‖ ^ 2)) ≤ M₁)
    (hfin : eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 μ ≠ ⊤)
    (hFf : ‖f‖ ≤ (eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 μ).toReal) :
    eLpNorm (fun z ↦ boundedExpWeight c ε z • y z) 2 μ ≤ ENNReal.ofReal
      (solutionConst c (limitConst a c c₀ M₀ M₁) *
        (eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 μ).toReal) := by
  have hw₀ := boundedExpWeight_nonneg (F := ℂ) (c := c) hε.le
  set w : ℂ →ᵇ ℝ := .ofNormedAddCommGroup (boundedExpWeight (F := ℂ) c ε)
    (contDiff_boundedExpWeight (n := 0) hε.le).continuous
    ε⁻¹ fun z ↦ by rw [Real.norm_of_nonneg (hw₀ z)]; exact boundedExpWeight_le_inv hε z
  have hwe : (w : ℂ → ℝ) = boundedExpWeight c ε :=
    BoundedContinuousFunction.coe_ofNormedAddCommGroup _ _ _ _
  have hwE (z : ℂ) : w z ≤ Real.exp (c * √(1 + ‖z‖ ^ 2)) := hwe ▸ boundedExpWeight_le hε.le z
  have hdw (z : ℂ) : ‖fderiv ℝ w z‖ ≤ c * w z := by
    simpa only [hwe, abs_of_nonneg hc] using norm_fderiv_boundedExpWeight_le (c := c) hε.le z
  have hFw :
      ‖smulLp μ 2 ofNat_ne_top w f‖ ≤
        (eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 μ).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_smulLp ofNat_ne_top w f)]
    refine ENNReal.toReal_mono hfin (eLpNorm_mono (w.continuous.aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable f)) fun z ↦ ?_)
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (hwe ▸ hw₀ z),
      Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (hwE z) (norm_nonneg _)
  have hWu := norm_smulLp_weight_le hx hsol ha hR hc hca hc₀ hM₀ hM₁ hT hS hweak hu β w hβ hβ₀ hβ₁
    hβR (hwe ▸ contDiff_boundedExpWeight hε.le) (hwe ▸ hw₀) hdw
    (fun z ↦ (mul_le_mul_of_nonneg_left (hwE z) (hβ₀ z)).trans (hβE z))
    (fun z ↦ (mul_le_mul_of_nonneg_left (hwE z) (norm_nonneg _)).trans (hdβE z)) hFf hFw
  have hWy := norm_smulLp_weight_le_of_norm_smulLp_le hx.continuous hc hT hS hweak w
    (hwe ▸ contDiff_boundedExpWeight hε.le) (hwe ▸ hw₀) hdw ENNReal.toReal_nonneg
    (limitConst_nonneg hc hca hc₀ hM₀ hM₁) hFw hWu
  rw [← hwe, ← eLpNorm_congr_ae (coeFn_smulLp ofNat_ne_top w y),
    ← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _),
    ← Lp.norm_def]
  exact ENNReal.ofReal_le_ofReal hWy

/-- **Exponential decay of the least-norm weak solution at a plane vortex.** Let `x` be a `C¹`
solution of the plane vortex equation with `|α| → 1` at infinity, and let `0 ≤ c < 1/2`. There
is a constant `K`, depending only on `x` and `c`, such that every `y ∈ L²` which is a weak
solution of `L_x y = f` and is orthogonal to the weak kernel of `L_x` satisfies

`‖exp(c ρ) y‖₂ ≤ K ‖exp(c ρ) f‖₂`,  `ρ(z) = √(1 + |z|²)`.

The right side may be infinite. The weak right inverse of
`exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq` produces such `y` from every
`f ∈ L²`. -/
theorem exists_eLpNorm_exp_smul_le_mul_eLpNorm_exp_smul (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {c : ℝ} (hc : 0 ≤ c) (hc' : c < 1 / 2) :
    ∃ K : ℝ≥0, ∀ f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ) →
      (∀ u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
        ∫ z, ⟪y z, u z⟫ ∂μ = 0) →
      eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) 2 μ ≤
        K * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 μ := by
  obtain ⟨c₀, hc₀, hgap⟩ :=
    exists_pos_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint (μ := μ) hx hsol hlim
  -- The exterior mass `a`, strictly between `c²` and `1/4`, and its radius `R`.
  have hc2 : c ^ 2 < 1 / 4 := by nlinarith
  obtain ⟨R, hR₀, hR⟩ := exists_exterior_lt_mass hlim (a := (c ^ 2 + 1 / 4) / 2) (by linarith)
  -- A cutoff `β = 1` on the disc of radius `R`, and the constants of the core region.
  set E : ℂ → ℝ := fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2))
  have hEc : Continuous E := (contDiff_exp_mul_sqrt_add_norm_sq (n := 0) c one_pos).continuous
  let b : ContDiffBump (0 : ℂ) := ⟨R, R + 1, hR₀, by linarith⟩
  have hb : ContDiff ℝ 2 b := b.contDiff
  obtain ⟨M₀, hM₀⟩ := (b.continuous.mul hEc).bounded_above_of_compact_support
    (b.hasCompactSupport.mul_right (f' := E))
  obtain ⟨M₁, hM₁⟩ :=
    ((hb.continuous_fderiv (by norm_num)).norm.mul hEc).bounded_above_of_compact_support
      ((b.hasCompactSupport.fderiv (𝕜 := ℝ)).norm.mul_right (f' := E))
  set β : ℂ →ᵇ ℝ := .ofNormedAddCommGroup b b.continuous 1 fun z ↦ by
    rw [Real.norm_of_nonneg b.nonneg]; exact b.le_one
  have hβe : (β : ℂ → ℝ) = b := BoundedContinuousFunction.coe_ofNormedAddCommGroup _ _ _ _
  have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ 0)
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  set Ky := solutionConst c (limitConst ((c ^ 2 + 1 / 4) / 2) c c₀ M₀ M₁)
  have hKy0 : 0 ≤ Ky :=
    solutionConst_nonneg hc (limitConst_nonneg hc (by linarith) hc₀ hM₀0 hM₁0)
  refine ⟨Real.toNNReal (Ky + 1), fun f y hweak horth ↦ ?_⟩
  rcases eq_or_ne (eLpNorm (fun z ↦ E z • f z) 2 μ) ⊤ with htop | hfin
  · rw [htop, ENNReal.mul_top (by simpa using hKy0.trans_lt (lt_add_one Ky))]
    exact le_top
  have hFf : ‖f‖ ≤ (eLpNorm (fun z ↦ E z • f z) 2 μ).toReal := by
    rw [Lp.norm_def]
    refine ENNReal.toReal_mono hfin (eLpNorm_mono (Lp.aestronglyMeasurable f) fun z ↦ ?_)
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by positivity))
  obtain ⟨η, u, hT, hS⟩ := exists_tendsto_testField hx.continuous hc₀ hgap horth
  have hweak' (ζ : TestField) :
      ⟪y, gaugeFixedAdjointToLp μ hx.continuous ζ⟫ = ⟪f, ambientToLp 2 μ ζ⟫ := by
    rw [inner_gaugeFixedAdjointToLp, inner_ambientToLp]
    exact hweak ζ ζ.contDiff ζ.hasCompactSupport
  have hu := norm_le_div_of_tendsto hx.continuous hc₀ hgap hT hS hweak'
  -- The bound at each regularized weight, uniformly in the regularization.
  have hn (n : ℕ) : eLpNorm (fun z ↦ boundedExpWeight c (1 / (n + 1)) z • y z) 2 μ ≤
      Real.toNNReal (Ky + 1) * eLpNorm (fun z ↦ E z • f z) 2 μ := by
    refine (eLpNorm_boundedExpWeight_smul_le hx hsol (by linarith) (fun z hz ↦ (hR z hz).le) hc
      (by linarith) hc₀ hM₀0 hM₁0
      Nat.one_div_pos_of_nat hT hS hweak' hu β (hβe ▸ hb) (hβe ▸ fun z ↦ b.nonneg)
      (hβe ▸ fun z ↦ b.le_one) (fun z hz ↦ hβe ▸ b.one_of_mem_closedBall (by simpa using hz))
      (fun z ↦ hβe ▸ (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le (hM₀ z)))
      (fun z ↦ hβe ▸ (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le (hM₁ z)))
      hfin hFf).trans ?_
    calc _ ≤ ENNReal.ofReal ((Ky + 1) * (eLpNorm (fun z ↦ E z • f z) 2 μ).toReal) := by
          exact ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) ENNReal.toReal_nonneg)
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hfin,
            ENNReal.ofNNReal_toNNReal]
  -- Fatou's lemma as the regularization is removed.
  have hy : AEStronglyMeasurable (fun z ↦ E z • y z) μ :=
    hEc.aestronglyMeasurable.smul (Lp.aestronglyMeasurable y)
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n ↦
    (contDiff_boundedExpWeight (n := 0) Nat.one_div_pos_of_nat.le).continuous
      |>.aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable y)) _ hy
    (ae_of_all _ fun z ↦ ((tendsto_boundedExpWeight c z).comp
      tendsto_one_div_add_atTop_nhds_zero_nat).smul_const (y z))).trans ?_
  exact liminf_le_of_frequently_le' (Frequently.of_forall hn)

/-- **The weak right inverse at a plane vortex preserves exponential decay.** Let `x` be a `C¹`
solution of the plane vortex equation with `|α| → 1` at infinity. There is a bounded operator
`Q` on `L²(ℂ; ℝ⁴)` such that `Q f` is a weak solution of `L_x y = f` orthogonal to the weak
kernel of `L_x`, and such that for every rate `0 ≤ c < 1/2` there is a constant `K` with
`‖exp(c ρ) Q f‖₂ ≤ K ‖exp(c ρ) f‖₂` for every `f`, where `ρ(z) = √(1 + |z|²)`. -/
theorem exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_and_eLpNorm_exp_smul_le
    (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪Q f z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ) ∧
      (∀ f u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
        ∫ z, ⟪Q f z, u z⟫ ∂μ = 0) ∧
      ∀ c : ℝ, 0 ≤ c → c < 1 / 2 → ∃ K : ℝ≥0, ∀ f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • Q f z) 2 μ ≤
          K * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 μ := by
  obtain ⟨Q, hQ, hQK⟩ :=
    exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq (μ := μ) hx hsol hlim
  refine ⟨Q, hQ, hQK, fun c hc hc' ↦ ?_⟩
  obtain ⟨K, hK⟩ := exists_eLpNorm_exp_smul_le_mul_eLpNorm_exp_smul (μ := μ) hx hsol hlim hc hc'
  exact ⟨K, fun f ↦ hK f (Q f) (hQ f) (hQK f)⟩

end TauCeti.Vortex
