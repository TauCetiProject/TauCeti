/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.RightInverse
public import TauCeti.Analysis.PDE.Vortex.WeightedEstimate
public import TauCeti.MeasureTheory.Function.Lp.Operator.Multiplication

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
`exp(c ρ) / (1 + ε exp(c ρ))`, whose logarithmic gradient is still at most `c`, and Fatou's lemma
removes the regularization.

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
  norm_smulLp_apply_le_norm_smulLp_apply smulLp_add smulLp_smul smulLp_const smulLp_mul
  inner_smulLp_apply_left)
open ENNReal (ofNat_ne_top)

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure] {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- Multiplication by `φ` on `L²(ℂ; ℝ⁴)` is dominated by multiplication by any `ψ ≥ |φ|`. -/
private theorem norm_smulLp_le_of_abs_le {φ ψ : ℂ →ᵇ ℝ} (h : ∀ z, |φ z| ≤ ψ z)
    (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    ‖smulLp μ 2 ofNat_ne_top φ g‖ ≤ ‖smulLp μ 2 ofNat_ne_top ψ g‖ :=
  norm_smulLp_apply_le_norm_smulLp_apply (fun z ↦ by
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (h z).trans (le_abs_self _)) g

/-! ### Test fields -/

/-- The compactly supported `C²` test fields. -/
private abbrev TestField := TestFunction (⊤ : TopologicalSpace.Opens ℂ) (EuclideanSpace ℝ (Fin 4)) 2

private theorem memLp_testField (η : TestField) : MemLp η 2 μ :=
  η.continuous.memLp_of_hasCompactSupport η.hasCompactSupport

private theorem memLp_gaugeFixedAdjoint_testField (hx : Continuous x) (η : TestField) :
    MemLp (gaugeFixedAdjoint x η) 2 μ :=
  (continuous_gaugeFixedAdjoint hx (η.contDiff.of_le (by norm_cast))).memLp_of_hasCompactSupport
    (hasCompactSupport_gaugeFixedAdjoint η.hasCompactSupport)

variable (μ) in
/-- The inclusion of the test fields into `L²`. -/
private def toL2 : TestField →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ where
  toFun η := (memLp_testField η).toLp η
  map_add' η ν := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (.of_eq (FunLike.coe_add η ν))
  map_smul' t η := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (.of_eq (FunLike.coe_smul t η))

variable (μ) in
/-- The formal adjoint `L_x*` on test fields, with values in `L²`. -/
private def adjL2 (hx : Continuous x) : TestField →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ where
  toFun η := (memLp_gaugeFixedAdjoint_testField hx η).toLp (gaugeFixedAdjoint x η)
  map_add' η ν := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun z ↦ ?_)
    rw [FunLike.coe_add, Pi.add_apply]
    exact gaugeFixedAdjoint_add x (η.contDiff.differentiable (by norm_num) z)
      (ν.contDiff.differentiable (by norm_num) z)
  map_smul' t η := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun z ↦ ?_)
    rw [FunLike.coe_smul, Pi.smul_apply]
    exact gaugeFixedAdjoint_smul x η t z

private theorem coeFn_toL2 (η : TestField) : toL2 μ η =ᵐ[μ] η :=
  (memLp_testField η).coeFn_toLp

private theorem coeFn_adjL2 (hx : Continuous x) (η : TestField) :
    adjL2 μ hx η =ᵐ[μ] gaugeFixedAdjoint x η :=
  (memLp_gaugeFixedAdjoint_testField hx η).coeFn_toLp

private theorem inner_adjL2 (hx : Continuous x) (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)
    (η : TestField) : ⟪g, adjL2 μ hx η⟫ = ∫ z, ⟪g z, gaugeFixedAdjoint x η z⟫ ∂μ :=
  L2.inner_toLp g (memLp_gaugeFixedAdjoint_testField hx η)

private theorem inner_toL2 (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) (η : TestField) :
    ⟪g, toL2 μ η⟫ = ∫ z, ⟪g z, η z⟫ ∂μ :=
  L2.inner_toLp g (memLp_testField η)

/-- The product of a `C²` real function and a test field. -/
private def smulTestField (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (η : TestField) : TestField :=
  have hη : ContDiff ℝ 2 (η : ℂ → EuclideanSpace ℝ (Fin 4)) := η.contDiff
  have hc : HasCompactSupport (fun z ↦ φ z • (η : ℂ → EuclideanSpace ℝ (Fin 4)) z) :=
    η.hasCompactSupport.mono fun z hz h0 ↦ hz (by simp [h0])
  ⟨fun z ↦ φ z • η z, hφ.smul hη, hc, by simp⟩

private theorem coe_smulTestField (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (η : TestField) :
    (smulTestField φ hφ η : ℂ → EuclideanSpace ℝ (Fin 4)) = fun z ↦ φ z • η z :=
  (rfl)

@[simp]
private theorem smulTestField_apply (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (η : TestField) (z : ℂ) :
    smulTestField φ hφ η z = φ z • η z :=
  (rfl)

private theorem toL2_smulTestField (φ : ℂ →ᵇ ℝ) (hφ : ContDiff ℝ 2 φ) (η : TestField) :
    toL2 μ (smulTestField φ hφ η) = smulLp μ 2 ofNat_ne_top φ (toL2 μ η) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_toL2 (μ := μ) (smulTestField φ hφ η),
    coeFn_smulLp ofNat_ne_top φ (toL2 μ η),
    coeFn_toL2 (μ := μ) η] with z h₁ h₂ h₃
  rw [h₁, h₂, h₃, smulTestField_apply]

/-- The commutator of `L_x*` with multiplication by `φ` is the principal symbol at `dφ`, whose
pointwise norm is `|dφ| |η|`. -/
private theorem norm_adjL2_smulTestField_sub_le (hx : Continuous x) (φ ψ : ℂ →ᵇ ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ∀ z, ‖fderiv ℝ φ z‖ ≤ ψ z) (η : TestField) :
    ‖adjL2 μ hx (smulTestField φ hφ η) - smulLp μ 2 ofNat_ne_top φ (adjL2 μ hx η)‖ ≤
      ‖smulLp μ 2 ofNat_ne_top ψ (toL2 μ η)‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [Lp.coeFn_sub (adjL2 μ hx (smulTestField φ hφ η))
      (smulLp μ 2 ofNat_ne_top φ (adjL2 μ hx η)),
    coeFn_adjL2 (μ := μ) hx (smulTestField φ hφ η), coeFn_smulLp ofNat_ne_top φ (adjL2 μ hx η),
    coeFn_adjL2 (μ := μ) hx η, coeFn_smulLp ofNat_ne_top ψ (toL2 μ η), coeFn_toL2 (μ := μ) η]
    with z h₁ h₂ h₃ h₄ h₅ h₆
  have hL := gaugeFixedAdjoint_fun_smul x (hφ.differentiable (by norm_num) z)
    (η.contDiff.differentiable (by norm_num) z)
  rw [h₁, Pi.sub_apply, h₂, h₃, h₄, h₅, h₆, coe_smulTestField, hL, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg ((norm_nonneg _).trans (hψ z)),
    ← sq_le_sq₀ (norm_nonneg _) (by have := (norm_nonneg _).trans (hψ z); positivity), mul_pow,
    norm_sq_gaugeFixedAdjointSymbol]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hψ z) 2) (by positivity)

private theorem contDiff_mul_self {φ : ℂ →ᵇ ℝ} (hφ : ContDiff ℝ 2 φ) : ContDiff ℝ 2 ⇑(φ * φ) := by
  rw [FunLike.coe_mul]
  exact hφ.mul hφ

/-- The localization identity `‖L_x* (φ η)‖² = ⟪L_x* (φ² η), L_x* η⟫ + ‖|dφ| η‖²` in `L²`. -/
private theorem norm_sq_adjL2_smulTestField (hx : Continuous x) (φ dφ : ℂ →ᵇ ℝ)
    (hφ : ContDiff ℝ 2 φ) (hdφ : ∀ z, dφ z = ‖fderiv ℝ φ z‖) (η : TestField) :
    ‖adjL2 μ hx (smulTestField φ hφ η)‖ ^ 2 =
      ⟪adjL2 μ hx (smulTestField (φ * φ) (contDiff_mul_self hφ) η), adjL2 μ hx η⟫ +
        ‖smulLp μ 2 ofNat_ne_top dφ (toL2 μ η)‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def,
    L2.inner_def, ← integral_add (L2.integrable_inner _ _) (L2.integrable_inner _ _)]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_adjL2 (μ := μ) hx (smulTestField φ hφ η),
    coeFn_adjL2 (μ := μ) hx (smulTestField (φ * φ) (contDiff_mul_self hφ) η),
    coeFn_adjL2 (μ := μ) hx η, coeFn_smulLp ofNat_ne_top dφ (toL2 μ η), coeFn_toL2 (μ := μ) η]
    with z h₁ h₂ h₃ h₄ h₅
  have hL := norm_sq_gaugeFixedAdjoint_fun_smul x (hφ.differentiable (by norm_num) z)
    (η.contDiff.differentiable (by norm_num) z)
  rw [h₁, h₂, h₃, h₄, h₅, coe_smulTestField, coe_smulTestField, real_inner_self_eq_norm_sq, hL,
    real_inner_comm,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hdφ]
  simp only [Pi.mul_apply, ← sq]
  rw [real_inner_comm]
  ring

/-- The exterior estimate for `L_x*` applied to `φ η`, for `φ` vanishing on the disc of radius
`R` outside which `|α|² / 4 ≥ a`. -/
private theorem mul_norm_sq_toL2_le_norm_sq_adjL2 (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0) {a R : ℝ} (ha : a ≤ 1 / 4)
    (hR : ∀ z, R < ‖z‖ → a ≤ x z 2 ^ 2 + x z 3 ^ 2) (φ : ℂ →ᵇ ℝ) (hφ : ContDiff ℝ 2 φ)
    (hφR : ∀ z, ‖z‖ ≤ R → φ z = 0) (η : TestField) :
    a * ‖toL2 μ (smulTestField φ hφ η)‖ ^ 2 ≤
      ‖adjL2 μ hx.continuous (smulTestField φ hφ η)‖ ^ 2 := by
  set ζ := smulTestField φ hφ η
  have hint := mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint (μ := μ) hx ζ.contDiff
    ζ.hasCompactSupport (fun z _ ↦ hsol z) ha fun z hz ↦ hR z <| lt_of_not_ge fun h ↦
      hz (by rw [smulTestField_apply, hφR z h, zero_smul])
  rw [L2.norm_sq_eq_integral_norm_sq, L2.norm_sq_eq_integral_norm_sq]
  calc a * ∫ z, ‖toL2 μ ζ z‖ ^ 2 ∂μ = a * ∫ z, ‖ζ z‖ ^ 2 ∂μ := by
        congr 1
        exact integral_congr_ae ((coeFn_toL2 ζ).mono fun z hz ↦ by simp only [hz])
    _ ≤ ∫ z, ‖gaugeFixedAdjoint x ζ z‖ ^ 2 ∂μ := hint
    _ = ∫ z, ‖adjL2 μ hx.continuous ζ z‖ ^ 2 ∂μ :=
        integral_congr_ae ((coeFn_adjL2 hx.continuous ζ).mono fun z hz ↦ by simp only [hz])

/-- An `L²` lower bound for `L_x*` on test fields, in operator form. -/
private theorem sqrt_mul_norm_toL2_le (hx : Continuous x) {c : ℝ} (hc : 0 ≤ c)
    (hgap : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      c * ∫ z, ‖η z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ) (η : TestField) :
    √c * ‖toL2 μ η‖ ≤ ‖adjL2 μ hx η‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [mul_pow, Real.sq_sqrt hc, L2.norm_sq_eq_integral_norm_sq, L2.norm_sq_eq_integral_norm_sq]
  calc c * ∫ z, ‖toL2 μ η z‖ ^ 2 ∂μ = c * ∫ z, ‖η z‖ ^ 2 ∂μ := by
        congr 1
        exact integral_congr_ae ((coeFn_toL2 η).mono fun z hz ↦ by simp only [hz])
    _ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ := hgap η η.contDiff η.hasCompactSupport
    _ = ∫ z, ‖adjL2 μ hx η z‖ ^ 2 ∂μ :=
        integral_congr_ae ((coeFn_adjL2 hx η).mono fun z hz ↦ by simp only [hz])

/-! ### Approximation of the least-norm weak solution -/

/-- A weak solution orthogonal to the weak kernel of `L_x` is an `L²` limit of `L_x* η_n` for
test fields `η_n`. Under a lower bound for `L_x*`, the `η_n` themselves converge in `L²`. -/
private theorem exists_tendsto_toL2_adjL2 (hx : Continuous x) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      c * ∫ z, ‖η z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ)
    {y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (horth : ∀ u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
      ∫ z, ⟪y z, u z⟫ ∂μ = 0) :
    ∃ (η : ℕ → TestField) (u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ),
      Tendsto (fun n ↦ toL2 μ (η n)) atTop (𝓝 u) ∧
        Tendsto (fun n ↦ adjL2 μ hx (η n)) atTop (𝓝 y) := by
  set S := adjL2 μ hx
  -- `y` lies in `(range S)ᗮᗮ`, the closure of the range of `S`.
  have hy : y ∈ (LinearMap.range S)ᗮᗮ := by
    refine (Submodule.mem_orthogonal _ _).2 fun u hu ↦ ?_
    rw [real_inner_comm, L2.inner_def]
    refine horth u fun η hη hηc ↦ ?_
    have h := (Submodule.mem_orthogonal _ _).1 hu (S ⟨η, hη, hηc, by simp⟩) ⟨_, rfl⟩
    rwa [real_inner_comm, inner_adjL2] at h
  rw [Submodule.orthogonal_orthogonal_eq_closure, ← SetLike.mem_coe,
    Submodule.topologicalClosure_coe] at hy
  obtain ⟨v, hv, hvy⟩ := mem_closure_iff_seq_limit.1 hy
  choose η hη using hv
  have hSη : Tendsto (fun n ↦ S (η n)) atTop (𝓝 y) := by simpa only [hη] using hvy
  -- The lower bound makes `toL2 μ (η n)` a Cauchy sequence.
  have hcau : CauchySeq fun n ↦ toL2 μ (η n) := by
    refine Metric.cauchySeq_iff.2 fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hSη.cauchySeq (√c * ε) (by positivity)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have h := sqrt_mul_norm_toL2_le hx hc.le hgap (η m - η n)
    rw [map_sub, map_sub, ← dist_eq_norm, ← dist_eq_norm] at h
    exact lt_of_mul_lt_mul_left (h.trans_lt (hN m hm n hn)) (Real.sqrt_nonneg c)
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hcau
  exact ⟨η, u, hu, hSη⟩

/-! ### Limits of the multiplier identities -/

/-- Along the approximating test fields, `‖L_x* (φ η_n)‖²` converges to
`⟪φ f, φ u⟫ + ‖|dφ| u‖²`. -/
private theorem tendsto_norm_sq_adjL2_smulTestField (hx : Continuous x)
    {f y u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} {η : ℕ → TestField}
    (hT : Tendsto (fun n ↦ toL2 μ (η n)) atTop (𝓝 u))
    (hS : Tendsto (fun n ↦ adjL2 μ hx (η n)) atTop (𝓝 y))
    (hweak : ∀ ζ : TestField, ⟪y, adjL2 μ hx ζ⟫ = ⟪f, toL2 μ ζ⟫) (φ dφ : ℂ →ᵇ ℝ)
    (hφ : ContDiff ℝ 2 φ) (hdφ : ∀ z, dφ z = ‖fderiv ℝ φ z‖) :
    Tendsto (fun n ↦ ‖adjL2 μ hx (smulTestField φ hφ (η n))‖ ^ 2) atTop
      (𝓝 (⟪smulLp μ 2 ofNat_ne_top φ f, smulLp μ 2 ofNat_ne_top φ u⟫ +
        ‖smulLp μ 2 ofNat_ne_top dφ u‖ ^ 2)) := by
  refine Tendsto.congr (fun n ↦ (norm_sq_adjL2_smulTestField hx φ dφ hφ hdφ (η n)).symm) ?_
  refine Tendsto.add ?_ ((((smulLp μ 2 ofNat_ne_top dφ).continuous.tendsto u).comp hT).norm.pow 2)
  set φ₂ : ℂ →ᵇ ℝ := φ * φ
  set hφ₂ := contDiff_mul_self hφ
  set S := adjL2 μ hx
  -- Split `⟪S (φ² η_n), S η_n⟫` into the weak pairing with `y` and an error term.
  have hsplit (n : ℕ) : ⟪f, smulLp μ 2 ofNat_ne_top φ₂ (toL2 μ (η n))⟫ +
      ⟪S (smulTestField φ₂ hφ₂ (η n)), S (η n) - y⟫ =
        ⟪S (smulTestField φ₂ hφ₂ (η n)), S (η n)⟫ := by
    rw [inner_sub_right, real_inner_comm y, hweak, toL2_smulTestField]
    ring
  refine Tendsto.congr hsplit ?_
  have hφφ : ⟪smulLp μ 2 ofNat_ne_top φ f, smulLp μ 2 ofNat_ne_top φ u⟫ =
      ⟪f, smulLp μ 2 ofNat_ne_top φ₂ u⟫ := by
    have hstar : star φ = φ := by
      ext z
      simp
    rw [inner_smulLp_apply_left, hstar, smulLp_mul, mul_apply_eq_comp]
  rw [← add_zero ⟪smulLp μ 2 ofNat_ne_top φ f, smulLp μ 2 ofNat_ne_top φ u⟫, hφφ]
  refine Tendsto.add (tendsto_const_nhds.inner
    (((smulLp μ 2 ofNat_ne_top φ₂).continuous.tendsto u).comp hT)) ?_
  -- The error term tends to zero, since `S (φ² η_n)` stays bounded.
  have hd (z : ℂ) : ‖fderiv ℝ φ₂ z‖ ≤ ((2 * ‖φ‖) • dφ) z := by
    have hd := hφ.differentiable (by norm_num) z
    rw [show (φ₂ : ℂ → ℝ) = fun t ↦ φ t * φ t from FunLike.coe_mul φ φ, fderiv_fun_mul hd hd,
      smul_apply, smul_eq_mul, hdφ, ← two_smul ℝ (φ z • fderiv ℝ φ z),
      smul_smul]
    calc ‖(2 * φ z) • fderiv ℝ φ z‖ = 2 * ‖φ z‖ * ‖fderiv ℝ φ z‖ := by
          rw [norm_smul, norm_mul, Real.norm_two]
      _ ≤ 2 * ‖φ‖ * ‖fderiv ℝ φ z‖ := by
          gcongr
          exact φ.norm_coe_le_norm z
  have hbound (n : ℕ) : ‖S (smulTestField φ₂ hφ₂ (η n))‖ ≤
      ‖φ₂‖ * ‖S (η n)‖ + ‖(2 * ‖φ‖) • dφ‖ * ‖toL2 μ (η n)‖ := by
    calc ‖S (smulTestField φ₂ hφ₂ (η n))‖
        ≤ ‖smulLp μ 2 ofNat_ne_top φ₂ (S (η n))‖ +
            ‖S (smulTestField φ₂ hφ₂ (η n)) - smulLp μ 2 ofNat_ne_top φ₂ (S (η n))‖ :=
          norm_le_insert' _ _
      _ ≤ ‖φ₂‖ * ‖S (η n)‖ + ‖(2 * ‖φ‖) • dφ‖ * ‖toL2 μ (η n)‖ :=
          add_le_add (norm_smulLp_apply_le _ _)
            ((norm_adjL2_smulTestField_sub_le hx φ₂ _ hφ₂ hd _).trans
            (norm_smulLp_apply_le _ _))
  refine squeeze_zero_norm (fun n ↦ (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _))) ?_
  have h0 : Tendsto (fun n ↦ ‖S (η n) - y‖) atTop (𝓝 0) := by
    simpa using (tendsto_sub_nhds_zero_iff.2 hS).norm
  simpa using (((hS.norm.const_mul ‖φ₂‖).add (hT.norm.const_mul ‖(2 * ‖φ‖) • dφ‖)).mul h0)

/-- **The exterior multiplier inequality.** For `φ` vanishing on the disc of radius `R` outside
which `|α|² / 4 ≥ a`, `a ‖φ u‖² ≤ ⟪φ f, φ u⟫ + ‖|dφ| u‖²`. -/
private theorem mul_norm_sq_smulLp_le (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    {a R : ℝ} (ha : a ≤ 1 / 4) (hR : ∀ z, R < ‖z‖ → a ≤ x z 2 ^ 2 + x z 3 ^ 2)
    {f y u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} {η : ℕ → TestField}
    (hT : Tendsto (fun n ↦ toL2 μ (η n)) atTop (𝓝 u))
    (hS : Tendsto (fun n ↦ adjL2 μ hx.continuous (η n)) atTop (𝓝 y))
    (hweak : ∀ ζ : TestField, ⟪y, adjL2 μ hx.continuous ζ⟫ = ⟪f, toL2 μ ζ⟫) (φ dφ : ℂ →ᵇ ℝ)
    (hφ : ContDiff ℝ 2 φ) (hdφ : ∀ z, dφ z = ‖fderiv ℝ φ z‖) (hφR : ∀ z, ‖z‖ ≤ R → φ z = 0) :
    a * ‖smulLp μ 2 ofNat_ne_top φ u‖ ^ 2 ≤
      ⟪smulLp μ 2 ofNat_ne_top φ f, smulLp μ 2 ofNat_ne_top φ u⟫ +
        ‖smulLp μ 2 ofNat_ne_top dφ u‖ ^ 2 := by
  have hl : Tendsto (fun n ↦ a * ‖toL2 μ (smulTestField φ hφ (η n))‖ ^ 2) atTop
      (𝓝 (a * ‖smulLp μ 2 ofNat_ne_top φ u‖ ^ 2)) := by
    refine Tendsto.congr (fun n ↦ ?_)
      (((((smulLp μ 2 ofNat_ne_top φ).continuous.tendsto u).comp hT).norm.pow 2).const_mul a)
    rw [Function.comp_apply, toL2_smulTestField]
  exact le_of_tendsto_of_tendsto' hl
    (tendsto_norm_sq_adjL2_smulTestField hx.continuous hT hS hweak φ dφ hφ hdφ) fun n ↦
      mul_norm_sq_toL2_le_norm_sq_adjL2 hx hsol ha hR φ hφ hφR (η n)

/-- The weighted norm of `y`: `‖φ y‖ ≤ (⟪φ f, φ u⟫ + ‖|dφ| u‖²)^(1/2) + ‖|dφ| u‖`. -/
private theorem norm_smulLp_le_sqrt_add (hx : Continuous x)
    {f y u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} {η : ℕ → TestField}
    (hT : Tendsto (fun n ↦ toL2 μ (η n)) atTop (𝓝 u))
    (hS : Tendsto (fun n ↦ adjL2 μ hx (η n)) atTop (𝓝 y))
    (hweak : ∀ ζ : TestField, ⟪y, adjL2 μ hx ζ⟫ = ⟪f, toL2 μ ζ⟫) (φ dφ : ℂ →ᵇ ℝ)
    (hφ : ContDiff ℝ 2 φ) (hdφ : ∀ z, dφ z = ‖fderiv ℝ φ z‖) :
    ‖smulLp μ 2 ofNat_ne_top φ y‖ ≤
      √(⟪smulLp μ 2 ofNat_ne_top φ f, smulLp μ 2 ofNat_ne_top φ u⟫ +
        ‖smulLp μ 2 ofNat_ne_top dφ u‖ ^ 2) + ‖smulLp μ 2 ofNat_ne_top dφ u‖ := by
  have hl : Tendsto (fun n ↦ ‖smulLp μ 2 ofNat_ne_top φ (adjL2 μ hx (η n))‖) atTop
      (𝓝 ‖smulLp μ 2 ofNat_ne_top φ y‖) :=
    (((smulLp μ 2 ofNat_ne_top φ).continuous.tendsto y).comp hS).norm
  have hΛ := tendsto_norm_sq_adjL2_smulTestField hx hT hS hweak φ dφ hφ hdφ
  have hd : Tendsto (fun n ↦ ‖smulLp μ 2 ofNat_ne_top dφ (toL2 μ (η n))‖) atTop
      (𝓝 ‖smulLp μ 2 ofNat_ne_top dφ u‖) :=
    (((smulLp μ 2 ofNat_ne_top dφ).continuous.tendsto u).comp hT).norm
  have hr := hΛ.sqrt.add hd
  refine le_of_tendsto_of_tendsto' hl hr fun n ↦ ?_
  have hsq : √(‖adjL2 μ hx (smulTestField φ hφ (η n))‖ ^ 2) =
      ‖adjL2 μ hx (smulTestField φ hφ (η n))‖ := Real.sqrt_sq (norm_nonneg _)
  have hc := norm_adjL2_smulTestField_sub_le (μ := μ) hx φ dφ hφ (fun z ↦ (hdφ z).ge) (η n)
  have hi := norm_le_insert (adjL2 μ hx (smulTestField φ hφ (η n)))
    (smulLp μ 2 ofNat_ne_top φ (adjL2 μ hx (η n)))
  rw [hsq]
  linarith

/-- Testing with `φ = 1`: `‖y‖² = ⟪f, u⟫`. -/
private theorem norm_sq_eq_inner_of_tendsto (hx : Continuous x)
    {f y u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} {η : ℕ → TestField}
    (hT : Tendsto (fun n ↦ toL2 μ (η n)) atTop (𝓝 u))
    (hS : Tendsto (fun n ↦ adjL2 μ hx (η n)) atTop (𝓝 y))
    (hweak : ∀ ζ : TestField, ⟪y, adjL2 μ hx ζ⟫ = ⟪f, toL2 μ ζ⟫) :
    ‖y‖ ^ 2 = ⟪f, u⟫ := by
  have h1 : ContDiff ℝ 2 (BoundedContinuousFunction.const ℂ (1 : ℝ)) := by
    simpa [BoundedContinuousFunction.const_apply'] using contDiff_const (c := (1 : ℝ))
  have hd (z : ℂ) : BoundedContinuousFunction.const ℂ (0 : ℝ) z =
      ‖fderiv ℝ (BoundedContinuousFunction.const ℂ (1 : ℝ)) z‖ := by
    simp [BoundedContinuousFunction.const_apply']
  have h := tendsto_norm_sq_adjL2_smulTestField hx hT hS hweak _ _ h1 hd
  have hη (ζ : TestField) : smulTestField _ h1 ζ = ζ :=
    TestFunction.ext fun z ↦ by
      rw [smulTestField_apply, BoundedContinuousFunction.const_apply', one_smul]
  simp only [hη, smulLp_const, _root_.smul_apply, one_smul, zero_smul, one_apply_eq_self,
    norm_zero] at h
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

/-- The derivative of `(1 - β) w` is bounded by `c (1 - β) w + |dβ| w` when `|dw| ≤ c w`. -/
private theorem norm_fderiv_one_sub_mul_le {β w : ℂ → ℝ} {c : ℝ} (hβ : Differentiable ℝ β)
    (hw : Differentiable ℝ w) (hβ₁ : ∀ z, β z ≤ 1) (hw₀ : ∀ z, 0 ≤ w z)
    (hdw : ∀ z, ‖fderiv ℝ w z‖ ≤ c * w z) (z : ℂ) :
    ‖fderiv ℝ (fun t ↦ (1 - β t) * w t) z‖ ≤ c * ((1 - β z) * w z) + ‖fderiv ℝ β z‖ * w z := by
  rw [fderiv_fun_mul ((hβ z).const_sub 1) (hw z), fderiv_const_sub]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_neg, Real.norm_of_nonneg (sub_nonneg.2 (hβ₁ z)),
    Real.norm_of_nonneg (hw₀ z)]
  nlinarith [mul_le_mul_of_nonneg_left (hdw z) (sub_nonneg.2 (hβ₁ z))]

/-- **The weighted bound for the `L²` limit `u` of the approximating test fields.** Let `w` be a
bounded `C²` weight with `|dw| ≤ c w`, `c² < a`, and let `β` be a cutoff equal to `1` on the
disc of radius `R`, outside which `|α|² / 4 ≥ a`. If `β w ≤ M₀` and `|dβ| w ≤ M₁`, then `‖w u‖`
is bounded by a constant multiple of any `F ≥ ‖f‖, ‖w f‖`. -/
private theorem norm_smulLp_weight_le (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    {a R c c₀ M₀ M₁ F : ℝ} (ha : a ≤ 1 / 4) (hR : ∀ z, R < ‖z‖ → a ≤ x z 2 ^ 2 + x z 3 ^ 2)
    (hc : 0 ≤ c) (hca : c ^ 2 < a) (hc₀ : 0 < c₀) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    {f y u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} {η : ℕ → TestField}
    (hT : Tendsto (fun n ↦ toL2 μ (η n)) atTop (𝓝 u))
    (hS : Tendsto (fun n ↦ adjL2 μ hx.continuous (η n)) atTop (𝓝 y))
    (hweak : ∀ ζ : TestField, ⟪y, adjL2 μ hx.continuous ζ⟫ = ⟪f, toL2 μ ζ⟫)
    (hu : ‖u‖ ≤ ‖f‖ / c₀) (β w : ℂ →ᵇ ℝ) (hβ : ContDiff ℝ 2 β) (hβ₀ : ∀ z, 0 ≤ β z)
    (hβ₁ : ∀ z, β z ≤ 1) (hβR : ∀ z, ‖z‖ ≤ R → β z = 1) (hw : ContDiff ℝ 2 w)
    (hw₀ : ∀ z, 0 ≤ w z) (hdw : ∀ z, ‖fderiv ℝ w z‖ ≤ c * w z) (hβw : ∀ z, β z * w z ≤ M₀)
    (hdβw : ∀ z, ‖fderiv ℝ β z‖ * w z ≤ M₁) (hFf : ‖f‖ ≤ F)
    (hFw : ‖smulLp μ 2 ofNat_ne_top w f‖ ≤ F) :
    ‖smulLp μ 2 ofNat_ne_top w u‖ ≤ ((1 + 2 * c * (M₁ / c₀)) / (a - c ^ 2) +
      (M₁ / c₀) ^ 2 / (a - c ^ 2) + 1 + M₀ / c₀) * F := by
  have hF : 0 ≤ F := (norm_nonneg _).trans hFf
  -- The cut-off weight `φ = (1 - β) w` and the norm of its derivative.
  set φ : ℂ →ᵇ ℝ := (1 - β) * w
  have hφe : (φ : ℂ → ℝ) = fun t ↦ (1 - β t) * w t := by
    ext t
    simp [φ]
  have hφ : ContDiff ℝ 2 φ := hφe ▸ (contDiff_const.sub hβ).mul hw
  have hdφ (z : ℂ) : ‖fderiv ℝ φ z‖ ≤ c * φ z + M₁ := by
    rw [hφe]
    exact (norm_fderiv_one_sub_mul_le (hβ.differentiable (by norm_num))
      (hw.differentiable (by norm_num)) hβ₁ hw₀ hdw z).trans (by linarith [hdβw z])
  have hφw (z : ℂ) : |φ z| ≤ w z := by
    rw [hφe, abs_of_nonneg (mul_nonneg (sub_nonneg.2 (hβ₁ z)) (hw₀ z))]
    nlinarith [hβ₀ z, hw₀ z]
  have hdφb (z : ℂ) : ‖‖fderiv ℝ φ z‖‖ ≤ c * ‖w‖ + M₁ := by
    have h1 := w.norm_coe_le_norm z
    rw [Real.norm_of_nonneg (hw₀ z)] at h1
    rw [norm_norm]
    exact (hdφ z).trans (by nlinarith [hφw z, le_abs_self (φ z)])
  set dφ : ℂ →ᵇ ℝ := .ofNormedAddCommGroup (fun z ↦ ‖fderiv ℝ φ z‖)
    (hφ.continuous_fderiv (by norm_num)).norm (c * ‖w‖ + M₁) hdφb
  -- The exterior multiplier inequality for `φ`.
  set X := ‖smulLp μ 2 ofNat_ne_top φ u‖
  have hB := mul_norm_sq_smulLp_le hx hsol ha hR hT hS hweak φ dφ hφ (fun z ↦ rfl) fun z hz ↦ by
    rw [hφe]; simp [hβR z hz]
  have hin : ⟪smulLp μ 2 ofNat_ne_top φ f, smulLp μ 2 ofNat_ne_top φ u⟫ ≤ F * X :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      ((norm_smulLp_le_of_abs_le hφw f).trans hFw) (norm_nonneg _))
  have hdu : ‖smulLp μ 2 ofNat_ne_top dφ u‖ ≤ c * X + M₁ * ‖u‖ := by
    refine (norm_smulLp_le_of_abs_le (ψ := c • φ + .const ℂ M₁) (fun z ↦ ?_) u).trans ?_
    · simpa [dφ] using hdφ z
    · rw [smulLp_add, smulLp_smul, smulLp_const, _root_.add_apply, _root_.smul_apply,
        _root_.smul_apply, one_apply_eq_self]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hc, Real.norm_of_nonneg hM₁]
  have hD : M₁ * ‖u‖ ≤ M₁ / c₀ * F := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc₀]
    nlinarith [(le_div_iff₀ hc₀).1 hu]
  have hX : X ≤ ((1 + 2 * c * (M₁ / c₀)) / (a - c ^ 2) + (M₁ / c₀) ^ 2 / (a - c ^ 2) + 1) * F := by
    refine le_mul_of_mul_sq_le hF (by linarith) (by positivity) (by positivity) ?_
    have hX0 : 0 ≤ X := norm_nonneg _
    have hdu0 : 0 ≤ ‖smulLp μ 2 ofNat_ne_top dφ u‖ := norm_nonneg _
    have hu0 : 0 ≤ M₁ * ‖u‖ := by positivity
    nlinarith [mul_le_mul hdu hdu hdu0 (by positivity), mul_le_mul_of_nonneg_left hD hX0,
      mul_le_mul hD hD hu0 (by positivity)]
  -- Split `w = (1 - β) w + β w`; the second part is bounded by `M₀` and supported in the core.
  have hsplit : smulLp μ 2 ofNat_ne_top w u =
      smulLp μ 2 ofNat_ne_top φ u + smulLp μ 2 ofNat_ne_top (β * w) u := by
    have hw' : w = φ + β * w := by
      ext z
      simp [φ]
      ring
    rw [← _root_.add_apply, ← smulLp_add, ← hw']
  have hβu : ‖smulLp μ 2 ofNat_ne_top (β * w) u‖ ≤ M₀ * ‖u‖ := by
    refine (norm_smulLp_le_of_abs_le (ψ := .const ℂ M₀) (fun z ↦ ?_) u).trans ?_
    · simpa [abs_of_nonneg (mul_nonneg (hβ₀ z) (hw₀ z))] using hβw z
    · rw [smulLp_const, _root_.smul_apply, one_apply_eq_self, norm_smul,
        Real.norm_of_nonneg hM₀]
  have hM₀u : M₀ * ‖u‖ ≤ M₀ / c₀ * F := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc₀]
    nlinarith [(le_div_iff₀ hc₀).1 hu]
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  nlinarith

/-- **The weighted bound for `y`** at a bounded `C²` weight `w` with `|dw| ≤ c w`, from the
weighted bound `‖w u‖ ≤ K F` for the `L²` limit `u` of the approximating test fields. -/
private theorem norm_smulLp_weight_le_of_norm_smulLp_le (hx : Continuous x) {c K F : ℝ}
    (hc : 0 ≤ c) {f y u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} {η : ℕ → TestField}
    (hT : Tendsto (fun n ↦ toL2 μ (η n)) atTop (𝓝 u))
    (hS : Tendsto (fun n ↦ adjL2 μ hx (η n)) atTop (𝓝 y))
    (hweak : ∀ ζ : TestField, ⟪y, adjL2 μ hx ζ⟫ = ⟪f, toL2 μ ζ⟫) (w : ℂ →ᵇ ℝ)
    (hw : ContDiff ℝ 2 w) (hw₀ : ∀ z, 0 ≤ w z) (hdw : ∀ z, ‖fderiv ℝ w z‖ ≤ c * w z)
    (hF : 0 ≤ F) (hK : 0 ≤ K) (hFw : ‖smulLp μ 2 ofNat_ne_top w f‖ ≤ F)
    (hWu : ‖smulLp μ 2 ofNat_ne_top w u‖ ≤ K * F) :
    ‖smulLp μ 2 ofNat_ne_top w y‖ ≤ (√(K + c ^ 2 * K ^ 2) + c * K) * F := by
  have hdwb (z : ℂ) : ‖‖fderiv ℝ w z‖‖ ≤ c * ‖w‖ := by
    have h1 := w.norm_coe_le_norm z
    rw [Real.norm_of_nonneg (hw₀ z)] at h1
    rw [norm_norm]
    exact (hdw z).trans (mul_le_mul_of_nonneg_left h1 hc)
  set dw : ℂ →ᵇ ℝ := .ofNormedAddCommGroup (fun z ↦ ‖fderiv ℝ w z‖)
    (hw.continuous_fderiv (by norm_num)).norm (c * ‖w‖) hdwb
  have hdu : ‖smulLp μ 2 ofNat_ne_top dw u‖ ≤ c * (K * F) := by
    refine (norm_smulLp_le_of_abs_le (ψ := c • w) (fun z ↦ ?_) u).trans ?_
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
  refine (norm_smulLp_le_sqrt_add hx hT hS hweak w dw hw fun z ↦ rfl).trans ?_
  nlinarith

/-! ### Regularized exponential weights -/

/-- The bounded regularization `E / (1 + ε E)` of the exponential weight
`E(z) = exp(c √(1 + |z|²))`. It increases to `E` as `ε` decreases to `0`. -/
private def regWeight (c ε : ℝ) (z : ℂ) : ℝ :=
  Real.exp (c * √(1 + ‖z‖ ^ 2)) / (1 + ε * Real.exp (c * √(1 + ‖z‖ ^ 2)))

section RegWeight

variable {c ε : ℝ} (hε : 0 ≤ ε)
include hε

private theorem one_le_one_add_mul_exp (z : ℂ) : 1 ≤ 1 + ε * Real.exp (c * √(1 + ‖z‖ ^ 2)) := by
  have := Real.exp_pos (c * √(1 + ‖z‖ ^ 2))
  nlinarith

private theorem regWeight_nonneg (z : ℂ) : 0 ≤ regWeight c ε z :=
  div_nonneg (Real.exp_pos _).le (zero_le_one.trans (one_le_one_add_mul_exp hε z))

private theorem regWeight_le (z : ℂ) : regWeight c ε z ≤ Real.exp (c * √(1 + ‖z‖ ^ 2)) :=
  div_le_self (Real.exp_pos _).le (one_le_one_add_mul_exp hε z)

private theorem contDiff_regWeight : ContDiff ℝ 2 (regWeight c ε) :=
  (contDiff_exp_mul_sqrt_one_add_norm_sq c).div
    (contDiff_const.add (contDiff_const.mul (contDiff_exp_mul_sqrt_one_add_norm_sq c)))
    fun z ↦ (zero_lt_one.trans_le (one_le_one_add_mul_exp hε z)).ne'

/-- The logarithmic gradient of the regularized weight is at most `|c|`. -/
private theorem norm_fderiv_regWeight_le (z : ℂ) :
    ‖fderiv ℝ (regWeight c ε) z‖ ≤ |c| * regWeight c ε z := by
  set E := fun t : ℂ ↦ Real.exp (c * √(1 + ‖t‖ ^ 2))
  have h1 := one_le_one_add_mul_exp (c := c) hε z
  have hg : HasDerivAt (fun s ↦ s / (1 + ε * s)) (1 / (1 + ε * E z) ^ 2) (E z) := by
    have h := (hasDerivAt_id' (E z)).div (((hasDerivAt_id' (E z)).const_mul ε).const_add 1)
      (zero_lt_one.trans_le h1).ne'
    rwa [show 1 * (1 + ε * E z) - E z * (ε * 1) = 1 by ring] at h
  have hE : HasFDerivAt E (fderiv ℝ E z) z :=
    ((contDiff_exp_mul_sqrt_one_add_norm_sq (n := 1) c).differentiable one_ne_zero z).hasFDerivAt
  rw [show regWeight c ε = (fun s ↦ s / (1 + ε * s)) ∘ E from rfl,
    (hg.comp_hasFDerivAt z hE).fderiv, norm_smul,
    Real.norm_of_nonneg (r := 1 / (1 + ε * E z) ^ 2) (by positivity)]
  have hd := norm_fderiv_exp_mul_sqrt_one_add_norm_sq_le c z
  have hEz : 0 < E z := Real.exp_pos _
  calc 1 / (1 + ε * E z) ^ 2 * ‖fderiv ℝ E z‖ ≤ 1 / (1 + ε * E z) ^ 2 * (|c| * E z) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
    _ ≤ |c| * (E z / (1 + ε * E z)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]
        have hi : ((1 + ε * E z) ^ 2)⁻¹ ≤ (1 + ε * E z)⁻¹ :=
          inv_anti₀ (by positivity) (by nlinarith)
        nlinarith [abs_nonneg c, mul_le_mul_of_nonneg_left hi (mul_nonneg (abs_nonneg c) hEz.le)]

end RegWeight

private theorem regWeight_le_inv {c ε : ℝ} (hε : 0 < ε) (z : ℂ) : regWeight c ε z ≤ ε⁻¹ := by
  rw [regWeight, div_le_iff₀ (zero_lt_one.trans_le (one_le_one_add_mul_exp hε.le z)),
    inv_mul_eq_div, le_div_iff₀ hε]
  nlinarith [Real.exp_pos (c * √(1 + ‖z‖ ^ 2))]

private theorem tendsto_regWeight (c : ℝ) (z : ℂ) :
    Tendsto (fun n : ℕ ↦ regWeight c (1 / (n + 1)) z) atTop
      (𝓝 (Real.exp (c * √(1 + ‖z‖ ^ 2)))) := by
  have h := ((tendsto_one_div_add_atTop_nhds_zero_nat.mul_const
    (Real.exp (c * √(1 + ‖z‖ ^ 2)))).const_add 1)
  rw [zero_mul, add_zero] at h
  have h' := (tendsto_const_nhds (x := Real.exp (c * √(1 + ‖z‖ ^ 2)))).div h one_ne_zero
  rw [div_one] at h'
  simpa only [regWeight, Pi.div_def] using h'

/-! ### The weighted estimate -/

/-- The unweighted bound `‖u‖ ≤ ‖f‖ / c₀` from `‖y‖² = ⟪f, u⟫` and the lower bound
`√c₀ ‖u‖ ≤ ‖y‖`. -/
private theorem norm_le_div_of_tendsto (hx : Continuous x) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hgap : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      c₀ * ∫ z, ‖η z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ)
    {f y u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} {η : ℕ → TestField}
    (hT : Tendsto (fun n ↦ toL2 μ (η n)) atTop (𝓝 u))
    (hS : Tendsto (fun n ↦ adjL2 μ hx (η n)) atTop (𝓝 y))
    (hweak : ∀ ζ : TestField, ⟪y, adjL2 μ hx ζ⟫ = ⟪f, toL2 μ ζ⟫) :
    ‖u‖ ≤ ‖f‖ / c₀ := by
  have hy : ‖y‖ ^ 2 ≤ ‖f‖ * ‖u‖ :=
    (norm_sq_eq_inner_of_tendsto hx hT hS hweak).trans_le (real_inner_le_norm f u)
  have hg : √c₀ * ‖u‖ ≤ ‖y‖ := le_of_tendsto_of_tendsto' (hT.norm.const_mul _) hS.norm
    fun n ↦ sqrt_mul_norm_toL2_le hx hc₀.le hgap (η n)
  have hs : √c₀ ^ 2 = c₀ := Real.sq_sqrt hc₀.le
  have hs0 : 0 ≤ √c₀ := Real.sqrt_nonneg c₀
  rw [le_div_iff₀ hc₀]
  rcases (norm_nonneg u).eq_or_lt with h0 | h0
  · rw [← h0, zero_mul]
    exact norm_nonneg f
  · have h2 : (√c₀ * ‖u‖) ^ 2 ≤ ‖f‖ * ‖u‖ :=
      (pow_le_pow_left₀ (by positivity) hg 2).trans hy
    rw [mul_pow, hs] at h2
    nlinarith

/-- The estimate at the regularized weight `E / (1 + ε E)`, uniformly in `ε > 0`. -/
private theorem eLpNorm_regWeight_smul_le (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    {a R c c₀ M₀ M₁ ε : ℝ} (ha : a ≤ 1 / 4) (hR : ∀ z, R < ‖z‖ → a ≤ x z 2 ^ 2 + x z 3 ^ 2)
    (hc : 0 ≤ c) (hca : c ^ 2 < a) (hc₀ : 0 < c₀) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hε : 0 < ε)
    {f y u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} {η : ℕ → TestField}
    (hT : Tendsto (fun n ↦ toL2 μ (η n)) atTop (𝓝 u))
    (hS : Tendsto (fun n ↦ adjL2 μ hx.continuous (η n)) atTop (𝓝 y))
    (hweak : ∀ ζ : TestField, ⟪y, adjL2 μ hx.continuous ζ⟫ = ⟪f, toL2 μ ζ⟫)
    (hu : ‖u‖ ≤ ‖f‖ / c₀) (β : ℂ →ᵇ ℝ) (hβ : ContDiff ℝ 2 β) (hβ₀ : ∀ z, 0 ≤ β z)
    (hβ₁ : ∀ z, β z ≤ 1) (hβR : ∀ z, ‖z‖ ≤ R → β z = 1)
    (hβE : ∀ z, β z * Real.exp (c * √(1 + ‖z‖ ^ 2)) ≤ M₀)
    (hdβE : ∀ z, ‖fderiv ℝ β z‖ * Real.exp (c * √(1 + ‖z‖ ^ 2)) ≤ M₁)
    (hfin : eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 μ ≠ ⊤)
    (hFf : ‖f‖ ≤ (eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 μ).toReal) :
    eLpNorm (fun z ↦ regWeight c ε z • y z) 2 μ ≤ ENNReal.ofReal
      ((√(((1 + 2 * c * (M₁ / c₀)) / (a - c ^ 2) + (M₁ / c₀) ^ 2 / (a - c ^ 2) + 1 + M₀ / c₀) +
          c ^ 2 * ((1 + 2 * c * (M₁ / c₀)) / (a - c ^ 2) + (M₁ / c₀) ^ 2 / (a - c ^ 2) + 1 +
            M₀ / c₀) ^ 2) +
        c * ((1 + 2 * c * (M₁ / c₀)) / (a - c ^ 2) + (M₁ / c₀) ^ 2 / (a - c ^ 2) + 1 +
          M₀ / c₀)) *
        (eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 μ).toReal) := by
  have hw₀ := regWeight_nonneg (c := c) hε.le
  set w : ℂ →ᵇ ℝ := .ofNormedAddCommGroup (regWeight c ε) (contDiff_regWeight hε.le).continuous
    ε⁻¹ fun z ↦ by rw [Real.norm_of_nonneg (hw₀ z)]; exact regWeight_le_inv hε z
  have hwe : (w : ℂ → ℝ) = regWeight c ε :=
    BoundedContinuousFunction.coe_ofNormedAddCommGroup _ _ _ _
  have hwE (z : ℂ) : w z ≤ Real.exp (c * √(1 + ‖z‖ ^ 2)) := hwe ▸ regWeight_le hε.le z
  have hdw (z : ℂ) : ‖fderiv ℝ w z‖ ≤ c * w z := by
    simpa only [hwe, abs_of_nonneg hc] using norm_fderiv_regWeight_le (c := c) hε.le z
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
    hβR (hwe ▸ contDiff_regWeight hε.le) (hwe ▸ hw₀) hdw
    (fun z ↦ (mul_le_mul_of_nonneg_left (hwE z) (hβ₀ z)).trans (hβE z))
    (fun z ↦ (mul_le_mul_of_nonneg_left (hwE z) (norm_nonneg _)).trans (hdβE z)) hFf hFw
  have hWy := norm_smulLp_weight_le_of_norm_smulLp_le hx.continuous hc hT hS hweak w
    (hwe ▸ contDiff_regWeight hε.le) (hwe ▸ hw₀) hdw ENNReal.toReal_nonneg
    (by have := sub_pos.2 hca; positivity) hFw hWu
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
  have hEc : Continuous E := (contDiff_exp_mul_sqrt_one_add_norm_sq (n := 0) c).continuous
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
  have hα : 0 < (c ^ 2 + 1 / 4) / 2 - c ^ 2 := by linarith
  set Ku := (1 + 2 * c * (M₁ / c₀)) / ((c ^ 2 + 1 / 4) / 2 - c ^ 2) +
    (M₁ / c₀) ^ 2 / ((c ^ 2 + 1 / 4) / 2 - c ^ 2) + 1 + M₀ / c₀ with hKu
  have hKu0 : 0 ≤ Ku := by
    have := div_nonneg (by positivity : (0 : ℝ) ≤ 1 + 2 * c * (M₁ / c₀)) hα.le
    have := div_nonneg (sq_nonneg (M₁ / c₀)) hα.le
    have : 0 ≤ M₀ / c₀ := by positivity
    linarith
  set Ky := √(Ku + c ^ 2 * Ku ^ 2) + c * Ku with hKy
  have hKy0 : 0 ≤ Ky := by positivity
  refine ⟨Real.toNNReal (Ky + 1), fun f y hweak horth ↦ ?_⟩
  rcases eq_or_ne (eLpNorm (fun z ↦ E z • f z) 2 μ) ⊤ with htop | hfin
  · rw [htop, ENNReal.mul_top (by simpa using hKy0.trans_lt (lt_add_one Ky))]
    exact le_top
  have hFf : ‖f‖ ≤ (eLpNorm (fun z ↦ E z • f z) 2 μ).toReal := by
    rw [Lp.norm_def]
    refine ENNReal.toReal_mono hfin (eLpNorm_mono (Lp.aestronglyMeasurable f) fun z ↦ ?_)
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by positivity))
  obtain ⟨η, u, hT, hS⟩ := exists_tendsto_toL2_adjL2 hx.continuous hc₀ hgap horth
  have hweak' (ζ : TestField) : ⟪y, adjL2 μ hx.continuous ζ⟫ = ⟪f, toL2 μ ζ⟫ := by
    rw [inner_adjL2, inner_toL2]
    exact hweak ζ ζ.contDiff ζ.hasCompactSupport
  have hu := norm_le_div_of_tendsto hx.continuous hc₀ hgap hT hS hweak'
  -- The bound at each regularized weight, uniformly in the regularization.
  have hn (n : ℕ) : eLpNorm (fun z ↦ regWeight c (1 / (n + 1)) z • y z) 2 μ ≤
      Real.toNNReal (Ky + 1) * eLpNorm (fun z ↦ E z • f z) 2 μ := by
    refine (eLpNorm_regWeight_smul_le hx hsol (by linarith) (fun z hz ↦ (hR z hz).le) hc
      (by linarith) hc₀ hM₀0 hM₁0
      Nat.one_div_pos_of_nat hT hS hweak' hu β (hβe ▸ hb) (hβe ▸ fun z ↦ b.nonneg)
      (hβe ▸ fun z ↦ b.le_one) (fun z hz ↦ hβe ▸ b.one_of_mem_closedBall (by simpa using hz))
      (fun z ↦ hβe ▸ (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le (hM₀ z)))
      (fun z ↦ hβe ▸ (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le (hM₁ z)))
      hfin hFf).trans ?_
    calc _ ≤ ENNReal.ofReal ((Ky + 1) * (eLpNorm (fun z ↦ E z • f z) 2 μ).toReal) := by
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg)
          rw [hKy, hKu]
          linarith
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hfin,
            ENNReal.ofNNReal_toNNReal]
  -- Fatou's lemma as the regularization is removed.
  have hy : AEStronglyMeasurable (fun z ↦ E z • y z) μ :=
    hEc.aestronglyMeasurable.smul (Lp.aestronglyMeasurable y)
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n ↦
    (contDiff_regWeight Nat.one_div_pos_of_nat.le).continuous.aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable y)) _ hy
    (ae_of_all _ fun z ↦ (tendsto_regWeight c z).smul_const (y z))).trans ?_
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
