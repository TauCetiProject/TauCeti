/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Distribution.TestFunction.Divergence
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence.Trace

/-!
# The antisymmetric part of a principal coefficient is a drift

Let `Ω ⊆ ℝⁿ` be open and let `K` be a matrix field on `Ω` with smooth entries and antisymmetric
values, `Kᵀ = -K`. Write `g` for its row divergence, `gᵢ = ∑ⱼ ∂ⱼ Kᵢⱼ`. Then for every `u ∈ H¹(Ω)`
and every test function `v` on `Ω`,

`∫_Ω ⟨K ∇u, ∇v⟩ = ∫_Ω ⟪g, ∇u⟫ v`,

that is, `-∂ᵢ(Kⁱʲ ∂ⱼu) = gⁱ ∂ᵢu` weakly
(`TauCeti.PDE.energyFormH1_ofTestFunctionₗ_eq_of_transpose_eq_neg`). So the principal part of a
divergence-form operator `-∂ᵢ(aⁱʲ ∂ⱼu)` with a smooth antisymmetric part changes, when that part is
removed, only by the first-order drift `g`; the quadratic form `ξ · a ξ`, which is all that
ellipticity sees, does not change at all. When `K` and `g` are bounded the identity holds for every
`v ∈ H¹₀(Ω)` (`TauCeti.PDE.energyFormH1_eq_of_transpose_eq_neg`), and adding `K` to a bounded
principal coefficient `a` is the same as adding `g` to the drift
(`TauCeti.PDE.energyFormH1_add_eq_of_transpose_eq_neg`). A constant antisymmetric matrix has
`g = 0`, so adding it to the principal coefficient does not change the energy form on
`H¹(Ω) × H¹₀(Ω)` (`TauCeti.PDE.energyFormH1_add_const_eq_of_transpose_eq_neg`); without
lower-order terms this is `TauCeti.PDE.energyFormH1_const_coefficientSymmetricPart`. The test
functions must vanish on the boundary: on `H¹(Ω) × H¹(Ω)` the antisymmetric part contributes
boundary terms.

In the plane, with `J = !![0, -1; 1, 0]`, the constant coefficient `1 + k J` has the energy form
of the Laplacian (`TauCeti.PDE.energyFormH1_one_add_const_smul_skew`), so `div ((1 + k J) ∇u) = 0`
and `Δu = 0` have the same weak solutions, although the ellipticity constants of `1 + k J` are
`1` and `√(1 + k²)`. The variable coefficient `1 + x₀ J` satisfies `ξ · (1 + x₀ J) ξ = ‖ξ‖²`, yet
its operator is `-Δu + ∂₁u` (`TauCeti.PDE.energyFormH1_one_add_coord_smul_skew`), with a
different solution set; here the coordinates are `x₀, x₁` and `∂₁` differentiates in `x₁`.

## The argument

For a test function `ψ`, the test vector field `W = Kᵀ ∇ψ - ψ g` is divergence free. Indeed
`div (Kᵀ ∇ψ) = ⟪g, ∇ψ⟫ + ∑ᵢⱼ Kᵢⱼ ∂ᵢ∂ⱼψ`, and the last sum vanishes because the Hessian of `ψ` is
symmetric and `K` is antisymmetric
(`TauCeti.sum_sum_smul_fderiv_fderiv_apply_eq_zero_of_transpose_eq_neg`); and
`div (ψ g) = ⟪∇ψ, g⟫ + ψ ∑ᵢⱼ ∂ᵢ∂ⱼ Kᵢⱼ`, where the double divergence of `K` vanishes for the same
reason (`TauCeti.sum_fderiv_sum_fderiv_apply_eq_zero_of_transpose_eq_neg`). Pairing the weak
gradient of `u` with `W` (`TauCeti.HasWeakFDerivOn.integral_divergenceCLM_smul_eq_neg_integral`)
gives `∫ ⟪∇u, W⟫ = 0`, which is the identity. Test functions are dense in `H¹₀(Ω)`, and both sides
are continuous in `v` when `K` and `g` are bounded.

## Main declarations

All in the `TauCeti.PDE` namespace.

* `energyFormH1_ofTestFunctionₗ_eq_of_transpose_eq_neg`: a smooth antisymmetric principal
  coefficient is the drift given by its row divergence, against test functions.
* `energyFormH1_eq_of_transpose_eq_neg`: the same against `H¹₀(Ω)`, for bounded `K` and `g`.
* `energyFormH1_add_eq_of_transpose_eq_neg`: adding a smooth antisymmetric matrix field to the
  principal coefficient adds its row divergence to the drift.
* `energyFormH1_add_const_eq_of_transpose_eq_neg`: adding a constant antisymmetric matrix to the
  principal coefficient does not change the energy form on `H¹(Ω) × H¹₀(Ω)`.
* `energyFormH1_one_add_const_smul_skew` and `energyFormH1_one_add_coord_smul_skew`: the planar
  witnesses `1 + k J` and `1 + x₀ J`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 8.1 (the weak formulation of divergence-form operators).
* G. Seregin, L. Silvestre, V. Šverák, A. Zlatoš, *On divergence-free drifts*, J. Differential
  Equations **252** (2012), 505–540 (a divergence-free drift as the divergence of an
  antisymmetric matrix field).
-/

public section

open MeasureTheory Set TopologicalSpace TestFunction Filter
open scoped ContDiff Distributions InnerProductSpace Gradient Matrix Topology

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Opens (EuclideanSpace ℝ ι)}
  {K : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}

/-- The test vector field `Kᵀ ∇ψ - ψ g`, for the row divergence `g` of a smooth antisymmetric
matrix field `K`, is divergence free. -/
private theorem divergenceCLM_sum_sub_eq_zero (hK : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ K x i j) Ω)
    (hKt : ∀ x ∈ Ω, (K x)ᵀ = -K x)
    (hg : ∀ x ∈ Ω, ∀ i, g x i = ∑ j, fderiv ℝ (fun y ↦ K y i j) x (EuclideanSpace.single j 1))
    (hr : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ WithLp.toLp 2 (K x i)) Ω) (hgs : ContDiffOn ℝ ∞ g Ω)
    (ψ : 𝓓(Ω, ℝ)) (x : EuclideanSpace ℝ ι) :
    divergenceCLM (∑ i, smulTestField (hr i) (lineDerivCLM ℝ (EuclideanSpace.single i 1) ψ) -
      smulTestField hgs ψ) x = 0 := by
  by_cases hx : x ∈ Ω
  swap
  · exact image_eq_zero_of_notMem_tsupport fun h ↦ hx ((divergenceCLM _).tsupport_subset h)
  -- The divergence of each row `Kᵢ` is the entry `gᵢ`.
  have htr : ∀ i, LinearMap.trace ℝ _ (fderiv ℝ (fun y ↦ WithLp.toLp 2 (K y i)) x :
      EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) = g x i := fun i ↦ by
    rw [trace_fderiv_eq_sum_fderiv_apply_single
      (((hr i).contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)), hg x hx i]
  -- The divergence of `g` is the double divergence of `K`, which vanishes.
  have htrg : LinearMap.trace ℝ _ (fderiv ℝ g x :
      EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) = 0 := by
    rw [trace_fderiv_eq_sum_fderiv_apply_single
        ((hgs.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)),
      ← sum_fderiv_sum_fderiv_apply_eq_zero_of_transpose_eq_neg
        (fun i j ↦ (hK i j).contDiffAt (Ω.isOpen.mem_nhds hx)) (by simp)
        (Filter.eventually_of_mem (Ω.isOpen.mem_nhds hx) hKt) fun j ↦ EuclideanSpace.single j 1]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (Ω.isOpen.mem_nhds hx)
      fun y hy ↦ hg y hy i)]
  -- The Hessian of `ψ`, contracted with the antisymmetric matrix `K x`, vanishes.
  have hhess : ∑ i, ⟪∇ (fun y ↦ lineDeriv ℝ (ψ : EuclideanSpace ℝ ι → ℝ) y
      (EuclideanSpace.single i 1)) x, WithLp.toLp 2 (K x i)⟫_ℝ = 0 := by
    rw [← sum_sum_smul_fderiv_fderiv_apply_eq_zero_of_transpose_eq_neg
      (ψ.contDiff.contDiffAt (x := x)) (by simp) (fun j ↦ EuclideanSpace.single j 1) (hKt x hx)]
    simp [-inner_gradient_left, TestFunction.lineDeriv_eq_fderiv ψ, PiLp.inner_apply,
      gradient_apply_eq_fderiv_apply_single,
      (ψ.contDiff.contDiffAt.hasFDerivAt_fderiv_apply (by simp) _).fderiv]
  have hgrad : ⟪∇ (ψ : EuclideanSpace ℝ ι → ℝ) x, g x⟫_ℝ =
      ∑ i, lineDeriv ℝ (ψ : EuclideanSpace ℝ ι → ℝ) x (EuclideanSpace.single i 1) * g x i := by
    simp [-inner_gradient_left, PiLp.inner_apply, gradient_apply_eq_fderiv_apply_single,
      TestFunction.lineDeriv_eq_fderiv ψ, mul_comm]
  rw [map_sub, map_sum, sub_apply, sum_apply, Finset.sum_congr rfl fun i _ ↦
      divergenceCLM_smulTestField (hr i) _ hx, divergenceCLM_smulTestField hgs ψ hx,
    Finset.sum_add_distrib]
  simp only [coe_lineDerivCLM]
  rw [hhess, htrg, hgrad]
  simp [htr]

omit [DecidableEq ι] in
/-- The rows of a matrix field with smooth entries are smooth vector fields. -/
private theorem contDiffOn_toLp_row (hK : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ K x i j) Ω) (i : ι) :
    ContDiffOn ℝ ∞ (fun x ↦ WithLp.toLp 2 (K x i)) Ω :=
  contDiffOn_piLp' 2 fun j ↦ hK i j

/-- The row divergence of a matrix field with smooth entries is smooth. -/
private theorem contDiffOn_of_eq_sum_fderiv (hK : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ K x i j) Ω)
    (hg : ∀ x ∈ Ω, ∀ i, g x i = ∑ j, fderiv ℝ (fun y ↦ K y i j) x (EuclideanSpace.single j 1)) :
    ContDiffOn ℝ ∞ g Ω :=
  contDiffOn_piLp' 2 fun i ↦ (ContDiffOn.sum fun j _ ↦
    ((hK i j).fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply contDiffOn_const).congr
      fun x hx ↦ hg x hx i

omit [DecidableEq ι] in
/-- A matrix field with smooth entries is continuous. -/
private theorem continuousOn_of_contDiffOn_apply
    (hK : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ K x i j) Ω) : ContinuousOn K Ω :=
  continuousOn_pi.2 fun i ↦ continuousOn_pi.2 fun j ↦ (hK i j).continuousOn

variable {mu : Measure (EuclideanSpace ℝ ι)}

omit [DecidableEq ι] in
/-- A bounded matrix field with smooth entries, as a principal coefficient alone, has an essentially
bounded field of pointwise energy forms on `Ω`. -/
private theorem memLp_energyIntegrand_of_contDiffOn_apply
    (hK : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ K x i j) Ω) {Λ : ℝ}
    (hKb : ∀ x ∈ Ω, ‖matrixBilinearForm (K x)‖ ≤ Λ) :
    MemLp (fun x ↦ energyIntegrand (K x) ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x)
      ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤ (mu.restrict Ω) :=
  memLp_energyIntegrand_of_continuousOn_of_norm_le (b := 0) (c := 0)
    (continuousOn_of_contDiffOn_apply hK) continuousOn_const continuousOn_const hKb
    (beta := 0) (fun _ _ ↦ by simp) (gamma := 0) (fun _ _ ↦ by simp)

/-- The bounded row divergence of a matrix field with smooth entries, as a drift alone, has an
essentially bounded field of pointwise energy forms on `Ω`. -/
private theorem memLp_energyIntegrand_drift_of_eq_sum_fderiv
    (hK : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ K x i j) Ω)
    (hg : ∀ x ∈ Ω, ∀ i, g x i = ∑ j, fderiv ℝ (fun y ↦ K y i j) x (EuclideanSpace.single j 1))
    {β : ℝ} (hgb : ∀ x ∈ Ω, ‖g x‖ ≤ β) :
    MemLp (fun x ↦ energyIntegrand ((0 : EuclideanSpace ℝ ι → Matrix ι ι ℝ) x) (g x)
      ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤ (mu.restrict Ω) :=
  memLp_energyIntegrand_of_continuousOn_of_norm_le (a := 0) (c := 0)
    continuousOn_const (contDiffOn_of_eq_sum_fderiv hK hg).continuousOn continuousOn_const
    (Lam := 0) (fun _ _ ↦ by simp [ContinuousLinearMap.opNorm_zero]) hgb
    (gamma := 0) (fun _ _ ↦ by simp)

variable [mu.IsAddHaarMeasure]

/-- **The antisymmetric part of a principal coefficient is a drift.** Let `K` be a matrix field
with entries smooth on `Ω` and antisymmetric values, `Kᵀ = -K`, and let `g` be its row divergence,
`gᵢ = ∑ⱼ ∂ⱼ Kᵢⱼ` on `Ω`. Then `∫_Ω ⟨K ∇u, ∇ψ⟩ = ∫_Ω ⟪g, ∇u⟫ ψ` for every `u ∈ H¹(Ω)` and every
test function `ψ`: weakly, `-∂ᵢ(Kⁱʲ ∂ⱼu) = gⁱ ∂ᵢu`. No bound on `K` or `g` is needed. -/
theorem energyFormH1_ofTestFunctionₗ_eq_of_transpose_eq_neg
    (hK : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ K x i j) Ω) (hKt : ∀ x ∈ Ω, (K x)ᵀ = -K x)
    (hg : ∀ x ∈ Ω, ∀ i, g x i = ∑ j, fderiv ℝ (fun y ↦ K y i j) x (EuclideanSpace.single j 1))
    (u : W1p mu Ω 2) (ψ : 𝓓(Ω, ℝ)) :
    energyFormH1 K 0 0 u (W1p.ofTestFunctionₗ mu Ω 2 ψ) =
      energyFormH1 0 g 0 u (W1p.ofTestFunctionₗ mu Ω 2 ψ) := by
  have hr := contDiffOn_toLp_row hK
  have hgs := contDiffOn_of_eq_sum_fderiv hK hg
  have hdiv := divergenceCLM_sum_sub_eq_zero hK hKt hg hr hgs ψ
  set Φ : 𝓓(Ω, EuclideanSpace ℝ ι) :=
    ∑ i, smulTestField (hr i) (lineDerivCLM ℝ (EuclideanSpace.single i 1) ψ)
  set Ψ : 𝓓(Ω, EuclideanSpace ℝ ι) := smulTestField hgs ψ
  have hloc := W1p.locallyIntegrableOn_gradient u
  -- A test vector field vanishes off `Ω`, so its pairing with `∇u` may be integrated over `E`.
  have hpair : ∀ Θ : 𝓓(Ω, EuclideanSpace ℝ ι), ∫ x in Ω, ⟪Θ x, W1p.gradient u x⟫_ℝ ∂mu =
      ∫ x, ⟪Θ x, W1p.gradient u x⟫_ℝ ∂mu := fun Θ ↦
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (Θ.tsupport_subset h), inner_zero_left]
  have hΦ : energyFormH1 K 0 0 u (W1p.ofTestFunctionₗ mu Ω 2 ψ) =
      ∫ x, ⟪Φ x, W1p.gradient u x⟫_ℝ ∂mu := by
    rw [energyFormH1_zero_zero_eq_setIntegral, ← hpair]
    refine integral_congr_ae ?_
    filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) 2 ψ] with x hx
    rw [W1p.gradient_ofTestFunctionₗ, hx, matrixBilinearForm_apply]
    simp [Φ, sum_apply, sum_inner, inner_smul_left, dotProduct, Matrix.mulVec,
      gradient_apply_eq_fderiv_apply_single, TestFunction.lineDeriv_eq_fderiv ψ, PiLp.inner_apply,
      mul_comm]
  have hΨ : energyFormH1 0 g 0 u (W1p.ofTestFunctionₗ mu Ω 2 ψ) =
      ∫ x, ⟪Ψ x, W1p.gradient u x⟫_ℝ ∂mu := by
    rw [energyFormH1_def, ← hpair]
    refine integral_congr_ae ?_
    filter_upwards [testFunctionLp_apply_ae (mu := mu) 2 ψ] with x hx
    simp [Ψ, energyIntegrand_apply, driftForm_apply, massForm_apply, jetField_apply, hx,
      inner_smul_left, mul_comm]
  have hzero := (W1p.hasWeakFDerivOn u).integral_divergenceCLM_smul_eq_neg_integral (Φ - Ψ)
  simp only [hdiv, zero_smul, integral_zero, zero_eq_neg] at hzero
  rw [hΦ, hΨ, ← sub_eq_zero, ← integral_sub (TestFunction.integrable_inner hloc Φ)
    (TestFunction.integrable_inner hloc Ψ), ← hzero]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [innerSL_apply_apply, sub_apply, inner_sub_right, real_inner_comm]

/-- **The antisymmetric part of a principal coefficient is a drift**, on `H¹₀(Ω)`. Let `K` be a
bounded matrix field with entries smooth on `Ω` and antisymmetric values, whose row divergence
`gᵢ = ∑ⱼ ∂ⱼ Kᵢⱼ` is bounded on `Ω`. Then `∫_Ω ⟨K ∇u, ∇v⟩ = ∫_Ω ⟪g, ∇u⟫ v` for every `u ∈ H¹(Ω)`
and every `v ∈ H¹₀(Ω)`. -/
theorem energyFormH1_eq_of_transpose_eq_neg
    (hK : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ K x i j) Ω) (hKt : ∀ x ∈ Ω, (K x)ᵀ = -K x)
    (hg : ∀ x ∈ Ω, ∀ i, g x i = ∑ j, fderiv ℝ (fun y ↦ K y i j) x (EuclideanSpace.single j 1))
    {Λ β : ℝ} (hKb : ∀ x ∈ Ω, ‖matrixBilinearForm (K x)‖ ≤ Λ) (hgb : ∀ x ∈ Ω, ‖g x‖ ≤ β)
    (u : W1p mu Ω 2) (v : W1p0 mu Ω 2) :
    energyFormH1 K 0 0 u v = energyFormH1 0 g 0 u v := by
  have hcK := memLp_energyIntegrand_of_contDiffOn_apply (mu := mu) hK hKb
  have hcg := memLp_energyIntegrand_drift_of_eq_sum_fderiv (mu := mu) hK hg hgb
  have hclosed : IsClosed {w : W1p mu Ω 2 | energyFormH1L hcK u w = energyFormH1L hcg u w} :=
    isClosed_eq (energyFormH1L hcK u).continuous (energyFormH1L hcg u).continuous
  have hmem := w1p0Submodule_subset_of_isClosed hclosed (fun ψ ↦ by
    simpa only [Set.mem_ofPred_eq, energyFormH1L_apply] using
      energyFormH1_ofTestFunctionₗ_eq_of_transpose_eq_neg hK hKt hg u ψ) v.property
  simpa only [Set.mem_ofPred_eq, energyFormH1L_apply] using hmem

/-- **Moving the antisymmetric part of the principal coefficient into the drift.** Adding to the
principal coefficient of a bounded coefficient triple `(a, b, c)` a bounded matrix field `K` with
smooth entries and antisymmetric values, whose row divergence `g` is bounded, has the same effect
on the energy form on `H¹(Ω) × H¹₀(Ω)` as adding `g` to the drift. -/
theorem energyFormH1_add_eq_of_transpose_eq_neg {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Ω))
    (hK : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ K x i j) Ω) (hKt : ∀ x ∈ Ω, (K x)ᵀ = -K x)
    (hg : ∀ x ∈ Ω, ∀ i, g x i = ∑ j, fderiv ℝ (fun y ↦ K y i j) x (EuclideanSpace.single j 1))
    {Λ β : ℝ} (hKb : ∀ x ∈ Ω, ‖matrixBilinearForm (K x)‖ ≤ Λ) (hgb : ∀ x ∈ Ω, ‖g x‖ ≤ β)
    (u : W1p mu Ω 2) (v : W1p0 mu Ω 2) :
    energyFormH1 (a + K) b c u v = energyFormH1 a (b + g) c u v := by
  have hcK := memLp_energyIntegrand_of_contDiffOn_apply (mu := mu) hK hKb
  have hcg := memLp_energyIntegrand_drift_of_eq_sum_fderiv (mu := mu) hK hg hgb
  calc energyFormH1 (a + K) b c u v = energyFormH1 (a + K) (b + 0) (c + 0) u v := by simp
    _ = energyFormH1 a b c u v + energyFormH1 K 0 0 u v := energyFormH1_add hcoeff hcK u v
    _ = energyFormH1 a b c u v + energyFormH1 0 g 0 u v := by
      rw [energyFormH1_eq_of_transpose_eq_neg hK hKt hg hKb hgb u v]
    _ = energyFormH1 (a + 0) (b + g) (c + 0) u v := (energyFormH1_add hcoeff hcg u v).symm
    _ = energyFormH1 a (b + g) c u v := by simp

omit [DecidableEq ι] in
/-- Adding a constant antisymmetric matrix `A` to the principal coefficient of a bounded coefficient
triple does not change the energy form on `H¹(Ω) × H¹₀(Ω)`. -/
theorem energyFormH1_add_const_eq_of_transpose_eq_neg {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Ω))
    {A : Matrix ι ι ℝ} (hA : Aᵀ = -A) (u : W1p mu Ω 2) (v : W1p0 mu Ω 2) :
    energyFormH1 (fun x ↦ a x + A) b c u v = energyFormH1 a b c u v := by
  classical
  have h := energyFormH1_add_eq_of_transpose_eq_neg (K := fun _ ↦ A) (g := 0) hcoeff
    (fun _ _ ↦ contDiffOn_const) (fun _ _ ↦ hA) (fun _ _ _ ↦ by simp) (fun _ _ ↦ le_rfl)
    (fun _ _ ↦ (norm_zero (E := EuclideanSpace ℝ ι)).le) u v
  rwa [add_zero] at h

/-! ### Witnesses in the plane -/

section Plane

variable {Ω : Opens (EuclideanSpace ℝ (Fin 2))} {mu : Measure (EuclideanSpace ℝ (Fin 2))}
  [mu.IsAddHaarMeasure]

/-- In the plane, the constant coefficient `1 + k J`, with `J = !![0, -1; 1, 0]` the rotation by
a right angle, has the energy form of the Laplacian on `H¹(Ω) × H¹₀(Ω)`: the weak solutions of
`div ((1 + k J) ∇u) = f` and of `Δu = f` coincide. -/
theorem energyFormH1_one_add_const_smul_skew (k : ℝ) (u : W1p mu Ω 2) (v : W1p0 mu Ω 2) :
    energyFormH1 (fun _ ↦ 1 + k • !![0, -1; 1, 0]) 0 0 u v = energyFormH1 1 0 0 u v := by
  refine energyFormH1_add_const_eq_of_transpose_eq_neg (a := 1)
    (memLp_energyIntegrand_const_zero_zero 1) ?_ u v
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- In the plane, the variable coefficient `1 + x₀ J`, with `J = !![0, -1; 1, 0]`, satisfies
`ξ · (1 + x₀ J) ξ = ‖ξ‖²`, but on a bounded open set its energy form on `H¹(Ω) × H¹₀(Ω)` is that of
`-Δu + ∂₁u`: the Laplacian with the constant drift `e₁`. -/
theorem energyFormH1_one_add_coord_smul_skew
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 2)))) (u : W1p mu Ω 2)
    (v : W1p0 mu Ω 2) :
    energyFormH1 (fun x ↦ 1 + x 0 • !![0, -1; 1, 0]) 0 0 u v =
      energyFormH1 1 (fun _ ↦ EuclideanSpace.single 1 1) 0 u v := by
  obtain ⟨R, hR⟩ := hΩ.subset_closedBall 0
  have hcoord : ∀ (y : EuclideanSpace ℝ (Fin 2)) (i : Fin 2),
      HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) ↦ z i)
        (EuclideanSpace.proj (𝕜 := ℝ) i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) y :=
    fun y i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
  have h := energyFormH1_add_eq_of_transpose_eq_neg (a := 1) (b := 0) (c := 0)
    (K := fun x ↦ x 0 • !![0, -1; 1, 0]) (g := fun _ ↦ EuclideanSpace.single 1 1)
    (memLp_energyIntegrand_const_zero_zero 1) (fun i j ↦ ?_) (fun x _ ↦ ?_) (fun x _ i ↦ ?_)
    (Λ := 2 * R) (β := 1) (fun x hx ↦ ?_) (fun _ _ ↦ by simp) u v
  · rwa [zero_add] at h
  · simp only [Matrix.smul_apply, smul_eq_mul]
    exact ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.mul contDiff_const).contDiffOn
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · fin_cases i <;> simp [((hcoord x 0).mul_const _).fderiv]
  · have h0 : |x 0| ≤ R := (PiLp.norm_apply_le x 0).trans (by simpa using hR hx)
    have hsum : ∑ i, ∑ j, |(x 0 • !![(0 : ℝ), -1; 1, 0]) i j| = 2 * |x 0| := by
      simp [Fin.sum_univ_two, two_mul]
    refine (norm_matrixBilinearForm_le_sum_abs _).trans ?_
    rw [hsum]
    linarith

end Plane

end PDE

end TauCeti
