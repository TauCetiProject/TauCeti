/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Directional differentiation and linear maps on Schwartz space

Directional derivatives of a Schwartz function commute, since its second derivative is symmetric,
and they commute with translation (`SchwartzMap.lineDerivOp_compSubConstCLM`).
Near a point where a Schwartz function is constant, its line derivatives vanish
(`SchwartzMap.lineDerivOp_eventuallyEq_zero`).
For a Schwartz function valued in a finite `L^p` product, such as Euclidean space, taking a
coordinate commutes with differentiation along any direction
(`SchwartzMap.fderiv_apply_eq_lineDerivOp_apply`).
On the plane `ℂ`, the Laplacian is the sum of the second derivatives along `1` and `I`.

Applying a continuous real- or complex-linear map to the values of a Schwartz function commutes
with directional differentiation, and hence with the Laplacian. In particular, real and imaginary
parts, and the embedding of real-valued functions into complex Schwartz space, commute with
differentiation.

Pairing with a function `g` of temperate growth through a continuous bilinear map `B` satisfies
the Leibniz rule `∂_v B(f, g) = B(f, ∂_v g) + B(∂_v f, g)` (`SchwartzMap.lineDerivOp_bilinLeftCLM`).
For multiplication by `g` it reads `∂_v (g f) = (∂_v g) f + g ∂_v f`, and for a continuous
real-linear `L` with values in a normed field over `ℝ`, such as `ℝ` or `ℂ`, it reads
`∂_v (L f) = L ∂_v f + L v f`, with iterate
`∂_v^(k+1) (L f) = L ∂_v^(k+1) f + (k + 1) L v ∂_v^k f`; when `f` vanishes outside
`closedBall 0 t`, this bounds at each point `x`
`‖∂_v^(k+1) (L f) (x)‖ ≤ t ‖L‖ ‖∂_v^(k+1) f (x)‖ + (k + 1) ‖L‖ ‖v‖ ‖∂_v^k f (x)‖`
(`SchwartzMap.norm_iterate_lineDerivOp_smulLeftCLM_clm_le_of_support_subset_closedBall`). On the
Fourier side, multiplying a symbol by `⟪h, ξ⟫` differentiates its kernel along `h`, so these
identities control the derivatives of the symbol of a differentiated kernel.

Integrating by parts along an orthonormal basis gives Green's identity
`∫ B(f, Δg) = -∑ᵢ ∫ B(∂_{bᵢ} f, ∂_{bᵢ} g)` for a continuous bilinear map `B`
(`SchwartzMap.integral_bilinear_laplacian_right_eq_neg_sum`). For the inner product this reads
`∫ ⟪f, Δf⟫ = -∑ᵢ ‖∂_{bᵢ} f‖₂²` (`SchwartzMap.integral_inner_laplacian_right_self_eq_neg_sum`),
and for the shifted Laplacian `-Δ + c` it is the energy identity
`∫ ⟪f, (-Δ + c) f⟫ = ∑ᵢ ‖∂_{bᵢ} f‖₂² + c ‖f‖₂²`
(`SchwartzMap.integral_inner_neg_laplacian_add_smul_self`).
-/

public section

namespace SchwartzMap

open scoped SchwartzMap LineDeriv

variable {𝕜 V F G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

section RCLike

variable [RCLike 𝕜] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]

/-- Directional differentiation commutes with a continuous linear map on the values of a
Schwartz function. -/
@[simp]
theorem lineDerivOp_postcompCLM (φ : 𝓢(V, F)) (L : F →L[𝕜] G) (v : V) :
    ∂_{v} (φ.postcompCLM L) = (∂_{v} φ).postcompCLM L := by
  ext x
  -- `φ.postcompCLM L` is `L ∘ φ` as a function; `L` is differentiated as a real-linear map.
  have hfun : ⇑(φ.postcompCLM L) = L.restrictScalars ℝ ∘ φ := by
    ext y
    simp
  rw [lineDerivOp_apply_eq_fderiv, hfun,
    (L.restrictScalars ℝ).fderiv_comp_left φ.differentiableAt]
  simp [lineDerivOp_apply_eq_fderiv]

open Laplacian in
/-- The Laplacian commutes with a continuous linear map on the values of a Schwartz
function. -/
@[simp]
theorem laplacian_postcompCLM {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (φ : 𝓢(W, F)) (L : F →L[𝕜] G) :
    Δ (φ.postcompCLM L) = (Δ φ).postcompCLM L := by
  ext x
  -- `φ.postcompCLM L` is `L ∘ φ` as a function; `L` is applied as a real-linear map.
  have hfun : ⇑(φ.postcompCLM L) = L.restrictScalars ℝ ∘ φ := by
    ext y
    simp
  rw [laplacian_apply, hfun, (φ.smooth 2).contDiffAt.laplacian_CLM_comp_left, postcompCLM_apply,
    laplacian_apply, Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']

/-- **Directional derivatives of Schwartz functions commute.** -/
theorem lineDerivOp_comm (f : 𝓢(V, F)) (v w : V) : ∂_{v} (∂_{w} f) = ∂_{w} (∂_{v} f) := by
  ext x
  have hd : DifferentiableAt ℝ (fderiv ℝ (f : V → F)) x :=
    ((f.smooth ⊤).fderiv_right (m := 1) (by simp)).differentiable one_ne_zero x
  have hfun (u : V) : ⇑(∂_{u} f : 𝓢(V, F)) = fun y ↦ fderiv ℝ (f : V → F) y u :=
    funext fun y ↦ lineDerivOp_apply_eq_fderiv u f y
  rw [lineDerivOp_apply_eq_fderiv, lineDerivOp_apply_eq_fderiv, hfun, hfun,
    fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using ((f.smooth 2).contDiffAt.isSymmSndFDerivAt (by simp)).eq v w

/-- Directional differentiation commutes with translation. -/
@[simp]
theorem lineDerivOp_compSubConstCLM (f : 𝓢(V, F)) (a v : V) :
    ∂_{v} (f.compSubConstCLM 𝕜 a) = (∂_{v} f).compSubConstCLM 𝕜 a := by
  ext x
  rw [lineDerivOp_apply_eq_fderiv, funext (compSubConstCLM_apply f a), fderiv_comp_sub,
    compSubConstCLM_apply, lineDerivOp_apply_eq_fderiv]

end RCLike

open scoped Topology in
/-- A Schwartz function that is constant near a point has line derivatives vanishing near that
point. -/
theorem lineDerivOp_eventuallyEq_zero {f : 𝓢(V, F)} {x : V} {c : F}
    (hf : ⇑f =ᶠ[𝓝 x] fun _ ↦ c) (v : V) : ⇑(∂_{v} f : 𝓢(V, F)) =ᶠ[𝓝 x] fun _ ↦ 0 := by
  filter_upwards [hf.eventually_nhds] with y hy
  rw [lineDerivOp_apply_eq_fderiv, Filter.EventuallyEq.fderiv_eq (f := fun _ ↦ c) hy,
    fderiv_const_apply, zero_apply]

open scoped ENNReal in
/-- Taking a coordinate commutes with directional differentiation: for a Schwartz function with
values in a finite `L^p` product (for instance Euclidean space), the derivative along `v` of its
`i`-th coordinate is the `i`-th coordinate of its line derivative along `v`. -/
@[simp]
theorem fderiv_apply_eq_lineDerivOp_apply {ι : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {β : ι → Type*} [∀ i, NormedAddCommGroup (β i)] [∀ i, NormedSpace ℝ (β i)]
    (f : 𝓢(V, PiLp p β)) (i : ι) (x v : V) :
    fderiv ℝ (fun y ↦ f y i) x v = ∂_{v} f x i := by
  have hp := (PiLp.proj p β (𝕜 := ℝ) i).fderiv_comp_left f.differentiableAt (x := x)
  simpa only [lineDerivOp_apply_eq_fderiv, Function.comp_def, PiLp.proj_apply,
    ContinuousLinearMap.comp_apply] using congr($hp v)

open Laplacian in
/-- **The Laplacian on the plane in coordinates**: `Δ f = ∂₁² f + ∂₂² f` for a Schwartz function
`f` on `ℂ`, where `∂₁` and `∂₂` differentiate along `1` and `I`. -/
theorem laplacian_eq_lineDerivOp_one_I (f : 𝓢(ℂ, F)) :
    Δ f = ∂_{(1 : ℂ)} (∂_{(1 : ℂ)} f) + ∂_{Complex.I} (∂_{Complex.I} f) := by
  simp [laplacian_eq_sum Complex.orthonormalBasisOneI, Fin.sum_univ_two]

variable [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]

/-- **The Leibniz rule for a continuous bilinear map with a function of temperate growth**:
`∂_v B(f, g) = B(f, ∂_v g) + B(∂_v f, g)`, where `∂_v g` is `x ↦ Dg(x) v`. -/
theorem lineDerivOp_bilinLeftCLM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace 𝕜 E] (f : 𝓢(V, E)) (B : E →L[𝕜] F →L[𝕜] G) {g : V → F}
    (hg : g.HasTemperateGrowth) (v : V) :
    ∂_{v} (bilinLeftCLM B hg f) =
      bilinLeftCLM B (hg.fderiv_apply v) f + bilinLeftCLM B hg (∂_{v} f) := by
  ext x
  -- `B` is differentiated as a real-bilinear map.
  have hB : ⇑(bilinLeftCLM B hg f) = fun y ↦ B.bilinearRestrictScalars ℝ (f y) (g y) := rfl
  rw [lineDerivOp_apply_eq_fderiv, hB, (B.bilinearRestrictScalars ℝ).fderiv_of_bilinear
    f.differentiableAt (hg.1.differentiable (by simp) x)]
  simp [lineDerivOp_apply_eq_fderiv]

/-- **The Leibniz rule for multiplication by a function of temperate growth**:
`∂_v (g f) = (∂_v g) f + g ∂_v f`, where `∂_v g` is `x ↦ Dg(x) v`. -/
theorem lineDerivOp_smulLeftCLM {g : V → 𝕜} (hg : g.HasTemperateGrowth) (f : 𝓢(V, F)) (v : V) :
    ∂_{v} (smulLeftCLM F g f) =
      smulLeftCLM F (fun x ↦ fderiv ℝ g x v) f + smulLeftCLM F g (∂_{v} f) := by
  -- Multiplication by a function of temperate growth is `bilinLeftCLM` of flipped scalar
  -- multiplication.
  have hsmul {h : V → 𝕜} (hh : h.HasTemperateGrowth) :
      smulLeftCLM F h = bilinLeftCLM (ContinuousLinearMap.lsmul 𝕜 𝕜).flip hh := by
    simp [smulLeftCLM, hh]
  rw [hsmul hg, hsmul (hg.fderiv_apply v), lineDerivOp_bilinLeftCLM]

/-- **The Leibniz rule for multiplication by a linear function**:
`∂_v (L f) = L ∂_v f + L v f` for a continuous real-linear map `L : V →L[ℝ] 𝕜`. -/
theorem lineDerivOp_smulLeftCLM_clm (f : 𝓢(V, F)) (L : V →L[ℝ] 𝕜) (v : V) :
    ∂_{v} (smulLeftCLM F L f) = smulLeftCLM F L (∂_{v} f) + L v • f := by
  rw [lineDerivOp_smulLeftCLM L.hasTemperateGrowth, add_comm]
  simp

/-- **The iterated Leibniz rule for multiplication by a linear function**:
`∂_v^(k+1) (L f) = L ∂_v^(k+1) f + (k + 1) L v ∂_v^k f` for a continuous real-linear map
`L : V →L[ℝ] 𝕜`. -/
theorem iterate_lineDerivOp_smulLeftCLM_clm (f : 𝓢(V, F)) (L : V →L[ℝ] 𝕜) (v : V) (k : ℕ) :
    (∂_{v})^[k + 1] (smulLeftCLM F L f) =
      smulLeftCLM F L ((∂_{v})^[k + 1] f) + ((k + 1) * L v) • (∂_{v})^[k] f := by
  -- Directional differentiation commutes with multiplication by a constant of `𝕜`.
  have hsmul (c : 𝕜) (g : 𝓢(V, F)) : ∂_{v} (c • g) = c • ∂_{v} g := by
    ext x
    simp [lineDerivOp_apply_eq_fderiv, fderiv_const_smul g.differentiableAt]
  induction k with
  | zero => simpa using lineDerivOp_smulLeftCLM_clm f L v
  | succ k ih =>
    calc (∂_{v})^[k + 1 + 1] (smulLeftCLM F L f)
        = ∂_{v} (smulLeftCLM F L ((∂_{v})^[k + 1] f) + ((k + 1) * L v) • (∂_{v})^[k] f) := by
          rw [Function.iterate_succ_apply' _ _ (smulLeftCLM F L f), ih]
      _ = smulLeftCLM F L ((∂_{v})^[k + 1 + 1] f) + ((↑(k + 1) + 1) * L v) • (∂_{v})^[k + 1] f := by
          rw [LineDeriv.lineDerivOp_add, hsmul, lineDerivOp_smulLeftCLM_clm]
          simp only [Function.iterate_succ_apply']
          rw [add_assoc, ← add_smul]
          congr 2
          push_cast
          ring

/-- At each point `x`, for `f` supported in `Metric.closedBall 0 t`, the iterated Leibniz rule
bounds the `(k + 1)`-st directional derivative of `L f` along `v` by
`‖∂_v^(k+1) (L f) (x)‖ ≤ t * ‖L‖ * ‖∂_v^(k+1) f (x)‖ + (k + 1) * ‖L‖ * ‖v‖ * ‖∂_v^k f (x)‖`. -/
theorem norm_iterate_lineDerivOp_smulLeftCLM_clm_le_of_support_subset_closedBall (f : 𝓢(V, F))
    (L : V →L[ℝ] 𝕜) {t : ℝ} (hf : Function.support f ⊆ Metric.closedBall 0 t) (v : V) (k : ℕ)
    (x : V) :
    ‖(∂_{v})^[k + 1] (smulLeftCLM F L f) x‖ ≤
      t * ‖L‖ * ‖(∂_{v})^[k + 1] f x‖ + (k + 1) * ‖L‖ * ‖v‖ * ‖(∂_{v})^[k] f x‖ := by
  have hsupp : Function.support ((∂_{v})^[k + 1] f : 𝓢(V, F)) ⊆ Metric.closedBall 0 t :=
    (subset_tsupport _).trans <|
      (LineDeriv.iteratedLineDerivOp_const_eq_iter_lineDerivOp (k + 1) v f ▸
        tsupport_iteratedLineDerivOp_subset _ f).trans <|
        closure_minimal hf Metric.isClosed_closedBall
  rw [iterate_lineDerivOp_smulLeftCLM_clm, add_apply, smul_apply,
    smulLeftCLM_apply_apply L.hasTemperateGrowth]
  refine (norm_add_le _ _).trans
    (add_le_add (L.norm_apply_smul_le_of_support_subset_closedBall hsupp x) ?_)
  -- The scalar `k + 1`, cast into `𝕜`, is the image of the real `k + 1` and keeps its norm.
  have hk : ‖((k : 𝕜) + 1)‖ = k + 1 := by
    rw [show ((k : 𝕜) + 1) = algebraMap ℝ 𝕜 (k + 1) by simp, norm_algebraMap',
      Real.norm_of_nonneg (by positivity)]
  rw [norm_smul, norm_mul, hk, mul_assoc ((k : ℝ) + 1) ‖L‖ ‖v‖]
  gcongr
  exact L.le_opNorm v

open MeasureTheory LineDeriv Laplacian in
/-- **Green's identity on Schwartz space**: for a continuous bilinear map `B` and an orthonormal
basis `b`, `∫ B(f, Δg) = -∑ᵢ ∫ B(∂_{bᵢ} f, ∂_{bᵢ} g)`. -/
theorem integral_bilinear_laplacian_right_eq_neg_sum {E F₁ F₂ F₃ ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] [NormedAddCommGroup F₁]
    [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup F₃]
    [NormedSpace ℝ F₃] [Fintype ι] (b : OrthonormalBasis ι ℝ E) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂))
    (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃) :
    ∫ x, B (f x) (Δ g x) ∂μ = -∑ i, ∫ x, B (∂_{b i} f x) (∂_{b i} g x) ∂μ := by
  simp_rw [laplacian_eq_sum b, _root_.sum_apply, map_sum]
  have hint : ∀ i ∈ Finset.univ, Integrable (fun x => B (f x) (∂_{b i} (∂_{b i} g) x)) μ :=
    fun i _ => (pairing B f (∂_{b i} (∂_{b i} g))).integrable
  rw [integral_finsetSum _ hint, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ =>
    integral_bilinear_lineDerivOp_right_eq_neg_left f (∂_{b i} g) B (b i)

open MeasureTheory LineDeriv Laplacian RealInnerProductSpace in
/-- Green's identity for the `L²` pairing of a Schwartz function with its Laplacian: for an
orthonormal basis `b`, `∫ ⟪f, Δf⟫ = -∑ᵢ ∫ ‖∂_{bᵢ} f‖²`. -/
theorem integral_inner_laplacian_right_self_eq_neg_sum {E F ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fintype ι] (b : OrthonormalBasis ι ℝ E) (f : 𝓢(E, F)) :
    ∫ x, ⟪f x, Δ f x⟫ ∂μ = -∑ i, ∫ x, ‖∂_{b i} f x‖ ^ 2 ∂μ := by
  have h : ∫ x, ⟪f x, Δ f x⟫ ∂μ = -∑ i, ∫ x, ⟪∂_{b i} f x, ∂_{b i} f x⟫ ∂μ :=
    -- `innerSL ℝ u w` unfolds to `⟪u, w⟫`.
    integral_bilinear_laplacian_right_eq_neg_sum b f f (innerSL ℝ)
  simpa only [real_inner_self_eq_norm_sq] using h

open MeasureTheory LineDeriv Laplacian RealInnerProductSpace in
/-- The **energy identity** for the shifted Laplacian `-Δ + c` on Schwartz space: for an
orthonormal basis `b` and a scalar `c`, `∫ ⟪f, (-Δ + c) f⟫ = ∑ᵢ ∫ ‖∂_{bᵢ} f‖² + c ∫ ‖f‖²`. -/
theorem integral_inner_neg_laplacian_add_smul_self {E F ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fintype ι] (b : OrthonormalBasis ι ℝ E) (c : ℝ) (f : 𝓢(E, F)) :
    ∫ x, ⟪f x, (-Δ f + c • f) x⟫ ∂μ =
      ∑ i, ∫ x, ‖∂_{b i} f x‖ ^ 2 ∂μ + c * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have e : ∀ x, ⟪f x, (-Δ f + c • f) x⟫ = -⟪f x, Δ f x⟫ + c * ‖f x‖ ^ 2 := fun x => by
    simp [inner_add_right, inner_neg_right, inner_smul_right]
  simp_rw [e]
  -- `innerSL ℝ u w` unfolds to `⟪u, w⟫`, so these pairings are the integrands.
  have hΔ : Integrable (fun x => ⟪f x, Δ f x⟫) μ := (pairing (innerSL ℝ) f (Δ f)).integrable
  have hf : Integrable (fun x => ⟪f x, f x⟫) μ := (pairing (innerSL ℝ) f f).integrable
  simp only [real_inner_self_eq_norm_sq] at hf
  rw [integral_add (by exact hΔ.neg) (hf.const_mul c), integral_neg, integral_const_mul,
    integral_inner_laplacian_right_self_eq_neg_sum b f, neg_neg]

end SchwartzMap
