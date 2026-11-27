/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Data.Fin.Tuple.Basic

/-!
# Directional differentiation and linear maps on Schwartz space

Directional derivatives of a Schwartz function commute, since its second derivative is symmetric,
and they commute with translation (`SchwartzMap.lineDerivOp_compSubConstCLM`) and with
multiplication by a constant from any normed field acting on the values, provided this action
commutes with real scalar multiplication (`SchwartzMap.lineDerivOp_smul`).
Near a point where a Schwartz function is constant, its line derivatives vanish
(`SchwartzMap.lineDerivOp_eventuallyEq_zero`).
For a Schwartz function valued in a finite `L^p` product, such as Euclidean space, taking a
coordinate commutes with differentiation along any direction
(`SchwartzMap.fderiv_apply_eq_lineDerivOp_apply`).
On the plane `ℂ`, the Laplacian is the sum of the second derivatives along `1` and `I`.
On `𝓢(ℝ, F)`, the `m`-th power of `SchwartzMap.derivCLM` is the `m`-th iterated derivative
(`SchwartzMap.coe_derivCLM_pow`).

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
Fourier side, multiplying a symbol by `2πi ⟪h, ξ⟫` differentiates its kernel along `h`, so these
identities control the derivatives of the symbol of a differentiated kernel.

The real or complex inner pairing satisfies directional integration by parts
(`SchwartzMap.integral_inner_lineDerivOp_right_eq_neg_left`), with sign `(-1)^k` after
transferring `k` derivatives (`SchwartzMap.integral_inner_iterate_lineDerivOp_right_eq`).
Integrating by parts along an orthonormal basis gives Green's identity
`∫ B(f, Δg) = -∑ᵢ ∫ B(∂_{bᵢ} f, ∂_{bᵢ} g)` for a continuous bilinear map `B`
(`SchwartzMap.integral_bilinear_laplacian_right_eq_neg_sum`). For the inner product this reads
`∫ ⟪f, Δf⟫ = -∑ᵢ ‖∂_{bᵢ} f‖₂²` (`SchwartzMap.integral_inner_laplacian_right_self_eq_neg_sum`),
and for the shifted Laplacian `-Δ + c` it is the energy identity
`∫ ⟪f, (-Δ + c) f⟫ = ∑ᵢ ‖∂_{bᵢ} f‖₂² + c ‖f‖₂²`
(`SchwartzMap.integral_inner_neg_laplacian_add_smul_self`). Integrating by parts `k` times along
directions `m : Fin k → E` moves the derivatives to the other side in reverse order, with the sign
`(-1) ^ k`: `∫ L (∂^{m} f) g = (-1) ^ k ∫ L f (∂^{m ∘ rev} g)`
(`SchwartzMap.integral_bilinear_iteratedLineDerivOp_left_eq_neg_one_pow_smul_right`).
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
  -- `L` is differentiated as a real-linear map.
  have h := (L.restrictScalars ℝ).fderiv_comp_left (φ.differentiableAt (x := x))
  simpa only [lineDerivOp_apply_eq_fderiv, coe_postcompCLM, postcompCLM_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply] using congr($h v)

open Laplacian in
/-- The Laplacian commutes with a continuous linear map on the values of a Schwartz
function. -/
@[simp]
theorem laplacian_postcompCLM {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (φ : 𝓢(W, F)) (L : F →L[𝕜] G) :
    Δ (φ.postcompCLM L) = (Δ φ).postcompCLM L := by
  ext x
  -- `L` is applied as a real-linear map.
  have h := (φ.smooth 2).contDiffAt.laplacian_CLM_comp_left (l := L.restrictScalars ℝ) (x := x)
  simpa only [laplacian_apply, coe_postcompCLM, postcompCLM_apply,
    ContinuousLinearMap.coe_restrictScalars', Function.comp_apply] using h

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

/-- The `m`-th power of the one-dimensional derivative on Schwartz space is the `m`-th iterated
derivative. -/
@[simp]
theorem coe_derivCLM_pow (m : ℕ) (f : 𝓢(ℝ, F)) :
    ⇑((derivCLM 𝕜 F ^ m) f) = iteratedDeriv m f := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, iteratedDeriv_succ',
      show ⇑(derivCLM 𝕜 F f) = deriv f from funext (derivCLM_apply 𝕜 f)]

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

/-- Directional differentiation commutes with multiplication by a constant `c` from any normed
field `R` acting on the values, provided this action commutes with real scalar multiplication
(`SMulCommClass ℝ R F`). Mathlib's `LineDeriv.lineDerivOp_smul` covers only `RCLike` scalars on
Schwartz space. -/
@[simp]
protected theorem lineDerivOp_smul {R : Type*} [NormedField R] [NormedSpace R F]
    [SMulCommClass ℝ R F] (f : 𝓢(V, F)) (c : R) (v : V) : ∂_{v} (c • f) = c • ∂_{v} f := by
  ext x
  simp [lineDerivOp_apply_eq_fderiv, fderiv_const_smul f.differentiableAt]

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
  have hB : ⇑(bilinLeftCLM B hg f) = fun y ↦ B.bilinearRestrictScalars ℝ (f y) (g y) := by
    simp only [bilinLeftCLM_apply, ContinuousLinearMap.bilinearRestrictScalars_apply_apply]
  rw [lineDerivOp_apply_eq_fderiv, hB, (B.bilinearRestrictScalars ℝ).fderiv_of_bilinear
    f.differentiableAt (hg.1.differentiable (by simp) x)]
  simp [lineDerivOp_apply_eq_fderiv]

/-- **The Leibniz rule for multiplication by a function of temperate growth**:
`∂_v (g f) = (∂_v g) f + g ∂_v f`, where `∂_v g` is `x ↦ Dg(x) v`. -/
theorem lineDerivOp_smulLeftCLM (f : 𝓢(V, F)) {g : V → 𝕜} (hg : g.HasTemperateGrowth) (v : V) :
    ∂_{v} (smulLeftCLM F g f) =
      smulLeftCLM F (fun x ↦ fderiv ℝ g x v) f + smulLeftCLM F g (∂_{v} f) := by
  rw [TauCeti.smulLeftCLM_eq_bilinLeftCLM hg,
    TauCeti.smulLeftCLM_eq_bilinLeftCLM (hg.fderiv_apply v),
    lineDerivOp_bilinLeftCLM]

/-- **The Leibniz rule for multiplication by a linear function**:
`∂_v (L f) = L ∂_v f + L v f` for a continuous real-linear map `L : V →L[ℝ] 𝕜`. -/
theorem lineDerivOp_smulLeftCLM_clm (f : 𝓢(V, F)) (L : V →L[ℝ] 𝕜) (v : V) :
    ∂_{v} (smulLeftCLM F L f) = smulLeftCLM F L (∂_{v} f) + L v • f := by
  rw [lineDerivOp_smulLeftCLM f L.hasTemperateGrowth, add_comm]
  simp

/-- **The iterated Leibniz rule for multiplication by a linear function**:
`∂_v^(k+1) (L f) = L ∂_v^(k+1) f + (k + 1) L v ∂_v^k f` for a continuous real-linear map
`L : V →L[ℝ] 𝕜`. -/
theorem iterate_lineDerivOp_smulLeftCLM_clm (f : 𝓢(V, F)) (L : V →L[ℝ] 𝕜) (v : V) (k : ℕ) :
    (∂_{v})^[k + 1] (smulLeftCLM F L f) =
      smulLeftCLM F L ((∂_{v})^[k + 1] f) + ((k + 1) * L v) • (∂_{v})^[k] f := by
  induction k with
  | zero => simpa using lineDerivOp_smulLeftCLM_clm f L v
  | succ k ih =>
    calc (∂_{v})^[k + 1 + 1] (smulLeftCLM F L f)
        = ∂_{v} (smulLeftCLM F L ((∂_{v})^[k + 1] f) + ((k + 1) * L v) • (∂_{v})^[k] f) := by
          rw [Function.iterate_succ_apply' _ _ (smulLeftCLM F L f), ih]
      _ = smulLeftCLM F L ((∂_{v})^[k + 1 + 1] f) + ((↑(k + 1) + 1) * L v) • (∂_{v})^[k + 1] f := by
          rw [LineDeriv.lineDerivOp_add, SchwartzMap.lineDerivOp_smul, lineDerivOp_smulLeftCLM_clm]
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
    simpa only [Nat.cast_succ, map_add, map_natCast, map_one] using
      (norm_algebraMap' 𝕜 ((k + 1 : ℕ) : ℝ)).trans (Real.norm_natCast (k + 1))
  rw [norm_smul, norm_mul, hk, mul_assoc ((k : ℝ) + 1) ‖L‖ ‖v‖]
  gcongr
  exact L.le_opNorm v

open MeasureTheory LineDeriv in
/-- Directional integration by parts for the real or complex Hilbert pairing of Schwartz maps. -/
theorem integral_inner_lineDerivOp_right_eq_neg_left {𝕜 E H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [InnerProductSpace 𝕜 H] (f g : 𝓢(E, H)) (v : E) :
    (∫ x, inner 𝕜 (f x) (∂_{v} g x) ∂μ) =
      -∫ x, inner 𝕜 (∂_{v} f x) (g x) ∂μ := by
  let B : H →L[ℝ] H →L[ℝ] 𝕜 :=
    (ContinuousLinearMap.restrictScalarsL 𝕜 H 𝕜 ℝ ℝ).comp
      ((innerSL 𝕜).toAddMonoidHom.toRealLinearMap (innerSL 𝕜).continuous)
  -- Restricting scalars and the native additive realification both preserve evaluation.
  have hB (x y : H) : B x y = inner 𝕜 x y := by rfl
  simpa only [hB] using integral_bilinear_lineDerivOp_right_eq_neg_left f g B v

open MeasureTheory LineDeriv in
/-- Transferring every directional derivative across a Schwartz inner pairing contributes
one factor of minus one per derivative. -/
theorem integral_inner_iterate_lineDerivOp_right_eq {𝕜 E H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [InnerProductSpace 𝕜 H]
    (f g : 𝓢(E, H)) (v : E) (k : ℕ) :
    (∫ x, inner 𝕜 (f x) (((∂_{v})^[k] g) x) ∂μ) =
      (-1 : 𝕜) ^ k * ∫ x, inner 𝕜 (((∂_{v})^[k] f) x) (g x) ∂μ := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', integral_inner_lineDerivOp_right_eq_neg_left, ih,
      Function.iterate_succ_apply, pow_succ]
    ring

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

open MeasureTheory LineDeriv in
/-- **Iterated integration by parts on Schwartz space.** For a continuous bilinear map `L`,
`∫ L (∂^{m} f) g = (-1) ^ k ∫ L f (∂^{m ∘ rev} g)`: the `k` derivatives move to `g` in reverse
order, each with a minus sign. -/
theorem integral_bilinear_iteratedLineDerivOp_left_eq_neg_one_pow_smul_right {E F₁ F₂ F₃ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] [NormedAddCommGroup F₁]
    [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup F₃]
    [NormedSpace ℝ F₃] (L : F₁ →L[ℝ] F₂ →L[ℝ] F₃) {k : ℕ} (m : Fin k → E) (f : 𝓢(E, F₁))
    (g : 𝓢(E, F₂)) :
    ∫ x, L ((∂^{m} f) x) (g x) ∂μ = (-1 : ℝ) ^ k • ∫ x, L (f x) ((∂^{m ∘ Fin.rev} g) x) ∂μ := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    -- One integration by parts in the direction `m 0`.
    have hstep : ∫ x, L ((∂_{m 0} (∂^{Fin.tail m} f)) x) (g x) ∂μ =
        -∫ x, L ((∂^{Fin.tail m} f) x) ((∂_{m 0} g) x) ∂μ := by
      rw [integral_bilinear_lineDerivOp_right_eq_neg_left (∂^{Fin.tail m} f) g L (m 0), neg_neg]
    rw [iteratedLineDerivOp_succ_left m f, hstep, ih, iteratedLineDerivOp_succ_right (m ∘ Fin.rev),
      Fin.init_comp_rev, Function.comp_apply, Fin.rev_last, pow_succ, mul_neg_one, neg_smul]

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
