/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.FourierMultiplier
import TauCeti.MeasureTheory.Integral.CalderonZygmund.InnerProductSpace
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Hessian

/-!
# The Calderón–Zygmund estimate `‖D²u‖_p ≤ C ‖Δu‖_p`

For `n ≥ 3` and `1 < p < ∞`, this file proves the `Lᵖ` estimate of the second derivatives by the
Laplacian on `ℝⁿ`: there is a constant `C` with

`‖D²u‖_{Lᵖ} ≤ C ‖Δu‖_{Lᵖ}`

for every Schwartz function `u` with values in a complex Hilbert space
(`TauCeti.exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian`). This is the whole-space
estimate at the heart of the Calderón–Zygmund `W^{2,p}` theory of strong solutions. For `p = 2` it
follows from Plancherel's theorem; for `p ≠ 2` it is a genuine singular integral estimate, and it
is false at the endpoints `p = 1` and `p = ∞`. A corollary gives the same estimate for real
Schwartz functions (`TauCeti.exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_real`).

## The argument

On Schwartz functions `∂_v ∂_w = T_{m_{v,w}} ∘ Δ`, where `T_{m_{v,w}}` is the `L²` Fourier
multiplier with symbol `m_{v,w}(ξ) = ⟪ξ, v⟫ ⟪ξ, w⟫ / ‖ξ‖²`
(`SchwartzMap.toLp_lineDerivOp_lineDerivOp_eq_fourierMultiplierCLM`). So it suffices to bound
`T_{m_{v,w}}` in the `Lᵖ` norm, which is the Calderón–Zygmund theorem
(`ContinuousLinearMap.exists_eLpNorm_le_of_norm_sub_le_mul_rpow`) applied with the kernel
`k(x, y) = -D²Gₙ(x - y)(v, w)` built from the Newtonian kernel `Gₙ`. Its three hypotheses are:

* the kernel representation of `T_{m_{v,w}}` off the support of its argument
  (`TauCeti.ae_fourierMultiplierCLM_hessianSymbolLp_eq_neg_integral`, which needs `n ≥ 3`);
* the size estimate `‖D²Gₙ(z)‖ ≲ ‖z‖⁻ⁿ` (`TauCeti.norm_iteratedFDeriv_two_newtonianKernel_le`);
* the smoothness estimate `‖D²Gₙ(a) - D²Gₙ(b)‖ ≲ ‖a - b‖ ‖b‖⁻ⁿ⁻¹` for `2 ‖a - b‖ ≤ ‖b‖`
  (`TauCeti.norm_iteratedFDeriv_two_newtonianKernel_sub_le`), giving exponent `δ = 1`.

The theorem also asks for the same of the adjoint. The symbol is real, so `T_{m_{v,w}}` is
self-adjoint (`MeasureTheory.Lp.adjoint_fourierMultiplierCLM`), also for the real inner product
of `L²` that the Calderón–Zygmund theorem uses, and the adjoint has the same kernel.

The full Hessian is controlled through an orthonormal basis `(eᵢ)`: the norm of a bilinear map
`M` is at most `∑ᵢⱼ ‖M(eᵢ, eⱼ)‖`
(`ContinuousMultilinearMap.opNorm_le_sum_norm_apply_orthonormalBasis`), so
`‖D²u‖_p ≤ ∑ᵢⱼ ‖∂_{eᵢ} ∂_{eⱼ} u‖_p`.

## Main declarations

* `TauCeti.exists_eLpNorm_fourierMultiplierCLM_hessianSymbolLp_le`: the multiplier `T_{m_{v,w}}`,
  that is `∂_v ∂_w Δ⁻¹`, is bounded in the `Lᵖ` norm for `1 < p < ∞`.
* `TauCeti.exists_eLpNorm_lineDerivOp_lineDerivOp_le_eLpNorm_laplacian`:
  `‖∂_v ∂_w u‖_p ≤ C ‖Δu‖_p` for Schwartz functions `u`.
* `TauCeti.exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian`: `‖D²u‖_p ≤ C ‖Δu‖_p` for
  Schwartz functions `u`, and `TauCeti.exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_real`
  for real ones.

## References

* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter III,
  §1.3.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.9.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap MeasureTheory Metric
open scoped ENNReal NNReal Laplacian LineDeriv SchwartzMap

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The kernel `k(x, y) = -D²Gₙ(x - y)(v, w)` of the Hessian multiplier, as a scalar multiple of
the identity of `F`. -/
private def hessianKernel (v w : EuclideanSpace ℝ (Fin n)) (x y : EuclideanSpace ℝ (Fin n)) :
    F →L[ℝ] F :=
  (-iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) ![v, w]) • ContinuousLinearMap.id ℝ F

private theorem stronglyMeasurable_hessianKernel (v w : EuclideanSpace ℝ (Fin n)) :
    StronglyMeasurable (Function.uncurry (hessianKernel (F := F) v w)) := by
  have hm : Measurable fun z : EuclideanSpace ℝ (Fin n) =>
      iteratedFDeriv ℝ 2 (newtonianKernel n) z ![v, w] := by
    simp only [iteratedFDeriv_two_apply]
    exact ((measurable_fderiv ℝ (fderiv ℝ (newtonianKernel n))).apply_continuousLinearMap
      (![v, w] 0)).apply_continuousLinearMap (![v, w] 1)
  exact ((hm.comp (measurable_fst.sub measurable_snd)).neg.stronglyMeasurable).smul_const _

/-- **The size estimate for the kernel of the Hessian multiplier**:
`‖k(x, y)‖ ≤ C ‖x - y‖⁻ⁿ` for `x ≠ y`. -/
private theorem norm_hessianKernel_le (v w : EuclideanSpace ℝ (Fin n))
    {x y : EuclideanSpace ℝ (Fin n)} (hxy : x ≠ y) :
    ‖hessianKernel (F := F) v w x y‖ ≤
      ((n : ℝ) + 1) * ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        (‖v‖ * ‖w‖) * dist x y ^ (-(n : ℝ)) := by
  rw [hessianKernel, norm_smul, Real.norm_eq_abs, abs_neg, dist_eq_norm]
  have hM : |iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) ![v, w]| ≤
      ‖iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y)‖ * (‖v‖ * ‖w‖) := by
    simpa [Fin.prod_univ_two] using
      (iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y)).le_opNorm ![v, w]
  refine ((mul_le_of_le_one_right (abs_nonneg _) norm_id_le).trans hM).trans ?_
  exact (mul_le_mul_of_nonneg_right (norm_iteratedFDeriv_two_newtonianKernel_le
    (sub_ne_zero.2 hxy)) (by positivity)).trans_eq (by ring)

/-- **The smoothness estimate for the kernel of the Hessian multiplier**:
`‖k(x, y) - k(x, y')‖ ≤ C ‖y - y'‖ ‖x - y'‖⁻ⁿ⁻¹` when `2 ‖y - y'‖ < ‖x - y'‖`. -/
private theorem norm_hessianKernel_sub_le (v w : EuclideanSpace ℝ (Fin n))
    {x y y' : EuclideanSpace ℝ (Fin n)} (h : 2 * dist y y' < dist x y') :
    ‖hessianKernel (F := F) v w x y - hessianKernel v w x y'‖ ≤
      2 ^ (n + 1) * ((n : ℝ) + 5) * (volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        (‖v‖ * ‖w‖) * (dist y y' * dist x y' ^ (-((n : ℝ) + 1))) := by
  have hsub : (x - y) - (x - y') = y' - y := by abel
  have hD := norm_iteratedFDeriv_two_newtonianKernel_sub_le (a := x - y) (b := x - y') (by
    rw [hsub, norm_sub_rev y' y, ← dist_eq_norm y y', ← dist_eq_norm x y']
    exact h.le)
  rw [hsub, norm_sub_rev y' y, ← dist_eq_norm y y', ← dist_eq_norm x y'] at hD
  have hM := (iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) -
    iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y')).le_opNorm ![v, w]
  simp only [sub_apply, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Real.norm_eq_abs] at hM
  rw [hessianKernel, hessianKernel, ← sub_smul, norm_smul, Real.norm_eq_abs, neg_sub_neg,
    abs_sub_comm]
  refine (mul_le_of_le_one_right (abs_nonneg _) norm_id_le).trans (hM.trans ?_)
  exact (mul_le_mul_of_nonneg_right hD (by positivity)).trans_eq (by ring)

/-- Off the support of its argument, the Hessian multiplier, viewed as a real-linear operator, is
given by the kernel `hessianKernel`. -/
private theorem ae_fourierMultiplierCLM_hessianSymbolLp_eq_integral_hessianKernel [CompleteSpace F]
    (hn : 3 ≤ n) (v w : EuclideanSpace ℝ (Fin n))
    (f : Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : IsCompact s) (hf : ∀ᵐ x, x ∉ s → f x = 0) :
    ∀ᵐ x, x ∉ s → (Lp.fourierMultiplierCLM F (hessianSymbolLp v w)).restrictScalars ℝ f x =
      ∫ z, hessianKernel v w x z (f z) := by
  filter_upwards [ae_fourierMultiplierCLM_hessianSymbolLp_eq_neg_integral hn v w f hs hf]
    with x hx hxs
  simp only [coe_restrictScalars', hx hxs, hessianKernel, neg_smul, neg_apply, smul_apply,
    id_apply, integral_neg]

variable [CompleteSpace F]

/-- **The Calderón–Zygmund estimate for the Hessian multiplier.** Let `n ≥ 3`, `v, w ∈ ℝⁿ` and
`1 < p < ∞`. The Fourier multiplier `T_{m_{v,w}}` on `L²(ℝⁿ, F)` with symbol
`⟪ξ, v⟫ ⟪ξ, w⟫ / ‖ξ‖²`, that is the operator `∂_v ∂_w Δ⁻¹`, is bounded in the `Lᵖ` norm: there is
a constant `C` with `‖T_{m_{v,w}} f‖_p ≤ C ‖f‖_p` for every `f ∈ L²`.

It is the singular integral operator with kernel `-D²Gₙ(x - y)(v, w)`, which satisfies the
standard Calderón–Zygmund size and smoothness estimates. -/
theorem exists_eLpNorm_fourierMultiplierCLM_hessianSymbolLp_le (hn : 3 ≤ n)
    (v w : EuclideanSpace ℝ (Fin n)) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ f : Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n))),
      eLpNorm (Lp.fourierMultiplierCLM F (hessianSymbolLp v w) f) p volume ≤
        C * eLpNorm f p volume := by
  -- The Calderón–Zygmund theorem is stated for real Hilbert spaces.
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    infer_instance
  set T := (Lp.fourierMultiplierCLM F (hessianSymbolLp v w)).restrictScalars ℝ
  -- The symbol is real, so `T` is self-adjoint, also for the real inner product of `L²`.
  have hT : adjoint T = T := by
    have hT : adjoint (Lp.fourierMultiplierCLM F (hessianSymbolLp v w)) =
        Lp.fourierMultiplierCLM F (hessianSymbolLp v w) := by
      rw [Lp.adjoint_fourierMultiplierCLM]
      congr 1
      refine Lp.ext ?_
      filter_upwards [Lp.coeFn_star (hessianSymbolLp v w), coeFn_hessianSymbolLp v w]
        with ξ h₁ h₂
      rw [h₁, Pi.star_apply, h₂, hessianSymbol_apply, Complex.star_def, Complex.conj_ofReal]
    have hre : ∀ f g : Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n))),
        inner ℝ f g = Complex.re (inner ℂ f g) := fun f g => by
      rw [L2.inner_def, L2.inner_def]
      exact integral_re (L2.integrable_inner (𝕜 := ℂ) f g)
    exact ((eq_adjoint_iff _ _).2 fun f g => by
      rw [hre, hre, coe_restrictScalars', ← adjoint_inner_right, hT]).symm
  -- The kernel satisfies the size and smoothness estimates with exponent `δ = 1`.
  have hfin : (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) = n := by
    rw [finrank_euclideanSpace_fin]
  have hvol := volume_real_unitBall_pos n
  set C₀ : ℝ≥0 := (((n : ℝ) + 1) * ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹
    * (‖v‖ * ‖w‖)).toNNReal
  set C : ℝ≥0 := (2 ^ (n + 1) * ((n : ℝ) + 5) *
    (volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ * (‖v‖ * ‖w‖)).toNNReal
  have hsize : ∀ x y : EuclideanSpace ℝ (Fin n), x ≠ y → ‖hessianKernel (F := F) v w x y‖ ≤
      C₀ * dist x y ^ (-(Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ)) := fun x y hxy => by
    rw [hfin, Real.coe_toNNReal _ (by positivity)]
    exact norm_hessianKernel_le v w hxy
  have hk : ∀ x y y' : EuclideanSpace ℝ (Fin n), 2 * dist y y' < dist x y' →
      ‖hessianKernel (F := F) v w x y - hessianKernel v w x y'‖ ≤
        C * (dist y y' ^ (1 : ℝ) *
          dist x y' ^ (-(Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) + 1 : ℝ))) :=
      fun x y y' h => by
    rw [hfin, Real.coe_toNNReal _ (by positivity), Real.rpow_one]
    exact norm_hessianKernel_sub_le v w h
  have hrep := fun f s (hs : IsCompact s) hf =>
    ae_fourierMultiplierCLM_hessianSymbolLp_eq_integral_hessianKernel (F := F) hn v w f hs hf
  exact T.exists_eLpNorm_le_of_norm_sub_le_mul_rpow (stronglyMeasurable_hessianKernel v w)
    (stronglyMeasurable_hessianKernel v w) one_pos one_pos hsize hsize hk hk hrep
    (by rw [hT]; exact hrep) hp hp_top

/-- **The Calderón–Zygmund estimate for a second directional derivative.** Let `n ≥ 3`,
`v, w ∈ ℝⁿ` and `1 < p < ∞`. There is a constant `C` with

`‖∂_v ∂_w u‖_{Lᵖ} ≤ C ‖Δu‖_{Lᵖ}`

for every Schwartz function `u` on `ℝⁿ` with values in a complex Hilbert space. -/
theorem exists_eLpNorm_lineDerivOp_lineDerivOp_le_eLpNorm_laplacian (hn : 3 ≤ n)
    (v w : EuclideanSpace ℝ (Fin n)) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), F),
      eLpNorm (⇑(∂_{v} (∂_{w} u) : 𝓢(EuclideanSpace ℝ (Fin n), F))) p volume ≤
        C * eLpNorm (⇑(Δ u : 𝓢(EuclideanSpace ℝ (Fin n), F))) p volume := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_fourierMultiplierCLM_hessianSymbolLp_le (F := F) hn v w hp hp_top
  refine ⟨C, fun u => ?_⟩
  have h := hC ((Δ u).toLp 2)
  rwa [← SchwartzMap.toLp_lineDerivOp_lineDerivOp_eq_fourierMultiplierCLM,
    eLpNorm_congr_ae (SchwartzMap.coeFn_toLp _ 2 volume),
    eLpNorm_congr_ae (SchwartzMap.coeFn_toLp _ 2 volume)] at h

/-- **The Calderón–Zygmund estimate `‖D²u‖_p ≤ C ‖Δu‖_p`.** Let `n ≥ 3` and `1 < p < ∞`. There is
a constant `C` with

`‖D²u‖_{Lᵖ} ≤ C ‖Δu‖_{Lᵖ}`

for every Schwartz function `u` on `ℝⁿ` with values in a complex Hilbert space, where `D²u` is the
second Fréchet derivative of `u`. -/
theorem exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian (hn : 3 ≤ n) {p : ℝ≥0∞}
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), F), eLpNorm (iteratedFDeriv ℝ 2 ⇑u) p volume ≤
      C * eLpNorm (⇑(Δ u : 𝓢(EuclideanSpace ℝ (Fin n), F))) p volume := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  choose C hC using fun r : Fin 2 → Fin n =>
    exists_eLpNorm_lineDerivOp_lineDerivOp_le_eLpNorm_laplacian (F := F) hn (b (r 0)) (b (r 1))
      hp hp_top
  refine ⟨∑ r, C r, fun u => ?_⟩
  set D : (Fin 2 → Fin n) → 𝓢(EuclideanSpace ℝ (Fin n), F) := fun r => ∂_{b (r 0)} (∂_{b (r 1)} u)
  -- The Hessian is bounded pointwise by the sum of its values on pairs of basis vectors.
  have hpt : ∀ x, ‖iteratedFDeriv ℝ 2 u x‖ ≤ ∑ r, ‖D r x‖ := fun x => by
    refine ((iteratedFDeriv ℝ 2 u x).opNorm_le_sum_norm_apply_orthonormalBasis b).trans_eq
      (Finset.sum_congr rfl fun r _ => ?_)
    rw [← SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
      LineDeriv.iteratedLineDerivOp_succ_left,
      LineDeriv.iteratedLineDerivOp_one]
    simp only [D, Fin.tail_def, Fin.succ_zero_eq_one]
  calc eLpNorm (iteratedFDeriv ℝ 2 ⇑u) p volume
      ≤ eLpNorm (∑ r, fun x => ‖D r x‖) p volume := by
        refine eLpNorm_mono_real
          ((u.smooth ⊤).continuous_iteratedFDeriv (by simp)).aestronglyMeasurable fun x => ?_
        rw [Finset.sum_apply]
        exact hpt x
    _ ≤ ∑ r, eLpNorm (fun x => ‖D r x‖) p volume := eLpNorm_sum_le hp.le
    _ ≤ ∑ r, C r * eLpNorm (⇑(Δ u : 𝓢(EuclideanSpace ℝ (Fin n), F))) p volume :=
        Finset.sum_le_sum fun r _ =>
          (eLpNorm_norm _ (D r).continuous.aestronglyMeasurable).trans_le (hC r u)
    _ = (∑ r, C r : ℝ≥0) * eLpNorm (⇑(Δ u : 𝓢(EuclideanSpace ℝ (Fin n), F))) p volume := by
        rw [ENNReal.ofNNReal_finsetSum, Finset.sum_mul]

/-- **The Calderón–Zygmund estimate `‖D²u‖_p ≤ C ‖Δu‖_p` for real functions.** Let `n ≥ 3` and
`1 < p < ∞`. There is a constant `C` with `‖D²u‖_{Lᵖ} ≤ C ‖Δu‖_{Lᵖ}` for every real Schwartz
function `u` on `ℝⁿ`. -/
theorem exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_real (hn : 3 ≤ n) {p : ℝ≥0∞}
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), ℝ), eLpNorm (iteratedFDeriv ℝ 2 ⇑u) p volume ≤
      C * eLpNorm (⇑(Δ u : 𝓢(EuclideanSpace ℝ (Fin n), ℝ))) p volume := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian (F := ℂ) hn hp hp_top
  refine ⟨C, fun u => ?_⟩
  -- Embed `u` in the complex Schwartz space; both sides keep their norms pointwise.
  set ψ := u.postcompCLM Complex.ofRealCLM
  have hψ : ⇑ψ = Complex.ofRealCLM ∘ ⇑u := funext (SchwartzMap.postcompCLM_apply _ u)
  have hu : ContDiff ℝ 2 ⇑u := (u.smooth ⊤).of_le (by simp)
  have h₁ : eLpNorm (iteratedFDeriv ℝ 2 ⇑ψ) p volume =
      eLpNorm (iteratedFDeriv ℝ 2 ⇑u) p volume := by
    refine eLpNorm_congr_norm_ae
      ((ψ.smooth ⊤).continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
      ((u.smooth ⊤).continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    have hψ' : ⇑ψ = Complex.ofRealLI ∘ ⇑u := funext fun y => by
      rw [hψ, Function.comp_apply, Function.comp_apply, Complex.ofRealCLM_apply,
        Complex.ofRealLI_apply]
    rw [hψ']
    exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left hu.contDiffAt le_rfl
  have h₂ : eLpNorm (⇑(Δ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))) p volume =
      eLpNorm (⇑(Δ u : 𝓢(EuclideanSpace ℝ (Fin n), ℝ))) p volume := by
    refine eLpNorm_congr_norm_ae
      (Δ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)).continuous.aestronglyMeasurable
      (Δ u : 𝓢(EuclideanSpace ℝ (Fin n), ℝ)).continuous.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [SchwartzMap.laplacian_apply, SchwartzMap.laplacian_apply, hψ,
      hu.contDiffAt.laplacian_CLM_comp_left]
    simp
  rw [← h₁, ← h₂]
  exact hC ψ

end TauCeti
