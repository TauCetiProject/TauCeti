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
import TauCeti.Analysis.Distribution.SchwartzSpace.Prod
import TauCeti.MeasureTheory.Function.Lp.Dilation
import TauCeti.MeasureTheory.Function.Lp.Iterated
import TauCeti.MeasureTheory.Measure.Haar.EuclideanSpace

/-!
# The Calderón–Zygmund estimate `‖D²u‖_p ≤ C ‖Δu‖_p`

For every dimension `n` and `1 < p < ∞`, this file proves the `Lᵖ` estimate of the second
derivatives by the Laplacian on `ℝⁿ`: there is a constant `C` with

`‖D²u‖_{Lᵖ} ≤ C ‖Δu‖_{Lᵖ}`

for every Schwartz function `u` with values in a complex Hilbert space
(`TauCeti.exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian`). This is the whole-space
estimate at the heart of the Calderón–Zygmund `W^{2,p}` theory of strong solutions. For `p = 2` it
follows from Plancherel's theorem. For `n ≥ 2` and `p ≠ 2` it is a genuine singular integral
estimate, and it is false at the endpoints `p = 1` and `p = ∞`. In dimension one it is
elementary: `D²u` and `Δu` have the same pointwise norm `‖u''‖`, so it holds for every `p`. A
corollary gives the same estimate for real Schwartz functions
(`TauCeti.exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_real`).

## The argument for `n ≥ 3`

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

## Descent to low dimensions

The estimate in `ℝⁿ⁺¹` implies the estimate in `ℝⁿ` with the same constant, by the method of
descent. Write `ℝⁿ⁺¹ = ℝ × ℝⁿ` (`EuclideanSpace.consEquivL`) and test the estimate in `ℝⁿ⁺¹`
against the tensor product `U(t, x) = ψ(t / R) u(x)` (`SchwartzMap.prodSMul`) of a fixed nonzero
profile `ψ` with `u`. For `v, w ∈ ℝⁿ`, `∂_{(0, v)} ∂_{(0, w)} U = ψ(· / R) ⊗ ∂_v ∂_w u` and
`ΔU = ψ(· / R) ⊗ Δu + R⁻² ψ''(· / R) ⊗ u`. The `Lᵖ` norm of a tensor product is the product of the
norms (`TauCeti.eLpNorm_prod_smul`), and the dilation `ψ(· / R)` multiplies `‖ψ‖_p` and `‖ψ''‖_p`
by the same factor (`TauCeti.eLpNorm_comp_inv_smul`). Dividing by it and letting `R → ∞` leaves the
estimate in `ℝⁿ`. This gives the planar case `n = 2`, where the Newtonian kernel is logarithmic
and the kernel representation above is not available, and the case `n = 1`.

The full Hessian is controlled through an orthonormal basis `(eᵢ)`: the norm of a bilinear map
`M` is at most `∑ᵢⱼ ‖M(eᵢ, eⱼ)‖`
(`ContinuousMultilinearMap.opNorm_le_sum_norm_apply_orthonormalBasis`), so
`‖D²u‖_p ≤ ∑ᵢⱼ ‖∂_{eᵢ} ∂_{eⱼ} u‖_p`.

## Main declarations

* `TauCeti.exists_eLpNorm_fourierMultiplierCLM_hessianSymbolLp_le`: for `n ≥ 3`, the multiplier
  `T_{m_{v,w}}`, that is `∂_v ∂_w Δ⁻¹`, is bounded in the `Lᵖ` norm for `1 < p < ∞`.
* `TauCeti.exists_eLpNorm_lineDerivOp_lineDerivOp_le_eLpNorm_laplacian`:
  `‖∂_v ∂_w u‖_p ≤ C ‖Δu‖_p` for Schwartz functions `u`, in every dimension.
* `TauCeti.exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian`: `‖D²u‖_p ≤ C ‖Δu‖_p` for
  Schwartz functions `u`, and `TauCeti.exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_real`
  for real ones, in every dimension.

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

section Descent

/-! ### Descent from `ℝⁿ⁺¹` to `ℝⁿ` -/

open EuclideanSpace Filter SchwartzMap Topology

/-- Transport of Schwartz functions from `ℝ × ℝⁿ` to `ℝⁿ⁺¹` along `EuclideanSpace.consEquivL`. -/
private noncomputable def consTransport (n : ℕ) :
    𝓢(ℝ × EuclideanSpace ℝ (Fin n), F) →L[ℝ] 𝓢(EuclideanSpace ℝ (Fin (n + 1)), F) :=
  compCLMOfContinuousLinearEquiv ℝ (consEquivL ℝ n).symm

private theorem eLpNorm_consTransport (U : 𝓢(ℝ × EuclideanSpace ℝ (Fin n), F)) (p : ℝ≥0∞) :
    eLpNorm (⇑(consTransport n U)) p volume = eLpNorm (⇑U) p (volume.prod volume) := by
  have h : ⇑(consTransport n U) ∘ consEquivL ℝ n = ⇑U := funext fun z => by simp [consTransport]
  rw [← eLpNorm_comp_measurePreserving (consTransport n U).continuous.aestronglyMeasurable
    (measurePreserving_consEquivL n), h, Measure.volume_eq_prod]

private theorem lineDerivOp_consTransport (U : 𝓢(ℝ × EuclideanSpace ℝ (Fin n), F)) (s : ℝ)
    (a : EuclideanSpace ℝ (Fin n)) :
    ∂_{consEquivL ℝ n (s, a)} (consTransport n U) = consTransport n (∂_{(s, a)} U) := by
  simp [consTransport, lineDerivOp_compCLMOfContinuousLinearEquiv]

/-- The Laplacian of `ψ ⊗ u` on `ℝⁿ⁺¹` is `ψ'' ⊗ u + ψ ⊗ Δu`. -/
private theorem laplacian_consTransport_prodSMul (ψ : 𝓢(ℝ, ℝ))
    (u : 𝓢(EuclideanSpace ℝ (Fin n), F)) :
    Δ (consTransport n (prodSMul ψ u)) = consTransport n (prodSMul (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} ψ)) u)
      + consTransport n (prodSMul ψ (Δ u)) := by
  -- The standard basis of `ℝⁿ⁺¹` is `(1, 0)` followed by the standard basis of `ℝⁿ`.
  set e := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  set e' := EuclideanSpace.basisFun (Fin n) ℝ
  have he0 : e 0 = consEquivL ℝ n (1, 0) := by
    ext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [e]
  have hes (i : Fin n) : e i.succ = consEquivL ℝ n (0, e' i) := by
    ext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [e, e', PiLp.single_apply]
  rw [laplacian_eq_sum e, Fin.sum_univ_succ, he0, laplacian_eq_sum e' u]
  simp only [hes, lineDerivOp_consTransport, lineDerivOp_prodSMul, LineDeriv.lineDerivOp_left_zero,
    prodSMul_zero, zero_prodSMul, add_zero, zero_add]
  congr 1
  let L : 𝓢(EuclideanSpace ℝ (Fin n), F) →+ 𝓢(EuclideanSpace ℝ (Fin (n + 1)), F) :=
    (consTransport (F := F) n : _ →+ _).comp (AddMonoidHom.mk' (prodSMul ψ) (prodSMul_add ψ))
  exact (map_sum L _ _).symm

/-- The estimate in `ℝⁿ⁺¹` for `∂_{(0, v)} ∂_{(0, w)}`, tested against `ψ ⊗ u`, gives
`‖ψ‖_p ‖∂_v ∂_w u‖_p ≤ C (‖ψ‖_p ‖Δu‖_p + ‖ψ''‖_p ‖u‖_p)`. -/
private theorem eLpNorm_mul_eLpNorm_lineDerivOp_lineDerivOp_le (v w : EuclideanSpace ℝ (Fin n))
    {p : ℝ≥0∞} (hp : 1 ≤ p) {C : ℝ≥0}
    (hC : ∀ U : 𝓢(EuclideanSpace ℝ (Fin (n + 1)), F),
      eLpNorm (⇑(∂_{consEquivL ℝ n (0, v)} (∂_{consEquivL ℝ n (0, w)} U) :
        𝓢(EuclideanSpace ℝ (Fin (n + 1)), F))) p volume ≤
        C * eLpNorm (⇑(Δ U : 𝓢(EuclideanSpace ℝ (Fin (n + 1)), F))) p volume)
    (ψ : 𝓢(ℝ, ℝ)) (u : 𝓢(EuclideanSpace ℝ (Fin n), F)) :
    eLpNorm (⇑ψ) p volume *
        eLpNorm (⇑(∂_{v} (∂_{w} u) : 𝓢(EuclideanSpace ℝ (Fin n), F))) p volume ≤
      C * (eLpNorm (⇑ψ) p volume * eLpNorm (⇑(Δ u : 𝓢(EuclideanSpace ℝ (Fin n), F))) p volume +
        eLpNorm (⇑(∂_{(1 : ℝ)} (∂_{(1 : ℝ)} ψ) : 𝓢(ℝ, ℝ))) p volume * eLpNorm (⇑u) p volume) := by
  have hm (f : 𝓢(ℝ, ℝ)) : AEStronglyMeasurable (⇑f) volume := f.continuous.aestronglyMeasurable
  have hm' (f : 𝓢(EuclideanSpace ℝ (Fin n), F)) : AEStronglyMeasurable (⇑f) volume :=
    f.continuous.aestronglyMeasurable
  have h := hC (consTransport n (prodSMul ψ u))
  simp only [lineDerivOp_consTransport, lineDerivOp_prodSMul, LineDeriv.lineDerivOp_left_zero,
    zero_prodSMul, zero_add, eLpNorm_consTransport, coe_prodSMul, eLpNorm_prod_smul (hm _) (hm' _),
    laplacian_consTransport_prodSMul, FunLike.coe_add] at h
  refine h.trans (mul_le_mul_right ((eLpNorm_add_le hp).trans_eq ?_) _)
  simp only [eLpNorm_consTransport, coe_prodSMul, eLpNorm_prod_smul (hm _) (hm' _), add_comm]

/-- **Descent in the dimension.** If `‖∂_{(0, v)} ∂_{(0, w)} U‖_p ≤ C ‖ΔU‖_p` for all Schwartz
functions `U` on `ℝ × ℝⁿ = ℝⁿ⁺¹`, then `‖∂_v ∂_w u‖_p ≤ C ‖Δu‖_p` for all Schwartz functions `u` on
`ℝⁿ`, with the same constant. -/
private theorem eLpNorm_lineDerivOp_lineDerivOp_le_of_succ (v w : EuclideanSpace ℝ (Fin n))
    {p : ℝ≥0∞} (hp : 1 ≤ p) {C : ℝ≥0}
    (hC : ∀ U : 𝓢(EuclideanSpace ℝ (Fin (n + 1)), F),
      eLpNorm (⇑(∂_{consEquivL ℝ n (0, v)} (∂_{consEquivL ℝ n (0, w)} U) :
        𝓢(EuclideanSpace ℝ (Fin (n + 1)), F))) p volume ≤
        C * eLpNorm (⇑(Δ U : 𝓢(EuclideanSpace ℝ (Fin (n + 1)), F))) p volume)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), F)) :
    eLpNorm (⇑(∂_{v} (∂_{w} u) : 𝓢(EuclideanSpace ℝ (Fin n), F))) p volume ≤
      C * eLpNorm (⇑(Δ u : 𝓢(EuclideanSpace ℝ (Fin n), F))) p volume := by
  -- Test against `ψ(· / R) ⊗ u` for a fixed nonzero profile `ψ`. With `S = R ^ (1 / p)`,
  -- `‖ψ(· / R)‖_p = S ‖ψ‖_p` and `‖(ψ(· / R))''‖_p = R⁻² S ‖ψ''‖_p`, so dividing by `S` and
  -- letting `R → ∞` kills the `ψ''` term.
  let φ : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  set ψ : 𝓢(ℝ, ℝ) := φ.hasCompactSupport.toSchwartzMap φ.contDiff
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hψ0 : eLpNorm (⇑ψ) p volume ≠ 0 := by
    intro h
    rw [eLpNorm_eq_zero_iff hp0] at h
    have h0 := congrFun ((ψ.continuous.ae_eq_iff_eq volume continuous_zero).1 h) 0
    simp [ψ, φ.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)] at h0
  have hψtop : eLpNorm (⇑ψ) p volume ≠ ∞ := (ψ.eLpNorm_lt_top p).ne
  set A := eLpNorm (⇑ψ) p volume with hA
  set B := eLpNorm (⇑(∂_{(1 : ℝ)} (∂_{(1 : ℝ)} ψ) : 𝓢(ℝ, ℝ))) p volume with hB
  set a := eLpNorm (⇑(∂_{v} (∂_{w} u) : 𝓢(EuclideanSpace ℝ (Fin n), F))) p volume with ha
  set b := eLpNorm (⇑(Δ u : 𝓢(EuclideanSpace ℝ (Fin n), F))) p volume with hb
  set c := eLpNorm (⇑u) p volume with hc
  have hBc : B * c ≠ ∞ :=
    ENNReal.mul_ne_top ((∂_{(1 : ℝ)} (∂_{(1 : ℝ)} ψ)).eLpNorm_lt_top p).ne (u.eLpNorm_lt_top p).ne
  have hR (R : ℝ) (hR : 0 < R) : A * a ≤ C * (A * b) + C * (‖R⁻¹ * R⁻¹‖ₑ * (B * c)) := by
    set δ : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 R⁻¹ (by positivity))
    set D : 𝓢(ℝ, ℝ) →L[ℝ] 𝓢(ℝ, ℝ) := compCLMOfContinuousLinearEquiv ℝ δ
    -- `D = ψ ↦ ψ (R⁻¹ •)` scales the `Lᵖ` norm by `S = R ^ (1 / p)` and the derivative by `R⁻¹`.
    set S := ENNReal.ofReal (R ^ ((Module.finrank ℝ ℝ : ℝ) / p.toReal))
    have hD_norm (f : 𝓢(ℝ, ℝ)) : eLpNorm (⇑(D f)) p volume = S * eLpNorm (⇑f) p volume := by
      have h : ⇑(D f) = fun t => f (R⁻¹ • t) := funext fun t => by simp [D, δ, mul_comm]
      rw [h, eLpNorm_comp_inv_smul volume f hR p]
    have hD_deriv (f : 𝓢(ℝ, ℝ)) : ∂_{(1 : ℝ)} (D f) = R⁻¹ • D (∂_{(1 : ℝ)} f) := by
      have h : δ 1 = R⁻¹ • (1 : ℝ) := by simp [δ]
      rw [lineDerivOp_compCLMOfContinuousLinearEquiv, ← map_smul, h,
        LineDeriv.lineDerivOp_left_smul]
    have hD_deriv2 : ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (D ψ)) =
        (R⁻¹ * R⁻¹) • D (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} ψ)) := by
      rw [hD_deriv, LineDeriv.lineDerivOp_smul, hD_deriv, smul_smul]
    have hD_norm2 : eLpNorm (⇑(∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (D ψ)) : 𝓢(ℝ, ℝ))) p volume =
        ‖R⁻¹ * R⁻¹‖ₑ * (S * B) := by
      rw [hD_deriv2, FunLike.coe_smul, eLpNorm_const_smul, hD_norm]
    have h : S * A * a ≤ C * (S * A * b + ‖R⁻¹ * R⁻¹‖ₑ * (S * B) * c) := by
      simpa only [hD_norm, hD_norm2] using
        eLpNorm_mul_eLpNorm_lineDerivOp_lineDerivOp_le v w hp hC (D ψ) u
    refine (ENNReal.mul_le_mul_iff_right (by positivity : S ≠ 0) ENNReal.ofReal_ne_top).1 ?_
    calc S * (A * a) = S * A * a := by ring
      _ ≤ _ := h
      _ = S * (C * (A * b) + C * (‖R⁻¹ * R⁻¹‖ₑ * (B * c))) := by ring
  -- Let `R → ∞`, then divide by `‖ψ‖_p`.
  have hlim : Tendsto (fun R : ℝ => C * (A * b) + C * (‖R⁻¹ * R⁻¹‖ₑ * (B * c))) atTop
      (𝓝 (C * (A * b))) := by
    have h0 : Tendsto (fun R : ℝ => ‖R⁻¹ * R⁻¹‖ₑ) atTop (𝓝 0) := by
      simpa using ((tendsto_inv_atTop_zero (𝕜 := ℝ)).mul tendsto_inv_atTop_zero).enorm
    simpa using (ENNReal.Tendsto.const_mul (ENNReal.Tendsto.mul_const h0 (Or.inr hBc))
      (Or.inr ENNReal.coe_ne_top)).const_add (C * (A * b))
  have hAa : A * a ≤ A * (C * b) := by
    rw [mul_left_comm]
    exact ge_of_tendsto hlim ((eventually_gt_atTop 0).mono hR)
  exact (ENNReal.mul_le_mul_iff_right hψ0 hψtop).1 hAa

end Descent

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
      rw [Lp.adjoint_fourierMultiplierCLM, star_hessianSymbolLp]
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

/-- The estimate for a second directional derivative in dimension `n ≥ 3`, from the bound on the
Hessian multiplier. -/
private theorem exists_eLpNorm_lineDerivOp_lineDerivOp_le_of_three_le (hn : 3 ≤ n)
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

/-- **The Calderón–Zygmund estimate for a second directional derivative.** Let `v, w ∈ ℝⁿ` and
`1 < p < ∞`. There is a constant `C` with

`‖∂_v ∂_w u‖_{Lᵖ} ≤ C ‖Δu‖_{Lᵖ}`

for every Schwartz function `u` on `ℝⁿ` with values in a complex Hilbert space. -/
theorem exists_eLpNorm_lineDerivOp_lineDerivOp_le_eLpNorm_laplacian
    (v w : EuclideanSpace ℝ (Fin n)) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), F),
      eLpNorm (⇑(∂_{v} (∂_{w} u) : 𝓢(EuclideanSpace ℝ (Fin n), F))) p volume ≤
        C * eLpNorm (⇑(Δ u : 𝓢(EuclideanSpace ℝ (Fin n), F))) p volume := by
  -- Descend from dimension `n + k ≥ 3`, one dimension at a time.
  suffices h : ∀ k m (v w : EuclideanSpace ℝ (Fin m)), 3 ≤ m + k → ∃ C : ℝ≥0,
      ∀ u : 𝓢(EuclideanSpace ℝ (Fin m), F),
        eLpNorm (⇑(∂_{v} (∂_{w} u) : 𝓢(EuclideanSpace ℝ (Fin m), F))) p volume ≤
          C * eLpNorm (⇑(Δ u : 𝓢(EuclideanSpace ℝ (Fin m), F))) p volume from
    h 3 n v w (by omega)
  intro k
  induction k with
  | zero =>
    intro m v w hm
    exact exists_eLpNorm_lineDerivOp_lineDerivOp_le_of_three_le (by omega) v w hp hp_top
  | succ k ih =>
    intro m v w hm
    obtain ⟨C, hC⟩ := ih (m + 1) (EuclideanSpace.consEquivL ℝ m (0, v))
      (EuclideanSpace.consEquivL ℝ m (0, w)) (by omega)
    exact ⟨C, eLpNorm_lineDerivOp_lineDerivOp_le_of_succ v w hp.le hC⟩

/-- **The Calderón–Zygmund estimate `‖D²u‖_p ≤ C ‖Δu‖_p`.** Let `1 < p < ∞`. There is
a constant `C` with

`‖D²u‖_{Lᵖ} ≤ C ‖Δu‖_{Lᵖ}`

for every Schwartz function `u` on `ℝⁿ` with values in a complex Hilbert space, where `D²u` is the
second Fréchet derivative of `u`. -/
theorem exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian {p : ℝ≥0∞}
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), F), eLpNorm (iteratedFDeriv ℝ 2 ⇑u) p volume ≤
      C * eLpNorm (⇑(Δ u : 𝓢(EuclideanSpace ℝ (Fin n), F))) p volume := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  choose C hC using fun r : Fin 2 → Fin n =>
    exists_eLpNorm_lineDerivOp_lineDerivOp_le_eLpNorm_laplacian (F := F) (b (r 0)) (b (r 1))
      hp hp_top
  refine ⟨∑ r, C r, fun u => ?_⟩
  set D : (Fin 2 → Fin n) → 𝓢(EuclideanSpace ℝ (Fin n), F) := fun r => ∂_{b (r 0)} (∂_{b (r 1)} u)
  -- The Hessian is bounded pointwise by the sum of its values on pairs of basis vectors.
  have hpt : ∀ x, ‖iteratedFDeriv ℝ 2 u x‖ ≤ ∑ r, ‖D r x‖ := fun x => by
    refine ((iteratedFDeriv ℝ 2 u x).opNorm_le_sum_norm_apply_orthonormalBasis
      (fun _ => b)).trans_eq (Finset.sum_congr (by ext; simp) fun r _ => ?_)
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

/-- **The Calderón–Zygmund estimate `‖D²u‖_p ≤ C ‖Δu‖_p` for real functions.** Let
`1 < p < ∞`. There is a constant `C` with `‖D²u‖_{Lᵖ} ≤ C ‖Δu‖_{Lᵖ}` for every real Schwartz
function `u` on `ℝⁿ`. -/
theorem exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_real {p : ℝ≥0∞}
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), ℝ), eLpNorm (iteratedFDeriv ℝ 2 ⇑u) p volume ≤
      C * eLpNorm (⇑(Δ u : 𝓢(EuclideanSpace ℝ (Fin n), ℝ))) p volume := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian (F := ℂ) hp hp_top
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
