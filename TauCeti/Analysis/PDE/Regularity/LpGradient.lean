/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.MihlinHormander
public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.PDE.Ellipticity.ConstantCoefficient
import TauCeti.Analysis.Sobolev.WeakDeriv.TemperedDistribution
import TauCeti.Analysis.Distribution.TemperedDistribution.Deriv
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.Fourier.HessianMultiplier
import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional

/-!
# The `W^{1,p}` estimate for constant-coefficient divergence-form equations

Let `A` be a constant `n × n` matrix, uniformly elliptic with constants `0 < λ ≤ Λ` and not
necessarily symmetric, and let `u ∈ H¹(ℝⁿ)` be a weak solution of

`-∂ᵢ(Aⁱʲ ∂ⱼu) = -div G`, that is `∫ ⟨A ∇u, ∇φ⟩ = ∫ ⟨G, ∇φ⟩` for every test function `φ`,

with `G ∈ L²(ℝⁿ; ℝⁿ)`. This file proves the Calderón–Zygmund estimate

`‖∇u‖_{Lᵖ} ≤ C √(Λ / λ) ^ N / λ ‖G‖_{Lᵖ}`, `1 < p < ∞`, `N = ⌊n / 2⌋ + 1`,

with `C` depending only on `n` and `p`
(`TauCeti.PDE.exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq`). It covers the whole range
`1 < p < ∞`, on both sides of `p = 2`, and assumes no integrability of `∇u` beyond `L²`. For
`A = 1` it is the boundedness on `Lᵖ` of the matrix `-(Rᵢ Rⱼ)` of Riesz transforms, which maps `G`
to `∇u`: `∂ᵢu = -∑ⱼ Rᵢ Rⱼ Gⱼ`. It is the constant-coefficient case of the `W^{1,p}` theory for
coefficients of small or vanishing mean oscillation, whose a priori estimate for `p > 2` is
`TauCeti.PDE.exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le`; the frozen
operators there are of the form treated here.

## The argument

* **Fourier side.** The weak equation is an identity of tempered distributions,
  `∑ⱼ ∂_{cⱼ} ∂ⱼu = ∑ⱼ ∂ⱼ Gⱼ` with `cⱼ` the columns of `A`. On the Fourier side, with
  `𝓕 (∂ⱼu) = 2πi ξⱼ 𝓕 u` (`MeasureTheory.Lp.coeFn_fourier_of_lineDerivOp_eq`), it becomes
  `2πi (ξᵀ A ξ) 𝓕 u = ∑ⱼ ξⱼ 𝓕 Gⱼ` (`MeasureTheory.Lp.sum_smul_coeFn_fourier_of_sum_lineDerivOp_eq`).
  Hence `𝓕 (∂ᵢu) = ∑ⱼ mᵢⱼ 𝓕 Gⱼ` with the symbols `mᵢⱼ(ξ) = ξᵢ ξⱼ / ξᵀ A ξ`, that is
  `∂ᵢu = ∑ⱼ T_{mᵢⱼ} Gⱼ` for the `L²` Fourier multipliers `T_{mᵢⱼ}`.
* **Multiplier bound.** The symbols are smooth away from the origin and homogeneous of degree
  `0`, so they satisfy Mihlin's condition and the Mihlin–Hörmander theorem
  (`TauCeti.exists_eLpNorm_fourierMultiplierCLM_le_of_norm_iteratedFDeriv_le`) bounds `T_{mᵢⱼ}` on
  `Lᵖ`. To make the constant uniform in `A`, write `ξᵀ A ξ = ‖e ξ‖²` for a linear automorphism
  `e` with `‖e‖ ≤ √Λ` and `‖e⁻¹‖ ≤ 1 / √λ`
  (`TauCeti.PDE.exists_continuousLinearEquiv_laplacian_comp_eq`). Then
  `mᵢⱼ(ξ) = ⟪e ξ, a⟫ ⟪e ξ, b⟫ / ‖e ξ‖²`, the Hessian symbol `TauCeti.hessianSymbol a b` at `e ξ`,
  for vectors with `‖a‖ ‖b‖ ≤ 1 / λ`. The Hessian symbols satisfy Mihlin's condition uniformly in
  `a`, `b` and `e` (`TauCeti.exists_norm_iteratedFDeriv_hessianSymbol_comp_le`); the change of
  variables costs the factor `(‖e‖ ‖e⁻¹‖) ^ k ≤ √(Λ / λ) ^ k` in the `k`-th derivative.

## Main declarations

* `TauCeti.PDE.exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq`: the `W^{1,p}` estimate for
  constant coefficients, `1 < p < ∞`.

## References

* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Princeton
  University Press, 1970, Chapter III, §1 (the Riesz transforms and the a priori estimates they
  give) and Chapter IV, §3 (the Mihlin–Hörmander multiplier theorem).
* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Theorem 6.2.7.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory SchwartzMap
open scoped FourierTransform LineDeriv InnerProductSpace ENNReal NNReal ContDiff Distributions
  Gradient

section Equation

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The weak equation as an identity of tempered distributions.** If `u ∈ H¹(ℝⁿ)` solves
`-div (A ∇u) = -div G` weakly for a constant matrix `A` and `G ∈ L²`, then, writing `Dⱼ` and `Gⱼ`
for the components of `∇u` and `G` and `cⱼ` for the `j`-th column of `A`,
`∑ⱼ ∂_{cⱼ} Dⱼ = ∑ⱼ ∂ⱼ Gⱼ` as complex tempered distributions. -/
private theorem sum_lineDerivOp_eq_of_forall_energyFormH1_eq {A : Matrix ι ι ℝ}
    {u : W1p volume (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ ι)) 2}
    {G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hu : ∀ φ : 𝓓((⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ ι)), ℝ),
      PDE.energyFormH1 (fun _ => A) 0 0 u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
        ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ)
    {D Gc : ι → Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ ι))}
    (hD : ∀ j, (D j : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume] fun x =>
      ⟪(W1p.gradient u : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x,
        EuclideanSpace.basisFun ι ℝ j⟫_ℝ)
    (hGc : ∀ j, (Gc j : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume] fun x =>
      ⟪G x, EuclideanSpace.basisFun ι ℝ j⟫_ℝ) :
    ∑ j, ∂_{WithLp.toLp 2 (Aᵀ j)} (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp (D j))) =
      ∑ j, ∂_{EuclideanSpace.basisFun ι ℝ j}
        (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp (Gc j))) := by
  apply TemperedDistribution.ext_real
  intro φ hφ
  simp only [sum_apply, Lp.lineDerivOp_toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM,
    Finset.sum_neg_distrib, ← Complex.ofReal_sum, neg_inj, Complex.ofReal_inj]
  set ψ : 𝓓((⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ ι)), ℝ) :=
    φ.toTestFunction hφ (by simp)
  have hψ : (ψ : EuclideanSpace ℝ ι → ℝ) = φ := φ.coe_toTestFunction hφ _
  have h := hu ψ
  rw [PDE.energyFormH1_ofTestFunctionₗ_eq_sum, hψ] at h
  -- Both sides are the two expressions of the weak equation tested against `φ`.
  have hl : ∀ j, ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x (WithLp.toLp 2 (Aᵀ j)) * D j x =
      ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x (WithLp.toLp 2 (Aᵀ j)) •
        (innerSL ℝ ((W1p.gradient u : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x))
          (EuclideanSpace.basisFun ι ℝ j) := fun j => by
    refine integral_congr_ae ?_
    filter_upwards [hD j] with x hx
    rw [hx, innerSL_apply_apply, smul_eq_mul]
  have hint : ∀ j, Integrable (fun x =>
      lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x (EuclideanSpace.basisFun ι ℝ j) * Gc j x) :=
    fun j => by
      simpa [hψ] using integrable_lineDeriv_smul_of_locallyIntegrableOn
        (((Lp.memLp (Gc j)).locallyIntegrable (by norm_num)).locallyIntegrableOn _) ψ _
  rw [Finset.sum_congr rfl fun j _ => hl j, h, ← integral_finsetSum _ fun j _ => hint j]
  refine integral_congr_ae ?_
  filter_upwards [ae_all_iff.2 hGc] with x hx
  -- Expand `G x` in the standard basis: `⟪G, ∇φ⟫ = ∑ⱼ ∂ⱼφ Gⱼ`.
  conv_lhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr' (G x)]
  simp only [sum_inner, real_inner_smul_left, φ.differentiableAt.lineDeriv_eq_fderiv, hx]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_comm (∇ _ _), inner_gradient_left, mul_comm, real_inner_comm (G x)]

/-- The symbol `ξ ↦ ⟪ξ, v⟫ ⟪ξ, w⟫ / ξᵀ A ξ` of the operator `∂_v ∂_w (div A ∇)⁻¹`, homogeneous of
degree `0` and bounded for elliptic `A`. -/
private def divergenceSymbol (A : Matrix ι ι ℝ) (v w : EuclideanSpace ℝ ι)
    (ξ : EuclideanSpace ℝ ι) : ℂ :=
  ((⟪ξ, v⟫_ℝ * ⟪ξ, w⟫_ℝ / PDE.matrixBilinearForm A ξ ξ : ℝ) : ℂ)

/-- **The divergence symbol in normalized coordinates.** For a uniformly elliptic constant
matrix `A` there is a linear automorphism `e` with `√λ ‖ξ‖ ≤ ‖e ξ‖` and `‖e‖ ≤ √Λ` such that every
symbol `⟪ξ, v⟫ ⟪ξ, w⟫ / ξᵀ A ξ` is the Hessian symbol `⟪e ξ, a⟫ ⟪e ξ, b⟫ / ‖e ξ‖²` for vectors
with `‖a‖ ‖b‖ ≤ ‖v‖ ‖w‖ / λ`. -/
private theorem exists_divergenceSymbol_eq_hessianSymbol_comp {A : Matrix ι ι ℝ} {lam Lam : ℝ}
    (hA : PDE.UniformlyEllipticOn Set.univ (fun _ : EuclideanSpace ℝ ι => A) lam Lam) :
    ∃ e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι, (∀ ξ, √lam * ‖ξ‖ ≤ ‖e ξ‖) ∧
      ‖(e : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖ ≤ √Lam ∧
      ∀ v w : EuclideanSpace ℝ ι, ∃ a b : EuclideanSpace ℝ ι, ‖a‖ * ‖b‖ ≤ ‖v‖ * ‖w‖ / lam ∧
        divergenceSymbol A v w = hessianSymbol a b ∘ e := by
  have hlam := hA.pos
  have hsqlam : 0 < √lam := Real.sqrt_pos.2 hlam
  -- Write `ξᵀ A ξ = ‖e ξ‖²` for a linear automorphism `e`.
  obtain ⟨e, hnorm, hsymm, hbound, -⟩ :=
    PDE.exists_continuousLinearEquiv_laplacian_comp_eq (F := ℝ) hlam
      (hA.lower_bound (Set.mem_univ 0)) (hA.toQuadraticForm'_le (Set.mem_univ 0))
  set T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι := ↑e.symm
  have hT : ‖T.adjoint‖ ≤ (√lam)⁻¹ := by
    rw [LinearIsometryEquiv.norm_map]
    exact ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hsqlam.le) hsymm
  refine ⟨e, fun ξ => ?_, ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) hbound,
    fun v w => ⟨T.adjoint v, T.adjoint w, ?_, ?_⟩⟩
  · have h := hsymm (e ξ)
    rw [ContinuousLinearEquiv.symm_apply_apply] at h
    calc √lam * ‖ξ‖ ≤ √lam * ((√lam)⁻¹ * ‖e ξ‖) := by gcongr
      _ = ‖e ξ‖ := by field_simp
  · calc ‖T.adjoint v‖ * ‖T.adjoint w‖ ≤ ((√lam)⁻¹ * ‖v‖) * ((√lam)⁻¹ * ‖w‖) :=
          mul_le_mul ((T.adjoint.le_opNorm v).trans (by gcongr))
            ((T.adjoint.le_opNorm w).trans (by gcongr)) (norm_nonneg _) (by positivity)
      _ = ‖v‖ * ‖w‖ * ((√lam)⁻¹ * (√lam)⁻¹) := by ring
      _ = ‖v‖ * ‖w‖ / lam := by rw [← mul_inv, Real.mul_self_sqrt hlam.le, div_eq_mul_inv]
  · -- In these coordinates `⟪ξ, c⟫ = ⟪e ξ, T† c⟫`, so the symbol is `⟪e ξ, a⟫ ⟪e ξ, b⟫ / ‖e ξ‖²`.
    have hinner : ∀ ξ c, ⟪e ξ, T.adjoint c⟫_ℝ = ⟪ξ, c⟫_ℝ := fun ξ c => by
      rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_apply_apply]
    funext ξ
    rw [divergenceSymbol, Function.comp_apply, hessianSymbol_apply, hinner, hinner, hnorm,
      PDE.matrixBilinearForm_self]

private theorem memLp_divergenceSymbol {A : Matrix ι ι ℝ} {lam Lam : ℝ}
    (hA : PDE.UniformlyEllipticOn Set.univ (fun _ : EuclideanSpace ℝ ι => A) lam Lam)
    (v w : EuclideanSpace ℝ ι) : MemLp (divergenceSymbol A v w) ⊤ volume := by
  obtain ⟨e, -, -, hsym⟩ := exists_divergenceSymbol_eq_hessianSymbol_comp hA
  obtain ⟨a, b, hab, hsym⟩ := hsym v w
  rw [hsym]
  exact memLp_top_of_bound
    ((measurable_hessianSymbol a b).comp e.continuous.measurable).aestronglyMeasurable _
    (.of_forall fun ξ => (norm_hessianSymbol_le a b (e ξ)).trans hab)

/-- **Mihlin's condition for the divergence symbol, uniformly in the matrix.** For every order `N`
there is a constant `A₀` such that for every uniformly elliptic constant matrix `A` the symbol
`⟪ξ, v⟫ ⟪ξ, w⟫ / ξᵀ A ξ` is smooth away from the origin and satisfies Mihlin's condition of order
`N` with constant `A₀ √(Λ / λ) ^ N / λ ‖v‖ ‖w‖`. -/
private theorem exists_norm_iteratedFDeriv_divergenceSymbol_le (N : ℕ) :
    ∃ A₀ : ℝ≥0, ∀ {A : Matrix ι ι ℝ} {lam Lam : ℝ},
      PDE.UniformlyEllipticOn Set.univ (fun _ : EuclideanSpace ℝ ι => A) lam Lam →
      ∀ v w : EuclideanSpace ℝ ι, ContDiffOn ℝ ∞ (divergenceSymbol A v w) {0}ᶜ ∧
        ∀ k ≤ N, ∀ ξ : EuclideanSpace ℝ ι, ξ ≠ 0 →
          ‖iteratedFDeriv ℝ k (divergenceSymbol A v w) ξ‖ ≤
            A₀ * (√(Lam / lam) ^ N / lam * ‖v‖ * ‖w‖) / ‖ξ‖ ^ k := by
  obtain ⟨A₀, hA₀⟩ :=
    exists_norm_iteratedFDeriv_hessianSymbol_comp_le (E := EuclideanSpace ℝ ι) N
  refine ⟨A₀, fun {A lam Lam} hA v w => ?_⟩
  have hlam := hA.pos
  obtain ⟨e, hlow, he, hab⟩ := exists_divergenceSymbol_eq_hessianSymbol_comp hA
  obtain ⟨a, b, hab, hsym⟩ := hab v w
  rw [hsym]
  refine ⟨?_, fun k hk ξ hξ => (hA₀ e a b (Real.sqrt_pos.2 hlam) hlow k hk ξ hξ).trans ?_⟩
  · exact (contDiffOn_hessianSymbol a b).comp e.contDiff.contDiffOn
      fun ξ hξ => Set.mem_compl_singleton_iff.2
        ((map_ne_zero_iff e e.injective).2 (Set.mem_compl_singleton_iff.1 hξ))
  -- `(‖e‖ / √λ) ^ k ≤ √(Λ / λ) ^ N`, since `√(Λ / λ) ≥ 1` and `k ≤ N`.
  have hk' : (‖(e : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖ / √lam) ^ k ≤
      √(Lam / lam) ^ N := by
    calc (‖(e : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖ / √lam) ^ k
        ≤ √(Lam / lam) ^ k := by
          gcongr
          rw [Real.sqrt_div' _ hlam.le]
          gcongr
      _ ≤ √(Lam / lam) ^ N :=
          pow_le_pow_right₀ (Real.one_le_sqrt.2 ((one_le_div hlam).2 hA.le)) hk
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  calc (A₀ : ℝ) * ‖a‖ * ‖b‖ * (‖(e : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖ / √lam) ^ k
      = A₀ * (‖a‖ * ‖b‖) * (‖(e : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖ / √lam) ^ k := by
        ring
    _ ≤ A₀ * (‖v‖ * ‖w‖ / lam) * √(Lam / lam) ^ N := by gcongr
    _ = A₀ * (√(Lam / lam) ^ N / lam * ‖v‖ * ‖w‖) := by ring

/-- **The uniform multiplier estimate for the divergence symbol.** For `1 < p < ∞` there is a
constant `C`, depending only on the dimension and `p`, such that for every constant matrix `A`
which is uniformly elliptic with constants `λ, Λ`, the `L²` Fourier multiplier with symbol
`⟪ξ, v⟫ ⟪ξ, w⟫ / ξᵀ A ξ` satisfies `‖T f‖_p ≤ C √(Λ / λ) ^ N / λ ‖v‖ ‖w‖ ‖f‖_p`, with
`N = ⌊n / 2⌋ + 1`. -/
private theorem exists_eLpNorm_fourierMultiplierCLM_divergenceSymbol_le [Nonempty ι]
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ≥0, ∀ {A : Matrix ι ι ℝ} {lam Lam : ℝ},
      PDE.UniformlyEllipticOn Set.univ (fun _ : EuclideanSpace ℝ ι => A) lam Lam →
      ∀ (v w : EuclideanSpace ℝ ι) (m : Lp ℂ ⊤ (volume : Measure (EuclideanSpace ℝ ι))),
        (m : EuclideanSpace ℝ ι → ℂ) =ᵐ[volume] divergenceSymbol A v w →
        ∀ f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)),
          eLpNorm (Lp.fourierMultiplierCLM ℂ m f) p volume ≤
            C * ENNReal.ofReal (√(Lam / lam) ^ (Fintype.card ι / 2 + 1) / lam * ‖v‖ * ‖w‖) *
              eLpNorm f p volume := by
  have hN : Module.finrank ℝ (EuclideanSpace ℝ ι) < 2 * (Fintype.card ι / 2 + 1) := by
    rw [finrank_euclideanSpace]
    omega
  obtain ⟨C, hC⟩ := exists_eLpNorm_fourierMultiplierCLM_le_of_norm_iteratedFDeriv_le
    (V := EuclideanSpace ℝ ι) (F := ℂ) hN hp hp_top
  obtain ⟨A₀, hA₀⟩ := exists_norm_iteratedFDeriv_divergenceSymbol_le (ι := ι)
    (Fintype.card ι / 2 + 1)
  refine ⟨C * A₀, fun {A lam Lam} hA v w m hm f => ?_⟩
  set X : ℝ := √(Lam / lam) ^ (Fintype.card ι / 2 + 1) / lam * ‖v‖ * ‖w‖
  have hX : 0 ≤ X :=
    mul_nonneg (mul_nonneg (div_nonneg (by positivity) hA.pos.le) (norm_nonneg _)) (norm_nonneg _)
  obtain ⟨hcd, hbd⟩ := hA₀ hA v w
  refine (hC hcd (A := A₀ * X.toNNReal) (fun k hk ξ hξ => (hbd k hk ξ hξ).trans_eq ?_) m hm
    f).trans_eq ?_
  · rw [NNReal.coe_mul, Real.coe_toNNReal _ hX]
  · rw [ENNReal.ofReal, ENNReal.coe_mul, ENNReal.coe_mul]
    ring

omit [DecidableEq ι] in
/-- **Solving the Fourier-side equation.** At a frequency `ξ` where `ξᵀ A ξ ≠ 0`, if the Fourier
transforms `Dⱼ` of the components of `∇u` are `Dⱼ = 2πi ξⱼ U`, with `U` the Fourier transform of
`u`, and satisfy the transformed equation `∑ⱼ ⟪ξ, cⱼ⟫ Dⱼ = ∑ⱼ ξⱼ Hⱼ`, where `Hⱼ` are the Fourier
transforms of the components of `G` and `cⱼ` the columns of `A`, then
`Dᵢ = ∑ⱼ ξᵢ ξⱼ / ξᵀ A ξ Hⱼ`. -/
private theorem eq_sum_divergenceSymbol_mul {A : Matrix ι ι ℝ} {ξ : EuclideanSpace ℝ ι}
    (hq : PDE.matrixBilinearForm A ξ ξ ≠ 0) {U : ℂ} {D H : ι → ℂ}
    (hD : ∀ j, D j = 2 * Real.pi * Complex.I * ⟪ξ, EuclideanSpace.basisFun ι ℝ j⟫_ℝ * U)
    (hsum : ∑ j, (⟪ξ, WithLp.toLp 2 (Aᵀ j)⟫_ℝ : ℂ) * D j =
      ∑ j, (⟪ξ, EuclideanSpace.basisFun ι ℝ j⟫_ℝ : ℂ) * H j) (i : ι) :
    D i = ∑ j, divergenceSymbol A (EuclideanSpace.basisFun ι ℝ i)
      (EuclideanSpace.basisFun ι ℝ j) ξ * H j := by
  have hqC : (PDE.matrixBilinearForm A ξ ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hq
  -- The transformed equation reads `2πi (ξᵀ A ξ) U = ∑ⱼ ξⱼ Hⱼ`.
  have h3 : 2 * Real.pi * Complex.I * PDE.matrixBilinearForm A ξ ξ * U =
      ∑ j, (⟪ξ, EuclideanSpace.basisFun ι ℝ j⟫_ℝ : ℂ) * H j := by
    rw [← hsum, PDE.matrixBilinearForm_eq_sum_inner_transpose]
    push_cast
    simp only [hD, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  calc D i = (⟪ξ, EuclideanSpace.basisFun ι ℝ i⟫_ℝ / PDE.matrixBilinearForm A ξ ξ : ℂ) *
        (2 * Real.pi * Complex.I * PDE.matrixBilinearForm A ξ ξ * U) := by
        rw [hD]
        field_simp
    _ = _ := by
        rw [h3, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [divergenceSymbol]
        push_cast
        ring

/-- **The gradient on the Fourier side.** Let `u ∈ H¹(ℝⁿ)` solve `-div (A ∇u) = -div G` weakly,
with `A` a uniformly elliptic constant matrix, and let `U`, `Dᵢ` and `Gᵢ` be real `L²`
representatives of `u` and of the components of `∇u` and `G`. Then
`𝓕 Dᵢ (ξ) = ∑ⱼ ξᵢ ξⱼ / ξᵀ A ξ 𝓕 Gⱼ (ξ)` for almost every `ξ`. -/
private theorem coeFn_fourier_gradient_ae_eq [Nonempty ι] {A : Matrix ι ι ℝ} {lam Lam : ℝ}
    (hA : PDE.UniformlyEllipticOn Set.univ (fun _ : EuclideanSpace ℝ ι => A) lam Lam)
    {u : W1p volume (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ ι)) 2}
    {G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hu : ∀ φ : 𝓓((⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ ι)), ℝ),
      PDE.energyFormH1 (fun _ => A) 0 0 u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
        ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ)
    {U : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ ι))}
    (hU : (U : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume] W1p.value u)
    {D Gc : ι → Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ ι))}
    (hD : ∀ j, (D j : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume] fun x =>
      ⟪(W1p.gradient u : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x,
        EuclideanSpace.basisFun ι ℝ j⟫_ℝ)
    (hGc : ∀ j, (Gc j : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume] fun x =>
      ⟪G x, EuclideanSpace.basisFun ι ℝ j⟫_ℝ) (i : ι) :
    (𝓕 (Complex.ofRealCLM.compLp (D i)) : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))
      =ᵐ[volume] fun ξ => ∑ j, divergenceSymbol A (EuclideanSpace.basisFun ι ℝ i)
        (EuclideanSpace.basisFun ι ℝ j) ξ • 𝓕 (Complex.ofRealCLM.compLp (Gc j)) ξ := by
  -- `Dⱼ` is the weak derivative of `u` in the direction `eⱼ`, so `𝓕 Dⱼ = 2πi ξⱼ 𝓕 U`.
  have hF1 : ∀ j, (𝓕 (Complex.ofRealCLM.compLp (D j)) :
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) =ᵐ[volume] fun ξ =>
        (2 * Real.pi * Complex.I * ⟪ξ, EuclideanSpace.basisFun ι ℝ j⟫_ℝ) •
          𝓕 (Complex.ofRealCLM.compLp U) ξ := fun j => by
    refine Lp.coeFn_fourier_of_lineDerivOp_eq
      ((hasWeakLineDerivOn_iff_lineDerivOp_toTemperedDistribution_ofReal_eq U (D j) _).1 ?_)
    refine (((W1p.hasWeakFDerivOn u).hasWeakLineDerivOn _).congr_ae
      (ae_restrict_of_ae hU.symm)).congr_ae_deriv (ae_restrict_of_ae ?_)
    filter_upwards [hD j] with x hx
    rw [hx, innerSL_apply_apply]
  -- The weak equation gives `∑ⱼ ⟪ξ, cⱼ⟫ 𝓕 Dⱼ = ∑ⱼ ξⱼ 𝓕 Gⱼ`.
  have hF2 := Lp.sum_smul_coeFn_fourier_of_sum_lineDerivOp_eq
    (sum_lineDerivOp_eq_of_forall_energyFormH1_eq hu hD hGc)
  filter_upwards [ae_all_iff.2 hF1, hF2, Measure.ae_ne volume 0] with ξ h1 h2 hξ
  have hq : PDE.matrixBilinearForm A ξ ξ ≠ 0 := by
    rw [PDE.matrixBilinearForm_self]
    exact (hA.quadraticForm_pos (Set.mem_univ ξ) hξ).ne'
  simp only [h1, smul_eq_mul] at h2 ⊢
  exact eq_sum_divergenceSymbol_mul hq (fun j => rfl) h2 i

/-- **From the Fourier identity to the `Lᵖ` bound.** If `𝓕 D = ∑ⱼ mᵢⱼ 𝓕 gⱼ` with the divergence
symbols `mᵢⱼ(ξ) = ξᵢ ξⱼ / ξᵀ A ξ`, then `D = ∑ⱼ T_{mᵢⱼ} gⱼ`, and any bound on the multipliers
`T_{mᵢⱼ}` in `Lᵖ` bounds `‖D‖_p` by the sum of the `‖gⱼ‖_p`. -/
private theorem eLpNorm_le_sum_of_coeFn_fourier_ae_eq {A : Matrix ι ι ℝ} {lam Lam : ℝ}
    (hA : PDE.UniformlyEllipticOn Set.univ (fun _ : EuclideanSpace ℝ ι => A) lam Lam)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {C₀ : ℝ≥0} {X : ℝ}
    (hC₀ : ∀ (v w : EuclideanSpace ℝ ι) (m : Lp ℂ ⊤ (volume : Measure (EuclideanSpace ℝ ι))),
      (m : EuclideanSpace ℝ ι → ℂ) =ᵐ[volume] divergenceSymbol A v w →
      ∀ f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)),
        eLpNorm (Lp.fourierMultiplierCLM ℂ m f) p volume ≤
          C₀ * ENNReal.ofReal (X * ‖v‖ * ‖w‖) * eLpNorm f p volume)
    {D : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))}
    {g : ι → Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))} (i : ι)
    (h : (𝓕 D : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) =ᵐ[volume] fun ξ =>
      ∑ j, divergenceSymbol A (EuclideanSpace.basisFun ι ℝ i)
        (EuclideanSpace.basisFun ι ℝ j) ξ • 𝓕 (g j) ξ) :
    eLpNorm D p volume ≤ ∑ j, C₀ * ENNReal.ofReal X * eLpNorm (g j) p volume := by
  set m := fun j => (memLp_divergenceSymbol hA (EuclideanSpace.basisFun ι ℝ i)
    (EuclideanSpace.basisFun ι ℝ j)).toLp
  -- `D = ∑ⱼ T_{mᵢⱼ} gⱼ`, since both sides have the same Fourier transform.
  have hD : D = ∑ j, Lp.fourierMultiplierCLM ℂ (m j) (g j) := by
    have h𝓕 : 𝓕 D = 𝓕 (∑ j, Lp.fourierMultiplierCLM ℂ (m j) (g j)) := by
      rw [FourierTransform.fourier_sum]
      refine Lp.ext ?_
      filter_upwards [h, Lp.coeFn_finsetSum Finset.univ fun j =>
          𝓕 (Lp.fourierMultiplierCLM ℂ (m j) (g j)),
        ae_all_iff.2 fun j => Lp.coeFn_fourier_fourierMultiplierCLM_toLp (g j)
          (memLp_divergenceSymbol hA (EuclideanSpace.basisFun ι ℝ i)
            (EuclideanSpace.basisFun ι ℝ j))] with ξ h1 h2 h3
      rw [h1, h2, Finset.sum_apply]
      exact Finset.sum_congr rfl fun j _ => (h3 j).symm
    have h' := congrArg 𝓕⁻ h𝓕
    rwa [FourierTransform.fourierInv_fourier_eq, FourierTransform.fourierInv_fourier_eq] at h'
  rw [hD, eLpNorm_congr_ae (Lp.coeFn_finsetSum _ _)]
  refine (eLpNorm_sum_le hp).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (hC₀ _ _ (m j) (MemLp.coeFn_toLp _) (g j)).trans_eq ?_
  simp only [OrthonormalBasis.norm_eq_one, mul_one]

omit [DecidableEq ι] in
/-- The complexification of a real `L²` representative of a component `⟪g, v⟫` has modulus
`|⟪g, v⟫|` almost everywhere. -/
private theorem norm_ofRealCLM_compLp_ae_eq {g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {v : EuclideanSpace ℝ ι} {f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ ι))}
    (hf : (f : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume] fun x => ⟪g x, v⟫_ℝ) :
    ∀ᵐ x ∂volume, ‖Complex.ofRealCLM.compLp f x‖ = |⟪g x, v⟫_ℝ| := by
  filter_upwards [Complex.ofRealCLM.coeFn_compLp f, hf] with x h1 h2
  rw [h1, Complex.ofRealCLM_apply, Complex.norm_real, h2, Real.norm_eq_abs]

omit [DecidableEq ι] in
/-- The components `x ↦ ⟪g x, eⱼ⟫` of a vector field `g ∈ L²` in the standard basis have real
`L²` representatives. -/
private theorem exists_forall_coeFn_ae_eq_inner_basisFun
    {g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hg : MemLp g 2 volume) :
    ∃ D : ι → Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ ι)), ∀ j,
      (D j : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume] fun x => ⟪g x, EuclideanSpace.basisFun ι ℝ j⟫_ℝ :=
  ⟨fun j => (((innerSL ℝ).flip (EuclideanSpace.basisFun ι ℝ j)).comp_memLp' hg).toLp _,
    fun _ => MemLp.coeFn_toLp _⟩

end Equation

namespace PDE

open Matrix TopologicalSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The `W^{1,p}` estimate for constant coefficients.** Let `1 < p < ∞`. There is a constant
`C`, depending only on the dimension `n` and on `p`, with the following property. Let `A` be a
constant matrix, uniformly elliptic with constants `0 < λ ≤ Λ` and not necessarily symmetric, and
let `u ∈ H¹(ℝⁿ)` solve `-div (A ∇u) = -div G` weakly, that is `∫ ⟨A ∇u, ∇φ⟩ = ∫ ⟨G, ∇φ⟩` for every
test function `φ`, with `G ∈ L²`. Then

`‖∇u‖_{Lᵖ} ≤ C √(Λ / λ) ^ N / λ ‖G‖_{Lᵖ}`, `N = ⌊n / 2⌋ + 1`.

Here `p` may lie on either side of `2`, and no integrability of `∇u` beyond `L²` is assumed: if
`G ∉ Lᵖ` the right-hand side is infinite. For `A = 1` the components of `∇u` are given by Riesz
transforms, `∂ⱼu = -∑ₖ Rⱼ Rₖ Gₖ`, so this is the Calderón–Zygmund estimate for the operator
`G ↦ ∇ Δ⁻¹ div G`. -/
theorem exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq {p : ℝ≥0∞}
    (hp : 1 < p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ≥0, ∀ {A : Matrix ι ι ℝ} {lam Lam : ℝ},
      UniformlyEllipticOn Set.univ (fun _ : EuclideanSpace ℝ ι => A) lam Lam →
      ∀ (u : W1p volume (⊤ : Opens (EuclideanSpace ℝ ι)) 2)
        (G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι), MemLp G 2 volume →
        (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ ι)), ℝ),
          energyFormH1 (fun _ => A) 0 0 u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
            ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ) →
        eLpNorm (W1p.gradient u : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) p volume ≤
          C * ENNReal.ofReal (√(Lam / lam) ^ (Fintype.card ι / 2 + 1) / lam) *
            eLpNorm G p volume := by
  -- In dimension `0` the gradient vanishes.
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨0, fun {A lam Lam} _ u G _ _ => ?_⟩
    have h0 : (W1p.gradient u : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) = 0 :=
      funext fun _ => Subsingleton.elim _ _
    rw [h0, eLpNorm_zero]
    exact zero_le
  obtain ⟨C₀, hC₀⟩ := exists_eLpNorm_fourierMultiplierCLM_divergenceSymbol_le (ι := ι) hp hp_top
  refine ⟨(Fintype.card ι : ℝ≥0) ^ 2 * C₀, fun {A lam Lam} hA u G hG hu => ?_⟩
  set e := EuclideanSpace.basisFun ι ℝ
  set X : ℝ := √(Lam / lam) ^ (Fintype.card ι / 2 + 1) / lam
  -- Real `L²` representatives of `u`, of the components of `∇u` and of those of `G`.
  have hgrad : MemLp (W1p.gradient u : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) 2 volume := by
    simpa using Lp.memLp (W1p.gradient u)
  have hU := MemLp.coeFn_toLp (W1p.memLp_value u)
  obtain ⟨D, hD⟩ := exists_forall_coeFn_ae_eq_inner_basisFun hgrad
  obtain ⟨Gc, hGc⟩ := exists_forall_coeFn_ae_eq_inner_basisFun hG
  -- Each component of `G`, and then each component of `∇u`, is bounded in `Lᵖ`.
  have hGle : ∀ j, eLpNorm (Complex.ofRealCLM.compLp (Gc j)) p volume ≤ eLpNorm G p volume :=
    fun j => eLpNorm_mono_ae (Lp.aestronglyMeasurable _) <|
      (norm_ofRealCLM_compLp_ae_eq (hGc j)).mono fun x hx =>
        hx.trans_le ((abs_real_inner_le_norm _ _).trans (by simp))
  have hDle : ∀ i, eLpNorm (Complex.ofRealCLM.compLp (D i)) p volume ≤
      Fintype.card ι * (C₀ * ENNReal.ofReal X * eLpNorm G p volume) := fun i => by
    refine (eLpNorm_le_sum_of_coeFn_fourier_ae_eq hA hp.le (fun v w => hC₀ hA v w) i
      (coeFn_fourier_gradient_ae_eq hA hu hU hD hGc i)).trans ?_
    calc ∑ j, (C₀ : ℝ≥0∞) * ENNReal.ofReal X * eLpNorm (Complex.ofRealCLM.compLp (Gc j)) p volume
        ≤ ∑ _j : ι, (C₀ : ℝ≥0∞) * ENNReal.ofReal X * eLpNorm G p volume :=
          Finset.sum_le_sum fun j _ => by gcongr; exact hGle j
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Summing over the components.
  have : Fact (1 ≤ p) := ⟨hp.le⟩
  calc eLpNorm (W1p.gradient u : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) p volume
      ≤ ∑ i, eLpNorm (Complex.ofRealCLM.compLp (D i)) p volume := by
        -- The gradient is controlled by its coordinates in the orthonormal basis `e`.
        refine (e.toBasis.eLpNorm_le_sum_enorm_mul_eLpNorm_coord
          hgrad.aestronglyMeasurable).trans_eq (Finset.sum_congr rfl fun i _ => ?_)
        rw [e.coe_toBasis, ← ofReal_norm (e i), e.orthonormal.1 i, ENNReal.ofReal_one, one_mul]
        refine eLpNorm_congr_norm_ae ((e.toBasis.coord i).continuous_of_finiteDimensional
          |>.comp_aestronglyMeasurable hgrad.aestronglyMeasurable) (Lp.aestronglyMeasurable _) ?_
        filter_upwards [norm_ofRealCLM_compLp_ae_eq (hD i)] with x hx
        rw [hx, Module.Basis.coord_apply, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.repr_apply_apply, real_inner_comm, Real.norm_eq_abs]
    _ ≤ ∑ _i : ι, (Fintype.card ι : ℝ≥0∞) * (C₀ * ENNReal.ofReal X * eLpNorm G p volume) :=
        Finset.sum_le_sum fun i _ => hDle i
    _ = ((Fintype.card ι : ℝ≥0) ^ 2 * C₀ : ℝ≥0) * ENNReal.ofReal X * eLpNorm G p volume := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        push_cast
        ring

end PDE

end TauCeti
