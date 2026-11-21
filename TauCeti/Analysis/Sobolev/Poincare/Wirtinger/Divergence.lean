/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Sobolev
public import TauCeti.Analysis.Sobolev.TestFunctionLp.Basic
public import TauCeti.MeasureTheory.Function.Lp.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional
import TauCeti.Analysis.Sobolev.W1p.Zero
import TauCeti.MeasureTheory.Function.Holder

/-!
# Mean-zero functions on a ball are divergences

Let `B = B(x₀, t)` be a ball in a finite-dimensional real inner product space `E` of dimension
`n ≥ 1`, with an additive Haar measure `μ`, and let `1 < r ≤ p < ∞` with `δ = 1/r - 1/p < 1/n`.
This file proves that every `h ∈ Lʳ` vanishing off `B` with `∫ h = 0` is the divergence of a field
in `Lᵖ`: there is `H ∈ Lᵖ(E; E)` with

`∫ h φ = ∫ ⟪H, ∇φ⟫` for every test function `φ`, and `‖H‖_{Lᵖ} ≤ C t μ(B)^(-δ) ‖h‖_{Lʳ}`,

with `C` depending only on `n`, `r` and `p`
(`TauCeti.exists_memLp_forall_integral_mul_eq_integral_inner_gradient_of_integral_eq_zero`).
So `-div H = h` in the sense of distributions, and `H` gains integrability over `h` when `p > r`.
This is how a scalar right-hand side `h` of a divergence-form equation `-div(a ∇u) = -div G + h`
is absorbed into the divergence datum, as in the localization of `W^{1,p}` estimates: a cutoff of a
local solution solves such an equation with a scalar term of mean zero.

The proof is by duality. Since `h` has mean zero on `B`, `∫ h φ = ∫_B h (φ - φ_B)`, and Hölder's
inequality with the Sobolev–Poincaré inequality on the ball
(`TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_ball_subset`, in norms rather than averages) bound
it by `C t μ(B)^(-δ) ‖h‖_{Lʳ} ‖∇φ‖_{L^q}`, `q` the exponent conjugate to `p`. A functional on test
functions bounded by the `L^q` norm of the gradient extends by Hahn–Banach, through the partial
derivatives along an orthonormal basis, to `(L^q)ⁿ`, and the integral representation of the dual of
`L^q` (`MeasureTheory.Lp.dualEquiv`) represents it by a field `H ∈ Lᵖ`
(`TauCeti.exists_memLp_forall_eq_integral_inner_gradient_of_abs_le`). Some condition on the mean of
`h` is needed: a function with nonzero integral, such as the indicator of `B`, is not the divergence
of a field in `Lᵖ` once `p ≤ n / (n - 1)`, since such fields have vanishing flux at infinity.

## Main declarations

* `TauCeti.exists_memLp_forall_eq_integral_inner_gradient_of_abs_le`: a linear functional on test
  functions bounded by `M ‖∇φ‖_{L^q}` is `φ ↦ ∫ ⟪H, ∇φ⟫` for a field `H ∈ Lᵖ` of norm at most
  `n² M`.
* `TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_ball_subset`: the Sobolev–Poincaré inequality
  on a ball inside the domain, `‖u - u_B‖_{Lˢ(B)} ≤ K t μ(B)^(-δ) ‖∇u‖_{L^q(B)}`.
* `TauCeti.exists_memLp_forall_integral_mul_eq_integral_inner_gradient_of_integral_eq_zero`:
  mean-zero functions on a ball are divergences of `Lᵖ` fields, with the scale-invariant bound.

## References

* G. P. Galdi, *An Introduction to the Mathematical Theory of the Navier–Stokes Equations*, 2nd ed.,
  Springer, 2011, Section III.3 (the equation `div H = h` for `h` of mean zero).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemmas 7.12 and 7.16 (the Sobolev–Poincaré inequality).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal NNReal Gradient InnerProductSpace

section Representation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Opens E}

/-- The directional derivative of a test function along `v` is the pairing of `v` with its
gradient. -/
private theorem lineDerivCLM_apply_eq_inner (φ : 𝓓(Ω, ℝ)) (v x : E) :
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ : E → ℝ) x =
      ⟪v, ∇ (φ : E → ℝ) x⟫_ℝ := by
  rw [TestFunction.lineDerivCLM_apply_of_le le_top, real_inner_comm, gradient,
    InnerProductSpace.toDual_symm_apply,
    (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv]

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
  {p q : ℝ≥0∞}

/-- The partial derivatives `⟪bᵢ, ∇φ⟫` of a test function along an orthonormal basis, as a linear
map into `(Lᵠ(Ω))ᵈ`. -/
private def partialDerivativesLp (b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E) :
    𝓓(Ω, ℝ) →ₗ[ℝ] (Fin (finrank ℝ E) → Lp ℝ q (μ.restrict Ω)) :=
  LinearMap.pi fun i => (testFunctionLpₗ μ Ω q).comp
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (b i)).toLinearMap

private theorem partialDerivativesLp_apply_ae (b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E)
    (φ : 𝓓(Ω, ℝ)) (i : Fin (finrank ℝ E)) :
    ∀ᵐ x ∂μ.restrict Ω, partialDerivativesLp (μ := μ) (q := q) b φ i x =
      ⟪b i, ∇ (φ : E → ℝ) x⟫_ℝ := by
  filter_upwards [testFunctionLp_apply_ae (mu := μ) q
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (b i) φ)] with x hx
  simp only [partialDerivativesLp, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
    testFunctionLpₗ_apply, ContinuousLinearMap.coe_coe]
  rw [hx, lineDerivCLM_apply_eq_inner]

/-- The `Lᵠ` norm of the gradient of a test function is at most `d` times the norm of its
partial derivatives in `(Lᵠ(Ω))ᵈ`. -/
private theorem toReal_eLpNorm_gradient_le [Fact (1 ≤ q)]
    (b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E) (φ : 𝓓(Ω, ℝ)) :
    (eLpNorm (∇ (φ : E → ℝ)) q μ).toReal ≤
      finrank ℝ E * ‖partialDerivativesLp (μ := μ) (q := q) b φ‖ := by
  set T := partialDerivativesLp (μ := μ) (q := q) b
  have hDnorm (i : Fin (finrank ℝ E)) :
      ‖T φ i‖ₑ = eLpNorm (fun x => ⟪b i, ∇ (φ : E → ℝ) x⟫_ℝ) q μ := by
    simp only [T, partialDerivativesLp, LinearMap.pi_apply, LinearMap.coe_comp,
      Function.comp_apply, testFunctionLpₗ_apply, ContinuousLinearMap.coe_coe]
    rw [enorm_testFunctionLp_eq_eLpNorm]
    congr 1
    funext x
    exact lineDerivCLM_apply_eq_inner φ (b i) x
  have h := b.toBasis.eLpNorm_le_sum_enorm_mul_eLpNorm_coord (p := q) (μ := μ)
    (continuous_gradient_testFunction φ).aestronglyMeasurable
  have hb (i : Fin (finrank ℝ E)) : ‖b i‖ₑ = 1 := by
    rw [← ofReal_norm, b.orthonormal.1 i, ENNReal.ofReal_one]
  simp only [OrthonormalBasis.coe_toBasis, hb, one_mul,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
    Basis.coord_apply] at h
  simp_rw [← hDnorm] at h
  have hfin : ∀ i ∈ Finset.univ, ‖T φ i‖ₑ ≠ ⊤ := fun i _ => eNorm_ne_top
  calc (eLpNorm (∇ (φ : E → ℝ)) q μ).toReal ≤ (∑ i, ‖T φ i‖ₑ).toReal :=
        ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hfin) h
    _ = ∑ i, ‖T φ i‖ := by
        rw [ENNReal.toReal_sum hfin]
        simp only [toReal_eNorm]
    _ ≤ ∑ _i : Fin (finrank ℝ E), ‖T φ‖ := Finset.sum_le_sum fun i _ => norm_le_pi_norm (T φ) i
    _ = finrank ℝ E * ‖T φ‖ := by simp

/-- **Hahn–Banach for gradient bounds.** A linear functional on test functions bounded by `M`
times the `Lᵠ` norm of the gradient extends to a continuous functional on `(Lᵠ(Ω))ᵈ`, of norm at
most `d M`, through the partial derivatives. -/
private theorem exists_dual_comp_partialDerivativesLp_eq [Fact (1 ≤ q)]
    (b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E) (ℓ : 𝓓(Ω, ℝ) →ₗ[ℝ] ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hℓ : ∀ φ : 𝓓(Ω, ℝ), |ℓ φ| ≤ M * (eLpNorm (∇ (φ : E → ℝ)) q μ).toReal) :
    ∃ Λ : StrongDual ℝ (Fin (finrank ℝ E) → Lp ℝ q (μ.restrict Ω)), ‖Λ‖ ≤ finrank ℝ E * M ∧
      ∀ φ, Λ (partialDerivativesLp (μ := μ) (q := q) b φ) = ℓ φ := by
  set T := partialDerivativesLp (μ := μ) (q := q) b
  have hbound (φ : 𝓓(Ω, ℝ)) : |ℓ φ| ≤ finrank ℝ E * M * ‖T φ‖ :=
    (hℓ φ).trans (by
      rw [mul_comm (finrank ℝ E : ℝ) M, mul_assoc]; gcongr; exact toReal_eLpNorm_gradient_le b φ)
  have hker : LinearMap.ker T.rangeRestrict ≤ LinearMap.ker ℓ := by
    rw [LinearMap.ker_rangeRestrict]
    intro φ hφ
    have h := hbound φ
    rw [LinearMap.mem_ker.mp hφ, norm_zero, mul_zero] at h
    exact LinearMap.mem_ker.mpr (abs_nonpos_iff.mp h)
  let f₀ : LinearMap.range T →ₗ[ℝ] ℝ :=
    T.rangeRestrict.liftOfSurjective T.surjective_rangeRestrict ⟨ℓ, hker⟩
  have hf₀_apply (φ : 𝓓(Ω, ℝ)) : f₀ (T.rangeRestrict φ) = ℓ φ :=
    LinearMap.equivOfSurjective_apply T.surjective_rangeRestrict hker
  have hf₀ : ∀ s, ‖f₀ s‖ ≤ finrank ℝ E * M * ‖s‖ := by
    intro s
    obtain ⟨φ, rfl⟩ := T.surjective_rangeRestrict s
    rw [hf₀_apply, Real.norm_eq_abs, ← Submodule.norm_coe, LinearMap.codRestrict_apply]
    exact hbound φ
  obtain ⟨Λ, hΛ, hΛnorm⟩ := exists_extension_norm_eq _ (f₀.mkContinuous (finrank ℝ E * M) hf₀)
  refine ⟨Λ, hΛnorm.trans_le (LinearMap.mkContinuous_norm_le _ (by positivity) hf₀),
    fun φ => ?_⟩
  have h := hΛ (T.rangeRestrict φ)
  simpa only [LinearMap.codRestrict_apply, LinearMap.mkContinuous_apply, hf₀_apply] using h

omit [FiniteDimensional ℝ E] [BorelSpace E] [IsFiniteMeasureOnCompacts μ] in
/-- **Representation of functionals on `(Lᵠ(Ω))ᵈ`.** A continuous functional `Λ` on `(Lᵠ(Ω))ᵈ` is
`g ↦ ∑ᵢ ∫_Ω ⟪H, bᵢ⟫ gᵢ` for a field `H ∈ Lᵖ(Ω; E)` with `‖H‖_{Lᵖ} ≤ d ‖Λ‖`. -/
private theorem exists_memLp_forall_dual_apply_eq [SigmaFinite (μ.restrict Ω)] [Fact (1 ≤ p)]
    [Fact (1 ≤ q)] [p.HolderConjugate q] (hq : 1 < q) (hq_top : q ≠ ⊤)
    (b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E)
    (Λ : StrongDual ℝ (Fin (finrank ℝ E) → Lp ℝ q (μ.restrict Ω))) :
    ∃ H : E → E, MemLp H p (μ.restrict Ω) ∧
      eLpNorm H p (μ.restrict Ω) ≤ finrank ℝ E * ENNReal.ofReal ‖Λ‖ ∧
      ∀ g, Λ g = ∑ i, ∫ x in Ω, ⟪H x, b i⟫_ℝ * g i x ∂μ := by
  classical
  let Λc : Fin (finrank ℝ E) → StrongDual ℝ (Lp ℝ q (μ.restrict Ω)) := fun i =>
    Λ.comp (ContinuousLinearMap.single ℝ (fun _ : Fin (finrank ℝ E) => Lp ℝ q (μ.restrict Ω)) i)
  let Hc : Fin (finrank ℝ E) → Lp ℝ p (μ.restrict Ω) := fun i =>
    (Lp.dualEquiv ℝ (μ.restrict Ω) p q hq hq_top).symm (Λc i)
  have hHc (i : Fin (finrank ℝ E)) : ‖Hc i‖ ≤ ‖Λ‖ := by
    simp only [Hc, LinearIsometryEquiv.norm_map]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun g => ?_
    calc ‖Λc i g‖ ≤ ‖Λ‖ *
          ‖Pi.single (M := fun _ : Fin (finrank ℝ E) => Lp ℝ q (μ.restrict Ω)) i g‖ :=
          Λ.le_opNorm _
      _ = ‖Λ‖ * ‖g‖ := by rw [Pi.norm_single]
  have hHi (i : Fin (finrank ℝ E)) : MemLp (fun x => (Hc i : E → ℝ) x • b i) p (μ.restrict Ω) :=
    (Lp.memLp (Hc i)).smul (memLp_top_const (b i))
  have hsum : (fun x => ∑ i, (Hc i : E → ℝ) x • b i) = ∑ i, fun x => (Hc i : E → ℝ) x • b i :=
    (Finset.sum_fn _ _).symm
  have hinner (x : E) (i : Fin (finrank ℝ E)) : ⟪∑ j, (Hc j : E → ℝ) x • b j, b i⟫_ℝ = Hc i x := by
    simp [sum_inner, real_inner_smul_left, b.inner_eq_ite]
  refine ⟨fun x => ∑ i, (Hc i : E → ℝ) x • b i, ?_, ?_, fun g => ?_⟩
  · rw [hsum]
    exact memLp_finsetSum' Finset.univ fun i _ => hHi i
  · calc eLpNorm (fun x => ∑ i, (Hc i : E → ℝ) x • b i) p (μ.restrict Ω)
        ≤ ∑ i, eLpNorm (fun x => (Hc i : E → ℝ) x • b i) p (μ.restrict Ω) := by
          rw [hsum]
          exact eLpNorm_sum_le Fact.out
      _ ≤ ∑ _i : Fin (finrank ℝ E), ENNReal.ofReal ‖Λ‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [eLpNorm_congr_norm_ae (hHi i).aestronglyMeasurable (Lp.aestronglyMeasurable (Hc i))
            (ae_of_all _ fun x => by rw [norm_smul, b.orthonormal.1 i, mul_one]), ← Lp.eNorm_def,
            ← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hHc i)
      _ = finrank ℝ E * ENNReal.ofReal ‖Λ‖ := by simp
  · conv_lhs => rw [← Finset.univ_sum_single g]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp_rw [hinner]
    exact (Lp.integral_dualEquiv_symm_mul (p := p) hq hq_top (Λc i) (g i)).symm

/-- **Functionals bounded by the gradient are divergences.** Let `1 < q < ∞` and let `p` be its
conjugate exponent. If a linear functional `ℓ` on the test functions of `Ω` satisfies
`|ℓ φ| ≤ M ‖∇φ‖_{L^q}`, then `ℓ φ = ∫_Ω ⟪H, ∇φ⟫` for a field `H ∈ Lᵖ(Ω; E)` with
`‖H‖_{Lᵖ(Ω)} ≤ d² M`, where `d` is the dimension. In other words `ℓ = -div H` in the sense of
distributions. -/
theorem exists_memLp_forall_eq_integral_inner_gradient_of_abs_le [SigmaFinite (μ.restrict Ω)]
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q] (hq : 1 < q) (hq_top : q ≠ ⊤)
    (ℓ : 𝓓(Ω, ℝ) →ₗ[ℝ] ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hℓ : ∀ φ : 𝓓(Ω, ℝ), |ℓ φ| ≤ M * (eLpNorm (∇ (φ : E → ℝ)) q μ).toReal) :
    ∃ H : E → E, MemLp H p (μ.restrict Ω) ∧
      eLpNorm H p (μ.restrict Ω) ≤ (finrank ℝ E : ℝ≥0∞) ^ 2 * ENNReal.ofReal M ∧
      ∀ φ : 𝓓(Ω, ℝ), ℓ φ = ∫ x in Ω, ⟪H x, ∇ (φ : E → ℝ) x⟫_ℝ ∂μ := by
  set b := stdOrthonormalBasis ℝ E
  obtain ⟨Λ, hΛ, hΛT⟩ := exists_dual_comp_partialDerivativesLp_eq (μ := μ) (q := q) b ℓ hM hℓ
  obtain ⟨H, hH, hHnorm, hHΛ⟩ := exists_memLp_forall_dual_apply_eq (p := p) hq hq_top b Λ
  refine ⟨H, hH, ?_, fun φ => ?_⟩
  · calc eLpNorm H p (μ.restrict Ω) ≤ finrank ℝ E * ENNReal.ofReal ‖Λ‖ := hHnorm
      _ ≤ finrank ℝ E * ENNReal.ofReal (finrank ℝ E * M) := by gcongr
      _ = (finrank ℝ E : ℝ≥0∞) ^ 2 * ENNReal.ofReal M := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, sq, mul_assoc]
  -- `∑ᵢ ⟪H, bᵢ⟫ ⟪bᵢ, ∇φ⟫ = ⟪H, ∇φ⟫`.
  have hint (i : Fin (finrank ℝ E)) : Integrable (fun x => ⟪H x, b i⟫_ℝ *
      partialDerivativesLp (μ := μ) (q := q) b φ i x) (μ.restrict Ω) :=
    (((innerSL ℝ).flip (b i)).comp_memLp' hH).integrable_mul (Lp.memLp _)
  rw [← hΛT φ, hHΛ, ← integral_finsetSum _ fun i _ => hint i]
  refine integral_congr_ae ?_
  filter_upwards [ae_all_iff.2 fun i => partialDerivativesLp_apply_ae (μ := μ) (q := q) b φ i]
    with x hx
  simp only [hx]
  exact b.sum_inner_mul_inner (H x) (∇ (φ : E → ℝ) x)

end Representation

section Ball

/-- An `Lˢ` average written as a norm: `(⨍_B ‖f‖ˢ)^(1/s) = μ(B)^(-1/s) ‖f‖_{Lˢ(B)}`. -/
private theorem setLAverage_rpow_rpow_inv_eq {E F : Type*} [MeasurableSpace E] {μ : Measure E}
    [NormedAddCommGroup F] {B : Set E}
    {f : E → F} (hf : AEStronglyMeasurable f (μ.restrict B)) {s : ℝ≥0∞} (hs0 : s ≠ 0)
    (hs : s ≠ ⊤) :
    (⨍⁻ x in B, ‖f x‖ₑ ^ s.toReal ∂μ) ^ s.toReal⁻¹ =
      μ B ^ (-s.toReal⁻¹) * eLpNorm f s (μ.restrict B) := by
  rw [setLAverage_eq, eLpNorm_eq_lintegral_rpow_eNorm_toReal hs0 hs hf, ENNReal.div_eq_inv_mul,
    ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 ENNReal.toReal_nonneg), ENNReal.inv_rpow,
    ← ENNReal.rpow_neg, one_div]

/-- If `h` vanishes off `B` and has mean zero, its pairing with `φ` only sees `φ - c`, for any
constant `c`. -/
private theorem integral_mul_eq_setIntegral_sub_smul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {B : Set α} {h φ : α → ℝ}
    (hh : Integrable h (μ.restrict B)) (hsupp : ∀ᵐ x ∂μ, x ∉ B → h x = 0)
    (hmean : ∫ x, h x ∂μ = 0) (c : ℝ)
    (hint : Integrable (fun x => (φ x - c) * h x) (μ.restrict B)) :
    ∫ x, h x * φ x ∂μ = ∫ x in B, (φ x - c) • h x ∂μ := by
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero (s := B)
    (by filter_upwards [hsupp] with x hx hxB; rw [hx hxB, zero_mul])]
  calc ∫ x in B, h x * φ x ∂μ = ∫ x in B, ((φ x - c) * h x + c * h x) ∂μ :=
        integral_congr_ae (ae_of_all _ fun x => by ring)
    _ = _ := by
        rw [integral_add hint (hh.const_mul c), integral_const_mul,
          (setIntegral_eq_integral_of_ae_compl_eq_zero hsupp).trans hmean, mul_zero, add_zero]
        simp only [smul_eq_mul]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] [Nontrivial E]

/-- **The Sobolev–Poincaré inequality on a ball, in norms.** Let `n ≥ 1` be the dimension, let
`1 ≤ q ≤ s < ∞` with `δ = 1/q - 1/s < 1/n`, and let `q ≤ p₀`. If `u ∈ W^{1,p₀}(Ω)` and
`B = B(x₀, t) ⊆ Ω`, then

`‖u - u_B‖_{Lˢ(B)} ≤ K t μ(B)^(-δ) ‖∇u‖_{L^q(B)}`,

with `K = 2ⁿ / n · ((1 - δ) / (1/n - δ)) ^ (1 - δ)` depending only on `n`, `q` and `s`. This is
`TauCeti.W1p.setLAverage_rpow_enorm_value_sub_setAverage_le_of_ball_subset` with the averages
written as norms. -/
theorem W1p.eLpNorm_value_sub_setAverage_le_of_ball_subset {Ω : Opens E} {p₀ q : ℝ≥0∞}
    [Fact (1 ≤ p₀)] [Fact (1 ≤ q)] (hq : q ≠ ⊤) (hqp₀ : q ≤ p₀) {s : ℝ≥0} (hqs : q ≤ s) {δ : ℝ}
    (hδ : q.toReal⁻¹ - (s : ℝ)⁻¹ = δ) (hδn : δ < (finrank ℝ E : ℝ)⁻¹) {x₀ : E} {t : ℝ}
    (ht : 0 < t) (hball : ball x₀ t ⊆ (Ω : Set E)) (u : W1p μ Ω p₀) :
    eLpNorm (fun x => W1p.value u x - ⨍ y in ball x₀ t, W1p.value u y ∂μ) s
        (μ.restrict (ball x₀ t)) ≤
      ENNReal.ofReal (2 ^ finrank ℝ E / finrank ℝ E *
          ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ) * t) *
        μ (ball x₀ t) ^ (-δ) * eLpNorm (W1p.gradient u) q (μ.restrict (ball x₀ t)) := by
  set B := ball x₀ t
  set K := ENNReal.ofReal (2 ^ finrank ℝ E / finrank ℝ E *
    ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ) * t)
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne'
  have hs0 : (s : ℝ≥0∞) ≠ 0 := ne_bot_of_le_ne_bot hq0 hqs
  have hB0 : μ B ≠ 0 := (measure_ball_pos μ x₀ ht).ne'
  have hBt : μ B ≠ ⊤ := measure_ball_lt_top.ne
  have hSP := W1p.setLAverage_rpow_enorm_value_sub_setAverage_le_of_ball_subset hq hqp₀ ht
    hball hqs hδ hδn u
  have hs' : ((s : ℝ≥0∞)).toReal = s := ENNReal.coe_toReal s
  have hle : μ.restrict B ≤ μ.restrict (Ω : Set E) := Measure.restrict_mono hball le_rfl
  rw [← hs', setLAverage_rpow_rpow_inv_eq
      (f := fun x => W1p.value u x - ⨍ y in B, W1p.value u y ∂μ)
      (((Lp.aestronglyMeasurable _).mono_measure hle).sub aestronglyMeasurable_const) hs0
      ENNReal.coe_ne_top,
    setLAverage_rpow_rpow_inv_eq ((Lp.aestronglyMeasurable _).mono_measure hle) hq0 hq, hs'] at hSP
  -- Multiply by `μ(B)^(1/s)`.
  have hcancel : μ B ^ (s : ℝ)⁻¹ * μ B ^ (-(s : ℝ)⁻¹) = 1 := by
    rw [← ENNReal.rpow_add _ _ hB0 hBt, add_neg_cancel, ENNReal.rpow_zero]
  calc eLpNorm (fun x => W1p.value u x - ⨍ y in B, W1p.value u y ∂μ) s (μ.restrict B)
      = μ B ^ (s : ℝ)⁻¹ * (μ B ^ (-(s : ℝ)⁻¹) *
          eLpNorm (fun x => W1p.value u x - ⨍ y in B, W1p.value u y ∂μ) s (μ.restrict B)) := by
        rw [← mul_assoc, hcancel, one_mul]
    _ ≤ μ B ^ (s : ℝ)⁻¹ * (K * (μ B ^ (-q.toReal⁻¹) *
          eLpNorm (W1p.gradient u) q (μ.restrict B))) := by gcongr
    _ = K * (μ B ^ ((s : ℝ)⁻¹ + -q.toReal⁻¹)) * eLpNorm (W1p.gradient u) q (μ.restrict B) := by
        rw [ENNReal.rpow_add _ _ hB0 hBt]
        ring
    _ = _ := by rw [← hδ]; ring_nf

/-- The Sobolev–Poincaré inequality on a ball for test functions, in norms. -/
private theorem eLpNorm_sub_setAverage_le_of_testFunction {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hq : q ≠ ⊤) {s : ℝ≥0} (hqs : q ≤ s) {δ : ℝ} (hδ : q.toReal⁻¹ - (s : ℝ)⁻¹ = δ)
    (hδn : δ < (finrank ℝ E : ℝ)⁻¹) {x₀ : E} {t : ℝ} (ht : 0 < t)
    (φ : 𝓓((⊤ : Opens E), ℝ)) :
    eLpNorm (fun x => (φ : E → ℝ) x - ⨍ y in ball x₀ t, (φ : E → ℝ) y ∂μ) s
        (μ.restrict (ball x₀ t)) ≤
      ENNReal.ofReal (2 ^ finrank ℝ E / finrank ℝ E *
          ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ) * t) *
        μ (ball x₀ t) ^ (-δ) * eLpNorm (∇ (φ : E → ℝ)) q (μ.restrict (ball x₀ t)) := by
  set v := W1p.ofTestFunctionₗ μ ⊤ q φ
  have hv : W1p.value v =ᵐ[μ] (φ : E → ℝ) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using W1p.value_ofTestFunctionₗ_ae (p := q) φ
  have hg : W1p.gradient v =ᵐ[μ] ∇ (φ : E → ℝ) := by
    have h := gradientTestFunctionLp_apply_ae (mu := μ) q φ
    simp only [Opens.coe_top, Measure.restrict_univ] at h
    filter_upwards [h] with x hx
    rw [W1p.gradient_ofTestFunctionₗ, hx]
  have h := W1p.eLpNorm_value_sub_setAverage_le_of_ball_subset (μ := μ) (x₀ := x₀) hq le_rfl hqs
    hδ hδn ht (by simp) v
  have havg : ⨍ y in ball x₀ t, W1p.value v y ∂μ = ⨍ y in ball x₀ t, (φ : E → ℝ) y ∂μ :=
    average_congr (ae_restrict_of_ae hv)
  have h1 : (fun x => W1p.value v x - ⨍ y in ball x₀ t, W1p.value v y ∂μ) =ᵐ[μ]
      fun x => (φ : E → ℝ) x - ⨍ y in ball x₀ t, (φ : E → ℝ) y ∂μ :=
    hv.mono fun x hx => by simp only [hx, havg]
  rwa [eLpNorm_congr_ae (ae_restrict_of_ae h1), eLpNorm_congr_ae (ae_restrict_of_ae hg)] at h

/-- Exponent bookkeeping for the conjugate exponents of `1 < r ≤ p < ∞`. -/
private theorem conjExponent_facts {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)] (hr : 1 < r)
    (hrp : r ≤ p) (hp : p ≠ ⊤) :
    1 < p.conjExponent ∧ p.conjExponent ≠ ⊤ ∧ r.conjExponent ≠ ⊤ ∧
      p.conjExponent ≤ r.conjExponent ∧
      p.conjExponent.toReal⁻¹ - r.conjExponent.toReal⁻¹ = r.toReal⁻¹ - p.toReal⁻¹ := by
  have hp1 : 1 < p := hr.trans_le hrp
  have hpq : p.conjExponent ≠ ⊤ := by
    rw [ENNReal.conjExponent, Ne, ENNReal.add_eq_top, not_or, ENNReal.inv_eq_top,
      tsub_eq_zero_iff_le]
    exact ⟨ENNReal.one_ne_top, not_le.2 hp1⟩
  have hrs : r.conjExponent ≠ ⊤ := by
    rw [ENNReal.conjExponent, Ne, ENNReal.add_eq_top, not_or, ENNReal.inv_eq_top,
      tsub_eq_zero_iff_le]
    exact ⟨ENNReal.one_ne_top, not_le.2 hr⟩
  have hr_top : r ≠ ⊤ := ne_top_of_le_ne_top hp hrp
  have hP := ENNReal.HolderConjugate.toReal_of_ne_top hp hpq (p := p) (q := p.conjExponent)
  have hR := ENNReal.HolderConjugate.toReal_of_ne_top hr_top hrs (p := r) (q := r.conjExponent)
  refine ⟨?_, hpq, hrs, ?_, ?_⟩
  · rw [ENNReal.conjExponent]
    exact ENNReal.lt_add_right ENNReal.one_ne_top
      (ENNReal.inv_ne_zero.2 (ENNReal.sub_ne_top hp))
  · rw [ENNReal.conjExponent, ENNReal.conjExponent]
    gcongr
  · have h1 := hP.inv_add_inv_eq_one
    have h2 := hR.inv_add_inv_eq_one
    linarith

/-- The pairing of a mean-zero `h ∈ Lʳ` supported in a ball `B = B(x₀, t)` with a test function
`φ` is bounded by `K t μ(B)^(-δ) ‖h‖_{Lʳ} ‖∇φ‖_{L^q}`, `q` the exponent conjugate to `p`. This is
the Sobolev–Poincaré inequality for `φ` on `B` read through Hölder's inequality. -/
private theorem abs_integral_mul_le_of_integral_eq_zero {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (hr : 1 < r) (hrp : r ≤ p) (hp : p ≠ ⊤) {δ : ℝ} (hδ : r.toReal⁻¹ - p.toReal⁻¹ = δ)
    (hδn : δ < (finrank ℝ E : ℝ)⁻¹) {x₀ : E} {t : ℝ} (ht : 0 < t) {h : E → ℝ}
    (hh : MemLp h r μ) (hsupp : ∀ᵐ x ∂μ, x ∉ ball x₀ t → h x = 0) (hmean : ∫ x, h x ∂μ = 0)
    (φ : 𝓓((⊤ : Opens E), ℝ)) :
    |∫ x, h x * (φ : E → ℝ) x ∂μ| ≤
      (ENNReal.ofReal (2 ^ finrank ℝ E / finrank ℝ E *
          ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ) * t) *
        μ (ball x₀ t) ^ (-δ) * eLpNorm h r μ).toReal *
      (eLpNorm (∇ (φ : E → ℝ)) p.conjExponent μ).toReal := by
  obtain ⟨hq1, hq_top, hs_top, hqs, hqsδ⟩ := conjExponent_facts hr hrp hp
  set q := p.conjExponent
  set s := r.conjExponent
  set K : ℝ := 2 ^ finrank ℝ E / finrank ℝ E * ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ)
  set B := ball x₀ t
  have hB0 : μ B ≠ 0 := (measure_ball_pos μ x₀ ht).ne'
  have hBt : μ B ≠ ⊤ := measure_ball_lt_top.ne
  have : IsFiniteMeasure (μ.restrict B) := isFiniteMeasure_restrict.2 hBt
  have hr1 : (1 : ℝ≥0∞) ≤ r := Fact.out
  have hsN : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) = s := ENNReal.coe_toNNReal hs_top
  have hδ' : q.toReal⁻¹ - ((s.toNNReal : ℝ≥0) : ℝ)⁻¹ = δ := by
    rw [← hδ, ← hqsδ, ENNReal.coe_toNNReal_eq_toReal]
  have hs : s.HolderConjugate r := inferInstance
  have : Fact (1 ≤ q) := ⟨hq1.le⟩
  set c := ⨍ y in B, (φ : E → ℝ) y ∂μ
  -- Sobolev–Poincaré for `φ` on `B`.
  have hSP := eLpNorm_sub_setAverage_le_of_testFunction (μ := μ) hq_top
    (by rw [hsN]; exact hqs) hδ' hδn (x₀ := x₀) ht φ
  rw [hsN] at hSP
  have hgrad : eLpNorm (∇ (φ : E → ℝ)) q μ ≠ ⊤ :=
    (φ.hasCompactSupport.memLp_gradient (φ.contDiff.of_le (by simp))).eLpNorm_ne_top
  have hφs : MemLp (fun x => (φ : E → ℝ) x - c) s (μ.restrict B) :=
    hSP.trans_lt (by
      refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_) ?_
      · exact (ENNReal.rpow_ne_top_of_ne_zero hB0 hBt).lt_top
      · exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans_lt hgrad.lt_top)
  have hhB : MemLp h r (μ.restrict B) := hh.restrict B
  have hint1 : Integrable (fun x => ((φ : E → ℝ) x - c) * h x) (μ.restrict B) :=
    hφs.integrable_mul hhB
  have heq := integral_mul_eq_setIntegral_sub_smul (hhB.integrable hr1) hsupp hmean c hint1
  have hHolder := enorm_integral_smul_le (μ := μ.restrict B) (p := s) (q := r)
    (a := fun x => (φ : E → ℝ) x - c) (f := h)
  have hfin : ENNReal.ofReal (K * t) * μ B ^ (-δ) * eLpNorm h r μ ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_) hh.eLpNorm_ne_top
    exact ENNReal.rpow_ne_top_of_ne_zero hB0 hBt
  rw [heq, ← Real.norm_eq_abs, ← toReal_eNorm, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top hfin hgrad) (hHolder.trans ?_)
  calc eLpNorm (fun x => (φ : E → ℝ) x - c) s (μ.restrict B) * eLpNorm h r (μ.restrict B)
      ≤ ENNReal.ofReal (K * t) * μ B ^ (-δ) *
          eLpNorm (∇ (φ : E → ℝ)) q (μ.restrict B) * eLpNorm h r μ :=
        mul_le_mul' hSP (eLpNorm_mono_measure _ Measure.restrict_le_self)
    _ ≤ ENNReal.ofReal (K * t) * μ B ^ (-δ) * eLpNorm (∇ (φ : E → ℝ)) q μ * eLpNorm h r μ := by
        gcongr
        exact Measure.restrict_le_self
    _ = _ := by ring

/-- **Mean-zero functions on a ball are divergences.** Let `n ≥ 1` be the dimension, let
`1 < r ≤ p < ∞` with `δ = 1/r - 1/p < 1/n`. There is a constant `C`, depending only on `n`, `r`
and `p`, such that every `h ∈ Lʳ(ℝⁿ)` vanishing off a ball `B = B(x₀, t)` with `∫ h = 0` is the
divergence of a field `H ∈ Lᵖ(ℝⁿ; ℝⁿ)`, in the sense that

`∫ h φ = ∫ ⟪H, ∇φ⟫` for every test function `φ`, with `‖H‖_{Lᵖ} ≤ C t μ(B)^(-δ) ‖h‖_{Lʳ}`.

So `-div H = h` in the sense of distributions. The factor `t μ(B)^(-δ)` is the scaling of the
estimate: it is `t` when `p = r`, and for `p > r` the field gains integrability. Some condition on
the mean is needed: a nonzero constant times the indicator of `B` is no divergence of an `Lᵖ`
field once `p ≤ n / (n - 1)`. -/
theorem exists_memLp_forall_integral_mul_eq_integral_inner_gradient_of_integral_eq_zero
    {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)] (hr : 1 < r) (hrp : r ≤ p) (hp : p ≠ ⊤) {δ : ℝ}
    (hδ : r.toReal⁻¹ - p.toReal⁻¹ = δ) (hδn : δ < (finrank ℝ E : ℝ)⁻¹) :
    ∃ C : ℝ≥0, ∀ {x₀ : E} {t : ℝ}, 0 < t → ∀ {h : E → ℝ}, MemLp h r μ →
      (∀ᵐ x ∂μ, x ∉ ball x₀ t → h x = 0) → ∫ x, h x ∂μ = 0 →
      ∃ H : E → E, MemLp H p μ ∧
        eLpNorm H p μ ≤ C * ENNReal.ofReal t * μ (ball x₀ t) ^ (-δ) * eLpNorm h r μ ∧
        ∀ φ : 𝓓((⊤ : Opens E), ℝ), ∫ x, h x * φ x ∂μ = ∫ x, ⟪H x, ∇ (φ : E → ℝ) x⟫_ℝ ∂μ := by
  obtain ⟨hq1, hq_top, -, -, -⟩ := conjExponent_facts hr hrp hp
  set q := p.conjExponent
  set K : ℝ := 2 ^ finrank ℝ E / finrank ℝ E * ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ)
  refine ⟨(finrank ℝ E : ℝ≥0) ^ 2 * K.toNNReal, fun {x₀ t} ht {h} hh hsupp hmean => ?_⟩
  have hK : 0 ≤ K := by
    have hn : (1 : ℝ) ≤ finrank ℝ E := by exact_mod_cast finrank_pos
    have hδ1 : δ < 1 := hδn.trans_le (inv_le_one_of_one_le₀ hn)
    exact mul_nonneg (by positivity)
      (Real.rpow_nonneg (div_nonneg (by linarith) (sub_nonneg.2 hδn.le)) _)
  have hfin : ENNReal.ofReal (K * t) * μ (ball x₀ t) ^ (-δ) * eLpNorm h r μ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_ne_zero
      (measure_ball_pos μ x₀ ht).ne' measure_ball_lt_top.ne)) hh.eLpNorm_ne_top
  have : Fact (1 ≤ q) := ⟨hq1.le⟩
  -- The pairing with `h` is bounded by the `L^q` norm of the gradient.
  set M : ℝ := (ENNReal.ofReal (K * t) * μ (ball x₀ t) ^ (-δ) * eLpNorm h r μ).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hloc : LocallyIntegrableOn h (⊤ : Opens E) μ :=
    (hh.locallyIntegrable Fact.out).locallyIntegrableOn _
  let ℓ : 𝓓((⊤ : Opens E), ℝ) →ₗ[ℝ] ℝ :=
    (TestFunction.integralAgainstBilinCLM (n := ⊤) (ContinuousLinearMap.mul ℝ ℝ) μ h).toLinearMap
  have hℓ (φ : 𝓓((⊤ : Opens E), ℝ)) : ℓ φ = ∫ x, h x * (φ : E → ℝ) x ∂μ := by
    simp only [ℓ, ContinuousLinearMap.coe_coe,
      TestFunction.integralAgainstBilinCLM_eq_integral hloc, ContinuousLinearMap.mul_apply',
      mul_comm]
  have hbound (φ : 𝓓((⊤ : Opens E), ℝ)) :
      |ℓ φ| ≤ M * (eLpNorm (∇ (φ : E → ℝ)) q μ).toReal := by
    rw [hℓ]
    exact abs_integral_mul_le_of_integral_eq_zero hr hrp hp hδ hδn ht hh hsupp hmean φ
  obtain ⟨H, hH, hHnorm, hHφ⟩ := exists_memLp_forall_eq_integral_inner_gradient_of_abs_le
    (μ := μ) (p := p) hq1 hq_top ℓ hM hbound
  simp only [Opens.coe_top, Measure.restrict_univ] at hH hHnorm hHφ
  refine ⟨H, hH, hHnorm.trans (le_of_eq ?_), fun φ => (hℓ φ).symm.trans (hHφ φ)⟩
  rw [ENNReal.ofReal_toReal hfin, ENNReal.ofReal_mul hK, ENNReal.coe_mul,
    ENNReal.coe_pow, ENNReal.coe_natCast, ENNReal.ofNNReal_toNNReal]
  ring

end Ball

end TauCeti
