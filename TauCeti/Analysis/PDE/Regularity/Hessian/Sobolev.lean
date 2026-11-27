/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.Matrix.Contraction
public import TauCeti.Topology.Algebra.Module.Trace
public import TauCeti.Analysis.PDE.Regularity.Hessian.ConstantCoefficient
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Analysis.Sobolev.Wkp.Density
import TauCeti.Analysis.Sobolev.Wkp.Laplacian
import TauCeti.Analysis.Normed.Operator.MethodOfContinuity
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.Lp.Trace

/-!
# The Calderón–Zygmund estimate for strong solutions in `W^{2,p}` of the whole space

For `1 < p < ∞`, this file proves the `W^{2,p}` estimate of the Hessian on the whole space for
constant-coefficient operators on `ℝⁿ`, and for the Laplacian on every finite-dimensional real
inner product space `V`. Here `D²u` is the highest recorded weak derivative
`TauCeti.Wkp.iteratedGradient 1 u`, the weak Hessian as an `Lᵖ` field of endomorphisms with the
operator norm, so that `⟪D²u(x) eᵢ, eⱼ⟫` is the weak second derivative `∂ᵢ∂ⱼu`.

* **Constant coefficients**
  (`TauCeti.exists_norm_iteratedGradient_le_mul_norm_of_sum_mul_inner_eq`). There is a constant
  `C`, depending only on `n` and `p`, such that for every matrix `A` with `λ ‖ξ‖² ≤ ξᵀ A ξ` and
  `0 < λ`, every `u ∈ W^{2,p}(ℝⁿ)` with `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = f ∈ Lᵖ(ℝⁿ)` almost everywhere satisfies
  `‖D²u‖_{Lᵖ} ≤ (C / λ) ‖f‖_{Lᵖ}`.
* **The Laplacian**. There is a constant `C`, depending only on `V` and `p`, such that
  `‖D²u‖_{Lᵖ} ≤ C ‖f‖_{Lᵖ}` for every `u ∈ W^{2,p}(V)` and `f ∈ Lᵖ(V)` with `Δu = f`. The
  equation `Δu = f` is taken either strongly, the trace of the weak Hessian of `u` being `f` in
  `Lᵖ` (`TauCeti.exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq`), or against
  test functions, `∫ Δφ • u = ∫ φ • f` for every `φ ∈ C_c^∞(V)`
  (`TauCeti.exists_norm_iteratedGradient_le_mul_norm_of_integral_laplacian_smul_eq`); the two
  agree by `TauCeti.Wkp.forall_integral_laplacian_smul_value_eq_iff`. Stating this on a general
  `V` rather than on `ℝⁿ` lets it apply on products such as `ℝ × E`, where half-spaces are
  described.

On an open set `Ω ⊆ V`, a non-divergence-form operator `u ↦ tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u` with
bounded measurable coefficients is a bounded operator `W^{2,p}(Ω) → Lᵖ(Ω)`
(`TauCeti.exists_continuousLinearMap_traceCLM_comp_add_inner_add_mul`). For constant coefficients
`A` these operators depend continuously on `A`, so an a priori estimate
`‖x‖ ≤ C ‖tr (A ∘ D x)‖_{Lᵖ}` that holds for each `A` of a compact set holds with one constant for
all of them (`IsCompact.exists_forall_norm_le_mul_eLpNorm_of_traceCLM_comp`).

## The argument

For Schwartz functions the constant-coefficient estimate is
`TauCeti.PDE.exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_sum_smul_fderiv_fderiv_real` and the
estimate for the Laplacian is `TauCeti.exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_real`,
the singular integral estimates for the Hessian, and test functions are Schwartz functions. Both
sides of each estimate are continuous on `W^{2,p}`: `D²u` is a continuous projection, and
`D²u ↦ ∑ᵢⱼ Aᵢⱼ ⟪D²u eᵢ, eⱼ⟫` and `D²u ↦ tr D²u` are continuous linear functionals
(`Matrix.contraction A` and `traceCLM`) applied pointwise. For a test function `φ` the trace of
the Hessian is `Δφ` (`TauCeti.Wkp.trace_iteratedGradient_ofTestFunctionₗ_ae_eq`). Test functions
are dense in `W^{2,p}` of the whole space for `p < ∞`
(`TauCeti.Wkp.denseRange_ofTestFunctionₗ_top`), so the estimates hold on all of `W^{2,p}`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.9 and §9.4.
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter III,
  §1.3.
-/

public section

noncomputable section

namespace TauCeti

open Filter InnerProductSpace MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Laplacian Distributions SchwartzMap Topology

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The Hessian of a test function `φ`, regarded as an element of `W^{2,p}(ℝⁿ)`, contracted with a
matrix `A` is `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼφ` almost everywhere. -/
private theorem contraction_compLpL_iteratedGradient_ofTestFunctionₗ_ae_eq
    (A : Matrix (Fin n) (Fin n) ℝ) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    ((Matrix.contraction A).compLpL p _ (Wkp.iteratedGradient 1
      (Wkp.ofTestFunctionₗ (mu := volume) (p := p) 2 φ)) : EuclideanSpace ℝ (Fin n) → ℝ)
        =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
          ((⊤ : Opens (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)))]
      fun x => ∑ i, ∑ j, A i j • fderiv ℝ (fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ)) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  filter_upwards [(Matrix.contraction A).coeFn_compLpL (Wkp.iteratedGradient 1
      (Wkp.ofTestFunctionₗ (mu := volume) (p := p) 2 φ)),
    iteratedGradientTestFunctionLp_apply_ae (mu := volume) p 1 φ] with x hx hHx
  rw [hx, Matrix.contraction_apply, Wkp.iteratedGradient_ofTestFunctionₗ 1 φ, hHx,
    iteratedGradientTestFunction_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul, inner_iteratedGradientChain_one_apply]

/-- An `Lᵖ` bound on the classical Hessian of a test function `φ` bounds the weak Hessian of `φ`,
regarded as an element of `W^{2,p}(ℝⁿ)`. -/
private theorem norm_iteratedGradient_ofTestFunctionₗ_le {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {c : ℝ} (hc : 0 ≤ c) {L : V → ℝ} (hL : eLpNorm L p volume ≠ ∞) (φ : 𝓓((⊤ : Opens V), ℝ))
    (h : eLpNorm (iteratedFDeriv ℝ 2 (φ : V → ℝ)) p volume ≤
      ENNReal.ofReal c * eLpNorm L p volume) :
    ‖Wkp.iteratedGradient 1 (Wkp.ofTestFunctionₗ (mu := volume) (p := p) 2 φ)‖ ≤
      c * lpNorm L p volume := by
  have hφ : ContDiff ℝ 2 (φ : V → ℝ) := φ.contDiff.of_le (by simp)
  rw [Wkp.norm_iteratedGradient_eq_lpNorm_of_contDiffOn 1 _ hφ.contDiffOn
    (by rw [Wkp.value_ofTestFunctionₗ]; exact testFunctionLp_apply_ae p φ), Opens.coe_top,
    Measure.restrict_univ]
  calc lpNorm (iteratedFDeriv ℝ (1 + 1) (φ : V → ℝ)) p volume
      ≤ (ENNReal.ofReal c * eLpNorm L p volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL) h
    _ = c * lpNorm L p volume := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, lpNorm]

/-- **The Calderón–Zygmund estimate for constant coefficients in `W^{2,p}(ℝⁿ)`.** Let `1 < p < ∞`,
in any dimension `n`. There is a constant `C`, depending only on `n` and `p`, such that for every
matrix `A` with `λ ‖ξ‖² ≤ ξᵀ A ξ` and `0 < λ`, every `u ∈ W^{2,p}(ℝⁿ)` solving
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere, with `f ∈ Lᵖ(ℝⁿ)`, satisfies

`‖D²u‖_{Lᵖ} ≤ (C / λ) ‖f‖_{Lᵖ}`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`, with the operator norm on
endomorphisms of `ℝⁿ`. -/
theorem exists_norm_iteratedGradient_le_mul_norm_of_sum_mul_inner_eq
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ {A : Matrix (Fin n) (Fin n) ℝ} {lam : ℝ}, 0 < lam →
      (∀ ξ : EuclideanSpace ℝ (Fin n), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin n))) ⊤ p 2)
        (f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
          (⊤ : Opens (EuclideanSpace ℝ (Fin n))))),
        (∀ᵐ x, ∑ i, ∑ j, A i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
          EuclideanSpace.single j 1⟫_ℝ = f x) →
        ‖Wkp.iteratedGradient 1 u‖ ≤ C / lam * ‖f‖ := by
  obtain ⟨C, hC⟩ :=
    PDE.exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_sum_smul_fderiv_fderiv_real hp hp_top
  refine ⟨C, fun {A lam} hlam hA u f hf => ?_⟩
  set T := Matrix.contraction A
  have hvol : ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
      ((⊤ : Opens (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)))) = volume := by
    rw [Opens.coe_top, Measure.restrict_univ]
  -- The equation says that `f` is the contraction of the weak Hessian with `A`.
  have hTf : T.compLpL p _ (Wkp.iteratedGradient 1 u) = f := by
    refine Lp.ext ?_
    filter_upwards [T.coeFn_compLpL (Wkp.iteratedGradient 1 u), ae_restrict_of_ae hf]
      with x hx hfx
    rw [hx, Matrix.contraction_apply, hfx]
  rw [← hTf]
  -- Both sides are continuous on `W^{2,p}(ℝⁿ)`, so it suffices to treat test functions.
  refine (Wkp.denseRange_ofTestFunctionₗ_top hp_top 2).induction_on u
    (isClosed_le ?_ ?_) fun φ => ?_
  · simp only [← Wkp.iteratedGradientL_apply]
    exact (Wkp.iteratedGradientL 1).continuous.norm
  · simp only [← Wkp.iteratedGradientL_apply]
    exact continuous_const.mul ((T.compLpL p _).continuous.comp
      (Wkp.iteratedGradientL 1).continuous).norm
  -- For a test function, the right side is the norm of `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼφ`, and the estimate is the
  -- one for Schwartz functions.
  obtain ⟨L, hL⟩ : ∃ L : EuclideanSpace ℝ (Fin n) → ℝ, L = fun x => ∑ i, ∑ j, A i j •
    fderiv ℝ (fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ)) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := ⟨_, rfl⟩
  have hae := contraction_compLpL_iteratedGradient_ofTestFunctionₗ_ae_eq (p := p) A φ
  rw [← hL] at hae
  have hLfin : eLpNorm L p volume ≠ ∞ := by
    rw [← hvol, ← eLpNorm_congr_ae hae]
    exact Lp.eLpNorm_ne_top _
  have h : eLpNorm (iteratedFDeriv ℝ 2 (φ : EuclideanSpace ℝ (Fin n) → ℝ)) p volume ≤
      ENNReal.ofReal (C / lam) * eLpNorm L p volume := by
    have hcoe : ⇑(φ.hasCompactSupport.toSchwartzMap φ.contDiff) = φ :=
      funext (HasCompactSupport.toSchwartzMap_toFun _ _)
    have := hC hlam hA (φ.hasCompactSupport.toSchwartzMap φ.contDiff)
    rwa [hcoe, ← hL] at this
  have hTH : ‖T.compLpL p _ (Wkp.iteratedGradient 1
      (Wkp.ofTestFunctionₗ (mu := volume) (p := p) 2 φ))‖ = lpNorm L p volume := by
    rw [Lp.norm_eq_lpNorm_of_ae_eq hae, hvol]
  rw [hTH]
  exact norm_iteratedGradient_ofTestFunctionₗ_le (by positivity) hLfin φ h

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **The Calderón–Zygmund estimate for strong solutions in `W^{2,p}`.** Let `1 < p < ∞`, and let
`V` be a finite-dimensional real inner product space with its volume measure. There is a constant
`C` such that every `u ∈ W^{2,p}(V)` solving `Δu = f` with `f ∈ Lᵖ(V)` strongly, in the sense that
the trace of the weak Hessian of `u` is `f` in `Lᵖ`, satisfies

`‖D²u‖_{Lᵖ} ≤ C ‖f‖_{Lᵖ}`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`, with the operator norm on
endomorphisms of `V`. -/
theorem exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ (u : Wkp (volume : Measure V) ⊤ p 2)
      (f : Lp ℝ p ((volume : Measure V).restrict (⊤ : Opens V))),
      (traceCLM ℝ V).compLpL p _ (Wkp.iteratedGradient 1 u) = f →
      ‖Wkp.iteratedGradient 1 u‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_real (V := V) hp hp_top
  refine ⟨C, fun u f hf => ?_⟩
  subst hf
  set T := (traceCLM ℝ V).compLpL p ((volume : Measure V).restrict ((⊤ : Opens V) : Set V))
  -- Both sides are continuous on `W^{2,p}(V)`, so it suffices to treat test functions.
  refine (Wkp.denseRange_ofTestFunctionₗ_top hp_top 2).induction_on u
    (isClosed_le ?_ ?_) fun φ => ?_
  · simp only [← Wkp.iteratedGradientL_apply]
    exact (Wkp.iteratedGradientL 1).continuous.norm
  · simp only [← Wkp.iteratedGradientL_apply]
    exact continuous_const.mul (T.continuous.comp (Wkp.iteratedGradientL 1).continuous).norm
  -- For a test function, the right side is the norm of `Δφ`, and the estimate is the one for
  -- Schwartz functions.
  have hvol : (volume : Measure V).restrict ((⊤ : Opens V) : Set V) = volume := by
    rw [Opens.coe_top, Measure.restrict_univ]
  have hae : (T (Wkp.iteratedGradient 1 (Wkp.ofTestFunctionₗ (mu := volume) (p := p) 2 φ)) :
      V → ℝ) =ᵐ[(volume : Measure V).restrict ((⊤ : Opens V) : Set V)] Δ (φ : V → ℝ) := by
    filter_upwards [(traceCLM ℝ V).coeFn_compLpL (Wkp.iteratedGradient 1
        (Wkp.ofTestFunctionₗ (mu := volume) (p := p) 2 φ)),
      Wkp.trace_iteratedGradient_ofTestFunctionₗ_ae_eq (mu := volume) (p := p) φ] with x hx hΔ
    rw [hx, traceCLM_apply, hΔ]
  have hLfin : eLpNorm (Δ (φ : V → ℝ)) p volume ≠ ∞ := by
    rw [← hvol, ← eLpNorm_congr_ae hae]
    exact Lp.eLpNorm_ne_top _
  have h : eLpNorm (iteratedFDeriv ℝ 2 (φ : V → ℝ)) p volume ≤
      ENNReal.ofReal C * eLpNorm (Δ (φ : V → ℝ)) p volume := by
    set ψ := φ.hasCompactSupport.toSchwartzMap φ.contDiff
    have hcoe : ⇑ψ = φ := funext (HasCompactSupport.toSchwartzMap_toFun _ _)
    have hΔ : ⇑(Δ ψ : 𝓢(V, ℝ)) = Δ (φ : V → ℝ) := funext fun x => by
      rw [SchwartzMap.laplacian_apply, hcoe]
    rw [ENNReal.ofReal_coe_nnreal, ← hΔ, ← hcoe]
    exact hC ψ
  have hTH : ‖T (Wkp.iteratedGradient 1 (Wkp.ofTestFunctionₗ (mu := volume) (p := p) 2 φ))‖ =
      lpNorm (Δ (φ : V → ℝ)) p volume := by
    rw [Lp.norm_eq_lpNorm_of_ae_eq hae, hvol]
  rw [hTH]
  exact norm_iteratedGradient_ofTestFunctionₗ_le C.coe_nonneg hLfin φ h

/-- **The Calderón–Zygmund estimate in `W^{2,p}`, against test functions.** Let `1 < p < ∞`, and
let `V` be a finite-dimensional real inner product space with its volume measure. There is a
constant `C` such that every `u ∈ W^{2,p}(V)` solving `Δu = f` with `f ∈ Lᵖ(V)`, in the sense that
`∫ Δφ • u = ∫ φ • f` for every test function `φ`, satisfies

`‖D²u‖_{Lᵖ} ≤ C ‖f‖_{Lᵖ}`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`, with the operator norm on
endomorphisms of `V`. -/
theorem exists_norm_iteratedGradient_le_mul_norm_of_integral_laplacian_smul_eq
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ (u : Wkp (volume : Measure V) ⊤ p 2)
      (f : Lp ℝ p ((volume : Measure V).restrict (⊤ : Opens V))),
      (∀ φ : 𝓓((⊤ : Opens V), ℝ), ∫ x, Δ (φ : V → ℝ) x • Wkp.value 2 u x = ∫ x, φ x • f x) →
      ‖Wkp.iteratedGradient 1 u‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq (V := V) hp
    hp_top
  refine ⟨C, fun u f hf => hC u f ?_⟩
  -- A solution against test functions is a strong solution: the trace of its weak Hessian is `f`.
  have hloc : LocallyIntegrableOn (f : V → ℝ) ⊤ volume :=
    (((Lp.memLp f).locallyIntegrable Fact.out).mono_measure
      (by rw [Opens.coe_top, Measure.restrict_univ])).locallyIntegrableOn _
  refine Lp.ext ?_
  filter_upwards [(traceCLM ℝ V).coeFn_compLpL (Wkp.iteratedGradient 1 u),
    (Wkp.forall_integral_laplacian_smul_value_eq_iff u hloc).1 hf] with x hx htr
  rw [hx, traceCLM_apply, htr]

/-- **A non-divergence-form operator with bounded measurable coefficients is bounded on
`W^{2,p}`.** Let `A`, `b` and `c` be almost everywhere strongly measurable on `Ω`, with
`‖A x‖ ≤ Λ`, `‖b x‖ ≤ β` and `|c x| ≤ γ` almost everywhere. Then
`u ↦ tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u` is a continuous linear map `W^{2,p}(Ω) → Lᵖ(Ω)`. -/
theorem exists_continuousLinearMap_traceCLM_comp_add_inner_add_mul {μ : Measure V}
    [μ.IsAddHaarMeasure] {Omega : Opens V} {A : V → V →L[ℝ] V} {b : V → V} {c : V → ℝ}
    {Λ β γ : ℝ} (hA : AEStronglyMeasurable A (μ.restrict Omega))
    (hAΛ : ∀ᵐ x ∂μ.restrict Omega, ‖A x‖ ≤ Λ) (hb : AEStronglyMeasurable b (μ.restrict Omega))
    (hbβ : ∀ᵐ x ∂μ.restrict Omega, ‖b x‖ ≤ β) (hc : AEStronglyMeasurable c (μ.restrict Omega))
    (hcγ : ∀ᵐ x ∂μ.restrict Omega, |c x| ≤ γ) :
    ∃ T : Wkp μ Omega p 2 →L[ℝ] Lp ℝ p (μ.restrict Omega),
      ∀ u, ∀ᵐ x ∂μ.restrict Omega,
        T u x = traceCLM ℝ V (A x ∘L Wkp.iteratedGradient 1 u x) +
          ⟪b x, Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x⟫_ℝ + c x * Wkp.value 2 u x := by
  obtain ⟨T₁, hT₁⟩ := exists_continuousLinearMap_traceCLM_comp (p := p) hA hAΛ
  -- The lower-order terms are pointwise pairings with the `L^∞` classes of `b` and `c`.
  have hb' := memLp_top_of_bound hb β hbβ
  have hc' := memLp_top_of_bound hc γ (hcγ.mono fun x hx => by rwa [Real.norm_eq_abs])
  set B := (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).holderL (μ.restrict Omega) ∞ p p (hb'.toLp b)
  set M := (ContinuousLinearMap.mul ℝ ℝ).holderL (μ.restrict Omega) ∞ p p (hc'.toLp c)
  refine ⟨T₁.comp (Wkp.iteratedGradientL 1) +
    B.comp ((Wkp.iteratedGradientL 0).comp (Wkp.lowerOrderL 1)) + M.comp (Wkp.valueL 2),
    fun u => ?_⟩
  filter_upwards [Lp.coeFn_add (T₁ (Wkp.iteratedGradientL 1 u) +
      B (Wkp.iteratedGradientL 0 (Wkp.lowerOrderL 1 u))) (M (Wkp.valueL 2 u)),
    Lp.coeFn_add (T₁ (Wkp.iteratedGradientL 1 u))
      (B (Wkp.iteratedGradientL 0 (Wkp.lowerOrderL 1 u))),
    hT₁ (Wkp.iteratedGradientL 1 u),
    (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).coeFn_holder (r := p) (hb'.toLp b)
      (Wkp.iteratedGradientL 0 (Wkp.lowerOrderL 1 u)),
    (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := p) (hc'.toLp c) (Wkp.valueL 2 u),
    hb'.coeFn_toLp, hc'.coeFn_toLp] with x h1 h2 h3 h4 h5 h6 h7
  simp only [add_apply, ContinuousLinearMap.comp_apply, B, M,
    ContinuousLinearMap.holderL_apply_apply, Wkp.iteratedGradientL_apply 1 u,
    Wkp.lowerOrderL_apply 1 u, Wkp.iteratedGradientL_apply 0 (Wkp.lowerOrder 1 u),
    Wkp.valueL_apply 2 u] at h1 h2 h3 h4 h5 ⊢
  simp only [h1, Pi.add_apply, h2, h3, h4, h5, h6, h7, ContinuousLinearMap.mul_apply']
  rw [innerSL_apply_apply]

end InnerProductSpace

section UniformInCoefficients

variable {V X α : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace α] {μ : Measure α}

/-- **A priori estimates for trace operators are uniform on compact sets of coefficients.** Let
`D : X → Lᵖ(α; V →L V)` be a bounded operator, such as the weak Hessian on a Sobolev space, and let
`K` be a compact set of endomorphisms of `V`. If for each `A ∈ K` there is a constant `C` with
`‖x‖ ≤ C ‖tr (A ∘ D x)‖_{Lᵖ}` for every `x`, then one constant serves for every `A ∈ K`. In the
conclusion the datum enters as any function `g` equal to `tr (A ∘ D x)` almost everywhere. The
operators `x ↦ tr (A ∘ D x)` depend linearly, hence continuously, on `A`, so this is
`IsCompact.exists_forall_norm_le_mul_norm_apply`. -/
theorem _root_.IsCompact.exists_forall_norm_le_mul_eLpNorm_of_traceCLM_comp
    {K : Set (V →L[ℝ] V)} (hK : IsCompact K) (D : X →L[ℝ] Lp (IteratedGradient V 1) p μ)
    (hC : ∀ A ∈ K, ∃ C : ℝ, ∀ (x : X) (f : Lp ℝ p μ),
      (∀ᵐ y ∂μ, traceCLM ℝ V (A ∘L D x y) = f y) → ‖x‖ ≤ C * ‖f‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A ∈ K, ∀ (x : X) (g : α → ℝ),
      (∀ᵐ y ∂μ, traceCLM ℝ V (A ∘L D x y) = g y) → ‖x‖ ≤ C * (eLpNorm g p μ).toReal := by
  -- The pairing `(A, G) ↦ tr (A ∘ G)` and the operators `T A x = tr (A ∘ D x)`, linear in `A`.
  let B : (V →L[ℝ] V) →L[ℝ] IteratedGradient V 1 →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ (V →L[ℝ] V) (V →L[ℝ] V) ℝ (traceCLM ℝ V)).comp
      (ContinuousLinearMap.compL ℝ V V V)
  let T : (V →L[ℝ] V) → X →L[ℝ] Lp ℝ p μ := fun A => (B.compLpL₂ p μ A).comp D
  have hT : ∀ A x, T A x =ᵐ[μ] fun y => traceCLM ℝ V (A ∘L D x y) := fun A x => by
    filter_upwards [(B A).coeFn_compLp (D x)] with y hy
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compLpL₂_apply_apply, hy]
    rfl
  have hTc : Continuous T := (B.compLpL₂ p μ).continuous.clm_comp continuous_const
  have hnorm : ∀ A x g, (∀ᵐ y ∂μ, traceCLM ℝ V (A ∘L D x y) = g y) →
      ‖T A x‖ = (eLpNorm g p μ).toReal := fun A x g hg => by
    rw [Lp.norm_def, eLpNorm_congr_ae ((hT A x).trans hg)]
  obtain ⟨C, hC⟩ := hK.exists_forall_norm_le_mul_norm_apply hTc.continuousOn fun A hA => by
    obtain ⟨C, hC⟩ := hC A hA
    exact ⟨C, fun x => hC x (T A x) (hT A x).symm⟩
  refine ⟨max C 0, le_max_right _ _, fun A hA x g hg => ?_⟩
  refine (hC A hA x).trans ?_
  rw [hnorm A x g hg]
  gcongr
  exact le_max_left _ _

end UniformInCoefficients

end TauCeti
