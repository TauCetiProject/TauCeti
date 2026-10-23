/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.Matrix.Contraction
public import TauCeti.Analysis.Normed.Module.Trace
public import TauCeti.Analysis.PDE.Regularity.Hessian.ConstantCoefficient
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.Calculus.Morse.Linearization
import TauCeti.Analysis.PDE.Ellipticity.Basic
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Analysis.Sobolev.Wkp.Density
import TauCeti.Analysis.Sobolev.Wkp.Laplacian

/-!
# The Calderón–Zygmund estimate for strong solutions in `W^{2,p}(ℝⁿ)`

For every dimension `n` and `1 < p < ∞`, this file proves the `W^{2,p}` estimate of the Hessian on
the whole
space for constant-coefficient operators, and in particular for the Laplacian. Here `D²u` is the
highest recorded weak derivative `TauCeti.Wkp.iteratedGradient 1 u`, the weak Hessian as an `Lᵖ`
field of endomorphisms of `ℝⁿ` with the operator norm, so that `⟪D²u(x) eᵢ, eⱼ⟫` is the weak
second derivative `∂ᵢ∂ⱼu`.

* **Constant coefficients**
  (`TauCeti.exists_norm_iteratedGradient_le_mul_norm_of_sum_mul_inner_eq`). There is a constant
  `C`, depending only on `n` and `p`, such that for every matrix `A` with `λ ‖ξ‖² ≤ ξᵀ A ξ` and
  `0 < λ`, every `u ∈ W^{2,p}(ℝⁿ)` with `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = f ∈ Lᵖ(ℝⁿ)` almost everywhere satisfies
  `‖D²u‖_{Lᵖ} ≤ (C / λ) ‖f‖_{Lᵖ}`.
* **The Laplacian**. There is a constant `C`, depending only on `n` and `p`, such that
  `‖D²u‖_{Lᵖ} ≤ C ‖f‖_{Lᵖ}` for every `u ∈ W^{2,p}(ℝⁿ)` and `f ∈ Lᵖ(ℝⁿ)` with `Δu = f`. The
  equation `Δu = f` is taken either strongly, the trace of the weak Hessian of `u` being `f` in
  `Lᵖ` (`TauCeti.exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq`), or against
  test functions, `∫ Δφ • u = ∫ φ • f` for every `φ ∈ C_c^∞(ℝⁿ)`
  (`TauCeti.exists_norm_iteratedGradient_le_mul_norm_of_integral_laplacian_smul_eq`); the two
  agree by `TauCeti.Wkp.forall_integral_laplacian_smul_value_eq_iff`.

## The argument

For Schwartz functions the constant-coefficient estimate is
`TauCeti.PDE.exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_sum_smul_fderiv_fderiv_real`, the
singular integral estimate for the Hessian, and test functions are Schwartz functions. Both sides
of the estimate are continuous on `W^{2,p}(ℝⁿ)`: `D²u` is a continuous projection, and
`D²u ↦ ∑ᵢⱼ Aᵢⱼ ⟪D²u eᵢ, eⱼ⟫` is the continuous linear functional `Matrix.contraction A`
applied pointwise. Test functions are dense in `W^{2,p}(ℝⁿ)` for `p < ∞`
(`TauCeti.Wkp.denseRange_ofTestFunctionₗ_top`), so the estimate holds on all of `W^{2,p}(ℝⁿ)`.
The Laplacian is the case `A = 1`, `λ = 1`: contracting with the identity matrix is the trace
(`Matrix.contraction_one`).

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
  rw [smul_eq_mul, iteratedGradientChain_succ, iteratedGradientChain_zero, fderiv_gradient,
    inner_hessianOperator_left]

/-- An `Lᵖ` bound on the classical Hessian of a test function `φ` bounds the weak Hessian of `φ`,
regarded as an element of `W^{2,p}(ℝⁿ)`. -/
private theorem norm_iteratedGradient_ofTestFunctionₗ_le {c : ℝ} (hc : 0 ≤ c)
    {L : EuclideanSpace ℝ (Fin n) → ℝ} (hL : eLpNorm L p volume ≠ ∞)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (h : eLpNorm (iteratedFDeriv ℝ 2 (φ : EuclideanSpace ℝ (Fin n) → ℝ)) p volume ≤
      ENNReal.ofReal c * eLpNorm L p volume) :
    ‖Wkp.iteratedGradient 1 (Wkp.ofTestFunctionₗ (mu := volume) (p := p) 2 φ)‖ ≤
      c * lpNorm L p volume := by
  have hφ : ContDiff ℝ 2 (φ : EuclideanSpace ℝ (Fin n) → ℝ) := φ.contDiff.of_le (by simp)
  rw [Wkp.norm_iteratedGradient_eq_lpNorm_of_contDiffOn 1 _ hφ.contDiffOn
    (by rw [Wkp.value_ofTestFunctionₗ]; exact testFunctionLp_apply_ae p φ), Opens.coe_top,
    Measure.restrict_univ]
  calc lpNorm (iteratedFDeriv ℝ (1 + 1) (φ : EuclideanSpace ℝ (Fin n) → ℝ)) p volume
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
    rw [Lp.norm_def, eLpNorm_congr_ae hae, hvol, lpNorm]
  rw [hTH]
  exact norm_iteratedGradient_ofTestFunctionₗ_le (by positivity) hLfin φ h

/-- **The Calderón–Zygmund estimate for strong solutions in `W^{2,p}(ℝⁿ)`.** Let `1 < p < ∞`, in
any dimension `n`. There is a constant `C` such that every `u ∈ W^{2,p}(ℝⁿ)` solving `Δu = f` with
`f ∈ Lᵖ(ℝⁿ)` strongly, in the sense that the trace of the weak Hessian of `u` is `f` in `Lᵖ`,
satisfies

`‖D²u‖_{Lᵖ} ≤ C ‖f‖_{Lᵖ}`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`, with the operator norm on
endomorphisms of `ℝⁿ`. -/
theorem exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin n))) ⊤ p 2)
      (f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
        (⊤ : Opens (EuclideanSpace ℝ (Fin n))))),
      (traceCLM ℝ (EuclideanSpace ℝ (Fin n))).compLpL p _ (Wkp.iteratedGradient 1 u) = f →
      ‖Wkp.iteratedGradient 1 u‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedGradient_le_mul_norm_of_sum_mul_inner_eq hp hp_top
  refine ⟨C, fun u f hf => ?_⟩
  -- The Laplacian has the identity matrix as constant coefficients, and contracting with the
  -- identity matrix is the trace.
  rw [← Matrix.contraction_one] at hf
  have htop :
      MeasurableSet ((⊤ : Opens (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n))) :=
    (⊤ : Opens (EuclideanSpace ℝ (Fin n))).isOpen.measurableSet
  have h := hC one_pos (fun ξ => (one_mul _).trans_le (PDE.toQuadraticForm'_one ξ).ge) u f (by
    filter_upwards [(ae_restrict_iff' htop).1
      ((Matrix.contraction 1).coeFn_compLpL (Wkp.iteratedGradient 1 u))] with x hx
    rw [← hf, hx (by simp), Matrix.contraction_apply])
  rwa [div_one] at h

/-- **The Calderón–Zygmund estimate in `W^{2,p}(ℝⁿ)`, against test functions.** Let `1 < p < ∞`,
in any dimension `n`. There is a constant `C` such that every `u ∈ W^{2,p}(ℝⁿ)` solving `Δu = f`
with
`f ∈ Lᵖ(ℝⁿ)`, in the sense that `∫ Δφ • u = ∫ φ • f` for every test function `φ`, satisfies

`‖D²u‖_{Lᵖ} ≤ C ‖f‖_{Lᵖ}`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`, with the operator norm on
endomorphisms of `ℝⁿ`. -/
theorem exists_norm_iteratedGradient_le_mul_norm_of_integral_laplacian_smul_eq
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin n))) ⊤ p 2)
      (f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
        (⊤ : Opens (EuclideanSpace ℝ (Fin n))))),
      (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
        ∫ x, Δ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x • Wkp.value 2 u x = ∫ x, φ x • f x) →
      ‖Wkp.iteratedGradient 1 u‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq hp hp_top
  refine ⟨C, fun u f hf => hC u f ?_⟩
  -- A solution against test functions is a strong solution: the trace of its weak Hessian is `f`.
  have hloc : LocallyIntegrableOn (f : EuclideanSpace ℝ (Fin n) → ℝ) ⊤ volume :=
    (((Lp.memLp f).locallyIntegrable Fact.out).mono_measure
      (by rw [Opens.coe_top, Measure.restrict_univ])).locallyIntegrableOn _
  refine Lp.ext ?_
  filter_upwards [(traceCLM ℝ (EuclideanSpace ℝ (Fin n))).coeFn_compLpL
      (Wkp.iteratedGradient 1 u),
    (Wkp.forall_integral_laplacian_smul_value_eq_iff u hloc).1 hf] with x hx htr
  rw [hx, traceCLM_apply, htr]

end TauCeti
