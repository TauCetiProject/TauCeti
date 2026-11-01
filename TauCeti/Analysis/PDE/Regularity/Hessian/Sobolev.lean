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
import TauCeti.Analysis.Calculus.Morse.Linearization
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Trace
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Analysis.Sobolev.Wkp.Density
import TauCeti.Analysis.Sobolev.Wkp.Laplacian

/-!
# The Calderón–Zygmund estimate for strong solutions in `W^{2,p}(ℝⁿ)`

For every dimension `n` and `1 < p < ∞`, this file proves the `W^{2,p}` estimate of the Hessian on
the whole space for constant-coefficient operators, and in particular for the Laplacian. Here `D²u`
is the highest recorded weak derivative `TauCeti.Wkp.iteratedGradient 1 u`, the weak Hessian as an
`Lᵖ` field of endomorphisms of `ℝⁿ` with the operator norm, so that `⟪D²u(x) eᵢ, eⱼ⟫` is the weak
second derivative `∂ᵢ∂ⱼu`.

* **Constant coefficients**
  (`TauCeti.exists_norm_iteratedGradient_le_mul_norm_of_sum_mul_inner_eq`). There is a constant
  `C`, depending only on `n` and `p`, such that for every matrix `A` with `λ ‖ξ‖² ≤ ξᵀ A ξ` and
  `0 < λ`, every `u ∈ W^{2,p}(ℝⁿ)` with `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = f ∈ Lᵖ(ℝⁿ)` almost everywhere satisfies
  `‖D²u‖_{Lᵖ} ≤ (C / λ) ‖f‖_{Lᵖ}`.
* **The Laplacian**, on any finite-dimensional real inner product space `F` in place of `ℝⁿ`, so
  that it applies directly on products such as `ℝ × E`. There is a constant `C`, depending only on
  `F` and `p`, such that `‖D²u‖_{Lᵖ} ≤ C ‖f‖_{Lᵖ}` for every `u ∈ W^{2,p}(F)` and `f ∈ Lᵖ(F)` with
  `Δu = f`. The equation `Δu = f` is taken either strongly, the trace of the weak Hessian of `u`
  being `f` in `Lᵖ` (`TauCeti.exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq`),
  or against test functions, `∫ Δφ • u = ∫ φ • f` for every `φ ∈ C_c^∞(F)`
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

For the Laplacian on `F`, a linear isometry `F ≃ ℝⁿ` preserves the volume, the norms of second
derivatives and the Laplacian (`TauCeti.laplacian_comp_linearIsometryEquiv_right`), so the
Schwartz estimate `TauCeti.exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_real` on `ℝⁿ`
transfers to test functions on `F`. The trace of the weak Hessian of a test function is its
Laplacian (`TauCeti.laplacian_eq_trace_iteratedGradientChain_one`), and the same density argument
applies.

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
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

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
regarded as an element of `W^{2,p}(F)`. -/
private theorem norm_iteratedGradient_ofTestFunctionₗ_le {c : ℝ} (hc : 0 ≤ c)
    {L : F → ℝ} (hL : eLpNorm L p volume ≠ ∞)
    (φ : 𝓓((⊤ : Opens F), ℝ))
    (h : eLpNorm (iteratedFDeriv ℝ 2 (φ : F → ℝ)) p volume ≤
      ENNReal.ofReal c * eLpNorm L p volume) :
    ‖Wkp.iteratedGradient 1 (Wkp.ofTestFunctionₗ (mu := volume) (p := p) 2 φ)‖ ≤
      c * lpNorm L p volume := by
  have hφ : ContDiff ℝ 2 (φ : F → ℝ) := φ.contDiff.of_le (by simp)
  rw [Wkp.norm_iteratedGradient_eq_lpNorm_of_contDiffOn 1 _ hφ.contDiffOn
    (by rw [Wkp.value_ofTestFunctionₗ]; exact testFunctionLp_apply_ae p φ), Opens.coe_top,
    Measure.restrict_univ]
  calc lpNorm (iteratedFDeriv ℝ (1 + 1) (φ : F → ℝ)) p volume
      ≤ (ENNReal.ofReal c * eLpNorm L p volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL) h
    _ = c * lpNorm L p volume := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, lpNorm]

/-- An estimate `‖D²u‖ ≤ c ‖T(D²u)‖` for a continuous linear functional `T` of the Hessian passes
from test functions to all of `W^{2,p}(F)`: both sides are continuous on `W^{2,p}(F)`, and test
functions are dense in it for `p < ∞`. -/
private theorem norm_iteratedGradient_le_mul_norm_compLpL_of_forall_testFunction
    (hp_top : p ≠ ∞) (T : (F →L[ℝ] F) →L[ℝ] ℝ) {c : ℝ}
    (h : ∀ φ : 𝓓((⊤ : Opens F), ℝ),
      ‖Wkp.iteratedGradient 1 (Wkp.ofTestFunctionₗ (mu := volume) (p := p) 2 φ)‖ ≤
        c * ‖T.compLpL p _ (Wkp.iteratedGradient 1
          (Wkp.ofTestFunctionₗ (mu := volume) (p := p) 2 φ))‖)
    (u : Wkp (volume : Measure F) ⊤ p 2) :
    ‖Wkp.iteratedGradient 1 u‖ ≤ c * ‖T.compLpL p _ (Wkp.iteratedGradient 1 u)‖ := by
  refine (Wkp.denseRange_ofTestFunctionₗ_top hp_top 2).induction_on u
    (isClosed_le ?_ ?_) h
  · simp only [← Wkp.iteratedGradientL_apply]
    exact (Wkp.iteratedGradientL 1).continuous.norm
  · simp only [← Wkp.iteratedGradientL_apply]
    exact continuous_const.mul ((T.compLpL p _).continuous.comp
      (Wkp.iteratedGradientL 1).continuous).norm

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
  refine norm_iteratedGradient_le_mul_norm_compLpL_of_forall_testFunction hp_top T
    (fun φ => ?_) u
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

/-! ### The Laplacian on a finite-dimensional inner product space -/

omit [Fact (1 ≤ p)] in
/-- The Calderón–Zygmund estimate for the Laplacian of a test function on a finite-dimensional
real inner product space `F`, transported from `ℝⁿ` along a linear isometry `F ≃ ℝⁿ`, which
preserves the volume, the norms of second derivatives, and the Laplacian. -/
private theorem exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_testFunction
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ φ : 𝓓((⊤ : Opens F), ℝ),
      eLpNorm (iteratedFDeriv ℝ 2 (φ : F → ℝ)) p volume ≤
        ENNReal.ofReal C * eLpNorm (Δ (φ : F → ℝ)) p volume := by
  obtain ⟨C, hC⟩ :=
    exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_real (n := Module.finrank ℝ F) hp hp_top
  refine ⟨C, fun φ => ?_⟩
  set e := (stdOrthonormalBasis ℝ F).repr
  have he := e.measurePreserving
  -- `φ ∘ e⁻¹` is a test function on `ℝⁿ`, hence a Schwartz function.
  have hs := φ.contDiff.comp e.symm.contDiff
  have hc : HasCompactSupport ((φ : F → ℝ) ∘ e.symm) :=
    φ.hasCompactSupport.comp_homeomorph e.symm.toHomeomorph
  set ψ := hc.toSchwartzMap hs
  have hφ : (φ : F → ℝ) = ψ ∘ e := by
    ext x
    rw [Function.comp_apply, HasCompactSupport.toSchwartzMap_toFun, Function.comp_apply,
      LinearIsometryEquiv.symm_apply_apply]
  have h₁ : eLpNorm (iteratedFDeriv ℝ 2 (φ : F → ℝ)) p volume =
      eLpNorm (iteratedFDeriv ℝ 2 ⇑ψ) p volume := by
    rw [← eLpNorm_comp_measurePreserving
      ((ψ.smooth ⊤).continuous_iteratedFDeriv (by simp)).aestronglyMeasurable he]
    refine eLpNorm_congr_norm_ae
      ((φ.contDiff.continuous_iteratedFDeriv (by simp))).aestronglyMeasurable
      (((ψ.smooth ⊤).continuous_iteratedFDeriv (by simp)).comp e.continuous).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [hφ, Function.comp_apply]
    exact e.norm_iteratedFDeriv_comp_right _ x 2
  have h₂ : eLpNorm (Δ (φ : F → ℝ)) p volume =
      eLpNorm ⇑(Δ ψ : 𝓢(EuclideanSpace ℝ (Fin (Module.finrank ℝ F)), ℝ)) p volume := by
    rw [← eLpNorm_comp_measurePreserving
      (Δ ψ : 𝓢(EuclideanSpace ℝ (Fin (Module.finrank ℝ F)), ℝ)).continuous.aestronglyMeasurable he,
      hφ,
      laplacian_comp_linearIsometryEquiv_right]
    congr 1
    ext x
    rw [Function.comp_apply, Function.comp_apply, SchwartzMap.laplacian_apply]
  rw [h₁, h₂, ENNReal.ofReal_coe_nnreal]
  exact hC ψ

/-- **The Calderón–Zygmund estimate for strong solutions of `Δu = f` in `W^{2,p}`.** Let
`1 < p < ∞`, and let `F` be a finite-dimensional real inner product space, such as `ℝⁿ`. There is a
constant `C` such that every `u ∈ W^{2,p}(F)` solving `Δu = f` with `f ∈ Lᵖ(F)` strongly, in the
sense that the trace of the weak Hessian of `u` is `f` in `Lᵖ`, satisfies

`‖D²u‖_{Lᵖ} ≤ C ‖f‖_{Lᵖ}`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`, with the operator norm on
endomorphisms of `F`. -/
theorem exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ (u : Wkp (volume : Measure F) ⊤ p 2)
      (f : Lp ℝ p ((volume : Measure F).restrict (⊤ : Opens F))),
      (traceCLM ℝ F).compLpL p _ (Wkp.iteratedGradient 1 u) = f →
      ‖Wkp.iteratedGradient 1 u‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC⟩ :=
    exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_testFunction (F := F) hp hp_top
  refine ⟨C, fun u f hf => ?_⟩
  set T := traceCLM ℝ F
  rw [← hf]
  -- Both sides are continuous on `W^{2,p}(F)`, so it suffices to treat test functions.
  refine norm_iteratedGradient_le_mul_norm_compLpL_of_forall_testFunction hp_top T
    (fun φ => ?_) u
  -- For a test function, the trace of the weak Hessian is the classical Laplacian.
  have hae : (T.compLpL p _ (Wkp.iteratedGradient 1
      (Wkp.ofTestFunctionₗ (mu := volume) (p := p) 2 φ)) : F → ℝ)
        =ᵐ[(volume : Measure F).restrict ((⊤ : Opens F) : Set F)] Δ (φ : F → ℝ) := by
    filter_upwards [T.coeFn_compLpL (Wkp.iteratedGradient 1
        (Wkp.ofTestFunctionₗ (mu := volume) (p := p) 2 φ)),
      iteratedGradientTestFunctionLp_apply_ae (mu := volume) p 1 φ] with x hx hHx
    rw [hx, Wkp.iteratedGradient_ofTestFunctionₗ 1 φ, hHx, iteratedGradientTestFunction_def,
      traceCLM_apply, laplacian_eq_trace_iteratedGradientChain_one]
  have hvol : (volume : Measure F).restrict ((⊤ : Opens F) : Set F) = volume := by
    rw [Opens.coe_top, Measure.restrict_univ]
  have hLfin : eLpNorm (Δ (φ : F → ℝ)) p volume ≠ ∞ := by
    rw [← hvol, ← eLpNorm_congr_ae hae]
    exact Lp.eLpNorm_ne_top _
  have hTH : ‖T.compLpL p _ (Wkp.iteratedGradient 1
      (Wkp.ofTestFunctionₗ (mu := volume) (p := p) 2 φ))‖ = lpNorm (Δ (φ : F → ℝ)) p volume := by
    rw [Lp.norm_def, eLpNorm_congr_ae hae, hvol, lpNorm]
  rw [hTH]
  exact norm_iteratedGradient_ofTestFunctionₗ_le C.coe_nonneg hLfin φ (hC φ)

/-- **The Calderón–Zygmund estimate for `Δu = f` in `W^{2,p}`, against test functions.** Let
`1 < p < ∞`, and let `F` be a finite-dimensional real inner product space, such as `ℝⁿ`. There is a
constant `C` such that every `u ∈ W^{2,p}(F)` solving `Δu = f` with `f ∈ Lᵖ(F)`, in the sense that
`∫ Δφ • u = ∫ φ • f` for every test function `φ`, satisfies

`‖D²u‖_{Lᵖ} ≤ C ‖f‖_{Lᵖ}`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`, with the operator norm on
endomorphisms of `F`. -/
theorem exists_norm_iteratedGradient_le_mul_norm_of_integral_laplacian_smul_eq
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ (u : Wkp (volume : Measure F) ⊤ p 2)
      (f : Lp ℝ p ((volume : Measure F).restrict (⊤ : Opens F))),
      (∀ φ : 𝓓((⊤ : Opens F), ℝ),
        ∫ x, Δ (φ : F → ℝ) x • Wkp.value 2 u x = ∫ x, φ x • f x) →
      ‖Wkp.iteratedGradient 1 u‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC⟩ :=
    exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq (F := F) hp hp_top
  refine ⟨C, fun u f hf => hC u f ?_⟩
  -- A solution against test functions is a strong solution: the trace of its weak Hessian is `f`.
  have hloc : LocallyIntegrableOn (f : F → ℝ) ⊤ volume :=
    (((Lp.memLp f).locallyIntegrable Fact.out).mono_measure
      (by rw [Opens.coe_top, Measure.restrict_univ])).locallyIntegrableOn _
  refine Lp.ext ?_
  filter_upwards [(traceCLM ℝ F).coeFn_compLpL (Wkp.iteratedGradient 1 u),
    (Wkp.forall_integral_laplacian_smul_value_eq_iff u hloc).1 hf] with x hx htr
  rw [hx, traceCLM_apply, htr]

end TauCeti
