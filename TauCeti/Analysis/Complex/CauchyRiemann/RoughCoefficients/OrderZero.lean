/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Complex.Wirtinger.DivergenceLaplace
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.Local.Mollification
import TauCeti.Analysis.Sobolev.Local.Multiplication
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Data.ENNReal.Inv

/-!
# Order-zero interior regularity for Cauchy–Riemann equations with Sobolev coefficients

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a finite-dimensional real inner product
space. For `2 < p ≤ ∞`, an almost complex structure `J ∈ W^{1,p}_loc(Ω; V →L[ℝ] V)` satisfying
`J² = -1` almost everywhere on `Ω` with weak derivative `DJ`, and a zeroth-order coefficient
`S ∈ Lᵖ_loc(Ω; V →L[ℝ] V)`, consider a weak solution `ξ` of

`∂_s ξ + J ∂_t ξ + S ξ = η`

in the sense of `TauCeti.IsWeakCRSolution q Ω J DJ S ξ η`. This file proves interior regularity at
order zero (McDuff–Salamon, Lemma B.4.6):

1. *Reduction to the divergence-form Laplace equation*
   (`TauCeti.IsWeakCRSolution.integral_laplacian_smul_eq`). Whenever `1/p + 1/q ≤ 1`, for every
   real test function `ψ` on `Ω`, `Δ ξ = ∂_s f + ∂_t g` weakly on `Ω` with
   `f = η - S ξ + (∂_t J) ξ` and `g = -J η + J S ξ - (∂_s J) ξ`.
   The proof tests the weak equation against `(∂_s ψ) • v` and against the smooth test functions
   `-(∂_t ψ) • J_nᵀ v` obtained by mollifying `J` near `tsupport ψ`. Passing to the limit cancels
   the mixed second derivatives of `ψ` and uses `(∂_t J) J + J (∂_t J) = 0`, obtained by
   differentiating `J² = -1` weakly.
2. *Single Hölder step* (`TauCeti.IsWeakCRSolution.memWkpLoc_one_of_inv_add_inv_le`). If
   `1 < r < ∞`, `1/p + 1/q ≤ 1/r` and `η ∈ Lʳ_loc(Ω)`, then `f, g ∈ Lʳ_loc(Ω)`, so divergence-form
   Laplace regularity (`TauCeti.memWkpLoc_one_of_forall_integral_laplacian_smul_eq`) puts `ξ` in
   `W^{1,r}_loc(Ω)`.
3. *Bootstrap across the Sobolev exponent ladder*
   (`TauCeti.IsWeakCRSolution.memWkpLoc_one_of_memLpLoc`). If `1/p + 1/q < 1`, `1 < s ≤ p` with
   `s < ∞` and `η ∈ Lˢ_loc(Ω)`, alternating the single Hölder step with the two-dimensional Sobolev
   embedding decreases `1/q` by `1/2 - 1/p > 0` at each subcritical step until the product exponent
   exceeds `2`, where `W^{1,r}_loc ⊂ L^∞_loc` finishes in one more step and yields
   `ξ ∈ W^{1,s}_loc(Ω)`. The coefficient endpoint `p = ∞` is handled by lowering `p` locally to a
   finite exponent above `max 2 s`. In particular `ξ ∈ W^{1,q}_loc(Ω)` when `q ≤ p`, `q < ∞`, and
   `η ∈ L^q_loc(Ω)` (`TauCeti.IsWeakCRSolution.memWkpLoc_one_of_le`), and `ξ ∈ W^{1,p}_loc(Ω)` when
   `p < ∞` and `η ∈ Lᵖ_loc(Ω)` (`TauCeti.IsWeakCRSolution.memWkpLoc_one`).

The strict inequality `1/p + 1/q < 1`, that is `q > p / (p - 1)`, is sharp for the Sobolev
regularity step: at the conjugate exponent `1/p + 1/q = 1` the product exponent is `r = 1`, where
Calderón–Zygmund estimates for the Cauchy transform fail (`TauCeti.productExponent_conjugate`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Lemma B.4.4 and Lemma B.4.6).
-/

public noncomputable section

open Complex Filter Laplacian LineDeriv MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal InnerProductSpace NNReal Topology

namespace TauCeti

/-! ### Reduction to the divergence-form Laplace equation -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ} {p q r s : ℝ≥0∞}
  {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

namespace IsWeakCRSolution

/-- Testing `∂_s ξ + J ∂_t ξ + S ξ = η` against `(∂_s ψ) • v` gives the `∂_s² ψ` and mixed
`∂_s ∂_t ψ` terms of the divergence-form Laplace identity. -/
private theorem integral_test_lineDeriv_one (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η)
    (ψ : 𝓓(Ω, ℝ)) (v : V) :
    (-∫ z, (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} ψ) : 𝓓(Ω, ℝ)) z * ⟪v, ξ z⟫_ℝ) -
      (∫ z, (∂_{(1 : ℂ)} (∂_{(I : ℂ)} ψ) : 𝓓(Ω, ℝ)) z * ⟪v, J z (ξ z)⟫_ℝ) -
      (∫ z, (∂_{(1 : ℂ)} ψ : 𝓓(Ω, ℝ)) z * ⟪v, DJ z I (ξ z)⟫_ℝ) +
      (∫ z, (∂_{(1 : ℂ)} ψ : 𝓓(Ω, ℝ)) z * ⟪v, S z (ξ z)⟫_ℝ) =
      ∫ z, (∂_{(1 : ℂ)} ψ : 𝓓(Ω, ℝ)) z * ⟪v, η z⟫_ℝ := by
  let ψs : 𝓓(Ω, ℝ) := ∂_{(1 : ℂ)} ψ
  let L : ℝ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  let Φ₁ : 𝓓(Ω, V) := TestFunction.postcompCLM L ψs
  have hΦ₁_fderiv (u : ℂ) (z : ℂ) :
      fderiv ℝ (Φ₁ : ℂ → V) z u = (∂_{u} ψs : 𝓓(Ω, ℝ)) z • v := by
    dsimp only [Φ₁]
    rw [TestFunction.fderiv_postcompCLM, TestFunction.lineDerivOp_apply_eq_fderiv]
    simp [L]
  have hderiv (u : ℂ) (w : ℂ → V) :
      ∫ z, ⟪fderiv ℝ (Φ₁ : ℂ → V) z u, w z⟫_ℝ = ∫ z, (∂_{u} ψs : 𝓓(Ω, ℝ)) z * ⟪v, w z⟫_ℝ :=
    integral_congr_ae (.of_forall fun z => by
      dsimp only; rw [hΦ₁_fderiv u z, inner_smul_left, RCLike.conj_to_real])
  have hval (w : ℂ → V) :
      ∫ z, ⟪(Φ₁ : ℂ → V) z, w z⟫_ℝ = ∫ z, (ψs : ℂ → ℝ) z * ⟪v, w z⟫_ℝ :=
    integral_congr_ae (.of_forall fun z => by simp [Φ₁, L, inner_smul_left])
  have hmain := (hc.integral_inner_crFormalAdjoint_eq_sub_add hpq hsol.memLpLoc Φ₁).symm.trans
    (hsol.integral_inner_crFormalAdjoint Φ₁)
  rwa [hderiv 1 ξ, hderiv I, ← TestFunction.lineDerivOp_comm ψ 1 I, hval, hval, hval] at hmain

/-- Testing `∂_s ξ + J ∂_t ξ + S ξ = η` against `(∂_t ψ) • J_nᵀ v`, passing to the limit as the
mollifier radius tends to zero, and simplifying `J² = -1` and `(∂_t J) J + J (∂_t J) = 0` gives the
`∂_t² ψ` and mixed `∂_t ∂_s ψ` terms of the divergence-form Laplace identity. -/
private theorem integral_test_mollified_adjoint (hp : 2 < p) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hJ : MemWkpLoc p Ω 1 J) (hJi : MemLpLoc ∞ Ω J)
    (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hDJI : MemLpLoc p Ω (fun z => DJ z I))
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (ψ : 𝓓(Ω, ℝ)) (v : V) :
    (∫ z, (∂_{(1 : ℂ)} (∂_{(I : ℂ)} ψ) : 𝓓(Ω, ℝ)) z * ⟪v, J z (ξ z)⟫_ℝ) +
      (∫ z, (∂_{(I : ℂ)} ψ : 𝓓(Ω, ℝ)) z * ⟪v, DJ z 1 (ξ z)⟫_ℝ) -
      (∫ z, (∂_{(I : ℂ)} (∂_{(I : ℂ)} ψ) : 𝓓(Ω, ℝ)) z * ⟪v, ξ z⟫_ℝ) -
      (∫ z, (∂_{(I : ℂ)} ψ : 𝓓(Ω, ℝ)) z * ⟪v, J z (S z (ξ z))⟫_ℝ) =
      -∫ z, (∂_{(I : ℂ)} ψ : 𝓓(Ω, ℝ)) z * ⟪v, J z (η z)⟫_ℝ := by
  have hξq : MemLpLoc q Ω ξ := hsol.memLpLoc
  have hJξq : MemLpLoc q Ω (fun z => J z (ξ z)) := hJi.clm_apply hξq (by simp)
  have hloc := Ω.isOpen.isLocallyClosed
  let ψt : 𝓓(Ω, ℝ) := ∂_{(I : ℂ)} ψ
  obtain ⟨Ψ, hderiv, hval⟩ :=
    exists_testFunction_tendsto_integral_inner_of_hasWeakFDerivOn hp hpq hJ
      hc.hasWeakFDerivOn ψt v
  have hlim_lhs := (((hderiv 1 hξq).neg.sub (hderiv I hJξq)).sub
    (hval (hDJI.locallyIntegrableOn_clm_apply hξq hpq hloc))).add
      (hval (hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hξq hpq hloc))
  have hlhs_eq (n : ℕ) :=
    (hc.integral_inner_crFormalAdjoint_eq_sub_add hpq hξq (Ψ n)).symm.trans
      (hsol.integral_inner_crFormalAdjoint (Ψ n))
  have heq₂ := tendsto_nhds_unique (hlim_lhs.congr hlhs_eq) (hval hsol.locallyIntegrableOn)
  have hJJ_eq : ∫ z, (∂_{(I : ℂ)} ψt : 𝓓(Ω, ℝ)) z * ⟪v, J z (J z (ξ z))⟫_ℝ =
      -∫ z, (∂_{(I : ℂ)} ψt : 𝓓(Ω, ℝ)) z * ⟪v, ξ z⟫_ℝ := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [ae_imp_of_ae_restrict hJsq] with z hz
    by_cases hzΩ : z ∈ (Ω : Set ℂ)
    · have hJz : J z (J z (ξ z)) = -ξ z := by simpa using congr($(hz hzΩ) (ξ z))
      rw [hJz, inner_neg_right, mul_neg]
    · simp [image_eq_zero_of_notMem_tsupport
        fun h => hzΩ ((∂_{(I : ℂ)} ψt : 𝓓(Ω, ℝ)).tsupport_subset h)]
  have hDJI_cancel : (∫ z, (ψt : ℂ → ℝ) z * ⟪v, DJ z I (J z (ξ z))⟫_ℝ) +
      ∫ z, (ψt : ℂ → ℝ) z * ⟪v, J z (DJ z I (ξ z))⟫_ℝ = 0 := by
    have hiA := ψt.integrable_mul_inner (hDJI.locallyIntegrableOn_clm_apply hJξq hpq hloc) v
    have hiB := ψt.integrable_mul_inner
      (hJi.locallyIntegrableOn_clm_apply (hDJI.clm_apply (r := 1) hξq (by simpa using hpq))
        (by simp) hloc) v
    rw [← integral_add hiA hiB]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_imp_of_ae_restrict
      (hc.hasWeakFDerivOn.ae_apply_add_apply_eq_zero_of_comp_self_eq_const hp hJ hJsq)] with z hz
    simp only [Pi.zero_apply]
    by_cases hzΩ : z ∈ (Ω : Set ℂ)
    · rw [← mul_add, ← inner_add_right, hz hzΩ I (ξ z), inner_zero_right, mul_zero]
    · simp [image_eq_zero_of_notMem_tsupport fun h => hzΩ (ψt.tsupport_subset h)]
  linarith

omit [FiniteDimensional ℝ V] in
/-- Linearity helper splitting `∫ ⟪v, α • (w₁ - w₂ + w₃)⟫` into three scalar-test-function inner
integrals when `w₁, w₂, w₃ ∈ L^{r₀}_loc(Ω)`. -/
private theorem integral_inner_smul_sub_add {r₀ : ℝ≥0∞} (hr₀ : 1 ≤ r₀) (α : 𝓓(Ω, ℝ)) (v : V)
    {w₁ w₂ w₃ : ℂ → V} (h₁ : MemLpLoc r₀ Ω w₁) (h₂ : MemLpLoc r₀ Ω w₂) (h₃ : MemLpLoc r₀ Ω w₃) :
    ∫ z, ⟪v, (α : ℂ → ℝ) z • (w₁ z - w₂ z + w₃ z)⟫_ℝ =
      (∫ z, (α : ℂ → ℝ) z * ⟪v, w₁ z⟫_ℝ) - (∫ z, (α : ℂ → ℝ) z * ⟪v, w₂ z⟫_ℝ) +
        ∫ z, (α : ℂ → ℝ) z * ⟪v, w₃ z⟫_ℝ := by
  have hloc := Ω.isOpen.isLocallyClosed
  have mk {w : ℂ → V} (hw : MemLpLoc r₀ Ω w) :=
    α.integrable_mul_inner (hw.locallyIntegrableOn hr₀ hloc) v
  have h12 : Integrable (fun z =>
      (α : ℂ → ℝ) z * ⟪v, w₁ z⟫_ℝ - (α : ℂ → ℝ) z * ⟪v, w₂ z⟫_ℝ) := (mk h₁).sub (mk h₂)
  have hcongr : (fun z => ⟪v, (α : ℂ → ℝ) z • (w₁ z - w₂ z + w₃ z)⟫_ℝ) =
      fun z => ((α : ℂ → ℝ) z * ⟪v, w₁ z⟫_ℝ - (α : ℂ → ℝ) z * ⟪v, w₂ z⟫_ℝ) +
        (α : ℂ → ℝ) z * ⟪v, w₃ z⟫_ℝ := by
    ext z; simp only [inner_smul_right, inner_add_right, inner_sub_right]; ring
  rw [hcongr, integral_add h12 (mk h₃), integral_sub (mk h₁) (mk h₂)]

omit [FiniteDimensional ℝ V] in
/-- Splitting `∫ ⟪v, Δψ • ξ⟫` into `∂_s² ψ` and `∂_t² ψ` inner-product integrals. -/
private theorem integral_inner_laplacian_smul_eq (hξ_loc : LocallyIntegrableOn ξ Ω)
    (ψ : 𝓓(Ω, ℝ)) (v : V) :
    ∫ z, ⟪v, Δ (ψ : ℂ → ℝ) z • ξ z⟫_ℝ =
      (∫ z, (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} ψ) : 𝓓(Ω, ℝ)) z * ⟪v, ξ z⟫_ℝ) +
        ∫ z, (∂_{(I : ℂ)} (∂_{(I : ℂ)} ψ) : 𝓓(Ω, ℝ)) z * ⟪v, ξ z⟫_ℝ := by
  have hΔ_coe (z : ℂ) : Δ (ψ : ℂ → ℝ) z = (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} ψ) : 𝓓(Ω, ℝ)) z +
      (∂_{(I : ℂ)} (∂_{(I : ℂ)} ψ) : 𝓓(Ω, ℝ)) z := by
    rw [← TestFunction.laplacianCLM_apply]
    simp [laplacianCLM_eq_sum Complex.orthonormalBasisOneI, Fin.sum_univ_two]
  rw [← integral_add ((∂_{(1 : ℂ)} (∂_{(1 : ℂ)} ψ)).integrable_mul_inner hξ_loc v)
    ((∂_{(I : ℂ)} (∂_{(I : ℂ)} ψ)).integrable_mul_inner hξ_loc v)]
  exact integral_congr_ae (.of_forall fun z => by
    dsimp only; rw [hΔ_coe z, inner_smul_right, add_mul])

/-- Under `1/p + 1/q ≤ 1/r`, both right-hand sides `f = η - S ξ + (∂_t J) ξ` and
`g = -J η + J S ξ - (∂_s J) ξ` of the divergence-form Laplace equation belong to `Lʳ_loc(Ω)`. -/
private theorem memLpLoc_laplacian_rhs (hp : 2 < p) (hpqr : p⁻¹ + q⁻¹ ≤ r⁻¹)
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hS : MemLpLoc p Ω S) (hξ : MemLpLoc q Ω ξ) (hη : MemLpLoc r Ω η) :
    MemLpLoc r Ω (fun z => η z - S z (ξ z) + DJ z I (ξ z)) ∧
      MemLpLoc r Ω (fun z => -J z (η z) + J z (S z (ξ z)) - DJ z 1 (ξ z)) := by
  have hJi : MemLpLoc ∞ Ω J := hJ.memLpLoc_top hp
  have hDJp : MemLpLoc p Ω DJ := hJ.memLpLoc_of_hasWeakFDerivOn hDJ
  have hSξ := hS.clm_apply hξ hpqr
  have hDJIξ := (hDJp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)).clm_apply hξ hpqr
  have hDJ1ξ := (hDJp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) 1)).clm_apply hξ hpqr
  exact ⟨(hη.sub hSξ).add hDJIξ,
    ((hJi.clm_apply hη (by simp)).neg.add (hJi.clm_apply hSξ (by simp))).sub hDJ1ξ⟩

/-- **Reduction of the weak Cauchy–Riemann equation to divergence-form Laplace.** Let `2 < p ≤ ∞`
and `1/p + 1/q ≤ 1`, let `J ∈ W^{1,p}_loc(Ω)` satisfy `J² = -1` almost everywhere on `Ω` with weak
derivative `DJ`, let `S ∈ Lᵖ_loc(Ω)`, and let `ξ` solve `∂_s ξ + J ∂_t ξ + S ξ = η` weakly on `Ω`.
Then for every real test function `ψ` on `Ω`,

`∫ Δψ • ξ = -∫ (∂_s ψ • (η - S ξ + (∂_t J) ξ) + ∂_t ψ • (-J η + J S ξ - (∂_s J) ξ))`. -/
theorem integral_laplacian_smul_eq (hp : 2 < p) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hS : MemLpLoc p Ω S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (ψ : 𝓓(Ω, ℝ)) :
    ∫ z, Δ (ψ : ℂ → ℝ) z • ξ z =
      -∫ z, (fderiv ℝ (ψ : ℂ → ℝ) z 1 • (η z - S z (ξ z) + DJ z I (ξ z)) +
        fderiv ℝ (ψ : ℂ → ℝ) z I • (-J z (η z) + J z (S z (ξ z)) - DJ z 1 (ξ z))) := by
  have hloc := Ω.isOpen.isLocallyClosed
  have hpq1 : p⁻¹ + q⁻¹ ≤ (1 : ℝ≥0∞)⁻¹ := by simpa using hpq
  have hη1 : MemLpLoc 1 Ω η :=
    (memLpLoc_one_iff_locallyIntegrableOn hloc).2 hsol.locallyIntegrableOn
  have hJi : MemLpLoc ∞ Ω J := hJ.memLpLoc_top hp
  have hDJp : MemLpLoc p Ω DJ := hJ.memLpLoc_of_hasWeakFDerivOn hDJ
  have hc : IsSobolevCRCoefficients p Ω J DJ S := ⟨hDJ, hJ.memLpLoc, hDJp, hS⟩
  have hDJI : MemLpLoc p Ω (fun z => DJ z I) :=
    hDJp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)
  have hDJ1 : MemLpLoc p Ω (fun z => DJ z 1) :=
    hDJp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) 1)
  have hSξ : MemLpLoc 1 Ω (fun z => S z (ξ z)) := hS.clm_apply hsol.memLpLoc hpq1
  have hDJIξ : MemLpLoc 1 Ω (fun z => DJ z I (ξ z)) := hDJI.clm_apply hsol.memLpLoc hpq1
  have hDJ1ξ : MemLpLoc 1 Ω (fun z => DJ z 1 (ξ z)) := hDJ1.clm_apply hsol.memLpLoc hpq1
  set f : ℂ → V := fun z => η z - S z (ξ z) + DJ z I (ξ z)
  set g : ℂ → V := fun z => -J z (η z) + J z (S z (ξ z)) - DJ z 1 (ξ z)
  obtain ⟨hf, hg⟩ := memLpLoc_laplacian_rhs hp hpq1 hJ hDJ hS hsol.memLpLoc hη1
  have hf_loc : LocallyIntegrableOn f Ω := hf.locallyIntegrableOn le_rfl hloc
  have hg_loc : LocallyIntegrableOn g Ω := hg.locallyIntegrableOn le_rfl hloc
  have hξ_loc := hsol.memLpLoc.locallyIntegrableOn (ENNReal.inv_le_one.1 (le_add_self.trans hpq))
    hloc
  have hint_rhs : Integrable (fun z => fderiv ℝ (ψ : ℂ → ℝ) z 1 • f z +
      fderiv ℝ (ψ : ℂ → ℝ) z I • g z) :=
    (integrable_fderiv_smul_of_locallyIntegrableOn hf_loc ψ 1).add
      (integrable_fderiv_smul_of_locallyIntegrableOn hg_loc ψ I)
  refine ext_inner_left ℝ fun v => ?_
  rw [← integral_inner (integrable_laplacian_smul_of_locallyIntegrableOn hξ_loc ψ) v,
    inner_neg_right, ← integral_inner hint_rhs v, integral_inner_laplacian_smul_eq hξ_loc ψ v]
  have heq₁ := hsol.integral_test_lineDeriv_one hpq hc ψ v
  have heq₂ := hsol.integral_test_mollified_adjoint hp hpq hJ hJi hc hJsq hDJI ψ v
  have h1 : Integrable (fun z => ⟪v, fderiv ℝ (ψ : ℂ → ℝ) z 1 • f z⟫_ℝ) :=
    (innerSL ℝ v).integrable_comp (integrable_fderiv_smul_of_locallyIntegrableOn hf_loc ψ 1)
  have h2 : Integrable (fun z => ⟪v, fderiv ℝ (ψ : ℂ → ℝ) z I • g z⟫_ℝ) :=
    (innerSL ℝ v).integrable_comp (integrable_fderiv_smul_of_locallyIntegrableOn hg_loc ψ I)
  have hg_eq (z : ℂ) : g z = J z (S z (ξ z)) - J z (η z) + -DJ z 1 (ξ z) := by dsimp [g]; abel
  simp only [inner_add_right]
  rw [integral_add h1 h2]
  simp only [← TestFunction.lineDerivOp_apply_eq_fderiv ψ 1,
    ← TestFunction.lineDerivOp_apply_eq_fderiv ψ I, f, hg_eq]
  rw [integral_inner_smul_sub_add le_rfl (∂_{(1 : ℂ)} ψ) v hη1 hSξ hDJIξ,
    integral_inner_smul_sub_add (w₃ := fun z => -DJ z 1 (ξ z)) le_rfl (∂_{(I : ℂ)} ψ) v
      (hJi.clm_apply hSξ (by simp)) (hJi.clm_apply hη1 (by simp)) hDJ1ξ.neg]
  simp only [inner_neg_right, mul_neg, integral_neg]
  linarith

/-! ### Single Hölder step and order-zero Sobolev iteration -/

/-- **Single Hölder step at order zero** (McDuff–Salamon, Lemma B.4.6). If `2 < p ≤ ∞`,
`1 < r < ∞`, `1/p + 1/q ≤ 1/r`, `J ∈ W^{1,p}_loc(Ω)` satisfies `J² = -1` almost everywhere on `Ω`
with weak derivative `DJ`, `S ∈ Lᵖ_loc(Ω)`, `ξ` solves `∂_s ξ + J ∂_t ξ + S ξ = η` weakly in
`L^q_loc(Ω)`, and `η ∈ Lʳ_loc(Ω)`, then `ξ ∈ W^{1,r}_loc(Ω)`. The endpoints `p = ∞` and `q = ∞`
are included. -/
theorem memWkpLoc_one_of_inv_add_inv_le (hp : 2 < p) (hr : 1 < r)
    (hr_top : r ≠ ⊤) (hpqr : p⁻¹ + q⁻¹ ≤ r⁻¹)
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hS : MemLpLoc p Ω S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hη : MemLpLoc r Ω η) :
    MemWkpLoc r Ω 1 ξ := by
  have hpq : p⁻¹ + q⁻¹ ≤ 1 := hpqr.trans (ENNReal.inv_le_one.2 hr.le)
  obtain ⟨hf, hg⟩ := memLpLoc_laplacian_rhs hp hpqr hJ hDJ hS hsol.memLpLoc hη
  have hξ_loc := hsol.memLpLoc.locallyIntegrableOn
    (ENNReal.inv_le_one.1 (le_add_self.trans hpq)) Ω.isOpen.isLocallyClosed
  exact memWkpLoc_one_of_forall_integral_laplacian_smul_eq hr hr_top hξ_loc hf hg
    (hsol.integral_laplacian_smul_eq hp hpq hJ hDJ hJsq hS)

/-- Once `ξ` reaches `W^{1,r}_loc` for some `r > 2`, the `L^∞` Sobolev embedding puts `ξ` in
`L^∞_loc`, and one more application of `memWkpLoc_one_of_inv_add_inv_le` reaches `W^{1,s}_loc`. -/
private theorem memWkpLoc_one_of_two_lt (hr : 2 < r) (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hs1 : 1 < s) (hsp : s ≤ p)
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hS : MemLpLoc p Ω S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hη : MemLpLoc s Ω η)
    (hξr : MemWkpLoc r Ω 1 ξ) : MemWkpLoc s Ω 1 ξ :=
  (hsol.of_memLpLoc (hξr.memLpLoc_top hr)).memWkpLoc_one_of_inv_add_inv_le hp hs1
    (ne_top_of_le_ne_top hp_top hsp) (by simpa using ENNReal.inv_le_inv.2 hsp) hJ hDJ hJsq hS hη

/-- Subcritical step (`1 < r₁ < 2`) of the order-zero ladder: for `1/r₁ = 1/p + 1/t`, the critical
two-dimensional Sobolev embedding `W^{1,r₁}_loc ⊂ L^{t'}_loc` decreases `1/t` by `1/2 - 1/p`. -/
private theorem memWkpLoc_one_subcritical_step {p t r₁ : ℝ≥0} (hp_inv : (p : ℝ)⁻¹ < 2⁻¹)
    (hpt : (p : ℝ)⁻¹ + (t : ℝ)⁻¹ < 1)
    (hr₁_coe : (r₁ : ℝ) = ((p : ℝ)⁻¹ + (t : ℝ)⁻¹)⁻¹) (hr₁_gt1 : 1 < (r₁ : ℝ))
    (hlt2 : (r₁ : ℝ) < 2) (hsolt : IsWeakCRSolution t Ω J DJ S ξ η)
    (hξ_r₁ : MemWkpLoc r₁ Ω 1 ξ) :
    ∃ t' : ℝ≥0, (0 : ℝ) < t' ∧ (p : ℝ)⁻¹ + (t' : ℝ)⁻¹ < 1 ∧
      (t' : ℝ)⁻¹ = (t : ℝ)⁻¹ - (2⁻¹ - (p : ℝ)⁻¹) ∧ IsWeakCRSolution t' Ω J DJ S ξ η := by
  have hr₁_pos : (0 : ℝ) < r₁ := zero_lt_one.trans hr₁_gt1
  set b' : ℝ := (r₁ : ℝ)⁻¹ - 2⁻¹
  have hb'_pos : 0 < b' := sub_pos.2 ((inv_lt_inv₀ zero_lt_two hr₁_pos).2 hlt2)
  have hb'_eq : b' = (t : ℝ)⁻¹ - (2⁻¹ - (p : ℝ)⁻¹) := by
    dsimp only [b']; rw [hr₁_coe, inv_inv]; ring
  let t' : ℝ≥0 := ⟨b'⁻¹, by positivity⟩
  have ht'_coe : (t' : ℝ) = b'⁻¹ := NNReal.coe_mk b'⁻¹ (by positivity)
  have ht'_pos : (0 : ℝ) < t' := by rw [ht'_coe]; positivity
  have ht'_inv : (t' : ℝ)⁻¹ = b' := by rw [ht'_coe, inv_inv]
  have hr₁_le_t' : r₁ ≤ t' := by
    rw [← NNReal.coe_le_coe]
    exact (inv_le_inv₀ ht'_pos hr₁_pos).1 (by rw [ht'_inv]; dsimp [b']; linarith)
  have hξ_t' : MemLpLoc t' Ω ξ :=
    hξ_r₁.memLpLoc_of_inv_sub_inv_le (by exact_mod_cast hr₁_gt1.le) hr₁_le_t'
      (by rw [ht'_inv]; dsimp [b']; linarith)
  refine ⟨t', ht'_pos, ?_, ht'_inv.trans hb'_eq, hsolt.of_memLpLoc hξ_t'⟩
  rw [ht'_inv, hb'_eq]; linarith

/-- Critical case (`r₁ = 2`) of the order-zero ladder: `W^{1,2}_loc` embeds into every finite
`L^{t*}_loc`; choosing `1/t* = (1/2 - 1/p) / 2` makes the next product exponent exceed `2`, where
`memWkpLoc_one_of_two_lt` finishes. -/
private theorem memWkpLoc_one_critical_case {p s r₁ : ℝ≥0} (hp : 2 < (p : ℝ≥0∞))
    (hs1 : 1 < (s : ℝ≥0∞)) (hsp : (s : ℝ≥0∞) ≤ p) (hrs : (r₁ : ℝ) < s) (heq2 : (r₁ : ℝ) = 2)
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hS : MemLpLoc p Ω S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hη : MemLpLoc s Ω η)
    (hξ_r₁ : MemWkpLoc r₁ Ω 1 ξ) : MemWkpLoc s Ω 1 ξ := by
  have hpR : (2 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hp_inv : (p : ℝ)⁻¹ < 2⁻¹ := (inv_lt_inv₀ hp0 zero_lt_two).2 hpR
  set a : ℝ := 2⁻¹ - (p : ℝ)⁻¹
  have ha : 0 < a := sub_pos.2 hp_inv
  let t_star : ℝ≥0 := ⟨(a / 2)⁻¹, by positivity⟩
  have ht_star_coe : (t_star : ℝ) = (a / 2)⁻¹ := NNReal.coe_mk (a / 2)⁻¹ (by positivity)
  have ht_star_pos : (0 : ℝ) < t_star := by rw [ht_star_coe]; positivity
  have ht_star_inv : (t_star : ℝ)⁻¹ = a / 2 := by rw [ht_star_coe, inv_inv]
  have hr₁_le_star : r₁ ≤ t_star := by
    rw [← NNReal.coe_le_coe, heq2]
    exact (inv_le_inv₀ ht_star_pos zero_lt_two).1
      (by rw [ht_star_inv]; dsimp [a]; linarith [inv_pos.2 hp0])
  have hξ_star : MemLpLoc t_star Ω ξ :=
    hξ_r₁.memLpLoc_of_inv_sub_inv_le (by rw [← NNReal.coe_le_coe, heq2]; norm_num) hr₁_le_star
      (by rw [heq2, ht_star_inv]; linarith)
  set r₂_real : ℝ := min (s : ℝ) ((p : ℝ)⁻¹ + a / 2)⁻¹
  have hr₂_gt2 : 2 < r₂_real := lt_min (heq2 ▸ hrs)
    ((lt_inv_comm₀ zero_lt_two (by positivity)).2 (by dsimp [a]; linarith [hp_inv]))
  let r₂ : ℝ≥0 := ⟨r₂_real, by positivity⟩
  have hr₂_coe : (r₂ : ℝ) = r₂_real := NNReal.coe_mk r₂_real (by positivity)
  have hr₂_pos : (0 : ℝ) < r₂ := by rw [hr₂_coe]; positivity
  have hpqr₂ : (p : ℝ≥0∞)⁻¹ + (t_star : ℝ≥0∞)⁻¹ ≤ (r₂ : ℝ≥0∞)⁻¹ :=
    (ENNReal.inv_coe_add_inv_coe_le_inv_coe_iff (by exact_mod_cast hp0.ne')
      (by exact_mod_cast ht_star_pos.ne') (by exact_mod_cast hr₂_pos.ne')).2 <| by
        rw [← NNReal.coe_le_coe]; push_cast
        rw [ht_star_inv, hr₂_coe]
        exact (le_inv_comm₀ (by positivity) (by positivity)).2 (min_le_right _ _)
  have hr₂_gt2' : (2 : ℝ) < r₂ := hr₂_coe.symm ▸ hr₂_gt2
  have hr₂_le_s : (r₂ : ℝ) ≤ s := hr₂_coe.trans_le (min_le_left _ _)
  have hξ_r₂ : MemWkpLoc r₂ Ω 1 ξ :=
    (hsol.of_memLpLoc hξ_star).memWkpLoc_one_of_inv_add_inv_le hp
      (by exact_mod_cast one_lt_two.trans hr₂_gt2') ENNReal.coe_ne_top hpqr₂ hJ hDJ hJsq hS
      (hη.mono_exponent (by exact_mod_cast hr₂_le_s))
  exact memWkpLoc_one_of_two_lt (by exact_mod_cast hr₂_gt2')
    hp ENNReal.coe_ne_top hs1 hsp hJ hDJ hJsq hS hsol hη hξ_r₂

/-- Finite-exponent Sobolev ladder: if `1/t ≤ n * (1/2 - 1/p)` with `1/p + 1/t < 1`, at most `n`
iterations of the single Hölder step and 2D Sobolev embedding upgrade `ξ` to `W^{1,s}_loc(Ω)`. -/
private theorem memWkpLoc_one_ladder {p s : ℝ≥0} (hp : 2 < (p : ℝ≥0∞))
    (hs1 : 1 < (s : ℝ≥0∞)) (hsp : (s : ℝ≥0∞) ≤ p)
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hS : MemLpLoc p Ω S) (hη : MemLpLoc s Ω η) :
    ∀ (n : ℕ) {t : ℝ≥0}, (0 : ℝ) < t → (p : ℝ)⁻¹ + (t : ℝ)⁻¹ < 1 →
      (t : ℝ)⁻¹ ≤ n * (2⁻¹ - (p : ℝ)⁻¹) → IsWeakCRSolution t Ω J DJ S ξ η →
      MemWkpLoc s Ω 1 ξ := by
  have hpR : (2 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := zero_lt_two.trans hpR
  have hp_inv : (p : ℝ)⁻¹ < 2⁻¹ := (inv_lt_inv₀ hp0 zero_lt_two).2 hpR
  have hs1R : (1 : ℝ) < s := by exact_mod_cast hs1
  intro n
  induction n with
  | zero => intro t ht0 _ htn _; linarith [inv_pos.2 ht0]
  | succ n ih =>
    intro t ht0 hpt htn hsolt
    set r_prod : ℝ := ((p : ℝ)⁻¹ + (t : ℝ)⁻¹)⁻¹
    have hr_prod_gt : 1 < r_prod := (one_lt_inv₀ (by positivity)).2 hpt
    -- If the product exponent `r_prod` already reaches `s`, a single Hölder step finishes.
    rcases le_or_gt (s : ℝ) r_prod with hsr | hrs
    · exact hsolt.memWkpLoc_one_of_inv_add_inv_le hp hs1 ENNReal.coe_ne_top
        ((ENNReal.inv_coe_add_inv_coe_le_inv_coe_iff (by exact_mod_cast hp0.ne')
          (by exact_mod_cast ht0.ne') (by exact_mod_cast (zero_lt_one.trans hs1R).ne')).2 <| by
            rw [← NNReal.coe_le_coe]; push_cast
            exact (le_inv_comm₀ (by positivity) (zero_lt_one.trans hs1R)).2 hsr)
        hJ hDJ hJsq hS hη
    · -- Otherwise step to `W^{1,r₁}_loc` at `r₁ = r_prod` and split on `r₁ < 2`, `= 2`, `> 2`.
      let r₁ : ℝ≥0 := ⟨r_prod, by positivity⟩
      have hr₁_coe : (r₁ : ℝ) = r_prod := NNReal.coe_mk r_prod (by positivity)
      have hr₁_pos : (0 : ℝ) < r₁ := by rw [hr₁_coe]; positivity
      have hξ_r₁ : MemWkpLoc r₁ Ω 1 ξ :=
        hsolt.memWkpLoc_one_of_inv_add_inv_le hp
          (by exact_mod_cast (hr₁_coe.symm ▸ hr_prod_gt : (1 : ℝ) < r₁)) ENNReal.coe_ne_top
          ((ENNReal.inv_coe_add_inv_coe_le_inv_coe_iff (by exact_mod_cast hp0.ne')
            (by exact_mod_cast ht0.ne') (by exact_mod_cast hr₁_pos.ne')).2 <| by
              rw [← NNReal.coe_le_coe]; simp [hr₁_coe, r_prod])
          hJ hDJ hJsq hS (hη.mono_exponent (by exact_mod_cast (hr₁_coe.trans_lt hrs).le))
      rcases lt_trichotomy (r₁ : ℝ) 2 with hlt2 | heq2 | hgt2
      · obtain ⟨t', ht'0, hpt', ht'_eq, hsolt'⟩ :=
          memWkpLoc_one_subcritical_step hp_inv hpt hr₁_coe (hr₁_coe ▸ hr_prod_gt) hlt2 hsolt hξ_r₁
        refine ih ht'0 hpt' ?_ hsolt'
        have hstep : ((n + 1 : ℕ) : ℝ) * (2⁻¹ - (p : ℝ)⁻¹) =
            (n : ℝ) * (2⁻¹ - (p : ℝ)⁻¹) + (2⁻¹ - (p : ℝ)⁻¹) := by push_cast; ring
        linarith [htn, ht'_eq, hstep]
      · exact memWkpLoc_one_critical_case hp hs1 hsp (hr₁_coe ▸ hrs) heq2 hJ hDJ hJsq hS hsolt hη
          hξ_r₁
      · exact memWkpLoc_one_of_two_lt (by exact_mod_cast hgt2) hp ENNReal.coe_ne_top hs1 hsp
          hJ hDJ hJsq hS hsolt hη hξ_r₁

/-- **Order-zero interior regularity** (McDuff–Salamon, Lemma B.4.6). Let `2 < p ≤ ∞`,
`1/p + 1/q < 1`, and `1 < s ≤ p` with `s < ∞`. If `J ∈ W^{1,p}_loc(Ω)` satisfies `J² = -1` almost
everywhere on `Ω` with weak derivative `DJ`, `S ∈ Lᵖ_loc(Ω)`, `ξ` solves
`∂_s ξ + J ∂_t ξ + S ξ = η` weakly in `L^q_loc(Ω)`, and `η ∈ Lˢ_loc(Ω)`, then
`ξ ∈ W^{1,s}_loc(Ω)`. The coefficient endpoint `p = ∞` is included. -/
theorem memWkpLoc_one_of_memLpLoc (hp : 2 < p) (hpq : p⁻¹ + q⁻¹ < 1)
    (hs1 : 1 < s) (hs_top : s ≠ ⊤) (hsp : s ≤ p)
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hS : MemLpLoc p Ω S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hη : MemLpLoc s Ω η) :
    MemWkpLoc s Ω 1 ξ := by
  obtain ⟨p', hp', hp'_top, hp'p, hp'q, hsp'⟩ :
      ∃ p' : ℝ≥0∞, 2 < p' ∧ p' ≠ ⊤ ∧ p' ≤ p ∧ p'⁻¹ + q⁻¹ < 1 ∧ s ≤ p' := by
    by_cases hp_top : p = ⊤
    · subst hp_top
      have hq1 : 1 < q := ENNReal.inv_lt_one.1 (by simpa using hpq)
      obtain ⟨p', hp'_gt, hp'_top, hp'q⟩ :=
        ENNReal.exists_gt_ne_top_and_inv_add_inv_lt_one
          (max_ne_top (by simp : (2 : ℝ≥0∞) ≠ ⊤) hs_top) hq1
      exact ⟨p', (le_max_left 2 s).trans_lt hp'_gt, hp'_top, le_top, hp'q,
        (le_max_right 2 s).trans hp'_gt.le⟩
    · exact ⟨p, hp, hp_top, le_rfl, hpq, hsp⟩
  have hJ' : MemWkpLoc p' Ω 1 J := hJ.mono_exponent hp'p
  have hS' : MemLpLoc p' Ω S := hS.mono_exponent hp'p
  have hq₀_top : min q p' ≠ ⊤ := ne_top_of_le_ne_top hp'_top (min_le_right q p')
  have hsol₀ : IsWeakCRSolution (min q p') Ω J DJ S ξ η := hsol.mono_exponent (min_le_left q p')
  have hpq₀ : p'⁻¹ + (min q p')⁻¹ < 1 := ENNReal.inv_add_inv_min_lt_one hp' hp'q
  generalize hq₀_def : min q p' = q₀
  rw [hq₀_def] at hq₀_top hsol₀ hpq₀
  lift q₀ to ℝ≥0 using hq₀_top
  lift p' to ℝ≥0 using hp'_top
  lift s to ℝ≥0 using hs_top
  have hpR : (2 : ℝ) < p' := by exact_mod_cast hp'
  have hp0 : (0 : ℝ) < p' := zero_lt_two.trans hpR
  have ha : 0 < 2⁻¹ - (p' : ℝ)⁻¹ := sub_pos.2 ((inv_lt_inv₀ hp0 zero_lt_two).2 hpR)
  have hq₀_pos : (0 : ℝ) < q₀ := by
    by_contra hle
    simp [NNReal.coe_eq_zero.1 (le_antisymm (not_lt.1 hle) q₀.coe_nonneg)] at hpq₀
  have hpq₀R : (p' : ℝ)⁻¹ + (q₀ : ℝ)⁻¹ < 1 := by
    have h := (ENNReal.inv_coe_add_inv_coe_lt_one_iff (by exact_mod_cast hp0.ne')
      (by exact_mod_cast hq₀_pos.ne')).1 hpq₀
    exact_mod_cast h
  exact memWkpLoc_one_ladder hp' hs1 hsp' hJ' hDJ hJsq hS' hη ⌈(q₀ : ℝ)⁻¹ / (2⁻¹ - (p' : ℝ)⁻¹)⌉₊
    hq₀_pos hpq₀R ((div_le_iff₀ ha).1 (Nat.le_ceil _)) hsol₀

/-- **Order-zero interior regularity at the solution's exponent.** If `2 < p ≤ ∞`,
`1/p + 1/q < 1`, `q < ∞`, `q ≤ p`, `J ∈ W^{1,p}_loc(Ω)` with `J² = -1` almost everywhere on `Ω`,
`S ∈ Lᵖ_loc(Ω)`, and `ξ` solves `∂_s ξ + J ∂_t ξ + S ξ = η` weakly in `L^q_loc(Ω)` with
`η ∈ L^q_loc(Ω)`, then `ξ ∈ W^{1,q}_loc(Ω)`. -/
theorem memWkpLoc_one_of_le (hp : 2 < p) (hpq : p⁻¹ + q⁻¹ < 1) (hq_top : q ≠ ⊤) (hqp : q ≤ p)
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hS : MemLpLoc p Ω S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hη : MemLpLoc q Ω η) :
    MemWkpLoc q Ω 1 ξ :=
  hsol.memWkpLoc_one_of_memLpLoc hp hpq
    (ENNReal.inv_lt_one.1 (lt_of_le_of_lt le_add_self hpq)) hq_top hqp hJ hDJ hJsq hS hη

/-- **Order-zero interior regularity at the coefficient exponent.** If `2 < p < ∞`,
`1/p + 1/q < 1`, `J ∈ W^{1,p}_loc(Ω)` with `J² = -1` almost everywhere on `Ω`, `S ∈ Lᵖ_loc(Ω)`,
and `ξ` solves `∂_s ξ + J ∂_t ξ + S ξ = η` weakly in `L^q_loc(Ω)` with `η ∈ Lᵖ_loc(Ω)`, then
`ξ ∈ W^{1,p}_loc(Ω)`. -/
theorem memWkpLoc_one (hp : 2 < p) (hp_top : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ < 1)
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hS : MemLpLoc p Ω S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hη : MemLpLoc p Ω η) :
    MemWkpLoc p Ω 1 ξ :=
  hsol.memWkpLoc_one_of_memLpLoc hp hpq
    ((by exact_mod_cast one_lt_two : (1 : ℝ≥0∞) < 2).trans hp) hp_top le_rfl hJ
    hDJ hJsq hS hη

end IsWeakCRSolution

end TauCeti
