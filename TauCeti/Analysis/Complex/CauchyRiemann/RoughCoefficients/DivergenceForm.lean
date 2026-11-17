/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
public import TauCeti.Analysis.Complex.Wirtinger.DivergenceLaplace
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Sobolev.Local.Holder
import TauCeti.Analysis.Sobolev.Mollification.Interior
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Weak solutions of `∂_s ξ + J ∂_t ξ + S ξ = η` solve a divergence-form Laplace equation

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a finite-dimensional real inner product
space. Let `J, S : ℂ → (V →L[ℝ] V)` be coefficient fields with `J ∈ W^{1,p}_loc`, `S ∈ Lᵖ_loc`,
`J` locally bounded and `J² = -1` almost everywhere, and let `ξ ∈ L^q_loc` be a weak solution of

`∂_s ξ + J ∂_t ξ + S ξ = η`

in the sense of `TauCeti.IsWeakCRSolution`, for `1/p + 1/q ≤ 1`. Applying the operator
`∂_s - J ∂_t` formally to the equation, and using `J² = -1`, gives

`Δ ξ = ∂_s F + ∂_t G`, with `F = η + (∂_t J) ξ - S ξ` and
`G = -J F - (∂_s J) ξ - (∂_t J) (J ξ)`.

This file proves that this holds weakly
(`TauCeti.IsWeakCRSolution.integral_laplacian_smul_eq`): for every real test function `ψ`,

`∫ Δψ • ξ = -∫ (∂_s ψ • F + ∂_t ψ • G)`.

Since `F` and `G` contain no derivative of `ξ`, the divergence-form Laplace regularity of
`TauCeti.memWkpLoc_one_of_forall_integral_laplacian_smul_eq` then puts `ξ` in `W^{1,r}_loc` as soon
as `F` and `G` are locally `Lʳ` for some `1 < r < ∞`. With the Hölder exponent
`1/r = 1/p + 1/q` and `η ∈ Lʳ_loc` they are, so a weak solution in `L^q_loc` gains a derivative in
`Lʳ_loc` (`TauCeti.IsWeakCRSolution.memWkpLoc_one`). This is the order-zero step of the interior
regularity theory of real Cauchy–Riemann operators with Sobolev coefficients
(McDuff–Salamon, Lemma B.4.6); for `p > 2` the coefficient `J` is continuous, hence locally
bounded, by Morrey's embedding.

## The argument

The identity comes from testing the weak equation against `φ = -(∂_s ψ) v + (∂_t ψ) Jᵀ v` for a
vector `v`. This is not a test function, since `J` is only weakly differentiable. The two parts
are treated separately. The first, `(∂_s ψ) v`, is a test function. For the second, `J` is
replaced by its mollifications `J_n`, which are smooth, so that `(∂_t ψ) J_nᵀ v` is a test
function. The weak equation tested against it is an identity between pairings of fixed functions
with `J_n` and with its derivative. As the mollifier shrinks, `J_n` converges to `J` against
integrable functions, since `J` is locally bounded, and the derivative of `J_n`, which is the
mollification of the weak derivative of `J`, converges to it against functions in the conjugate
exponent of `p` (`ContinuousLinearMap.tendsto_integral_bilin_normed_convolution`). In the limit the
pairings with `J` and its weak derivative remain, and adding the identity for the first part, with
`Jᵀ Jᵀ = -1`, gives the divergence-form equation.

## Main results

* `TauCeti.IsWeakCRSolution.integral_laplacian_smul_eq`: a weak solution satisfies
  `Δ ξ = ∂_s F + ∂_t G` weakly.
* `TauCeti.IsWeakCRSolution.memWkpLoc_one`: a weak solution in `L^q_loc` with right-hand side in
  `Lʳ_loc`, `1/r = 1/p + 1/q` and `1 < r < ∞`, lies in `W^{1,r}_loc`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4, Lemma B.4.6 and its proof.
-/

public section

open MeasureTheory TopologicalSpace Complex Filter Topology Metric
open scoped InnerProductSpace ContDiff Distributions ENNReal Laplacian Convolution LineDeriv

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ} {p q r : ℝ≥0∞}
  {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

/-! ### Preliminaries -/

/-- The pairing `w ↦ A ↦ ⟪v, A w⟫`. -/
private noncomputable def crPairing (v : V) : V →L[ℝ] (V →L[ℝ] V) →L[ℝ] ℝ :=
  ContinuousLinearMap.compL ℝ (V →L[ℝ] V) V ℝ (innerSL ℝ v) ∘L
    (ContinuousLinearMap.id ℝ (V →L[ℝ] V)).flip

omit [FiniteDimensional ℝ V] in
private theorem crPairing_apply (v w : V) (A : V →L[ℝ] V) : crPairing v w A = ⟪v, A w⟫_ℝ := by
  simp [crPairing]

/-- A bilinear pairing of an integrable function vanishing off a compact set `K` with a function
continuous on `K` is integrable. -/
private theorem integrable_bilin_of_continuousOn {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E →L[ℝ] F →L[ℝ] ℝ)
    {a : ℂ → E} (ha : Integrable a) {K : Set ℂ} (hK : IsCompact K) (haK : ∀ z ∉ K, a z = 0)
    {M : ℂ → F} (hM : ContinuousOn M K) : Integrable (fun z => B (a z) (M z)) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hM
  have heq : (fun z => B (a z) (M z)) = fun z => B (a z) (K.indicator M z) := by
    funext z
    by_cases hz : z ∈ K
    · rw [Set.indicator_of_mem hz]
    · simp [haK z hz]
  rw [heq]
  refine B.integrable_of_bilin_of_bdd_right (max C 0) ha
    ((aestronglyMeasurable_indicator_iff hK.measurableSet).2
      (hM.aestronglyMeasurable hK.measurableSet))
    (.of_forall fun z => ?_)
  by_cases hz : z ∈ K
  · rw [Set.indicator_of_mem hz]
    exact (hC z hz).trans (le_max_left _ _)
  · rw [Set.indicator_of_notMem hz, norm_zero]
    exact le_max_right _ _

omit [FiniteDimensional ℝ V] in
/-- A test function times a locally `Lˢ` function on `Ω` is in `Lˢ` of the plane. -/
private theorem memLp_testFunction_smul {s : ℝ≥0∞} {W : ℂ → V} (c : 𝓓(Ω, ℝ))
    (hW : MemLpLoc s Ω W) : MemLp (fun z => c z • W z) s volume :=
  hW.memLp_smul_of_hasCompactSupport c.continuous c.hasCompactSupport c.tsupport_subset

/-! ### Testing the weak equation against `χ Aᵀ v` -/

/-- The field `a = ∂_s χ ξ + ∂_t χ J ξ + χ ((∂_t J) ξ - S ξ + η)` paired with the coefficient is
integrable. -/
private theorem IsWeakCRSolution.integrable_crPairingField
    (h : IsWeakCRSolution q Ω J DJ S ξ η) (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (χ : 𝓓(Ω, ℝ)) :
    Integrable (fun z => fderiv ℝ χ z 1 • ξ z + fderiv ℝ χ z I • J z (ξ z) +
      χ z • (DJ z I (ξ z) - S z (ξ z) + η z)) := by
  have hloc := Ω.isOpen.isLocallyClosed
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hξ1 : MemLpLoc 1 Ω ξ := h.memLpLoc.mono_exponent hq1
  have hJξ : MemLpLoc 1 Ω (fun z => J z (ξ z)) := (memLpLoc_one_iff_locallyIntegrableOn hloc).2
    (hc.memLpLoc_coeff.locallyIntegrableOn_clm_apply h.memLpLoc hpq hloc)
  have hDJξ : MemLpLoc 1 Ω (fun z => DJ z I (ξ z)) :=
    (memLpLoc_one_iff_locallyIntegrableOn hloc).2
      (MemLpLoc.locallyIntegrableOn_clm_apply
        (hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I))
        h.memLpLoc hpq hloc)
  have hSξ : MemLpLoc 1 Ω (fun z => S z (ξ z)) := (memLpLoc_one_iff_locallyIntegrableOn hloc).2
    (hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply h.memLpLoc hpq hloc)
  have hη : MemLpLoc 1 Ω η := (memLpLoc_one_iff_locallyIntegrableOn hloc).2 h.locallyIntegrableOn
  have hW : MemLpLoc 1 Ω (fun z => DJ z I (ξ z) - S z (ξ z) + η z) := (hDJξ.sub hSξ).add hη
  have hd (e : ℂ) : (fun z => fderiv ℝ (χ : ℂ → ℝ) z e) = ⇑(∂_{e} χ : 𝓓(Ω, ℝ)) :=
    funext fun z => (TestFunction.lineDerivOp_apply_eq_fderiv χ e z).symm
  have h1 := memLp_testFunction_smul (∂_{(1 : ℂ)} χ) hξ1
  have h2 := memLp_testFunction_smul (∂_{I} χ) hJξ
  have h3 := memLp_testFunction_smul χ hW
  rw [← hd] at h1 h2
  exact memLp_one_iff_integrable.1 ((h1.add h2).add h3)


/-- **The test function `χ Aᵀ v`.** For a smooth field `A` of operators, a test function `χ` and a
vector `v`, the function `χ Aᵀ v` is a test function `Φ`, and pointwise
`⟪D* Φ, ξ⟫ - ⟪Φ, η⟫ = -(⟪v, A a⟫ + ⟪v, A' 1 (χ ξ)⟫ + ⟪v, A' I (χ J ξ)⟫)`, where `A'` is the
derivative of `A` and `a = ∂_s χ ξ + ∂_t χ J ξ + χ ((∂_t J) ξ - S ξ + η)`. -/
private theorem exists_testFunction_inner_crFormalAdjoint_sub_inner (χ : 𝓓(Ω, ℝ)) (v : V)
    {A : ℂ → V →L[ℝ] V} (hA : ContDiff ℝ ∞ A) :
    ∃ Φ : 𝓓(Ω, V), ∀ z, ⟪crFormalAdjoint J DJ S Φ z, ξ z⟫_ℝ - ⟪(Φ : ℂ → V) z, η z⟫_ℝ =
      -(crPairing v (fderiv ℝ χ z 1 • ξ z + fderiv ℝ χ z I • J z (ξ z) +
          χ z • (DJ z I (ξ z) - S z (ξ z) + η z)) (A z) +
        crPairing v (χ z • ξ z) (fderiv ℝ A z 1) +
        crPairing v (χ z • J z (ξ z)) (fderiv ℝ A z I)) := by
  let adj : (V →L[ℝ] V) ≃L[ℝ] V →L[ℝ] V :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := V) (F := V)).toContinuousLinearEquiv
  have hadj (B : V →L[ℝ] V) : adj B = ContinuousLinearMap.adjoint B := by simp [adj]
  have hB : ContDiff ℝ ∞ (fun z => adj (A z) v) :=
    ((adj : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V).contDiff.comp hA).clm_apply contDiff_const
  let Φ : 𝓓(Ω, V) := ⟨⇑χ • fun z => adj (A z) v, χ.contDiff.smul hB,
    χ.hasCompactSupport.smul_right, (tsupport_smul_subset_left _ _).trans χ.tsupport_subset⟩
  have hΦ : (Φ : ℂ → V) = ⇑χ • fun z => adj (A z) v := rfl
  have hΦd (z e : ℂ) : fderiv ℝ (Φ : ℂ → V) z e =
      fderiv ℝ χ z e • adj (A z) v + χ z • adj (fderiv ℝ A z e) v := by
    have h1 : HasFDerivAt (fun z => adj (A z))
        ((adj : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V).comp (fderiv ℝ A z)) z :=
      (adj : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V).hasFDerivAt.comp z
        (hA.differentiable (by simp) z).hasFDerivAt
    rw [hΦ, ((χ.contDiff.differentiable (by simp) z).hasFDerivAt.smul
      (h1.clm_apply (hasFDerivAt_const v z))).fderiv]
    simp [add_comm]
  refine ⟨Φ, fun z => ?_⟩
  rw [inner_crFormalAdjoint, hΦd, hΦd, hΦ]
  simp only [map_add, map_sub, map_smul, add_apply, sub_apply, FunLike.coe_smul, Pi.smul_apply,
    Pi.smul_apply', smul_eq_mul, crPairing_apply, hadj, inner_add_left, real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left]
  ring

/-- **The weak equation tested against `χ Aᵀ v`.** For a smooth field `A` of operators, a test
function `χ` and a vector `v`, the function `χ Aᵀ v` is a test function, and the weak equation
tested against it reads `∫ ⟪v, A a⟫ + ∫ ⟪v, A' 1 (χ ξ)⟫ + ∫ ⟪v, A' I (χ J ξ)⟫ = 0`, where `A'`
is the derivative of `A` and `a = ∂_s χ ξ + ∂_t χ J ξ + χ ((∂_t J) ξ - S ξ + η)`. -/
private theorem IsWeakCRSolution.integral_crPairing_of_contDiff
    (h : IsWeakCRSolution q Ω J DJ S ξ η) (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (χ : 𝓓(Ω, ℝ)) (v : V) {A : ℂ → V →L[ℝ] V} (hA : ContDiff ℝ ∞ A) :
    Integrable (fun z => crPairing v (fderiv ℝ χ z 1 • ξ z + fderiv ℝ χ z I • J z (ξ z) +
        χ z • (DJ z I (ξ z) - S z (ξ z) + η z)) (A z)) ∧
      Integrable (fun z => crPairing v (χ z • ξ z) (fderiv ℝ A z 1)) ∧
      Integrable (fun z => crPairing v (χ z • J z (ξ z)) (fderiv ℝ A z I)) ∧
      (∫ z, crPairing v (fderiv ℝ χ z 1 • ξ z + fderiv ℝ χ z I • J z (ξ z) +
          χ z • (DJ z I (ξ z) - S z (ξ z) + η z)) (A z)) +
        (∫ z, crPairing v (χ z • ξ z) (fderiv ℝ A z 1)) +
        ∫ z, crPairing v (χ z • J z (ξ z)) (fderiv ℝ A z I) = 0 := by
  have hK : IsCompact (tsupport (χ : ℂ → ℝ)) := χ.hasCompactSupport
  have hloc := Ω.isOpen.isLocallyClosed
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hξ1 : MemLpLoc 1 Ω ξ := h.memLpLoc.mono_exponent hq1
  have hJξ : MemLpLoc 1 Ω (fun z => J z (ξ z)) := (memLpLoc_one_iff_locallyIntegrableOn hloc).2
    (hc.memLpLoc_coeff.locallyIntegrableOn_clm_apply h.memLpLoc hpq hloc)
  have ha := h.integrable_crPairingField hc hpq χ
  have hb₁ : Integrable (fun z => χ z • ξ z) :=
    memLp_one_iff_integrable.1 (memLp_testFunction_smul χ hξ1)
  have hb₂ : Integrable (fun z => χ z • J z (ξ z)) :=
    memLp_one_iff_integrable.1 (memLp_testFunction_smul χ hJξ)
  have hχK (z : ℂ) (hz : z ∉ tsupport (χ : ℂ → ℝ)) : χ z = 0 ∧ fderiv ℝ χ z = 0 :=
    ⟨image_eq_zero_of_notMem_tsupport hz, fderiv_of_notMem_tsupport ℝ hz⟩
  have haK (z : ℂ) (hz : z ∉ tsupport (χ : ℂ → ℝ)) : fderiv ℝ χ z 1 • ξ z +
      fderiv ℝ χ z I • J z (ξ z) + χ z • (DJ z I (ξ z) - S z (ξ z) + η z) = 0 := by
    simp [(hχK z hz).1, (hχK z hz).2]
  have hbK₁ (z : ℂ) (hz : z ∉ tsupport (χ : ℂ → ℝ)) : χ z • ξ z = 0 := by
    simp [(hχK z hz).1]
  have hbK₂ (z : ℂ) (hz : z ∉ tsupport (χ : ℂ → ℝ)) : χ z • J z (ξ z) = 0 := by
    simp [(hχK z hz).1]
  have hP := integrable_bilin_of_continuousOn (crPairing v) ha hK haK hA.continuous.continuousOn
  have hA' (e : ℂ) : ContinuousOn (fun z => fderiv ℝ A z e) (tsupport (χ : ℂ → ℝ)) :=
    ((hA.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn
  have hQ₁ := integrable_bilin_of_continuousOn (crPairing v) hb₁ hK hbK₁ (hA' 1)
  have hQ₂ := integrable_bilin_of_continuousOn (crPairing v) hb₂ hK hbK₂ (hA' I)
  refine ⟨hP, hQ₁, hQ₂, ?_⟩
  obtain ⟨Φ, hpt⟩ := exists_testFunction_inner_crFormalAdjoint_sub_inner (J := J) (DJ := DJ)
    (S := S) (ξ := ξ) (η := η) χ v hA
  have h0 : ∫ z, (⟪crFormalAdjoint J DJ S Φ z, ξ z⟫_ℝ - ⟪(Φ : ℂ → V) z, η z⟫_ℝ) = 0 := by
    rw [integral_sub (h.integrable_inner_crFormalAdjoint Φ)
      (Φ.integrable_inner h.locallyIntegrableOn), h.integral_inner_crFormalAdjoint Φ, sub_self]
  rw [integral_congr_ae (.of_forall hpt), integral_neg, neg_eq_zero,
    integral_add ?_ hQ₂, integral_add hP hQ₁] at h0
  · exact h0
  · exact hP.add hQ₁

/-! ### Passing to the coefficient `J` by mollification -/

omit [FiniteDimensional ℝ V] in
/-- A compact subset `K` of `Ω` has an open neighbourhood `U` with compact closure in `Ω`
containing the closed balls of radius less than some `δ > 0` about the points of `K`. -/
private theorem exists_opens_closedBall_subset {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ U : Opens ℂ, ∃ δ > 0, IsCompact (closure (U : Set ℂ)) ∧ closure (U : Set ℂ) ⊆ Ω ∧
      ∀ z ∈ K, ∀ r < δ, closedBall z r ⊆ U := by
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open Ω.isOpen hKΩ
  have hcl : closure (thickening δ K) ⊆ cthickening δ K := closure_thickening_subset_cthickening δ K
  exact ⟨⟨thickening δ K, isOpen_thickening⟩, δ, hδ,
    hK.cthickening.of_isClosed_subset isClosed_closure hcl, hcl.trans hδΩ,
    fun z hz r hr => (closedBall_subset_ball hr).trans (ball_subset_thickening hz δ)⟩

/-- On `U`, the derivative of the mollification of the zero extension of a weakly differentiable
function `u`, in a direction `e`, is the mollification of the zero extension of its weak
derivative in that direction, at every point whose closed ball of the bump radius lies in `U`. -/
private theorem fderiv_normed_convolution_indicator_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {U : Opens ℂ} {u : ℂ → F} {Du : ℂ → ℂ →L[ℝ] F}
    (hu : HasWeakFDerivOn volume U u Du) (hup : MemLp u p (volume.restrict U))
    (hDup : MemLp Du p (volume.restrict U)) (hp : 1 ≤ p) (φ : ContDiffBump (0 : ℂ)) {z : ℂ}
    (hz : closedBall z φ.rOut ⊆ U) (e : ℂ) :
    fderiv ℝ (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (U : Set ℂ).indicator u)
        z e =
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (U : Set ℂ).indicator (fun z => Du z e)) z := by
  have h1 := hu.fderiv_indicator_convolution_normed hup hDup hp hp φ z hz
  rw [convolution_flip, convolution_flip] at h1
  have hloc : LocallyIntegrable ((U : Set ℂ).indicator Du) volume :=
    MemLp.locallyIntegrable
      ((memLp_indicator_iff_restrict U.isOpen.measurableSet.nullMeasurableSet).2 hDup) hp
  have hint := ((φ.hasCompactSupport_normed (μ := volume)).convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) φ.continuous_normed hloc) z
  rw [h1, convolution_def, convolution_def, ContinuousLinearMap.integral_apply hint]
  refine integral_congr_ae (.of_forall fun t => ?_)
  by_cases ht : z - t ∈ (U : Set ℂ)
  · simp [Set.indicator_of_mem ht]
  · simp [Set.indicator_of_notMem ht]

/-- The directional derivatives of an `Lᵖ` field of derivatives are in `Lᵖ`. This is
`ContinuousLinearMap.comp_memLp'` for evaluation at `e`, stated for an arbitrary codomain `F`:
applied directly to `F = V →L[ℝ] V` for an inner product space `V`, the instance search for the
norm structure of `ℂ →L[ℝ] V →L[ℝ] V` does not terminate in reasonable time. -/
private theorem memLp_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure ℂ}
    {Du : ℂ → ℂ →L[ℝ] F} (hDu : MemLp Du p μ) (e : ℂ) : MemLp (fun z => Du z e) p μ :=
  (ContinuousLinearMap.apply ℝ F e).comp_memLp' hDu

/-- **Passing to the limit in the pairings.** If the pairings of fixed fields `a ∈ L¹` and
`b₁, b₂ ∈ Lᵖ'` with the mollifications of `g ∈ L^∞` and `g₁, g₂ ∈ Lᵖ` add up to zero along a
sequence of shrinking bumps, then so do their pairings with `g`, `g₁` and `g₂`. -/
private theorem integral_add_eq_zero_of_forall_normed_convolution [Fact (1 ≤ p)]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (B : E →L[ℝ] F →L[ℝ] ℝ) {a b₁ b₂ : ℂ → E}
    {g g₁ g₂ : ℂ → F} (ha : MemLp a 1 volume) (hb₁ : MemLp b₁ p.conjExponent volume)
    (hb₂ : MemLp b₂ p.conjExponent volume) (hg : MemLp g ⊤ volume) (hg₁ : MemLp g₁ p volume)
    (hg₂ : MemLp g₂ p volume) {φ : ℕ → ContDiffBump (0 : ℂ)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    (hn : ∀ n, (∫ z, B (a z) (((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) z)) +
      (∫ z, B (b₁ z) (((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g₁) z)) +
      ∫ z, B (b₂ z) (((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g₂) z) = 0) :
    (∫ z, B (a z) (g z)) + (∫ z, B (b₁ z) (g₁ z)) + ∫ z, B (b₂ z) (g₂ z) = 0 := by
  have T1 := B.tendsto_integral_bilin_normed_convolution (q := 1) hφ ha hg
  have T2 := B.tendsto_integral_bilin_normed_convolution hφ hb₁ hg₁
  have T3 := B.tendsto_integral_bilin_normed_convolution hφ hb₂ hg₂
  exact tendsto_nhds_unique ((T1.add T2).add T3) (tendsto_const_nhds.congr fun n => (hn n).symm)

/-- The identity of `IsWeakCRSolution.integral_crPairing_of_contDiff` for the mollification of
the zero extension of `J` off a neighbourhood `U` of the support of `χ`, whose derivative on the
support is the mollification of the zero extension of `DJ`. -/
private theorem IsWeakCRSolution.integral_crPairing_normed_convolution
    (h : IsWeakCRSolution q Ω J DJ S ξ η) (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (χ : 𝓓(Ω, ℝ)) (v : V) {U : Opens ℂ}
    (hwJ : HasWeakFDerivOn volume U J DJ) (hJpU : MemLp J p (volume.restrict U))
    (hDJU : MemLp DJ p (volume.restrict U)) (hp1 : 1 ≤ p)
    (hg : LocallyIntegrable ((U : Set ℂ).indicator J) volume) (φ : ContDiffBump (0 : ℂ))
    (hball : ∀ z ∈ tsupport (χ : ℂ → ℝ), closedBall z φ.rOut ⊆ U) :
    (∫ z, crPairing v (fderiv ℝ χ z 1 • ξ z + fderiv ℝ χ z I • J z (ξ z) +
        χ z • (DJ z I (ξ z) - S z (ξ z) + η z))
          ((φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (U : Set ℂ).indicator J) z)) +
      (∫ z, crPairing v (χ z • ξ z) ((φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (U : Set ℂ).indicator (fun z => DJ z 1)) z)) +
      ∫ z, crPairing v (χ z • J z (ξ z)) ((φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (U : Set ℂ).indicator (fun z => DJ z I)) z) = 0 := by
  obtain ⟨-, -, -, h0⟩ := h.integral_crPairing_of_contDiff hc hpq χ v
    ((φ.hasCompactSupport_normed (μ := volume)).contDiff_convolution_left _ φ.contDiff_normed hg)
  have e (e : ℂ) (w : ℂ → V) (hw : ∀ z ∉ tsupport (χ : ℂ → ℝ), w z = 0) :
      ∫ z, crPairing v (w z) (fderiv ℝ
        (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (U : Set ℂ).indicator J) z e) =
      ∫ z, crPairing v (w z) ((φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (U : Set ℂ).indicator (fun z => DJ z e)) z) := by
    refine integral_congr_ae (.of_forall fun z => ?_)
    dsimp only
    by_cases hz : z ∈ tsupport (χ : ℂ → ℝ)
    · rw [fderiv_normed_convolution_indicator_apply hwJ hJpU hDJU hp1 φ (hball z hz)]
    · simp [hw z hz]
  rwa [e 1 _ fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz],
    e I _ fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]] at h0

/-- The fields `χ ξ` and `χ J ξ` paired with the derivative of `J` lie in the conjugate exponent
of `p`, when `J` is locally bounded and `1/p + 1/q ≤ 1`. -/
private theorem IsWeakCRSolution.memLp_conjExponent_smul (h : IsWeakCRSolution q Ω J DJ S ξ η)
    (hJ : MemLpLoc ⊤ Ω J) (hpq : p⁻¹ + q⁻¹ ≤ 1) (χ : 𝓓(Ω, ℝ)) :
    MemLp (fun z => χ z • ξ z) p.conjExponent volume ∧
      MemLp (fun z => χ z • J z (ξ z)) p.conjExponent volume := by
  have hp1 : 1 ≤ p := ENNReal.inv_le_one.1 (le_self_add.trans hpq)
  have : Fact (1 ≤ p) := ⟨hp1⟩
  have hp'q : p.conjExponent ≤ q := by
    have h1 : p⁻¹ + p.conjExponent⁻¹ = 1 := by
      rw [ENNReal.HolderTriple.inv_add_inv_eq_inv p p.conjExponent 1, inv_one]
    exact ENNReal.inv_le_inv.1 (ENNReal.le_of_add_le_add_left
      (ENNReal.inv_ne_top.2 (zero_lt_one.trans_le hp1).ne') (h1 ▸ hpq))
  exact ⟨memLp_testFunction_smul χ (h.memLpLoc.mono_exponent hp'q),
    memLp_testFunction_smul χ ((hJ.clm_apply h.memLpLoc).mono_exponent hp'q)⟩

/-- A sequence of bumps whose radii are less than `δ` and tend to zero. -/
private theorem exists_seq_contDiffBump_rOut_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ φ : ℕ → ContDiffBump (0 : ℂ), Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) ∧
      ∀ n, (φ n).rOut < δ :=
  ⟨fun n => ⟨δ / (n + 2) / 2, δ / (n + 2), by positivity, half_lt_self (by positivity)⟩,
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop),
    fun n => div_lt_self hδ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])⟩

/-- **The weak equation tested against `χ Jᵀ v`.** The identity of
`IsWeakCRSolution.integral_crPairing_of_contDiff` also holds for the coefficient `J` itself, paired
with its weak derivative `DJ`, when `J` is locally bounded and `p < ∞`. The proof applies it to the
mollifications of `J` and passes to the limit. -/
private theorem IsWeakCRSolution.integral_crPairing_coeff
    (h : IsWeakCRSolution q Ω J DJ S ξ η) (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hJ : MemLpLoc ⊤ Ω J) (hpq : p⁻¹ + q⁻¹ ≤ 1) (χ : 𝓓(Ω, ℝ)) (v : V) :
    Integrable (fun z => crPairing v (fderiv ℝ χ z 1 • ξ z + fderiv ℝ χ z I • J z (ξ z) +
        χ z • (DJ z I (ξ z) - S z (ξ z) + η z)) (J z)) ∧
      Integrable (fun z => crPairing v (χ z • ξ z) (DJ z 1)) ∧
      Integrable (fun z => crPairing v (χ z • J z (ξ z)) (DJ z I)) ∧
    (∫ z, crPairing v (fderiv ℝ χ z 1 • ξ z + fderiv ℝ χ z I • J z (ξ z) +
          χ z • (DJ z I (ξ z) - S z (ξ z) + η z)) (J z)) +
        (∫ z, crPairing v (χ z • ξ z) (DJ z 1)) +
        ∫ z, crPairing v (χ z • J z (ξ z)) (DJ z I) = 0 := by
  have hK : IsCompact (tsupport (χ : ℂ → ℝ)) := χ.hasCompactSupport
  have hp1 : 1 ≤ p := ENNReal.inv_le_one.1 (le_self_add.trans hpq)
  have : Fact (1 ≤ p) := ⟨hp1⟩
  obtain ⟨hb₁, hb₂⟩ := h.memLp_conjExponent_smul hJ hpq χ
  have hw₁ (z : ℂ) (hz : z ∉ tsupport (χ : ℂ → ℝ)) : χ z • ξ z = 0 := by
    simp [image_eq_zero_of_notMem_tsupport hz]
  have hw₂ (z : ℂ) (hz : z ∉ tsupport (χ : ℂ → ℝ)) : χ z • J z (ξ z) = 0 := by
    simp [image_eq_zero_of_notMem_tsupport hz]
  have ha := h.integrable_crPairingField hc hpq χ
  -- the zero extensions of `J` and `DJ` off a neighbourhood `U` of the support of `χ`
  obtain ⟨U, δ, hδ, hUc, hUΩ, hball⟩ := exists_opens_closedBall_subset hK χ.tsupport_subset
  have hKU (z : ℂ) (hz : z ∈ tsupport (χ : ℂ → ℝ)) : z ∈ U :=
    hball z hz 0 hδ (mem_closedBall_self le_rfl)
  have hUm : MeasurableSet (U : Set ℂ) := U.isOpen.measurableSet
  have hJpU : MemLp J p (volume.restrict U) :=
    hc.memLpLoc_coeff.memLp_restrict_of_isCompact_closure hUc hUΩ
  have hDJU : MemLp DJ p (volume.restrict U) :=
    hc.memLpLoc_deriv.memLp_restrict_of_isCompact_closure hUc hUΩ
  have hg : MemLp ((U : Set ℂ).indicator J) ⊤ volume :=
    (memLp_indicator_iff_restrict hUm.nullMeasurableSet).2
      (hJ.memLp_restrict_of_isCompact_closure hUc hUΩ)
  have hDg (e : ℂ) : MemLp ((U : Set ℂ).indicator (fun z => DJ z e)) p volume :=
    (memLp_indicator_iff_restrict hUm.nullMeasurableSet).2 (memLp_apply hDJU e)
  have hwJ : HasWeakFDerivOn volume U J DJ :=
    hc.hasWeakFDerivOn.mono fun x hx => hUΩ (subset_closure hx)
  -- mollifiers of radius less than `δ`
  obtain ⟨φ, hφ, hφδ⟩ := exists_seq_contDiffBump_rOut_lt hδ
  have key := integral_add_eq_zero_of_forall_normed_convolution (crPairing v)
    (memLp_one_iff_integrable.2 ha) hb₁ hb₂ hg (hDg 1) (hDg I) hφ fun n =>
      h.integral_crPairing_normed_convolution hc hpq χ v hwJ hJpU hDJU hp1
        (hg.locallyIntegrable le_top) (φ n) fun z hz => hball z hz _ (hφδ n)
  -- off `U` the fields vanish, so the zero extensions can be replaced by `J` and `DJ`
  have eU (w : ℂ → V) (hw : ∀ z ∉ tsupport (χ : ℂ → ℝ), w z = 0) (f : ℂ → V →L[ℝ] V) (z : ℂ) :
      crPairing v (w z) ((U : Set ℂ).indicator f z) = crPairing v (w z) (f z) := by
    by_cases hz : z ∈ (U : Set ℂ)
    · simp only [Set.indicator_of_mem hz]
    · simp [hw z fun h' => hz (hKU z h')]
  have ha0 (z : ℂ) (hz : z ∉ tsupport (χ : ℂ → ℝ)) : fderiv ℝ χ z 1 • ξ z +
      fderiv ℝ χ z I • J z (ξ z) + χ z • (DJ z I (ξ z) - S z (ξ z) + η z) = 0 := by
    simp [image_eq_zero_of_notMem_tsupport hz, fderiv_of_notMem_tsupport ℝ hz]
  have hP := memLp_one_iff_integrable.1
    ((crPairing v).memLp_of_bilin 1 (memLp_one_iff_integrable.2 ha) hg)
  have hQ₁ := memLp_one_iff_integrable.1 ((crPairing v).memLp_of_bilin 1 hb₁ (hDg 1))
  have hQ₂ := memLp_one_iff_integrable.1 ((crPairing v).memLp_of_bilin 1 hb₂ (hDg I))
  rw [integral_congr_ae (.of_forall (eU _ ha0 J)), integral_congr_ae (.of_forall (eU _ hw₁ _)),
    integral_congr_ae (.of_forall (eU _ hw₂ _))] at key
  exact ⟨hP.congr (.of_forall (eU _ ha0 J)), hQ₁.congr (.of_forall (eU _ hw₁ _)),
    hQ₂.congr (.of_forall (eU _ hw₂ _)), key⟩

/-! ### The divergence-form equation -/

omit [FiniteDimensional ℝ V] in
/-- The pointwise identity behind the divergence form, at a point where `J² = -1` if it lies in
`Ω`: the pairing of `v` with `Δψ ξ + ∂_s ψ F + ∂_t ψ G` is the pairing for the test function
`(∂_s ψ) v` minus the pairings for `(∂_t ψ) Jᵀ v`. -/
private theorem inner_divergenceForm_eq (v : V) (ψ : 𝓓(Ω, ℝ)) (z : ℂ)
    (hJJ : z ∈ Ω → J z * J z = -1) :
    ⟪v, Δ (ψ : ℂ → ℝ) z • ξ z⟫_ℝ + ⟪v, fderiv ℝ (ψ : ℂ → ℝ) z 1 • (η z + DJ z I (ξ z) - S z (ξ z)) +
      fderiv ℝ (ψ : ℂ → ℝ) z I • (-J z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) -
        DJ z I (J z (ξ z)))⟫_ℝ =
      crPairing v (fderiv ℝ (∂_{(1 : ℂ)} ψ : 𝓓(Ω, ℝ)) z 1 • ξ z +
        fderiv ℝ (∂_{(1 : ℂ)} ψ : 𝓓(Ω, ℝ)) z I • J z (ξ z) +
          (∂_{(1 : ℂ)} ψ : 𝓓(Ω, ℝ)) z • (DJ z I (ξ z) - S z (ξ z) + η z))
        (ContinuousLinearMap.id ℝ V) -
      (crPairing v (fderiv ℝ (∂_{I} ψ : 𝓓(Ω, ℝ)) z 1 • ξ z +
          fderiv ℝ (∂_{I} ψ : 𝓓(Ω, ℝ)) z I • J z (ξ z) +
            (∂_{I} ψ : 𝓓(Ω, ℝ)) z • (DJ z I (ξ z) - S z (ξ z) + η z)) (J z) +
        crPairing v ((∂_{I} ψ : 𝓓(Ω, ℝ)) z • ξ z) (DJ z 1) +
        crPairing v ((∂_{I} ψ : 𝓓(Ω, ℝ)) z • J z (ξ z)) (DJ z I)) := by
  have hc (e : ℂ) : ⇑(∂_{e} ψ : 𝓓(Ω, ℝ)) = fun w => fderiv ℝ (ψ : ℂ → ℝ) w e :=
    funext (TestFunction.lineDerivOp_apply_eq_fderiv ψ e)
  have hd : DifferentiableAt ℝ (fderiv ℝ (ψ : ℂ → ℝ)) z :=
    (ψ.contDiff.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero z
  -- mixed second derivatives agree
  have hsymm : fderiv ℝ (fun w => fderiv ℝ (ψ : ℂ → ℝ) w 1) z I =
      fderiv ℝ (fun w => fderiv ℝ (ψ : ℂ → ℝ) w I) z 1 := by
    have h := TestFunction.lineDeriv_lineDerivOp_comm ψ 1 I z
    rwa [TestFunction.lineDeriv_eq_fderiv, TestFunction.lineDeriv_eq_fderiv, hc, hc] at h
  -- `J (J ξ) = -ξ` wherever the second derivative in `t` does not vanish
  have hJJξ : fderiv ℝ (fun w => fderiv ℝ (ψ : ℂ → ℝ) w I) z I * ⟪v, J z (J z (ξ z))⟫_ℝ =
      -(fderiv ℝ (fun w => fderiv ℝ (ψ : ℂ → ℝ) w I) z I * ⟪v, ξ z⟫_ℝ) := by
    by_cases hz : z ∈ Ω
    · have h2 := congrArg (fun T : V →L[ℝ] V => T (ξ z)) (hJJ hz)
      simp only [mul_apply_eq_comp, neg_apply, one_apply_eq_self] at h2
      rw [h2, inner_neg_right, mul_neg]
    · have hz' : z ∉ tsupport (∂_{I} ψ : 𝓓(Ω, ℝ)) := fun h' => hz ((∂_{I} ψ).tsupport_subset h')
      rw [← hc, fderiv_of_notMem_tsupport ℝ hz']
      simp
  rw [hc, hc, laplacian_eq_fderiv_fderiv_apply_one_add_fderiv_fderiv_apply_I hd]
  simp only [map_add, map_sub, map_smul, add_apply, sub_apply, FunLike.coe_smul, Pi.smul_apply,
    smul_eq_mul, crPairing_apply, ContinuousLinearMap.id_apply, inner_add_right, inner_sub_right,
    inner_neg_right, real_inner_smul_right, add_smul]
  linear_combination (-⟪v, J z (ξ z)⟫_ℝ) * hsymm + hJJξ

/-- **Weak solutions solve a divergence-form Laplace equation.** Let `DJ` be a weak derivative of
the coefficient `J` on `Ω`, with `J` locally bounded, `J² = -1` almost everywhere on `Ω`, and `J`,
`DJ`, `S` locally `Lᵖ`, and let `1/p + 1/q ≤ 1`. If `ξ ∈ L^q_loc` is a weak solution of
`∂_s ξ + J ∂_t ξ + S ξ = η` on `Ω`, then `Δ ξ = ∂_s F + ∂_t G` weakly on `Ω`, where
`F = η + (∂_t J) ξ - S ξ` and `G = -J F - (∂_s J) ξ - (∂_t J) (J ξ)`: for every real test
function `ψ`,

`∫ Δψ • ξ = -∫ (∂_s ψ • F + ∂_t ψ • G)`.

This is the weak form of applying `∂_s - J ∂_t` to the equation. -/
theorem IsWeakCRSolution.integral_laplacian_smul_eq (h : IsWeakCRSolution q Ω J DJ S ξ η)
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJ : MemLpLoc ⊤ Ω J)
    (hJJ : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) (hpq : p⁻¹ + q⁻¹ ≤ 1) (ψ : 𝓓(Ω, ℝ)) :
    ∫ z, Δ (ψ : ℂ → ℝ) z • ξ z =
      -∫ z, (fderiv ℝ (ψ : ℂ → ℝ) z 1 • (η z + DJ z I (ξ z) - S z (ξ z)) +
        fderiv ℝ (ψ : ℂ → ℝ) z I • (-J z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) -
          DJ z I (J z (ξ z)))) := by
  have hloc := Ω.isOpen.isLocallyClosed
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hl (A : ℂ → V →L[ℝ] V) (hA : MemLpLoc p Ω A) {w : ℂ → V} (hw : MemLpLoc q Ω w) :
      MemLpLoc 1 Ω (fun z => A z (w z)) :=
    (memLpLoc_one_iff_locallyIntegrableOn hloc).2 (hA.locallyIntegrableOn_clm_apply hw hpq hloc)
  have hDJ (e : ℂ) : MemLpLoc p Ω (fun z => DJ z e) :=
    hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) e)
  have hF : MemLpLoc 1 Ω (fun z => η z + DJ z I (ξ z) - S z (ξ z)) :=
    (((memLpLoc_one_iff_locallyIntegrableOn hloc).2 h.locallyIntegrableOn).add
      (hl _ (hDJ I) h.memLpLoc)).sub (hl _ hc.memLpLoc_zeroth h.memLpLoc)
  have hG : MemLpLoc 1 Ω (fun z => -J z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) -
      DJ z I (J z (ξ z))) :=
    ((hJ.clm_apply hF).neg.sub (hl _ (hDJ 1) h.memLpLoc)).sub
      (hl _ (hDJ I) (hJ.clm_apply (r := q) h.memLpLoc))
  have hd (e : ℂ) : (fun z => fderiv ℝ (ψ : ℂ → ℝ) z e) = ⇑(∂_{e} ψ : 𝓓(Ω, ℝ)) :=
    funext fun z => (TestFunction.lineDerivOp_apply_eq_fderiv ψ e z).symm
  have hL : Integrable (fun z => Δ (ψ : ℂ → ℝ) z • ξ z) := by
    have h1 := memLp_testFunction_smul (LineDeriv.laplacianCLM ℝ ℂ 𝓓(Ω, ℝ) ψ)
      (h.memLpLoc.mono_exponent hq1)
    simp only [TestFunction.laplacianCLM_apply] at h1
    exact memLp_one_iff_integrable.1 h1
  have hR : Integrable (fun z => fderiv ℝ (ψ : ℂ → ℝ) z 1 • (η z + DJ z I (ξ z) - S z (ξ z)) +
      fderiv ℝ (ψ : ℂ → ℝ) z I • (-J z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) -
        DJ z I (J z (ξ z)))) := by
    have h1 := memLp_testFunction_smul (∂_{(1 : ℂ)} ψ) hF
    have h2 := memLp_testFunction_smul (∂_{I} ψ) hG
    rw [← hd] at h1 h2
    exact memLp_one_iff_integrable.1 (h1.add h2)
  refine ext_inner_left ℝ fun v => ?_
  rw [← integral_inner hL v, inner_neg_right, ← integral_inner hR v, eq_neg_iff_add_eq_zero,
    ← integral_add (hL.const_inner v) (hR.const_inner v)]
  -- the weak equation tested against `(∂_s ψ) v` and against `(∂_t ψ) Jᵀ v`
  obtain ⟨hP₁, -, -, h₁⟩ := h.integral_crPairing_of_contDiff hc hpq (∂_{(1 : ℂ)} ψ) v
    (contDiff_const (c := ContinuousLinearMap.id ℝ V))
  simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, map_zero,
    integral_zero, add_zero] at h₁
  obtain ⟨hP₂, hQ₁, hQ₂, h₂⟩ := h.integral_crPairing_coeff hc hJ hpq (∂_{I} ψ) v
  have hae : ∀ᵐ z, z ∈ Ω → J z * J z = -1 := (ae_restrict_iff' Ω.isOpen.measurableSet).1 hJJ
  rw [integral_congr_ae (hae.mono fun z hz => inner_divergenceForm_eq v ψ z hz),
    integral_sub hP₁ ?_, integral_add ?_ hQ₂, integral_add hP₂ hQ₁]
  · linarith
  · exact hP₂.add hQ₁
  · exact (hP₂.add hQ₁).add hQ₂

/-- **Order-zero regularity of weak solutions** (McDuff–Salamon, Lemma B.4.6). Let `DJ` be a weak
derivative of the coefficient `J` on `Ω`, with `J` locally bounded, `J² = -1` almost everywhere on
`Ω`, and `J`, `DJ`, `S` locally `Lᵖ`. Let `1/p + 1/q = 1/r` with `1 < r < ∞`. If `ξ ∈ L^q_loc` is a
weak solution of `∂_s ξ + J ∂_t ξ + S ξ = η` on `Ω` with `η ∈ Lʳ_loc`, then `ξ ∈ W^{1,r}_loc`. -/
theorem IsWeakCRSolution.memWkpLoc_one (h : IsWeakCRSolution q Ω J DJ S ξ η)
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJ : MemLpLoc ⊤ Ω J)
    (hJJ : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) [ENNReal.HolderTriple p q r] (hr : 1 < r)
    (hr_top : r ≠ ⊤) (hη : MemLpLoc r Ω η) : MemWkpLoc r Ω 1 ξ := by
  have hpq : p⁻¹ + q⁻¹ ≤ 1 := by
    rw [ENNReal.HolderTriple.inv_add_inv_eq_inv p q r]
    exact (ENNReal.inv_lt_one.2 hr).le
  have hrq : r ≤ q := ENNReal.HolderTriple.le q p r
  have hDJ (e : ℂ) : MemLpLoc p Ω (fun z => DJ z e) :=
    hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) e)
  have hF : MemLpLoc r Ω (fun z => η z + DJ z I (ξ z) - S z (ξ z)) :=
    (hη.add ((hDJ I).clm_apply h.memLpLoc)).sub (hc.memLpLoc_zeroth.clm_apply h.memLpLoc)
  have hG : MemLpLoc r Ω (fun z => -J z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) -
      DJ z I (J z (ξ z))) :=
    ((hJ.clm_apply hF).neg.sub ((hDJ 1).clm_apply h.memLpLoc)).sub
      ((hDJ I).clm_apply (hJ.clm_apply (r := q) h.memLpLoc))
  exact memWkpLoc_one_of_forall_integral_laplacian_smul_eq hr hr_top
    (h.memLpLoc.locallyIntegrableOn (hr.le.trans hrq) Ω.isOpen.isLocallyClosed) hF hG
    fun ψ => h.integral_laplacian_smul_eq hc hJ hJJ hpq ψ

end TauCeti
