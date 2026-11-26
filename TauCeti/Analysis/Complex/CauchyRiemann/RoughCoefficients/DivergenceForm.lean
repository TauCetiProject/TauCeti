/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
public import TauCeti.Analysis.Complex.Wirtinger.DivergenceLaplace.Basic
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.Sobolev.Mollification.Interior
import TauCeti.Data.ENNReal.Holder
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.Topology.MetricSpace.Thickening
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
`Lʳ_loc` (`TauCeti.IsWeakCRSolution.memWkpLoc_one_of_memLpLoc_top`). This is the order-zero step
of the interior regularity theory of real Cauchy–Riemann operators with Sobolev coefficients
(McDuff–Salamon, Lemma B.4.6); for `p > 2` the coefficient `J` is continuous, hence locally
bounded, by Morrey's embedding. Here only the local boundedness of `J` is assumed; the form with
`p > 2` and `1/p + 1/q ≤ 1/r` is `TauCeti.IsWeakCRSolution.memWkpLoc_one`.

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
* `TauCeti.IsWeakCRSolution.memWkpLoc_one_of_memLpLoc_top`: for a locally bounded coefficient `J`,
  a weak solution in `L^q_loc` with right-hand side in `Lʳ_loc`, `1/r = 1/p + 1/q` and
  `1 < r < ∞`, lies in `W^{1,r}_loc`.

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

omit [FiniteDimensional ℝ V] in
/-- A test function times any field vanishes off the support of the test function. -/
private theorem smul_eq_zero_of_notMem_tsupport (χ : 𝓓(Ω, ℝ)) (w : ℂ → V) {z : ℂ}
    (hz : z ∉ tsupport (χ : ℂ → ℝ)) : χ z • w z = 0 := by
  simp [image_eq_zero_of_notMem_tsupport hz]

omit [FiniteDimensional ℝ V] in
/-- The field `a = ∂_s χ ξ + ∂_t χ J ξ + χ (η + (∂_t J) ξ - S ξ)` vanishes off the support
of `χ`. -/
private theorem crPairingField_eq_zero_of_notMem_tsupport (χ : 𝓓(Ω, ℝ)) {z : ℂ}
    (hz : z ∉ tsupport (χ : ℂ → ℝ)) : fderiv ℝ χ z 1 • ξ z + fderiv ℝ χ z I • J z (ξ z) +
      χ z • (η z + DJ z I (ξ z) - S z (ξ z)) = 0 := by
  simp [image_eq_zero_of_notMem_tsupport hz, fderiv_of_notMem_tsupport ℝ hz]

omit [FiniteDimensional ℝ V] in
/-- A test function times a locally `Lˢ` function on `Ω` is in `Lˢ` of the plane. -/
private theorem memLp_testFunction_smul {s : ℝ≥0∞} {W : ℂ → V} (c : 𝓓(Ω, ℝ))
    (hW : MemLpLoc s Ω W) : MemLp (fun z => c z • W z) s volume :=
  hW.memLp_smul_of_hasCompactSupport c.continuous c.hasCompactSupport c.tsupport_subset

/-- The field `F = η + (∂_t J) ξ - S ξ` is locally `Lˢ` when `η` is, for a Hölder triple
`1/p + 1/q = 1/t` with `s ≤ t`. -/
theorem IsWeakCRSolution.memLpLoc_divergenceForm_fst {s t : ℝ≥0∞}
    [ENNReal.HolderTriple p q t] (h : IsWeakCRSolution q Ω J DJ S ξ η)
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hst : s ≤ t) (hη : MemLpLoc s Ω η) :
    MemLpLoc s Ω (fun z => η z + DJ z I (ξ z) - S z (ξ z)) :=
  (hη.add (((hc.memLpLoc_deriv_apply I).clm_apply h.memLpLoc).mono_exponent hst)).sub
    ((hc.memLpLoc_zeroth.clm_apply h.memLpLoc).mono_exponent hst)

/-- The field `G = -J F - (∂_s J) ξ - (∂_t J) (J ξ)` is locally `Lˢ` when `η` is and `J` is
locally bounded, for a Hölder triple `1/p + 1/q = 1/t` with `s ≤ t`. -/
theorem IsWeakCRSolution.memLpLoc_divergenceForm_snd {s t : ℝ≥0∞}
    [ENNReal.HolderTriple p q t] (h : IsWeakCRSolution q Ω J DJ S ξ η)
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJ : MemLpLoc ⊤ Ω J) (hst : s ≤ t)
    (hη : MemLpLoc s Ω η) :
    MemLpLoc s Ω (fun z => -J z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) -
      DJ z I (J z (ξ z))) :=
  ((hJ.clm_apply (h.memLpLoc_divergenceForm_fst hc hst hη)).neg.sub
    (((hc.memLpLoc_deriv_apply 1).clm_apply h.memLpLoc).mono_exponent hst)).sub
    (((hc.memLpLoc_deriv_apply I).clm_apply (hJ.clm_apply (r := q) h.memLpLoc)).mono_exponent hst)

/-! ### Testing the weak equation against `χ Aᵀ v` -/

/-- The field `a = ∂_s χ ξ + ∂_t χ J ξ + χ (η + (∂_t J) ξ - S ξ)` paired with the coefficient is
integrable. -/
private theorem IsWeakCRSolution.integrable_crPairingField
    (h : IsWeakCRSolution q Ω J DJ S ξ η) (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (χ : 𝓓(Ω, ℝ)) :
    Integrable (fun z => fderiv ℝ χ z 1 • ξ z + fderiv ℝ χ z I • J z (ξ z) +
      χ z • (η z + DJ z I (ξ z) - S z (ξ z))) := by
  have hξ1 : MemLpLoc 1 Ω ξ :=
    h.memLpLoc.mono_exponent (ENNReal.one_le_right_of_inv_add_inv_le_one hpq)
  have hJξ := hc.memLpLoc_coeff.memLpLoc_one_clm_apply h.memLpLoc hpq
  have : ENNReal.HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ := ⟨(inv_inv _).symm⟩
  have hW := h.memLpLoc_divergenceForm_fst hc (ENNReal.one_le_inv.2 hpq)
    ((memLpLoc_one_iff_locallyIntegrableOn Ω.isOpen.isLocallyClosed).2 h.locallyIntegrableOn)
  have h1 := memLp_testFunction_smul (∂_{(1 : ℂ)} χ) hξ1
  have h2 := memLp_testFunction_smul (∂_{I} χ) hJξ
  have h3 := memLp_testFunction_smul χ hW
  rw [TestFunction.coe_lineDerivOp_eq_fderiv] at h1 h2
  exact memLp_one_iff_integrable.1 ((h1.add h2).add h3)

/-- **The test function `χ Aᵀ v`.** For a smooth field `A` of operators, a test function `χ` and a
vector `v`, the function `χ Aᵀ v` is a test function `Φ`, and pointwise
`⟪D* Φ, ξ⟫ - ⟪Φ, η⟫ = -(⟪v, A a⟫ + ⟪v, A' 1 (χ ξ)⟫ + ⟪v, A' I (χ J ξ)⟫)`, where `A'` is the
derivative of `A` and `a = ∂_s χ ξ + ∂_t χ J ξ + χ (η + (∂_t J) ξ - S ξ)`. -/
private theorem exists_testFunction_inner_crFormalAdjoint_sub_inner (χ : 𝓓(Ω, ℝ)) (v : V)
    {A : ℂ → V →L[ℝ] V} (hA : ContDiff ℝ ∞ A) :
    ∃ Φ : 𝓓(Ω, V), ∀ z, ⟪crFormalAdjoint J DJ S Φ z, ξ z⟫_ℝ - ⟪(Φ : ℂ → V) z, η z⟫_ℝ =
      -(crPairing v (fderiv ℝ χ z 1 • ξ z + fderiv ℝ χ z I • J z (ξ z) +
          χ z • (η z + DJ z I (ξ z) - S z (ξ z))) (A z) +
        crPairing v (χ z • ξ z) (fderiv ℝ A z 1) +
        crPairing v (χ z • J z (ξ z)) (fderiv ℝ A z I)) := by
  let adj : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V := ContinuousLinearMap.adjointRealCLM
  have hB : ContDiff ℝ ∞ (fun z => adj (A z) v) :=
    (adj.contDiff.comp hA).clm_apply contDiff_const
  let Φ : 𝓓(Ω, V) := ⟨⇑χ • fun z => adj (A z) v, χ.contDiff.smul hB,
    χ.hasCompactSupport.smul_right, (tsupport_smul_subset_left _ _).trans χ.tsupport_subset⟩
  have hΦ : (Φ : ℂ → V) = ⇑χ • fun z => adj (A z) v := TestFunction.coe_mk
  have hΦd (z e : ℂ) : fderiv ℝ (Φ : ℂ → V) z e =
      fderiv ℝ χ z e • adj (A z) v + χ z • adj (fderiv ℝ A z e) v := by
    have h1 : HasFDerivAt (fun z => adj (A z)) (adj.comp (fderiv ℝ A z)) z :=
      adj.hasFDerivAt.comp z (hA.differentiable (by simp) z).hasFDerivAt
    rw [hΦ, ((χ.contDiff.differentiable (by simp) z).hasFDerivAt.smul
      (h1.clm_apply (hasFDerivAt_const v z))).fderiv]
    simp [add_comm]
  refine ⟨Φ, fun z => ?_⟩
  rw [inner_crFormalAdjoint, hΦd, hΦd, hΦ]
  simp only [map_add, map_sub, map_smul, add_apply, sub_apply, FunLike.coe_smul, Pi.smul_apply,
    Pi.smul_apply', smul_eq_mul, crPairing_apply, adj, ContinuousLinearMap.adjointRealCLM_apply,
    inner_add_left, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left]
  ring

/-- **The weak equation tested against `χ Aᵀ v`.** For a smooth field `A` of operators, a test
function `χ` and a vector `v`, the function `χ Aᵀ v` is a test function, and the weak equation
tested against it reads `∫ ⟪v, A a⟫ + ∫ ⟪v, A' 1 (χ ξ)⟫ + ∫ ⟪v, A' I (χ J ξ)⟫ = 0`, where `A'`
is the derivative of `A` and `a = ∂_s χ ξ + ∂_t χ J ξ + χ (η + (∂_t J) ξ - S ξ)`. -/
private theorem IsWeakCRSolution.integral_crPairing_of_contDiff
    (h : IsWeakCRSolution q Ω J DJ S ξ η) (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (χ : 𝓓(Ω, ℝ)) (v : V) {A : ℂ → V →L[ℝ] V} (hA : ContDiff ℝ ∞ A) :
    Integrable (fun z => crPairing v (fderiv ℝ χ z 1 • ξ z + fderiv ℝ χ z I • J z (ξ z) +
        χ z • (η z + DJ z I (ξ z) - S z (ξ z))) (A z)) ∧
      Integrable (fun z => crPairing v (χ z • ξ z) (fderiv ℝ A z 1)) ∧
      Integrable (fun z => crPairing v (χ z • J z (ξ z)) (fderiv ℝ A z I)) ∧
      (∫ z, crPairing v (fderiv ℝ χ z 1 • ξ z + fderiv ℝ χ z I • J z (ξ z) +
          χ z • (η z + DJ z I (ξ z) - S z (ξ z))) (A z)) +
        (∫ z, crPairing v (χ z • ξ z) (fderiv ℝ A z 1)) +
        ∫ z, crPairing v (χ z • J z (ξ z)) (fderiv ℝ A z I) = 0 := by
  have hK : IsCompact (tsupport (χ : ℂ → ℝ)) := χ.hasCompactSupport
  have hξ1 : MemLpLoc 1 Ω ξ :=
    h.memLpLoc.mono_exponent (ENNReal.one_le_right_of_inv_add_inv_le_one hpq)
  have hJξ := hc.memLpLoc_coeff.memLpLoc_one_clm_apply h.memLpLoc hpq
  have ha := h.integrable_crPairingField hc hpq χ
  have hb₁ : Integrable (fun z => χ z • ξ z) :=
    memLp_one_iff_integrable.1 (memLp_testFunction_smul χ hξ1)
  have hb₂ : Integrable (fun z => χ z • J z (ξ z)) :=
    memLp_one_iff_integrable.1 (memLp_testFunction_smul χ hJξ)
  have hP := (crPairing v).integrable_of_bilin_of_continuousOn ha.integrableOn hK
    (.of_forall fun z hz => crPairingField_eq_zero_of_notMem_tsupport χ hz)
    hA.continuous.continuousOn
  have hA' (e : ℂ) : ContinuousOn (fun z => fderiv ℝ A z e) (tsupport (χ : ℂ → ℝ)) :=
    ((hA.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn
  have hQ₁ := (crPairing v).integrable_of_bilin_of_continuousOn hb₁.integrableOn hK
    (.of_forall fun z hz => smul_eq_zero_of_notMem_tsupport χ ξ hz) (hA' 1)
  have hQ₂ := (crPairing v).integrable_of_bilin_of_continuousOn hb₂.integrableOn hK
    (.of_forall fun z hz => smul_eq_zero_of_notMem_tsupport χ (fun z => J z (ξ z)) hz)
    (hA' I)
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
        χ z • (η z + DJ z I (ξ z) - S z (ξ z)))
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
    · rw [hwJ.fderiv_normed_convolution_indicator_apply hJpU hDJU hp1 hp1 φ (hball z hz)]
    · simp [hw z hz]
  rwa [e 1 _ fun z hz => smul_eq_zero_of_notMem_tsupport χ ξ hz,
    e I _ fun z hz => smul_eq_zero_of_notMem_tsupport χ (fun z => J z (ξ z)) hz] at h0

/-- The fields `χ ξ` and `χ J ξ` paired with the derivative of `J` lie in the conjugate exponent
of `p`, when `J` is locally bounded and `1/p + 1/q ≤ 1`. -/
private theorem IsWeakCRSolution.memLp_conjExponent_smul (h : IsWeakCRSolution q Ω J DJ S ξ η)
    (hJ : MemLpLoc ⊤ Ω J) (hpq : p⁻¹ + q⁻¹ ≤ 1) (χ : 𝓓(Ω, ℝ)) :
    MemLp (fun z => χ z • ξ z) p.conjExponent volume ∧
      MemLp (fun z => χ z • J z (ξ z)) p.conjExponent volume := by
  have hp'q := ENNReal.conjExponent_le_of_inv_add_inv_le_one hpq
  exact ⟨memLp_testFunction_smul χ (h.memLpLoc.mono_exponent hp'q),
    memLp_testFunction_smul χ ((hJ.clm_apply h.memLpLoc).mono_exponent hp'q)⟩

/-- **The weak equation tested against `χ Jᵀ v`.** The identity of
`IsWeakCRSolution.integral_crPairing_of_contDiff` also holds for the coefficient `J` itself, paired
with its weak derivative `DJ`, when `J` is locally bounded. -/
private theorem IsWeakCRSolution.integral_crPairing_coeff
    (h : IsWeakCRSolution q Ω J DJ S ξ η) (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hJ : MemLpLoc ⊤ Ω J) (hpq : p⁻¹ + q⁻¹ ≤ 1) (χ : 𝓓(Ω, ℝ)) (v : V) :
    Integrable (fun z => crPairing v (fderiv ℝ χ z 1 • ξ z + fderiv ℝ χ z I • J z (ξ z) +
        χ z • (η z + DJ z I (ξ z) - S z (ξ z))) (J z)) ∧
      Integrable (fun z => crPairing v (χ z • ξ z) (DJ z 1)) ∧
      Integrable (fun z => crPairing v (χ z • J z (ξ z)) (DJ z I)) ∧
    (∫ z, crPairing v (fderiv ℝ χ z 1 • ξ z + fderiv ℝ χ z I • J z (ξ z) +
          χ z • (η z + DJ z I (ξ z) - S z (ξ z))) (J z)) +
        (∫ z, crPairing v (χ z • ξ z) (DJ z 1)) +
        ∫ z, crPairing v (χ z • J z (ξ z)) (DJ z I) = 0 := by
  have hp1 := ENNReal.one_le_left_of_inv_add_inv_le_one hpq
  have : Fact (1 ≤ p) := ⟨hp1⟩
  obtain ⟨hb₁, hb₂⟩ := h.memLp_conjExponent_smul hJ hpq χ
  have hw₁ (z : ℂ) (hz : z ∉ tsupport (χ : ℂ → ℝ)) := smul_eq_zero_of_notMem_tsupport χ ξ hz
  have hw₂ (z : ℂ) (hz : z ∉ tsupport (χ : ℂ → ℝ)) :=
    smul_eq_zero_of_notMem_tsupport χ (fun z => J z (ξ z)) hz
  have ha := h.integrable_crPairingField hc hpq χ
  -- the zero extensions of `J` and `DJ` off a neighbourhood `U` of the support of `χ`
  obtain ⟨U₀, hU₀, δ, hδ, hUc, hUΩ, hball⟩ :=
    IsCompact.exists_isOpen_closedBall_subset χ.hasCompactSupport Ω.isOpen χ.tsupport_subset
  let U : Opens ℂ := ⟨U₀, hU₀⟩
  have hKU (z : ℂ) (hz : z ∈ tsupport (χ : ℂ → ℝ)) : z ∈ U :=
    hball z hz 0 hδ.le (mem_closedBall_self le_rfl)
  have hUm : MeasurableSet (U : Set ℂ) := U.isOpen.measurableSet
  have hJpU : MemLp J p (volume.restrict U) :=
    hc.memLpLoc_coeff.memLp_restrict_of_isCompact_closure hUc hUΩ
  have hDJU : MemLp DJ p (volume.restrict U) :=
    hc.memLpLoc_deriv.memLp_restrict_of_isCompact_closure hUc hUΩ
  have hg : MemLp ((U : Set ℂ).indicator J) ⊤ volume :=
    (memLp_indicator_iff_restrict hUm.nullMeasurableSet).2
      (hJ.memLp_restrict_of_isCompact_closure hUc hUΩ)
  have hDg (e : ℂ) : MemLp ((U : Set ℂ).indicator (fun z => DJ z e)) p volume :=
    (memLp_indicator_iff_restrict hUm.nullMeasurableSet).2
      ((hc.memLpLoc_deriv_apply e).memLp_restrict_of_isCompact_closure hUc hUΩ)
  have hwJ : HasWeakFDerivOn volume U J DJ :=
    hc.hasWeakFDerivOn.mono fun x hx => hUΩ (subset_closure hx)
  have key := integral_add_eq_zero_of_forall_normed_convolution (crPairing v)
    (memLp_one_iff_integrable.2 ha) hb₁ hb₂ hg (hDg 1) (hDg I)
    (ContDiffBump.tendsto_rOut_shrinking hδ) fun n =>
      h.integral_crPairing_normed_convolution hc hpq χ v hwJ hJpU hDJU hp1
        (hg.locallyIntegrable le_top) (ContDiffBump.shrinking hδ n) fun z hz => hball z hz _
          ((ContDiffBump.rOut_shrinking hδ n).trans_le
            (div_le_self hδ.le (le_add_of_nonneg_left n.cast_nonneg)))
  -- off `U` the fields vanish, so the zero extensions can be replaced by `J` and `DJ`
  have eU (w : ℂ → V) (hw : ∀ z ∉ tsupport (χ : ℂ → ℝ), w z = 0) (f : ℂ → V →L[ℝ] V) (z : ℂ) :
      crPairing v (w z) ((U : Set ℂ).indicator f z) = crPairing v (w z) (f z) := by
    by_cases hz : z ∈ (U : Set ℂ)
    · simp only [Set.indicator_of_mem hz]
    · simp [hw z fun h' => hz (hKU z h')]
  have ha0 (z : ℂ) (hz : z ∉ tsupport (χ : ℂ → ℝ)) :=
    crPairingField_eq_zero_of_notMem_tsupport (J := J) (DJ := DJ) (S := S) (ξ := ξ) (η := η) χ hz
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
          (∂_{(1 : ℂ)} ψ : 𝓓(Ω, ℝ)) z • (η z + DJ z I (ξ z) - S z (ξ z)))
        (ContinuousLinearMap.id ℝ V) -
      (crPairing v (fderiv ℝ (∂_{I} ψ : 𝓓(Ω, ℝ)) z 1 • ξ z +
          fderiv ℝ (∂_{I} ψ : 𝓓(Ω, ℝ)) z I • J z (ξ z) +
            (∂_{I} ψ : 𝓓(Ω, ℝ)) z • (η z + DJ z I (ξ z) - S z (ξ z))) (J z) +
        crPairing v ((∂_{I} ψ : 𝓓(Ω, ℝ)) z • ξ z) (DJ z 1) +
        crPairing v ((∂_{I} ψ : 𝓓(Ω, ℝ)) z • J z (ξ z)) (DJ z I)) := by
  have hc := TestFunction.coe_lineDerivOp_eq_fderiv ψ
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
  have : ENNReal.HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ := ⟨(inv_inv _).symm⟩
  have hη : MemLpLoc 1 Ω η :=
    (memLpLoc_one_iff_locallyIntegrableOn Ω.isOpen.isLocallyClosed).2 h.locallyIntegrableOn
  have hF := h.memLpLoc_divergenceForm_fst hc (ENNReal.one_le_inv.2 hpq) hη
  have hG := h.memLpLoc_divergenceForm_snd hc hJ (ENNReal.one_le_inv.2 hpq) hη
  have hL : Integrable (fun z => Δ (ψ : ℂ → ℝ) z • ξ z) := by
    have h1 := memLp_testFunction_smul (LineDeriv.laplacianCLM ℝ ℂ 𝓓(Ω, ℝ) ψ)
      (h.memLpLoc.mono_exponent (ENNReal.one_le_right_of_inv_add_inv_le_one hpq))
    simp only [TestFunction.laplacianCLM_apply] at h1
    exact memLp_one_iff_integrable.1 h1
  have hR : Integrable (fun z => fderiv ℝ (ψ : ℂ → ℝ) z 1 • (η z + DJ z I (ξ z) - S z (ξ z)) +
      fderiv ℝ (ψ : ℂ → ℝ) z I • (-J z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) -
        DJ z I (J z (ξ z)))) := by
    have h1 := memLp_testFunction_smul (∂_{(1 : ℂ)} ψ) hF
    have h2 := memLp_testFunction_smul (∂_{I} ψ) hG
    rw [TestFunction.coe_lineDerivOp_eq_fderiv] at h1 h2
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
theorem IsWeakCRSolution.memWkpLoc_one_of_memLpLoc_top (h : IsWeakCRSolution q Ω J DJ S ξ η)
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJ : MemLpLoc ⊤ Ω J)
    (hJJ : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) [ENNReal.HolderTriple p q r] (hr : 1 < r)
    (hr_top : r ≠ ⊤) (hη : MemLpLoc r Ω η) : MemWkpLoc r Ω 1 ξ := by
  have hpq : p⁻¹ + q⁻¹ ≤ 1 := by
    rw [ENNReal.HolderTriple.inv_add_inv_eq_inv p q r]
    exact (ENNReal.inv_lt_one.2 hr).le
  have hrq : r ≤ q := ENNReal.HolderTriple.le q p r
  exact memWkpLoc_one_of_forall_integral_laplacian_smul_eq hr hr_top
    (h.memLpLoc.locallyIntegrableOn (hr.le.trans hrq) Ω.isOpen.isLocallyClosed)
    (h.memLpLoc_divergenceForm_fst hc (t := r) le_rfl hη)
    (h.memLpLoc_divergenceForm_snd hc hJ (t := r) le_rfl hη)
    fun ψ => h.integral_laplacian_smul_eq hc hJ hJJ hpq ψ

end TauCeti
