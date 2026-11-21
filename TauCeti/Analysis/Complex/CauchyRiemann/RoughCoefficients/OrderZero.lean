/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Complex.Wirtinger.DivergenceLaplace.Basic
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Sobolev.Leibniz
import TauCeti.Analysis.Sobolev.Local.Morrey.Higher
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Analysis.Sobolev.Mollification.Interior
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.Topology.MetricSpace.Thickening

/-!
# Order-zero regularity for real Cauchy–Riemann equations with Sobolev coefficients

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a finite-dimensional real inner product
space. For coefficients `J ∈ W^{1,p}_loc(Ω; End V)` with `J² = -1` and `S ∈ Lᵖ_loc(Ω; End V)`,
`p > 2`, consider a weak solution `ξ ∈ L^q_loc` of

`∂_s ξ + J ∂_t ξ + S ξ = η`

in the sense of `TauCeti.IsWeakCRSolution`. This file proves the order-zero step of interior
regularity (McDuff–Salamon, Lemma B.4.6):

1. *Single Hölder step* (`TauCeti.IsWeakCRSolution.memWkpLoc_one`): if `η ∈ Lʳ_loc` with
   `1 < r < ∞` and `1/p + 1/q ≤ 1/r`, then `ξ ∈ W^{1,r}_loc(Ω)`. No derivative of `ξ` is
   assumed.
2. *Bootstrap across the Sobolev exponent ladder*
   (`TauCeti.IsWeakCRSolution.memWkpLoc_one_of_memLpLoc`): if `1/p + 1/q < 1`, `1 < s ≤ p` with
   `s < ∞` and `η ∈ Lˢ_loc(Ω)`, alternating the single Hölder step with the two-dimensional Sobolev
   embedding decreases `1/q` by `1/2 - 1/p > 0` at each subcritical step (`r₁ < 2`), stopping
   immediately if the product exponent reaches `s`. At the critical exponent `r₁ = 2`, embedding
   `W^{1,2}_loc` into a large finite `L^{t*}_loc` pushes the next product exponent above `2`, and
   for `r₁ > 2` the embedding `W^{1,r₁}_loc ⊂ L^∞_loc` finishes in one final step to yield
   `ξ ∈ W^{1,s}_loc(Ω)`. The coefficient endpoint `p = ∞` is handled by lowering `p` locally to a
   finite exponent above `max 2 s`. In particular `ξ ∈ W^{1,q}_loc(Ω)` when `q ≤ p`, `q < ∞`, and
   `η ∈ L^q_loc(Ω)` (`TauCeti.IsWeakCRSolution.memWkpLoc_one_of_le`), and `ξ ∈ W^{1,p}_loc(Ω)`
   when `p < ∞` and `η ∈ Lᵖ_loc(Ω)` (`TauCeti.IsWeakCRSolution.memWkpLoc_one_self`).

The proof of the single Hölder step rewrites the first-order equation as a divergence-form Laplace
equation for `ξ` with locally `Lʳ` data and applies
`TauCeti.memWkpLoc_one_of_forall_integral_laplacian_smul_eq`. For a real test function `φ` and a
vector `v`, test the weak equation against

`ψ = ∂_s φ • v - ∂_t φ • Jᵀ v`.

Since `J² = -1`, the formal adjoint turns `ψ` into `-Δφ • v` plus terms with at most one
derivative on `φ`, and one obtains `Δξ = ∂_s f + ∂_t g` weakly, with

* `f = η + (∂_t J) ξ - S ξ`,
* `g = J S ξ - J η - (∂_s J) ξ - (∂_t J) J ξ - J (∂_t J) ξ`.

These are locally `Lʳ` by Hölder's inequality, because `J` is locally bounded by Morrey's
embedding (`TauCeti.IsSobolevCRCoefficients.memLpLoc_top_coeff`).

The test field `ψ` is not smooth: it is only as regular as `J`. So the weak equation is first
extended from smooth test functions to bounded compactly supported test fields with a weak
derivative in `Lˢ`, `1/s + 1/q ≤ 1`
(`TauCeti.IsWeakCRSolution.integral_inner_eq_of_hasWeakFDerivOn`). The proof mollifies the test
field: the mollifications are smooth test functions, their derivatives are the mollifications of
the weak derivative, and every pairing in the weak equation converges via
`ContinuousLinearMap.tendsto_integral_bilin_normed_convolution`—by strong `Lˢ` convergence of the
derivative mollifications when `s < ∞`, and by weak-star convergence against `L¹` for the bounded
test field itself and for the derivatives at `s = ∞`.

## Main results

* `TauCeti.IsWeakCRSolution.integral_inner_eq_of_hasWeakFDerivOn`: the weak equation holds
  against bounded compactly supported Sobolev test fields.
* `TauCeti.IsSobolevCRCoefficients.memLpLoc_top_coeff`: for `p > 2` a `W^{1,p}_loc` coefficient
  `J` is locally bounded.
* `TauCeti.IsWeakCRSolution.memWkpLoc_one`: single Hölder step of order-zero interior regularity.
* `TauCeti.IsWeakCRSolution.memWkpLoc_one_of_memLpLoc`,
  `TauCeti.IsWeakCRSolution.memWkpLoc_one_of_le`,
  `TauCeti.IsWeakCRSolution.memWkpLoc_one_self`: order-zero interior regularity across the
  Sobolev exponent ladder.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4, Lemma B.4.6 and its proof.
-/

public section

open MeasureTheory TopologicalSpace Complex Set Metric Filter
open scoped InnerProductSpace ContDiff Distributions ENNReal NNReal Convolution Topology
open Laplacian LineDeriv

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω : Opens ℂ} {p q s : ℝ≥0∞}
  {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

/-! ### Mollifying a Sobolev test field -/

section Mollify

variable {ψ : ℂ → V} {Dψ : ℂ → ℂ →L[ℝ] V}

/-- Pairings of the derivatives of mollifications with a fixed field converge. -/
private theorem tendsto_integral_inner_fderiv_mollify {K' : Set ℂ} (hK'm : MeasurableSet K')
    (hK'Ω : K' ⊆ Ω) [Fact (1 ≤ s)] {ρ : ℕ → ContDiffBump (0 : ℂ)}
    (hρ : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0)) {φ : ℕ → 𝓓(Ω, V)}
    (hφs : ∀ n, tsupport (φ n : ℂ → V) ⊆ K')
    (hderiv : ∀ n, ∀ z ∈ K', fderiv ℝ (φ n : ℂ → V) z =
      ((ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (Ω : Set ℂ).indicator Dψ) z)
    (hDψ : MemLp Dψ s (volume.restrict Ω)) (c : ℂ) {a : ℂ → V}
    (ha : MemLp a s.conjExponent (volume.restrict K')) :
    Tendsto (fun n => ∫ z, ⟪fderiv ℝ (φ n : ℂ → V) z c, a z⟫_ℝ) atTop
      (𝓝 (∫ z in K', ⟪Dψ z c, a z⟫_ℝ)) := by
  let B : V →L[ℝ] (ℂ →L[ℝ] V) →L[ℝ] ℝ := (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).bilinearComp
    (ContinuousLinearMap.id ℝ V) (ContinuousLinearMap.apply ℝ V c)
  have hB : ∀ w M, B w M = ⟪w, M c⟫_ℝ := fun w M => by simp [B]
  have := B.tendsto_integral_bilin_normed_convolution hρ
    ((memLp_indicator_iff_restrict hK'm.nullMeasurableSet).2 ha)
    ((memLp_indicator_iff_restrict Ω.isOpen.measurableSet.nullMeasurableSet).2 hDψ)
  convert this using 1
  · funext n
    refine integral_congr_ae (.of_forall fun z => ?_)
    dsimp only
    by_cases hz : z ∈ K'
    · rw [indicator_of_mem hz, hB, hderiv n z hz, real_inner_comm]
    · rw [indicator_of_notMem hz, map_zero, zero_apply,
        fderiv_of_notMem_tsupport ℝ fun h' => hz (hφs n h'), zero_apply, inner_zero_left]
  · rw [← integral_indicator hK'm]
    congr 1
    refine integral_congr_ae (.of_forall fun z => ?_)
    dsimp only
    by_cases hz : z ∈ K'
    · rw [indicator_of_mem hz, indicator_of_mem hz, indicator_of_mem (hK'Ω hz), hB,
        real_inner_comm]
    · rw [indicator_of_notMem hz, indicator_of_notMem hz, map_zero, zero_apply]

/-- Pairings of mollifications of a bounded field with a fixed integrable field converge. -/
private theorem tendsto_integral_inner_mollify {K' : Set ℂ} (hK'm : MeasurableSet K')
    {ρ : ℕ → ContDiffBump (0 : ℂ)} (hρ : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0))
    {φ : ℕ → 𝓓(Ω, V)}
    (hφ : ∀ n, ⇑(φ n) = (ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ)
    (hφs : ∀ n, tsupport (φ n : ℂ → V) ⊆ K') (hψb : MemLp ψ ⊤) {a : ℂ → V}
    (ha : IntegrableOn a K') :
    Tendsto (fun n => ∫ z, ⟪(φ n : ℂ → V) z, a z⟫_ℝ) atTop (𝓝 (∫ z in K', ⟪ψ z, a z⟫_ℝ)) := by
  have : ENNReal.HolderConjugate ∞ 1 := ENNReal.HolderConjugate.top_one
  have := (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).tendsto_integral_bilin_normed_convolution
    (p := ∞) (q := 1) hρ
    (memLp_one_iff_integrable.2 ((integrable_indicator_iff hK'm).2 ha)) hψb
  convert this using 1
  · funext n
    refine integral_congr_ae (.of_forall fun z => ?_)
    dsimp only
    rw [innerSL_apply_apply, ← hφ n]
    by_cases hz : z ∈ K'
    · rw [indicator_of_mem hz, real_inner_comm]
    · rw [indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport fun h' => hz (hφs n h'),
        inner_zero_left, inner_zero_left]
  · rw [← integral_indicator hK'm]
    congr 1
    refine integral_congr_ae (.of_forall fun z => ?_)
    dsimp only
    rw [innerSL_apply_apply]
    by_cases hz : z ∈ K'
    · rw [indicator_of_mem hz, indicator_of_mem hz, real_inner_comm]
    · rw [indicator_of_notMem hz, indicator_of_notMem hz, inner_zero_left]

omit [CompleteSpace V] in
/-- The weak equation tested against `ψ` localizes: since `Dψ` vanishes almost everywhere on `Ω`
where `ψ` does, an identity between integrals over a set `K' ⊆ Ω` containing the support of `ψ`
is the same identity over `Ω`. -/
private theorem integral_inner_eq_of_setIntegral_eq (hψ : HasWeakFDerivOn volume Ω ψ Dψ)
    {K' : Set ℂ} (hK'Ω : K' ⊆ Ω) (hKK' : tsupport ψ ⊆ K')
    (h1 : IntegrableOn (fun z => ⟪Dψ z 1, ξ z⟫_ℝ) K')
    (h2 : IntegrableOn (fun z => ⟪Dψ z I, J z (ξ z)⟫_ℝ) K')
    (h3 : IntegrableOn (fun z => ⟪ψ z, DJ z I (ξ z)⟫_ℝ) K')
    (h4 : IntegrableOn (fun z => ⟪ψ z, S z (ξ z)⟫_ℝ) K')
    (hkey : -(∫ z in K', ⟪Dψ z 1, ξ z⟫_ℝ) - (∫ z in K', ⟪Dψ z I, J z (ξ z)⟫_ℝ) -
      (∫ z in K', ⟪ψ z, DJ z I (ξ z)⟫_ℝ) + (∫ z in K', ⟪ψ z, S z (ξ z)⟫_ℝ) =
        ∫ z in K', ⟪ψ z, η z⟫_ℝ) :
    IntegrableOn (fun z => -⟪Dψ z 1, ξ z⟫_ℝ - ⟪Dψ z I, J z (ξ z)⟫_ℝ -
        ⟪ψ z, DJ z I (ξ z)⟫_ℝ + ⟪ψ z, S z (ξ z)⟫_ℝ) Ω ∧
      ∫ z in Ω, (-⟪Dψ z 1, ξ z⟫_ℝ - ⟪Dψ z I, J z (ξ z)⟫_ℝ -
        ⟪ψ z, DJ z I (ξ z)⟫_ℝ + ⟪ψ z, S z (ξ z)⟫_ℝ) = ∫ z in Ω, ⟪ψ z, η z⟫_ℝ := by
  have hDψ0 : ∀ c : ℂ, ∀ᵐ z ∂volume.restrict Ω, z ∈ (tsupport ψ)ᶜ → Dψ z c = 0 := fun c =>
    (hψ.hasWeakLineDerivOn c).ae_eq_zero_of_isOpen (isClosed_tsupport ψ).isOpen_compl
      (.of_forall fun z hz => image_eq_zero_of_notMem_tsupport hz)
  have hP0 : ∀ᵐ z ∂volume, z ∈ (Ω : Set ℂ) \ K' → -⟪Dψ z 1, ξ z⟫_ℝ -
      ⟪Dψ z I, J z (ξ z)⟫_ℝ - ⟪ψ z, DJ z I (ξ z)⟫_ℝ + ⟪ψ z, S z (ξ z)⟫_ℝ = 0 := by
    filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).1 ((hDψ0 1).and (hDψ0 I))]
      with z hz hzΩ
    have hzK : z ∉ tsupport ψ := fun h' => hzΩ.2 (hKK' h')
    obtain ⟨h1, hI⟩ := hz hzΩ.1
    simp [h1 hzK, hI hzK, image_eq_zero_of_notMem_tsupport hzK]
  have hψη0 : ∀ᵐ z ∂volume, z ∈ (Ω : Set ℂ) \ K' → ⟪ψ z, η z⟫_ℝ = 0 :=
    .of_forall fun z hz => by simp [image_eq_zero_of_notMem_tsupport fun h' => hz.2 (hKK' h')]
  have hΩm : NullMeasurableSet (Ω : Set ℂ) := Ω.isOpen.measurableSet.nullMeasurableSet
  refine ⟨((((h1.neg).sub h2).sub h3).add h4).of_ae_sdiff_eq_zero hΩm hP0, ?_⟩
  rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hΩm hK'Ω hP0,
    setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hΩm hK'Ω hψη0, ← hkey,
    integral_add _ h4, integral_sub _ h3, integral_sub _ h2, integral_neg]
  exacts [h1.neg, h1.neg.sub h2, (h1.neg.sub h2).sub h3]

end Mollify

/-- **The weak equation for Sobolev test fields.** Let `ξ` be a weak solution of
`∂_s ξ + J ∂_t ξ + S ξ = η` on `Ω` with Sobolev coefficients, `1/p + 1/q ≤ 1`, and `J` locally
bounded on `Ω`. Then the weak equation also holds against every bounded compactly supported test
field `ψ` with support in `Ω` and a weak derivative `Dψ ∈ Lˢ(Ω)`, `1/s + 1/q ≤ 1`, in place of
the classical derivative of a smooth test function: the pairing
`⟪D* ψ, ξ⟫ = -⟪∂_s ψ, ξ⟫ - ⟪∂_t ψ, J ξ⟫ - ⟪ψ, (∂_t J) ξ⟫ + ⟪ψ, S ξ⟫` is integrable on `Ω` with
integral `∫_Ω ⟪ψ, η⟫`. -/
theorem IsWeakCRSolution.integral_inner_eq_of_hasWeakFDerivOn
    (h : IsWeakCRSolution q Ω J DJ S ξ η) (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (hJ : MemLpLoc ⊤ Ω J) {ψ : ℂ → V} {Dψ : ℂ → ℂ →L[ℝ] V}
    (hψ : HasWeakFDerivOn volume Ω ψ Dψ) (hψc : HasCompactSupport ψ) (hψΩ : tsupport ψ ⊆ Ω)
    (hψb : MemLp ψ ⊤) (hDψ : MemLp Dψ s (volume.restrict Ω)) (hsq : s⁻¹ + q⁻¹ ≤ 1) :
    IntegrableOn (fun z => -⟪Dψ z 1, ξ z⟫_ℝ - ⟪Dψ z I, J z (ξ z)⟫_ℝ -
        ⟪ψ z, DJ z I (ξ z)⟫_ℝ + ⟪ψ z, S z (ξ z)⟫_ℝ) Ω ∧
      ∫ z in Ω, (-⟪Dψ z 1, ξ z⟫_ℝ - ⟪Dψ z I, J z (ξ z)⟫_ℝ -
        ⟪ψ z, DJ z I (ξ z)⟫_ℝ + ⟪ψ z, S z (ξ z)⟫_ℝ) = ∫ z in Ω, ⟪ψ z, η z⟫_ℝ := by
  -- A compact neighbourhood `K'` of the support of `ψ` whose `δ`-balls stay in `Ω`.
  obtain ⟨δ, hδ, hball⟩ := hψc.isCompact.exists_forall_closedBall_subset_of_isOpen Ω.isOpen hψΩ
  set K' := cthickening δ (tsupport ψ)
  have hK'c : IsCompact K' := hψc.isCompact.cthickening
  have hK'm : MeasurableSet K' := isClosed_cthickening.measurableSet
  have hK'Ω : K' ⊆ Ω := fun z hz => hball z hz (mem_closedBall_self hδ.le)
  have hs1 : 1 ≤ s := ENNReal.inv_le_one.1 (le_self_add.trans hsq)
  have : Fact (1 ≤ s) := ⟨hs1⟩
  have hs'q : s.conjExponent ≤ q := ENNReal.inv_le_inv.1 <|
    (ENNReal.add_le_add_iff_left (ENNReal.inv_ne_top.2 (zero_lt_one.trans_le hs1).ne')).1 <|
      hsq.trans (ENNReal.HolderConjugate.inv_add_inv_eq_one s s.conjExponent).ge
  have : IsFiniteMeasure (volume.restrict K') :=
    isFiniteMeasure_restrict.2 hK'c.measure_lt_top.ne
  -- The fields paired with `ψ` and its derivative, on `K'`.
  have hξK : MemLp ξ q (volume.restrict K') := memLpLoc_iff.1 h.memLpLoc K' hK'Ω hK'c
  have hJξK : MemLp (fun z => J z (ξ z)) q (volume.restrict K') :=
    memLpLoc_iff.1 (hJ.clm_apply h.memLpLoc) K' hK'Ω hK'c
  have hint : ∀ {A : ℂ → V →L[ℝ] V}, MemLpLoc p Ω A → IntegrableOn (fun z => A z (ξ z)) K' :=
    fun hA => (hA.locallyIntegrableOn_clm_apply h.memLpLoc hpq
      Ω.isOpen.isLocallyClosed).integrableOn_compact_subset hK'Ω hK'c
  have hDJξ : IntegrableOn (fun z => DJ z I (ξ z)) K' :=
    hint (hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I))
  have hSξ := hint hc.memLpLoc_zeroth
  have hintD : ∀ c : ℂ, ∀ {a : ℂ → V}, MemLp a q (volume.restrict K') →
      IntegrableOn (fun z => ⟪Dψ z c, a z⟫_ℝ) K' := fun c a ha =>
    memLp_one_iff_integrable.1 ((innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).memLp_of_bilin 1
      ((ContinuousLinearMap.apply ℝ V c).comp_memLp'
        (hDψ.mono_measure (Measure.restrict_mono hK'Ω le_rfl))) (ha.mono_exponent hs'q))
  have hint0 : ∀ {a : ℂ → V}, IntegrableOn a K' → IntegrableOn (fun z => ⟪ψ z, a z⟫_ℝ) K' :=
    fun ha => memLp_one_iff_integrable.1 ((innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).memLp_of_bilin 1
      (hψb.restrict K') (memLp_one_iff_integrable.2 ha))
  -- Test the weak equation against the mollifications of `ψ` and pass to the limit.
  choose φ hφ hφs hderiv using fun n => hψ.exists_testFunction_convolution_normed hψc hψb hDψ
    le_top hs1 hball (ContDiffBump.shrinking hδ n) ((ContDiffBump.rOut_shrinking hδ n).trans_le
      (div_le_self hδ.le (le_add_of_nonneg_left n.cast_nonneg)))
  have hρ := ContDiffBump.tendsto_rOut_shrinking (c := (0 : ℂ)) hδ
  have hlimD : ∀ (c : ℂ) {a : ℂ → V}, MemLp a q (volume.restrict K') →
      Tendsto (fun n => ∫ z, ⟪fderiv ℝ (φ n : ℂ → V) z c, a z⟫_ℝ) atTop
        (𝓝 (∫ z in K', ⟪Dψ z c, a z⟫_ℝ)) := fun c _ ha =>
    tendsto_integral_inner_fderiv_mollify hK'm hK'Ω hρ hφs hderiv hDψ c (ha.mono_exponent hs'q)
  have hlim0 : ∀ {a : ℂ → V}, IntegrableOn a K' →
      Tendsto (fun n => ∫ z, ⟪(φ n : ℂ → V) z, a z⟫_ℝ) atTop
        (𝓝 (∫ z in K', ⟪ψ z, a z⟫_ℝ)) := fun ha =>
    tendsto_integral_inner_mollify hK'm hρ hφ hφs hψb ha
  have hlhs := (((hlimD 1 hξK).neg.sub (hlimD I hJξK)).sub (hlim0 hDJξ)).add (hlim0 hSξ)
  have heq := fun n => (hc.integral_inner_crFormalAdjoint_eq_terms hpq h.memLpLoc (φ n)).symm.trans
    (h.integral_inner_crFormalAdjoint (φ n))
  exact integral_inner_eq_of_setIntegral_eq hψ hK'Ω (self_subset_cthickening _) (hintD 1 hξK)
    (hintD I hJξK) (hint0 hDJξ) (hint0 hSξ) (tendsto_nhds_unique (hlhs.congr heq)
      (hlim0 (h.locallyIntegrableOn.integrableOn_compact_subset hK'Ω hK'c)))

/-! ### Order-zero regularity -/

omit [CompleteSpace V] in
/-- **Sobolev coefficients are locally bounded.** For `p > 2`, a coefficient `J` of class
`W^{1,p}_loc` agrees almost everywhere with a continuous map, by Morrey's embedding, so it is
locally bounded on `Ω`. -/
theorem IsSobolevCRCoefficients.memLpLoc_top_coeff [FiniteDimensional ℝ V]
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hp : 2 < p) : MemLpLoc ⊤ Ω J :=
  (memWkpLoc_succ_iff_of_isOpen.2 ⟨hc.memLpLoc_coeff, DJ, hc.hasWeakFDerivOn,
    memWkpLoc_zero_iff.2 hc.memLpLoc_deriv⟩ : MemWkpLoc p Ω (0 + 1) J).memLpLoc_top hp

/-- `M ↦ Mᵀ v`, as a continuous linear map. -/
private noncomputable def adjointApply (v : V) : (V →L[ℝ] V) →L[ℝ] V :=
  (ContinuousLinearMap.apply ℝ V v).comp (ContinuousLinearMap.adjointRealCLM (𝕜 := ℝ))

private theorem inner_adjointApply (v : V) (M : V →L[ℝ] V) (w : V) :
    ⟪adjointApply v M, w⟫_ℝ = ⟪v, M w⟫_ℝ := by
  simp [adjointApply, ContinuousLinearMap.adjoint_inner_left]

/-- The coefficient `f = η + (∂_t J) ξ - S ξ` of `∂_s` in the divergence-form Laplace equation
`Δξ = ∂_s f + ∂_t g`. -/
private noncomputable def orderZeroS (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (S : ℂ → V →L[ℝ] V)
    (ξ η : ℂ → V) (z : ℂ) : V :=
  η z + DJ z I (ξ z) - S z (ξ z)

/-- The coefficient `g = J S ξ - J η - (∂_s J) ξ - (∂_t J) J ξ - J (∂_t J) ξ` of `∂_t` in the
divergence-form Laplace equation `Δξ = ∂_s f + ∂_t g`. -/
private noncomputable def orderZeroT (J : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V)
    (S : ℂ → V →L[ℝ] V) (ξ η : ℂ → V) (z : ℂ) : V :=
  J z (S z (ξ z)) - J z (η z) - DJ z 1 (ξ z) - DJ z I (J z (ξ z)) - J z (DJ z I (ξ z))

/-- The coefficients `f` and `g` are locally `Lʳ` when `1/p + 1/q ≤ 1/r` and `η` is. -/
private theorem memLpLoc_orderZero (h : IsWeakCRSolution q Ω J DJ S ξ η)
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJb : MemLpLoc ⊤ Ω J) {r : ℝ≥0∞}
    (hpqr : p⁻¹ + q⁻¹ ≤ r⁻¹) (hη : MemLpLoc r Ω η) :
    MemLpLoc r Ω (orderZeroS DJ S ξ η) ∧ MemLpLoc r Ω (orderZeroT J DJ S ξ η) := by
  have : ENNReal.HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ := ENNReal.HolderTriple.of p q
  have hrr : r ≤ (p⁻¹ + q⁻¹)⁻¹ := by rw [← ENNReal.inv_le_inv, inv_inv]; exact hpqr
  have happly : ∀ {A : ℂ → V →L[ℝ] V} {w : ℂ → V}, MemLpLoc p Ω A → MemLpLoc q Ω w →
      MemLpLoc r Ω (fun z => A z (w z)) := fun hA hw => (hA.clm_apply hw).mono_exponent hrr
  have hDJ : ∀ c : ℂ, MemLpLoc p Ω (fun z => DJ z c) := fun c =>
    hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) c)
  have hJr : ∀ {w : ℂ → V}, MemLpLoc r Ω w → MemLpLoc r Ω (fun z => J z (w z)) := fun hw =>
    hJb.clm_apply hw
  exact ⟨(hη.add (happly (hDJ I) h.memLpLoc)).sub (happly hc.memLpLoc_zeroth h.memLpLoc),
    ((((hJr (happly hc.memLpLoc_zeroth h.memLpLoc)).sub (hJr hη)).sub
      (happly (hDJ 1) h.memLpLoc)).sub (happly (hDJ I) (hJb.clm_apply h.memLpLoc))).sub
        (hJr (happly (hDJ I) h.memLpLoc))⟩

/-- Off the support of `φ`, a directional derivative of `φ` vanishes together with its
derivative. -/
private theorem lineDerivOp_eq_zero_of_notMem (φ : 𝓓(Ω, ℝ)) (c : ℂ) {z : ℂ}
    (hz : z ∉ tsupport (φ : ℂ → ℝ)) :
    (∂_{c} φ : 𝓓(Ω, ℝ)) z = 0 ∧ fderiv ℝ (∂_{c} φ : 𝓓(Ω, ℝ)) z = 0 :=
  have hz' : z ∉ tsupport (∂_{c} φ : 𝓓(Ω, ℝ)) :=
    fun h' => hz (TestFunction.tsupport_lineDerivOp_subset φ c h')
  ⟨image_eq_zero_of_notMem_tsupport hz', fderiv_of_notMem_tsupport ℝ hz'⟩

/-- The test field `ψ = ∂_s φ • v - ∂_t φ • Jᵀ v`. -/
private noncomputable def crTestField (J : ℂ → V →L[ℝ] V) (φ : 𝓓(Ω, ℝ)) (v : V) (z : ℂ) : V :=
  (∂_{(1 : ℂ)} φ : 𝓓(Ω, ℝ)) z • v - (∂_{I} φ : 𝓓(Ω, ℝ)) z • adjointApply v (J z)

/-- The weak derivative of the test field `TauCeti.crTestField`. -/
private noncomputable def crTestFieldDeriv (J : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V)
    (φ : 𝓓(Ω, ℝ)) (v : V) (z : ℂ) : ℂ →L[ℝ] V :=
  (fderiv ℝ (∂_{(1 : ℂ)} φ : 𝓓(Ω, ℝ)) z).smulRight v -
    ((∂_{I} φ : 𝓓(Ω, ℝ)) z • (adjointApply v).comp (DJ z) +
      (fderiv ℝ (∂_{I} φ : 𝓓(Ω, ℝ)) z).smulRight (adjointApply v (J z)))

private theorem crTestField_eq_zero (φ : 𝓓(Ω, ℝ)) (v : V) {z : ℂ}
    (hz : z ∉ tsupport (φ : ℂ → ℝ)) :
    crTestField J φ v z = 0 ∧ crTestFieldDeriv J DJ φ v z = 0 := by
  obtain ⟨ha, hda⟩ := lineDerivOp_eq_zero_of_notMem φ 1 hz
  obtain ⟨hb, hdb⟩ := lineDerivOp_eq_zero_of_notMem φ I hz
  simp [crTestField, crTestFieldDeriv, ha, hda, hb, hdb]

/-- The test field `TauCeti.crTestField` and its weak derivative satisfy the hypotheses of
`TauCeti.IsWeakCRSolution.integral_inner_eq_of_hasWeakFDerivOn`, with `s = p`. -/
private theorem crTestField_props (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hJb : MemLpLoc ⊤ Ω J) (φ : 𝓓(Ω, ℝ)) (v : V) :
    HasWeakFDerivOn volume Ω (crTestField J φ v) (crTestFieldDeriv J DJ φ v) ∧
      HasCompactSupport (crTestField J φ v) ∧ tsupport (crTestField J φ v) ⊆ Ω ∧
      MemLp (crTestField J φ v) ⊤ ∧ MemLp (crTestFieldDeriv J DJ φ v) p (volume.restrict Ω) := by
  set a : 𝓓(Ω, ℝ) := ∂_{(1 : ℂ)} φ
  set b : 𝓓(Ω, ℝ) := ∂_{I} φ
  set A := adjointApply v
  have hs : Function.support (crTestField J φ v) ⊆ tsupport φ := fun z hz =>
    by_contra fun h' => hz (crTestField_eq_zero (DJ := DJ) φ v h').1
  have hw : HasWeakFDerivOn volume Ω (fun z => a z • v) (fun z => (fderiv ℝ a z).smulRight v) :=
    (((a.contDiff.smul contDiff_const).contDiffOn.of_le (by simp) :
      ContDiffOn ℝ 1 (fun z => a z • v) Ω).hasWeakFDerivOn_fderiv (μ := volume)).congr_ae_deriv
        (.of_forall fun z => fderiv_smul_const (a.contDiff.differentiable (by simp) z) v)
  refine ⟨hw.sub ((hc.hasWeakFDerivOn.clm_comp A).contDiff_smul b.contDiff),
    φ.hasCompactSupport.mono' hs,
    (closure_minimal hs (isClosed_tsupport _)).trans φ.tsupport_subset,
    MemLpLoc.memLp_of_forall_notMem_eq_zero ?_ φ.hasCompactSupport φ.tsupport_subset
      fun z hz => (crTestField_eq_zero (DJ := DJ) φ v hz).1,
    (MemLpLoc.memLp_of_forall_notMem_eq_zero ?_ φ.hasCompactSupport φ.tsupport_subset
      fun z hz => (crTestField_eq_zero φ v hz).2).restrict _⟩
  · exact (a.contDiff.smul contDiff_const).continuous.continuousOn.memLpLoc.sub
      ((hJb.clm_comp A).continuousOn_smul b.contDiff.continuous.continuousOn)
  · have h1 : ContinuousOn (fun z => (fderiv ℝ a z).smulRight v) Ω :=
      (((StrongDual.smulRightL ℝ ℂ V).flip v).continuous.comp
        (a.contDiff.continuous_fderiv (by simp))).continuousOn
    have h2 : MemLpLoc p Ω (fun z => b z • A.comp (DJ z)) :=
      (hc.memLpLoc_deriv.clm_comp
        (ContinuousLinearMap.compL ℝ ℂ (V →L[ℝ] V) V A)).continuousOn_smul
          b.contDiff.continuous.continuousOn
    have h3 : MemLpLoc ⊤ Ω (fun z => (fderiv ℝ b z).smulRight (A (J z))) :=
      (hJb.clm_comp ((StrongDual.smulRightL ℝ ℂ V).flip.comp A)).clm_apply_continuousOn
        (b.contDiff.continuous_fderiv (by simp)).continuousOn
    exact h1.memLpLoc.sub (h2.add (h3.mono_exponent le_top))

/-- **The pointwise identity behind the order-zero lemma.** Where `J² = -1`, the pairing of the
formal adjoint with the test field `ψ = ∂_s φ • v - ∂_t φ • Jᵀ v`, minus `⟪ψ, η⟫`, is
`-⟪v, Δφ • ξ + ∂_s φ • f + ∂_t φ • g⟫`. -/
private theorem inner_crTestField_eq (φ : 𝓓(Ω, ℝ)) (v : V) (z : ℂ)
    (hJJ : z ∈ tsupport (φ : ℂ → ℝ) → J z (J z (ξ z)) = -ξ z) :
    ⟪v, Δ (φ : ℂ → ℝ) z • ξ z⟫_ℝ + ⟪v, fderiv ℝ (φ : ℂ → ℝ) z 1 • orderZeroS DJ S ξ η z +
      fderiv ℝ (φ : ℂ → ℝ) z I • orderZeroT J DJ S ξ η z⟫_ℝ =
      -((-⟪crTestFieldDeriv J DJ φ v z 1, ξ z⟫_ℝ - ⟪crTestFieldDeriv J DJ φ v z I, J z (ξ z)⟫_ℝ -
        ⟪crTestField J φ v z, DJ z I (ξ z)⟫_ℝ + ⟪crTestField J φ v z, S z (ξ z)⟫_ℝ) -
          ⟪crTestField J φ v z, η z⟫_ℝ) := by
  -- `Δφ = ∂_s (∂_s φ) + ∂_t (∂_t φ)`, and `∂_s (∂_t φ) = ∂_t (∂_s φ)`.
  have hΔ : Δ (φ : ℂ → ℝ) z = fderiv ℝ (∂_{(1 : ℂ)} φ : 𝓓(Ω, ℝ)) z 1 +
      fderiv ℝ (∂_{I} φ : 𝓓(Ω, ℝ)) z I := by
    rw [laplacian_eq_fderiv_fderiv_apply_one_add_fderiv_fderiv_apply_I
      ((φ.contDiff.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero z),
      show ((∂_{(1 : ℂ)} φ : 𝓓(Ω, ℝ)) : ℂ → ℝ) = fun w => fderiv ℝ (φ : ℂ → ℝ) w 1 from
        funext (TestFunction.lineDerivOp_apply_eq_fderiv φ 1),
      show ((∂_{I} φ : 𝓓(Ω, ℝ)) : ℂ → ℝ) = fun w => fderiv ℝ (φ : ℂ → ℝ) w I from
        funext (TestFunction.lineDerivOp_apply_eq_fderiv φ I)]
  have hsymm : fderiv ℝ (∂_{I} φ : 𝓓(Ω, ℝ)) z 1 = fderiv ℝ (∂_{(1 : ℂ)} φ : 𝓓(Ω, ℝ)) z I := by
    simpa only [TestFunction.lineDerivOp_apply_eq_fderiv] using
      congrArg (fun χ : 𝓓(Ω, ℝ) => χ z) (TestFunction.lineDerivOp_comm φ 1 I)
  rw [hΔ, ← TestFunction.lineDerivOp_apply_eq_fderiv φ 1,
    ← TestFunction.lineDerivOp_apply_eq_fderiv φ I]
  by_cases hz : z ∈ tsupport (φ : ℂ → ℝ)
  · simp only [crTestField, crTestFieldDeriv, orderZeroS, orderZeroT, sub_apply, add_apply,
      smul_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      inner_sub_left, inner_add_left, inner_sub_right, inner_add_right, real_inner_smul_left,
      inner_smul_right, inner_adjointApply, hJJ hz, inner_neg_right, hsymm]
    ring
  · obtain ⟨ha, hda⟩ := lineDerivOp_eq_zero_of_notMem φ 1 hz
    obtain ⟨hb, hdb⟩ := lineDerivOp_eq_zero_of_notMem φ I hz
    obtain ⟨hψ, hDψ⟩ := crTestField_eq_zero (J := J) (DJ := DJ) φ v hz
    simp [ha, hda, hb, hdb, hψ, hDψ]

/-- **Order-zero interior regularity for real Cauchy–Riemann equations with Sobolev
coefficients** (McDuff–Salamon, Lemma B.4.6). Let `V` be finite-dimensional, `p > 2`, and let
`J ∈ W^{1,p}_loc(Ω)` with `J² = -1` almost everywhere and `S ∈ Lᵖ_loc(Ω)`, in the sense of
`TauCeti.IsSobolevCRCoefficients`. If `ξ ∈ L^q_loc` is a weak solution of
`∂_s ξ + J ∂_t ξ + S ξ = η` on `Ω`, and `η ∈ Lʳ_loc` with `1 < r < ∞` and `1/p + 1/q ≤ 1/r`,
then `ξ ∈ W^{1,r}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc_one [FiniteDimensional ℝ V]
    (h : IsWeakCRSolution q Ω J DJ S ξ η) (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hp : 2 < p) (hJ2 : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) {r : ℝ≥0∞} (hr : 1 < r)
    (hr_top : r ≠ ⊤) (hpqr : p⁻¹ + q⁻¹ ≤ r⁻¹) (hη : MemLpLoc r Ω η) :
    MemWkpLoc r Ω 1 ξ := by
  have hpq : p⁻¹ + q⁻¹ ≤ 1 := hpqr.trans (ENNReal.inv_le_one.2 hr.le)
  have hloc := Ω.isOpen.isLocallyClosed
  have hJb := hc.memLpLoc_top_coeff hp
  obtain ⟨hfr, hgr⟩ := memLpLoc_orderZero h hc hJb hpqr hη
  have hξloc : LocallyIntegrableOn ξ Ω volume :=
    h.memLpLoc.locallyIntegrableOn (ENNReal.inv_le_one.1 (le_add_self.trans hpq)) hloc
  refine memWkpLoc_one_of_forall_integral_laplacian_smul_eq hr hr_top hξloc hfr hgr fun φ => ?_
  have hI1 : Integrable (fun z => Δ (φ : ℂ → ℝ) z • ξ z) := by
    simpa only [TestFunction.laplacianCLM_apply] using
      (laplacianCLM ℝ ℂ 𝓓(Ω, ℝ) φ).integrable_smul hξloc
  have hI2 : Integrable (fun z => fderiv ℝ (φ : ℂ → ℝ) z 1 • orderZeroS DJ S ξ η z +
      fderiv ℝ (φ : ℂ → ℝ) z I • orderZeroT J DJ S ξ η z) :=
    (integrable_fderiv_smul_of_locallyIntegrableOn (hfr.locallyIntegrableOn hr.le hloc) φ 1).add
      (integrable_fderiv_smul_of_locallyIntegrableOn (hgr.locallyIntegrableOn hr.le hloc) φ I)
  refine ext_inner_left ℝ fun v => ?_
  rw [← integral_inner hI1, inner_neg_right, ← integral_inner hI2]
  -- Test the weak equation against `ψ = ∂_s φ • v - ∂_t φ • Jᵀ v`.
  obtain ⟨hψw, hψc, hψΩ, hψb, hDψp⟩ := crTestField_props (DJ := DJ) hc hJb φ v
  obtain ⟨hPΩ, hPeq⟩ :=
    h.integral_inner_eq_of_hasWeakFDerivOn hc hpq hJb hψw hψc hψΩ hψb hDψp hpq
  have hΩT : ∀ z ∉ (Ω : Set ℂ), z ∉ tsupport (φ : ℂ → ℝ) :=
    fun z hz h' => hz (φ.tsupport_subset h')
  have hP0 : ∀ z ∉ (Ω : Set ℂ), -⟪crTestFieldDeriv J DJ φ v z 1, ξ z⟫_ℝ -
      ⟪crTestFieldDeriv J DJ φ v z I, J z (ξ z)⟫_ℝ - ⟪crTestField J φ v z, DJ z I (ξ z)⟫_ℝ +
        ⟪crTestField J φ v z, S z (ξ z)⟫_ℝ = 0 := fun z hz => by
    obtain ⟨hψ, hDψ⟩ := crTestField_eq_zero (J := J) (DJ := DJ) φ v (hΩT z hz)
    simp [hψ, hDψ]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hP0,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      simp [(crTestField_eq_zero (J := J) (DJ := DJ) φ v (hΩT z hz)).1]] at hPeq
  have hψη : Integrable (fun z => ⟪crTestField J φ v z, η z⟫_ℝ) := by
    have h1 := (integrable_fderiv_smul_of_locallyIntegrableOn
      (hη.locallyIntegrableOn hr.le hloc) φ 1).const_inner (𝕜 := ℝ) v
    have h2 := (integrable_fderiv_smul_of_locallyIntegrableOn
      ((hJb.clm_apply hη).locallyIntegrableOn hr.le hloc) φ I).const_inner (𝕜 := ℝ) v
    refine (h1.sub h2).congr (.of_forall fun z => ?_)
    simp only [Pi.sub_apply, crTestField, TestFunction.lineDerivOp_apply_eq_fderiv,
      inner_sub_left, real_inner_smul_left, inner_smul_right, inner_adjointApply]
  -- `J² = -1` almost everywhere on the support of `φ`.
  have hJJ : ∀ᵐ z ∂volume, z ∈ tsupport (φ : ℂ → ℝ) → J z (J z (ξ z)) = -ξ z := by
    filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).1 hJ2] with z hz hzT
    simpa using congrArg (fun M : V →L[ℝ] V => M (ξ z)) (hz (φ.tsupport_subset hzT))
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← integral_add (hI1.const_inner (𝕜 := ℝ) v) (hI2.const_inner (𝕜 := ℝ) v),
    integral_congr_ae (hJJ.mono fun z hz => inner_crTestField_eq φ v z hz), integral_neg,
    integral_sub (hPΩ.integrable_of_forall_notMem_eq_zero hP0) hψη, hPeq, sub_self, neg_zero]

/-! ### Order-zero Sobolev exponent ladder -/

section Ladder

variable [FiniteDimensional ℝ V] {r : ℝ≥0∞}

/-- Once `ξ` reaches `W^{1,r}_loc` for some `r > 2`, the `L^∞` Sobolev embedding puts `ξ` in
`L^∞_loc`, and one more application of `IsWeakCRSolution.memWkpLoc_one` reaches
`W^{1,s}_loc`. -/
private theorem memWkpLoc_one_of_two_lt (hr : 2 < r) (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hs1 : 1 < s) (hsp : s ≤ p)
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemLpLoc p Ω S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hη : MemLpLoc s Ω η)
    (hξr : MemWkpLoc r Ω 1 ξ) : MemWkpLoc s Ω 1 ξ :=
  have hc : IsSobolevCRCoefficients p Ω J DJ S :=
    ⟨hDJ, hJ.memLpLoc, hJ.memLpLoc_of_hasWeakFDerivOn hDJ, hS⟩
  (hsol.of_memLpLoc (hξr.memLpLoc_top hr)).memWkpLoc_one hc hp hJsq hs1
    (ne_top_of_le_ne_top hp_top hsp) (by simpa using ENNReal.inv_le_inv.2 hsp) hη

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
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemLpLoc p Ω S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hη : MemLpLoc s Ω η)
    (hξ_r₁ : MemWkpLoc r₁ Ω 1 ξ) : MemWkpLoc s Ω 1 ξ := by
  have hc : IsSobolevCRCoefficients p Ω J DJ S :=
    ⟨hDJ, hJ.memLpLoc, hJ.memLpLoc_of_hasWeakFDerivOn hDJ, hS⟩
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
    (hsol.of_memLpLoc hξ_star).memWkpLoc_one hc hp hJsq
      (by exact_mod_cast one_lt_two.trans hr₂_gt2') ENNReal.coe_ne_top hpqr₂
      (hη.mono_exponent (by exact_mod_cast hr₂_le_s))
  exact memWkpLoc_one_of_two_lt (by exact_mod_cast hr₂_gt2')
    hp ENNReal.coe_ne_top hs1 hsp hJ hDJ hJsq hS hsol hη hξ_r₂

/-- Finite-exponent Sobolev ladder: `n` serves as induction fuel for the subcritical recursion
(`1/t ≤ n * (1/2 - 1/p)` with `1/p + 1/t < 1`), since each subcritical step (`r₁ < 2`) decreases
`1/t` by `1/2 - 1/p`. At any step the recursion terminates immediately if the product exponent
reaches `s`, handles the critical case `r₁ = 2` by embedding `W^{1,2}_loc` into a large finite
`L^{t*}_loc` before continuing past `2`, and finishes `r₁ > 2` via `W^{1,r₁}_loc ⊂ L^∞_loc`. -/
private theorem memWkpLoc_one_ladder {p s : ℝ≥0} (hp : 2 < (p : ℝ≥0∞))
    (hs1 : 1 < (s : ℝ≥0∞)) (hsp : (s : ℝ≥0∞) ≤ p)
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemLpLoc p Ω S) (hη : MemLpLoc s Ω η) :
    ∀ (n : ℕ) {t : ℝ≥0}, (0 : ℝ) < t → (p : ℝ)⁻¹ + (t : ℝ)⁻¹ < 1 →
      (t : ℝ)⁻¹ ≤ n * (2⁻¹ - (p : ℝ)⁻¹) → IsWeakCRSolution t Ω J DJ S ξ η →
      MemWkpLoc s Ω 1 ξ := by
  have hc : IsSobolevCRCoefficients p Ω J DJ S :=
    ⟨hDJ, hJ.memLpLoc, hJ.memLpLoc_of_hasWeakFDerivOn hDJ, hS⟩
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
    · exact hsolt.memWkpLoc_one hc hp hJsq hs1 ENNReal.coe_ne_top
        ((ENNReal.inv_coe_add_inv_coe_le_inv_coe_iff (by exact_mod_cast hp0.ne')
          (by exact_mod_cast ht0.ne') (by exact_mod_cast (zero_lt_one.trans hs1R).ne')).2 <| by
            rw [← NNReal.coe_le_coe]; push_cast
            exact (le_inv_comm₀ (by positivity) (zero_lt_one.trans hs1R)).2 hsr)
        hη
    · -- Otherwise step to `W^{1,r₁}_loc` at `r₁ = r_prod` and split on `r₁ < 2`, `= 2`, `> 2`.
      let r₁ : ℝ≥0 := ⟨r_prod, by positivity⟩
      have hr₁_coe : (r₁ : ℝ) = r_prod := NNReal.coe_mk r_prod (by positivity)
      have hr₁_pos : (0 : ℝ) < r₁ := by rw [hr₁_coe]; positivity
      have hξ_r₁ : MemWkpLoc r₁ Ω 1 ξ :=
        hsolt.memWkpLoc_one hc hp hJsq
          (by exact_mod_cast (hr₁_coe.symm ▸ hr_prod_gt : (1 : ℝ) < r₁)) ENNReal.coe_ne_top
          ((ENNReal.inv_coe_add_inv_coe_le_inv_coe_iff (by exact_mod_cast hp0.ne')
            (by exact_mod_cast ht0.ne') (by exact_mod_cast hr₁_pos.ne')).2 <| by
              rw [← NNReal.coe_le_coe]; simp [hr₁_coe, r_prod])
          (hη.mono_exponent (by exact_mod_cast (hr₁_coe.trans_lt hrs).le))
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
theorem IsWeakCRSolution.memWkpLoc_one_of_memLpLoc (hp : 2 < p) (hpq : p⁻¹ + q⁻¹ < 1)
    (hs1 : 1 < s) (hs_top : s ≠ ⊤) (hsp : s ≤ p)
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hS : MemLpLoc p Ω S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hη : MemLpLoc s Ω η) :
    MemWkpLoc s Ω 1 ξ := by
  have hJsq' : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1 := by
    simpa [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def] using hJsq
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
  exact memWkpLoc_one_ladder hp' hs1 hsp' hJ' hDJ hJsq' hS' hη
    ⌈(q₀ : ℝ)⁻¹ / (2⁻¹ - (p' : ℝ)⁻¹)⌉₊ hq₀_pos hpq₀R ((div_le_iff₀ ha).1 (Nat.le_ceil _)) hsol₀

/-- **Order-zero interior regularity at the solution's exponent.** If `2 < p ≤ ∞`,
`1/p + 1/q < 1`, `q < ∞`, `q ≤ p`, `J ∈ W^{1,p}_loc(Ω)` with `J² = -1` almost everywhere on `Ω`,
`S ∈ Lᵖ_loc(Ω)`, and `ξ` solves `∂_s ξ + J ∂_t ξ + S ξ = η` weakly in `L^q_loc(Ω)` with
`η ∈ L^q_loc(Ω)`, then `ξ ∈ W^{1,q}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc_one_of_le (hp : 2 < p) (hpq : p⁻¹ + q⁻¹ < 1) (hq_top : q ≠ ⊤)
    (hqp : q ≤ p) (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hS : MemLpLoc p Ω S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hη : MemLpLoc q Ω η) :
    MemWkpLoc q Ω 1 ξ :=
  hsol.memWkpLoc_one_of_memLpLoc hp hpq
    (ENNReal.inv_lt_one.1 (lt_of_le_of_lt le_add_self hpq)) hq_top hqp hJ hDJ hJsq hS hη

/-- **Order-zero interior regularity at the coefficient exponent.** If `2 < p < ∞`,
`1/p + 1/q < 1`, `J ∈ W^{1,p}_loc(Ω)` with `J² = -1` almost everywhere on `Ω`, `S ∈ Lᵖ_loc(Ω)`,
and `ξ` solves `∂_s ξ + J ∂_t ξ + S ξ = η` weakly in `L^q_loc(Ω)` with `η ∈ Lᵖ_loc(Ω)`, then
`ξ ∈ W^{1,p}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc_one_self (hp : 2 < p) (hp_top : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ < 1)
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hS : MemLpLoc p Ω S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hη : MemLpLoc p Ω η) :
    MemWkpLoc p Ω 1 ξ :=
  hsol.memWkpLoc_one_of_memLpLoc hp hpq
    ((by exact_mod_cast one_lt_two : (1 : ℝ≥0∞) < 2).trans hp) hp_top le_rfl hJ
    hDJ hJsq hS hη

end Ladder

end TauCeti
