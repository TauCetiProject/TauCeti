/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.StandardFrame
public import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Contracting
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Comparison
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.TargetChange
import TauCeti.Analysis.Complex.Pompeiu.Pointwise
import TauCeti.Analysis.Complex.Pompeiu.Weak
import TauCeti.Analysis.Complex.Wirtinger.Regularity
import TauCeti.Analysis.Sobolev.Local.ChainRule
import TauCeti.Analysis.Sobolev.Local.Multiplication
import TauCeti.Geometry.Symplectic.Complex.Module.Conjugacy
import TauCeti.MeasureTheory.Function.RankOne

/-!
# The vector similarity principle for Sobolev solutions of linear Cauchy–Riemann equations

Let `p > 2` be finite and `Ω ⊆ ℂ` be open. Let `J` be a continuous `W^{1,p}_loc` field of
real-linear endomorphisms with `J² = -1` on `Ω`, let `C` be a locally `Lᵖ` field of real-linear
endomorphisms, and let `ξ` solve the weak linear Cauchy–Riemann equation

`∂ₛξ + J(z) ∂ₜξ + C(z) ξ = 0`

on `Ω` (`TauCeti.IsWeakLinearCauchyRiemannOn p Ω J C ξ`). The **Carleman vector similarity
principle** (McDuff–Salamon, Theorem 2.3.5) asserts that near every point `z₀ ∈ Ω` the solution
factors on a disc as `ξ = Φ σ`, where `Φ` is a continuous `W^{1,p}_loc` family of invertible
real-linear maps intertwining `J` with multiplication by `i` (`J Φ = Φ i`), and `σ` is holomorphic
(`TauCeti.exists_similarity_of_isWeakLinearCauchyRiemannOn`).

Unlike `TauCeti.Analysis.Complex.CauchyRiemann.Similarity`, which assumes `J = i`, `ξ` of class
`C¹`, and `C` locally bounded, here `ξ` and `J` are only in `W^{1,p}_loc` and `C` is only in
`Lᵖ_loc` for `2 < p < ∞`:

1. For `J = i` on a finite-dimensional complex inner product space, the real-linear term `C ξ` is
   absorbed along `ξ` into the complex-linear rank-one field `D w = ‖ξ‖⁻² ⟪ξ, w⟫ C ξ`
   (`TauCeti.rankOneDivNormSq`), which satisfies `D ξ = C ξ` and `‖D‖ ≤ ‖C‖`, so `D` inherits
   local `Lᵖ` integrability from `C`.
2. Since `2 < p`, the conjugate exponent `q` satisfies `q < 2`, so the truncated Cauchy kernel lies
   in `L^q` with norm tending to `0` as the disc radius shrinks
   (`TauCeti.tendsto_eLpNorm_truncatedCauchyKernel_nhds_zero`). On a sufficiently small closed disc,
   `Ψ ↦ 1 + T(½ Ψ D)` is therefore a contraction on continuous endomorphism fields, producing a
   continuous `Ψ = 1 + T g` close to `1` with `g = ½ Ψ D ∈ Lᵖ` supported in the disc.
3. Because `bar∂(T g) = g ∈ Lᵖ`, interior `Lᵖ` regularity for `bar∂`
   (`HasWeakConjWirtingerDerivOn.memWkpLoc_one`) places `Ψ` and its pointwise inverse `Φ = Ψ⁻¹` in
   `W^{1,p}_loc`. Expanding `σ = Ψ ξ` with the weak Sobolev Leibniz rule
   (`TauCeti.HasWeakFDerivOn.bilin_of_memLpLoc`) gives `bar∂σ = 0` weakly, hence `σ` is holomorphic
   by Weyl's lemma.
4. A variable complex structure `J ∈ W^{1,p}_loc` with `J² = -1` reduces locally to `J = i` via
   `TauCeti.standardFrame`, whose derivative contributes an `Lᵖ_loc` zeroth-order term absorbed by
   the `J = i` case.

From the local factorization follow `TauCeti.HasSimilarityFactorizationAt` at every point of `Ω`,
unique continuation (from an open set, a neighbourhood, or a zero of infinite order), discreteness
of the zero set of a nontrivial solution, and finite positive vanishing orders at zeros. The
unique continuation and isolated-zero theorems hold on any finite-dimensional *real* normed space
admitting `J² = -1`, by transporting to `ℂⁿ` via
`ContinuousLinearMap.exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul`. Conversely,
every product `Φ σ` of a continuous `W^{1,p}_loc` intertwining frame `Φ` (`J Φ = Φ i`) with a
holomorphic map `σ` solves a weak linear Cauchy–Riemann equation with `Lᵖ_loc` coefficient
(`TauCeti.isWeakLinearCauchyRiemannOn_clm_apply_of_differentiableOn`).

## Main results

* `TauCeti.exists_similarity_of_isWeakLinearCauchyRiemannOn_I_smul_id`: the Sobolev similarity
  principle for `J = i`, with complex-linear `Φ ∈ W^{1,p}_loc`.
* `TauCeti.exists_similarity_of_isWeakLinearCauchyRiemannOn`: the Carleman vector similarity
  principle for variable `J ∈ W^{1,p}_loc` with `J² = -1` and `C ∈ Lᵖ_loc` (`2 < p < ∞`).
* `TauCeti.hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn` and
  `TauCeti.exists_analyticOrderAt_eq_of_isWeakLinearCauchyRiemannOn`: local factorization and
  positive finite zero orders on complex targets.
* `TauCeti.eventually_eq_zero_or_eventually_ne_zero_of_isWeakLinearCauchyRiemannOn`,
  `TauCeti.eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_eventually_eq_zero`,
  `TauCeti.eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_eqOn_zero`,
  `TauCeti.eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_forall_isBigO`,
  `TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_isWeakLinearCauchyRiemannOn`,
  `TauCeti.exists_pos_isTheta_pow_of_isWeakLinearCauchyRiemannOn`: unique continuation, isolated
  zeros, and positive vanishing orders on general finite-dimensional real targets.
* `TauCeti.isWeakLinearCauchyRiemannOn_clm_apply_of_differentiableOn`: converse construction of the
  weak equation satisfied by `Φ σ`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 2.3.5 and Appendix B.4.
* T. Carleman, *Sur les systèmes linéaires aux dérivées partielles du premier ordre à deux
  variables*, C. R. Acad. Sci. Paris **197** (1933), 471–474.
-/

public noncomputable section

open Asymptotics Complex Filter Function MeasureTheory Metric Set Topology TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace

namespace TauCeti

/-! ### The Cauchy integral equation for `Lᵖ` coefficients -/

private theorem conjExponent_lt_two {p : ℝ≥0∞} (hp : 2 < p) : p.conjExponent < 2 := by
  have h1 : 1 < p - 1 := lt_tsub_iff_left.2 (by rwa [one_add_one_eq_two])
  simpa only [ENNReal.conjExponent, one_add_one_eq_two] using
    ENNReal.add_lt_add_left ENNReal.one_ne_top (ENNReal.inv_lt_one.2 h1)

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The source term `½ Ψ D` of the Cauchy integral equation on a closed disc, extended by `0`
outside the disc. -/
private def cauchySource {c : ℂ} {r : ℝ} (D : ℂ → E →L[ℂ] E)
    (Ψ : C(closedBall c r, E →L[ℂ] E)) (z : ℂ) : E →L[ℂ] E :=
  (2 : ℂ)⁻¹ • (extend Subtype.val Ψ 0 z).comp (D z)

private theorem cauchySource_of_mem {c : ℂ} {r : ℝ} (D : ℂ → E →L[ℂ] E)
    (Ψ : C(closedBall c r, E →L[ℂ] E)) {z : ℂ} (hz : z ∈ closedBall c r) :
    cauchySource D Ψ z = (2 : ℂ)⁻¹ • (Ψ ⟨z, hz⟩).comp (D z) := by
  rw [cauchySource, Subtype.val_injective.extend_apply Ψ 0 ⟨z, hz⟩]

private theorem cauchySource_of_notMem {c : ℂ} {r : ℝ} (D : ℂ → E →L[ℂ] E)
    (Ψ : C(closedBall c r, E →L[ℂ] E)) {z : ℂ} (hz : z ∉ closedBall c r) :
    cauchySource D Ψ z = 0 := by
  rw [cauchySource, extend_apply' _ _ _ fun ⟨w, hw⟩ ↦ hz (hw ▸ w.2)]
  simp

private theorem support_cauchySource_subset {c : ℂ} {r : ℝ} (D : ℂ → E →L[ℂ] E)
    (Ψ : C(closedBall c r, E →L[ℂ] E)) : support (cauchySource D Ψ) ⊆ closedBall c r :=
  fun _ hz ↦ by_contra fun h ↦ hz (cauchySource_of_notMem D Ψ h)

private theorem cauchySource_sub {c : ℂ} {r : ℝ} (D : ℂ → E →L[ℂ] E)
    (Ψ Ψ' : C(closedBall c r, E →L[ℂ] E)) :
    cauchySource D (Ψ - Ψ') = cauchySource D Ψ - cauchySource D Ψ' := by
  ext1 z
  by_cases hz : z ∈ closedBall c r
  · simp only [Pi.sub_apply, cauchySource_of_mem D _ hz, ContinuousMap.sub_apply,
      ContinuousLinearMap.sub_comp, smul_sub]
  · simp [cauchySource_of_notMem D _ hz]

private theorem aestronglyMeasurable_cauchySource {c : ℂ} {r : ℝ} {D : ℂ → E →L[ℂ] E}
    (hD : AEStronglyMeasurable D (volume.restrict (closedBall c r)))
    (Ψ : C(closedBall c r, E →L[ℂ] E)) : AEStronglyMeasurable (cauchySource D Ψ) volume := by
  have he : ContinuousOn (extend Subtype.val Ψ 0) (closedBall c r) := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert Ψ.continuous using 1
    ext1 z
    exact Subtype.val_injective.extend_apply Ψ 0 z
  have heq : cauchySource D Ψ = (closedBall c r).indicator (cauchySource D Ψ) :=
    (indicator_eq_self.2 (support_cauchySource_subset D Ψ)).symm
  rw [heq, aestronglyMeasurable_indicator_iff measurableSet_closedBall]
  exact ((ContinuousLinearMap.compL ℂ E E E).aestronglyMeasurable_comp₂
    (he.aestronglyMeasurable measurableSet_closedBall) hD).const_smul (2 : ℂ)⁻¹

private theorem norm_cauchySource_le_mul_indicator {c : ℂ} {r B : ℝ} {D : ℂ → E →L[ℂ] E}
    {Ψ : C(closedBall c r, E →L[ℂ] E)} (hΨ : ∀ x, ‖Ψ x‖ ≤ B) (z : ℂ) :
    ‖cauchySource D Ψ z‖ ≤ (2⁻¹ * B) * ‖(closedBall c r).indicator D z‖ := by
  by_cases hz : z ∈ closedBall c r
  · rw [cauchySource_of_mem D Ψ hz, indicator_of_mem hz, norm_smul, norm_inv, Complex.norm_ofNat,
      mul_assoc]
    gcongr
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hΨ _) (norm_nonneg _))
  · simp [cauchySource_of_notMem D Ψ hz, indicator_of_notMem hz]

private theorem memLp_cauchySource {c : ℂ} {r : ℝ} {p : ℝ≥0∞} {D : ℂ → E →L[ℂ] E}
    (hD : MemLp D p (volume.restrict (closedBall c r))) (Ψ : C(closedBall c r, E →L[ℂ] E)) :
    MemLp (cauchySource D Ψ) p volume := by
  have hD₀ : MemLp ((closedBall c r).indicator D) p volume :=
    (memLp_indicator_iff_restrict measurableSet_closedBall.nullMeasurableSet).2 hD
  exact hD₀.of_le_mul (aestronglyMeasurable_cauchySource hD.aestronglyMeasurable Ψ)
    (ae_of_all _ (norm_cauchySource_le_mul_indicator Ψ.norm_coe_le_norm))

private theorem toReal_eLpNorm_cauchySource_le {c : ℂ} {r B : ℝ} {p : ℝ≥0∞} {D : ℂ → E →L[ℂ] E}
    (hD : MemLp D p (volume.restrict (closedBall c r))) (hB : 0 ≤ B)
    {Ψ : C(closedBall c r, E →L[ℂ] E)} (hΨ : ∀ x, ‖Ψ x‖ ≤ B) :
    (eLpNorm (cauchySource D Ψ) p volume).toReal ≤
      2⁻¹ * B * (eLpNorm D p (volume.restrict (closedBall c r))).toReal := by
  have hle := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (aestronglyMeasurable_cauchySource hD.aestronglyMeasurable Ψ)
    (ae_of_all _ (norm_cauchySource_le_mul_indicator hΨ)) p
  rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall.nullMeasurableSet] at hle
  have hfin : ENNReal.ofReal (2⁻¹ * B) * eLpNorm D p (volume.restrict (closedBall c r)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hD.eLpNorm_ne_top
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2⁻¹ * B)]
    using ENNReal.toReal_mono hfin hle

private theorem norm_cauchyTransform_cauchySource_le {c : ℂ} {r B : ℝ} {p : ℝ≥0∞} (hp : 2 < p)
    {D : ℂ → E →L[ℂ] E} (hD : MemLp D p (volume.restrict (closedBall c r))) (hB : 0 ≤ B)
    {Ψ : C(closedBall c r, E →L[ℂ] E)} (hΨ : ∀ x, ‖Ψ x‖ ≤ B) {w : ℂ} (hw : w ∈ closedBall c r) :
    ‖cauchyTransform (cauchySource D Ψ) w‖ ≤
      ((2 * Real.pi)⁻¹ * (eLpNorm (truncatedCauchyKernel (2 * r)) p.conjExponent volume).toReal *
        (eLpNorm D p (volume.restrict (closedBall c r))).toReal) * B := by
  have hp1 : 1 < p := (by norm_num : (1 : ℝ≥0∞) < 2).trans hp
  have : p.HolderConjugate p.conjExponent := .conjExponent hp1.le
  have hb := norm_cauchyTransform_le (conjExponent_lt_two hp) (memLp_cauchySource hD Ψ)
    (support_cauchySource_subset D Ψ) hw
  rw [show r + r = 2 * r by ring] at hb
  refine hb.trans ((mul_le_mul_of_nonneg_left
    (toReal_eLpNorm_cauchySource_le hD hB hΨ) (by positivity)).trans (le_of_eq ?_))
  rw [mul_inv_rev]
  ring

/-- **The Cauchy integral equation for supercritical `Lᵖ` coefficients.** For `p > 2` and `D` in
`Lᵖ` on `closedBall c r`, once the product of the `L^q` norm of the truncated Cauchy kernel of
radius `2 r` and the `Lᵖ` norm of `D` is small enough, `Ψ ↦ 1 + T (½ Ψ D)` is a contraction on
continuous endomorphism fields on the closed disc. Its fixed point yields `g ∈ Lᵖ(ℂ)` supported in
the disc with `T g` continuous, `g = ½ (1 + T g) D` on the disc, and `‖T g‖ < 1` there. -/
private theorem exists_cauchyTransform_eq_of_memLp [FiniteDimensional ℂ E] {D : ℂ → E →L[ℂ] E}
    {c : ℂ} {r : ℝ} {p : ℝ≥0∞} (hp : 2 < p)
    (hD : MemLp D p (volume.restrict (closedBall c r)))
    (hK : (2 * Real.pi)⁻¹ * (eLpNorm (truncatedCauchyKernel (2 * r)) p.conjExponent volume).toReal *
      (eLpNorm D p (volume.restrict (closedBall c r))).toReal ≤ 4⁻¹) :
    ∃ g : ℂ → E →L[ℂ] E, MemLp g p volume ∧ support g ⊆ closedBall c r ∧
      Continuous (cauchyTransform g) ∧
      (∀ z ∈ closedBall c r, g z = (2 : ℂ)⁻¹ • (1 + cauchyTransform g z).comp (D z)) ∧
      ∀ z ∈ closedBall c r, ‖cauchyTransform g z‖ < 1 := by
  have := FiniteDimensional.completeSpace ℂ E
  have hp1 : 1 < p := (by norm_num : (1 : ℝ≥0∞) < 2).trans hp
  have : p.HolderConjugate p.conjExponent := .conjExponent hp1.le
  have hq : p.conjExponent < 2 := conjExponent_lt_two hp
  set K := (2 * Real.pi)⁻¹ *
    (eLpNorm (truncatedCauchyKernel (2 * r)) p.conjExponent volume).toReal *
    (eLpNorm D p (volume.restrict (closedBall c r))).toReal
  have hK0 : 0 ≤ K := by positivity
  have hsupp := support_cauchySource_subset (c := c) (r := r) D
  have hLp := memLp_cauchySource hD
  have hcont (Ψ : C(closedBall c r, E →L[ℂ] E)) :
      Continuous (cauchyTransform (cauchySource D Ψ)) :=
    continuous_cauchyTransform_of_memLp hq (hLp Ψ) (hsupp Ψ)
  have hlin (Ψ Ψ' : C(closedBall c r, E →L[ℂ] E)) (w : ℂ) :
      cauchyTransform (cauchySource D Ψ) w - cauchyTransform (cauchySource D Ψ') w =
        cauchyTransform (cauchySource D (Ψ - Ψ')) w := by
    rw [cauchySource_sub, cauchyTransform_sub_of_memLp hq (hLp Ψ) (hsupp Ψ) (hLp Ψ') (hsupp Ψ'),
      Pi.sub_apply]
  let op (Ψ : C(closedBall c r, E →L[ℂ] E)) : C(closedBall c r, E →L[ℂ] E) :=
    ⟨fun w ↦ 1 + cauchyTransform (cauchySource D Ψ) w,
      (continuous_const.add (hcont Ψ)).comp continuous_subtype_val⟩
  have hop : ContractingWith K.toNNReal op := by
    refine ⟨by rw [Real.toNNReal_lt_one]; linarith, LipschitzWith.of_dist_le_mul fun Ψ Ψ' ↦ ?_⟩
    rw [Real.coe_toNNReal _ hK0]
    refine (ContinuousMap.dist_le (by positivity)).2 fun w ↦ ?_
    simp only [op, ContinuousMap.coe_mk, dist_eq_norm, add_sub_add_left_eq_sub, hlin]
    refine norm_cauchyTransform_cauchySource_le hp hD dist_nonneg (fun x ↦ ?_) w.2
    rw [ContinuousMap.sub_apply, ← dist_eq_norm]
    exact ContinuousMap.dist_apply_le_dist x
  set Ψ₀ := ContractingWith.fixedPoint op hop
  set g := cauchySource D Ψ₀ with hg
  have hΨ₀ (z : ℂ) (hz : z ∈ closedBall c r) : Ψ₀ ⟨z, hz⟩ = 1 + cauchyTransform g z := by
    simpa only [op, ContinuousMap.coe_mk, hg] using
      congr_arg (fun Φ : C(closedBall c r, E →L[ℂ] E) ↦ Φ ⟨z, hz⟩) hop.fixedPoint_isFixedPt.symm
  have hnorm : ‖Ψ₀‖ ≤ 4 / 3 := by
    have h1 : ‖Ψ₀‖ ≤ 1 + 4⁻¹ * ‖Ψ₀‖ := by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun w ↦ ?_
      rw [hΨ₀ w w.2]
      exact (norm_add_le _ _).trans ((add_le_add ContinuousLinearMap.norm_id_le
        (norm_cauchyTransform_cauchySource_le hp hD (norm_nonneg _) Ψ₀.norm_coe_le_norm w.2)).trans
        (by gcongr))
    linarith
  refine ⟨g, hLp Ψ₀, hsupp Ψ₀, hcont Ψ₀, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hg, cauchySource_of_mem D Ψ₀ hz, hΨ₀ z hz]
  · calc ‖cauchyTransform g z‖ ≤ K * ‖Ψ₀‖ :=
          norm_cauchyTransform_cauchySource_le hp hD (norm_nonneg _) Ψ₀.norm_coe_le_norm hz
      _ ≤ 4⁻¹ * (4 / 3) := by gcongr
      _ < 1 := by norm_num

/-- Choosing a small positive radius `r ≤ R` so that the truncated Cauchy kernel of radius `2 r`
makes the contraction constant at most `1/4`. -/
private theorem exists_pos_radius_le_quarter {q : ℝ≥0∞} (hq : q < 2) {R : ℝ} (hR : 0 < R)
    (M : ℝ) :
    ∃ r, 0 < r ∧ r ≤ R ∧
      (2 * Real.pi)⁻¹ * (eLpNorm (truncatedCauchyKernel (2 * r)) q volume).toReal * M ≤ 4⁻¹ := by
  have h2r : Tendsto (fun r : ℝ ↦ 2 * r) (𝓝 0) (𝓝 0) :=
    ((continuous_const (y := (2 : ℝ))).mul continuous_id).tendsto' 0 0 (mul_zero 2)
  have hlim : Tendsto (fun r : ℝ ↦
      (2 * Real.pi)⁻¹ * (eLpNorm (truncatedCauchyKernel (2 * r)) q volume).toReal * M)
      (𝓝 0) (𝓝 0) := by
    have hk := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      ((tendsto_eLpNorm_truncatedCauchyKernel_nhds_zero hq).comp h2r)
    simpa only [ENNReal.toReal_zero, mul_zero, zero_mul, Function.comp_def] using
      (hk.const_mul (2 * Real.pi)⁻¹).mul_const M
  obtain ⟨δ, hδ, hδle⟩ := Metric.eventually_nhds_iff.1
    (hlim.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < 4⁻¹)))
  refine ⟨min R (δ / 2), lt_min hR (half_pos hδ), min_le_left _ _, (hδle ?_).le⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (lt_min hR (half_pos hδ))]
  exact (min_le_right _ _).trans_lt (half_lt_self hδ)

/-- Where `Ψ ∈ W^{1,p}_loc` satisfies `bar∂Ψ = ½ Ψ D` with `D ξ = C ξ` and `ξ` solves
`∂ₛξ + i ∂ₜξ + C ξ = 0` weakly, `Ψ ξ` satisfies `bar∂(Ψ ξ) = 0` weakly and is therefore
holomorphic. -/
private theorem differentiableOn_apply_of_hasWeakConjWirtingerDerivOn [FiniteDimensional ℂ E]
    {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ⊤) {B : Opens ℂ} {Ψ : ℂ → E →L[ℂ] E}
    {g D : ℂ → E →L[ℂ] E} {C : ℂ → E →L[ℝ] E} {ξ : ℂ → E}
    (hΨc : ContinuousOn Ψ B) (hΨw : MemWkpLoc p B 1 Ψ)
    (hΨg : HasWeakConjWirtingerDerivOn volume B Ψ g)
    (hg : ∀ z ∈ (B : Set ℂ), g z = (2 : ℂ)⁻¹ • (Ψ z).comp (D z))
    (hDC : ∀ z ∈ (B : Set ℂ), D z (ξ z) = C z (ξ z))
    (hξ : IsWeakLinearCauchyRiemannOn p B (fun _ ↦ I • ContinuousLinearMap.id ℝ E) C ξ) :
    DifferentiableOn ℂ (fun z ↦ Ψ z (ξ z)) B := by
  have := FiniteDimensional.completeSpace ℂ E
  lift p to ℝ≥0 using hp_top
  have hp' : 2 < p := by exact_mod_cast hp
  obtain ⟨DΨ, hDΨ, hDΨp⟩ := hΨw.exists_weakFDeriv_of_isOpen
  rw [memWkpLoc_zero_iff] at hDΨp
  obtain ⟨hξc, hξp, Dξ, hDξ, hDξp, hξeq⟩ := isWeakLinearCauchyRiemannOn_iff_of_isOpen.1 hξ
  let ev : (E →L[ℂ] E) →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ
  have hDσ := hDΨ.bilin_of_memLpLoc ev hp' (one_lt_two.trans hp') le_rfl hΨc.memLpLoc hDΨp hDξ
    hξp hDξp
  have hw0 : HasWeakConjWirtingerDerivOn volume B (fun z ↦ Ψ z (ξ z)) 0 := by
    refine hDσ.hasWeakConjWirtingerDerivOn.congr_ae_deriv ?_
    filter_upwards [ae_restrict_mem B.isOpen.measurableSet,
      hDΨ.hasWeakConjWirtingerDerivOn.ae_eq hΨg, hξeq] with z hz hzΨ hzξ
    have h2 : (2 : ℂ)⁻¹ ≠ 0 := by norm_num
    have hΨz : DΨ z 1 + I • DΨ z I = (Ψ z).comp (D z) :=
      smul_right_injective _ h2 (hzΨ.trans (hg z hz))
    simp only [smul_apply, ContinuousLinearMap.id_apply] at hzξ
    have hξz : Dξ z 1 + I • Dξ z I = -C z (ξ z) := eq_neg_of_add_eq_zero_left hzξ
    have hcalc : (ev.precompL ℂ (DΨ z) (ξ z) + ev.precompR ℂ (Ψ z) (Dξ z)) 1 +
        I • (ev.precompL ℂ (DΨ z) (ξ z) + ev.precompR ℂ (Ψ z) (Dξ z)) I =
        (DΨ z 1 + I • DΨ z I) (ξ z) + Ψ z (Dξ z 1 + I • Dξ z I) := by
      change (DΨ z 1) (ξ z) + Ψ z (Dξ z 1) + I • ((DΨ z I) (ξ z) + Ψ z (Dξ z I)) =
        ((DΨ z 1) (ξ z) + I • (DΨ z I) (ξ z)) + Ψ z (Dξ z 1 + I • Dξ z I)
      rw [smul_add, map_add, map_smul]
      abel
    rw [hcalc, hΨz, hξz, ContinuousLinearMap.comp_apply, hDC z hz, map_neg, add_neg_cancel,
      smul_zero, Pi.zero_apply]
  exact hw0.differentiableOn ((ev.continuous.comp_continuousOn hΨc).clm_apply hξc)

/-- **The Sobolev similarity principle on a complex inner product space** for `J = i`. -/
private theorem exists_similarity_of_isWeakLinearCauchyRiemannOn_I_smul_id_of_innerProductSpace
    [FiniteDimensional ℂ E] {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ⊤) {Ω : Set ℂ}
    (hΩ : IsOpen Ω) {C : ℂ → E →L[ℝ] E} (hC : MemLpLoc p Ω C) {ξ : ℂ → E}
    (hξ : IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ E) C ξ)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ r, 0 < r ∧ ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → E →L[ℂ] E) (σ : ℂ → E),
      ContinuousOn Φ (ball z₀ r) ∧ MemWkpLoc p (ball z₀ r) 1 Φ ∧
      (∀ z ∈ ball z₀ r, IsUnit (Φ z)) ∧ DifferentiableOn ℂ σ (ball z₀ r) ∧
      EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ E
  have hp1 : 1 < p := (by norm_num : (1 : ℝ≥0∞) < 2).trans hp
  obtain ⟨R₀, hR₀, hR₀Ω⟩ := Metric.mem_nhds_iff.1 (hΩ.mem_nhds hz₀)
  have hRΩ : closedBall z₀ (R₀ / 2) ⊆ Ω := (closedBall_subset_ball (half_lt_self hR₀)).trans hR₀Ω
  let D : ℂ → E →L[ℂ] E := fun z ↦ rankOneDivNormSq ℂ (C z (ξ z)) (ξ z)
  have hDR : MemLp D p (volume.restrict (closedBall z₀ (R₀ / 2))) :=
    (memLpLoc_iff.1 hC _ hRΩ (isCompact_closedBall _ _)).rankOneDivNormSq_apply
      ((hξ.continuousOn.mono hRΩ).aestronglyMeasurable measurableSet_closedBall)
  obtain ⟨r, hr, hrR, hrK⟩ := exists_pos_radius_le_quarter (conjExponent_lt_two hp) (half_pos hR₀)
    (eLpNorm D p (volume.restrict (closedBall z₀ (R₀ / 2)))).toReal
  have hsubR : closedBall z₀ r ⊆ closedBall z₀ (R₀ / 2) := closedBall_subset_closedBall hrR
  have hDr : MemLp D p (volume.restrict (closedBall z₀ r)) :=
    hDR.mono_measure (Measure.restrict_mono hsubR le_rfl)
  have hK : (2 * Real.pi)⁻¹ *
      (eLpNorm (truncatedCauchyKernel (2 * r)) p.conjExponent volume).toReal *
      (eLpNorm D p (volume.restrict (closedBall z₀ r))).toReal ≤ 4⁻¹ :=
    (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hDR.eLpNorm_ne_top
      (eLpNorm_mono_measure D (Measure.restrict_mono hsubR le_rfl))) (by positivity)).trans hrK
  obtain ⟨g, hg, hsupp, hTg, hgeq, hTg1⟩ := exists_cauchyTransform_eq_of_memLp hp hDr hK
  set Ψ : ℂ → E →L[ℂ] E := fun z ↦ 1 + cauchyTransform g z with hΨ
  let B : Opens ℂ := ⟨ball z₀ r, isOpen_ball⟩
  have hball : ball z₀ r ⊆ Ω := ball_subset_closedBall.trans (hsubR.trans hRΩ)
  have hunit (z : ℂ) (hz : z ∈ ball z₀ r) : IsUnit (Ψ z) := by
    by_contra h
    exact nonunits.subset_compl_ball h
      (by simpa only [mem_ball_iff_norm, hΨ, add_sub_cancel_left] using
        hTg1 z (ball_subset_closedBall hz))
  have hΨc : ContinuousOn Ψ B := (continuous_const.add hTg).continuousOn
  have hΨg : HasWeakConjWirtingerDerivOn volume B Ψ g := by
    convert (differentiableOn_const (1 : E →L[ℂ] E)).hasWeakConjWirtingerDerivOn_zero.add
      (hasWeakConjWirtingerDerivOn_cauchyTransform_of_memLp (r := ⟨r, hr.le⟩)
        hp1.le (hg.mono_measure Measure.restrict_le_self) hsupp B) using 1
    exact (zero_add g).symm
  have hΨw : MemWkpLoc p B 1 Ψ := hΨg.memWkpLoc_one hp1 hp_top hΨc.memLpLoc
    (hg.mono_measure Measure.restrict_le_self).memLpLoc
  have hΦc : ContinuousOn (fun z ↦ Ring.inverse (Ψ z)) (ball z₀ r) := fun z hz ↦ by
    have hc := NormedRing.inverse_continuousAt (hunit z hz).unit
    rw [IsUnit.unit_spec] at hc
    exact (hc.comp (continuous_const.add hTg).continuousAt).continuousWithinAt
  refine ⟨r, hr, hball, fun z ↦ Ring.inverse (Ψ z), fun z ↦ Ψ z (ξ z), hΦc,
    hΨw.ring_inverse hΨc hunit, fun z hz ↦ ?_,
    differentiableOn_apply_of_hasWeakConjWirtingerDerivOn hp hp_top hΨc hΨw hΨg
      (fun z hz ↦ hgeq z (ball_subset_closedBall hz))
      (fun z _ ↦ (C z).rankOneDivNormSq_apply_map _) (hξ.mono hball),
    fun z hz ↦ ?_⟩
  · beta_reduce
    rw [← (hunit z hz).unit_spec, Ring.inverse_unit]
    exact Units.isUnit _
  · simpa using (congr($(Ring.inverse_mul_cancel _ (hunit z hz)) (ξ z))).symm

end InnerProductSpace

/-! ### The Sobolev similarity principle for `J = i` and variable `J` -/

section ComplexTarget

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- **The Sobolev similarity principle for `J = i`.** Let `2 < p < ∞`, let `Ω ⊆ ℂ` be open, let
`C` be a locally `Lᵖ` field of real-linear endomorphisms of a finite-dimensional complex normed
space `V`, and let `ξ` solve `∂ₛξ + i ∂ₜξ + C ξ = 0` weakly on `Ω`. Around every `z₀ ∈ Ω` there
is a disc in `Ω` on which `ξ = Φ σ`, with `Φ` a continuous `W^{1,p}_loc` family of invertible
complex-linear maps and `σ` holomorphic. -/
theorem exists_similarity_of_isWeakLinearCauchyRiemannOn_I_smul_id
    {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ⊤) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {C : ℂ → V →L[ℝ] V} (hC : MemLpLoc p Ω C) {ξ : ℂ → V}
    (hξ : IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ V) C ξ)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ r, 0 < r ∧ ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → V →L[ℂ] V) (σ : ℂ → V),
      ContinuousOn Φ (ball z₀ r) ∧ MemWkpLoc p (ball z₀ r) 1 Φ ∧
      (∀ z ∈ ball z₀ r, IsUnit (Φ z)) ∧ DifferentiableOn ℂ σ (ball z₀ r) ∧
      EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ V
  let e : V ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let eR : V ≃L[ℝ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    ContinuousLinearEquiv.equivOfInverse (e.toContinuousLinearMap.restrictScalars ℝ)
      (e.symm.toContinuousLinearMap.restrictScalars ℝ) (fun x ↦ e.symm_apply_apply x)
      (fun x ↦ e.apply_symm_apply x)
  let C' : ℂ → EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →L[ℝ]
      EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    fun z ↦ (eR : V →L[ℝ] _).comp ((C z).comp (eR.symm : _ →L[ℝ] V))
  have hC' : MemLpLoc p Ω C' :=
    (hC.clm_comp_continuousOn continuousOn_const).continuousOn_clm_comp continuousOn_const
  have hξ' : IsWeakLinearCauchyRiemannOn p Ω
      (fun _ ↦ I • ContinuousLinearMap.id ℝ _) C' (fun z ↦ eR (ξ z)) := by
    have h := eR.isWeakCauchyRiemannOn_iff_comp.1 hξ
    refine (isWeakCauchyRiemannOn_congr_ae (Eventually.of_forall fun z ↦ ?_)
      (Eventually.of_forall fun z ↦ ?_)).1 h
    · refine ContinuousLinearMap.ext fun w ↦ ?_
      change e (I • e.symm w) = I • w
      simp
    · simp [C']
  obtain ⟨r, hr, hrΩ, Φ, σ, hΦc, hΦw, hΦu, hσ, hξσ⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemannOn_I_smul_id_of_innerProductSpace hp hp_top hΩ
      hC' hξ' hz₀
  let conjL : (EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →L[ℂ]
      EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) →L[ℝ] (V →L[ℂ] V) :=
    e.symm.conjContinuousAlgEquiv.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  refine ⟨r, hr, hrΩ, fun z ↦ e.symm.conjContinuousAlgEquiv (Φ z), fun z ↦ e.symm (σ z),
    conjL.continuous.comp_continuousOn hΦc, hΦw.clm_comp conjL,
    fun z hz ↦ (hΦu z hz).map _,
    ((e.symm : _ →L[ℂ] V).differentiable.comp_differentiableOn hσ).congr fun _ _ ↦ rfl,
    fun z hz ↦ ?_⟩
  have h : e (ξ z) = Φ z (σ z) := hξσ hz
  simpa using congrArg e.symm h

/-- **The Carleman vector similarity principle** (McDuff–Salamon, Theorem 2.3.5). Let `V` be a
finite-dimensional complex normed space, let `2 < p < ∞`, let `Ω ⊆ ℂ` be open, let `J` be a
continuous `W^{1,p}_loc` field of real-linear endomorphisms of `V` with `J² = -1` on `Ω`, and let
`C` be a locally `Lᵖ` field of real-linear endomorphisms of `V`. If `ξ` solves
`∂ₛξ + J(z) ∂ₜξ + C(z) ξ = 0` weakly on `Ω`, then around every `z₀ ∈ Ω` there is a disc in `Ω`
carrying a continuous `W^{1,p}_loc` family `Φ` of invertible real-linear endomorphisms of `V` and a
holomorphic `σ : ℂ → V` such that `J(z) ∘ Φ(z) = Φ(z) ∘ i` and `ξ(z) = Φ(z)(σ(z))` on the disc. -/
theorem exists_similarity_of_isWeakLinearCauchyRiemannOn
    {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ⊤) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {J C : ℂ → V →L[ℝ] V} (hJc : ContinuousOn J Ω) (hJw : MemWkpLoc p Ω 1 J)
    (hJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    {ξ : ℂ → V} (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ r, 0 < r ∧ ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → V →L[ℝ] V) (σ : ℂ → V),
      ContinuousOn Φ (ball z₀ r) ∧ MemWkpLoc p (ball z₀ r) 1 Φ ∧
      (∀ z ∈ ball z₀ r, IsUnit (Φ z)) ∧
      (∀ z ∈ ball z₀ r, J z ∘L Φ z = Φ z ∘L (I • ContinuousLinearMap.id ℝ V)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧ EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ V
  obtain ⟨Φ₁, hΦ₁⟩ := (J z₀).exists_continuousLinearEquiv_comp_eq_comp_I_smul (hJ z₀ hz₀)
  obtain ⟨r₁, hr₁, hr₁Ω, hu₁⟩ :=
    exists_ball_isUnit_standardFrame (Φ₁ := Φ₁) hΩ hz₀ hJc (hJ z₀ hz₀)
  let B₁ : Opens ℂ := ⟨ball z₀ r₁, isOpen_ball⟩
  set Φ₀ := standardFrame J z₀ Φ₁
  have hΦ₀w : MemWkpLoc p B₁ 1 Φ₀ := memWkpLoc_standardFrame (hJw.mono hr₁Ω)
  obtain ⟨DΦ₀, hDΦ₀, hDΦ₀p⟩ := hΦ₀w.exists_weakFDeriv_of_isOpen
  rw [memWkpLoc_zero_iff] at hDΦ₀p
  lift p to ℝ≥0 using hp_top
  have hp' : 2 < p := by exact_mod_cast hp
  have hη : IsWeakLinearCauchyRiemannOn p B₁ (fun _ ↦ I • ContinuousLinearMap.id ℝ V)
      (frameCoeff J C Φ₀ DΦ₀) (fun z ↦ Ring.inverse (Φ₀ z) (ξ z)) :=
    (isWeakLinearCauchyRiemannOn_iff_standardFrame hp' (hJc.mono hr₁Ω)
      (fun z hz ↦ hJ z (hr₁Ω hz)) (hJ z₀ hz₀) hΦ₁ hu₁ hDΦ₀ hDΦ₀p).1 (hξ.mono hr₁Ω)
  have hC' : MemLpLoc p B₁ (frameCoeff J C Φ₀ DΦ₀) :=
    (memLpLoc_frameCoeff_iff (C := C) isOpen_ball.measurableSet
      (continuousOn_standardFrame (hJc.mono hr₁Ω)) hDΦ₀p hu₁ (hJc.mono hr₁Ω)).2 (hC.mono_set hr₁Ω)
  obtain ⟨r, hr, hrr₁, Φ₂, σ, hΦ₂c, hΦ₂w, hΦ₂u, hσ, hησ⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemannOn_I_smul_id hp ENNReal.coe_ne_top isOpen_ball
      hC' hη (mem_ball_self hr₁)
  let B : Opens ℂ := ⟨ball z₀ r, isOpen_ball⟩
  let restL := ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ
  have hΦ₂w' : MemWkpLoc p B 1 (fun z ↦ (Φ₂ z).restrictScalars ℝ) := hΦ₂w.clm_comp restL
  have hΦw : MemWkpLoc p B 1 (fun z ↦ Φ₀ z ∘L (Φ₂ z).restrictScalars ℝ) :=
    (hΦ₀w.mono hrr₁).bilin (ContinuousLinearMap.compL ℝ V V V) hp' (one_lt_two.trans hp') le_rfl
      hΦ₂w'
  refine ⟨r, hr, hrr₁.trans hr₁Ω, fun z ↦ Φ₀ z ∘L (Φ₂ z).restrictScalars ℝ, σ,
    ((continuousOn_standardFrame hJc).mono (hrr₁.trans hr₁Ω)).clm_comp
      (restL.continuous.comp_continuousOn hΦ₂c),
    hΦw, fun z hz ↦ ?_, fun z hz ↦ ?_, hσ, fun z hz ↦ ?_⟩
  · obtain ⟨u, hu⟩ := hΦ₂u z hz
    exact (hu₁ z (hrr₁ hz)).mul
      (hu ▸ ⟨((ContinuousLinearEquiv.unitsEquiv ℂ V u).restrictScalars ℝ).toUnit, rfl⟩)
  · have hJ₀ := comp_standardFrame (hJ z (hr₁Ω (hrr₁ hz))) (hJ z₀ hz₀) hΦ₁
    ext v
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      smul_apply, ContinuousLinearMap.id_apply, map_smul] using
      congr($hJ₀ (Φ₂ z v))
  · have hinv : Φ₀ z (Ring.inverse (Φ₀ z) (ξ z)) = ξ z := by
      simpa using congr($(Ring.mul_inverse_cancel _ (hu₁ z (hrr₁ hz))) (ξ z))
    simpa [hinv] using congrArg (Φ₀ z) (hησ hz)

/-- A weak Sobolev solution of `∂ₛξ + J ∂ₜξ + C ξ = 0` on an open set `Ω` (`2 < p < ∞`,
`J ∈ W^{1,p}_loc` continuous with `J² = -1`, `C ∈ Lᵖ_loc`) has a local similarity factorization
(`TauCeti.HasSimilarityFactorizationAt`) at every point of `Ω`. -/
theorem hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn
    {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ⊤) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {J C : ℂ → V →L[ℝ] V} (hJc : ContinuousOn J Ω) (hJw : MemWkpLoc p Ω 1 J)
    (hJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    {ξ : ℂ → V} (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    HasSimilarityFactorizationAt ξ z₀ := by
  have := FiniteDimensional.completeSpace ℂ V
  obtain ⟨r, hr, -, Φ, σ, hΦc, -, hΦu, -, hσ, hξσ⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemannOn hp hp_top hΩ hJc hJw hJ hC hξ hz₀
  exact .of_eqOn_ball hr hΦc (hΦu z₀ (mem_ball_self hr)) hσ hξσ

/-- **Positive orders of zeros** for weak Sobolev solutions on complex targets. On an open
preconnected `Ω`, let `ξ` solve `∂ₛξ + J ∂ₜξ + C ξ = 0` weakly (`2 < p < ∞`) without vanishing
identically on `Ω`. At every zero `z₀ ∈ Ω`, `‖ξ z‖` is comparable to `‖z - z₀‖ ^ m` for a unique
positive integer `m`, which equals the analytic order at `z₀` of the holomorphic factor `σ` in
every local similarity factorization `ξ = Φ σ`. -/
theorem exists_analyticOrderAt_eq_of_isWeakLinearCauchyRiemannOn
    {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ⊤) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) {J C : ℂ → V →L[ℝ] V} (hJc : ContinuousOn J Ω)
    (hJw : MemWkpLoc p Ω 1 J) (hJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (hC : MemLpLoc p Ω C) {ξ : ℂ → V} (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ)
    (hne : ∃ z ∈ Ω, ξ z ≠ 0) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hξ₀ : ξ z₀ = 0) :
    ∃ m : ℕ, 0 < m ∧ (ξ =Θ[𝓝 z₀] fun z ↦ (z - z₀) ^ m) ∧
      ∀ (Φ : ℂ → V →L[ℝ] V) (σ : ℂ → V), ContinuousAt Φ z₀ → IsUnit (Φ z₀) →
        AnalyticAt ℂ σ z₀ → (∀ᶠ z in 𝓝 z₀, ξ z = Φ z (σ z)) → analyticOrderAt σ z₀ = m := by
  have := FiniteDimensional.completeSpace ℂ V
  exact exists_analyticOrderAt_eq_of_hasSimilarityFactorizationAt hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn hp hp_top hΩ hJc hJw
      hJ hC hξ hz) hne hz₀ hξ₀

/-- **Converse to the vector similarity principle.** Let `2 < p < ∞`, let `Φ` be a continuous
family of invertible real-linear maps on an open set `Ω` with weak derivative `DΦ ∈ Lᵖ_loc`, let
`J` be continuous on `Ω` with `J Φ = Φ i`, and let `σ : ℂ → V` be holomorphic on `Ω`. Then
`C = -(∂ₛΦ + J ∂ₜΦ) Φ⁻¹` lies in `Lᵖ_loc(Ω)` and `ξ = Φ σ` solves `∂ₛξ + J ∂ₜξ + C ξ = 0` weakly
on `Ω`. -/
theorem isWeakLinearCauchyRiemannOn_clm_apply_of_differentiableOn
    {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ⊤) {Ω : Opens ℂ} {J Φ : ℂ → V →L[ℝ] V}
    {DΦ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {σ : ℂ → V} (hJc : ContinuousOn J Ω)
    (hΦc : ContinuousOn Φ Ω) (hΦ : HasWeakFDerivOn volume Ω Φ DΦ) (hDΦ : MemLpLoc p Ω DΦ)
    (hu : ∀ z ∈ Ω, IsUnit (Φ z))
    (hJ : ∀ z ∈ Ω, J z ∘L Φ z = Φ z ∘L (I • ContinuousLinearMap.id ℝ V))
    (hσ : DifferentiableOn ℂ σ Ω) :
    MemLpLoc p Ω (fun z ↦ -(DΦ z 1 + J z ∘L DΦ z I) ∘L Ring.inverse (Φ z)) ∧
      IsWeakLinearCauchyRiemannOn p Ω J
        (fun z ↦ -(DΦ z 1 + J z ∘L DΦ z I) ∘L Ring.inverse (Φ z))
        (fun z ↦ Φ z (σ z)) := by
  have := FiniteDimensional.completeSpace ℂ V
  set C : ℂ → V →L[ℝ] V := fun z ↦ -(DΦ z 1 + J z ∘L DΦ z I) ∘L Ring.inverse (Φ z)
  have hfc (z : ℂ) (hz : z ∈ (Ω : Set ℂ)) : frameCoeff J C Φ DΦ z = 0 := by
    have hinv (v : V) : Ring.inverse (Φ z) (Φ z v) = v := by
      simpa using congr($(Ring.inverse_mul_cancel _ (hu z hz)) v)
    ext v
    simp [frameCoeff_apply, C, hinv]
  have hC : MemLpLoc p Ω C :=
    (memLpLoc_frameCoeff_iff (C := C) Ω.isOpen.measurableSet hΦc hDΦ hu hJc).1
      (memLpLoc_zero.congr_mono (fun z hz ↦ by simp [hfc z hz]) subset_rfl)
  lift p to ℝ≥0 using hp_top
  have hp' : 2 < p := by exact_mod_cast hp
  have hp1 : (1 : ℝ≥0∞) < p := by exact_mod_cast one_lt_two.trans hp'
  have hσ0 : IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ V) 0 σ := by
    have h := isWeakCauchyRiemannOn_I_smul_id_zero_iff.2 ⟨hσ.continuousOn,
      hσ.hasWeakConjWirtingerDerivOn_zero.memWkpLoc_one hp1 ENNReal.coe_ne_top
        hσ.continuousOn.memLpLoc memLpLoc_zero,
      hσ.hasWeakConjWirtingerDerivOn_zero⟩
    exact (isWeakCauchyRiemannOn_congr_ae (Eventually.of_forall fun _ ↦ rfl)
      (Eventually.of_forall fun _ ↦ by simp)).1 h
  refine ⟨hC, (isWeakLinearCauchyRiemannOn_iff_frame hp' hΦc hΦ hDΦ hu hJ).2 ?_⟩
  have hσ1 : IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ V) 0
      (fun z ↦ Ring.inverse (Φ z) (Φ z (σ z))) := by
    refine hσ0.congr fun z hz ↦ ?_
    simpa using (congr($(Ring.inverse_mul_cancel _ (hu z hz)) (σ z))).symm
  refine (isWeakCauchyRiemannOn_congr_ae (Eventually.of_forall fun _ ↦ rfl)
    ((ae_restrict_iff' measurableSet_interior).2 (Eventually.of_forall fun z hz ↦ ?_))).1 hσ1
  simp [hfc z (interior_subset hz)]

end ComplexTarget

/-! ### Unique continuation and isolated zeros on real targets -/

section RealTarget

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {p : ℝ≥0∞} {Ω : Set ℂ} {J C : ℂ → G →L[ℝ] G} {ξ : ℂ → G}

/-- Transporting a real-target linear Cauchy–Riemann equation with `J² = -1` along a constant
real-linear isomorphism `G ≃L[ℝ] ℂⁿ` gives `HasSimilarityFactorizationAt` for the coordinate map
at every point of `Ω`. -/
private theorem exists_euclideanSpace_hasSimilarityFactorizationAt
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : IsOpen Ω) (hJc : ContinuousOn J Ω)
    (hJw : MemWkpLoc p Ω 1 J) (hJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ G)
    (hC : MemLpLoc p Ω C) (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ (n : ℕ) (e : G ≃L[ℝ] EuclideanSpace ℂ (Fin n)),
      ∀ z ∈ Ω, HasSimilarityFactorizationAt (fun w ↦ e (ξ w)) z := by
  obtain ⟨n, Ψ, -⟩ :=
    (J z₀).exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul (hJ z₀ hz₀)
  let e := Ψ.symm
  let conjE : (G →L[ℝ] G) →L[ℝ]
      (EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n)) :=
    (e.arrowCongr e).toContinuousLinearMap
  have hJ' (z : ℂ) (hz : z ∈ Ω) :
      conjE (J z) ∘L conjE (J z) = -ContinuousLinearMap.id ℝ _ := by
    refine ContinuousLinearMap.ext fun v ↦ ?_
    have hzz := congr($(hJ z hz) (Ψ v))
    simpa [conjE, e] using congrArg e hzz
  have hξ' : IsWeakLinearCauchyRiemannOn p Ω (fun z ↦ conjE (J z)) (fun z ↦ conjE (C z))
      (fun z ↦ e (ξ z)) := by
    refine (isWeakCauchyRiemannOn_congr_ae (Eventually.of_forall fun z ↦ rfl)
      (Eventually.of_forall fun z ↦ ?_)).1 (e.isWeakCauchyRiemannOn_iff_comp.1 hξ)
    simp [conjE, e]
  exact ⟨n, e, fun z hz ↦ hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn hp hp_top hΩ
    (conjE.continuous.comp_continuousOn hJc) (hJw.clm_comp conjE) hJ' (hC.clm_comp conjE) hξ' hz⟩

/-- **Local zero dichotomy** for weak Sobolev solutions. At every point `z₀ ∈ Ω`, a weak solution
either vanishes in a neighbourhood of `z₀` or has no zeros in a punctured neighbourhood of `z₀`. -/
theorem eventually_eq_zero_or_eventually_ne_zero_of_isWeakLinearCauchyRiemannOn
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : IsOpen Ω) (hJc : ContinuousOn J Ω)
    (hJw : MemWkpLoc p Ω 1 J) (hJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ G)
    (hC : MemLpLoc p Ω C) (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    (∀ᶠ z in 𝓝 z₀, ξ z = 0) ∨ ∀ᶠ z in 𝓝[≠] z₀, ξ z ≠ 0 := by
  obtain ⟨n, e, hfac⟩ := exists_euclideanSpace_hasSimilarityFactorizationAt hp hp_top hΩ hJc hJw
    hJ hC hξ hz₀
  have h := eventually_eq_zero_or_eventually_ne_zero_of_hasSimilarityFactorizationAt hΩ
    (e.continuous.comp_continuousOn hξ.continuousOn) (fun z hz _ ↦ hfac z hz) hz₀
  exact h.imp (fun h0 ↦ h0.mono fun z hz ↦ (map_eq_zero_iff e e.injective).1 hz)
    (fun hne ↦ hne.mono fun z hz h0 ↦ hz (by simp [h0]))

/-- **Unique continuation from a neighbourhood** for weak Sobolev solutions. On a preconnected open
set `Ω`, a weak solution vanishing near one point of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_eventually_eq_zero
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJc : ContinuousOn J Ω) (hJw : MemWkpLoc p Ω 1 J)
    (hJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ G) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ᶠ z in 𝓝 z₀, ξ z = 0) : EqOn ξ 0 Ω := by
  obtain ⟨n, e, hfac⟩ := exists_euclideanSpace_hasSimilarityFactorizationAt hp hp_top hΩ hJc hJw
    hJ hC hξ hz₀
  have he := eqOn_zero_of_hasSimilarityFactorizationAt_of_eventually_eq_zero hΩ hΩc
    (e.continuous.comp_continuousOn hξ.continuousOn) (fun z hz _ ↦ hfac z hz) hz₀
    (h₀.mono fun z hz ↦ by simp [hz])
  exact fun z hz ↦ (map_eq_zero_iff e e.injective).1 (he hz)

/-- **Unique continuation from an open set** for weak Sobolev solutions. On a preconnected open set
`Ω`, a weak solution vanishing on a nonempty open subset of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_eqOn_zero
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJc : ContinuousOn J Ω) (hJw : MemWkpLoc p Ω 1 J)
    (hJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ G) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) {U : Set ℂ} (hU : IsOpen U)
    (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (h₀ : EqOn ξ 0 U) : EqOn ξ 0 Ω := by
  obtain ⟨z₀, hz₀⟩ := hUne
  exact eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_eventually_eq_zero hp hp_top hΩ hΩc hJc hJw hJ
    hC hξ (hUΩ hz₀) (eventually_of_mem (hU.mem_nhds hz₀) h₀)

/-- **Unique continuation from a zero of infinite order** for weak Sobolev solutions. On a
preconnected open set `Ω`, a weak solution satisfying `ξ = O((z - z₀) ^ n)` near one point
`z₀ ∈ Ω` for every `n : ℕ` vanishes on `Ω`. -/
theorem eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_forall_isBigO
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJc : ContinuousOn J Ω) (hJw : MemWkpLoc p Ω 1 J)
    (hJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ G) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n) : EqOn ξ 0 Ω := by
  obtain ⟨n, e, hfac⟩ := exists_euclideanSpace_hasSimilarityFactorizationAt hp hp_top hΩ hJc hJw
    hJ hC hξ hz₀
  have he := eqOn_zero_of_hasSimilarityFactorizationAt_of_forall_isBigO hΩ hΩc
    (e.continuous.comp_continuousOn hξ.continuousOn) (fun z hz _ ↦ hfac z hz) hz₀
    fun m ↦ (e.toContinuousLinearMap.isBigO_comp _ _).trans (h₀ m)
  exact fun z hz ↦ (map_eq_zero_iff e e.injective).1 (he hz)

/-- **Isolated zeros** of weak Sobolev solutions. On a preconnected open set `Ω`, the zeros of a
weak solution that is not identically zero on `Ω` form a discrete subset of `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_isWeakLinearCauchyRiemannOn
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJc : ContinuousOn J Ω) (hJw : MemWkpLoc p Ω 1 J)
    (hJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ G) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hne : ∃ z ∈ Ω, ξ z ≠ 0) :
    {z | ξ z ≠ 0} ∈ codiscreteWithin Ω := by
  obtain ⟨z₁, hz₁, hξ₁⟩ := hne
  obtain ⟨n, e, hfac⟩ := exists_euclideanSpace_hasSimilarityFactorizationAt hp hp_top hΩ hJc hJw
    hJ hC hξ hz₁
  have hc := setOf_ne_zero_mem_codiscreteWithin_of_hasSimilarityFactorizationAt hΩ hΩc
    (e.continuous.comp_continuousOn hξ.continuousOn) (fun z hz _ ↦ hfac z hz)
    ⟨z₁, hz₁, fun h0 ↦ hξ₁ ((map_eq_zero_iff e e.injective).1 h0)⟩
  exact Filter.mem_of_superset hc fun z hz h0 ↦ hz (by simp [h0])

/-- **Positive vanishing orders** on real targets. On a preconnected open set `Ω`, at every zero
`z₀ ∈ Ω` of a weak solution not identically zero on `Ω`, `‖ξ z‖` is comparable near `z₀` to
`‖z - z₀‖ ^ m` for some positive integer `m`. -/
theorem exists_pos_isTheta_pow_of_isWeakLinearCauchyRiemannOn
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJc : ContinuousOn J Ω) (hJw : MemWkpLoc p Ω 1 J)
    (hJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ G) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hne : ∃ z ∈ Ω, ξ z ≠ 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hξ₀ : ξ z₀ = 0) :
    ∃ m : ℕ, 0 < m ∧ (ξ =Θ[𝓝 z₀] fun z ↦ (z - z₀) ^ m) := by
  obtain ⟨z₁, hz₁, hξ₁⟩ := hne
  obtain ⟨n, e, hfac⟩ := exists_euclideanSpace_hasSimilarityFactorizationAt hp hp_top hΩ hJc hJw
    hJ hC hξ hz₀
  obtain ⟨m, hm, hΘ, -⟩ := exists_analyticOrderAt_eq_of_hasSimilarityFactorizationAt hΩ hΩc
    (e.continuous.comp_continuousOn hξ.continuousOn) (fun z hz _ ↦ hfac z hz)
    ⟨z₁, hz₁, fun h0 ↦ hξ₁ ((map_eq_zero_iff e e.injective).1 h0)⟩ hz₀ (by simp [hξ₀])
  exact ⟨m, hm, ⟨((e.symm.toContinuousLinearMap.isBigO_comp _ _).trans hΘ.isBigO).congr'
    (Eventually.of_forall fun z ↦ e.symm_apply_apply (ξ z)) EventuallyEq.rfl,
    hΘ.isBigO_symm.trans (e.toContinuousLinearMap.isBigO_comp _ _)⟩⟩

end RealTarget

/-! ### Checks -/

section Checks

/-- **Check: wrong intertwining sign fails.** For an invertible `C¹` frame `Φ` on an open set `Ω`
containing `0` and `J` continuous with `J Φ = -Φ i` (the negated intertwining sign), the map
`z ↦ Φ z z` does *not* solve `∂ₛξ + J ∂ₜξ + C ξ = 0` with `C = -(∂ₛΦ + J ∂ₜΦ) Φ⁻¹`, because the
`σ` derivative term leaves `2 Φ(0) 1 ≠ 0` at `0`. -/
theorem not_isWeakLinearCauchyRiemannOn_of_comp_eq_neg_comp_I_smul {p : ℝ≥0∞} {Ω : Opens ℂ}
    (h0 : (0 : ℂ) ∈ Ω) {J Φ : ℂ → ℂ →L[ℝ] ℂ} (hJc : ContinuousOn J Ω)
    (hΦ : ContDiffOn ℝ 1 Φ Ω) (hu : ∀ z ∈ Ω, IsUnit (Φ z))
    (hJneg : ∀ z ∈ Ω, J z ∘L Φ z = -(Φ z ∘L (I • ContinuousLinearMap.id ℝ ℂ))) :
    ¬IsWeakLinearCauchyRiemannOn p Ω J
      (fun z ↦ -(fderiv ℝ Φ z 1 + J z ∘L fderiv ℝ Φ z I) ∘L Ring.inverse (Φ z))
      (fun z ↦ Φ z z) := by
  let C : ℂ → ℂ →L[ℝ] ℂ :=
    fun z ↦ -(fderiv ℝ Φ z 1 + J z ∘L fderiv ℝ Φ z I) ∘L Ring.inverse (Φ z)
  have hΨc : ContinuousOn (fun z ↦ Ring.inverse (Φ z)) Ω := fun z hz ↦ by
    have h := NormedRing.inverse_continuousAt (hu z hz).unit
    rw [IsUnit.unit_spec] at h
    exact h.comp_continuousWithinAt (hΦ.continuousOn z hz)
  have hCc : ContinuousOn C Ω := by
    have hd : ContinuousOn (fderiv ℝ Φ) Ω := hΦ.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl
    exact (((hd.clm_apply continuousOn_const).add
      (hJc.clm_comp (hd.clm_apply continuousOn_const))).neg).clm_comp hΨc
  have hξ : ContDiffOn ℝ 1 (fun z ↦ Φ z z) Ω := hΦ.clm_apply contDiffOn_id
  rw [IsWeakLinearCauchyRiemannOn, isWeakCauchyRiemannOn_iff_of_contDiffOn hξ
    hJc ((hCc.clm_apply hξ.continuousOn).neg)]
  intro hall
  have h0eq := hall 0 h0
  have hd0 : DifferentiableAt ℝ Φ 0 :=
    (hΦ.differentiableOn one_ne_zero).differentiableAt (Ω.isOpen.mem_nhds h0)
  have hf0 : fderiv ℝ (fun z : ℂ ↦ Φ z z) 0 = Φ 0 := by
    simpa using fderiv_clm_apply hd0 differentiableAt_id
  have hJ0 : J 0 (Φ 0 I) = Φ 0 1 := by
    simpa [Complex.I_mul_I] using congr($(hJneg 0 h0) I)
  rw [hf0, hJ0, map_zero, map_zero, neg_zero] at h0eq
  have htwo : (2 : ℝ) • Φ 0 1 = 0 := by
    simpa [two_smul] using h0eq
  have hΦ01 : Φ 0 1 = 0 := (smul_eq_zero.1 htwo).resolve_left two_ne_zero
  exact one_ne_zero ((ContinuousLinearMap.isUnit_iff_bijective.1 (hu 0 h0)).1
    (by rw [hΦ01, map_zero]))

end Checks

end TauCeti
