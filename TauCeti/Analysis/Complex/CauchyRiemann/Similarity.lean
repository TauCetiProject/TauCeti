/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.MetricSpace.Contracting
public import TauCeti.Analysis.Complex.Pompeiu.Pointwise
import TauCeti.Analysis.Complex.Pompeiu.Weak
import TauCeti.MeasureTheory.Function.RankOne

/-!
# The similarity principle for classical solutions of linear Cauchy–Riemann equations

Let `V` be a finite-dimensional complex normed space, `Ω ⊆ ℂ` open, and `ξ : ℂ → V` a map of
class `C¹` on `Ω` solving the linear Cauchy–Riemann equation

`∂ₛξ + i ∂ₜξ + C ξ = 0`

on `Ω`, in the coordinate `z = s + i t`, for a measurable, locally bounded (for instance
continuous) field `C` of *real*-linear endomorphisms of `V`. The **similarity principle** says
that near every point `z₀ ∈ Ω` the solution factors as `ξ = Φ σ` with `Φ` a continuous family of
invertible complex-linear maps and `σ` holomorphic (`TauCeti.exists_similarity_of_contDiffOn`).
In particular `ξ` has a similarity factorization in the sense of
`TauCeti.HasSimilarityFactorizationAt` at every point of `Ω`
(`TauCeti.hasSimilarityFactorizationAt_of_contDiffOn`), so it inherits the zero structure of a
holomorphic map: unique continuation from a zero of infinite order
(`TauCeti.eqOn_zero_of_contDiffOn_of_forall_isBigO`) and isolated zeros
(`TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn`).

The coefficient `C` need not commute with `i`, and a solution is in general not holomorphic.
The proof follows Carleman's argument as presented by McDuff and Salamon, after transporting the
equation along a complex-linear equivalence of `V` with a Euclidean space, whose inner product is
used only in the next step. First the real-linear term `C ξ` is absorbed into a complex-linear
coefficient depending on `ξ`: the rank-one map `D w = ‖ξ‖⁻² ⟪ξ, w⟫ C ξ`
(`TauCeti.rankOneDivNormSq`) is complex-linear, satisfies `D ξ = C ξ` and `‖D‖ ≤ ‖C‖`, and is
merely measurable, since it jumps at the zeros of `ξ`. Then the Cauchy integral equation
`Ψ = 1 + T (½ Ψ D)`, for the Cauchy transform `T` inverting `bar∂ = (∂ₛ + i ∂ₜ)/2`, is solved on a
small closed disc by the contraction mapping theorem. Its solution `Ψ` is continuous, close to
`1` and hence invertible, and has weak derivative `bar∂Ψ = ½ Ψ D`. The Leibniz rule for the
Cauchy transform (`TauCeti.hasWeakConjWirtingerDerivOn_cauchyTransform_apply`) then gives
`bar∂ (Ψ ξ) = Ψ (bar∂ξ + ½ D ξ) = Ψ (bar∂ξ + ½ C ξ) = 0` weakly, so `σ = Ψ ξ` is holomorphic by
Weyl's lemma, and `ξ = Ψ⁻¹ σ`.

## Main results

* `TauCeti.exists_cauchyTransform_eq_of_memLp`: the Cauchy integral equation `Ψ = 1 + T (½ Ψ D)`
  for a coefficient `D` dominated by a function of small `Lᵖ` norm, `p > 2`. It is the step of the
  proof that changes for weak solutions with `Lᵖ` coefficients
  (`TauCeti.Analysis.Complex.CauchyRiemann.Similarity.Weak`).
* `TauCeti.exists_similarity_of_contDiffOn`: the local factorization `ξ = Φ σ` on a disc.
* `TauCeti.hasSimilarityFactorizationAt_of_contDiffOn`: the factorization in the form consumed by
  `TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation`.
* `TauCeti.eqOn_zero_of_contDiffOn_of_forall_isBigO`: unique continuation from a zero of infinite
  order.
* `TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn`: a solution that is not identically
  zero on a connected open set has isolated zeros.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 2.3.5 (the Carleman similarity principle) and its proof.
* T. Carleman, *Sur les systèmes linéaires aux dérivées partielles du premier ordre à deux
  variables*, C. R. Acad. Sci. Paris **197** (1933), 471–474.
-/

public noncomputable section

open Asymptotics Complex Filter Function MeasureTheory Metric Set Topology TopologicalSpace
open scoped ENNReal InnerProductSpace

namespace TauCeti

section CauchyIntegralEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### The Cauchy integral equation -/

/-- The source term `½ Ψ D` of the Cauchy integral equation, for `Ψ` given on the closed disc
and extended by `0`. -/
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

/-- **The Cauchy integral equation with an `Lᵖ` coefficient.** Let `E` be a complex Banach space,
let `p, q` be Hölder conjugate with `q < 2`, that is `p > 2`, and let `D` be a measurable field of
complex-linear maps of `E` on the closed disc of radius `r ≤ R` about `c`, bounded there by a
function `G ∈ Lᵖ` with `π⁻¹ ‖K_{2R}‖_{L^q} ‖G‖_{Lᵖ} ≤ 1/2`, where `K_{2R}` is the reciprocal kernel
truncated at `2R`. Then there is `g ∈ Lᵖ`, vanishing off the disc, whose Cauchy transform `T g` is
continuous and satisfies `g = ½ (1 + T g) D` on the disc, with `‖T g‖ < 1` there.

In the similarity principle, `Ψ = 1 + T g` is then a continuous family of invertible maps on the
disc with `bar∂Ψ = ½ Ψ D` on its interior. -/
theorem exists_cauchyTransform_eq_of_memLp [CompleteSpace E] {p q : ℝ≥0∞}
    [p.HolderConjugate q] (hq : q < 2) {D : ℂ → E →L[ℂ] E} {G : ℂ → ℝ} {c : ℂ} {r R : ℝ}
    (hrR : r ≤ R) (hD : AEStronglyMeasurable D (volume.restrict (closedBall c r)))
    (hG : MemLp G p volume) (hDG : ∀ z ∈ closedBall c r, ‖D z‖ ≤ G z)
    (hsmall : Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (R + R)) q volume).toReal *
      (eLpNorm G p volume).toReal ≤ 2⁻¹) :
    ∃ g : ℂ → E →L[ℂ] E, MemLp g p volume ∧ support g ⊆ closedBall c r ∧
      Continuous (cauchyTransform g) ∧
      (∀ z ∈ closedBall c r, g z = (2 : ℂ)⁻¹ • (1 + cauchyTransform g z).comp (D z)) ∧
      ∀ z ∈ closedBall c r, ‖cauchyTransform g z‖ < 1 := by
  -- `Ψ = 1 + T g` is the fixed point of the contraction `Ψ ↦ 1 + T (½ Ψ D)` of the continuous
  -- maps on the disc; the smallness of `‖G‖_{Lᵖ}` makes it a contraction
  have hmeas := aestronglyMeasurable_cauchySource hD
  have hsupp := support_cauchySource_subset (c := c) (r := r) D
  have hsuppR (Ψ : C(closedBall c r, E →L[ℂ] E)) : support (cauchySource D Ψ) ⊆ closedBall c R :=
    (hsupp Ψ).trans (closedBall_subset_closedBall hrR)
  -- the source is dominated by `½ ‖Ψ‖ G`
  have hbd (Ψ : C(closedBall c r, E →L[ℂ] E)) (z : ℂ) :
      ‖cauchySource D Ψ z‖ ≤ 2⁻¹ * ‖Ψ‖ * ‖G z‖ := by
    by_cases hz : z ∈ closedBall c r
    · rw [cauchySource_of_mem D Ψ hz, norm_smul, norm_inv, Complex.norm_ofNat, mul_assoc]
      gcongr
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (Ψ.norm_coe_le_norm _)
        ((hDG z hz).trans (Real.le_norm_self _)) (norm_nonneg _) (by positivity))
    · rw [cauchySource_of_notMem D Ψ hz, norm_zero]
      positivity
  have hmem (Ψ : C(closedBall c r, E →L[ℂ] E)) : MemLp (cauchySource D Ψ) p volume :=
    hG.of_le_mul (hmeas Ψ) (ae_of_all _ (hbd Ψ))
  have hcont (Ψ : C(closedBall c r, E →L[ℂ] E)) :
      Continuous (cauchyTransform (cauchySource D Ψ)) :=
    continuous_cauchyTransform_of_memLp hq (hmem Ψ) (hsupp Ψ)
  -- the Cauchy transform of the source is at most a quarter of `‖Ψ‖` on the disc
  have hT (Ψ : C(closedBall c r, E →L[ℂ] E)) (w : ℂ) (hw : w ∈ closedBall c r) :
      ‖cauchyTransform (cauchySource D Ψ) w‖ ≤ 4⁻¹ * ‖Ψ‖ := by
    have hsrc : (eLpNorm (cauchySource D Ψ) p volume).toReal ≤
        2⁻¹ * ‖Ψ‖ * (eLpNorm G p volume).toReal := by
      have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hmeas Ψ) (ae_of_all _ (hbd Ψ)) p
      refine (ENNReal.toReal_mono (by finiteness [hG.eLpNorm_ne_top]) h).trans_eq ?_
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    calc ‖cauchyTransform (cauchySource D Ψ) w‖
        ≤ Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (R + R)) q volume).toReal *
            (eLpNorm (cauchySource D Ψ) p volume).toReal :=
          norm_cauchyTransform_le hq (hmem Ψ) (hsuppR Ψ) (closedBall_subset_closedBall hrR hw)
      _ ≤ Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (R + R)) q volume).toReal *
            (2⁻¹ * ‖Ψ‖ * (eLpNorm G p volume).toReal) := by gcongr
      _ = (Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (R + R)) q volume).toReal *
            (eLpNorm G p volume).toReal) * (2⁻¹ * ‖Ψ‖) := by ring
      _ ≤ 2⁻¹ * (2⁻¹ * ‖Ψ‖) := by gcongr
      _ = 4⁻¹ * ‖Ψ‖ := by ring
  -- and depends linearly on `Ψ`
  have hlin (Ψ Ψ' : C(closedBall c r, E →L[ℂ] E)) (w : ℂ) :
      cauchyTransform (cauchySource D Ψ) w - cauchyTransform (cauchySource D Ψ') w =
        cauchyTransform (cauchySource D (Ψ - Ψ')) w := by
    rw [cauchySource_sub, cauchyTransform_sub_of_memLp hq (hmem Ψ) (hsupp Ψ) (hmem Ψ')
      (hsupp Ψ'), Pi.sub_apply]
  let op (Ψ : C(closedBall c r, E →L[ℂ] E)) : C(closedBall c r, E →L[ℂ] E) :=
    ⟨fun w ↦ 1 + cauchyTransform (cauchySource D Ψ) w,
      (continuous_const.add (hcont Ψ)).comp continuous_subtype_val⟩
  have hop : ContractingWith 4⁻¹ op := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun Ψ Ψ' ↦ ?_⟩
    rw [NNReal.coe_inv, NNReal.coe_ofNat]
    refine (ContinuousMap.dist_le (by positivity)).2 fun w ↦ ?_
    simp only [op, ContinuousMap.coe_mk, dist_eq_norm, add_sub_add_left_eq_sub, hlin]
    refine (hT _ w w.2).trans ?_
    exact le_of_eq (congrArg _ (dist_eq_norm Ψ Ψ').symm)
  set Ψ₀ := ContractingWith.fixedPoint op hop
  set g := cauchySource D Ψ₀ with hg
  have hfix : op Ψ₀ = Ψ₀ := ContractingWith.fixedPoint_isFixedPt hop
  have hΨ₀ (z : ℂ) (hz : z ∈ closedBall c r) : Ψ₀ ⟨z, hz⟩ = 1 + cauchyTransform g z := by
    rw [← hfix]
    simp only [op, ContinuousMap.coe_mk, hg]
  have hnorm : ‖Ψ₀‖ ≤ 4 / 3 := by
    have h1 : ‖Ψ₀‖ ≤ 1 + 4⁻¹ * ‖Ψ₀‖ := by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun w ↦ ?_
      rw [hΨ₀ w w.2]
      exact (norm_add_le _ _).trans
        (add_le_add ContinuousLinearMap.norm_id_le (hT _ w w.2))
    linarith
  refine ⟨g, hmem Ψ₀, hsupp Ψ₀, hcont Ψ₀, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hg, cauchySource_of_mem D Ψ₀ hz, hΨ₀ z hz]
  · calc ‖cauchyTransform g z‖ ≤ 4⁻¹ * ‖Ψ₀‖ := hT _ z hz
      _ ≤ 4⁻¹ * (4 / 3) := by gcongr
      _ < 1 := by norm_num

/-- **The Cauchy integral equation with a bounded coefficient**, the case `p = ∞` of
`TauCeti.exists_cauchyTransform_eq_of_memLp`: on a closed disc of radius `r` on which a measurable
field `D` of complex-linear maps is bounded by `M`, with `2 r M ≤ 1/4`, there is an integrable `g`
whose Cauchy transform is continuous and satisfies `g = ½ (1 + T g) D` on the disc, with
`‖T g‖ < 1` there. -/
private theorem exists_cauchyTransform_eq [CompleteSpace E] {D : ℂ → E →L[ℂ] E} {c : ℂ}
    {r M : ℝ} (hr : 0 ≤ r) (hM : 0 ≤ M) (hrM : 2 * r * M ≤ 4⁻¹)
    (hD : AEStronglyMeasurable D (volume.restrict (closedBall c r)))
    (hDM : ∀ z ∈ closedBall c r, ‖D z‖ ≤ M) :
    ∃ g : ℂ → E →L[ℂ] E, Integrable g ∧ Continuous (cauchyTransform g) ∧
      (∀ z ∈ closedBall c r, g z = (2 : ℂ)⁻¹ • (1 + cauchyTransform g z).comp (D z)) ∧
      ∀ z ∈ closedBall c r, ‖cauchyTransform g z‖ < 1 := by
  -- the `L¹` norm of the kernel truncated at `2 r` is `4 π r`
  have hK : (eLpNorm (truncatedCauchyKernel (r + r)) 1 volume).toReal = 2 * Real.pi * (r + r) := by
    rw [eLpNorm_one_eq_lintegral_eNorm, ← ofReal_integral_norm_eq_lintegral_eNorm
      (integrable_truncatedCauchyKernel _), integral_norm_truncatedCauchyKernel (by positivity),
      ENNReal.toReal_ofReal (by positivity)]
    exact (measurable_truncatedCauchyKernel _).aestronglyMeasurable
  have hMtop : (eLpNorm (fun _ : ℂ ↦ M) ∞ volume).toReal ≤ M :=
    ENNReal.toReal_le_of_le_ofReal hM <| (eLpNorm_exponent_top aestronglyMeasurable_const).trans_le
      (eLpNormEssSup_le_of_ae_bound (ae_of_all _ fun _ ↦ (Real.norm_of_nonneg hM).le))
  have hsmall : Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (r + r)) 1 volume).toReal *
      (eLpNorm (fun _ : ℂ ↦ M) ∞ volume).toReal ≤ 2⁻¹ := by
    rw [hK]
    calc Real.pi⁻¹ * (2 * Real.pi * (r + r)) * (eLpNorm (fun _ : ℂ ↦ M) ∞ volume).toReal
        ≤ Real.pi⁻¹ * (2 * Real.pi * (r + r)) * M := by gcongr
      _ = 2 * (2 * r * M) := by field_simp; ring
      _ ≤ 2⁻¹ := by linarith
  obtain ⟨g, hgp, hgs, hTg, hgeq, hTg1⟩ := exists_cauchyTransform_eq_of_memLp (p := ∞) (q := 1)
    (by norm_num) le_rfl hD (memLp_top_const M) hDM hsmall
  have : IsFiniteMeasure (volume.restrict (closedBall c r)) :=
    ⟨by simpa using measure_closedBall_lt_top⟩
  have hg : Integrable g := (integrableOn_iff_integrable_of_support_subset (ε' := E →L[ℂ] E)
    hgs).1 ((hgp.restrict (closedBall c r)).integrable le_top)
  exact ⟨g, hg, hTg, hgeq, hTg1⟩

/-! ### The similarity principle -/

/-- A small enough radius for the contraction: `2 r M ≤ 1/4` for `r = min R (8 (M + 1))⁻¹`. -/
private theorem two_mul_min_mul_le {R M : ℝ} (hM : 0 ≤ M) :
    2 * min R (8 * (M + 1))⁻¹ * M ≤ 4⁻¹ := by
  have h : (8 * (M + 1))⁻¹ * M ≤ 8⁻¹ := by
    rw [inv_mul_le_iff₀ (by positivity)]
    linarith
  calc 2 * min R (8 * (M + 1))⁻¹ * M ≤ 2 * ((8 * (M + 1))⁻¹ * M) := by
        rw [mul_assoc]
        gcongr
        exact min_le_right _ _
    _ ≤ 4⁻¹ := by linarith

/-- The value of `bar∂ (Ψ ξ)` vanishes where `ξ` solves the equation and `bar∂Ψ = ½ Ψ D` with
`D ξ = C ξ`. -/
private theorem conjWirtingerDeriv_add_eq_zero {ξ : ℂ → E} {C : E →L[ℝ] E} {T G D : E →L[ℂ] E}
    {z : ℂ} (heq : fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I + C (ξ z) = 0)
    (hG : G = (2 : ℂ)⁻¹ • (1 + T).comp D) (hD : D (ξ z) = C (ξ z)) :
    conjWirtingerDeriv ξ z 1 + (G (ξ z) + T (conjWirtingerDeriv ξ z 1)) = 0 := by
  have hC : C (ξ z) = -(fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I) := eq_neg_of_add_eq_zero_right heq
  rw [hG]
  simp only [conjWirtingerDeriv_apply, smul_eq_mul, mul_one, smul_apply,
    ContinuousLinearMap.comp_apply, hD, hC, add_apply, one_apply_eq_self, map_neg, map_smul]
  module

end CauchyIntegralEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **The similarity principle** on a complex inner product space, for a solution of class `C¹`
on an open set with a measurable, locally bounded coefficient: the factorization on a disc. -/
private theorem exists_similarity_of_contDiffOn_of_innerProductSpace [FiniteDimensional ℂ E]
    {Ω : Set ℂ} {ξ : ℂ → E} {C : ℂ → E →L[ℝ] E} (hΩ : IsOpen Ω) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I + C z (ξ z) = 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) :
    ∃ r, 0 < r ∧ ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → E →L[ℂ] E) (σ : ℂ → E),
      ContinuousOn Φ (ball z₀ r) ∧ (∀ z ∈ ball z₀ r, IsUnit (Φ z)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧ EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ E
  -- a disc in `Ω` on which `C` is bounded
  obtain ⟨M₀, hM₀⟩ := hCb z₀ hz₀
  obtain ⟨R, hR, hRΩ⟩ := Metric.mem_nhds_iff.1 (inter_mem hM₀ (hΩ.mem_nhds hz₀))
  set M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  set r := min (R / 2) (8 * (M + 1))⁻¹
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hsub : closedBall z₀ r ⊆ ball z₀ R :=
    closedBall_subset_ball ((min_le_left _ _).trans_lt (half_lt_self hR))
  have hsubΩ : closedBall z₀ r ⊆ Ω := fun z hz ↦ (hRΩ (hsub hz)).2
  have hball : ball z₀ r ⊆ Ω := ball_subset_closedBall.trans hsubΩ
  -- absorb the real-linear coefficient and solve the Cauchy integral equation
  obtain ⟨g, hg, hTg, hgeq, hTg1⟩ := exists_cauchyTransform_eq hr.le hM (two_mul_min_mul_le hM)
    ((hCm.mono_measure (Measure.restrict_mono hsubΩ le_rfl)).rankOneDivNormSq_apply (𝕜 := ℂ)
      ((hξ.continuousOn.mono hsubΩ).aestronglyMeasurable measurableSet_closedBall))
    (fun z hz ↦ ((C z).norm_rankOneDivNormSq_map_le _).trans
      ((hRΩ (hsub hz)).1.trans (le_max_left _ _)))
  set Ψ : ℂ → E →L[ℂ] E := fun z ↦ 1 + cauchyTransform g z with hΨ
  have hunit (z : ℂ) (hz : z ∈ ball z₀ r) : IsUnit (Ψ z) := by
    simpa [hΨ] using isUnit_one_sub_of_norm_lt_one (x := -cauchyTransform g z)
      (by simpa using hTg1 z (ball_subset_closedBall hz))
  refine ⟨r, hr, hball, fun z ↦ Ring.inverse (Ψ z), fun z ↦ Ψ z (ξ z),
    fun z hz ↦ ?_, fun z hz ↦ ?_, ?_, fun z hz ↦ ?_⟩
  · have hc := NormedRing.inverse_continuousAt (hunit z hz).unit
    rw [IsUnit.unit_spec] at hc
    exact (hc.comp (continuous_const.add hTg).continuousAt).continuousWithinAt
  · exact (hunit z hz).ringInverse
  · -- `Ψ ξ` is weakly holomorphic on the disc, hence holomorphic
    let D : Opens ℂ := ⟨ball z₀ r, isOpen_ball⟩
    have hξD : ContDiffOn ℝ 1 ξ D := hξ.mono hball
    have hw := (hasWeakConjWirtingerDerivOn_of_contDiffOn (μ := volume) hξD).add
      (hasWeakConjWirtingerDerivOn_cauchyTransform_apply hg hξD)
    have hval : ∀ z ∈ (D : Set ℂ), ((fun z ↦ conjWirtingerDeriv ξ z 1) +
        fun z ↦ g z (ξ z) + cauchyTransform g z (conjWirtingerDeriv ξ z 1)) z = 0 :=
      fun z hz ↦ conjWirtingerDeriv_add_eq_zero (heq z (hball hz))
        (hgeq z (ball_subset_closedBall hz)) ((C z).rankOneDivNormSq_apply_map _)
    have hw0 := hw.congr_ae_deriv ((ae_restrict_iff' D.isOpen.measurableSet).2
      (ae_of_all _ hval))
    have hσ : (ξ + fun z ↦ cauchyTransform g z (ξ z)) = fun z ↦ Ψ z (ξ z) := by
      ext1 z
      simp [hΨ]
    rw [hσ] at hw0
    exact hw0.differentiableOn
      ((continuous_const.add hTg).continuousOn.clm_apply (hξ.continuousOn.mono hball))
  · beta_reduce
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def,
      Ring.inverse_mul_cancel _ (hunit z hz), one_apply_eq_self]

/-! ### Finite-dimensional complex normed spaces -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {Ω : Set ℂ} {ξ : ℂ → V} {C : ℂ → V →L[ℝ] V}

/-- **The similarity principle** (Carleman) for classical solutions. Let `ξ` be of class `C¹` on
an open set `Ω ⊆ ℂ` and solve `∂ₛξ + i ∂ₜξ + C ξ = 0` on `Ω`, for a measurable, locally bounded
field `C` of real-linear endomorphisms of a finite-dimensional complex normed space `V` (for
instance a continuous one). Then every point `z₀ ∈ Ω` is the centre of a disc in `Ω` on which
`ξ = Φ σ`, with `Φ` a continuous family of invertible complex-linear maps and `σ` holomorphic. -/
theorem exists_similarity_of_contDiffOn (hΩ : IsOpen Ω) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I + C z (ξ z) = 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) :
    ∃ r, 0 < r ∧ ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → V →L[ℂ] V) (σ : ℂ → V),
      ContinuousOn Φ (ball z₀ r) ∧ (∀ z ∈ ball z₀ r, IsUnit (Φ z)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧ EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r) := by
  -- transport the equation to a Euclidean space, whose inner product absorbs `C`
  let e : V ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let eR : V →L[ℝ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    (e : V →L[ℂ] _).restrictScalars ℝ
  let eR' : EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →L[ℝ] V :=
    (e.symm : _ →L[ℂ] V).restrictScalars ℝ
  have hξ' : ContDiffOn ℝ 1 (eR ∘ ξ) Ω := eR.contDiff.comp_contDiffOn hξ
  have hconj : Continuous fun A : V →L[ℝ] V ↦ eR.comp (A.comp eR') :=
    continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
  have hC'b (z : ℂ) (hz : z ∈ Ω) : ∃ M, ∀ᶠ w in 𝓝 z, ‖eR.comp ((C w).comp eR')‖ ≤ M := by
    obtain ⟨M, hM⟩ := hCb z hz
    refine ⟨‖eR‖ * (M * ‖eR'‖), hM.mono fun w hw ↦ (eR.opNorm_comp_le _).trans ?_⟩
    gcongr
    exact ((C w).opNorm_comp_le _).trans (by gcongr)
  have heq' (z : ℂ) (hz : z ∈ Ω) : fderiv ℝ (eR ∘ ξ) z 1 + I • fderiv ℝ (eR ∘ ξ) z I +
      eR.comp ((C z).comp eR') ((eR ∘ ξ) z) = 0 := by
    have hd : fderiv ℝ (eR ∘ ξ) z = eR.comp (fderiv ℝ ξ z) :=
      (eR.hasFDerivAt.comp z (((hξ.differentiableOn one_ne_zero).differentiableAt
        (hΩ.mem_nhds hz)).hasFDerivAt)).fderiv
    have h := congrArg e (heq z hz)
    simp only [map_add, map_smul, map_zero] at h
    rw [hd]
    simpa only [eR, eR', ContinuousLinearMap.comp_apply, Function.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearEquiv.coe_coe,
      e.symm_apply_apply] using h
  obtain ⟨r, hr, hrΩ, Φ, σ, hΦ, hΦu, hσ, hξσ⟩ :=
    exists_similarity_of_contDiffOn_of_innerProductSpace hΩ hξ'
      (hconj.comp_aestronglyMeasurable hCm) hC'b heq' hz₀
  refine ⟨r, hr, hrΩ, fun z ↦ e.symm.conjContinuousAlgEquiv (Φ z), fun z ↦ e.symm (σ z),
    ?_, fun z hz ↦ (hΦu z hz).map _,
    ((e.symm : _ →L[ℂ] V).differentiable.comp_differentiableOn hσ).congr fun _ _ ↦ rfl,
    fun z hz ↦ ?_⟩
  · simp only [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply]
    exact continuousOn_const.clm_comp (hΦ.clm_comp continuousOn_const)
  · have h := congrArg e.symm (hξσ hz)
    simp only [Function.comp_apply, eR, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] at h
    simp [h]

/-- A `C¹` solution of `∂ₛξ + i ∂ₜξ + C ξ = 0` on an open set `Ω`, with measurable, locally
bounded real-linear coefficient `C`, has a similarity factorization at every point of `Ω`. -/
theorem hasSimilarityFactorizationAt_of_contDiffOn (hΩ : IsOpen Ω) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I + C z (ξ z) = 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) : HasSimilarityFactorizationAt ξ z₀ := by
  have := FiniteDimensional.completeSpace ℂ V
  obtain ⟨r, hr, -, Φ, σ, hΦ, hΦu, hσ, hξσ⟩ :=
    exists_similarity_of_contDiffOn hΩ hξ hCm hCb heq hz₀
  obtain ⟨u, hu⟩ := hΦu z₀ (mem_ball_self hr)
  -- restricting the scalars of the equivalence `Φ z₀` to `ℝ` keeps it invertible
  refine .of_eqOn_ball hr (Φ := fun z ↦ (Φ z).restrictScalars ℝ)
    ((ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℂ).continuous.comp_continuousOn hΦ)
    (hu ▸ ⟨((ContinuousLinearEquiv.unitsEquiv ℂ V u).restrictScalars ℝ).toUnit, rfl⟩) hσ hξσ

/-- **Unique continuation** for classical solutions. On a connected open set `Ω`, a `C¹` solution
of `∂ₛξ + i ∂ₜξ + C ξ = 0`, with measurable, locally bounded real-linear coefficient `C`, that
vanishes to infinite order at one point of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_contDiffOn_of_forall_isBigO (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hξ : ContDiffOn ℝ 1 ξ Ω) (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I + C z (ξ z) = 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) (h₀ : ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n) : EqOn ξ 0 Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact eqOn_zero_of_hasSimilarityFactorizationAt_of_forall_isBigO hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_contDiffOn hΩ hξ hCm hCb heq hz) hz₀ h₀

/-- **Isolated zeros** of classical solutions. On a connected open set `Ω`, the zeros of a `C¹`
solution of `∂ₛξ + i ∂ₜξ + C ξ = 0`, with measurable, locally bounded real-linear coefficient
`C`, that is not identically zero on `Ω` form a discrete subset of `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I + C z (ξ z) = 0)
    (hne : ∃ z ∈ Ω, ξ z ≠ 0) : {z | ξ z ≠ 0} ∈ codiscreteWithin Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact setOf_ne_zero_mem_codiscreteWithin_of_hasSimilarityFactorizationAt hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_contDiffOn hΩ hξ hCm hCb heq hz) hne

end TauCeti
