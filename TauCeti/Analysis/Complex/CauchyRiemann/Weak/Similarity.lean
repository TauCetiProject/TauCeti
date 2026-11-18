/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.StandardFrame
public import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.MetricSpace.Contracting
import TauCeti.Analysis.Complex.Pompeiu.Pointwise
import TauCeti.Analysis.Complex.Wirtinger.Beurling.Lp
import TauCeti.Analysis.Complex.Wirtinger.Weyl
import TauCeti.Analysis.Sobolev.Local.Multiplication
import TauCeti.Geometry.Symplectic.Complex.Module.Conjugacy
import TauCeti.MeasureTheory.Function.RankOne

/-!
# The similarity principle for weak solutions of linear Cauchy–Riemann equations

Let `V` be a finite-dimensional complex normed space, `Ω ⊆ ℂ` open and `p > 2`. Let
`J ∈ W^{1,p}_loc(Ω; End_ℝ V)` be a continuous field of complex structures, `J² = -1`, and
`C ∈ Lᵖ_loc(Ω; End_ℝ V)` a field of real-linear endomorphisms. Let `ξ : ℂ → V` be a weak solution
of the linear Cauchy–Riemann equation

`∂ₛξ + J(z) ∂ₜξ + C(z) ξ = 0`

on `Ω` in the sense of `TauCeti.IsWeakLinearCauchyRiemannOn`: `ξ` is continuous, with a weak
derivative in `Lᵖ_loc`, and the equation holds almost everywhere. The **vector similarity
principle** (Carleman; McDuff–Salamon, Theorem 2.3.5) says that near every point `z₀ ∈ Ω` the
solution factors as `ξ = Φ σ`, with `Φ` a continuous `W^{1,p}` family of invertible real-linear
maps satisfying `J Φ = Φ i` and `σ` holomorphic
(`TauCeti.exists_similarity_of_isWeakLinearCauchyRiemannOn_of_complexStructure`). Consequently a
weak solution has the zero structure of a holomorphic map: it has a similarity factorization at
every point, it vanishes on a connected open set as soon as it vanishes to infinite order at one
point or on a nonempty open subset, and otherwise its zeros are isolated.
These are the statements used for the local theory of pseudoholomorphic curves of finite
regularity, whose linearized equations have Sobolev coefficients.

The classical version, for `C¹` solutions with locally bounded coefficients and `J = i`, is
`TauCeti.exists_similarity_of_contDiffOn`. Here only `C ∈ Lᵖ` is available, and the solution is
only weakly differentiable, so the proof follows Carleman's argument with `Lᵖ` estimates.

* **The standard structure.** For `J = i`
  (`TauCeti.exists_similarity_of_isWeakLinearCauchyRiemannOn`) the real-linear term `C ξ` is first
  absorbed into a complex-linear coefficient `D` with `D ξ = C ξ` and `‖D‖ ≤ K ‖C‖`, a rank-one map
  for an auxiliary inner product on `V` (`TauCeti.rankOneDivNormSq`). On a small closed disc the
  Cauchy integral equation `Φ = 1 - T (½ D Φ)`, for the Cauchy transform `T` inverting
  `bar∂ = (∂ₛ + i ∂ₜ)/2`, is solved by the contraction mapping theorem in the continuous maps on the
  disc. Since `p > 2`, `T` maps `Lᵖ` data on the disc to continuous functions, with a pointwise
  bound by the `Lᵖ` norm (`TauCeti.norm_cauchyTransform_le`,
  `TauCeti.continuous_cauchyTransform_of_memLp`), and the `Lᵖ` norm of `D` on the disc is small when
  the disc is small. The solution `Φ` is continuous, close to `1` and hence invertible, lies in
  `W^{1,p}` by the Calderón–Zygmund inequality
  (`TauCeti.exists_hasWeakFDerivOn_cauchyTransform_of_memLp`), and satisfies `bar∂ Φ = -½ D Φ`. The
  frame reduction `TauCeti.isWeakLinearCauchyRiemannOn_iff_frame` then shows that `σ = Φ⁻¹ ξ` solves
  the equation with coefficient `Φ⁻¹(2 bar∂Φ + C Φ)`, which vanishes along `σ`, since
  `2 bar∂Φ Φ⁻¹ ξ = -D ξ = -C ξ`. So `σ` is weakly holomorphic, hence holomorphic by Weyl's lemma.
* **A variable structure.** The standard frame of `TauCeti.standardFrame` reduces the equation
  for `J` to an equation for `i` with a new coefficient in `Lᵖ_loc`
  (`TauCeti.isWeakLinearCauchyRiemannOn_iff_standardFrame`), to which the first case applies.

## Main results

* `TauCeti.exists_similarity_of_isWeakLinearCauchyRiemannOn`: the factorization for `J = i`, with
  `Φ` complex-linear.
* `TauCeti.exists_similarity_of_isWeakLinearCauchyRiemannOn_of_complexStructure`: the
  factorization for a continuous `W^{1,p}` field of complex structures `J`, with `J Φ = Φ i`.
* `TauCeti.hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn_of_complexStructure`: the
  factorization in the form consumed by `TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation`.
* `TauCeti.eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_forall_isBigO_of_complexStructure` and
  `TauCeti.eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_eqOn_zero_of_complexStructure`: unique
  continuation.
* `TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_isWeakLinearCauchyRiemannOn_of_complexStructure`:
  isolated zeros.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 2.3.5 (the Carleman similarity principle) and its proof.
* T. Carleman, *Sur les systèmes linéaires aux dérivées partielles du premier ordre à deux
  variables*, C. R. Acad. Sci. Paris **197** (1933), 471–474.
-/

public noncomputable section

open Asymptotics Complex Filter Function MeasureTheory Metric Set Topology TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-! ### Absorbing the real-linear coefficient -/

variable (V) in
/-- **A complex-linear coefficient along a solution.** For every `ξ` and every field `C` of
real-linear maps there is a field `D` of complex-linear maps with `D ξ = C ξ` and `‖D‖ ≤ K ‖C‖`,
measurable when `C` and `ξ` are, with a constant `K` depending only on `V`. It is a rank-one map
for the inner product transported from a Euclidean space. -/
private theorem exists_complexLinear_apply_eq [FiniteDimensional ℂ V] :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ξ : ℂ → V) (C : ℂ → V →L[ℝ] V), ∃ D : ℂ → V →L[ℂ] V,
      (∀ z, D z (ξ z) = C z (ξ z)) ∧ (∀ z, ‖D z‖ ≤ K * ‖C z‖) ∧
      ∀ μ : Measure ℂ, AEStronglyMeasurable C μ → AEStronglyMeasurable ξ μ →
        AEStronglyMeasurable D μ := by
  let E := EuclideanSpace ℂ (Fin (Module.finrank ℂ V))
  let e : V ≃L[ℂ] E := ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let eR : V →L[ℝ] E := (e : V →L[ℂ] E).restrictScalars ℝ
  let eR' : E →L[ℝ] V := (e.symm : E →L[ℂ] V).restrictScalars ℝ
  refine ⟨‖(e.symm : E →L[ℂ] V)‖ * (‖eR‖ * ‖eR'‖) * ‖(e : V →L[ℂ] E)‖, by positivity,
    fun ξ C ↦ ?_⟩
  let C' : ℂ → E →L[ℝ] E := fun z ↦ eR ∘L C z ∘L eR'
  have hconj : Continuous fun A : E →L[ℂ] E ↦ (e.symm : E →L[ℂ] V) ∘L A ∘L (e : V →L[ℂ] E) :=
    continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
  refine ⟨fun z ↦ (e.symm : E →L[ℂ] V) ∘L rankOneDivNormSq ℂ (C' z (e (ξ z))) (e (ξ z)) ∘L
    (e : V →L[ℂ] E), fun z ↦ ?_, fun z ↦ ?_, fun μ hC hξ ↦ ?_⟩
  · have h := (C' z).rankOneDivNormSq_apply_map (𝕜 := ℂ) (e (ξ z))
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [h]
    simp [C', eR, eR']
  · calc ‖(e.symm : E →L[ℂ] V) ∘L rankOneDivNormSq ℂ (C' z (e (ξ z))) (e (ξ z)) ∘L
          (e : V →L[ℂ] E)‖
        ≤ ‖(e.symm : E →L[ℂ] V)‖ * (‖rankOneDivNormSq ℂ (C' z (e (ξ z))) (e (ξ z))‖ *
          ‖(e : V →L[ℂ] E)‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ ‖(e.symm : E →L[ℂ] V)‖ * ((‖eR‖ * (‖C z‖ * ‖eR'‖)) * ‖(e : V →L[ℂ] E)‖) := by
          gcongr
          refine ((C' z).norm_rankOneDivNormSq_map_le _).trans ?_
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _)
      _ = _ := by ring
  · have hC' : AEStronglyMeasurable C' μ :=
      (continuous_const.clm_comp
        (continuous_id.clm_comp continuous_const)).comp_aestronglyMeasurable hC
    exact hconj.comp_aestronglyMeasurable
      (hC'.rankOneDivNormSq_apply (𝕜 := ℂ) (e.continuous.comp_aestronglyMeasurable hξ))

/-! ### The Cauchy integral equation with `Lᵖ` coefficients -/

/-- The source term `½ D Φ` of the Cauchy integral equation, for `Φ` given on the closed disc and
extended by `0`. -/
private def lpCauchySource {c : ℂ} {r : ℝ} (D : ℂ → V →L[ℂ] V)
    (Φ : C(closedBall c r, V →L[ℂ] V)) (z : ℂ) : V →L[ℂ] V :=
  (2 : ℂ)⁻¹ • (D z).comp (extend Subtype.val Φ 0 z)

private theorem lpCauchySource_of_mem {c : ℂ} {r : ℝ} (D : ℂ → V →L[ℂ] V)
    (Φ : C(closedBall c r, V →L[ℂ] V)) {z : ℂ} (hz : z ∈ closedBall c r) :
    lpCauchySource D Φ z = (2 : ℂ)⁻¹ • (D z).comp (Φ ⟨z, hz⟩) := by
  rw [lpCauchySource, Subtype.val_injective.extend_apply Φ 0 ⟨z, hz⟩]

private theorem lpCauchySource_of_notMem {c : ℂ} {r : ℝ} (D : ℂ → V →L[ℂ] V)
    (Φ : C(closedBall c r, V →L[ℂ] V)) {z : ℂ} (hz : z ∉ closedBall c r) :
    lpCauchySource D Φ z = 0 := by
  rw [lpCauchySource, extend_apply' _ _ _ fun ⟨w, hw⟩ ↦ hz (hw ▸ w.2)]
  simp

private theorem support_lpCauchySource_subset {c : ℂ} {r : ℝ} (D : ℂ → V →L[ℂ] V)
    (Φ : C(closedBall c r, V →L[ℂ] V)) : support (lpCauchySource D Φ) ⊆ closedBall c r :=
  fun _ hz ↦ by_contra fun h ↦ hz (lpCauchySource_of_notMem D Φ h)

private theorem lpCauchySource_sub {c : ℂ} {r : ℝ} (D : ℂ → V →L[ℂ] V)
    (Φ Φ' : C(closedBall c r, V →L[ℂ] V)) :
    lpCauchySource D (Φ - Φ') = lpCauchySource D Φ - lpCauchySource D Φ' := by
  ext1 z
  by_cases hz : z ∈ closedBall c r
  · simp only [Pi.sub_apply, lpCauchySource_of_mem D _ hz, ContinuousMap.sub_apply,
      ContinuousLinearMap.comp_sub, smul_sub]
  · simp [lpCauchySource_of_notMem D _ hz]

private theorem norm_lpCauchySource_le {c : ℂ} {r : ℝ} (D : ℂ → V →L[ℂ] V)
    (Φ : C(closedBall c r, V →L[ℂ] V)) (z : ℂ) :
    ‖lpCauchySource D Φ z‖ ≤ 2⁻¹ * ‖Φ‖ * ‖(closedBall c r).indicator D z‖ := by
  by_cases hz : z ∈ closedBall c r
  · rw [lpCauchySource_of_mem D Φ hz, indicator_of_mem hz, norm_smul, norm_inv,
      Complex.norm_ofNat, mul_assoc]
    gcongr
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by rw [mul_comm]; gcongr; exact Φ.norm_coe_le_norm _)
  · rw [lpCauchySource_of_notMem D Φ hz, norm_zero]
    positivity

private theorem aestronglyMeasurable_lpCauchySource {c : ℂ} {r : ℝ} {D : ℂ → V →L[ℂ] V}
    (hD : AEStronglyMeasurable D (volume.restrict (closedBall c r)))
    (Φ : C(closedBall c r, V →L[ℂ] V)) : AEStronglyMeasurable (lpCauchySource D Φ) volume := by
  have he : ContinuousOn (extend Subtype.val Φ 0) (closedBall c r) := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert Φ.continuous using 1
    ext1 z
    exact Subtype.val_injective.extend_apply Φ 0 z
  have heq : lpCauchySource D Φ = (closedBall c r).indicator (lpCauchySource D Φ) :=
    (indicator_eq_self.2 (support_lpCauchySource_subset D Φ)).symm
  rw [heq, aestronglyMeasurable_indicator_iff measurableSet_closedBall]
  exact ((ContinuousLinearMap.compL ℂ V V V).aestronglyMeasurable_comp₂ hD
    (he.aestronglyMeasurable measurableSet_closedBall)).const_smul (2 : ℂ)⁻¹

private theorem memLp_lpCauchySource {p : ℝ≥0∞} {c : ℂ} {r : ℝ} {D : ℂ → V →L[ℂ] V}
    (hD : MemLp ((closedBall c r).indicator D) p volume) (Φ : C(closedBall c r, V →L[ℂ] V)) :
    MemLp (lpCauchySource D Φ) p volume :=
  hD.of_le_mul (aestronglyMeasurable_lpCauchySource
    ((aestronglyMeasurable_indicator_iff measurableSet_closedBall).1 hD.aestronglyMeasurable) Φ)
    (Eventually.of_forall (norm_lpCauchySource_le D Φ))

private theorem toReal_eLpNorm_lpCauchySource_le {p : ℝ≥0∞} {c : ℂ} {r : ℝ}
    {D : ℂ → V →L[ℂ] V} (hD : MemLp ((closedBall c r).indicator D) p volume)
    (Φ : C(closedBall c r, V →L[ℂ] V)) :
    (eLpNorm (lpCauchySource D Φ) p volume).toReal ≤
      2⁻¹ * ‖Φ‖ * (eLpNorm ((closedBall c r).indicator D) p volume).toReal := by
  have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (memLp_lpCauchySource hD Φ).aestronglyMeasurable
    (Eventually.of_forall (norm_lpCauchySource_le D Φ)) p
  rw [← ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2⁻¹ * ‖Φ‖), ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hD.eLpNorm_ne_top) h

/-- **The Cauchy integral equation with `Lᵖ` coefficients.** Let `p` have a conjugate exponent
`q < 2`, and let the Cauchy transform of `Lᵖ` data supported in a closed disc be bounded on the
disc by `K` times the `Lᵖ` norm of the data. If the field `D` is `Lᵖ` on the disc with
`K ‖D‖_{Lᵖ} ≤ 1/4`, there is `g ∈ Lᵖ`, supported in the disc, whose Cauchy transform is
continuous and satisfies `g = ½ D (1 - T g)` on the disc, with `‖T g‖ < 1` there. So
`Φ = 1 - T g` is a continuous family of invertible maps on the disc solving `bar∂Φ = -½ D Φ`. It
is the fixed point of the contraction `Φ ↦ 1 - T (½ D Φ)` of the continuous maps on the disc. -/
private theorem exists_cauchyTransform_eq_of_memLp [FiniteDimensional ℂ V] {p q : ℝ≥0∞}
    [p.HolderConjugate q] (hq : q < 2) {D : ℂ → V →L[ℂ] V} {c : ℂ} {r K : ℝ} (hK : 0 ≤ K)
    (hT : ∀ f : ℂ → V →L[ℂ] V, MemLp f p volume → support f ⊆ closedBall c r →
      ∀ w ∈ closedBall c r, ‖cauchyTransform f w‖ ≤ K * (eLpNorm f p volume).toReal)
    (hD : MemLp ((closedBall c r).indicator D) p volume)
    (hDK : K * (eLpNorm ((closedBall c r).indicator D) p volume).toReal ≤ 4⁻¹) :
    ∃ g : ℂ → V →L[ℂ] V, MemLp g p volume ∧ support g ⊆ closedBall c r ∧
      Continuous (cauchyTransform g) ∧
      (∀ z ∈ closedBall c r, g z = (2 : ℂ)⁻¹ • (D z).comp (1 - cauchyTransform g z)) ∧
      ∀ z ∈ closedBall c r, ‖cauchyTransform g z‖ < 1 := by
  have := FiniteDimensional.completeSpace ℂ V
  have hsupp := support_lpCauchySource_subset (c := c) (r := r) D
  have hmem := memLp_lpCauchySource hD
  have hnorm := toReal_eLpNorm_lpCauchySource_le hD
  have hcont (Φ : C(closedBall c r, V →L[ℂ] V)) :
      Continuous (cauchyTransform (lpCauchySource D Φ)) :=
    continuous_cauchyTransform_of_memLp hq (hmem Φ) (hsupp Φ)
  -- the Cauchy transform of the source is small on the disc
  have hTs (Φ : C(closedBall c r, V →L[ℂ] V)) (w : ℂ) (hw : w ∈ closedBall c r) :
      ‖cauchyTransform (lpCauchySource D Φ) w‖ ≤ 8⁻¹ * ‖Φ‖ := by
    calc ‖cauchyTransform (lpCauchySource D Φ) w‖
        ≤ K * (2⁻¹ * ‖Φ‖ * (eLpNorm ((closedBall c r).indicator D) p volume).toReal) :=
          (hT _ (hmem Φ) (hsupp Φ) w hw).trans (by gcongr; exact hnorm Φ)
      _ = 2⁻¹ * ‖Φ‖ * (K * (eLpNorm ((closedBall c r).indicator D) p volume).toReal) := by ring
      _ ≤ 2⁻¹ * ‖Φ‖ * 4⁻¹ := by gcongr
      _ = 8⁻¹ * ‖Φ‖ := by ring
  -- and depends linearly on `Φ`
  have hlin (Φ Φ' : C(closedBall c r, V →L[ℂ] V)) (w : ℂ) :
      cauchyTransform (lpCauchySource D Φ) w - cauchyTransform (lpCauchySource D Φ') w =
        cauchyTransform (lpCauchySource D (Φ - Φ')) w := by
    rw [lpCauchySource_sub, cauchyTransform_sub_of_memLp hq (hmem Φ) (hsupp Φ) (hmem Φ')
      (hsupp Φ'), Pi.sub_apply]
  let op (Φ : C(closedBall c r, V →L[ℂ] V)) : C(closedBall c r, V →L[ℂ] V) :=
    ⟨fun w ↦ 1 - cauchyTransform (lpCauchySource D Φ) w,
      (continuous_const.sub (hcont Φ)).comp continuous_subtype_val⟩
  have hop : ContractingWith 8⁻¹ op := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun Φ Φ' ↦ ?_⟩
    rw [NNReal.coe_inv, NNReal.coe_ofNat]
    refine (ContinuousMap.dist_le (by positivity)).2 fun w ↦ ?_
    simp only [op, ContinuousMap.coe_mk, dist_eq_norm, sub_sub_sub_cancel_left, hlin]
    refine (hTs _ w w.2).trans_eq ?_
    rw [dist_comm, dist_eq_norm Φ' Φ]
  set Φ₀ := ContractingWith.fixedPoint op hop
  set g := lpCauchySource D Φ₀ with hg
  have hfix : op Φ₀ = Φ₀ := ContractingWith.fixedPoint_isFixedPt hop
  have hΦ₀ (z : ℂ) (hz : z ∈ closedBall c r) : Φ₀ ⟨z, hz⟩ = 1 - cauchyTransform g z := by
    rw [← hfix]
    simp only [op, ContinuousMap.coe_mk, hg]
  have hnorm₀ : ‖Φ₀‖ ≤ 8 / 7 := by
    have h1 : ‖Φ₀‖ ≤ 1 + 8⁻¹ * ‖Φ₀‖ := by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun w ↦ ?_
      rw [hΦ₀ w w.2]
      exact (norm_sub_le _ _).trans
        (add_le_add ContinuousLinearMap.norm_id_le (hTs Φ₀ w w.2))
    linarith
  refine ⟨g, hmem Φ₀, hsupp Φ₀, hcont Φ₀, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hg, lpCauchySource_of_mem D Φ₀ hz, hΦ₀ z hz]
  · calc ‖cauchyTransform g z‖ ≤ 8⁻¹ * ‖Φ₀‖ := hTs Φ₀ z hz
      _ ≤ 8⁻¹ * (8 / 7) := by gcongr
      _ < 1 := by norm_num

/-! ### The similarity principle for the standard structure -/

/-- **The Cauchy integral equation on a small disc.** For `p > 2` and a field `D` that is `Lᵖ` on
the closed disc of radius `R` about `z₀`, there is a smaller closed disc about `z₀` on which the
Cauchy integral equation `Φ = 1 - T (½ D Φ)` has a solution `Φ = 1 - T g` close to `1`. The
radius is chosen so small that the `Lᵖ` norm of `D` on the disc, times the constant of the
pointwise bound for the Cauchy transform of `Lᵖ` data, is at most `1/4`; since `p < ∞`, the
`Lᵖ` norm on a set is small when its measure is. -/
private theorem exists_cauchyTransform_eq_of_memLp_closedBall [FiniteDimensional ℂ V] {p : ℝ≥0}
    (hp : 2 < p) {D : ℂ → V →L[ℂ] V} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hD : MemLp ((closedBall z₀ R).indicator D) p volume) :
    ∃ r, 0 < r ∧ r ≤ R ∧ ∃ g : ℂ → V →L[ℂ] V, MemLp g p volume ∧ support g ⊆ closedBall z₀ r ∧
      Continuous (cauchyTransform g) ∧
      (∀ z ∈ closedBall z₀ r, g z = (2 : ℂ)⁻¹ • (D z).comp (1 - cauchyTransform g z)) ∧
      ∀ z ∈ closedBall z₀ r, ‖cauchyTransform g z‖ < 1 := by
  -- the conjugate exponent `q < 2`
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by positivity
  have hle : (p : ℝ≥0∞)⁻¹ ≤ 1 := ENNReal.inv_le_one.2 (by exact_mod_cast one_le_two.trans hp.le)
  set q := (1 - (p : ℝ≥0∞)⁻¹)⁻¹
  have : (p : ℝ≥0∞).HolderConjugate q := ENNReal.holderConjugate_iff.2 <| by
    rw [inv_inv, add_tsub_cancel_of_le hle]
  have hq : q < 2 := by
    rw [ENNReal.inv_lt_iff_inv_lt,
      (ENNReal.cancel_of_ne (ENNReal.inv_ne_top.2 hp0)).lt_tsub_iff_right]
    calc (2 : ℝ≥0∞)⁻¹ + (p : ℝ≥0∞)⁻¹ < 2⁻¹ + 2⁻¹ := by
          gcongr
          · simp
          · exact_mod_cast hp
      _ = 1 := ENNReal.inv_two_add_inv_two
  -- a radius `r ≤ R` on which `K ‖D‖_{Lᵖ} ≤ 1/4`, where `K` bounds `T` on discs of radius `≤ R`
  set K := Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (R + R)) q volume).toReal
  have hK : 0 ≤ K := by positivity
  obtain ⟨δ, hδ, hδD⟩ := hD.eLpNorm_indicator_le (by exact_mod_cast (one_lt_two.trans hp).le)
    ENNReal.coe_ne_top (ENNReal.ofReal_pos.2 (by positivity : (0 : ℝ) < 4⁻¹ / (K + 1)))
  have hlim : Tendsto (fun r : ℝ ↦ volume (closedBall z₀ r)) (𝓝 0) (𝓝 0) := by
    simp only [Complex.volume_closedBall]
    have h1 : Tendsto (fun r : ℝ ↦ ENNReal.ofReal r ^ 2) (𝓝 0) (𝓝 0) := by
      simpa [Function.comp_def] using
        ((ENNReal.continuous_pow 2).comp ENNReal.continuous_ofReal).tendsto 0
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr ENNReal.coe_ne_top)
  obtain ⟨r, ⟨hrδ, hrR⟩, hr⟩ := (((hlim.eventually (ge_mem_nhds hδ)).and
    (eventually_le_nhds hR)).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0)) |>.exists
  have hsub : closedBall z₀ r ⊆ closedBall z₀ R := closedBall_subset_closedBall hrR
  have hrD := hδD (closedBall z₀ r) measurableSet_closedBall.nullMeasurableSet hrδ
  rw [indicator_indicator, inter_eq_left.2 hsub] at hrD
  have hDr : MemLp ((closedBall z₀ r).indicator D) p volume := by
    simpa [indicator_indicator, inter_eq_left.2 hsub] using
      MemLp.indicator (s := closedBall z₀ r) measurableSet_closedBall.nullMeasurableSet hD
  have hDK : K * (eLpNorm ((closedBall z₀ r).indicator D) p volume).toReal ≤ 4⁻¹ :=
    calc K * (eLpNorm ((closedBall z₀ r).indicator D) p volume).toReal
        ≤ (K + 1) * (4⁻¹ / (K + 1)) := by
          gcongr
          · linarith
          · exact ENNReal.toReal_le_of_le_ofReal (by positivity) hrD
      _ = 4⁻¹ := by field_simp
  exact ⟨r, hr, hrR, exists_cauchyTransform_eq_of_memLp hq hK
    (fun f hf hs w hw ↦ norm_cauchyTransform_le hq hf (hs.trans hsub) (hsub hw)) hDr hDK⟩

/-- **The frame step.** Let `Ψ` be a continuous family of invertible complex-linear maps on an
open set `B`, with weak derivative `DΨ ∈ Lᵖ_loc`, `p > 2`, satisfying `∂ₛΨ + i ∂ₜΨ = -D Ψ` for a
field `D` with `D ξ = C ξ`. If `ξ` solves `∂ₛξ + i ∂ₜξ + C ξ = 0` weakly on `B`, then `ξ = Ψ σ`
with `σ` holomorphic on `B`: by the frame reduction, `σ = Ψ⁻¹ ξ` solves the equation with
coefficient `Ψ⁻¹((∂ₛΨ + i ∂ₜΨ) + C Ψ)`, which vanishes along `σ`. -/
private theorem exists_differentiableOn_eqOn_clm_apply [FiniteDimensional ℂ V] {p : ℝ≥0}
    (hp : 2 < p) {B : Opens ℂ} {Ψ D : ℂ → V →L[ℂ] V} {DΨ : ℂ → ℂ →L[ℝ] V →L[ℂ] V}
    {C : ℂ → V →L[ℝ] V} {ξ : ℂ → V} (hΨc : ContinuousOn Ψ B) (hΨu : ∀ z ∈ B, IsUnit (Ψ z))
    (hΨ : HasWeakFDerivOn volume B Ψ DΨ) (hDΨ : MemLpLoc p B DΨ)
    (hΨD : ∀ z ∈ B, DΨ z 1 + I • DΨ z I = -(D z).comp (Ψ z))
    (hDξ : ∀ z ∈ B, D z (ξ z) = C z (ξ z))
    (h : IsWeakLinearCauchyRiemannOn p B (fun _ ↦ I • ContinuousLinearMap.id ℝ V) C ξ) :
    ∃ σ : ℂ → V, DifferentiableOn ℂ σ B ∧ EqOn ξ (fun z ↦ Ψ z (σ z)) B := by
  have := FiniteDimensional.completeSpace ℂ V
  -- the frame `Φ = Ψ`, read as a family of real-linear maps
  let L : (V →L[ℂ] V) →L[ℝ] V →L[ℝ] V := ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ
  have hΦu (z : ℂ) (hz : z ∈ (B : Set ℂ)) : IsUnit (L (Ψ z)) := by
    obtain ⟨u, hu⟩ := hΨu z hz
    exact hu ▸ ⟨((ContinuousLinearEquiv.unitsEquiv ℂ V u).restrictScalars ℝ).toUnit, rfl⟩
  have hDΦ : MemLpLoc p B fun w ↦ L.comp (DΨ w) := memLpLoc_iff.2 fun K hK hc ↦
    (memLpLoc_iff.1 hDΨ K hK hc).of_le_mul (c := ‖L‖)
      ((continuous_const.clm_comp continuous_id).comp_aestronglyMeasurable
        (memLpLoc_iff.1 hDΨ K hK hc).aestronglyMeasurable)
      (Eventually.of_forall fun w ↦ L.opNorm_comp_le _)
  have hΦc : ContinuousOn (fun z ↦ L (Ψ z)) B := L.continuous.comp_continuousOn hΨc
  have hη := (isWeakLinearCauchyRiemannOn_iff_frame hp hΦc (hΨ.clm_comp L) hDΦ hΦu
    fun z _ ↦ by ext v; simp [L]).1 h
  set σ := fun z ↦ Ring.inverse (L (Ψ z)) (ξ z)
  have hinv (z : ℂ) (hz : z ∈ (B : Set ℂ)) : Ψ z (σ z) = ξ z := by
    simpa [L, σ] using congr($(Ring.mul_inverse_cancel _ (hΦu z hz)) (ξ z))
  -- the new coefficient vanishes along `σ`, since `(∂ₛΨ + i ∂ₜΨ) σ = -D ξ = -C ξ`
  have hkey (z : ℂ) (hz : z ∈ (B : Set ℂ)) : frameCoeff (fun _ ↦ I • ContinuousLinearMap.id ℝ V)
      C (fun z ↦ L (Ψ z)) (fun w ↦ L.comp (DΨ w)) z (σ z) = 0 := by
    have h := congr($(hΨD z hz) (σ z))
    simp only [add_apply, smul_apply, neg_apply, ContinuousLinearMap.comp_apply, hinv z hz,
      hDξ z hz] at h
    rw [frameCoeff_apply]
    convert map_zero (Ring.inverse (L (Ψ z))) using 2
    simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrict_scalarsL',
      ContinuousLinearMap.coe_restrictScalars', smul_apply, ContinuousLinearMap.id_apply]
    rw [hinv z hz, h, neg_add_cancel]
  -- so `σ` is weakly holomorphic, hence holomorphic
  obtain ⟨hσc, -, Dσ, hDσ, -, hae⟩ := isWeakLinearCauchyRiemannOn_iff_of_isOpen.1 hη
  have hσ0 : HasWeakConjWirtingerDerivOn volume B σ 0 :=
    hDσ.hasWeakConjWirtingerDerivOn.congr_ae_deriv <| by
      filter_upwards [hae, ae_restrict_mem B.isOpen.measurableSet] with z hz hzB
      rw [hkey z hzB, add_zero] at hz
      simp only [Pi.zero_apply]
      exact smul_eq_zero_of_right _ (by simpa using hz)
  exact ⟨σ, hσ0.differentiableOn hσc, fun z hz ↦ (hinv z hz).symm⟩

/-- **The similarity principle for weak solutions**, for the standard complex structure. Let
`p > 2`, let `C` be a locally `Lᵖ` field of real-linear endomorphisms of a finite-dimensional
complex normed space `V` on an open set `Ω`, and let `ξ` be a weak solution of
`∂ₛξ + i ∂ₜξ + C ξ = 0` on `Ω`. Then every point `z₀ ∈ Ω` is the centre of a disc in `Ω` on which
`ξ = Φ σ`, with `Φ` a continuous `W^{1,p}` family of invertible complex-linear maps and `σ`
holomorphic. -/
theorem exists_similarity_of_isWeakLinearCauchyRiemannOn [FiniteDimensional ℂ V] {p : ℝ≥0}
    (hp : 2 < p) {Ω : Opens ℂ} {C : ℂ → V →L[ℝ] V} {ξ : ℂ → V}
    (h : IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ V) C ξ)
    (hC : MemLpLoc p Ω C) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ r > 0, ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → V →L[ℂ] V) (σ : ℂ → V),
      ContinuousOn Φ (ball z₀ r) ∧ MemWkpLoc p (ball z₀ r) 1 Φ ∧
      (∀ z ∈ ball z₀ r, IsUnit (Φ z)) ∧ DifferentiableOn ℂ σ (ball z₀ r) ∧
      EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ V
  have hp1 : (1 : ℝ≥0∞) < p := by exact_mod_cast one_lt_two.trans hp
  -- absorb the real-linear coefficient into a complex-linear one, `Lᵖ` on a closed disc in `Ω`
  obtain ⟨KD, -, habs⟩ := exists_complexLinear_apply_eq V
  obtain ⟨D, hDξ, hDC, hDm⟩ := habs ξ C
  obtain ⟨R, hR, hRΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen z₀ hz₀
  have hR₀Ω : closedBall z₀ (R / 2) ⊆ Ω := (closedBall_subset_ball (half_lt_self hR)).trans hRΩ
  have hCR : MemLp C p (volume.restrict (closedBall z₀ (R / 2))) :=
    memLpLoc_iff.1 hC _ hR₀Ω (isCompact_closedBall _ _)
  have hDR : MemLp D p (volume.restrict (closedBall z₀ (R / 2))) :=
    hCR.of_le_mul (hDm _ hCR.aestronglyMeasurable
      ((h.continuousOn.mono hR₀Ω).aestronglyMeasurable (μ := volume) measurableSet_closedBall))
      (Eventually.of_forall hDC)
  -- solve the Cauchy integral equation `Ψ = 1 - T (½ D Ψ)` on a small closed disc
  obtain ⟨r, hr, hrR, g, hg, hgs, hTg, hgeq, hTg1⟩ :=
    exists_cauchyTransform_eq_of_memLp_closedBall hp (half_pos hR)
      ((memLp_indicator_iff_restrict measurableSet_closedBall.nullMeasurableSet).2 hDR)
  have hball : ball z₀ r ⊆ Ω :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall hrR).trans hR₀Ω)
  let B : Opens ℂ := ⟨ball z₀ r, isOpen_ball⟩
  set Ψ : ℂ → V →L[ℂ] V := fun z ↦ 1 - cauchyTransform g z with hΨ
  have hunit (z : ℂ) (hz : z ∈ ball z₀ r) : IsUnit (Ψ z) := by
    by_contra hn
    refine nonunits.subset_compl_ball hn ?_
    rw [mem_ball_iff_norm, hΨ, sub_sub_cancel_left, norm_neg]
    exact hTg1 z (ball_subset_closedBall hz)
  -- its weak derivative `-DT` has `∂ₛΨ + i ∂ₜΨ = -2 g = -D Ψ`
  obtain ⟨DT, hDTp, hDT, hDTI⟩ :=
    exists_hasWeakFDerivOn_cauchyTransform_of_memLp hp1 ENNReal.coe_ne_top hg hgs
  have h1 : HasWeakFDerivOn volume B (fun _ ↦ (1 : V →L[ℂ] V)) 0 :=
    hasWeakFDerivOn_iff.2 fun v ↦ by simpa using hasWeakLineDerivOn_const (v := v) _
  have hΨw : HasWeakFDerivOn volume B Ψ fun w ↦ -DT w :=
    (h1.sub (hDT B)).congr_ae_deriv (Eventually.of_forall fun w ↦ by simp)
  have hΨc : ContinuousOn Ψ B := (continuous_const.sub hTg).continuousOn
  have hDΨ : MemLpLoc p B fun w ↦ -DT w := (hDTp.neg.restrict _).memLpLoc
  obtain ⟨σ, hσ, hξσ⟩ := exists_differentiableOn_eqOn_clm_apply hp hΨc hunit hΨw hDΨ
    (fun z hz ↦ by
      rw [neg_apply, neg_apply, smul_neg, ← neg_add, hDTI, hgeq z (ball_subset_closedBall hz),
        smul_smul, mul_inv_cancel₀ (two_ne_zero' ℂ), one_smul])
    (fun z _ ↦ hDξ z) (h.mono hball)
  exact ⟨r, hr, hball, Ψ, σ, hΨc,
    memWkpLoc_succ_iff_of_isOpen.2 ⟨hΨc.memLpLoc, _, hΨw, memWkpLoc_zero_iff.2 hDΨ⟩, hunit, hσ,
    hξσ⟩

/-! ### A variable complex structure -/

variable [FiniteDimensional ℂ V] {p : ℝ≥0} {Ω : Opens ℂ} {J C : ℂ → V →L[ℝ] V} {ξ : ℂ → V}

/-- **The similarity principle for weak solutions** (Carleman; McDuff–Salamon, Theorem 2.3.5).
Let `p > 2`, let `J` be a continuous field of complex structures, `J² = -1`, on a
finite-dimensional complex normed space `V`, of class `W^{1,p}_loc` on an open set `Ω`, let `C` be
a locally `Lᵖ` field of real-linear endomorphisms of `V`, and let `ξ` be a weak solution of
`∂ₛξ + J ∂ₜξ + C ξ = 0` on `Ω`. Then every point `z₀ ∈ Ω` is the centre of a disc in `Ω` on which
`ξ = Φ σ`, with `Φ` a continuous `W^{1,p}` family of invertible real-linear maps satisfying
`J Φ = Φ i` and `σ` holomorphic. -/
theorem exists_similarity_of_isWeakLinearCauchyRiemannOn_of_complexStructure (hp : 2 < p)
    (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (h : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hC : MemLpLoc p Ω C) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) :
    ∃ r > 0, ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → V →L[ℝ] V) (σ : ℂ → V),
      ContinuousOn Φ (ball z₀ r) ∧ MemWkpLoc p (ball z₀ r) 1 Φ ∧
      (∀ z ∈ ball z₀ r,
        IsUnit (Φ z) ∧ J z ∘L Φ z = Φ z ∘L (I • ContinuousLinearMap.id ℝ V)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧ EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ V
  have h₀ := hJJ z₀ hz₀
  -- reduce to the standard structure with the standard frame `S` on a disc `B₁`
  obtain ⟨Φ₁, hΦ₁⟩ :=
    ContinuousLinearMap.exists_continuousLinearEquiv_comp_eq_comp_I_smul (J z₀) h₀
  obtain ⟨r₁, hr₁, hr₁Ω, hu⟩ :=
    exists_ball_isUnit_standardFrame (Φ₁ := Φ₁) Ω.isOpen hz₀ hJc h₀
  let B₁ : Opens ℂ := ⟨ball z₀ r₁, isOpen_ball⟩
  set S := standardFrame J z₀ Φ₁
  have hSw : MemWkpLoc p B₁ 1 S := (memWkpLoc_standardFrame hJ).mono hr₁Ω
  obtain ⟨DS, hDS, hDSp⟩ := hSw.exists_weakFDeriv_of_isOpen
  rw [memWkpLoc_zero_iff] at hDSp
  have hJc₁ : ContinuousOn J B₁ := hJc.mono hr₁Ω
  have hη := (isWeakLinearCauchyRiemannOn_iff_standardFrame hp hJc₁
    (fun z hz ↦ hJJ z (hr₁Ω hz)) h₀ hΦ₁ hu hDS hDSp).1 (h.mono hr₁Ω)
  have hC₁ : MemLpLoc p B₁ (frameCoeff J C S DS) :=
    (memLpLoc_frameCoeff_iff isOpen_ball.measurableSet (continuousOn_standardFrame hJc₁) hDSp hu
      hJc₁).2 (hC.mono_set hr₁Ω)
  -- and factor the solution of the reduced equation
  obtain ⟨r, hr, hrB, Ψ, σ, hΨc, hΨw, hΨu, hσ, hησ⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemannOn hp hη hC₁ (mem_ball_self hr₁)
  have hrr₁ : ball z₀ r ⊆ ball z₀ r₁ := hrB
  let L : (V →L[ℂ] V) →L[ℝ] V →L[ℝ] V := ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ
  refine ⟨r, hr, hrr₁.trans hr₁Ω, fun z ↦ S z ∘L L (Ψ z), σ, ?_, ?_, fun z hz ↦ ⟨?_, ?_⟩, hσ,
    fun z hz ↦ ?_⟩
  · exact ((continuousOn_standardFrame hJc₁).mono hrr₁).clm_comp
      (L.continuous.comp_continuousOn hΨc)
  · let Br : Opens ℂ := ⟨ball z₀ r, isOpen_ball⟩
    have hp1 : (1 : ℝ≥0) < p := one_lt_two.trans hp
    exact (hSw.mono hrr₁ : MemWkpLoc p Br 1 S).bilin (ContinuousLinearMap.compL ℝ V V V) hp hp1
      le_rfl (hΨw.clm_comp L : MemWkpLoc p Br 1 fun z ↦ L (Ψ z))
  · obtain ⟨u, hu'⟩ := hΨu z hz
    exact (hu z (hrr₁ hz)).mul
      (hu' ▸ ⟨((ContinuousLinearEquiv.unitsEquiv ℂ V u).restrictScalars ℝ).toUnit, rfl⟩)
  · rw [← ContinuousLinearMap.comp_assoc, comp_standardFrame (hJJ z (hr₁Ω (hrr₁ hz))) h₀ hΦ₁,
      ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc]
    congr 1
    ext v
    simp [L]
  · have hinv : S z (Ring.inverse (S z) (ξ z)) = ξ z := by
      simpa using congr($(Ring.mul_inverse_cancel _ (hu z (hrr₁ hz))) (ξ z))
    have hη : Ring.inverse (S z) (ξ z) = Ψ z (σ z) := hησ hz
    rw [← hinv, hη]
    simp [L]

/-- A weak solution of `∂ₛξ + J ∂ₜξ + C ξ = 0` on an open set `Ω`, with `J` a continuous
`W^{1,p}_loc` field of complex structures and `C` locally `Lᵖ`, `p > 2`, has a similarity
factorization at every point of `Ω`. -/
theorem hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn_of_complexStructure (hp : 2 < p)
    (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (h : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hC : MemLpLoc p Ω C) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) : HasSimilarityFactorizationAt ξ z₀ := by
  have := FiniteDimensional.completeSpace ℂ V
  obtain ⟨r, hr, -, Φ, σ, hΦ, -, hΦu, hσ, hξσ⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemannOn_of_complexStructure hp hJc hJ hJJ h hC hz₀
  exact .of_eqOn_ball hr hΦ (hΦu z₀ (mem_ball_self hr)).1 hσ hξσ

/-- **Unique continuation** for weak solutions. On a connected open set `Ω`, a weak solution of
`∂ₛξ + J ∂ₜξ + C ξ = 0`, with `J` a continuous `W^{1,p}_loc` field of complex structures and `C`
locally `Lᵖ`, `p > 2`, that vanishes to infinite order at one point of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_forall_isBigO_of_complexStructure (hp : 2 < p)
    (hΩc : IsPreconnected (Ω : Set ℂ)) (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (h : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hC : MemLpLoc p Ω C) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) (h₀ : ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n) : EqOn ξ 0 Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact eqOn_zero_of_hasSimilarityFactorizationAt_of_forall_isBigO Ω.isOpen hΩc h.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn_of_complexStructure
      hp hJc hJ hJJ h hC hz) hz₀ h₀

/-- **Unique continuation** for weak solutions. On a connected open set `Ω`, a weak solution of
`∂ₛξ + J ∂ₜξ + C ξ = 0`, with `J` a continuous `W^{1,p}_loc` field of complex structures and `C`
locally `Lᵖ`, `p > 2`, that vanishes on a nonempty open subset of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_eqOn_zero_of_complexStructure (hp : 2 < p)
    (hΩc : IsPreconnected (Ω : Set ℂ)) (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (h : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hC : MemLpLoc p Ω C) {U : Set ℂ}
    (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (h₀ : EqOn ξ 0 U) : EqOn ξ 0 Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact eqOn_zero_of_hasSimilarityFactorizationAt_of_eqOn_zero Ω.isOpen hΩc h.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn_of_complexStructure
      hp hJc hJ hJJ h hC hz) hU hUne hUΩ h₀

/-- **Isolated zeros** of weak solutions. On a connected open set `Ω`, the zeros of a weak
solution of `∂ₛξ + J ∂ₜξ + C ξ = 0`, with `J` a continuous `W^{1,p}_loc` field of complex
structures and `C` locally `Lᵖ`, `p > 2`, that is not identically zero on `Ω` form a discrete
subset of `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_isWeakLinearCauchyRiemannOn_of_complexStructure
    (hp : 2 < p) (hΩc : IsPreconnected (Ω : Set ℂ)) (hJc : ContinuousOn J Ω)
    (hJ : MemWkpLoc p Ω 1 J) (hJJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (h : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hC : MemLpLoc p Ω C)
    (hne : ∃ z ∈ Ω, ξ z ≠ 0) : {z | ξ z ≠ 0} ∈ codiscreteWithin (Ω : Set ℂ) := by
  have := FiniteDimensional.completeSpace ℂ V
  exact setOf_ne_zero_mem_codiscreteWithin_of_hasSimilarityFactorizationAt Ω.isOpen hΩc
    h.continuousOn (fun _ hz _ ↦
      hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn_of_complexStructure hp hJc hJ hJJ
        h hC hz) hne

end TauCeti
