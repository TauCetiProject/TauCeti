/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.MetricSpace.Contracting
import TauCeti.Analysis.Complex.Pompeiu.Holder.Basic
import TauCeti.Analysis.Complex.Pompeiu.Pointwise
import TauCeti.Analysis.Complex.Pompeiu.Weak

/-!
# The similarity principle for classical solutions of linear Cauchy–Riemann equations

Let `V` be a finite-dimensional complex normed space, `Ω ⊆ ℂ` open, and `ξ : ℂ → V` a map of
class `C¹` on `Ω` solving the linear Cauchy–Riemann equation

`∂ₛξ + i ∂ₜξ + C ξ = 0`

on `Ω`, in the coordinate `z = s + i t`, for a continuous field `C` of *real*-linear endomorphisms
of `V`. The **similarity principle** says that near every point `z₀ ∈ Ω` the solution factors as
`ξ = Φ σ` with `Φ` a continuous family of invertible complex-linear maps and `σ` holomorphic
(`TauCeti.exists_similarity_of_contDiffOn`). In particular `ξ` has a similarity factorization in
the sense of `TauCeti.HasSimilarityFactorizationAt` at every point of `Ω`
(`TauCeti.hasSimilarityFactorizationAt_of_contDiffOn`), so it inherits the zero structure of a
holomorphic map: unique continuation from a zero of infinite order
(`TauCeti.eqOn_zero_of_contDiffOn_of_forall_isBigO`) and isolated zeros
(`TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn`).

The coefficient `C` need not commute with `i`, and a solution is in general not holomorphic.
The proof follows Carleman's argument as presented by McDuff and Salamon, after transporting the
equation along a complex-linear equivalence of `V` with a Euclidean space, whose inner product is
used only in the next step. First the real-linear term `C ξ` is absorbed into a complex-linear
coefficient depending on `ξ`: the rank-one map `D w = ‖ξ‖⁻² ⟪ξ, w⟫ C ξ` is complex-linear,
satisfies `D ξ = C ξ` and `‖D‖ ≤ ‖C‖`, and is merely measurable, since it jumps at the zeros
of `ξ`. Then the Cauchy integral equation
`Ψ = 1 + T (½ Ψ D)`, for the Cauchy transform `T` inverting `bar∂ = (∂ₛ + i ∂ₜ)/2`, is solved on a
small closed disc by the contraction mapping theorem. Its solution `Ψ` is continuous, close to
`1` and hence invertible, and has weak derivative `bar∂Ψ = ½ Ψ D`. The Leibniz rule for the
Cauchy transform (`TauCeti.hasWeakConjWirtingerDerivOn_cauchyTransform_apply`) then gives
`bar∂ (Ψ ξ) = Ψ (bar∂ξ + ½ D ξ) = Ψ (bar∂ξ + ½ C ξ) = 0` weakly, so `σ = Ψ ξ` is holomorphic by
Weyl's lemma, and `ξ = Ψ⁻¹ σ`.

## Main results

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ### Absorbing a real-linear coefficient -/

/-- A complex-linear map agreeing with the real-linear map `A` at `v`: the rank-one map
`w ↦ ‖v‖⁻² ⟪v, w⟫ • A v`, which is `0` when `v = 0`. -/
private def absorb (A : E →L[ℝ] E) (v : E) : E →L[ℂ] E :=
  ((‖v‖ : ℂ) ^ 2)⁻¹ • InnerProductSpace.rankOne ℂ (A v) v

/-- `absorb A v` agrees with `A` at `v`. -/
private theorem absorb_apply_self (A : E →L[ℝ] E) (v : E) : absorb A v v = A v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [absorb]
  · rw [absorb, smul_apply, InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K,
      smul_smul]
    simp [hv]

/-- `absorb A v` is no larger than `A`. -/
private theorem norm_absorb_le (A : E →L[ℝ] E) (v : E) : ‖absorb A v‖ ≤ ‖A‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [absorb]
  · have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
    rw [absorb, norm_smul, InnerProductSpace.norm_rankOne, norm_inv, norm_pow, Complex.norm_real,
      norm_norm]
    calc (‖v‖ ^ 2)⁻¹ * (‖A v‖ * ‖v‖) ≤ (‖v‖ ^ 2)⁻¹ * (‖A‖ * ‖v‖ * ‖v‖) := by
          gcongr
          exact A.le_opNorm v
      _ = ‖A‖ := by field_simp

/-- On a set where `A` and `v` are continuous, `z ↦ absorb (A z) (v z)` is almost everywhere
strongly measurable. It is continuous away from the zeros of `v`, but in general not at them. -/
private theorem aestronglyMeasurable_absorb {A : ℂ → E →L[ℝ] E} {v : ℂ → E} {s : Set ℂ}
    (hs : MeasurableSet s) (hA : ContinuousOn A s) (hv : ContinuousOn v s) :
    AEStronglyMeasurable (fun z ↦ absorb (A z) (v z)) (volume.restrict s) := by
  have hn : AEMeasurable (fun z ↦ ((‖v z‖ : ℂ) ^ 2)⁻¹) (volume.restrict s) :=
    measurable_inv.comp_aemeasurable
      (((Complex.continuous_ofReal.comp_continuousOn hv.norm).pow 2).aestronglyMeasurable
        hs).aemeasurable
  -- the rank-one map is `smulRight` of the functional `⟪v, ·⟫`, continuous in both arguments
  have hi : ContinuousOn (fun z ↦ ContinuousLinearMap.smulRightL ℂ E E (innerSL ℂ (v z))) s :=
    (ContinuousLinearMap.smulRightL ℂ E E).continuous.comp_continuousOn
      ((innerSL ℂ (E := E)).continuous.comp_continuousOn hv)
  have hr : ContinuousOn (fun z ↦ InnerProductSpace.rankOne ℂ (A z (v z)) (v z)) s :=
    (hi.clm_apply (hA.clm_apply hv)).congr fun _ _ ↦ rfl
  exact hn.aestronglyMeasurable.smul (hr.aestronglyMeasurable hs)

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

private theorem norm_cauchySource_le {c : ℂ} {r M B : ℝ} {D : ℂ → E →L[ℂ] E} (hM : 0 ≤ M)
    (hB : 0 ≤ B) (hD : ∀ z ∈ closedBall c r, ‖D z‖ ≤ M) {Ψ : C(closedBall c r, E →L[ℂ] E)}
    (hΨ : ∀ x, ‖Ψ x‖ ≤ B) (z : ℂ) : ‖cauchySource D Ψ z‖ ≤ 2⁻¹ * (B * M) := by
  by_cases hz : z ∈ closedBall c r
  · rw [cauchySource_of_mem D Ψ hz, norm_smul, norm_inv, Complex.norm_ofNat]
    gcongr
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hΨ _) (hD z hz) (norm_nonneg _) hB)
  · rw [cauchySource_of_notMem D Ψ hz, norm_zero]
    positivity

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

private theorem integrable_cauchySource {c : ℂ} {r M : ℝ} {D : ℂ → E →L[ℂ] E} (hM : 0 ≤ M)
    (hD : AEStronglyMeasurable D (volume.restrict (closedBall c r)))
    (hDM : ∀ z ∈ closedBall c r, ‖D z‖ ≤ M) (Ψ : C(closedBall c r, E →L[ℂ] E)) :
    Integrable (cauchySource D Ψ) :=
  (Measure.integrableOn_of_bounded measure_closedBall_lt_top.ne
    (aestronglyMeasurable_cauchySource hD Ψ)
    (ae_of_all _ (norm_cauchySource_le hM (by positivity) hDM (Ψ.norm_coe_le_norm))))
    |>.integrable_of_forall_notMem_eq_zero
    fun _ hz ↦ cauchySource_of_notMem D Ψ hz

/-- **The Cauchy integral equation of the similarity principle.** On a closed disc of radius `r`
on which a measurable field `D` of complex-linear maps is bounded by `M`, with `2 r M ≤ 1/4`,
there is an integrable `g`, vanishing off the disc, whose Cauchy transform is continuous and
satisfies `g = ½ (1 + T g) D` on the disc, with `‖T g‖ < 1` there. So `Ψ = 1 + T g` is a
continuous family of invertible maps on the disc solving `bar∂Ψ = ½ Ψ D`. It is the fixed point
of the contraction `Ψ ↦ 1 + T (½ Ψ D)` of the continuous maps on the disc. -/
private theorem exists_cauchyTransform_eq [FiniteDimensional ℂ E] {D : ℂ → E →L[ℂ] E} {c : ℂ}
    {r M : ℝ} (hr : 0 ≤ r) (hM : 0 ≤ M) (hrM : 2 * r * M ≤ 4⁻¹)
    (hD : AEStronglyMeasurable D (volume.restrict (closedBall c r)))
    (hDM : ∀ z ∈ closedBall c r, ‖D z‖ ≤ M) :
    ∃ g : ℂ → E →L[ℂ] E, Integrable g ∧ Continuous (cauchyTransform g) ∧
      (∀ z ∈ closedBall c r, g z = (2 : ℂ)⁻¹ • (1 + cauchyTransform g z).comp (D z)) ∧
      ∀ z ∈ closedBall c r, ‖cauchyTransform g z‖ < 1 := by
  have := FiniteDimensional.complete ℂ E
  have hmeas := aestronglyMeasurable_cauchySource hD
  have hsupp := support_cauchySource_subset (c := c) (r := r) D
  have hbd (Ψ : C(closedBall c r, E →L[ℂ] E)) :=
    norm_cauchySource_le hM (by positivity) hDM (Ψ.norm_coe_le_norm)
  have hcont (Ψ : C(closedBall c r, E →L[ℂ] E)) :
      Continuous (cauchyTransform (cauchySource D Ψ)) :=
    continuous_cauchyTransform_of_norm_le (hmeas Ψ) (hsupp Ψ) (hbd Ψ)
  -- the Cauchy transform of the source is small on the disc
  have hT (Ψ : C(closedBall c r, E →L[ℂ] E)) {B : ℝ} (hB : 0 ≤ B) (hΨ : ∀ x, ‖Ψ x‖ ≤ B) (w : ℂ)
      (hw : w ∈ closedBall c r) : ‖cauchyTransform (cauchySource D Ψ) w‖ ≤ 2 * r * M * B := by
    rw [cauchyTransform_apply]
    refine (norm_pi_inv_smul_integral_sub_inv_smul_le hr hr (hsupp Ψ)
      (norm_cauchySource_le hM hB hDM hΨ) hw).trans (le_of_eq (by ring))
  -- and depends linearly on `Ψ`
  have hlin (Ψ Ψ' : C(closedBall c r, E →L[ℂ] E)) (w : ℂ) :
      cauchyTransform (cauchySource D Ψ) w - cauchyTransform (cauchySource D Ψ') w =
        cauchyTransform (cauchySource D (Ψ - Ψ')) w := by
    have hi (Φ : C(closedBall c r, E →L[ℂ] E)) :
        Integrable fun z ↦ (w - z)⁻¹ • cauchySource D Φ z :=
      integrable_sub_inv_smul_of_memLp (p := ∞) (q := 1) (by norm_num)
        (memLp_top_of_bound (hmeas Φ) _ (ae_of_all _ (hbd Φ))) (hsupp Φ) w
    rw [cauchyTransform_apply, cauchyTransform_apply, cauchyTransform_apply, ← smul_sub,
      ← integral_sub (hi Ψ) (hi Ψ'), cauchySource_sub]
    simp only [Pi.sub_apply, smul_sub]
  let op (Ψ : C(closedBall c r, E →L[ℂ] E)) : C(closedBall c r, E →L[ℂ] E) :=
    ⟨fun w ↦ 1 + cauchyTransform (cauchySource D Ψ) w,
      (continuous_const.add (hcont Ψ)).comp continuous_subtype_val⟩
  have hop : ContractingWith (2 * r * M).toNNReal op := by
    refine ⟨by rw [Real.toNNReal_lt_one]; linarith, LipschitzWith.of_dist_le_mul fun Ψ Ψ' ↦ ?_⟩
    rw [Real.coe_toNNReal _ (by positivity)]
    refine (ContinuousMap.dist_le (by positivity)).2 fun w ↦ ?_
    simp only [op, ContinuousMap.coe_mk, dist_eq_norm, add_sub_add_left_eq_sub, hlin]
    refine hT _ dist_nonneg (fun x ↦ ?_) w w.2
    rw [ContinuousMap.sub_apply, ← dist_eq_norm]
    exact ContinuousMap.dist_apply_le_dist x
  set Ψ₀ := ContractingWith.fixedPoint op hop
  set g := cauchySource D Ψ₀ with hg
  have hfix : op Ψ₀ = Ψ₀ := ContractingWith.fixedPoint_isFixedPt hop
  have hΨ₀ (z : ℂ) (hz : z ∈ closedBall c r) : Ψ₀ ⟨z, hz⟩ = 1 + cauchyTransform g z := by
    rw [← hfix]
    rfl
  have hnorm : ‖Ψ₀‖ ≤ 4 / 3 := by
    have h1 : ‖Ψ₀‖ ≤ 1 + 4⁻¹ * ‖Ψ₀‖ := by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun w ↦ ?_
      rw [hΨ₀ w w.2]
      calc ‖1 + cauchyTransform g w‖ ≤ ‖(1 : E →L[ℂ] E)‖ + ‖cauchyTransform g w‖ :=
            norm_add_le _ _
        _ ≤ 1 + 2 * r * M * ‖Ψ₀‖ :=
          add_le_add ContinuousLinearMap.norm_id_le
            (hT _ (by positivity) Ψ₀.norm_coe_le_norm w w.2)
        _ ≤ 1 + 4⁻¹ * ‖Ψ₀‖ := by gcongr
    linarith
  refine ⟨g, integrable_cauchySource hM hD hDM Ψ₀, hcont Ψ₀, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hg, cauchySource_of_mem D Ψ₀ hz, hΨ₀ z hz]
  · calc ‖cauchyTransform g z‖ ≤ 2 * r * M * ‖Ψ₀‖ :=
          hT _ (by positivity) Ψ₀.norm_coe_le_norm z hz
      _ ≤ 4⁻¹ * (4 / 3) := by gcongr
      _ < 1 := by norm_num

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
  rw [conjWirtingerDeriv_apply, smul_eq_mul, mul_one, hG, smul_apply,
    ContinuousLinearMap.comp_apply, hD, hC, add_apply, one_apply_eq_self, map_neg, map_smul]
  module

/-- **The similarity principle on a disc**, for a solution of class `C¹` on the whole plane. -/
private theorem exists_similarity_of_contDiff [FiniteDimensional ℂ E] {ξ : ℂ → E}
    (hξ : ContDiff ℝ 1 ξ) {C : ℂ → E →L[ℝ] E} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hC : ContinuousOn C (closedBall c R))
    (heq : ∀ z ∈ ball c R, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I + C z (ξ z) = 0) :
    ∃ r, 0 < r ∧ r ≤ R ∧ ∃ (Φ : ℂ → E →L[ℂ] E) (σ : ℂ → E), ContinuousOn Φ (ball c r) ∧
      (∀ z ∈ ball c r, IsUnit (Φ z)) ∧ DifferentiableOn ℂ σ (ball c r) ∧
      EqOn ξ (fun z ↦ Φ z (σ z)) (ball c r) := by
  have := FiniteDimensional.complete ℂ E
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hC
  set M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  set r := min R (8 * (M + 1))⁻¹
  have hr : 0 < r := lt_min hR (by positivity)
  have hsub : closedBall c r ⊆ closedBall c R := closedBall_subset_closedBall (min_le_left _ _)
  -- absorb the real-linear coefficient and solve the Cauchy integral equation
  obtain ⟨g, hg, hTg, hgeq, hTg1⟩ := exists_cauchyTransform_eq hr.le hM (two_mul_min_mul_le hM)
    (aestronglyMeasurable_absorb measurableSet_closedBall (hC.mono hsub)
      hξ.continuous.continuousOn)
    (fun z hz ↦ (norm_absorb_le _ _).trans ((hM₀ z (hsub hz)).trans (le_max_left _ _)))
  set Ψ : ℂ → E →L[ℂ] E := fun z ↦ 1 + cauchyTransform g z with hΨ
  have hunit (z : ℂ) (hz : z ∈ ball c r) : IsUnit (Ψ z) := by
    by_contra h
    refine nonunits.subset_compl_ball h ?_
    rw [mem_ball_iff_norm, hΨ, add_sub_cancel_left]
    exact hTg1 z (ball_subset_closedBall hz)
  refine ⟨r, hr, min_le_left _ _, fun z ↦ Ring.inverse (Ψ z), fun z ↦ Ψ z (ξ z),
    fun z hz ↦ ?_, fun z hz ↦ ?_, ?_, fun z hz ↦ ?_⟩
  · have hc := NormedRing.inverse_continuousAt (hunit z hz).unit
    rw [IsUnit.unit_spec] at hc
    exact (hc.comp (continuous_const.add hTg).continuousAt).continuousWithinAt
  · beta_reduce
    rw [← (hunit z hz).unit_spec, Ring.inverse_unit]
    exact Units.isUnit _
  · -- `Ψ ξ` is weakly holomorphic on the disc, hence holomorphic
    let Ω : Opens ℂ := ⟨ball c r, isOpen_ball⟩
    have hw := (hasWeakConjWirtingerDerivOn_of_contDiffOn (μ := volume) (Ω := Ω)
      hξ.contDiffOn).add (hasWeakConjWirtingerDerivOn_cauchyTransform_apply hg hξ Ω)
    have hval : ∀ z ∈ (Ω : Set ℂ), ((fun z ↦ conjWirtingerDeriv ξ z 1) +
        fun z ↦ g z (ξ z) + cauchyTransform g z (conjWirtingerDeriv ξ z 1)) z = 0 :=
      fun z hz ↦ conjWirtingerDeriv_add_eq_zero (heq z (ball_subset_ball (min_le_left _ _) hz))
        (hgeq z (ball_subset_closedBall hz)) (absorb_apply_self _ _)
    have hw0 := hw.congr_ae_deriv ((ae_restrict_iff' Ω.isOpen.measurableSet).2
      (ae_of_all _ hval))
    have hσ : (ξ + fun z ↦ cauchyTransform g z (ξ z)) = fun z ↦ Ψ z (ξ z) := by
      ext1 z
      simp [hΨ]
    rw [hσ] at hw0
    exact hw0.differentiableOn
      ((continuous_const.add hTg).clm_apply hξ.continuous).continuousOn
  · beta_reduce
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def,
      Ring.inverse_mul_cancel _ (hunit z hz), one_apply_eq_self]

/-- The similarity principle on a complex inner product space, for a solution of class `C¹` on an
open set: the disc version cut off to the whole plane. -/
private theorem exists_similarity_of_contDiffOn_of_innerProductSpace [FiniteDimensional ℂ E]
    {Ω : Set ℂ} {ξ : ℂ → E} {C : ℂ → E →L[ℝ] E} (hΩ : IsOpen Ω) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hC : ContinuousOn C Ω)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I + C z (ξ z) = 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) :
    ∃ r, 0 < r ∧ ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → E →L[ℂ] E) (σ : ℂ → E),
      ContinuousOn Φ (ball z₀ r) ∧ (∀ z ∈ ball z₀ r, IsUnit (Φ z)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧ EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r) := by
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 hΩ z₀ hz₀
  -- cut `ξ` off outside a smaller disc, to get a `C¹` map on the whole plane
  let χ : ContDiffBump z₀ := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  set ξ' : ℂ → E := fun z ↦ χ z • ξ z with hξ'
  have hχΩ : closedBall z₀ (ε / 2) ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hεΩ
  have hξ'c : ContDiff ℝ 1 ξ' := by
    refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
    by_cases hx : x ∈ Ω
    · exact χ.contDiff.contDiffAt.smul (hξ.contDiffAt (hΩ.mem_nhds hx))
    · refine (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq ?_
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds fun h ↦ hx (hχΩ h)] with y hy
      simp only [hξ', χ.zero_of_le_dist (le_of_lt (by simpa using hy)), zero_smul]
  have hξ'eq : EqOn ξ' ξ (closedBall z₀ (ε / 4)) := fun z hz ↦ by
    simp [hξ', χ.one_of_mem_closedBall hz]
  have heq' (z : ℂ) (hz : z ∈ ball z₀ (ε / 4)) :
      fderiv ℝ ξ' z 1 + I • fderiv ℝ ξ' z I + C z (ξ' z) = 0 := by
    have hev : ξ' =ᶠ[𝓝 z] ξ := eventually_of_mem (isOpen_ball.mem_nhds hz) fun w hw ↦
      hξ'eq (ball_subset_closedBall hw)
    rw [hev.fderiv_eq, hξ'eq (ball_subset_closedBall hz)]
    exact heq z (hεΩ (ball_subset_ball (by linarith) hz))
  obtain ⟨r, hr, hrε, Φ, σ, hΦ, hΦu, hσ, hξσ⟩ := exists_similarity_of_contDiff hξ'c
    (by positivity) (hC.mono ((closedBall_subset_ball (by linarith)).trans hεΩ)) heq'
  refine ⟨r, hr, (ball_subset_ball (by linarith)).trans hεΩ, Φ, σ, hΦ, hΦu, hσ, fun z hz ↦ ?_⟩
  rw [← hξ'eq (ball_subset_closedBall (ball_subset_ball hrε hz))]
  exact hξσ hz

/-! ### Finite-dimensional complex normed spaces -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {Ω : Set ℂ} {ξ : ℂ → V} {C : ℂ → V →L[ℝ] V}

/-- **The similarity principle** (Carleman) for classical solutions. Let `ξ` be of class `C¹` on
an open set `Ω ⊆ ℂ` and solve `∂ₛξ + i ∂ₜξ + C ξ = 0` on `Ω`, for a continuous field `C` of
real-linear endomorphisms of a finite-dimensional complex normed space `V`. Then every point
`z₀ ∈ Ω` is the centre of a disc in `Ω` on which `ξ = Φ σ`, with `Φ` a continuous family of
invertible complex-linear maps and `σ` holomorphic. -/
theorem exists_similarity_of_contDiffOn (hΩ : IsOpen Ω) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hC : ContinuousOn C Ω)
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
  -- the real restrictions act as `e` and `e.symm`
  have h₁ (x : V) : eR x = e x := rfl
  have h₂ (y : EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) : eR' y = e.symm y := rfl
  have hξ' : ContDiffOn ℝ 1 (eR ∘ ξ) Ω := eR.contDiff.comp_contDiffOn hξ
  have hC' : ContinuousOn (fun z ↦ eR.comp ((C z).comp eR')) Ω :=
    continuousOn_const.clm_comp (hC.clm_comp continuousOn_const)
  have heq' (z : ℂ) (hz : z ∈ Ω) : fderiv ℝ (eR ∘ ξ) z 1 + I • fderiv ℝ (eR ∘ ξ) z I +
      eR.comp ((C z).comp eR') ((eR ∘ ξ) z) = 0 := by
    have hd : fderiv ℝ (eR ∘ ξ) z = eR.comp (fderiv ℝ ξ z) :=
      (eR.hasFDerivAt.comp z (((hξ.differentiableOn one_ne_zero).differentiableAt
        (hΩ.mem_nhds hz)).hasFDerivAt)).fderiv
    rw [hd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, Function.comp_apply, h₁,
      h₁, h₁, h₂, h₁, e.symm_apply_apply, ← map_smul, ← map_add, ← map_add, heq z hz, map_zero]
  obtain ⟨r, hr, hrΩ, Φ, σ, hΦ, hΦu, hσ, hξσ⟩ :=
    exists_similarity_of_contDiffOn_of_innerProductSpace hΩ hξ' hC' heq' hz₀
  refine ⟨r, hr, hrΩ, fun z ↦ e.symm.conjContinuousAlgEquiv (Φ z), fun z ↦ e.symm (σ z),
    ?_, fun z hz ↦ (hΦu z hz).map _,
    ((e.symm : _ →L[ℂ] V).differentiable.comp_differentiableOn hσ).congr fun _ _ ↦ rfl,
    fun z hz ↦ ?_⟩
  · simp only [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply]
    exact continuousOn_const.clm_comp (hΦ.clm_comp continuousOn_const)
  · have h := congrArg e.symm (hξσ hz)
    rw [Function.comp_apply, h₁, e.symm_apply_apply] at h
    simp [h]

/-- A `C¹` solution of `∂ₛξ + i ∂ₜξ + C ξ = 0` on an open set `Ω`, with continuous real-linear
coefficient `C`, has a similarity factorization at every point of `Ω`. -/
theorem hasSimilarityFactorizationAt_of_contDiffOn (hΩ : IsOpen Ω) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hC : ContinuousOn C Ω)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I + C z (ξ z) = 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) : HasSimilarityFactorizationAt ξ z₀ := by
  have := FiniteDimensional.complete ℂ V
  obtain ⟨r, hr, -, Φ, σ, hΦ, hΦu, hσ, hξσ⟩ := exists_similarity_of_contDiffOn hΩ hξ hC heq hz₀
  obtain ⟨u, hu⟩ := hΦu z₀ (mem_ball_self hr)
  refine .of_eqOn_ball hr (Φ := fun z ↦ (Φ z).restrictScalars ℝ)
    ((ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℂ).continuous.comp_continuousOn hΦ)
    ⟨⟨(Φ z₀).restrictScalars ℝ, (↑u⁻¹ : V →L[ℂ] V).restrictScalars ℝ, ?_, ?_⟩, rfl⟩ hσ hξσ
  · ext v
    have h := DFunLike.congr_fun u.mul_inv v
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, one_apply_eq_self] at h
    simpa [← hu] using h
  · ext v
    have h := DFunLike.congr_fun u.inv_mul v
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, one_apply_eq_self] at h
    simpa [← hu] using h

/-- **Unique continuation** for classical solutions. On a connected open set `Ω`, a `C¹` solution
of `∂ₛξ + i ∂ₜξ + C ξ = 0`, with continuous real-linear coefficient `C`, that vanishes to infinite
order at one point of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_contDiffOn_of_forall_isBigO (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hξ : ContDiffOn ℝ 1 ξ Ω) (hC : ContinuousOn C Ω)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I + C z (ξ z) = 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) (h₀ : ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n) : EqOn ξ 0 Ω := by
  have := FiniteDimensional.complete ℂ V
  exact eqOn_zero_of_hasSimilarityFactorizationAt_of_forall_isBigO hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_contDiffOn hΩ hξ hC heq hz) hz₀ h₀

/-- **Isolated zeros** of classical solutions. On a connected open set `Ω`, the zeros of a `C¹`
solution of `∂ₛξ + i ∂ₜξ + C ξ = 0`, with continuous real-linear coefficient `C`, that is not
identically zero on `Ω` form a discrete subset of `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hξ : ContDiffOn ℝ 1 ξ Ω) (hC : ContinuousOn C Ω)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I + C z (ξ z) = 0)
    (hne : ∃ z ∈ Ω, ξ z ≠ 0) : {z | ξ z ≠ 0} ∈ codiscreteWithin Ω := by
  have := FiniteDimensional.complete ℂ V
  exact setOf_ne_zero_mem_codiscreteWithin_of_hasSimilarityFactorizationAt hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_contDiffOn hΩ hξ hC heq hz) hne

end TauCeti
