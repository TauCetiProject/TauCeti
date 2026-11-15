/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation
public import TauCeti.Analysis.Complex.Pompeiu.Basic
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.MetricSpace.Contracting
import TauCeti.Analysis.Complex.Pompeiu.Pointwise
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
small closed disc by the contraction mapping theorem, here formulated for any supercritical `Lᵖ`
coefficient (`p > 2`, including `p = ∞`, in `TauCeti.exists_cauchyTransform_eq_of_memLp` and
`TauCeti.exists_pos_cauchyTransform_eq_of_memLp`). Its solution `Ψ` is continuous, close to
`1` and hence invertible, and has weak derivative `bar∂Ψ = ½ Ψ D`. The Leibniz rule for the
Cauchy transform (`TauCeti.hasWeakConjWirtingerDerivOn_cauchyTransform_apply`) then gives
`bar∂ (Ψ ξ) = Ψ (bar∂ξ + ½ D ξ) = Ψ (bar∂ξ + ½ C ξ) = 0` weakly, so `σ = Ψ ξ` is holomorphic by
Weyl's lemma, and `ξ = Ψ⁻¹ σ`.

## Main results

* `TauCeti.exists_cauchyTransform_eq_of_memLp` and
  `TauCeti.exists_pos_cauchyTransform_eq_of_memLp`: solvability of the Cauchy integral equation
  `Ψ = 1 + T (½ Ψ D)` on a small disc for supercritical `Lᵖ` operator coefficients.
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

/-! ### The Cauchy integral equation -/

section CauchyIntegralEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

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

private theorem norm_cauchySource_le_mul {c : ℂ} {r B : ℝ} {D : ℂ → E →L[ℂ] E}
    {Ψ : C(closedBall c r, E →L[ℂ] E)} (hΨ : ∀ x, ‖Ψ x‖ ≤ B) {z : ℂ}
    (hz : z ∈ closedBall c r) : ‖cauchySource D Ψ z‖ ≤ (2⁻¹ * B) * ‖D z‖ := by
  rw [cauchySource_of_mem D Ψ hz, norm_smul, norm_inv, Complex.norm_ofNat, mul_assoc]
  gcongr
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (hΨ _) (norm_nonneg _))

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

private theorem eLpNorm_cauchySource_le {c : ℂ} {r B : ℝ} {p : ℝ≥0∞} {D : ℂ → E →L[ℂ] E}
    (hD : AEStronglyMeasurable D (volume.restrict (closedBall c r)))
    {Ψ : C(closedBall c r, E →L[ℂ] E)} (hΨ : ∀ x, ‖Ψ x‖ ≤ B) :
    eLpNorm (cauchySource D Ψ) p volume ≤
      ENNReal.ofReal (2⁻¹ * B) * eLpNorm D p (volume.restrict (closedBall c r)) := by
  have heq : cauchySource D Ψ = (closedBall c r).indicator (cauchySource D Ψ) :=
    (indicator_eq_self.2 (support_cauchySource_subset D Ψ)).symm
  have hs : NullMeasurableSet (closedBall c r) volume := measurableSet_closedBall.nullMeasurableSet
  calc eLpNorm (cauchySource D Ψ) p volume
      = eLpNorm ((closedBall c r).indicator (cauchySource D Ψ)) p volume := by rw [← heq]
    _ = eLpNorm (cauchySource D Ψ) p (volume.restrict (closedBall c r)) :=
        eLpNorm_indicator_eq_eLpNorm_restrict (p := p) (f := cauchySource D Ψ) hs
    _ ≤ ENNReal.ofReal (2⁻¹ * B) * eLpNorm D p (volume.restrict (closedBall c r)) :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul (aestronglyMeasurable_cauchySource hD Ψ).restrict
          ((ae_restrict_mem measurableSet_closedBall).mono fun _ hz ↦
            norm_cauchySource_le_mul hΨ hz) p

private theorem memLp_cauchySource {c : ℂ} {r : ℝ} {p : ℝ≥0∞} {D : ℂ → E →L[ℂ] E}
    (hD : MemLp D p (volume.restrict (closedBall c r))) (Ψ : C(closedBall c r, E →L[ℂ] E)) :
    MemLp (cauchySource D Ψ) p volume :=
  (eLpNorm_cauchySource_le hD.aestronglyMeasurable Ψ.norm_coe_le_norm).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hD)

private theorem norm_cauchyTransform_cauchySource_le {p q : ℝ≥0∞} [p.HolderConjugate q]
    (hq : q < 2) {c : ℂ} {r B : ℝ} {D : ℂ → E →L[ℂ] E}
    (hD : MemLp D p (volume.restrict (closedBall c r))) {Ψ : C(closedBall c r, E →L[ℂ] E)}
    (hB : 0 ≤ B) (hΨ : ∀ x, ‖Ψ x‖ ≤ B) {w : ℂ} (hw : w ∈ closedBall c r) :
    ‖cauchyTransform (cauchySource D Ψ) w‖ ≤
      (2⁻¹ * Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (r + r)) q volume).toReal *
        (eLpNorm D p (volume.restrict (closedBall c r))).toReal) * B := by
  calc ‖cauchyTransform (cauchySource D Ψ) w‖
      ≤ Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (r + r)) q volume).toReal *
          (eLpNorm (cauchySource D Ψ) p volume).toReal :=
        norm_cauchyTransform_le hq (memLp_cauchySource hD Ψ) (support_cauchySource_subset D Ψ) hw
    _ ≤ Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (r + r)) q volume).toReal *
          ((2⁻¹ * B) * (eLpNorm D p (volume.restrict (closedBall c r))).toReal) := by
        gcongr
        have hfin : ENNReal.ofReal (2⁻¹ * B) *
            eLpNorm D p (volume.restrict (closedBall c r)) ≠ ⊤ :=
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top hD.eLpNorm_ne_top
        simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2⁻¹ * B)] using
          ENNReal.toReal_mono hfin (eLpNorm_cauchySource_le hD.aestronglyMeasurable hΨ)
    _ = _ := by ring

/-- **The supercritical Cauchy integral equation of the similarity principle.** On a closed disc
`closedBall c r` on which `D : ℂ → E →L[ℂ] E` belongs to `Lᵖ` (for Hölder conjugate exponents `p`,
`q` with `q < 2`, including `p = ∞`, `q = 1`), if
`2⁻¹ * π⁻¹ * ‖K_{r+r}‖_{L^q} * ‖D‖_{Lᵖ(closedBall c r)} ≤ 4⁻¹`, there is `g ∈ Lᵖ(ℂ)` supported in
`closedBall c r` whose Cauchy transform is continuous and satisfies `g = ½ (1 + T g) D` and
`‖T g‖ < 1` on `closedBall c r`. Thus `Ψ = 1 + T g` is a continuous family of invertible
complex-linear maps on the disc solving `bar∂Ψ = ½ Ψ D` weakly, obtained as the fixed point of the
contraction `Ψ ↦ 1 + T (½ Ψ D)` on `C(closedBall c r, E →L[ℂ] E)`. -/
theorem exists_cauchyTransform_eq_of_memLp [CompleteSpace E] {p q : ℝ≥0∞} [p.HolderConjugate q]
    (hq : q < 2) {D : ℂ → E →L[ℂ] E} {c : ℂ} {r : ℝ}
    (hD : MemLp D p (volume.restrict (closedBall c r)))
    (hrD : 2⁻¹ * Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (r + r)) q volume).toReal *
      (eLpNorm D p (volume.restrict (closedBall c r))).toReal ≤ 4⁻¹) :
    ∃ g : ℂ → E →L[ℂ] E, MemLp g p volume ∧ support g ⊆ closedBall c r ∧
      Continuous (cauchyTransform g) ∧
      (∀ z ∈ closedBall c r, g z = (2 : ℂ)⁻¹ • (1 + cauchyTransform g z).comp (D z)) ∧
      ∀ z ∈ closedBall c r, ‖cauchyTransform g z‖ < 1 := by
  set κ := 2⁻¹ * Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (r + r)) q volume).toReal *
    (eLpNorm D p (volume.restrict (closedBall c r))).toReal
  have hκ0 : 0 ≤ κ := by positivity
  have hsupp := support_cauchySource_subset (c := c) (r := r) D
  have hcont (Ψ : C(closedBall c r, E →L[ℂ] E)) :
      Continuous (cauchyTransform (cauchySource D Ψ)) :=
    continuous_cauchyTransform_of_memLp hq (memLp_cauchySource hD Ψ) (hsupp Ψ)
  have hT (Ψ : C(closedBall c r, E →L[ℂ] E)) {B : ℝ} (hB : 0 ≤ B) (hΨ : ∀ x, ‖Ψ x‖ ≤ B) (w : ℂ)
      (hw : w ∈ closedBall c r) : ‖cauchyTransform (cauchySource D Ψ) w‖ ≤ κ * B :=
    norm_cauchyTransform_cauchySource_le hq hD hB hΨ hw
  -- and depends linearly on `Ψ`
  have hlin (Ψ Ψ' : C(closedBall c r, E →L[ℂ] E)) (w : ℂ) :
      cauchyTransform (cauchySource D Ψ) w - cauchyTransform (cauchySource D Ψ') w =
        cauchyTransform (cauchySource D (Ψ - Ψ')) w := by
    rw [cauchySource_sub, cauchyTransform_sub_of_memLp hq (memLp_cauchySource hD Ψ) (hsupp Ψ)
      (memLp_cauchySource hD Ψ') (hsupp Ψ'), Pi.sub_apply]
  let op (Ψ : C(closedBall c r, E →L[ℂ] E)) : C(closedBall c r, E →L[ℂ] E) :=
    ⟨fun w ↦ 1 + cauchyTransform (cauchySource D Ψ) w,
      (continuous_const.add (hcont Ψ)).comp continuous_subtype_val⟩
  have hop : ContractingWith κ.toNNReal op := by
    refine ⟨by rw [Real.toNNReal_lt_one]; linarith, LipschitzWith.of_dist_le_mul fun Ψ Ψ' ↦ ?_⟩
    rw [Real.coe_toNNReal _ hκ0]
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
    simp only [op, ContinuousMap.coe_mk, hg]
  have hnorm : ‖Ψ₀‖ ≤ 4 / 3 := by
    have h1 : ‖Ψ₀‖ ≤ 1 + 4⁻¹ * ‖Ψ₀‖ := by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun w ↦ ?_
      rw [hΨ₀ w w.2]
      calc ‖1 + cauchyTransform g w‖ ≤ ‖(1 : E →L[ℂ] E)‖ + ‖cauchyTransform g w‖ :=
            norm_add_le _ _
        _ ≤ 1 + κ * ‖Ψ₀‖ :=
          add_le_add ContinuousLinearMap.norm_id_le
            (hT _ (by positivity) Ψ₀.norm_coe_le_norm w w.2)
        _ ≤ 1 + 4⁻¹ * ‖Ψ₀‖ := by gcongr
    linarith
  refine ⟨g, memLp_cauchySource hD Ψ₀, hsupp Ψ₀, hcont Ψ₀, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hg, cauchySource_of_mem D Ψ₀ hz, hΨ₀ z hz]
  · calc ‖cauchyTransform g z‖ ≤ κ * ‖Ψ₀‖ :=
          hT _ (by positivity) Ψ₀.norm_coe_le_norm z hz
      _ ≤ 4⁻¹ * (4 / 3) := by gcongr
      _ < 1 := by norm_num

/-- **Local solvability of the supercritical Cauchy integral equation.** If `D : ℂ → E →L[ℂ] E`
belongs to `Lᵖ` on `closedBall c R` (`R > 0`, with Hölder conjugate `q < 2`, including `p = ∞`,
`q = 1`), then on some smaller concentric closed disc `closedBall c r` with `0 < r < R` there is
`g ∈ Lᵖ(ℂ)` supported in `closedBall c r` whose Cauchy transform is continuous and satisfies
`g = ½ (1 + T g) D` and `‖T g‖ < 1` on `closedBall c r`. -/
theorem exists_pos_cauchyTransform_eq_of_memLp [CompleteSpace E] {p q : ℝ≥0∞}
    [p.HolderConjugate q] (hq : q < 2) {D : ℂ → E →L[ℂ] E} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hD : MemLp D p (volume.restrict (closedBall c R))) :
    ∃ r ∈ Ioo 0 R, ∃ g : ℂ → E →L[ℂ] E, MemLp g p volume ∧ support g ⊆ closedBall c r ∧
      Continuous (cauchyTransform g) ∧
      (∀ z ∈ closedBall c r, g z = (2 : ℂ)⁻¹ • (1 + cauchyTransform g z).comp (D z)) ∧
      ∀ z ∈ closedBall c r, ‖cauchyTransform g z‖ < 1 := by
  have : q.HolderConjugate p := ‹p.HolderConjugate q›.symm
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le (ENNReal.HolderConjugate.one_le q p)).ne'
  have hk0 : Tendsto (fun r : ℝ ↦ (eLpNorm (truncatedCauchyKernel (r + r)) q volume).toReal)
      (𝓝 0) (𝓝 0) := by
    have h1 := (tendsto_eLpNorm_truncatedCauchyKernel_nhds_zero hq0 hq).comp
      ((continuous_id.add continuous_id).tendsto' (0 : ℝ) 0 (add_zero 0))
    simpa only [Function.comp_def, Pi.add_apply, id_eq, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
  have hlim : Tendsto (fun r : ℝ ↦ 2⁻¹ * Real.pi⁻¹ *
      (eLpNorm (truncatedCauchyKernel (r + r)) q volume).toReal *
        (eLpNorm D p (volume.restrict (closedBall c R))).toReal) (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (hk0.const_mul (2⁻¹ * Real.pi⁻¹)).mul_const
        (eLpNorm D p (volume.restrict (closedBall c R))).toReal
  obtain ⟨δ, hδ, hδ4⟩ :=
    Metric.mem_nhds_iff.1 (hlim.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < 4⁻¹)))
  set r := min (R / 2) (δ / 2)
  have hr0 : 0 < r := lt_min (half_pos hR) (half_pos hδ)
  have hrR : r < R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hrδ : r ∈ ball (0 : ℝ) δ := by
    rw [mem_ball_zero_iff, Real.norm_of_nonneg hr0.le]
    exact (min_le_right _ _).trans_lt (half_lt_self hδ)
  have hsub : closedBall c r ⊆ closedBall c R := closedBall_subset_closedBall hrR.le
  have hDr : MemLp D p (volume.restrict (closedBall c r)) :=
    hD.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hrD : 2⁻¹ * Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (r + r)) q volume).toReal *
      (eLpNorm D p (volume.restrict (closedBall c r))).toReal ≤ 4⁻¹ := by
    refine (le_of_lt (hδ4 hrδ)).trans' ?_
    have hmono : (eLpNorm D p (volume.restrict (closedBall c r))).toReal ≤
        (eLpNorm D p (volume.restrict (closedBall c R))).toReal :=
      ENNReal.toReal_mono hD.eLpNorm_ne_top
        (eLpNorm_mono_measure D (Measure.restrict_mono hsub le_rfl))
    gcongr
  exact ⟨r, ⟨hr0, hrR⟩, exists_cauchyTransform_eq_of_memLp hq hDr hrD⟩

end CauchyIntegralEquation

/-! ### The similarity principle -/

section ClassicalInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

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
  have := ENNReal.HolderConjugate.top_one
  -- a disc in `Ω` on which `C` is bounded
  obtain ⟨M, hM⟩ := hCb z₀ hz₀
  obtain ⟨R, hR, hRΩ⟩ := Metric.mem_nhds_iff.1 (inter_mem hM (hΩ.mem_nhds hz₀))
  have hsubR : closedBall z₀ (R / 2) ⊆ ball z₀ R := closedBall_subset_ball (half_lt_self hR)
  have hsubRΩ : closedBall z₀ (R / 2) ⊆ Ω := fun z hz ↦ (hRΩ (hsubR hz)).2
  have hD : MemLp (fun z ↦ rankOneDivNormSq ℂ (C z (ξ z)) (ξ z)) ∞
      (volume.restrict (closedBall z₀ (R / 2))) :=
    memLp_top_of_bound
      ((hCm.mono_measure (Measure.restrict_mono hsubRΩ le_rfl)).rankOneDivNormSq_apply (𝕜 := ℂ)
        ((hξ.continuousOn.mono hsubRΩ).aestronglyMeasurable measurableSet_closedBall)) M
      ((ae_restrict_mem measurableSet_closedBall).mono fun z hz ↦
        ((C z).norm_rankOneDivNormSq_map_le _).trans (hRΩ (hsubR hz)).1)
  -- absorb the real-linear coefficient and solve the Cauchy integral equation
  obtain ⟨r, ⟨hr, hrR⟩, g, hg, hgs, hTg, hgeq, hTg1⟩ :=
    exists_pos_cauchyTransform_eq_of_memLp (p := ∞) (q := 1) (by norm_num) (half_pos hR) hD
  have hball : ball z₀ r ⊆ Ω :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hrR.le)).trans hsubRΩ
  have : IsFiniteMeasure (volume.restrict (closedBall z₀ r)) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have hgi : Integrable g := by
    rw [← indicator_eq_self.2 hgs]
    exact (integrable_indicator_iff measurableSet_closedBall).2 ((hg.restrict _).integrable le_top)
  set Ψ : ℂ → E →L[ℂ] E := fun z ↦ 1 + cauchyTransform g z with hΨ
  have hunit (z : ℂ) (hz : z ∈ ball z₀ r) : IsUnit (Ψ z) := by
    by_contra h
    refine nonunits.subset_compl_ball h ?_
    rw [mem_ball_iff_norm, hΨ, add_sub_cancel_left]
    exact hTg1 z (ball_subset_closedBall hz)
  refine ⟨r, hr, hball, fun z ↦ Ring.inverse (Ψ z), fun z ↦ Ψ z (ξ z),
    fun z hz ↦ ?_, fun z hz ↦ ?_, ?_, fun z hz ↦ ?_⟩
  · have hc := NormedRing.inverse_continuousAt (hunit z hz).unit
    rw [IsUnit.unit_spec] at hc
    exact (hc.comp (continuous_const.add hTg).continuousAt).continuousWithinAt
  · beta_reduce
    rw [← (hunit z hz).unit_spec, Ring.inverse_unit]
    exact Units.isUnit _
  · -- `Ψ ξ` is weakly holomorphic on the disc, hence holomorphic
    let D : Opens ℂ := ⟨ball z₀ r, isOpen_ball⟩
    have hξD : ContDiffOn ℝ 1 ξ D := hξ.mono hball
    have hw := (hasWeakConjWirtingerDerivOn_of_contDiffOn (μ := volume) hξD).add
      (hasWeakConjWirtingerDerivOn_cauchyTransform_apply hgi hξD)
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

end ClassicalInnerProductSpace

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
