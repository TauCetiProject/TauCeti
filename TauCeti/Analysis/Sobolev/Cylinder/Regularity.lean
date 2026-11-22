/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import TauCeti.Algebra.Order.Floor.Ring
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence

/-!
# Square-integrable sections with square-integrable image lie in `W^{1,2}` of the cylinder

Let `D ξ = M (ξ, ∂s ξ, ∂t ξ)` be a first-order operator on the cylinder `ℝ × S¹` with an
essentially bounded coefficient field `M`, satisfying the semi-Fredholm estimate
`TauCeti.CylinderSobolev.HasSemiFredholmEstimate`, as the linearized Floer operator along a Floer
trajectory does. The Sobolev space `TauCeti.CylinderSobolev.H1` is the closure of the jets of test
sections, which vanish for `|s|` large. This file shows that a `C²` section `ξ` of period one in
`t` which does not vanish for `|s|` large still defines an element of `H1` as soon as `ξ` and
`D ξ` are square integrable on the strip: its jet `(ξ, ∂s ξ, ∂t ξ)` is square integrable
(`TauCeti.CylinderSobolev.memLp_jet_of_hasSemiFredholmEstimate`). A `C²` section of period one
in `t` with square-integrable jet has its class in `H1`
(`TauCeti.CylinderSobolev.toLp_jet_mem_H1`), where the extension of `D` acts on it pointwise
(`TauCeti.coeFn_jetOperator`). In particular a classical solution of `D ξ = 0`
that is square integrable on the cylinder lies in the kernel of the extension of `D` to `H1`.
A continuous section of period one in `t` that vanishes almost everywhere
on the strip vanishes everywhere (`TauCeti.CylinderSobolev.eq_zero_of_ae_eq_zero`), so a nonzero
such solution gives a nonzero element of the kernel.

The sections are cut off by functions `ρ(s)` equal to `1` on `[-R, R]` and to `0` off
`[-2 R, 2 R]`, whose derivatives are `O(1 / R)`. Since `D (ρ ξ) = ρ D ξ + ρ' M (0, ξ, 0)`, the
semi-Fredholm estimate bounds the `W^{1,2}` norms of the cut-off sections uniformly in `R ≥ 1`;
Fatou's lemma then bounds that of `ξ`, and the cut-off jets converge to the jet of `ξ` in `L²` by
dominated convergence.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B,
  on Sobolev spaces and the semi-Fredholm estimate for first-order elliptic operators.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm theory of operators `∂s + J ∂t + S` on the
  cylinder.
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti.CylinderSobolev

open StripSobolev

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

omit [NormedSpace ℝ V] in
/-- A continuous section of period one in `t` that vanishes almost everywhere on the strip
`ℝ × [0, 1]` vanishes everywhere. -/
theorem eq_zero_of_ae_eq_zero {ξ : ℝ × ℝ → V} (hξ : Continuous ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (h : ξ =ᵐ[stripMeasure] 0) : ξ = 0 := by
  have hsub : (univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1 ⊆ univ ×ˢ Icc 0 1 :=
    prod_mono subset_rfl Ioo_subset_Icc_self
  -- `ξ` vanishes on the open strip, hence by continuity on the closed strip.
  have hopen : EqOn ξ 0 ((univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1) :=
    Measure.eqOn_open_of_ae_eq (μ := volume) (ae_restrict_of_ae_restrict_of_subset hsub h)
      (isOpen_univ.prod isOpen_Ioo) hξ.continuousOn continuousOn_const
  have hclosed : EqOn ξ 0 ((univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1) := by
    refine hopen.of_subset_closure hξ.continuousOn continuousOn_const hsub ?_
    rw [closure_prod_eq, closure_univ, closure_Ioo zero_ne_one]
  -- By periodicity every point has the value of a point of the closed strip.
  funext ⟨s, t⟩
  have hp : Function.Periodic (fun t ↦ ξ (s, t)) 1 := fun t ↦ hper s t
  rw [← hp.apply_fract t]
  exact hclosed ⟨mem_univ s, Int.fract_nonneg t, (Int.fract_lt_one t).le⟩

/-- A sequence of cutoffs in `s`: smooth functions `ρ n` with values in `[0, 1]`, equal to `1`
for `|s| ≤ n + 1` and to `0` for `|s| > 2 (n + 1)`, with derivatives bounded independently of
`n`. -/
private theorem exists_cutoff_seq : ∃ B : ℝ, ∃ ρ ρ' : ℕ → ℝ → ℝ,
    (∀ n, ContDiff ℝ 2 (ρ n)) ∧ (∀ n s, 0 ≤ ρ n s ∧ ρ n s ≤ 1) ∧
      (∀ (n : ℕ) (s : ℝ), |s| ≤ n + 1 → ρ n s = 1) ∧
        (∀ (n : ℕ) (s : ℝ), 2 * (n + 1) < |s| → ρ n s = 0) ∧
          (∀ n s, HasDerivAt (ρ n) (ρ' n s) s) ∧ ∀ n s, |ρ' n s| ≤ B := by
  obtain ⟨C, hC, h⟩ := exists_cutoff_fderiv_bound (E := ℝ)
  choose ρ ρ' hρ h01 h1 h0 hd hb _ _ using fun n : ℕ ↦ h 0 (n + 1) (by positivity)
  refine ⟨C, ρ, fun n s ↦ ρ' n s 1, fun n ↦ hρ n 2, h01, fun n s hs ↦ h1 n s ?_,
    fun n s hs ↦ h0 n s ?_, fun n s ↦ (hd n s).hasDerivAt, fun n s ↦ ?_⟩
  · rwa [Metric.mem_closedBall, Real.dist_0_eq_abs]
  · rwa [Real.dist_0_eq_abs]
  · rw [← Real.norm_eq_abs]
    refine ((ρ' n s).le_opNorm 1).trans ?_
    rw [norm_one, mul_one]
    exact (hb n s).trans (mul_le_of_le_one_right hC
      (inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg n))))

/-- The norm of the jet-shaped triple `(0, c v, 0)`, the correction term in `jet (β(s) ξ)`. -/
private theorem norm_zero_smul_zero (c : ℝ) (v : V) :
    ‖((0 : V), c • v, (0 : V))‖ = |c| * ‖v‖ := by
  simp only [Prod.norm_def, norm_zero, norm_smul, Real.norm_eq_abs]
  have ha : 0 ≤ |c| * ‖v‖ := by positivity
  rw [max_eq_left ha, max_eq_right ha]

variable {M : ℝ × ℝ → V × V × V →L[ℝ] W} {C T : ℝ} {ξ : ℝ × ℝ → V}

/-- A `C²` section of period one in `t`, cut off by a `C²` function of `s` vanishing for
`|s| > R`, is a test section. -/
private theorem smul_fst_mem_testSection {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 2 ρ) {R : ℝ}
    (hρ0 : ∀ s, R < |s| → ρ s = 0) (hξ : ContDiff ℝ 2 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) :
    (fun w : ℝ × ℝ ↦ ρ w.1 • ξ w) ∈ testSection V := by
  refine mem_testSection_iff.2 ⟨(hρ.comp contDiff_fst).smul hξ, fun s t ↦ by simp [hper],
    R + 1, fun s t hs ↦ ?_⟩
  rw [hρ0 s (by linarith), zero_smul]

/-- Pointwise, `D (ρ ξ) = ρ D ξ + ρ' M (0, ξ, 0)` is bounded by `‖D ξ‖ + B ‖M‖ ‖ξ‖` when
`0 ≤ ρ ≤ 1` and `|ρ'| ≤ B`. -/
private theorem norm_apply_jet_smul_fst_le {ρ : ℝ → ℝ} {ρ' : ℝ} {B : ℝ} {z : ℝ × ℝ}
    (hρd : HasDerivAt ρ ρ' z.1) (hρ01 : 0 ≤ ρ z.1 ∧ ρ z.1 ≤ 1) (hρ'B : |ρ'| ≤ B)
    (hξ : DifferentiableAt ℝ ξ z) :
    ‖M z (jet (fun w ↦ ρ w.1 • ξ w) z)‖ ≤ ‖M z (jet ξ z)‖ + B * ‖M z‖ * ‖ξ z‖ := by
  have h0 : ‖M z ((0 : V), ρ' • ξ z, (0 : V))‖ ≤ B * ‖M z‖ * ‖ξ z‖ := by
    refine ((M z).le_opNorm _).trans ?_
    rw [norm_zero_smul_zero]
    calc ‖M z‖ * (|ρ'| * ‖ξ z‖) ≤ ‖M z‖ * (B * ‖ξ z‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hρ'B (norm_nonneg _))
            (norm_nonneg _)
      _ = B * ‖M z‖ * ‖ξ z‖ := by ring
  rw [jet_smul_fst hρd hξ, map_add, map_smul]
  refine (norm_add_le _ _).trans (add_le_add ?_ h0)
  rw [norm_smul, Real.norm_of_nonneg hρ01.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hρ01.2

/-- **A uniform bound for cut-off sections.** Under the semi-Fredholm estimate, if `ξ` and `D ξ`
are square integrable, the `W^{1,2}` norms of the cut-off sections `ρ(s) ξ` are bounded uniformly
over all cutoffs `0 ≤ ρ ≤ 1` vanishing for `|s|` large with `|ρ'| ≤ B`. -/
private theorem exists_eLpNorm_jet_smul_fst_le (hM : MemLp M ∞ stripMeasure)
    (hest : HasSemiFredholmEstimate M C T) (hξ : ContDiff ℝ 2 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (hξ2 : MemLp ξ 2 stripMeasure)
    (hD : MemLp (fun z ↦ M z (jet ξ z)) 2 stripMeasure) (B : ℝ) :
    ∃ A : ℝ≥0∞, A ≠ ∞ ∧ ∀ ⦃ρ ρ' : ℝ → ℝ⦄ ⦃R : ℝ⦄, ContDiff ℝ 2 ρ →
      (∀ s, 0 ≤ ρ s ∧ ρ s ≤ 1) → (∀ s, R < |s| → ρ s = 0) → (∀ s, HasDerivAt ρ (ρ' s) s) →
        (∀ s, |ρ' s| ≤ B) → eLpNorm (jet fun w ↦ ρ w.1 • ξ w) 2 stripMeasure ≤ A := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ᵐ z ∂stripMeasure, ‖M z‖ ≤ K := ⟨_, ae_le_lpNorm_exponent_top hM⟩
  set G : ℝ × ℝ → ℝ := fun z ↦ ‖M z (jet ξ z)‖ + B * K * ‖ξ z‖
  have hG : MemLp G 2 stripMeasure := hD.norm.add (hξ2.norm.const_mul (B * K))
  refine ⟨ENNReal.ofReal (√(max C 0) * ((eLpNorm G 2 stripMeasure).toReal +
    (eLpNorm ξ 2 stripMeasure).toReal)), ENNReal.ofReal_ne_top,
    fun ρ ρ' R hρ hρ01 hρ0 hρd hρ'B ↦ ?_⟩
  have hB : 0 ≤ B := (abs_nonneg _).trans (hρ'B 0)
  set η : testSection V := ⟨_, smul_fst_mem_testSection hρ hρ0 hξ hper⟩
  have hξd : Differentiable ℝ ξ := hξ.differentiable two_ne_zero
  have hηc : Continuous fun w : ℝ × ℝ ↦ ρ w.1 • ξ w :=
    (hρ.continuous.comp continuous_fst).smul hξ.continuous
  -- The two terms on the right of the semi-Fredholm estimate for `η = ρ ξ`.
  have hDη : ‖jetOperator stripMeasure M (jetLp (testSection V) η)‖ ≤
      (eLpNorm G 2 stripMeasure).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae (jetOperator_jetLp_ae_eq hM η)]
    refine ENNReal.toReal_mono hG.eLpNorm_ne_top (eLpNorm_mono_ae_real
      ((Lp.aestronglyMeasurable _).congr (jetOperator_jetLp_ae_eq hM η)) ?_)
    filter_upwards [hK] with z hz
    refine (norm_apply_jet_smul_fst_le (hρd z.1) (hρ01 z.1) (hρ'B z.1) (hξd z)).trans ?_
    simp only [G]
    gcongr
  have hTη : ‖restrictValue T (jetLp (testSection V) η)‖ ≤ (eLpNorm ξ 2 stripMeasure).toReal := by
    have hae : restrictValue T (jetLp (testSection V) η)
        =ᵐ[stripMeasure.restrict (Icc (-T) T ×ˢ Icc 0 1)] fun w ↦ ρ w.1 • ξ w := by
      filter_upwards [coeFn_restrictValue T (jetLp (testSection V) η),
        ae_restrict_of_ae (coeFn_jetLp η)] with z h₁ h₂
      rw [h₁, h₂, jet_apply]
    rw [Lp.norm_def, eLpNorm_congr_ae hae]
    refine ENNReal.toReal_mono hξ2.eLpNorm_ne_top
      ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans
        (eLpNorm_mono hηc.aestronglyMeasurable fun z ↦ ?_))
    rw [norm_smul, Real.norm_of_nonneg (hρ01 z.1).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hρ01 z.1).2
  -- Conclude from the semi-Fredholm estimate for `η`.
  have hη := norm_jetLp_le hM hest η
  rw [norm_jetLp] at hη
  rw [← ENNReal.ofReal_toReal (memLp_jet η.property).eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal (hη.trans (by gcongr))

/-- Where a cutoff equals `1` nearby, the cut-off section has the same jet as the section. -/
private theorem jet_smul_fst_eq {ρ : ℝ → ℝ} {R : ℝ} (hρ1 : ∀ s, |s| ≤ R → ρ s = 1)
    {z : ℝ × ℝ} (hz : |z.1| < R) : jet (fun w ↦ ρ w.1 • ξ w) z = jet ξ z := by
  have h : (fun w : ℝ × ℝ ↦ ρ w.1 • ξ w) =ᶠ[𝓝 z] ξ := by
    filter_upwards [(continuous_abs.comp continuous_fst).continuousAt.eventually
      (gt_mem_nhds hz)] with w hw
    rw [hρ1 w.1 hw.le, one_smul]
  simp only [jet_apply, h.fderiv_eq, h.eq_of_nhds]

/-- The jets of the sections cut off by cutoffs equal to `1` for `|s| ≤ n + 1` converge to the jet
of the section at every point. -/
private theorem tendsto_jet_smul_fst {ρ : ℕ → ℝ → ℝ}
    (hρ1 : ∀ n : ℕ, ∀ s : ℝ, |s| ≤ n + 1 → ρ n s = 1) (z : ℝ × ℝ) :
    Tendsto (fun n ↦ jet (fun w ↦ ρ n w.1 • ξ w) z) atTop (𝓝 (jet ξ z)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop |z.1|] with n hn
  exact (jet_smul_fst_eq (hρ1 n) (by linarith)).symm

/-- **Square-integrable sections with square-integrable image have square-integrable jets.** Let
`D ξ = M (ξ, ∂s ξ, ∂t ξ)` have an essentially bounded coefficient field and satisfy the
semi-Fredholm estimate. If a `C²` section `ξ` of period one in `t` and `D ξ` are square
integrable on the strip, so is the jet `(ξ, ∂s ξ, ∂t ξ)`. -/
theorem memLp_jet_of_hasSemiFredholmEstimate (hM : MemLp M ∞ stripMeasure)
    (hest : HasSemiFredholmEstimate M C T) (hξ : ContDiff ℝ 2 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (hξ2 : MemLp ξ 2 stripMeasure)
    (hD : MemLp (fun z ↦ M z (jet ξ z)) 2 stripMeasure) : MemLp (jet ξ) 2 stripMeasure := by
  obtain ⟨B, ρ, ρ', hρ, h01, h1, h0, hd, hb⟩ := exists_cutoff_seq
  obtain ⟨A, hA, hbound⟩ := exists_eLpNorm_jet_smul_fst_le hM hest hξ hper hξ2 hD B
  have hj (n : ℕ) : Continuous (jet fun w ↦ ρ n w.1 • ξ w) :=
    continuous_jet ((((hρ n).comp contDiff_fst).smul hξ).of_le (by norm_num))
  refine memLp_iff.2 ((Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall fun n ↦
    hbound (hρ n) (h01 n) (h0 n) (hd n) (hb n))
    (fun n ↦ (hj n).aestronglyMeasurable)
    (continuous_jet (hξ.of_le (by norm_num))).aestronglyMeasurable
    (Eventually.of_forall (tendsto_jet_smul_fst h1))).trans_lt hA.lt_top)

/-- **Sections with square-integrable jets lie in `W^{1,2}`.** If a `C²` section `ξ` of period
one in `t` has a square-integrable jet `(ξ, ∂s ξ, ∂t ξ)` on the strip, the class of that jet lies
in `H1 = W^{1,2}(ℝ × S¹, V)`, although `ξ` need not vanish for `|s|` large. -/
theorem toLp_jet_mem_H1 (hξ : ContDiff ℝ 2 ξ) (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t))
    (hj : MemLp (jet ξ) 2 stripMeasure) : hj.toLp (jet ξ) ∈ H1 V := by
  have hξ2 : MemLp ξ 2 stripMeasure := by simpa only [jet_apply] using hj.fst
  obtain ⟨B, ρ, ρ', hρ, h01, h1, h0, hd, hb⟩ := exists_cutoff_seq
  have hB : 0 ≤ B := (abs_nonneg _).trans (hb 0 0)
  have hmem (n : ℕ) : (fun w : ℝ × ℝ ↦ ρ n w.1 • ξ w) ∈ testSection V :=
    smul_fst_mem_testSection (hρ n) (h0 n) hξ hper
  refine (isClosed_jetClosure (testSection V)).mem_of_tendsto (b := atTop)
    (f := fun n : ℕ ↦ jetLp (testSection V) ⟨_, hmem n⟩) ?_
    (Eventually.of_forall fun n ↦ jetLp_mem_jetClosure _)
  -- The cut-off jets converge to the jet of `ξ` in `L²`, dominated by `‖jet ξ‖ + B ‖ξ‖`.
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hξd : Differentiable ℝ ξ := hξ.differentiable two_ne_zero
  refine (TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) ENNReal.ofNat_ne_top
    (Eventually.of_forall fun n ↦ (memLp_jet (hmem n)).aestronglyMeasurable)
    (hj.norm.add (hξ2.norm.const_mul B)) (Eventually.of_forall fun n ↦
      Eventually.of_forall fun z ↦ ?_)
    (Eventually.of_forall (tendsto_jet_smul_fst h1))).congr fun n ↦
      eLpNorm_congr_ae (((coeFn_jetLp ⟨_, hmem n⟩).sub hj.coeFn_toLp).symm)
  rw [ENNReal.coe_one, one_mul, eNorm_le_iff_norm_le, Pi.add_apply,
    Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))),
    jet_smul_fst (hd n z.1) (hξd z)]
  have hρz := h01 n z.1
  calc ‖ρ n z.1 • jet ξ z + ((0 : V), ρ' n z.1 • ξ z, (0 : V)) - jet ξ z‖
      = ‖(ρ n z.1 - 1) • jet ξ z + ((0 : V), ρ' n z.1 • ξ z, (0 : V))‖ := by
        congr 1
        rw [sub_smul, one_smul]
        abel
    _ ≤ |ρ n z.1 - 1| * ‖jet ξ z‖ + |ρ' n z.1| * ‖ξ z‖ := by
        refine (norm_add_le _ _).trans (add_le_add (by rw [norm_smul, Real.norm_eq_abs]) ?_)
        rw [norm_zero_smul_zero]
    _ ≤ 1 * ‖jet ξ z‖ + B * ‖ξ z‖ := by
        gcongr
        · rw [abs_le]
          constructor <;> linarith [hρz.1, hρz.2]
        · exact hb n z.1
    _ = ‖jet ξ z‖ + B * ‖ξ z‖ := by rw [one_mul]

end TauCeti.CylinderSobolev
