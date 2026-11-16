/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Lp
public import TauCeti.Analysis.Complex.Pompeiu.Weak
public import TauCeti.Analysis.Complex.Wirtinger.Beurling.Cauchy
public import TauCeti.Analysis.Complex.Wirtinger.Lp
public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.Analysis.Normed.Lp.SmoothApprox
import TauCeti.Analysis.Sobolev.WeakDeriv.Limit
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# The Cauchy transform of `Lᵖ` data is weakly differentiable

For `1 < p < ∞` and `f ∈ Lᵖ(ℂ)` supported in the closed disc of radius `r` about `c`, the Cauchy
transform `T f w = π⁻¹ ∫ (w - z)⁻¹ • f z` has a weak real derivative on the whole plane whose
Wirtinger parts are `∂ (T f) = B f` and `bar∂ (T f) = f`, where `B` is the Beurling operator
`TauCeti.beurlingLp` on `Lᵖ(ℂ)` (`TauCeti.hasWeakFDerivOn_cauchyTransform_of_memLp`). A real-linear
map `ℂ → F` with Wirtinger parts `a` and `b` is `v ↦ v • a + conj v • b`
(`TauCeti.wirtingerPartsCLM`), so the weak derivative is `w ↦ wirtingerPartsCLM (B f w) (f w)`.

The proof is by density. Smooth functions `g` supported in the disc of radius `r + 1` approximate
`f` in `Lᵖ`. For them the classical derivative of `T g` has Wirtinger parts `B g` (almost
everywhere, `HasCompactSupport.wirtingerDeriv_cauchyTransform_ae_eq_beurlingLp`) and `g`. On a
bounded disc `D_R`, `T g → T f` in `Lᵖ(D_R)` by the fixed-disc bound
`TauCeti.eLpNorm_cauchyTransform_le` with constant `2 (r + 1 + R)`, and `B g → B f` in `Lᵖ(ℂ)`
by continuity of `B`. Both convergences pass to `L¹(D_R)`, and weak derivatives survive `L¹`
limits (`TauCeti.hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub`). The discs exhaust the plane.

Consequences:

* `∂ (T f) = B f` almost everywhere for compactly supported `C¹` data
  (`HasCompactSupport.wirtingerDeriv_cauchyTransform_ae_eq_beurlingLp_of_contDiff_one`),
  extending the smooth case of `TauCeti.Analysis.Complex.Wirtinger.Beurling.Cauchy`;
* the global bound `‖w ↦ wirtingerPartsCLM (B f w) (f w)‖_{Lᵖ(ℂ)} ≤ (‖B‖ + 1) ‖f‖_{Lᵖ}` for all
  `Lᵖ` data (`TauCeti.eLpNorm_wirtingerPartsCLM_beurlingLp_le`), which bounds the weak derivative
  of `T f` globally; for `1 < p ≤ 2` and data with nonzero integral `T f` itself is not in
  `Lᵖ(ℂ)`, so only the derivative is bounded globally;
* the bound `T : Lᵖ(D_r) → W^{1,p}(D_R)` with explicit constant `2 (r + R) + ‖B‖ + 1`
  (`TauCeti.eLpNorm_cauchyTransform_add_eLpNorm_wirtingerPartsCLM_beurlingLp_le`), and membership
  of `T f` in the local Sobolev class `W^{1,p}_loc` on every subset of the plane
  (`TauCeti.memWkpLoc_one_cauchyTransform_of_memLp`);
* continuity in parameters of the derivative term: for a family of data depending continuously
  on a parameter in `Lᵖ`, the fields `w ↦ wirtingerPartsCLM (B f w) (f w)` depend continuously on
  it in `Lᵖ(ℂ)` (`TauCeti.continuous_toLp_wirtingerPartsCLM_beurlingLp`). The function term is
  `TauCeti.continuous_toLp_cauchyTransform`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.2 (the Cauchy and Beurling operators on `Lᵖ`).
* L. V. Ahlfors, *Lectures on Quasiconformal Mappings*, second edition, Chapter V, §A
  (`∂ (P f) = T f` and `bar∂ (P f) = f` for `f ∈ Lᵖ`, `p > 2`, in the notation there).
-/

public noncomputable section

open MeasureTheory Complex ComplexConjugate Metric Filter Topology Function Set TopologicalSpace
open scoped ENNReal NNReal ContDiff

namespace TauCeti

/-! ### The weak derivative of the Cauchy transform of `Lᵖ` data -/

section Weak

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On a disc, the weak derivative of the Cauchy transform of `Lᵖ` data supported in a disc. -/
private theorem hasWeakFDerivOn_cauchyTransform_ball (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {f : ℂ → F} (hf : MemLp f p volume)
    {c : ℂ} {r : ℝ≥0} (hs : support f ⊆ closedBall c (r : ℝ)) (R : ℝ≥0) :
    HasWeakFDerivOn volume ⟨ball c R, isOpen_ball⟩ (cauchyTransform f)
      fun w ↦ wirtingerPartsCLM (beurlingLp p hp hp_top (hf.toLp f) w) (f w) := by
  set B := beurlingLp (F := F) p hp hp_top
  set Ω : Opens ℂ := ⟨ball c R, isOpen_ball⟩
  set t := closedBall c ((r + 1 : ℝ≥0) : ℝ)
  have hst : closedBall c (r : ℝ) ⊆ t := closedBall_subset_closedBall (by simp)
  have hfs : support f ⊆ t := hs.trans hst
  have : IsFiniteMeasure (volume.restrict (closedBall c (r : ℝ))) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have hfint : Integrable f :=
    (integrableOn_iff_integrable_of_support_subset hs).1 ((hf.restrict _).integrable hp.le)
  have : IsFiniteMeasure (volume.restrict (ball c (R : ℝ))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  -- Smooth approximants supported in `t`.
  have ht : t ∈ 𝓝ˢ (closedBall c (r : ℝ)) :=
    mem_of_superset (isOpen_ball.mem_nhdsSet.2 (closedBall_subset_ball (by simp)))
      ball_subset_closedBall
  have happrox (n : ℕ) := hf.exist_contDiff_tsupport_subset_eLpNorm_sub_le hp_top hp.le
    isClosed_closedBall ht (.of_forall fun y hy ↦ notMem_support.1 fun h ↦ hy (hs h))
    (Nat.one_div_pos_of_nat (n := n))
  choose g hgc hg hgt hgf using happrox
  have hgm (n : ℕ) : MemLp (g n) p volume :=
    (hg n).continuous.memLp_of_hasCompactSupport (hgc n)
  have hgs (n : ℕ) : support (g n) ⊆ t := (subset_tsupport _).trans (hgt n)
  have hlim : Tendsto (fun n ↦ eLpNorm (g n - f) p volume) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ ↦ zero_le) fun n ↦ (eLpNorm_sub_comm _ _ _ _).trans_le (hgf n)
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  have hgLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hgm f hf).2 hlim
  -- `B g → B f` in `Lᵖ(ℂ)`.
  have hBlim : Tendsto (fun n ↦ eLpNorm (⇑(B ((hgm n).toLp (g n))) - ⇑(B (hf.toLp f))) p volume)
      atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 ((B.continuous.tendsto _).comp hgLp)
  -- The weak derivative of each smooth approximant.
  have hweak (n : ℕ) : HasWeakFDerivOn volume Ω (cauchyTransform (g n))
      fun w ↦ wirtingerPartsCLM (B ((hgm n).toLp (g n)) w) (g n w) := by
    have hT := (hgc n).contDiff_cauchyTransform (hg n)
    have hcl := hasWeakFDerivOn_of_differentiableOn (μ := volume) (Ω := Ω)
      ((hT.continuous_fderiv (by simp)).locallyIntegrable.locallyIntegrableOn _)
      fun x _ ↦ hT.differentiable (by simp) x
    refine hcl.congr_ae_deriv (ae_restrict_of_ae ?_)
    filter_upwards [(hgc n).wirtingerDeriv_cauchyTransform_ae_eq_beurlingLp (hg n) hp hp_top]
      with w hw
    rw [fderiv_eq_wirtingerPartsCLM, hw,
      (hgc n).conjWirtingerDeriv_cauchyTransform ((hg n).of_le (by simp))]
  -- The limit derivative field is in `Lᵖ(ℂ)`.
  have hD : MemLp (fun w ↦ wirtingerPartsCLM (B (hf.toLp f) w) (f w)) p volume :=
    MemLp.wirtingerPartsCLM (Lp.memLp _) hf
  refine hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub (l := atTop)
    ((locallyIntegrable_cauchyTransform hfint).locallyIntegrableOn _)
    (fun v ↦ (((ContinuousLinearMap.apply ℝ F v).comp_memLp' hD).locallyIntegrable
      hp.le).locallyIntegrableOn _) hweak ?_ ?_
  · -- `T g → T f` in `L¹` on the disc.
    refine (MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm hp.le ?_).congr fun n ↦
      eLpNorm_one_eq_lintegral_eNorm
        ((locallyIntegrable_cauchyTransform ((hg n).continuous.integrable_of_hasCompactSupport
          (hgc n))).aestronglyMeasurable.sub
            (locallyIntegrable_cauchyTransform hfint).aestronglyMeasurable).restrict
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).1
        (tendsto_toLp_cauchyTransform hf hgm hfs hgs hgLp R)) (fun _ ↦ zero_le)
      fun n ↦ eLpNorm_mono_measure _ (Measure.restrict_mono_set _ ball_subset_closedBall)
  · -- `D (T g) → D (T f)` in `L¹` on the disc.
    refine (MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm hp.le ?_).congr fun n ↦
      eLpNorm_one_eq_lintegral_eNorm ((MemLp.wirtingerPartsCLM (Lp.memLp _)
        (hgm n)).aestronglyMeasurable.sub hD.aestronglyMeasurable).restrict
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_eLpNorm_wirtingerPartsCLM_sub hp.le
        (fun _ ↦ (Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))
        (fun n ↦ ((hgm n).sub hf).aestronglyMeasurable) hBlim hlim) (fun _ ↦ zero_le)
      fun n ↦ eLpNorm_mono_measure _ Measure.restrict_le_self

/-- **The weak derivative of the Cauchy transform of `Lᵖ` data.** For `1 < p < ∞` and `f ∈ Lᵖ(ℂ)`
supported in a closed disc, the Cauchy transform `T f` is weakly differentiable on every open
subset of the plane, and its weak derivative has Wirtinger parts `∂ (T f) = B f`, the Beurling
operator applied to `f`, and `bar∂ (T f) = f`. -/
theorem hasWeakFDerivOn_cauchyTransform_of_memLp (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {f : ℂ → F} (hf : MemLp f p volume) {c : ℂ} {r : ℝ} (hs : support f ⊆ closedBall c r)
    (Ω : Opens ℂ) :
    HasWeakFDerivOn volume Ω (cauchyTransform f)
      fun w ↦ wirtingerPartsCLM (beurlingLp p hp hp_top (hf.toLp f) w) (f w) := by
  have hs' : support f ⊆ closedBall c (r.toNNReal : ℝ) :=
    hs.trans (closedBall_subset_closedBall (Real.le_coe_toNNReal r))
  refine hasWeakFDerivOn_iff_locally.2 fun x _ ↦
    ⟨⟨ball c ((‖x - c‖₊ + 1 : ℝ≥0) : ℝ), isOpen_ball⟩, ?_,
      hasWeakFDerivOn_cauchyTransform_ball hp hp_top hf hs' _⟩
  rw [Opens.mem_mk, mem_ball, dist_eq_norm]
  push_cast
  linarith

/-- **`∂ T = B` on compactly supported `C¹` data.** For `1 < p < ∞` and compactly supported `C¹`
data `f`, the Wirtinger derivative `∂ (T f)` agrees almost everywhere with the Beurling operator
on `Lᵖ(ℂ)` applied to `f`. -/
theorem _root_.HasCompactSupport.wirtingerDeriv_cauchyTransform_ae_eq_beurlingLp_of_contDiff_one
    {f : ℂ → F} (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (fun w ↦ wirtingerDeriv (cauchyTransform f) w 1) =ᵐ[volume]
      beurlingLp p hp hp_top ((hf.continuous.memLp_of_hasCompactSupport hc).toLp f) := by
  have hfm : MemLp f p volume := hf.continuous.memLp_of_hasCompactSupport hc
  obtain ⟨r, hr⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  have hT := hc.contDiff_cauchyTransform hf
  have hcl := (hasWeakFDerivOn_cauchyTransform_of_memLp hp hp_top hfm
    ((subset_tsupport f).trans hr) ⊤).ae_eq_fderiv
      ((hT.continuous_fderiv one_ne_zero).locallyIntegrable.locallyIntegrableOn _)
      fun x _ ↦ hT.differentiable one_ne_zero x
  rw [Opens.coe_top, Measure.restrict_univ] at hcl
  filter_upwards [hcl] with w hw
  rw [fderiv_eq_wirtingerPartsCLM, hc.conjWirtingerDeriv_cauchyTransform hf] at hw
  exact (wirtingerPartsCLM_inj.1 hw).1.symm

/-- **The global derivative bound for the Cauchy transform of `Lᵖ` data.** The field
`w ↦ wirtingerPartsCLM (B f w) (f w)`, that is `v ↦ v • B f + conj v • f`, has `Lᵖ(ℂ)` norm at most
`(‖B‖ + 1) ‖f‖_{Lᵖ}`, where `‖B‖` is the operator norm of the Beurling operator on `Lᵖ(ℂ)`. For
`f` supported in a closed disc this field is the weak derivative of `T f`
(`TauCeti.hasWeakFDerivOn_cauchyTransform_of_memLp`). For `1 < p ≤ 2` and data with nonzero
integral `T f` itself is not in `Lᵖ(ℂ)`, so only the derivative is bounded globally. -/
theorem eLpNorm_wirtingerPartsCLM_beurlingLp_le (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {f : ℂ → F} (hf : MemLp f p volume) :
    eLpNorm (fun w ↦ wirtingerPartsCLM (beurlingLp p hp hp_top (hf.toLp f) w) (f w)) p volume ≤
      ((‖beurlingLp (F := F) p hp hp_top‖₊ : ℝ≥0∞) + 1) * eLpNorm f p volume := by
  set B := beurlingLp (F := F) p hp hp_top
  set a := ⇑(B (hf.toLp f))
  have hB : eLpNorm a p volume ≤ ‖B‖₊ * eLpNorm f p volume :=
    calc eLpNorm a p volume = ‖B (hf.toLp f)‖ₑ := (Lp.eNorm_def _).symm
      _ ≤ ‖B‖₊ * ‖hf.toLp f‖ₑ := by
          simp only [eNorm_eq_nnNorm]
          exact_mod_cast B.le_opNNNorm _
      _ = ‖B‖₊ * eLpNorm f p volume := by
          rw [Lp.eNorm_def, eLpNorm_congr_ae hf.coeFn_toLp]
  calc eLpNorm (fun w ↦ wirtingerPartsCLM (a w) (f w)) p volume
      ≤ eLpNorm a p volume + eLpNorm f p volume :=
        eLpNorm_wirtingerPartsCLM_le hp.le (Lp.aestronglyMeasurable _) hf.aestronglyMeasurable
    _ ≤ ‖B‖₊ * eLpNorm f p volume + eLpNorm f p volume := by gcongr
    _ = ((‖B‖₊ : ℝ≥0∞) + 1) * eLpNorm f p volume := by ring

/-- **`T : Lᵖ(D_r) → W^{1,p}(D_R)` is bounded.** For `1 < p < ∞`, data `f ∈ Lᵖ` supported in the
closed disc of radius `r` about `c`, and every output radius `R`, the `Lᵖ` norms on the closed disc
of radius `R` of `T f` and of its weak derivative `w ↦ wirtingerPartsCLM (B f w) (f w)`
(`TauCeti.hasWeakFDerivOn_cauchyTransform_of_memLp`) sum to at most `2 (r + R) + ‖B‖ + 1` times
`‖f‖_{Lᵖ}`, where `‖B‖` is the operator norm of the Beurling operator on `Lᵖ(ℂ)`. -/
theorem eLpNorm_cauchyTransform_add_eLpNorm_wirtingerPartsCLM_beurlingLp_le (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) {f : ℂ → F} (hf : MemLp f p volume) {c : ℂ} {r : ℝ≥0}
    (hs : support f ⊆ closedBall c r) (R : ℝ≥0) :
    eLpNorm (cauchyTransform f) p (volume.restrict (closedBall c R)) +
        eLpNorm (fun w ↦ wirtingerPartsCLM (beurlingLp p hp hp_top (hf.toLp f) w) (f w)) p
          (volume.restrict (closedBall c R)) ≤
      ((2 * (r + R) + ‖beurlingLp (F := F) p hp hp_top‖₊ + 1 : ℝ≥0) : ℝ≥0∞) *
        eLpNorm f p volume := by
  have h₁ : eLpNorm (cauchyTransform f) p (volume.restrict (closedBall c R)) ≤
      (2 * (r + R) : ℝ≥0) * eLpNorm f p volume :=
    (eLpNorm_cauchyTransform_le hp.le hf.aestronglyMeasurable.restrict hs).trans
      (by gcongr; exact Measure.restrict_le_self)
  have h₂ := (eLpNorm_mono_measure
    (fun w ↦ wirtingerPartsCLM (beurlingLp p hp hp_top (hf.toLp f) w) (f w))
    (Measure.restrict_le_self (s := closedBall c (R : ℝ)))).trans
      (eLpNorm_wirtingerPartsCLM_beurlingLp_le hp hp_top hf)
  calc _ ≤ (2 * (r + R) : ℝ≥0) * eLpNorm f p volume +
        ((‖beurlingLp (F := F) p hp hp_top‖₊ : ℝ≥0∞) + 1) * eLpNorm f p volume :=
        add_le_add h₁ h₂
    _ = _ := by
        push_cast
        ring

/-- **The Cauchy transform of `Lᵖ` data is locally `W^{1,p}`.** For `1 < p < ∞` and `f ∈ Lᵖ(ℂ)`
supported in a closed disc, `T f` belongs to the local Sobolev class `W^{1,p}_loc` on every subset
of the plane. -/
theorem memWkpLoc_one_cauchyTransform_of_memLp (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {f : ℂ → F} (hf : MemLp f p volume) {c : ℂ} {r : ℝ} (hs : support f ⊆ closedBall c r)
    (U : Set ℂ) : MemWkpLoc p U 1 (cauchyTransform f) := by
  have hs' : support f ⊆ closedBall c (r.toNNReal : ℝ) :=
    hs.trans (closedBall_subset_closedBall (Real.le_coe_toNNReal r))
  refine memWkpLoc_succ_iff.2 ⟨memLpLoc_iff.2 fun K _ hK ↦ ?_, _,
    hasWeakFDerivOn_cauchyTransform_of_memLp hp hp_top hf hs _,
    memWkpLoc_zero_iff.2 <| memLpLoc_iff.2 fun K _ _ ↦
      (MemLp.wirtingerPartsCLM (Lp.memLp _) hf).restrict K⟩
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall c
  exact (memLp_cauchyTransform (R := R.toNNReal) hp.le (hf.restrict _) hs').mono_measure
    (Measure.restrict_mono_set _
      (hR.trans (closedBall_subset_closedBall (Real.le_coe_toNNReal R))))

/-- **Continuity in parameters of the derivative term.** For a family `f x` of `Lᵖ` data depending
continuously on `x` in `Lᵖ(ℂ)`, `1 < p < ∞`, the fields `v ↦ v • B (f x) + conj v • f x` depend
continuously on `x` in `Lᵖ(ℂ)`. When the data is supported in a common closed disc, these fields
are the weak derivatives of the Cauchy transforms `T (f x)`
(`TauCeti.hasWeakFDerivOn_cauchyTransform_of_memLp`). -/
theorem continuous_toLp_wirtingerPartsCLM_beurlingLp (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {X : Type*} [TopologicalSpace X] {f : X → ℂ → F} (hf : ∀ x, MemLp (f x) p volume)
    (hcont : Continuous fun x ↦ (hf x).toLp (f x)) :
    Continuous fun x ↦ (MemLp.wirtingerPartsCLM
      (Lp.memLp (beurlingLp p hp hp_top ((hf x).toLp (f x)))) (hf x)).toLp
        fun w ↦ wirtingerPartsCLM (beurlingLp p hp hp_top ((hf x).toLp (f x)) w) (f x w) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hf _ (hf x)).1 (hcont.tendsto x)
  have hB := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1
    (((beurlingLp p hp hp_top).continuous.comp hcont).tendsto x)
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).2
    (tendsto_eLpNorm_wirtingerPartsCLM_sub hp.le
      (fun _ ↦ (Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))
      (fun y ↦ ((hf y).sub (hf x)).aestronglyMeasurable) hB h)

end Weak

end TauCeti
