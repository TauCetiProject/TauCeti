/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Lp
public import TauCeti.Analysis.Complex.Wirtinger.Beurling.Cauchy
public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.Analysis.Complex.Pompeiu.Weak
import TauCeti.Analysis.Normed.Lp.SmoothApprox
import TauCeti.Analysis.Sobolev.WeakDeriv.Limit
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# The Cauchy transform of `Lᵖ` data is a `W^{1,p}` map

The Cauchy transform `T f w = π⁻¹ ∫ (w - z)⁻¹ • f z` inverts `bar∂ = (∂ₛ + i ∂ₜ) / 2`, and on
smooth compactly supported data its Wirtinger derivative `∂ (T f)` is the Beurling operator `B f`
(`HasCompactSupport.wirtingerDeriv_cauchyTransform_ae_eq_beurlingLp`). This file extends the
second identity to rough data and reads off the mapping property `T : Lᵖ(D_r) → W^{1,p}(D_R)`.

Let `1 < p < ∞` and let `f ∈ Lᵖ(ℂ)` vanish outside the closed disc `D_r` of radius `r` about
`c`. Then `T f` is weakly differentiable on the whole plane, with weak real derivative

`D (T f) (w) v = v • B f (w) + conj v • f (w)`,

that is, `∂ (T f) = B f` and `bar∂ (T f) = f` weakly. Both terms lie in `Lᵖ(ℂ)`, so
`‖D (T f)‖_{Lᵖ(ℂ)} ≤ (‖B‖ + 1) ‖f‖_{Lᵖ}`, while `T f` itself is controlled only on bounded output
discs, `‖T f‖_{Lᵖ(D_R)} ≤ 2 (r + R) ‖f‖_{Lᵖ}` (`TauCeti.eLpNorm_cauchyTransform_le`): for
`1 < p ≤ 2` and data with nonzero integral, `T f` decays only like `1 / w` and is not in `Lᵖ(ℂ)`.
In particular `T f` belongs to the local Sobolev class `W^{1,p}_loc` of the whole plane.

The proof is by approximation. A function in `Lᵖ` vanishing outside `D_r` is the `Lᵖ` limit of
smooth functions supported in `D_{r + 1}`
(`MeasureTheory.MemLp.exist_contDiff_tsupport_subset_eLpNorm_sub_le`). For those the classical
derivative of `T g` is `v • B g + conj v • g` almost everywhere. On every bounded disc `D_R`,
`T g → T f` in `Lᵖ(D_R)` because `T` is bounded from `Lᵖ(D_{r + 1})` to `Lᵖ(D_R)`
(`TauCeti.cauchyTransformLp`), and the derivatives converge in `Lᵖ(ℂ)` because `B` is bounded on
`Lᵖ(ℂ)`. Convergence in `L¹` of a disc passes weak derivatives to the limit
(`TauCeti.hasWeakLineDerivOn_of_tendsto_lintegral_enorm_sub`), and every test function is
supported in some disc.

## Main results

* `TauCeti.hasWeakLineDerivOn_cauchyTransform`: the weak derivative of `T f` in the direction `v`
  is `v • B f + conj v • f`, on every open subset of the plane.
* `TauCeti.hasWeakFDerivOn_cauchyTransform`: the same statement for the weak real derivative.
* `TauCeti.eLpNorm_le_of_hasWeakFDerivOn_cauchyTransform`: every weak derivative of `T f` has
  `Lᵖ` norm at most `(‖B‖ + 1) ‖f‖_{Lᵖ}`, on the whole plane as on any open subset.
* `TauCeti.eLpNorm_cauchyTransform_add_eLpNorm_le_of_hasWeakFDerivOn`: on an open subset `Ω` of
  `D_R`, `‖T f‖_{Lᵖ(Ω)} + ‖D (T f)‖_{Lᵖ(Ω)} ≤ (2 (r + R) + ‖B‖ + 1) ‖f‖_{Lᵖ}`, so
  `T : Lᵖ(D_r) → W^{1,p}(D_R)` is bounded.
* `TauCeti.memWkpLoc_one_cauchyTransform`: `T f` belongs to the local Sobolev class
  `W^{1,p}_loc` of every subset of the plane.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.2 (the Cauchy and Beurling operators on `Lᵖ`, extended from smooth data by
  density).
* L. V. Ahlfors, *Lectures on Quasiconformal Mappings*, second edition, Chapter V, §A
  (the operators `P` and `T` with `∂(P f) = T f` and `bar∂ (P f) = f` on `Lᵖ`).
-/

public noncomputable section

open MeasureTheory Complex ComplexConjugate Metric Filter Topology Set TopologicalSpace Function
open scoped ENNReal NNReal ContDiff

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : ℂ → F} {c : ℂ} {r : ℝ≥0}

/-- For smooth compactly supported `g`, the classical derivative of `T g` in the direction `v` is
`v • B g + conj v • g` almost everywhere. -/
private theorem fderiv_cauchyTransform_apply_ae_eq {g : ℂ → F} (hc : HasCompactSupport g)
    (hg : ContDiff ℝ ∞ g) (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) (v : ℂ) :
    (fun w ↦ fderiv ℝ (cauchyTransform g) w v) =ᵐ[volume] fun w ↦
      v • beurlingLp p hp hp_top ((hg.continuous.memLp_of_hasCompactSupport hc).toLp g) w +
        conj v • g w := by
  filter_upwards [hc.wirtingerDeriv_cauchyTransform_ae_eq_beurlingLp hg hp hp_top] with w hw
  rw [fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv, hw,
    hc.conjWirtingerDeriv_cauchyTransform (hg.of_le (by simp))]

/-- The weak derivative `w ↦ v • B f (w) + conj v • f (w)` lies in `Lᵖ(ℂ)`. -/
private theorem memLp_smul_beurlingLp_add_smul (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (hf : MemLp f p volume) (v : ℂ) :
    MemLp (fun w ↦ v • beurlingLp p hp hp_top (hf.toLp f) w + conj v • f w) p volume :=
  ((Lp.memLp _).const_smul v).add (hf.const_smul (conj v))

/-- If smooth compactly supported `g n → f` in `Lᵖ(ℂ)`, then the classical derivatives of
`T (g n)` in the direction `v` converge to `v • B f + conj v • f` in `Lᵖ(ℂ)`, since `B` is bounded
on `Lᵖ(ℂ)`. -/
private theorem tendsto_eLpNorm_fderiv_cauchyTransform_sub (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) {g : ℕ → ℂ → F} (hgc : ∀ n, HasCompactSupport (g n))
    (hgs : ∀ n, ContDiff ℝ ∞ (g n)) (hgm : ∀ n, MemLp (g n) p volume) (hf : MemLp f p volume)
    (hconv : Tendsto (fun n ↦ eLpNorm (g n - f) p volume) atTop (𝓝 0)) (v : ℂ) :
    Tendsto (fun n ↦ eLpNorm (fun w ↦ fderiv ℝ (cauchyTransform (g n)) w v -
      (v • beurlingLp p hp hp_top (hf.toLp f) w + conj v • f w)) p volume) atTop (𝓝 0) := by
  set B := beurlingLp (F := F) p hp hp_top
  have hB : Tendsto (fun n ↦ eLpNorm (⇑(B ((hgm n).toLp (g n))) - ⇑(B (hf.toLp f))) p volume)
      atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 ((B.continuous.tendsto _).comp
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).2 hconv))
  have hle (n : ℕ) : eLpNorm (fun w ↦ fderiv ℝ (cauchyTransform (g n)) w v -
      (v • B (hf.toLp f) w + conj v • f w)) p volume ≤
      ‖v‖ₑ * eLpNorm (⇑(B ((hgm n).toLp (g n))) - ⇑(B (hf.toLp f))) p volume +
        ‖v‖ₑ * eLpNorm (g n - f) p volume := by
    calc _ = eLpNorm (v • (⇑(B ((hgm n).toLp (g n))) - ⇑(B (hf.toLp f))) +
          conj v • (g n - f)) p volume := by
          refine eLpNorm_congr_ae ?_
          filter_upwards [fderiv_cauchyTransform_apply_ae_eq (hgc n) (hgs n) hp hp_top v]
            with w hw
          simp only [hw, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_sub]
          abel
      _ ≤ _ := by
          refine (eLpNorm_add_le hp.le).trans ?_
          rw [eLpNorm_const_smul, eLpNorm_const_smul, RCLike.enorm_conj]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le) hle
  simpa using (ENNReal.Tendsto.const_mul hB (.inr enorm_ne_top)).add
    (ENNReal.Tendsto.const_mul hconv (.inr enorm_ne_top))

/-- The weak derivative on a disc, by approximation with smooth data supported in a slightly
larger disc. -/
private theorem hasWeakLineDerivOn_cauchyTransform_ball (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (hf : MemLp f p volume) (hfi : Integrable f) (hs : support f ⊆ closedBall c (r : ℝ))
    (R : ℝ≥0) (v : ℂ) :
    HasWeakLineDerivOn volume ⟨ball c R, isOpen_ball⟩ (cauchyTransform f)
      (fun w ↦ v • beurlingLp p hp hp_top (hf.toLp f) w + conj v • f w) v := by
  -- Smooth approximants `g n → f` in `Lᵖ`, supported in the disc of radius `r + 1`.
  have hr' : closedBall c ((r + 1 : ℝ≥0) : ℝ) ∈ 𝓝ˢ (closedBall c (r : ℝ)) :=
    mem_of_superset (isOpen_ball.mem_nhdsSet.2 (closedBall_subset_ball (by simp)))
      ball_subset_closedBall
  have hfs : ∀ᵐ y ∂volume, y ∉ closedBall c (r : ℝ) → f y = 0 :=
    .of_forall fun y hy ↦ notMem_support.1 fun h ↦ hy (hs h)
  choose g hgc hgs hgt hgf using fun n : ℕ ↦
    hf.exist_contDiff_tsupport_subset_eLpNorm_sub_le hp_top hp.le isClosed_closedBall hr' hfs
      (Nat.one_div_pos_of_nat (n := n) (α := ℝ))
  have hgm (n : ℕ) : MemLp (g n) p volume :=
    (hgs n).continuous.memLp_of_hasCompactSupport (hgc n)
  have hconv : Tendsto (fun n ↦ eLpNorm (g n - f) p volume) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ ↦ zero_le)
      fun n ↦ ?_
    rw [eLpNorm_sub_comm]
    exact hgf n
  have hT := tendsto_eLpNorm_cauchyTransform_sub hgm (fun n ↦ (subset_tsupport _).trans (hgt n))
    hf (hs.trans (closedBall_subset_closedBall (by simp))) hconv R
  -- The classical derivatives of `T (g n)` are weak derivatives on the disc.
  have hTg (n : ℕ) : ContDiff ℝ ∞ (cauchyTransform (g n)) :=
    (hgc n).contDiff_cauchyTransform (hgs n)
  have hdTg (n : ℕ) : Continuous fun w ↦ fderiv ℝ (cauchyTransform (g n)) w v :=
    ((hTg n).continuous_fderiv (by simp)).clm_apply continuous_const
  have hweak (n : ℕ) : HasWeakLineDerivOn volume ⟨ball c R, isOpen_ball⟩ (cauchyTransform (g n))
      (fun w ↦ fderiv ℝ (cauchyTransform (g n)) w v) v :=
    hasWeakLineDerivOn_of_hasLineDerivAt
      ((hTg n).continuous.locallyIntegrable.locallyIntegrableOn _)
      ((hdTg n).locallyIntegrable.locallyIntegrableOn _)
      fun w _ ↦ ((hTg n).differentiable (by simp) w).hasFDerivAt.hasLineDerivAt v
  -- They converge in `Lᵖ(ℂ)`, and `Lᵖ` convergence on the disc gives `L¹` convergence there, which
  -- passes to the limit.
  have hD := tendsto_eLpNorm_fderiv_cauchyTransform_sub hp hp_top hgc hgs hgm hf hconv v
  have hDm := memLp_smul_beurlingLp_add_smul hp hp_top hf v
  have : IsFiniteMeasure (volume.restrict (closedBall c (R : ℝ))) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have : IsFiniteMeasure (volume.restrict (ball c (R : ℝ))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  refine hasWeakLineDerivOn_of_tendsto_lintegral_enorm_sub (l := atTop)
    ((locallyIntegrable_cauchyTransform hfi).locallyIntegrableOn _)
    ((hDm.locallyIntegrable hp.le).locallyIntegrableOn _) hweak ?_ ?_
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm hp.le hT).congr fun n ↦
        eLpNorm_one_eq_lintegral_enorm ((((hTg n).continuous.aestronglyMeasurable).sub
          (locallyIntegrable_cauchyTransform hfi).aestronglyMeasurable).restrict))
      (fun _ ↦ zero_le) fun n ↦ lintegral_mono_set ball_subset_closedBall
  · exact (MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm hp.le
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hD (fun _ ↦ zero_le)
        fun n ↦ eLpNorm_mono_measure _ Measure.restrict_le_self)).congr fun n ↦
      eLpNorm_one_eq_lintegral_enorm
        ((hdTg n).aestronglyMeasurable.sub hDm.aestronglyMeasurable).restrict

/-- **`∂ (T f) = B f` and `bar∂ (T f) = f` weakly, for `Lᵖ` data.** For `1 < p < ∞` and `f ∈ Lᵖ(ℂ)`
vanishing outside a closed disc, the weak derivative of the Cauchy transform `T f` in the
direction `v`, on every open subset of the plane, is `v • B f + conj v • f`, where `B` is the
Beurling operator on `Lᵖ(ℂ)`. -/
theorem hasWeakLineDerivOn_cauchyTransform (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (hf : MemLp f p volume) (hs : support f ⊆ closedBall c (r : ℝ)) (Ω : Opens ℂ) (v : ℂ) :
    HasWeakLineDerivOn volume Ω (cauchyTransform f)
      (fun w ↦ v • beurlingLp p hp hp_top (hf.toLp f) w + conj v • f w) v := by
  -- Data in `Lᵖ` vanishing outside a disc is integrable.
  have hfi : Integrable f := by
    have : IsFiniteMeasure (volume.restrict (closedBall c (r : ℝ))) :=
      isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
    exact IntegrableOn.integrable_of_forall_notMem_eq_zero
      ((hf.restrict (closedBall c (r : ℝ))).integrable hp.le)
      fun y hy ↦ notMem_support.1 fun h ↦ hy (hs h)
  have hDm := memLp_smul_beurlingLp_add_smul hp hp_top hf v
  refine hasWeakLineDerivOn_iff_testFunction.2 ⟨inferInstance,
    (locallyIntegrable_cauchyTransform hfi).locallyIntegrableOn _,
    (hDm.locallyIntegrable hp.le).locallyIntegrableOn _, fun φ ↦ ?_⟩
  -- Every test function is supported in a disc about `c`.
  obtain ⟨R, hR, hφR⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_ball_lt 0 c
  have hR' : ((R.toNNReal : ℝ≥0) : ℝ) = R := Real.coe_toNNReal R hR.le
  exact (hasWeakLineDerivOn_cauchyTransform_ball hp hp_top hf hfi hs R.toNNReal v
    ).integral_lineDeriv_smul_eq_neg_integral_smul
      ⟨φ, φ.contDiff, φ.hasCompactSupport, by simpa [hR'] using hφR⟩

/-- **The weak real derivative of the Cauchy transform of `Lᵖ` data.** For `1 < p < ∞` and
`f ∈ Lᵖ(ℂ)` vanishing outside a closed disc, the Cauchy transform `T f` has weak real derivative
`v ↦ v • B f + conj v • f` on every open subset of the plane. -/
theorem hasWeakFDerivOn_cauchyTransform (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (hf : MemLp f p volume) (hs : support f ⊆ closedBall c (r : ℝ)) (Ω : Opens ℂ) :
    HasWeakFDerivOn volume Ω (cauchyTransform f) fun w ↦
      (ContinuousLinearMap.id ℝ ℂ).smulRight (beurlingLp p hp hp_top (hf.toLp f) w) +
        (conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.smulRight (f w) :=
  hasWeakFDerivOn_iff.2 fun v ↦ by
    simpa using hasWeakLineDerivOn_cauchyTransform hp hp_top hf hs Ω v

/-- The weak derivative `w ↦ (v ↦ v • B f (w) + conj v • f (w))` has `Lᵖ(ℂ)` norm at most
`(‖B‖ + 1) ‖f‖_{Lᵖ}`. -/
private theorem eLpNorm_smulRight_beurlingLp_add_smulRight_le (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) (hf : MemLp f p volume) :
    eLpNorm (fun w ↦
        (ContinuousLinearMap.id ℝ ℂ).smulRight (beurlingLp p hp hp_top (hf.toLp f) w) +
          (conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.smulRight (f w)) p volume ≤
      (‖beurlingLp (F := F) p hp hp_top‖ₑ + 1) * eLpNorm f p volume := by
  set u := beurlingLp p hp hp_top (hf.toLp f)
  -- With `L a = (v ↦ v • a)`, the derivative is `w ↦ L (u w) + L (f w) ∘ conj`.
  set L : F →L[ℝ] ℂ →L[ℝ] F := (ContinuousLinearMap.lsmul ℝ ℂ).flip
  have hL (a b : F) : (ContinuousLinearMap.id ℝ ℂ).smulRight a +
      (conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.smulRight b =
        L a + (L b).comp (conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap := by
    ext v
    simp [L]
  have hm : AEStronglyMeasurable (fun w ↦ (ContinuousLinearMap.id ℝ ℂ).smulRight (u w) +
      (conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.smulRight (f w)) volume := by
    simp only [hL]
    exact (L.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)).add
      ((L.continuous.clm_comp continuous_const).comp_aestronglyMeasurable hf.aestronglyMeasurable)
  -- Pointwise, `‖v • a + conj v • b‖ ≤ (‖a‖ + ‖b‖) ‖v‖`.
  have hb (w : ℂ) : ‖(ContinuousLinearMap.id ℝ ℂ).smulRight (u w) +
      (conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.smulRight (f w)‖ ≤ ‖u w‖ + ‖f w‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
    simp only [add_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearEquiv.coe_coe, conjCLE_apply]
    calc ‖v • u w + conj v • f w‖ ≤ ‖v • u w‖ + ‖conj v • f w‖ := norm_add_le _ _
      _ = (‖u w‖ + ‖f w‖) * ‖v‖ := by rw [norm_smul, norm_smul, RCLike.norm_conj]; ring
  calc _ ≤ eLpNorm (fun w ↦ ‖u w‖ + ‖f w‖) p volume := eLpNorm_mono_real hm hb
    _ ≤ eLpNorm (⇑u) p volume + eLpNorm f p volume := by
        refine (eLpNorm_add_le hp.le).trans_eq ?_
        rw [eLpNorm_norm _ (Lp.aestronglyMeasurable u), eLpNorm_norm _ hf.aestronglyMeasurable]
    _ ≤ ‖beurlingLp (F := F) p hp hp_top‖ₑ * eLpNorm f p volume + eLpNorm f p volume := by
        gcongr
        rw [← Lp.enorm_def, ← eLpNorm_congr_ae hf.coeFn_toLp, ← Lp.enorm_def]
        exact (beurlingLp (F := F) p hp hp_top).le_opENorm _
    _ = _ := by ring

/-- **The global derivative bound for the Cauchy transform of `Lᵖ` data.** For `1 < p < ∞` and
`f ∈ Lᵖ(ℂ)` vanishing outside a closed disc, every weak derivative `D` of `T f` on an open set `Ω`
satisfies `‖D‖_{Lᵖ(Ω)} ≤ (‖B‖ + 1) ‖f‖_{Lᵖ}`, uniformly in `Ω`; with `Ω = ℂ` this is the bound
on the whole plane. -/
theorem eLpNorm_le_of_hasWeakFDerivOn_cauchyTransform (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (hf : MemLp f p volume) (hs : support f ⊆ closedBall c (r : ℝ)) {Ω : Opens ℂ}
    {D : ℂ → ℂ →L[ℝ] F} (hD : HasWeakFDerivOn volume Ω (cauchyTransform f) D) :
    eLpNorm D p (volume.restrict Ω) ≤
      (‖beurlingLp (F := F) p hp hp_top‖ₑ + 1) * eLpNorm f p volume := by
  rw [eLpNorm_congr_ae (hD.ae_eq (hasWeakFDerivOn_cauchyTransform hp hp_top hf hs Ω))]
  exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
    (eLpNorm_smulRight_beurlingLp_add_smulRight_le hp hp_top hf)

/-- **`T : Lᵖ(D_r) → W^{1,p}(D_R)` is bounded.** For `1 < p < ∞` and `f ∈ Lᵖ(ℂ)` vanishing outside
the closed disc of radius `r` about `c`, the Cauchy transform `T f` and any weak derivative `D` of
it on an open subset `Ω` of the closed disc of radius `R` about `c` satisfy
`‖T f‖_{Lᵖ(Ω)} + ‖D‖_{Lᵖ(Ω)} ≤ (2 (r + R) + ‖B‖ + 1) ‖f‖_{Lᵖ}`. -/
theorem eLpNorm_cauchyTransform_add_eLpNorm_le_of_hasWeakFDerivOn (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) (hf : MemLp f p volume) (hs : support f ⊆ closedBall c (r : ℝ))
    {R : ℝ≥0} {Ω : Opens ℂ} (hΩ : (Ω : Set ℂ) ⊆ closedBall c (R : ℝ)) {D : ℂ → ℂ →L[ℝ] F}
    (hD : HasWeakFDerivOn volume Ω (cauchyTransform f) D) :
    eLpNorm (cauchyTransform f) p (volume.restrict Ω) + eLpNorm D p (volume.restrict Ω) ≤
      ((2 * (r + R) : ℝ≥0) + ‖beurlingLp (F := F) p hp hp_top‖ₑ + 1) * eLpNorm f p volume := by
  have hT : eLpNorm (cauchyTransform f) p (volume.restrict Ω) ≤
      (2 * (r + R) : ℝ≥0) * eLpNorm f p volume :=
    calc _ ≤ eLpNorm (cauchyTransform f) p (volume.restrict (closedBall c (R : ℝ))) :=
          eLpNorm_mono_measure _ (Measure.restrict_mono hΩ le_rfl)
      _ ≤ (2 * (r + R) : ℝ≥0) * eLpNorm f p (volume.restrict (closedBall c (r : ℝ))) :=
          eLpNorm_cauchyTransform_le hp.le hf.aestronglyMeasurable.restrict hs
      _ ≤ _ := by gcongr; exact Measure.restrict_le_self
  calc _ ≤ (2 * (r + R) : ℝ≥0) * eLpNorm f p volume +
        (‖beurlingLp (F := F) p hp hp_top‖ₑ + 1) * eLpNorm f p volume :=
        add_le_add hT (eLpNorm_le_of_hasWeakFDerivOn_cauchyTransform hp hp_top hf hs hD)
    _ = _ := by ring

/-- **The Cauchy transform of `Lᵖ` data is a local `W^{1,p}` map.** For `1 < p < ∞` and
`f ∈ Lᵖ(ℂ)` vanishing outside a closed disc, the Cauchy transform `T f` belongs to the local
Sobolev class `W^{1,p}_loc` of every subset `U` of the plane. -/
theorem memWkpLoc_one_cauchyTransform (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (hf : MemLp f p volume) (hs : support f ⊆ closedBall c (r : ℝ)) (U : Set ℂ) :
    MemWkpLoc p U 1 (cauchyTransform f) := by
  have hDm : MemLp (fun w ↦
      (ContinuousLinearMap.id ℝ ℂ).smulRight (beurlingLp p hp hp_top (hf.toLp f) w) +
        (conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.smulRight (f w)) p volume :=
    memLp_iff.2 <| (eLpNorm_smulRight_beurlingLp_add_smulRight_le hp hp_top hf).trans_lt
      (ENNReal.mul_lt_top (by simp) hf.eLpNorm_lt_top)
  refine memWkpLoc_succ_iff.2 ⟨memLpLoc_iff.2 fun K _ hK ↦ ?_, _,
    hasWeakFDerivOn_cauchyTransform hp hp_top hf hs _,
    memWkpLoc_zero_iff.2 <| memLpLoc_iff.2 fun K _ _ ↦ hDm.restrict K⟩
  -- On a compact set, `T f` is controlled by its `Lᵖ` bound on a disc containing it.
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 c
  have h := memLp_cauchyTransform (R := R.toNNReal) hp.le (hf.restrict _) hs
  rw [Real.coe_toNNReal R hR.le] at h
  exact h.mono_measure (Measure.restrict_mono hKR le_rfl)

end TauCeti
