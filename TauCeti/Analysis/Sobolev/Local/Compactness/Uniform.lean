/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Compactness
public import TauCeti.Analysis.Sobolev.Local.Morrey
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Analysis.Sobolev.Wkp.Chain

/-!
# Locally uniform convergence of local Rellich subsequences for `p > 2`

Let `Ω` be an open subset of `ℂ` and `2 < p ≤ ∞`. Local Rellich compactness
(`TauCeti.exists_subseq_memWkpLoc_tendsto_wkp`) extracts, from a sequence bounded in `W^{k+1,p}`
on every relatively compact open subset of `Ω`, a subsequence converging in `W^{k,p}` on every such
subset. This file upgrades that convergence: the precise representatives of the subsequence and
of its weak derivatives of orders `1` through `k` converge locally uniformly on `Ω`, that is,
uniformly on every compact subset of `Ω`. These are the representatives that are continuous by
Morrey's embedding (`TauCeti.MemWkpLoc.continuousOn_preciseRepresentative`), so this is `C^k`
convergence on compact subsets in the precise-representative form.

The argument is an interpolation between the `W^{1,p}` bound and the `Lᵖ` convergence. The local
Morrey sup bound `TauCeti.MemWkpLoc.exists_norm_preciseRepresentative_le` states that for
`w ∈ W^{1,p}_loc` with weak derivative `D` and `closedBall x (2 r) ⊆ Ω`,

`‖w*(x)‖ ≤ r^{-2/p} ‖w‖_{Lᵖ(B(x, r))} + C ‖D‖_{Lᵖ(B(x, 2 r))} r^{1 - 2/p}`.

Applied to differences of members of a sequence whose derivatives are bounded in `Lᵖ` on compact
sets, the second term is made small by choosing `r` small, and the first by `Lᵖ` convergence. This
gives `TauCeti.tendstoLocallyUniformlyOn_preciseRepresentative_of_tendsto_eLpNorm`: a sequence in
`W^{1,p}_loc` with derivatives bounded in `Lᵖ` on compact sets which converges in `Lᵖ` on compact
sets to some `g` converges locally uniformly to the precise representative of `g`. The limit `g`
is only assumed locally `Lᵖ`; this matters at the top order `k`, where the limit of the order-`k`
derivatives is not known to have a weak derivative.

## Main declarations

* `TauCeti.tendstoLocallyUniformlyOn_preciseRepresentative_of_tendsto_eLpNorm`: `Lᵖ` convergence
  on compact sets and `W^{1,p}` bounds give locally uniform convergence of precise
  representatives.
* `TauCeti.tendstoLocallyUniformlyOn_preciseRepresentative_of_tendsto_wkp` and
  `TauCeti.tendstoLocallyUniformlyOn_preciseRepresentative_iteratedGradient_of_tendsto_wkp`: for
  real functions, convergence in `W^{k,p}` together with bounds in `W^{k+1,p}` on relatively
  compact subsets gives locally uniform convergence of the precise representatives of the
  function and of its weak derivatives of orders `1` through `k`, recorded as iterated
  gradients.
* `TauCeti.exists_subseq_memWkpLoc_tendstoLocallyUniformlyOn`: local Rellich with `C^k`
  convergence on compact subsets, for real functions.
* `Module.Basis.tendstoLocallyUniformlyOn_preciseRepresentative_of_tendsto_wkp` and
  `Module.Basis.exists_subseq_memWkpLoc_tendstoLocallyUniformlyOn`: the vector-valued versions,
  through the coordinates in a basis.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Morrey's embedding and Rellich's theorem for local Sobolev spaces).
* L. C. Evans, *Partial Differential Equations*, §5.6.2 and §5.7.
-/

public section

noncomputable section

open Filter Metric Set MeasureTheory TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal Topology

namespace TauCeti

section Morrey

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {p : ℝ≥0∞} {Ω : Opens ℂ}

/-- **Locally uniform convergence from `Lᵖ` convergence and `W^{1,p}` bounds.** Let `2 < p ≤ ∞`.
Let `f m ∈ MemWkpLoc p Ω 1` have weak derivatives `D m` on `Ω` which are bounded in `Lᵖ(K)`
uniformly in `m` for every compact `K ⊆ Ω`, and suppose that `f m` converges in `Lᵖ(K)` to a
locally `Lᵖ` function `g` for every compact `K ⊆ Ω`. Then the precise representatives of the `f m`
converge to the precise representative of `g` locally uniformly on `Ω`; in particular the latter
is continuous on `Ω`. No derivative of `g` is assumed. -/
theorem tendstoLocallyUniformlyOn_preciseRepresentative_of_tendsto_eLpNorm (hp : 2 < p)
    {f : ℕ → ℂ → F} {D : ℕ → ℂ → ℂ →L[ℝ] F} {g : ℂ → F} (hf : ∀ m, MemWkpLoc p Ω 1 (f m))
    (hD : ∀ m, HasWeakFDerivOn volume Ω (f m) (D m))
    (hDbdd : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ M : ℝ≥0, ∀ m, eLpNorm (D m) p (volume.restrict K) ≤ M)
    (hg : MemLpLoc p Ω g)
    (hfg : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      Tendsto (fun m => eLpNorm (f m - g) p (volume.restrict K)) atTop (𝓝 0)) :
    TendstoLocallyUniformlyOn (fun m => preciseRepresentative volume (f m))
      (preciseRepresentative volume g) atTop Ω := by
  have hp1 : 1 ≤ p := one_le_two.trans hp.le
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  set α : ℝ := (((1 : ℝ≥0∞) - 2 / p).toNNReal : ℝ)
  have hα : 0 < α := by
    have h2p : 2 / p < 1 := by
      exact ENNReal.div_lt_of_lt_mul (by rwa [one_mul])
    simp only [α, NNReal.coe_pos, ENNReal.toNNReal_pos_iff]
    exact ⟨tsub_pos_of_lt h2p, tsub_le_self.trans_lt ENNReal.one_lt_top⟩
  obtain ⟨C, hC, hsup⟩ := MemWkpLoc.exists_norm_preciseRepresentative_le (F := F) hp
  -- The precise representatives are uniformly Cauchy on compact subsets of `Ω`.
  have hcauchy : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      UniformCauchySeqOn (fun m => preciseRepresentative volume (f m)) atTop K := by
    intro K hK hKΩ
    obtain ⟨R, hR, hRK⟩ := hK.exists_cthickening_subset_open Ω.isOpen hKΩ
    have hK' : IsCompact (cthickening R K) := hK.cthickening
    obtain ⟨M, hM⟩ := hDbdd _ hK' hRK
    have hmem : ∀ m, MemLp (f m) p (volume.restrict (cthickening R K)) := fun m =>
      memLpLoc_iff.1 (hf m).memLpLoc _ hRK hK'
    have hgK : MemLp g p (volume.restrict (cthickening R K)) := memLpLoc_iff.1 hg _ hRK hK'
    have hDmem : ∀ m, MemLp (D m) p (volume.restrict (cthickening R K)) := fun m =>
      memLpLoc_iff.1 ((hf m).memLpLoc_of_hasWeakFDerivOn (hD m)) _ hRK hK'
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    have hrα : Tendsto (fun r : ℝ => r ^ α) (𝓝[>] 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
      rw [Real.zero_rpow hα.ne'] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r ∧ r ≤ R / 2 ∧ C * (2 * M) * r ^ α < ε / 2 := by
      have e1 : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := eventually_mem_nhdsWithin
      have e2 : ∀ᶠ r : ℝ in 𝓝[>] 0, r ≤ R / 2 :=
        Filter.mem_of_superset (Ioo_mem_nhdsGT (half_pos hR))
          fun r (hr : r ∈ Ioo 0 (R / 2)) => (hr.2.le : r ≤ R / 2)
      refine e1.and (e2.and ?_)
      have h0 : Tendsto (fun r : ℝ => C * (2 * M) * r ^ α) (𝓝[>] 0) (𝓝 0) := by
        simpa using hrα.const_mul (C * (2 * M))
      exact h0.eventually (gt_mem_nhds (half_pos hε))
    obtain ⟨r, hr0, hrR, hrε⟩ := hev.exists
    set T := r ^ (-(2 / p.toReal))
    have hT : 0 < T := Real.rpow_pos_of_pos hr0 _
    have hconv : Tendsto (fun m => (eLpNorm (f m - g) p
        (volume.restrict (cthickening R K))).toReal) atTop (𝓝 0) := by
      simpa only [ENNReal.toReal_zero, Function.comp_def] using
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hfg _ hK' hRK)
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (hconv.eventually (gt_mem_nhds (show 0 < ε / (4 * (T + 1)) by positivity)))
    refine ⟨N, fun m hm n hn x hx => ?_⟩
    have hxr : closedBall x (2 * r) ⊆ cthickening R K :=
      (closedBall_subset_cthickening hx _).trans (cthickening_mono (by linarith) K)
    have hball : ball x (2 * r) ⊆ cthickening R K := ball_subset_closedBall.trans hxr
    have hball' : ball x r ⊆ cthickening R K :=
      (ball_subset_ball (by linarith)).trans hball
    have hb := hsup ((hf m).sub (hf n)) ((hD m).sub (hD n)) hr0 (hxr.trans hRK)
    rw [(hf m).eqOn_preciseRepresentative_sub hp (hf n) (hRK (self_subset_cthickening K hx))]
      at hb
    -- The `Lᵖ` term.
    have hfmg := ((hmem m).sub hgK).eLpNorm_ne_top
    have hfng := ((hmem n).sub hgK).eLpNorm_ne_top
    have h1 : (eLpNorm (f m - f n) p (volume.restrict (ball x r))).toReal ≤
        (eLpNorm (f m - g) p (volume.restrict (cthickening R K))).toReal +
          (eLpNorm (f n - g) p (volume.restrict (cthickening R K))).toReal := by
      rw [← ENNReal.toReal_add hfmg hfng]
      refine ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfmg, hfng⟩) ?_
      calc eLpNorm (f m - f n) p (volume.restrict (ball x r))
          ≤ eLpNorm (f m - f n) p (volume.restrict (cthickening R K)) :=
            eLpNorm_mono_measure _ (Measure.restrict_mono hball' le_rfl)
        _ = eLpNorm ((f m - g) - (f n - g)) p (volume.restrict (cthickening R K)) := by
            rw [sub_sub_sub_cancel_right]
        _ ≤ _ := eLpNorm_sub_le hp1
    -- The derivative term.
    have h2 : (eLpNorm (D m - D n) p (volume.restrict (ball x (2 * r)))).toReal ≤ 2 * M := by
      have hle : eLpNorm (D m - D n) p (volume.restrict (ball x (2 * r))) ≤ 2 * (M : ℝ≥0∞) :=
        calc _ ≤ eLpNorm (D m - D n) p (volume.restrict (cthickening R K)) :=
              eLpNorm_mono_measure _ (Measure.restrict_mono hball le_rfl)
          _ ≤ eLpNorm (D m) p (volume.restrict (cthickening R K)) +
              eLpNorm (D n) p (volume.restrict (cthickening R K)) :=
              eLpNorm_sub_le hp1
          _ ≤ M + M := add_le_add (hM m) (hM n)
          _ = 2 * (M : ℝ≥0∞) := (two_mul _).symm
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.coe_toReal] using
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.coe_ne_top) hle
    have hm' := hN m hm
    have hn' := hN n hn
    rw [dist_eq_norm]
    have hrα0 : 0 ≤ r ^ α := Real.rpow_nonneg hr0.le _
    calc _ ≤ T * (eLpNorm (f m - f n) p (volume.restrict (ball x r))).toReal +
          C * (eLpNorm (D m - D n) p (volume.restrict (ball x (2 * r)))).toReal * r ^ α := hb
      _ ≤ T * (ε / (4 * (T + 1)) + ε / (4 * (T + 1))) + C * (2 * M) * r ^ α := by
          gcongr
          exact h1.trans (add_le_add hm'.le hn'.le)
      _ < ε / 2 + ε / 2 := by
          refine add_lt_add_of_le_of_lt ?_ hrε
          rw [show T * (ε / (4 * (T + 1)) + ε / (4 * (T + 1))) = ε / 2 * (T / (T + 1)) by
            field_simp
            ring]
          exact mul_le_of_le_one_right (by positivity)
            ((div_le_one (by positivity)).2 (by linarith))
      _ = ε := add_halves ε
  -- The pointwise limit `h`, which is continuous on `Ω`.
  set h : ℂ → F := fun y => limUnder atTop fun m => preciseRepresentative volume (f m) y
  have hpt : ∀ y ∈ (Ω : Set ℂ),
      Tendsto (fun m => preciseRepresentative volume (f m) y) atTop (𝓝 (h y)) :=
    fun y hy => tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete
      ((hcauchy {y} isCompact_singleton (singleton_subset_iff.2 hy)).cauchySeq
        (mem_singleton y)))
  have hloc : TendstoLocallyUniformlyOn (fun m => preciseRepresentative volume (f m)) h atTop Ω :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact Ω.isOpen).2 fun K hKΩ hK =>
      (hcauchy K hK hKΩ).tendstoUniformlyOn_of_tendsto fun y hy => hpt y (hKΩ hy)
  have hcont : ContinuousOn h Ω :=
    hloc.continuousOn
      (Eventually.of_forall fun m => (hf m).continuousOn_preciseRepresentative hp).frequently
  -- The limit `h` agrees with `g` almost everywhere near every point of `Ω`.
  refine hloc.congr_right fun x hx => ?_
  obtain ⟨ρ, hρ, hρΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen x hx
  have hKΩ : closedBall x (ρ / 2) ⊆ Ω := (closedBall_subset_ball (half_lt_self hρ)).trans hρΩ
  obtain ⟨ψ, hψ, hψae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm hp0
    (hfg _ (isCompact_closedBall _ _) hKΩ)).exists_seq_tendsto_ae
  have hfae : ∀ᵐ y ∂volume.restrict (closedBall x (ρ / 2)),
      ∀ j, f (ψ j) y = preciseRepresentative volume (f (ψ j)) y :=
    ae_all_iff.2 fun j => ae_restrict_of_ae_restrict_of_subset hKΩ
      ((hf (ψ j)).memLpLoc.ae_eq_preciseRepresentative hp1)
  have hgh : g =ᵐ[volume.restrict (ball x (ρ / 2))] h := by
    refine ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall ?_
    filter_upwards [hψae, hfae, self_mem_ae_restrict measurableSet_closedBall]
      with y hy hy' hyK
    refine tendsto_nhds_unique hy ?_
    simpa only [hy', Function.comp_def] using (hpt y (hKΩ hyK)).comp hψ.tendsto_atTop
  exact (eqOn_preciseRepresentative_of_continuousOn isOpen_ball
    ((hg.locallyIntegrableOn hp1 Ω.isOpen.isLocallyClosed).mono_set
      (ball_subset_closedBall.trans hKΩ)) hgh (hcont.mono (ball_subset_closedBall.trans hKΩ))
    (mem_ball_self (half_pos hρ))).symm

end Morrey

section Rellich

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℂ} {k : ℕ}

/-- If `y m → w` in `W^{n,p}(W)` and the values of `y m` and `w` represent `f m` and `g` on `W`,
then `f m → g` in `Lᵖ(W)`. -/
private theorem tendsto_eLpNorm_sub_of_tendsto_wkp {W : Opens ℂ} {n : ℕ}
    {y : ℕ → Wkp volume W p n} {w : Wkp volume W p n} {f : ℕ → ℂ → ℝ} {g : ℂ → ℝ}
    (hyw : Tendsto y atTop (𝓝 w)) (hy : ∀ m, Wkp.value n (y m) =ᵐ[volume.restrict W] f m)
    (hw : Wkp.value n w =ᵐ[volume.restrict W] g) :
    Tendsto (fun m => eLpNorm (f m - g) p (volume.restrict W)) atTop (𝓝 0) := by
  refine ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1
    (((Wkp.valueL n).continuous.tendsto w).comp hyw)).congr fun m => eLpNorm_congr_ae ?_
  simpa only [Function.comp_apply, Wkp.valueL_apply] using (hy m).sub hw

/-- Every compact subset of an open `Ω ⊆ ℂ` lies in an open `W` whose closure is compact and
contained in `Ω`, and then `W ≤ Ω`. -/
private theorem exists_opens_of_isCompact {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ W : Opens ℂ, K ⊆ W ∧ IsCompact (closure (W : Set ℂ)) ∧ closure (W : Set ℂ) ⊆ Ω ∧
      W ≤ Ω := by
  obtain ⟨W, hKW, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hK hKΩ
  exact ⟨W, hKW, hWc, hWΩ, SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ)⟩

/-- **Locally uniform convergence of local Rellich limits.** Let `2 < p ≤ ∞`. Let `u m` be real
functions bounded in `W^{k+1,p}` on every relatively compact open subset `W` of `Ω`, as in
`TauCeti.exists_subseq_memWkpLoc_tendsto_wkp`, which converge in `W^{k,p}` on every such `W` to
`v ∈ MemWkpLoc p Ω k`: representatives of `u m` in `Wkp volume W p k` converge to the
representative of `v`. Then the precise representatives of the `u m` converge to the precise
representative of `v` locally uniformly on `Ω`. -/
theorem tendstoLocallyUniformlyOn_preciseRepresentative_of_tendsto_wkp (hp : 2 < p)
    {u : ℕ → ℂ → ℝ} {v : ℂ → ℝ}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ R : ℝ, ∀ m, ∃ y : Wkp volume W p (k + 1),
        ‖y‖ ≤ R ∧ Wkp.value (k + 1) y =ᵐ[volume.restrict W] u m)
    (hv : MemWkpLoc p Ω k v)
    (hlim : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∀ (y : ℕ → Wkp volume W p k) (w : Wkp volume W p k),
        (∀ m, Wkp.value k (y m) =ᵐ[volume.restrict W] u m) →
        Wkp.value k w =ᵐ[volume.restrict W] v → Tendsto y atTop (𝓝 w)) :
    TendstoLocallyUniformlyOn (fun m => preciseRepresentative volume (u m))
      (preciseRepresentative volume v) atTop Ω := by
  have hum : ∀ m, MemWkpLoc p Ω (k + 1) (u m) := fun m =>
    memWkpLoc_of_forall_wkp fun W hWc hWΩ => by
      obtain ⟨R, hR⟩ := hu W hWc hWΩ
      obtain ⟨y, -, hy⟩ := hR m
      exact ⟨y, hy⟩
  choose _ G hG0 hG _ using fun m => (memWkpLoc_succ_iff_exists_iteratedGradient k).1 (hum m)
  refine tendstoLocallyUniformlyOn_preciseRepresentative_of_tendsto_eLpNorm hp
    (D := fun m z => innerSL ℝ (G m 0 z)) (fun m => (hum m).of_le (by omega)) hG0
    (fun K hK hKΩ => ?_) hv.memLpLoc (fun K hK hKΩ => ?_)
  · obtain ⟨W, hKW, hWc, hWΩ, hWle⟩ := exists_opens_of_isCompact hK hKΩ
    obtain ⟨R, hR⟩ := hu W hWc hWΩ
    refine ⟨R.toNNReal, fun m => ?_⟩
    obtain ⟨y, hyR, hy⟩ := hR m
    obtain ⟨-, hb⟩ := Wkp.iteratedGradient_ae_eq_and_eLpNorm_le_of_chain k y hy
      ((hG0 m).mono hWle) fun i hi => (hG m i hi).mono hWle
    calc eLpNorm (fun z => innerSL ℝ (G m 0 z)) p (volume.restrict K)
        ≤ eLpNorm (fun z => innerSL ℝ (G m 0 z)) p (volume.restrict W) :=
          eLpNorm_mono_measure _ (Measure.restrict_mono hKW le_rfl)
      _ = eLpNorm (G m 0) p (volume.restrict W) :=
          have hmeas := (hb 0 (Nat.zero_le _)).1.aestronglyMeasurable
          eLpNorm_congr_norm_ae ((innerSL ℝ).continuous.comp_aestronglyMeasurable hmeas) hmeas
            (Eventually.of_forall fun z => innerSL_apply_norm _ _)
      _ ≤ ENNReal.ofReal ‖y‖ := (hb 0 (Nat.zero_le _)).2
      _ ≤ R.toNNReal := ENNReal.ofReal_le_ofReal hyR
  · obtain ⟨W, hKW, hWc, hWΩ, hWle⟩ := exists_opens_of_isCompact hK hKΩ
    obtain ⟨R, hR⟩ := hu W hWc hWΩ
    choose V _ hV using hR
    obtain ⟨w, hw⟩ := hv.exists_wkp hWc hWΩ
    have hy : ∀ m, Wkp.value k (Wkp.lowerOrder k (V m)) =ᵐ[volume.restrict W] u m := fun m => by
      rw [← Wkp.value_succ]
      exact hV m
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_eLpNorm_sub_of_tendsto_wkp (hlim W hWc hWΩ _ w hy hw) hy hw) (fun _ => bot_le)
      fun m => eLpNorm_mono_measure _ (Measure.restrict_mono hKW le_rfl)

/-- **Locally uniform convergence of the iterated weak gradients of local Rellich limits.** Let
`2 < p ≤ ∞` and let `u m` and `v` be as in
`TauCeti.tendstoLocallyUniformlyOn_preciseRepresentative_of_tendsto_wkp`. Let `G m` be a chain of
iterated weak gradients of `u m` on `Ω` through order `k + 1`, and `H` one of `v` through order
`k`, as in `TauCeti.memWkpLoc_succ_iff_exists_iteratedGradient`. Then for every `i < k` the
precise representatives of the `G m i` converge to the precise representative of `H i` locally
uniformly on `Ω`. Together with the convergence of the values this is `C^k` convergence on compact
subsets of `Ω`; the chains are unique almost everywhere, so the statement does not depend on
their choice. -/
theorem tendstoLocallyUniformlyOn_preciseRepresentative_iteratedGradient_of_tendsto_wkp
    (hp : 2 < p) {u : ℕ → ℂ → ℝ} {v : ℂ → ℝ}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ R : ℝ, ∀ m, ∃ y : Wkp volume W p (k + 1),
        ‖y‖ ≤ R ∧ Wkp.value (k + 1) y =ᵐ[volume.restrict W] u m)
    (hv : MemWkpLoc p Ω k v)
    (hlim : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∀ (y : ℕ → Wkp volume W p k) (w : Wkp volume W p k),
        (∀ m, Wkp.value k (y m) =ᵐ[volume.restrict W] u m) →
        Wkp.value k w =ᵐ[volume.restrict W] v → Tendsto y atTop (𝓝 w))
    {G : ℕ → (i : ℕ) → ℂ → IteratedGradient ℂ i} {H : (i : ℕ) → ℂ → IteratedGradient ℂ i}
    (hG0 : ∀ m, HasWeakFDerivOn volume Ω (u m) fun z => innerSL ℝ (G m 0 z))
    (hG : ∀ m, ∀ i < k, HasWeakFDerivOn volume Ω (G m i) (G m (i + 1)))
    (hH0 : 0 < k → HasWeakFDerivOn volume Ω v fun z => innerSL ℝ (H 0 z))
    (hH : ∀ i, i + 1 < k → HasWeakFDerivOn volume Ω (H i) (H (i + 1))) {i : ℕ} (hi : i < k) :
    TendstoLocallyUniformlyOn (fun m => preciseRepresentative volume (G m i))
      (preciseRepresentative volume (H i)) atTop Ω := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  -- The fields of the chains `G m` are in `Lᵖ` on relatively compact subsets, with uniform bounds.
  have hfield : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ R : ℝ, ∀ m, ∀ j ≤ n + 1, MemLp (G m j) p (volume.restrict W) ∧
        eLpNorm (G m j) p (volume.restrict W) ≤ ENNReal.ofReal R := by
    intro W hWc hWΩ
    have hWle : W ≤ Ω := SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ)
    obtain ⟨R, hR⟩ := hu W hWc hWΩ
    refine ⟨R, fun m j hj => ?_⟩
    obtain ⟨y, hyR, hy⟩ := hR m
    obtain ⟨-, hb⟩ := Wkp.iteratedGradient_ae_eq_and_eLpNorm_le_of_chain (n + 1) y hy
      ((hG0 m).mono hWle) fun i hi => (hG m i hi).mono hWle
    exact ⟨(hb j hj).1, (hb j hj).2.trans (ENNReal.ofReal_le_ofReal hyR)⟩
  have hGloc : ∀ m, ∀ j ≤ n + 1, MemLpLoc p Ω (G m j) := fun m j hj =>
    memLpLoc_of_forall_opens fun W hWc hWΩ => by
      obtain ⟨R, hR⟩ := hfield W hWc hWΩ
      exact ⟨G m j, (hR m j hj).1, EventuallyEq.rfl⟩
  have hHloc : MemLpLoc p Ω (H i) := memLpLoc_of_forall_opens fun W hWc hWΩ => by
    have hWle : W ≤ Ω := SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ)
    obtain ⟨w, hw⟩ := hv.exists_wkp hWc hWΩ
    obtain ⟨-, hb⟩ := Wkp.iteratedGradient_ae_eq_and_eLpNorm_le_of_chain n w hw
      ((hH0 (by omega)).mono hWle) fun j hj => (hH j (by omega)).mono hWle
    exact ⟨H i, (hb i (by omega)).1, EventuallyEq.rfl⟩
  refine tendstoLocallyUniformlyOn_preciseRepresentative_of_tendsto_eLpNorm hp
    (D := fun m => G m (i + 1))
    (fun m => memWkpLoc_succ_iff_of_isOpen.2 ⟨hGloc m i (by omega), G m (i + 1), hG m i hi,
      memWkpLoc_zero_iff.2 (hGloc m (i + 1) (by omega))⟩)
    (fun m => hG m i hi) (fun K hK hKΩ => ?_) hHloc (fun K hK hKΩ => ?_)
  · obtain ⟨W, hKW, hWc, hWΩ, -⟩ := exists_opens_of_isCompact hK hKΩ
    obtain ⟨R, hR⟩ := hfield W hWc hWΩ
    exact ⟨R.toNNReal, fun m => (eLpNorm_mono_measure _ (Measure.restrict_mono hKW le_rfl)).trans
      (hR m (i + 1) (by omega)).2⟩
  · obtain ⟨W, hKW, hWc, hWΩ, hWle⟩ := exists_opens_of_isCompact hK hKΩ
    obtain ⟨R, hR⟩ := hu W hWc hWΩ
    choose V _ hV using hR
    obtain ⟨w, hw⟩ := hv.exists_wkp hWc hWΩ
    set y : ℕ → Wkp volume W p (n + 1) := fun m => Wkp.lowerOrder (n + 1) (V m)
    have hy : ∀ m, Wkp.value (n + 1) (y m) =ᵐ[volume.restrict W] u m := fun m => by
      rw [← Wkp.value_succ]
      exact hV m
    have hyw : Tendsto (fun m => ‖y m - w‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 (hlim W hWc hWΩ y w hy hw)
    -- The chain `G m - H` of `u m - v` bounds the difference of the fields by `‖y m - w‖`.
    have hle : ∀ m, eLpNorm (G m i - H i) p (volume.restrict W) ≤ ENNReal.ofReal ‖y m - w‖ := by
      intro m
      have hval : Wkp.value (n + 1) (y m - w) =ᵐ[volume.restrict W] u m - v := by
        rw [← Wkp.valueL_apply, map_sub, Wkp.valueL_apply, Wkp.valueL_apply]
        filter_upwards [Lp.coeFn_sub (Wkp.value (n + 1) (y m)) (Wkp.value (n + 1) w), hy m, hw]
          with z hz hyz hwz
        rw [hz, Pi.sub_apply, Pi.sub_apply, hyz, hwz]
      have h0 : HasWeakFDerivOn volume W (u m - v)
          fun z => innerSL ℝ ((fun j => G m j - H j) 0 z) := by
        have heq : (fun z => innerSL ℝ ((fun j => G m j - H j) 0 z)) =
            (fun z => innerSL ℝ (G m 0 z)) - fun z => innerSL ℝ (H 0 z) :=
          funext fun z => by simp only [Pi.sub_apply, map_sub]
        rw [heq]
        exact ((hG0 m).sub (hH0 (by omega))).mono hWle
      obtain ⟨-, hb⟩ := Wkp.iteratedGradient_ae_eq_and_eLpNorm_le_of_chain n (y m - w) hval h0
        fun j hj => ((hG m j (by omega)).sub (hH j (by omega))).mono hWle
      exact (hb i (by omega)).2
    have h0 : Tendsto (fun m => ENNReal.ofReal ‖y m - w‖) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hyw
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => bot_le)
      fun m => (eLpNorm_mono_measure _ (Measure.restrict_mono hKW le_rfl)).trans (hle m)

/-- **Local Rellich compactness with `C^k` convergence on compact sets.** Let `2 < p ≤ ∞` and let
`u m` be real functions bounded in `W^{k+1,p}` on every relatively compact open subset of `Ω`, as
in `TauCeti.exists_subseq_memWkpLoc_tendsto_wkp`. Then there are a subsequence `u (φ m)` and a
limit `v ∈ MemWkpLoc p Ω k` such that the precise representatives of the `u (φ m)` converge to that
of `v` locally uniformly on `Ω`, and so do those of the fields `G m i`, `i < k`, which record the
weak derivatives of orders `1` through `k`, for any chains `G m` of `u (φ m)` and `H` of `v` as in
`TauCeti.memWkpLoc_succ_iff_exists_iteratedGradient`. -/
theorem exists_subseq_memWkpLoc_tendstoLocallyUniformlyOn (hp : 2 < p) {u : ℕ → ℂ → ℝ}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ R : ℝ, ∀ m, ∃ y : Wkp volume W p (k + 1),
        ‖y‖ ≤ R ∧ Wkp.value (k + 1) y =ᵐ[volume.restrict W] u m) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → ℝ, MemWkpLoc p Ω k v ∧
      TendstoLocallyUniformlyOn (fun m => preciseRepresentative volume (u (φ m)))
        (preciseRepresentative volume v) atTop Ω ∧
      ∀ (G : ℕ → (i : ℕ) → ℂ → IteratedGradient ℂ i) (H : (i : ℕ) → ℂ → IteratedGradient ℂ i),
        (∀ m, HasWeakFDerivOn volume Ω (u (φ m)) fun z => innerSL ℝ (G m 0 z)) →
        (∀ m, ∀ i < k, HasWeakFDerivOn volume Ω (G m i) (G m (i + 1))) →
        (0 < k → HasWeakFDerivOn volume Ω v fun z => innerSL ℝ (H 0 z)) →
        (∀ i, i + 1 < k → HasWeakFDerivOn volume Ω (H i) (H (i + 1))) →
        ∀ i < k, TendstoLocallyUniformlyOn (fun m => preciseRepresentative volume (G m i))
          (preciseRepresentative volume (H i)) atTop Ω := by
  obtain ⟨φ, hφ, v, hv, hlim⟩ := exists_subseq_memWkpLoc_tendsto_wkp hu
  have hu' : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ R : ℝ, ∀ m, ∃ y : Wkp volume W p (k + 1),
        ‖y‖ ≤ R ∧ Wkp.value (k + 1) y =ᵐ[volume.restrict W] u (φ m) := fun W hWc hWΩ => by
    obtain ⟨R, hR⟩ := hu W hWc hWΩ
    exact ⟨R, fun m => hR (φ m)⟩
  exact ⟨φ, hφ, v, hv, tendstoLocallyUniformlyOn_preciseRepresentative_of_tendsto_wkp hp hu' hv
    hlim, fun G H hG0 hG hH0 hH i hi =>
      tendstoLocallyUniformlyOn_preciseRepresentative_iteratedGradient_of_tendsto_wkp hp hu' hv
        hlim hG0 hG hH0 hH hi⟩

end Rellich

section Basis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*}
  {p : ℝ≥0∞} {Ω : Opens ℂ}

/-- **Locally uniform convergence of vector-valued local Rellich limits.** Let `F` be a
finite-dimensional real vector space with basis `b`, let `2 < p ≤ ∞`, and let `u m : ℂ → F` have
coordinates bounded in `W^{k+1,p}` on every relatively compact open subset `W` of `Ω` which
converge in `W^{k,p}` on every such `W` to the coordinates of `v ∈ MemWkpLoc p Ω k`, as produced by
`Module.Basis.exists_subseq_memWkpLoc_tendsto_wkp`. Then the precise representatives of the `u m`
converge to that of `v` locally uniformly on `Ω`. The iterated weak gradients converge coordinate
by coordinate, by
`TauCeti.tendstoLocallyUniformlyOn_preciseRepresentative_iteratedGradient_of_tendsto_wkp`. -/
theorem _root_.Module.Basis.tendstoLocallyUniformlyOn_preciseRepresentative_of_tendsto_wkp
    [Finite ι] [Fact (1 ≤ p)] {k : ℕ} (b : Module.Basis ι ℝ F) (hp : 2 < p) {u : ℕ → ℂ → F}
    {v : ℂ → F}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∀ i, ∃ R : ℝ, ∀ m, ∃ y : Wkp volume W p (k + 1),
        ‖y‖ ≤ R ∧ Wkp.value (k + 1) y =ᵐ[volume.restrict W] fun z => b.repr (u m z) i)
    (hv : MemWkpLoc p Ω k v)
    (hlim : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∀ i (y : ℕ → Wkp volume W p k) (w : Wkp volume W p k),
        (∀ m, Wkp.value k (y m) =ᵐ[volume.restrict W] fun z => b.repr (u m z) i) →
        Wkp.value k w =ᵐ[volume.restrict W] (fun z => b.repr (v z) i) →
        Tendsto y atTop (𝓝 w)) :
    TendstoLocallyUniformlyOn (fun m => preciseRepresentative volume (u m))
      (preciseRepresentative volume v) atTop Ω := by
  have := Fintype.ofFinite ι
  have : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  have hp1 : 1 ≤ p := one_le_two.trans hp.le
  have hc : ∀ i, TendstoLocallyUniformlyOn
      (fun m => preciseRepresentative volume fun z => b.repr (u m z) i)
      (preciseRepresentative volume fun z => b.repr (v z) i) atTop Ω := fun i =>
    TauCeti.tendstoLocallyUniformlyOn_preciseRepresentative_of_tendsto_wkp hp
      (fun W hWc hWΩ => hu W hWc hWΩ i) (b.memWkpLoc_iff.1 hv i)
      fun W hWc hWΩ => hlim W hWc hWΩ i
  have hum : ∀ m i, MemWkpLoc p Ω 1 fun z => b.repr (u m z) i := fun m i =>
    (memWkpLoc_of_forall_wkp fun W hWc hWΩ => by
      obtain ⟨R, hR⟩ := hu W hWc hWΩ i
      obtain ⟨y, -, hy⟩ := hR m
      exact ⟨y, hy⟩).of_le (by omega)
  have hcv : ∀ i, ContinuousOn (preciseRepresentative volume fun z => b.repr (v z) i) Ω :=
    fun i => (hc i).continuousOn
      (Eventually.of_forall fun m => (hum m i).continuousOn_preciseRepresentative hp).frequently
  -- Combine the coordinates.
  have hterm : ∀ i, TendstoLocallyUniformlyOn
      (fun m z => preciseRepresentative volume (fun w => b.repr (u m w) i) z • b i)
      (fun z => preciseRepresentative volume (fun w => b.repr (v w) i) z • b i) atTop Ω :=
    fun i => by
      simpa [Function.comp_def] using
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (b i)).uniformContinuous
          |>.comp_tendstoLocallyUniformlyOn (hc i)
  have hsum : ∀ s : Finset ι, TendstoLocallyUniformlyOn
      (fun m z => ∑ i ∈ s, preciseRepresentative volume (fun w => b.repr (u m w) i) z • b i)
      (fun z => ∑ i ∈ s, preciseRepresentative volume (fun w => b.repr (v w) i) z • b i)
      atTop Ω := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using
        (tendsto_const_nhds (x := (0 : F)) (f := atTop (α := ℕ))).tendstoUniformlyOn_const
          (Ω : Set ℂ) |>.tendstoLocallyUniformlyOn
    | insert a s ha ih =>
      simpa only [Finset.sum_insert ha, Pi.add_def] using (hterm a).add ih
  refine ((hsum Finset.univ).congr fun m => ?_).congr_right ?_
  · exact (b.eqOn_preciseRepresentative_sum_repr hp1 (b.memWkpLoc_iff.2 (hum m)).memLpLoc fun i =>
      (hum m i).continuousOn_preciseRepresentative hp).symm
  · exact (b.eqOn_preciseRepresentative_sum_repr hp1 hv.memLpLoc hcv).symm

/-- **Local Rellich compactness with `C^k` convergence on compact sets, vector-valued version.**
Let `F` be a finite-dimensional real vector space with basis `b`, let `2 < p ≤ ∞`, and let
`u m : ℂ → F` have coordinates bounded in `W^{k+1,p}` on every relatively compact open subset of
`Ω`. Then there are a subsequence `u (φ m)` and a limit `v ∈ MemWkpLoc p Ω k` such that the precise
representatives of the `u (φ m)` converge to that of `v` locally uniformly on `Ω`, and, coordinate
by coordinate, so do those of the fields `G m j`, `j < k`, recording the weak derivatives of orders
`1` through `k`, for any chains
`G m` of the coordinates of `u (φ m)` and `H` of the coordinate of `v`. -/
theorem _root_.Module.Basis.exists_subseq_memWkpLoc_tendstoLocallyUniformlyOn [Finite ι]
    [Fact (1 ≤ p)]
    {k : ℕ} (b : Module.Basis ι ℝ F) (hp : 2 < p) {u : ℕ → ℂ → F}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∀ i, ∃ R : ℝ, ∀ m, ∃ y : Wkp volume W p (k + 1),
        ‖y‖ ≤ R ∧ Wkp.value (k + 1) y =ᵐ[volume.restrict W] fun z => b.repr (u m z) i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → F, MemWkpLoc p Ω k v ∧
      TendstoLocallyUniformlyOn (fun m => preciseRepresentative volume (u (φ m)))
        (preciseRepresentative volume v) atTop Ω ∧
      ∀ i (G : ℕ → (j : ℕ) → ℂ → IteratedGradient ℂ j) (H : (j : ℕ) → ℂ → IteratedGradient ℂ j),
        (∀ m, HasWeakFDerivOn volume Ω (fun z => b.repr (u (φ m) z) i)
          fun z => innerSL ℝ (G m 0 z)) →
        (∀ m, ∀ j < k, HasWeakFDerivOn volume Ω (G m j) (G m (j + 1))) →
        (0 < k → HasWeakFDerivOn volume Ω (fun z => b.repr (v z) i)
          fun z => innerSL ℝ (H 0 z)) →
        (∀ j, j + 1 < k → HasWeakFDerivOn volume Ω (H j) (H (j + 1))) →
        ∀ j < k, TendstoLocallyUniformlyOn (fun m => preciseRepresentative volume (G m j))
          (preciseRepresentative volume (H j)) atTop Ω := by
  obtain ⟨φ, hφ, v, hv, hlim⟩ := b.exists_subseq_memWkpLoc_tendsto_wkp hu
  have hu' : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∀ i, ∃ R : ℝ, ∀ m, ∃ y : Wkp volume W p (k + 1),
        ‖y‖ ≤ R ∧ Wkp.value (k + 1) y =ᵐ[volume.restrict W] fun z => b.repr (u (φ m) z) i :=
    fun W hWc hWΩ i => by
      obtain ⟨R, hR⟩ := hu W hWc hWΩ i
      exact ⟨R, fun m => hR (φ m)⟩
  exact ⟨φ, hφ, v, hv, b.tendstoLocallyUniformlyOn_preciseRepresentative_of_tendsto_wkp hp hu' hv
    hlim, fun i G H hG0 hG hH0 hH j hj =>
      tendstoLocallyUniformlyOn_preciseRepresentative_iteratedGradient_of_tendsto_wkp hp
        (fun W hWc hWΩ => hu' W hWc hWΩ i) (b.memWkpLoc_iff.1 hv i)
        (fun W hWc hWΩ => hlim W hWc hWΩ i) hG0 hG hH0 hH hj⟩

end Basis

end TauCeti
