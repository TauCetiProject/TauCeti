/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.CompactSupport
public import TauCeti.Analysis.Sobolev.W1p.LevelSet

public import TauCeti.MeasureTheory.Function.UnifTight
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Continuity of positive truncation

For `1 ≤ p < ∞` and `0 ≤ k`, the truncation `u ↦ (u - k)⁺` is continuous in
`W^{1,p}(Ω)` and preserves `W^{1,p}_0(Ω)`. Neither assertion requires boundedness or
boundary regularity of `Ω`.

Positive parts of functions with zero boundary values are therefore admissible Sobolev test
functions. In particular, this applies to the difference of two functions with the same
Dirichlet boundary data, as needed in weak comparison arguments.

* `TauCeti.W1p.continuous_posPartAbove`: continuity in the full Sobolev norm.
* `TauCeti.W1p.posPartAbove_mem_w1p0Submodule`: preservation of the homogeneous Dirichlet
  condition.
* `TauCeti.W1p.posPart_sub_mem_w1p0Submodule`: lowering `u ∈ W^{1,p}_0(Ω)` by a nonnegative
  `v ∈ W^{1,p}(Ω)` keeps `(u - v)⁺` in `W^{1,p}_0(Ω)`.
* `TauCeti.W1p.value_posPart_sub_posPart_sub_smul_ae`,
  `TauCeti.W1p.gradient_posPart_sub_posPart_sub_smul_eq_zero_ae`: the truncation
  `min(u⁺, c v) = u⁺ - (u⁺ - c v)⁺` and the vanishing of its gradient where `u ≤ 0`.
* `TauCeti.W1p.mem_w1p0Submodule_of_nonneg_of_le`: a function between `0` and an element of
  `W^{1,p}_0(Ω)` lies in `W^{1,p}_0(Ω)`.
* `TauCeti.W1p.posPartAbove_mem_w1p0Submodule_of_le`: a boundary bound `u ≤ k` on `∂Ω`, expressed
  by `(u - k)⁺ ∈ W^{1,p}_0(Ω)`, persists at every higher level.
* `TauCeti.W1p.contDiffComp_mem_w1p0Submodule_of_nonneg`: a Lipschitz `C¹` function `F` with
  `0 ≤ F s ≤ C s` for `s ≥ 0` maps a nonnegative `v ∈ W^{1,p}_0(Ω)` into `W^{1,p}_0(Ω)`.
* `TauCeti.W1p.exists_mem_w1p0Submodule_value_eq_sq_div`: the truncated squares
  `v² / (1 + t v²)` of a nonnegative `v ∈ W^{1,p}_0(Ω)` lie in `W^{1,p}_0(Ω)`.
* `TauCeti.W1p.norm_posPartAbove_le`: truncation does not increase the Sobolev norm.
* `TauCeti.W1p0.posPart`: the positive part as a map of `W^{1,p}_0(Ω)` to itself, with its value
  `TauCeti.W1p0.valueL_posPart`, continuity `TauCeti.W1p0.continuous_posPart` and norm bound
  `TauCeti.W1p0.norm_posPart_le`.

The corresponding positive-part results are the special case `k = 0`.
-/

public section

noncomputable section

namespace TauCeti

open Filter _root_.MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E]

private def posPartJet (z : Sobolev1Jet E) : Sobolev1Jet E :=
  if 0 < z.fst then z else 0

private theorem norm_posPartJet_le (z : Sobolev1Jet E) :
    ‖posPartJet z‖ ≤ ‖z‖ := by
  by_cases hz : 0 < z.fst <;> simp [posPartJet, hz]

private theorem continuousAt_posPartJet {z : Sobolev1Jet E}
    (hzero : z.fst = 0 → z = 0) : ContinuousAt posPartJet z := by
  rcases lt_trichotomy 0 z.fst with hpos | heq | hneg
  · have he : ∀ᶠ w in 𝓝 z, 0 < w.fst :=
      ((WithLp.continuous_fst 2 ℝ E).tendsto z).eventually (eventually_gt_nhds hpos)
    rw [ContinuousAt, posPartJet, ite_eq_left hpos]
    exact tendsto_id.congr' (he.mono fun w hw ↦ by simp [posPartJet, hw])
  · have hz := hzero heq.symm
    subst z
    simpa only [ContinuousAt, posPartJet, WithLp.zero_fst, lt_self_iff_false,
      ite_false] using squeeze_zero_norm norm_posPartJet_le tendsto_norm_zero
  · have he : ∀ᶠ w in 𝓝 z, w.fst < 0 :=
      ((WithLp.continuous_fst 2 ℝ E).tendsto z).eventually (eventually_lt_nhds hneg)
    rw [ContinuousAt, posPartJet, ite_eq_right (not_lt_of_gt hneg)]
    exact tendsto_const_nhds.congr' (he.mono fun w hw ↦ by
      simp [posPartJet, not_lt_of_gt hw])

private def posPartAboveJet (k : ℝ) (z : Sobolev1Jet E) : Sobolev1Jet E :=
  posPartJet (z - WithLp.toLp 2 (k, 0))

private theorem norm_posPartAboveJet_le {k : ℝ} (hk : 0 ≤ k) (z : Sobolev1Jet E) :
    ‖posPartAboveJet k z‖ ≤ ‖z‖ := by
  by_cases hz : k < z.fst
  · simp only [posPartAboveJet, posPartJet, WithLp.sub_fst, WithLp.toLp_fst,
      sub_pos.mpr hz, ite_true]
    rw [WithLp.prod_norm_eq_of_L2, WithLp.prod_norm_eq_of_L2]
    simp only [WithLp.sub_fst, WithLp.sub_snd, WithLp.toLp_fst, WithLp.toLp_snd,
      sub_zero, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hz.le),
      abs_of_nonneg (hk.trans hz.le)]
    gcongr
    exact sub_le_self _ hk
  · simp [posPartAboveJet, posPartJet, sub_pos, hz]

private theorem continuousAt_posPartAboveJet (k : ℝ) {z : Sobolev1Jet E}
    (hzero : z.fst = k → z.snd = 0) : ContinuousAt (posPartAboveJet k) z := by
  have hz : (z - WithLp.toLp 2 (k, 0)).fst = 0 → z - WithLp.toLp 2 (k, 0) = 0 := by
    intro hx
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · simpa only [WithLp.ofLp_fst, WithLp.zero_fst] using hx
    · simp only [WithLp.ofLp_snd, WithLp.sub_snd, WithLp.toLp_snd, sub_zero,
        WithLp.zero_snd]
      exact hzero (sub_eq_zero.mp (by simpa only [WithLp.sub_fst, WithLp.toLp_fst] using hx))
  have hshift : ContinuousAt (fun w : Sobolev1Jet E ↦ w - WithLp.toLp 2 (k, 0)) z :=
    continuousAt_id.sub continuousAt_const
  exact (continuousAt_posPartJet hz).comp
    (f := fun w : Sobolev1Jet E ↦ w - WithLp.toLp 2 (k, 0)) hshift

variable [MeasurableSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

private theorem posPartAbove_coe_ae (hp : p ≠ ∞) {k : ℝ} (hk : 0 ≤ k)
    (u : W1p mu Omega p) :
    ⇑(W1p.posPartAbove hp hk u : Sobolev1JetLp mu Omega p) =ᵐ[mu.restrict Omega]
      fun x ↦ posPartAboveJet k ((u : Sobolev1JetLp mu Omega p) x) := by
  filter_upwards [W1p.value_apply_ae (W1p.posPartAbove hp hk u),
    W1p.gradient_apply_ae (W1p.posPartAbove hp hk u), W1p.value_apply_ae u,
    W1p.gradient_apply_ae u, W1p.value_posPartAbove_ae hp hk u,
    W1p.gradient_posPartAbove_ae hp hk u] with x hv hg huv hug hvp hgp
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · simp only [WithLp.ofLp_fst]
    rw [← hv, hvp]
    by_cases hx : k < W1p.value u x
    · simp [posPartAboveJet, posPartJet, ← huv, sub_pos, hx,
        max_eq_left (sub_nonneg.mpr hx.le)]
    · simp [posPartAboveJet, posPartJet, ← huv, sub_pos, hx,
        max_eq_right (sub_nonpos.mpr (le_of_not_gt hx))]
  · simp only [WithLp.ofLp_snd]
    rw [← hg, hgp]
    by_cases hx : k < W1p.value u x <;>
      simp [posPartAboveJet, posPartJet, ← huv, ← hug, sub_pos, hx]

/-- Truncation above a nonnegative level is continuous in the Sobolev norm for finite
exponents. -/
theorem W1p.continuous_posPartAbove (hp : p ≠ ∞) {k : ℝ} (hk : 0 ≤ k) :
    Continuous (W1p.posPartAbove (mu := mu) (Omega := Omega) hp hk) := by
  rw [continuous_iff_seqContinuous]
  intro a u ha
  apply tendsto_subtype_rng.mpr
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  have hsrc : Tendsto (fun n ↦ (a (ns n) : Sobolev1JetLp mu Omega p)) atTop
      (𝓝 (u : Sobolev1JetLp mu Omega p)) :=
    (tendsto_subtype_rng.mp ha).comp hns
  -- An almost-everywhere convergent subsequence identifies the truncated limit.
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hsrc).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  let f : ℕ → Sobolev1JetLp mu Omega p := fun n ↦ a (ns (ms n))
  let g : ℕ → Sobolev1JetLp mu Omega p := fun n ↦ W1p.posPartAbove hp hk (a (ns (ms n)))
  have hf : Tendsto f atTop (𝓝 (u : Sobolev1JetLp mu Omega p)) :=
    hsrc.comp hms.tendsto_atTop
  have hvitali := (tendstoInMeasure_iff_tendsto_Lp (Fact.out : 1 ≤ p) hp
    (fun n ↦ Lp.memLp (f n)) (Lp.memLp (u : Sobolev1JetLp mu Omega p))).mpr
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hf)
  have hnorm (n : ℕ) : ∀ᵐ x ∂mu.restrict Omega, ‖g n x‖ ≤ ‖f n x‖ := by
    filter_upwards [posPartAbove_coe_ae hp hk (a (ns (ms n)))] with x hx
    dsimp only [g, f]
    rw [hx]
    exact norm_posPartAboveJet_le hk _
  have hui : UnifIntegrable (fun n x ↦ g n x) p (mu.restrict Omega) :=
    hvitali.2.1.ae_mono (fun n ↦ (Lp.memLp (g n)).aestronglyMeasurable) fun n ↦
      (hnorm n).mono fun x hx ↦ by
        simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hx
  have hut : UnifTight (fun n x ↦ g n x) p (mu.restrict Omega) :=
    hvitali.2.2.ae_mono (fun n ↦ (Lp.memLp (g n)).aestronglyMeasurable) fun n ↦
      (hnorm n).mono fun x hx ↦ by
        simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hx
  -- The only discontinuity of the jet truncation disappears on Sobolev level sets.
  have hzero := W1p.snd_ae_eq_zero_of_fst_eq hp u k
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr
  apply tendsto_Lp_of_tendsto_ae (Fact.out : 1 ≤ p) hp
    (fun n ↦ (Lp.memLp (g n)).aestronglyMeasurable)
    (Lp.memLp (W1p.posPartAbove hp hk u : Sobolev1JetLp mu Omega p)) hui hut
  filter_upwards [hae, hzero,
    ae_all_iff.mpr (fun n ↦ posPartAbove_coe_ae hp hk (a (ns (ms n)))),
    posPartAbove_coe_ae hp hk u] with x hx hz hg hu
  rw [hu]
  exact ((continuousAt_posPartAboveJet k hz).tendsto.comp hx).congr'
    (Eventually.of_forall fun n ↦ (hg n).symm)

/-- Taking the positive part is continuous in the Sobolev norm for finite exponents. -/
theorem W1p.continuous_posPart (hp : p ≠ ∞) :
    Continuous (W1p.posPart (mu := mu) (Omega := Omega) hp) := by
  exact (W1p.continuous_posPartAbove (mu := mu) (Omega := Omega) hp (le_refl 0)).congr
    (W1p.posPartAbove_zero hp)

/-- Truncation above a nonnegative level does not increase the Sobolev norm. -/
theorem W1p.norm_posPartAbove_le (hp : p ≠ ∞) {k : ℝ} (hk : 0 ≤ k) (u : W1p mu Omega p) :
    ‖W1p.posPartAbove hp hk u‖ ≤ ‖u‖ :=
  Lp.norm_le_norm_of_ae_le ((posPartAbove_coe_ae hp hk u).mono fun _ hx ↦
    hx ▸ norm_posPartAboveJet_le hk _)

/-- Taking the positive part does not increase the Sobolev norm. -/
theorem W1p.norm_posPart_le (hp : p ≠ ∞) (u : W1p mu Omega p) :
    ‖W1p.posPart hp u‖ ≤ ‖u‖ := by
  simpa only [W1p.posPartAbove_zero] using W1p.norm_posPartAbove_le hp (le_refl 0) u

/-- Truncation above a nonnegative level preserves the homogeneous Dirichlet boundary
condition. -/
theorem W1p.posPartAbove_mem_w1p0Submodule (hp : p ≠ ∞) {k : ℝ} (hk : 0 ≤ k)
    {u : W1p mu Omega p} (hu : u ∈ w1p0Submodule mu Omega p) :
    W1p.posPartAbove hp hk u ∈ w1p0Submodule mu Omega p := by
  refine w1p0Submodule_subset_of_isClosed
    ((w1p0Submodule mu Omega p).isClosed.preimage (W1p.continuous_posPartAbove hp hk)) ?_ hu
  intro phi
  apply W1p.mem_w1p0Submodule_of_isCompact hp phi.hasCompactSupport phi.tsupport_subset
  filter_upwards [W1p.value_posPartAbove_ae hp hk (W1p.ofTestFunctionₗ mu Omega p phi),
    testFunctionLp_apply_ae (mu := mu) p phi] with x hx hphi
  intro hxK
  rw [hx, W1p.value_ofTestFunctionₗ, hphi, image_eq_zero_of_notMem_tsupport hxK,
    max_eq_right (sub_nonpos.mpr hk)]

/-- Positive truncation preserves the homogeneous Dirichlet boundary condition. -/
theorem W1p.posPart_mem_w1p0Submodule (hp : p ≠ ∞) {u : W1p mu Omega p}
    (hu : u ∈ w1p0Submodule mu Omega p) :
    W1p.posPart hp u ∈ w1p0Submodule mu Omega p := by
  simpa only [W1p.posPartAbove_zero] using
    W1p.posPartAbove_mem_w1p0Submodule hp (le_refl 0) hu

/-- **Lowering a zero-boundary function keeps its positive part zero on the boundary.** If
`u ∈ W^{1,p}_0(Ω)` and `v ∈ W^{1,p}(Ω)` is nonnegative almost everywhere, then
`(u - v)⁺ ∈ W^{1,p}_0(Ω)`, whatever the boundary behaviour of `v`: `0 ≤ (u - v)⁺ ≤ u⁺`. -/
theorem W1p.posPart_sub_mem_w1p0Submodule (hp : p ≠ ∞) {u v : W1p mu Omega p}
    (hu : u ∈ w1p0Submodule mu Omega p) (hv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value v x) :
    W1p.posPart hp (u - v) ∈ w1p0Submodule mu Omega p := by
  refine w1p0Submodule_subset_of_isClosed ((w1p0Submodule mu Omega p).isClosed.preimage
    ((W1p.continuous_posPart hp).comp (continuous_id.sub continuous_const))) ?_ hu
  intro phi
  apply W1p.mem_w1p0Submodule_of_isCompact hp phi.hasCompactSupport phi.tsupport_subset
  filter_upwards [Lp.coeFn_posPart (W1p.value (W1p.ofTestFunctionₗ mu Omega p phi - v)),
    W1p.value_sub_ae (W1p.ofTestFunctionₗ mu Omega p phi) v,
    testFunctionLp_apply_ae (mu := mu) p phi, hv] with x hx hsub hphi hvx
  intro hxK
  simp only [Function.comp_apply, id_eq, W1p.value_posPart, hx, hsub, Pi.sub_apply,
    W1p.value_ofTestFunctionₗ, hphi, image_eq_zero_of_notMem_tsupport hxK, zero_sub]
  exact max_eq_right (neg_nonpos.2 hvx)

/-- **Functions squeezed below a zero-boundary function have zero boundary values.** If
`u ∈ W^{1,p}_0(Ω)` and `v ∈ W^{1,p}(Ω)` satisfy `0 ≤ v ≤ u` almost everywhere, then
`v ∈ W^{1,p}_0(Ω)`, since `v = u - (u - v)⁺`. -/
theorem W1p.mem_w1p0Submodule_of_nonneg_of_le (hp : p ≠ ∞) {u v : W1p mu Omega p}
    (hu : u ∈ w1p0Submodule mu Omega p) (hv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value v x)
    (hvu : ∀ᵐ x ∂mu.restrict Omega, W1p.value v x ≤ W1p.value u x) :
    v ∈ w1p0Submodule mu Omega p := by
  have heq : u - W1p.posPart hp (u - v) = v := by
    refine W1p.ext_value (Lp.ext ?_)
    filter_upwards [W1p.value_sub_ae u (W1p.posPart hp (u - v)),
      Lp.coeFn_posPart (W1p.value (u - v)), W1p.value_sub_ae u v, hvu] with x h1 h2 h3 h4
    rw [h1, Pi.sub_apply, W1p.value_posPart, h2, h3, Pi.sub_apply,
      max_eq_left (sub_nonneg.2 h4), sub_sub_cancel]
  rw [← heq]
  exact (w1p0Submodule mu Omega p).toSubmodule.sub_mem hu
    (W1p.posPart_sub_mem_w1p0Submodule hp hu hv)

/-- **The truncation `min(u⁺, c v)`.** The function `u⁺ - (u⁺ - c v)⁺` has value
`min(u⁺, c v)` almost everywhere. -/
theorem W1p.value_posPart_sub_posPart_sub_smul_ae (hp : p ≠ ∞) (u v : W1p mu Omega p) (c : ℝ) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value (W1p.posPart hp u -
      W1p.posPart hp (W1p.posPart hp u - c • v)) x =
        min (max (W1p.value u x) 0) (c * W1p.value v x) := by
  filter_upwards [W1p.value_sub_ae (W1p.posPart hp u) (W1p.posPart hp (W1p.posPart hp u - c • v)),
    Lp.coeFn_posPart (W1p.value (W1p.posPart hp u - c • v)),
    W1p.value_sub_ae (W1p.posPart hp u) (c • v), Lp.coeFn_posPart (W1p.value u),
    W1p.value_smul_ae c v] with x h1 h2 h3 h4 h5
  rw [h1, Pi.sub_apply, W1p.value_posPart (u := W1p.posPart hp u - c • v), h2, h3, Pi.sub_apply,
    W1p.value_posPart, h4, h5, Pi.smul_apply, smul_eq_mul]
  rcases le_total (max (W1p.value u x) 0) (c * W1p.value v x) with hle | hle
  · rw [min_eq_left hle, max_eq_right (sub_nonpos.2 hle), sub_zero]
  · rw [min_eq_right hle, max_eq_left (sub_nonneg.2 hle), sub_sub_cancel]

/-- **The truncation `min(u⁺, c v)` is constant where `u ≤ 0`.** If `c v ≥ 0`, the weak gradient
of `u⁺ - (u⁺ - c v)⁺` vanishes almost everywhere on `{u ≤ 0}`. -/
theorem W1p.gradient_posPart_sub_posPart_sub_smul_eq_zero_ae (hp : p ≠ ∞)
    (u v : W1p mu Omega p) {c : ℝ} (hcv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ c * W1p.value v x) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ 0 → W1p.gradient (W1p.posPart hp u -
      W1p.posPart hp (W1p.posPart hp u - c • v)) x = 0 := by
  filter_upwards [W1p.gradient_sub_ae (W1p.posPart hp u)
      (W1p.posPart hp (W1p.posPart hp u - c • v)), W1p.gradient_posPart_ae hp u,
    W1p.gradient_posPart_ae hp (W1p.posPart hp u - c • v),
    W1p.value_sub_ae (W1p.posPart hp u) (c • v), Lp.coeFn_posPart (W1p.value u),
    W1p.value_smul_ae c v, hcv] with x h1 h2 h3 h4 h5 h6 h7 hu
  have hup : W1p.value (W1p.posPart hp u) x = 0 := by
    rw [W1p.value_posPart, h5, max_eq_right hu]
  rw [h1, Pi.sub_apply, h2, h3, indicator_of_notMem (s := {y | 0 < W1p.value u y})
    (not_lt.2 hu), indicator_of_notMem (s := {y | 0 < W1p.value (W1p.posPart hp u - c • v) y})
      (by rw [mem_ofPred_eq, h4, Pi.sub_apply, hup, h6, Pi.smul_apply, smul_eq_mul, not_lt]
          linarith), sub_zero]

/-- If `(u - k)⁺` satisfies the homogeneous Dirichlet boundary condition, then so does
`(u - l)⁺` at every higher level `l ≥ k`: boundary values at most `k` are at most `l`. -/
theorem W1p.posPartAbove_mem_w1p0Submodule_of_le (hp : p ≠ ∞) {k l : ℝ} (hk : 0 ≤ k)
    (hkl : k ≤ l) {u : W1p mu Omega p}
    (hu : W1p.posPartAbove hp hk u ∈ w1p0Submodule mu Omega p) :
    W1p.posPartAbove hp (hk.trans hkl) u ∈ w1p0Submodule mu Omega p := by
  have h := W1p.posPartAbove_mem_w1p0Submodule hp (sub_nonneg.2 hkl) hu
  rw [W1p.posPartAbove_posPartAbove] at h
  simpa only [add_sub_cancel] using h

/-- **Composition preserves zero boundary values.** If `F` is a Lipschitz `C¹` function with
`F 0 = 0` and `0 ≤ F s ≤ C s` for `s ≥ 0`, and `v ∈ W^{1,p}_0(Ω)` is nonnegative, then
`F ∘ v ∈ W^{1,p}_0(Ω)`, since it lies between `0` and `C v`. -/
theorem W1p.contDiffComp_mem_w1p0Submodule_of_nonneg (hp : p ≠ ∞) {F : ℝ → ℝ} {M : NNReal}
    (hF : ContDiff ℝ 1 F) (hM : ∀ s, ‖deriv F s‖₊ ≤ M) (hF0 : F 0 = 0) {C : ℝ}
    (hFnonneg : ∀ s, 0 ≤ s → 0 ≤ F s) (hFle : ∀ s, 0 ≤ s → F s ≤ C * s)
    {v : W1p mu Omega p} (hv : v ∈ w1p0Submodule mu Omega p)
    (hv0 : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value v x) :
    W1p.contDiffComp hp hF hM hF0 v ∈ w1p0Submodule mu Omega p := by
  have hval := W1p.value_contDiffComp_ae hp hF hM hF0 v
  refine W1p.mem_w1p0Submodule_of_nonneg_of_le hp
    ((w1p0Submodule mu Omega p).toSubmodule.smul_mem C hv) ?_ ?_
  · filter_upwards [hval, hv0] with x hx hs
    rw [hx]
    exact hFnonneg _ hs
  · filter_upwards [hval, W1p.value_smul_ae C v, hv0] with x hx hsx hs
    rw [hx, hsx, Pi.smul_apply, smul_eq_mul]
    exact hFle _ hs

/-- **Truncated squares.** For `t > 0` and a nonnegative `v ∈ W^{1,p}_0(Ω)`, the truncated
square `v² / (1 + t v²)` lies in `W^{1,p}_0(Ω)`, with gradient `2 v ∇v / (1 + t v²)²`. Unlike `v²`,
it is a Lipschitz function of `v`, and it lies below `(1 + 1 / t) v`. -/
theorem W1p.exists_mem_w1p0Submodule_value_eq_sq_div (hp : p ≠ ∞) {t : ℝ} (ht0 : 0 < t)
    {v : W1p mu Omega p} (hv : v ∈ w1p0Submodule mu Omega p)
    (hv0 : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value v x) :
    ∃ φ ∈ w1p0Submodule mu Omega p,
      (∀ᵐ x ∂mu.restrict Omega,
        W1p.value φ x = W1p.value v x ^ 2 / (1 + t * W1p.value v x ^ 2)) ∧
      ∀ᵐ x ∂mu.restrict Omega, W1p.gradient φ x =
        (2 * W1p.value v x / (1 + t * W1p.value v x ^ 2) ^ 2) • W1p.gradient v x := by
  set F : ℝ → ℝ := fun s ↦ s ^ 2 / (1 + t * s ^ 2)
  have hden : ∀ s, 1 ≤ 1 + t * s ^ 2 := fun s ↦
    le_add_of_nonneg_right (mul_nonneg ht0.le (sq_nonneg s))
  have hFc : ContDiff ℝ 1 F :=
    (contDiff_id.pow 2).div (contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2)))
      fun s ↦ (zero_lt_one.trans_le (hden s)).ne'
  have hderiv : ∀ s, deriv F s = 2 * s / (1 + t * s ^ 2) ^ 2 := fun s ↦ by
    refine HasDerivAt.deriv ?_
    convert (hasDerivAt_pow 2 s).div (((hasDerivAt_pow 2 s).const_mul t).const_add 1)
      (zero_lt_one.trans_le (hden s)).ne' using 1
    field_simp
    ring
  -- `|F'| ≤ 1 + 1 / t`, since `2 |s| t ≤ t (1 + s²) ≤ (t + 1) (1 + t s²) ≤ (t + 1) (1 + t s²)²`.
  have hM : ∀ s, ‖deriv F s‖₊ ≤ (1 + 1 / t).toNNReal := fun s ↦ by
    have hs : 2 * |s| ≤ 1 + s ^ 2 := by nlinarith [sq_nonneg (|s| - 1), sq_abs s]
    have hts : t * (2 * |s|) ≤ (t + 1) * (1 + t * s ^ 2) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hs ht0.le, hden s, sq_nonneg s,
        mul_nonneg (mul_nonneg ht0.le ht0.le) (sq_nonneg s),
        mul_le_mul_of_nonneg_left (hden s) (mul_nonneg (by positivity : (0 : ℝ) ≤ t + 1)
          (zero_le_one.trans (hden s)))]
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity)]
    simp only [coe_nnNorm, hderiv, Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> field_simp <;> nlinarith [neg_abs_le s, le_abs_self s]
  have hF0 : F 0 = 0 := by simp [F]
  refine ⟨W1p.contDiffComp hp hFc hM hF0 v, W1p.contDiffComp_mem_w1p0Submodule_of_nonneg hp hFc hM
    hF0 (C := 1 + 1 / t) (fun s _ ↦ div_nonneg (sq_nonneg s) (zero_le_one.trans (hden s)))
    (fun s hs ↦ ?_) hv hv0, W1p.value_contDiffComp_ae hp hFc hM hF0 v, ?_⟩
  · -- `s² / (1 + t s²) ≤ (1 + 1 / t) s` for `s ≥ 0`, since `s² ≤ s + s³`.
    rw [div_le_iff₀ (zero_lt_one.trans_le (hden _))]
    have heq : (1 + 1 / t) * s * (1 + t * s ^ 2) = s + s ^ 3 + s / t + t * s ^ 3 := by
      field_simp
      ring
    rw [heq]
    nlinarith [mul_nonneg hs (sq_nonneg (s - 1 / 2)), div_nonneg hs ht0.le,
      mul_nonneg ht0.le (pow_nonneg hs 3)]
  · filter_upwards [W1p.gradient_contDiffComp_ae hp hFc hM hF0 v] with x hx
    rw [hx, hderiv]

/-! ### The positive part on `W^{1,p}_0(Ω)` -/

/-- **The positive part on `W^{1,p}_0(Ω)`**: for `1 ≤ p < ∞`, the positive part `u⁺` of a
zero-boundary Sobolev function again has zero boundary values
(`TauCeti.W1p.posPart_mem_w1p0Submodule`). -/
def W1p0.posPart (hp : p ≠ ∞) (u : W1p0 mu Omega p) : W1p0 mu Omega p :=
  ⟨W1p.posPart hp u, W1p.posPart_mem_w1p0Submodule hp u.property⟩

@[simp]
theorem W1p0.coe_posPart (hp : p ≠ ∞) (u : W1p0 mu Omega p) :
    (W1p0.posPart hp u : W1p mu Omega p) = W1p.posPart hp u :=
  (rfl)

/-- The value of `u⁺` is the `Lᵖ` positive part of the value of `u`. -/
theorem W1p0.valueL_posPart (hp : p ≠ ∞) (u : W1p0 mu Omega p) :
    W1p0.valueL (W1p0.posPart hp u) = Lp.posPart (W1p0.valueL u) := by
  simp only [W1p0.valueL_apply, W1p0.coe_posPart, W1p.value_posPart]

/-- Taking the positive part is continuous on `W^{1,p}_0(Ω)` for finite exponents. -/
theorem W1p0.continuous_posPart (hp : p ≠ ∞) :
    Continuous (W1p0.posPart (mu := mu) (Omega := Omega) hp) :=
  ((W1p.continuous_posPart hp).comp continuous_subtypeVal).subtype_mk _

/-- Taking the positive part does not increase the norm of `W^{1,p}_0(Ω)`. -/
theorem W1p0.norm_posPart_le (hp : p ≠ ∞) (u : W1p0 mu Omega p) :
    ‖W1p0.posPart hp u‖ ≤ ‖u‖ :=
  W1p.norm_posPart_le hp (u : W1p mu Omega p)

end TauCeti
