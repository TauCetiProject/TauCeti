/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.W1p.MixedMultiplication
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Calculus.LineDeriv.Bilinear
import TauCeti.Analysis.Sobolev.Mollification.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Holder
import TauCeti.Analysis.Sobolev.WeakDeriv.Limit
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.Data.ENNReal.Holder
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.Topology.UniformSpace.UniformConvergence.ENorm

/-!
# Mixed-exponent products of local Sobolev maps on planar domains

Let `p > 2`, `1 ≤ q ≤ p` and let `B : F × G → H` be continuous bilinear with `G`
finite-dimensional. This file proves the first two orders of the mixed-exponent product
theorem for the local classes `TauCeti.MemLpLoc` and `TauCeti.MemWkpLoc` on an open planar
domain `Ω`.

* Order zero: for `f ∈ Lᵖ_loc` and `g ∈ W^{1,q}_loc`, the product `B(f, g)` is in `L^q_loc`.
  This combines Hölder's inequality with the local gain of integrability `W^{1,q} ⊂ Lʳ`,
  where `1/p + 1/r = 1/q`, and it uses `p > 2`.
* Order one: for `f ∈ W^{1,p}_loc ∩ L^∞_loc` and `g ∈ W^{1,q}_loc` with `1 < q`, the product
  `B(f, g)` is in `W^{1,q}_loc`, with weak derivative `B(Df, g) + B(f, Dg)`.
  At `q = p` this is the algebra property of `W^{1,p}_loc`. When `F` is finite-dimensional, the
  local boundedness of `f` follows from the local gain of integrability at `q = p`.

Both rest on local bounds that are uniform in the bilinear map.

## Main declarations

* `TauCeti.MemWkpLoc.memLpLoc_of_holderTriple`: the local gain of integrability.
* `TauCeti.MemLpLoc.bilin_of_memWkpLoc`: order-zero membership.
* `TauCeti.HasWeakLineDerivOn.bilin_of_memLpLoc`,
  `TauCeti.HasWeakLineDerivOn.bilin_of_continuousOn`, and
  `TauCeti.HasWeakFDerivOn.bilin_of_memLpLoc`:
  the directional and Fréchet weak Leibniz rules at local Hölder exponents.
* `TauCeti.MemWkpLoc.bilin_of_memLpLoc_top` and `TauCeti.MemWkpLoc.bilin`: order-one membership.

The local bounds behind them, `TauCeti.W1p.exists_eLpNorm_le_of_holderTriple`,
`TauCeti.W1p.exists_eLpNorm_bilin_le` and `TauCeti.W1p.exists_eLpNorm_bilin_add_eLpNorm_deriv_le`,
hold in any finite-dimensional space with `dim E < p` and live in
`TauCeti.Analysis.Sobolev.W1p.MixedMultiplication`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Proposition B.1.19.
-/

public noncomputable section

open MeasureTheory TopologicalSpace Module
open scoped ENNReal NNReal

namespace TauCeti

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {Ω : Opens ℂ} {p q : ℝ≥0}

/-- **Local gain of integrability.** For `p > 2` and `1 ≤ q ≤ p`, a map in `W^{1,q}_loc` with
finite-dimensional values is in `Lʳ_loc` for `1/p + 1/r = 1/q`. At `q = p` this is `r = ∞`. -/
theorem MemWkpLoc.memLpLoc_of_holderTriple (hp : 2 < p) (hqp : q ≤ p) [Fact (1 ≤ (q : ℝ≥0∞))]
    {r : ℝ≥0∞} [ENNReal.HolderTriple p r q] {g : ℂ → G} (hg : MemWkpLoc q Ω 1 g) :
    MemLpLoc r Ω g := by
  refine memLpLoc_iff.2 fun K hKΩ hK => ?_
  obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  obtain ⟨Dg, hDg, hDq⟩ := hg.exists_weakFDeriv_of_isOpen
  obtain ⟨C, hC⟩ := W1p.exists_eLpNorm_le_of_holderTriple (μ := volume) (Ω := ⟨W, hWo⟩)
    (G := G) (r := r) (by simpa using hp) hqp hK hKW
  have hgW := hg.memLpLoc.memLp_restrict_of_isCompact_closure hWc hWΩ
  have hDW := (memWkpLoc_zero_iff.1 hDq).memLp_restrict_of_isCompact_closure hWc hWΩ
  exact (hC g Dg (hDg.mono (subset_closure.trans hWΩ)) hgW hDW).trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top
      (ENNReal.add_lt_top.2 ⟨hgW.eLpNorm_lt_top, hDW.eLpNorm_lt_top⟩))

/-- **Order-zero mixed products.** For `p > 2` and `1 ≤ q ≤ p`, the product of a locally `Lᵖ`
map with a `W^{1,q}_loc` map with finite-dimensional values is locally `L^q`. -/
theorem MemLpLoc.bilin_of_memWkpLoc (B : F →L[ℝ] G →L[ℝ] H) (hp : 2 < p) (hqp : q ≤ p)
    [Fact (1 ≤ (q : ℝ≥0∞))] {f : ℂ → F} {g : ℂ → G} (hf : MemLpLoc p Ω f)
    (hg : MemWkpLoc q Ω 1 g) : MemLpLoc q Ω (fun z => B (f z) (g z)) := by
  let _ := ENNReal.HolderTriple.of_le (p := (p : ℝ≥0∞)) (q := q) (by exact_mod_cast hqp)
  have hgr : MemLpLoc ((q : ℝ≥0∞)⁻¹ - (p : ℝ≥0∞)⁻¹)⁻¹ Ω g :=
    hg.memLpLoc_of_holderTriple hp hqp
  exact memLpLoc_iff.2 fun K hKΩ hK =>
    B.memLp_of_bilin q (memLpLoc_iff.1 hf K hKΩ hK) (memLpLoc_iff.1 hgr K hKΩ hK)

omit [FiniteDimensional ℝ G] in
/-- **The directional weak Leibniz rule at finite local Hölder exponents.** If `f, g` have weak
directional derivatives `f', g'` along `v` on `Ω` with finite local `Lᵖ` bounds satisfying
`p⁻¹ + q⁻¹ ≤ 1`, `p'⁻¹ + q⁻¹ ≤ 1`, and `p⁻¹ + q'⁻¹ ≤ 1`, then `B(f, g)` has weak directional
derivative `B(f', g) + B(f, g')` along `v`. -/
theorem HasWeakLineDerivOn.bilin_of_memLpLoc [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H)
    {p p' q q' : ℝ≥0∞} (hp : p ≠ ⊤) (hp' : p' ≠ ⊤) (hq : q ≠ ⊤) (hq' : q' ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (hp'q : p'⁻¹ + q⁻¹ ≤ 1) (hpq' : p⁻¹ + q'⁻¹ ≤ 1)
    {v : ℂ} {f f' : ℂ → F} {g g' : ℂ → G}
    (hf : HasWeakLineDerivOn volume Ω f f' v) (hg : HasWeakLineDerivOn volume Ω g g' v)
    (hfp : MemLpLoc p Ω f) (hf'p : MemLpLoc p' Ω f')
    (hgq : MemLpLoc q Ω g) (hg'q : MemLpLoc q' Ω g') :
    HasWeakLineDerivOn volume Ω (fun z => B (f z) (g z))
      (fun z => B (f' z) (g z) + B (f z) (g' z)) v := by
  let _ : Fact (1 ≤ p) := ⟨ENNReal.inv_le_one.1 (le_self_add.trans hpq)⟩
  let _ : Fact (1 ≤ p') := ⟨ENNReal.inv_le_one.1 (le_self_add.trans hp'q)⟩
  let _ : Fact (1 ≤ q) := ⟨ENNReal.inv_le_one.1 (le_add_self.trans hpq)⟩
  let _ : Fact (1 ≤ q') := ⟨ENNReal.inv_le_one.1 (le_add_self.trans hpq')⟩
  exact hf.bilin_of_memLp B hp hp' hq hq' hpq hp'q hpq' hg
    (fun K hK hKΩ => memLpLoc_iff.1 hfp K hKΩ hK)
    (fun K hK hKΩ => memLpLoc_iff.1 hf'p K hKΩ hK)
    (fun K hK hKΩ => memLpLoc_iff.1 hgq K hKΩ hK)
    (fun K hK hKΩ => memLpLoc_iff.1 hg'q K hKΩ hK)

section Endpoint

open Filter Set
open scoped Convolution Distributions Topology

private theorem tendsto_integral_smul_bilin_of_tendstoUniformlyOn {E F G H : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [T2Space E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    {μ : Measure E} {B : F →L[ℝ] G →L[ℝ] H} {K : Set E} (hK : IsCompact K)
    {ψ : E → ℝ} (hψc : Continuous ψ) (hψK : tsupport ψ ⊆ K)
    {u : E → G} (hu : IntegrableOn u K μ)
    {f_n : ℕ → E → F} {f : E → F} (hfn_cont : ∀ n, ContinuousOn (f_n n) K)
    (hunif : TendstoUniformlyOn f_n f atTop K) :
    Tendsto (fun n => ∫ x, ψ x • B (f_n n x) (u x) ∂μ) atTop
      (𝓝 (∫ x, ψ x • B (f x) (u x) ∂μ)) := by
  have hKm : MeasurableSet K := hK.measurableSet
  have hint {h : E → F} (hh : ContinuousOn h K) :
      Integrable (fun x => ψ x • B (h x) (u x)) μ := by
    refine (integrableOn_iff_integrable_of_support_subset
      (fun x hx => hψK (subset_tsupport ψ fun h0 => hx (by simp [h0])))).1 ?_
    exact hu.continuousOn_clm_apply (hψc.continuousOn.smul (B.continuous.comp_continuousOn hh)) hK
  have hfc : ContinuousOn f K := hunif.continuousOn (.of_forall hfn_cont)
  obtain ⟨M, hM⟩ := hψc.bounded_above_of_compact_support
    (HasCompactSupport.of_support_subset_isCompact hK ((subset_tsupport ψ).trans hψK))
  have hsup : Tendsto (fun n => ENNReal.ofReal (M * ‖B‖) *
      (⨆ x ∈ K, ‖f_n n x - f x‖ₑ) * ∫⁻ x in K, ‖u x‖ₑ ∂μ) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ENNReal.ofReal (M * ‖B‖) * ⨆ x ∈ K, ‖f_n n x - f x‖ₑ)
        atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hunif.tendsto_iSup_enorm_sub
        (Or.inr ENNReal.ofReal_ne_top)
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hu.2.ne)
  refine tendsto_integral_of_L1 _ (hint hfc).aestronglyMeasurable
    (.of_forall fun n => hint (hfn_cont n))
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsup
      (fun _ => zero_le) fun n => ?_)
  rw [← lintegral_const_mul'' _ hu.aestronglyMeasurable.eNorm, ← lintegral_indicator hKm]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx, ← smul_sub, ← sub_apply,
      ← ContinuousLinearMap.map_sub, eNorm_smul, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_mul (norm_nonneg _)]
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x)
    have hle : ‖ψ x‖ * ‖B (f_n n x - f x) (u x)‖ ≤ M * ‖B‖ * ‖f_n n x - f x‖ * ‖u x‖ := by
      calc ‖ψ x‖ * ‖B (f_n n x - f x) (u x)‖
          ≤ M * (‖B‖ * ‖f_n n x - f x‖ * ‖u x‖) :=
            mul_le_mul (hM x) (B.le_opNorm₂ _ _) (norm_nonneg _) hM0
        _ = M * ‖B‖ * ‖f_n n x - f x‖ * ‖u x‖ := by ring
    refine (ENNReal.ofReal_le_ofReal hle).trans ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (mul_nonneg hM0 (norm_nonneg B)),
      ofReal_norm, ofReal_norm]
    gcongr
    exact le_biSup (fun y => ‖f_n n y - f y‖ₑ) hx
  · simp [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport fun h => hx (hψK h)]

omit [FiniteDimensional ℝ G] in
/-- **Endpoint directional weak Leibniz rule for a continuous left factor.** If `f` is continuous
on `Ω` with weak directional derivative `f' ∈ Lᵖ_loc(Ω)` along `v`, and `g ∈ L^q_loc(Ω)` has weak
directional derivative `g'` along `v` (without assuming `g' ∈ L^q_loc`), where `p⁻¹ + q⁻¹ ≤ 1`
(allowing `p = ∞` or `q = ∞`), then `B(f, g)` has weak directional derivative `B(f', g) + B(f, g')`
along `v`. -/
theorem HasWeakLineDerivOn.bilin_of_continuousOn [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H)
    {p q : ℝ≥0∞} (hpq : p⁻¹ + q⁻¹ ≤ 1) {v : ℂ} {f f' : ℂ → F} {g g' : ℂ → G}
    (hf : HasWeakLineDerivOn volume Ω f f' v) (hfc : ContinuousOn f Ω) (hf'p : MemLpLoc p Ω f')
    (hg : HasWeakLineDerivOn volume Ω g g' v) (hgq : MemLpLoc q Ω g) :
    HasWeakLineDerivOn volume Ω (fun z => B (f z) (g z))
      (fun z => B (f' z) (g z) + B (f z) (g' z)) v := by
  have : CompleteSpace F := hf.completeSpace
  have : CompleteSpace G := hg.completeSpace
  have hloc := Ω.isOpen.isLocallyClosed
  have hBf : ContinuousOn (fun z => B (f z)) Ω := B.continuous.comp_continuousOn hfc
  have hBfg : LocallyIntegrableOn (fun z => B (f z) (g z)) Ω volume :=
    hg.locallyIntegrableOn.continuousOn_clm_apply hloc hBf
  have hBf'g : LocallyIntegrableOn (fun z => B (f' z) (g z)) Ω volume :=
    (hf'p.clm_comp B).locallyIntegrableOn_clm_apply hgq hpq hloc
  have hBfg' : LocallyIntegrableOn (fun z => B (f z) (g' z)) Ω volume :=
    hg.locallyIntegrableOn_deriv.continuousOn_clm_apply hloc hBf
  refine hasWeakLineDerivOn_iff_testFunction.2 ⟨inferInstance, hBfg, hBf'g.add hBfg', fun φ => ?_⟩
  obtain ⟨W, hφW, hWΩ, hWc⟩ :=
    Opens.exists_between_and_isCompact_closure φ.hasCompactSupport φ.tsupport_subset
  obtain ⟨W₀, hφW₀, hW₀W, hW₀c⟩ :=
    Opens.exists_between_and_isCompact_closure φ.hasCompactSupport hφW
  obtain ⟨ρ, hρ0, hball⟩ := ContDiffBump.exists_seq_sub_tsupport_subset (μ := volume) hW₀c hW₀W
  have hWm : MeasurableSet (W : Set ℂ) := W.isOpen.measurableSet
  have hf_int : Integrable ((W : Set ℂ).indicator f) volume :=
    (integrable_indicator_iff hWm).2
      ((hf.locallyIntegrableOn.integrableOn_compact_subset hWΩ hWc).mono_set subset_closure)
  have hf'_int : Integrable ((W : Set ℂ).indicator f') volume :=
    (integrable_indicator_iff hWm).2
      ((hf.locallyIntegrableOn_deriv.integrableOn_compact_subset hWΩ hWc).mono_set subset_closure)
  have hg_int : Integrable ((W : Set ℂ).indicator g) volume :=
    (integrable_indicator_iff hWm).2
      ((hg.locallyIntegrableOn.integrableOn_compact_subset hWΩ hWc).mono_set subset_closure)
  have hg'_int : Integrable ((W : Set ℂ).indicator g') volume :=
    (integrable_indicator_iff hWm).2
      ((hg.locallyIntegrableOn_deriv.integrableOn_compact_subset hWΩ hWc).mono_set subset_closure)
  have hf'W : MemLp f' p (volume.restrict W) := hf'p.memLp_restrict_of_isCompact_closure hWc hWΩ
  have hgW : MemLp g q (volume.restrict W) := hgq.memLp_restrict_of_isCompact_closure hWc hWΩ
  let f_n (n : ℕ) :=
    (ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator f
  let f'_n (n : ℕ) :=
    (ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator f'
  let g_m (m : ℕ) :=
    (ρ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator g
  let g'_m (m : ℕ) :=
    (ρ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator g'
  have hfn_cont (n : ℕ) : Continuous (f_n n) :=
    (ρ n).hasCompactSupport_normed.continuous_convolution_left _ (ρ n).continuous_normed
      hf_int.locallyIntegrable
  have hf'n_cont (n : ℕ) : Continuous (f'_n n) :=
    (ρ n).hasCompactSupport_normed.continuous_convolution_left _ (ρ n).continuous_normed
      hf'_int.locallyIntegrable
  have hgm_cont (m : ℕ) : Continuous (g_m m) :=
    (ρ m).hasCompactSupport_normed.continuous_convolution_left _ (ρ m).continuous_normed
      hg_int.locallyIntegrable
  have hg'm_cont (m : ℕ) : Continuous (g'_m m) :=
    (ρ m).hasCompactSupport_normed.continuous_convolution_left _ (ρ m).continuous_normed
      hg'_int.locallyIntegrable
  have hW₀Ω : (W₀ : Set ℂ) ⊆ Ω := subset_closure.trans (hW₀W.trans (subset_closure.trans hWΩ))
  have hW₀W' : (W₀ : Set ℂ) ⊆ W := subset_closure.trans hW₀W
  have hweak_n (n : ℕ) : HasWeakLineDerivOn volume W₀ (fun z => B (f_n n z) (g z))
      (fun z => B (f'_n n z) (g z) + B (f_n n z) (g' z)) v := by
    have hweak_nm (m : ℕ) : HasWeakLineDerivOn volume W₀ (fun z => B (f_n n z) (g_m m z))
        (fun z => B (f'_n n z) (g_m m z) + B (f_n n z) (g'_m m z)) v := by
      refine hasWeakLineDerivOn_of_hasLineDerivAt
        ((B.continuous₂.comp
          ((hfn_cont n).prodMk (hgm_cont m))).locallyIntegrable.locallyIntegrableOn _)
        (((B.continuous₂.comp ((hf'n_cont n).prodMk (hgm_cont m))).add
          (B.continuous₂.comp
            ((hfn_cont n).prodMk (hg'm_cont m)))).locallyIntegrable.locallyIntegrableOn _)
        fun x hx => ?_
      have hfd := ((hf.mono (subset_closure.trans hWΩ)).indicator).hasLineDerivAt_convolution_right
        hf_int.locallyIntegrable _ (ρ n).contDiff_normed (ρ n).hasCompactSupport_normed x
        (hball n x hx)
      have hgd := ((hg.mono (subset_closure.trans hWΩ)).indicator).hasLineDerivAt_convolution_right
        hg_int.locallyIntegrable _ (ρ m).contDiff_normed (ρ m).hasCompactSupport_normed x
        (hball m x hx)
      rw [convolution_flip, convolution_flip] at hfd hgd
      exact hfd.clm_bilin B hgd
    obtain ⟨C₁, hC₁⟩ := hW₀c.exists_bound_of_continuousOn (hfn_cont n).continuousOn
    obtain ⟨C₂, hC₂⟩ := hW₀c.exists_bound_of_continuousOn (hf'n_cont n).continuousOn
    let M₁ := max 0 C₁
    let M₂ := max 0 C₂
    have hM₁ : 0 ≤ M₁ := le_max_left _ _
    have hM₂ : 0 ≤ M₂ := le_max_left _ _
    have hgm_lim : Tendsto (fun m => ∫⁻ z in (W₀ : Set ℂ), ‖g_m m z - g z‖ₑ) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (tendsto_lintegral_enorm_normed_convolution_sub hρ0 hg_int) (fun _ => zero_le) fun m => by
          refine (setLIntegral_mono_ae' W₀.isOpen.measurableSet (.of_forall fun z hz => ?_)).trans
            (setLIntegral_le_lintegral _ _)
          rw [Set.indicator_of_mem (hW₀W' hz)]
    have hg'm_lim : Tendsto (fun m => ∫⁻ z in (W₀ : Set ℂ), ‖g'_m m z - g' z‖ₑ) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (tendsto_lintegral_enorm_normed_convolution_sub hρ0 hg'_int) (fun _ => zero_le) fun m => by
          refine (setLIntegral_mono_ae' W₀.isOpen.measurableSet (.of_forall fun z hz => ?_)).trans
            (setLIntegral_le_lintegral _ _)
          rw [Set.indicator_of_mem (hW₀W' hz)]
    have hL₁ : Tendsto (fun m => ∫⁻ z in (W₀ : Set ℂ), ‖B (f_n n z) (g_m m z) - B (f_n n z) (g z)‖ₑ)
        atTop (𝓝 0) := by
      have hmul : Tendsto (fun m => ENNReal.ofReal (‖B‖ * M₁) *
          ∫⁻ z in (W₀ : Set ℂ), ‖g_m m z - g z‖ₑ) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul hgm_lim (Or.inr ENNReal.ofReal_ne_top)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul
        (fun _ => zero_le) fun m => ?_
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono_ae' W₀.isOpen.measurableSet (.of_forall fun z hz => ?_)
      rw [← ContinuousLinearMap.map_sub, ← ofReal_norm, ← ofReal_norm,
        ← ENNReal.ofReal_mul (mul_nonneg (norm_nonneg B) hM₁)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc ‖B (f_n n z) (g_m m z - g z)‖
          ≤ ‖B‖ * ‖f_n n z‖ * ‖g_m m z - g z‖ := B.le_opNorm₂ _ _
        _ ≤ ‖B‖ * M₁ * ‖g_m m z - g z‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              ((hC₁ z (subset_closure hz)).trans (le_max_right _ _)) (norm_nonneg B))
              (norm_nonneg _)
    have hL₂ : Tendsto (fun m => ∫⁻ z in (W₀ : Set ℂ),
        ‖(B (f'_n n z) (g_m m z) + B (f_n n z) (g'_m m z)) -
          (B (f'_n n z) (g z) + B (f_n n z) (g' z))‖ₑ) atTop (𝓝 0) := by
      have hm1 : Tendsto (fun m => ENNReal.ofReal (‖B‖ * M₂) *
          ∫⁻ z in (W₀ : Set ℂ), ‖g_m m z - g z‖ₑ) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul hgm_lim (Or.inr ENNReal.ofReal_ne_top)
      have hm2 : Tendsto (fun m => ENNReal.ofReal (‖B‖ * M₁) *
          ∫⁻ z in (W₀ : Set ℂ), ‖g'_m m z - g' z‖ₑ) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul hg'm_lim (Or.inr ENNReal.ofReal_ne_top)
      have hmul := hm1.add hm2
      simp only [add_zero] at hmul
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul
        (fun _ => zero_le) fun m => ?_
      have hint_g : AEMeasurable (fun z => ‖g_m m z - g z‖ₑ)
          (volume.restrict (W₀ : Set ℂ)) :=
        ((hgm_cont m).aestronglyMeasurable.sub
          (hg.locallyIntegrableOn.mono_set hW₀Ω).aestronglyMeasurable).eNorm
      have hint_g' : AEMeasurable (fun z => ‖g'_m m z - g' z‖ₑ)
          (volume.restrict (W₀ : Set ℂ)) :=
        ((hg'm_cont m).aestronglyMeasurable.sub
          (hg.locallyIntegrableOn_deriv.mono_set hW₀Ω).aestronglyMeasurable).eNorm
      calc ∫⁻ z in (W₀ : Set ℂ),
            ‖(B (f'_n n z) (g_m m z) + B (f_n n z) (g'_m m z)) -
              (B (f'_n n z) (g z) + B (f_n n z) (g' z))‖ₑ
          ≤ ∫⁻ z in (W₀ : Set ℂ),
              (ENNReal.ofReal (‖B‖ * M₂) * ‖g_m m z - g z‖ₑ +
                ENNReal.ofReal (‖B‖ * M₁) * ‖g'_m m z - g' z‖ₑ) := by
            refine setLIntegral_mono_ae' W₀.isOpen.measurableSet (.of_forall fun z hz => ?_)
            have hsub : (B (f'_n n z) (g_m m z) + B (f_n n z) (g'_m m z)) -
                (B (f'_n n z) (g z) + B (f_n n z) (g' z)) =
                B (f'_n n z) (g_m m z - g z) + B (f_n n z) (g'_m m z - g' z) := by
              simp only [map_sub]
              abel
            rw [hsub]
            refine (eNorm_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [← ofReal_norm, ← ofReal_norm,
                ← ENNReal.ofReal_mul (mul_nonneg (norm_nonneg B) hM₂)]
              refine ENNReal.ofReal_le_ofReal ?_
              calc ‖B (f'_n n z) (g_m m z - g z)‖
                  ≤ ‖B‖ * ‖f'_n n z‖ * ‖g_m m z - g z‖ := B.le_opNorm₂ _ _
                _ ≤ ‖B‖ * M₂ * ‖g_m m z - g z‖ :=
                    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
                      ((hC₂ z (subset_closure hz)).trans (le_max_right _ _)) (norm_nonneg B))
                      (norm_nonneg _)
            · rw [← ofReal_norm, ← ofReal_norm,
                ← ENNReal.ofReal_mul (mul_nonneg (norm_nonneg B) hM₁)]
              refine ENNReal.ofReal_le_ofReal ?_
              calc ‖B (f_n n z) (g'_m m z - g' z)‖
                  ≤ ‖B‖ * ‖f_n n z‖ * ‖g'_m m z - g' z‖ := B.le_opNorm₂ _ _
                _ ≤ ‖B‖ * M₁ * ‖g'_m m z - g' z‖ :=
                    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
                      ((hC₁ z (subset_closure hz)).trans (le_max_right _ _)) (norm_nonneg B))
                      (norm_nonneg _)
        _ = (∫⁻ z in (W₀ : Set ℂ), ENNReal.ofReal (‖B‖ * M₂) * ‖g_m m z - g z‖ₑ) +
              ∫⁻ z in (W₀ : Set ℂ), ENNReal.ofReal (‖B‖ * M₁) * ‖g'_m m z - g' z‖ₑ :=
            lintegral_add_left' (hint_g.const_mul _) _
        _ = ENNReal.ofReal (‖B‖ * M₂) * (∫⁻ z in (W₀ : Set ℂ), ‖g_m m z - g z‖ₑ) +
              ENNReal.ofReal (‖B‖ * M₁) * ∫⁻ z in (W₀ : Set ℂ), ‖g'_m m z - g' z‖ₑ := by
            rw [lintegral_const_mul'' _ hint_g, lintegral_const_mul'' _ hint_g']
    exact hasWeakLineDerivOn_of_tendsto_lintegral_enorm_sub
      ((hg.locallyIntegrableOn.mono_set hW₀Ω).continuousOn_clm_apply W₀.isOpen.isLocallyClosed
        (B.continuous.comp_continuousOn (hfn_cont n).continuousOn))
      (((hg.locallyIntegrableOn.mono_set hW₀Ω).continuousOn_clm_apply W₀.isOpen.isLocallyClosed
          (B.continuous.comp_continuousOn (hf'n_cont n).continuousOn)).add
        ((hg.locallyIntegrableOn_deriv.mono_set hW₀Ω).continuousOn_clm_apply
          W₀.isOpen.isLocallyClosed (B.continuous.comp_continuousOn (hfn_cont n).continuousOn)))
      hweak_nm hL₁ hL₂
  let φ₀ : 𝓓(W₀, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφW₀⟩
  have hid (n : ℕ) : (∫ z, fderiv ℝ (φ : ℂ → ℝ) z v • B (f_n n z) (g z)) =
      -((∫ z, (φ : ℂ → ℝ) z • B (f'_n n z) (g z)) +
        ∫ z, (φ : ℂ → ℝ) z • B (f_n n z) (g' z)) := by
    have h := (hweak_n n).integral_lineDeriv_smul_eq_neg_integral_smul φ₀
    have hi1 : Integrable (fun z => (φ : ℂ → ℝ) z • B (f'_n n z) (g z)) volume :=
      φ₀.integrable_smul ((hg.locallyIntegrableOn.mono_set hW₀Ω).continuousOn_clm_apply
        W₀.isOpen.isLocallyClosed (B.continuous.comp_continuousOn (hf'n_cont n).continuousOn))
    have hi2 : Integrable (fun z => (φ : ℂ → ℝ) z • B (f_n n z) (g' z)) volume :=
      φ₀.integrable_smul ((hg.locallyIntegrableOn_deriv.mono_set hW₀Ω).continuousOn_clm_apply
        W₀.isOpen.isLocallyClosed (B.continuous.comp_continuousOn (hfn_cont n).continuousOn))
    simp only [φ₀, TestFunction.coe_mk, smul_add] at h
    simp_rw [(φ.contDiff.differentiable (by simp) _).lineDeriv_eq_fderiv] at h
    rwa [integral_add hi1 hi2] at h
  set K := tsupport (φ : ℂ → ℝ)
  have hKc : IsCompact K := φ.hasCompactSupport
  have hKm : MeasurableSet K := (isClosed_tsupport _).measurableSet
  have hunif : TendstoUniformlyOn f_n f atTop K :=
    ContDiffBump.tendstoUniformlyOn_normed_convolution_indicator (μ := volume) hρ0 W.isOpen
      hKc hφW (hfc.mono (subset_closure.trans hWΩ))
  have ht1 : Tendsto (fun n => ∫ z, fderiv ℝ (φ : ℂ → ℝ) z v • B (f_n n z) (g z))
      atTop (𝓝 (∫ z, fderiv ℝ (φ : ℂ → ℝ) z v • B (f z) (g z))) :=
    tendsto_integral_smul_bilin_of_tendstoUniformlyOn hKc
      ((φ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const)
      (tsupport_fderiv_apply_subset ℝ v)
      (hg.locallyIntegrableOn.integrableOn_compact_subset φ.tsupport_subset hKc)
      (fun n => (hfn_cont n).continuousOn) hunif
  have ht3 : Tendsto (fun n => ∫ z, (φ : ℂ → ℝ) z • B (f_n n z) (g' z))
      atTop (𝓝 (∫ z, (φ : ℂ → ℝ) z • B (f z) (g' z))) :=
    tendsto_integral_smul_bilin_of_tendstoUniformlyOn hKc φ.continuous subset_rfl
      (hg.locallyIntegrableOn_deriv.integrableOn_compact_subset φ.tsupport_subset hKc)
      (fun n => (hfn_cont n).continuousOn) hunif
  have ht2 : Tendsto (fun n => ∫ z, (φ : ℂ → ℝ) z • B (f'_n n z) (g z))
      atTop (𝓝 (∫ z, (φ : ℂ → ℝ) z • B (f' z) (g z))) := by
    set p' : ℝ≥0∞ := (1 - p⁻¹)⁻¹
    have hp1' : p⁻¹ ≤ 1 := le_self_add.trans hpq
    have : p.HolderConjugate p' := ⟨by rw [inv_inv, inv_one, add_tsub_cancel_of_le hp1']⟩
    have hp'q : p' ≤ q := by
      rw [← inv_inv q]
      exact ENNReal.inv_le_inv.2 <|
        (ENNReal.add_sub_cancel_left (ne_top_of_le_ne_top ENNReal.one_ne_top hp1')).symm.trans_le
          (tsub_le_tsub_right hpq p⁻¹)
    have : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.2 hKc.measure_lt_top.ne
    have hgK : MemLp g p' (volume.restrict K) :=
      (hgW.mono_measure (Measure.restrict_mono hφW le_rfl)).mono_exponent hp'q
    let a : ℂ → G := fun z => (φ : ℂ → ℝ) z • K.indicator g z
    have ha : MemLp a p' volume :=
      (ContinuousLinearMap.lsmul ℝ ℝ).memLp_of_bilin p' φ.memLp_top
        ((memLp_indicator_iff_restrict hKm.nullMeasurableSet).2 hgK)
    have hlim := B.flip.tendsto_integral_bilin_normed_convolution hρ0 ha
      ((memLp_indicator_iff_restrict hWm.nullMeasurableSet).2 hf'W)
    have hpt1 (n : ℕ) : (∫ z, B.flip (a z) (f'_n n z)) =
        ∫ z, (φ : ℂ → ℝ) z • B (f'_n n z) (g z) :=
      integral_congr_ae (.of_forall fun z => by
        by_cases hz : z ∈ K
        · simp [a, hz, map_smul]
        · simp [a, image_eq_zero_of_notMem_tsupport hz])
    have hpt2 : (∫ z, B.flip (a z) ((W : Set ℂ).indicator f' z)) =
        ∫ z, (φ : ℂ → ℝ) z • B (f' z) (g z) :=
      integral_congr_ae (.of_forall fun z => by
        by_cases hz : z ∈ K
        · simp [a, hz, hφW hz, map_smul]
        · simp [a, image_eq_zero_of_notMem_tsupport hz])
    simpa only [f'_n, hpt1, hpt2] using hlim
  have hrhs := (ht2.add ht3).neg
  have heq : (fun z => (φ : ℂ → ℝ) z • (B (f' z) (g z) + B (f z) (g' z))) =
      fun z => (φ : ℂ → ℝ) z • B (f' z) (g z) + (φ : ℂ → ℝ) z • B (f z) (g' z) :=
    funext fun z => smul_add _ _ _
  rw [heq, integral_add (φ.integrable_smul hBf'g) (φ.integrable_smul hBfg')]
  simp_rw [(φ.contDiff.differentiable (by simp) _).lineDeriv_eq_fderiv]
  exact tendsto_nhds_unique (ht1.congr fun n => hid n) hrhs

end Endpoint

/-- **The weak Leibniz rule for order-one mixed products.** For `p > 2` and `1 < q ≤ p`, let
`f ∈ L^{q'}_loc` have weak derivative `Df ∈ Lᵖ_loc`, where `q'` is the conjugate exponent of `q`,
and let `g ∈ L^q_loc` have weak derivative `Dg ∈ L^q_loc`. Then `B(f, g)` has weak derivative
`B(Df, g) + B(f, Dg)`. -/
theorem HasWeakFDerivOn.bilin_of_memLpLoc [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H)
    (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p) {f : ℂ → F} {Df : ℂ → ℂ →L[ℝ] F} {g : ℂ → G}
    {Dg : ℂ → ℂ →L[ℝ] G} (hf : HasWeakFDerivOn volume Ω f Df)
    (hfi : MemLpLoc (q : ℝ≥0∞).conjExponent Ω f)
    (hDf : MemLpLoc p Ω Df) (hg : HasWeakFDerivOn volume Ω g Dg) (hgq : MemLpLoc q Ω g)
    (hDg : MemLpLoc q Ω Dg) :
    HasWeakFDerivOn volume Ω (fun z => B (f z) (g z))
      (fun z => B.precompL ℂ (Df z) (g z) + B.precompR ℂ (f z) (Dg z)) := by
  have hq1 : (1 : ℝ≥0∞) < q := by exact_mod_cast hq
  have hp1 : (1 : ℝ≥0∞) < p := hq1.trans_le (by exact_mod_cast hqp)
  let _ : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨hq1.le⟩
  let _ : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨hp1.le⟩
  -- Exponents: `f` in `L^{q'}`, `Df` in `Lᵖ`, `g` in `L^b` with `b = max q p'`, `Dg` in `L^q`.
  set a := (q : ℝ≥0∞).conjExponent
  set p' := (p : ℝ≥0∞).conjExponent
  set b := max (q : ℝ≥0∞) p'
  have ha : a ≠ ⊤ := (ENNReal.HolderConjugate.ne_top_iff_ne_one a q).2 hq1.ne'
  have hp' : p' ≠ ⊤ := (ENNReal.HolderConjugate.ne_top_iff_ne_one p' p).2 hp1.ne'
  have hb : b ≠ ⊤ := max_ne_top ENNReal.coe_ne_top hp'
  let _ : Fact (1 ≤ a) := ⟨ENNReal.HolderConjugate.one_le a q⟩
  let _ : Fact (1 ≤ b) := ⟨hq1.le.trans (le_max_left _ _)⟩
  have haq : a⁻¹ + (q : ℝ≥0∞)⁻¹ = 1 := ENNReal.HolderConjugate.inv_add_inv_eq_one a q
  have hpp : (p : ℝ≥0∞)⁻¹ + p'⁻¹ = 1 := ENNReal.HolderConjugate.inv_add_inv_eq_one _ _
  have hbq : b⁻¹ ≤ (q : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 (le_max_left _ _)
  have hbp : b⁻¹ ≤ p'⁻¹ := ENNReal.inv_le_inv.2 (le_max_right _ _)
  -- `g` lies in `L^b_loc` because `q ≤ b ≤ r` with `1/p + 1/r = 1/q`.
  let r := ((q : ℝ≥0∞)⁻¹ - (p : ℝ≥0∞)⁻¹)⁻¹
  let _ := ENNReal.HolderTriple.of_le (p := (p : ℝ≥0∞)) (q := q) (by exact_mod_cast hqp)
  have hgr : MemLpLoc r Ω g := MemWkpLoc.memLpLoc_of_holderTriple hp hqp
    (memWkpLoc_succ_iff_of_isOpen.2 ⟨hgq, Dg, hg, memWkpLoc_zero_iff.2 hDg⟩)
  have hbr : b ≤ r := by
    refine max_le (ENNReal.inv_le_inv.1 ?_) (ENNReal.inv_le_inv.1 ?_)
    · rw [inv_inv]
      exact tsub_le_self
    · rw [inv_inv, ← ENNReal.HolderConjugate.one_sub_inv (p : ℝ≥0∞) p']
      exact tsub_le_tsub_right (ENNReal.inv_le_one.2 hq1.le) _
  have hgb : MemLpLoc b Ω g := hgr.mono_exponent hbr
  exact hf.bilin_of_memLp B ha ENNReal.coe_ne_top hb ENNReal.coe_ne_top
    ((add_le_add le_rfl hbq).trans haq.le) ((add_le_add le_rfl hbp).trans hpp.le) haq.le hg
    (fun K hK hKΩ => memLpLoc_iff.1 hfi K hKΩ hK)
    (fun K hK hKΩ => memLpLoc_iff.1 hDf K hKΩ hK)
    (fun K hK hKΩ => memLpLoc_iff.1 hgb K hKΩ hK) (fun K hK hKΩ => memLpLoc_iff.1 hDg K hKΩ hK)

/-- **Order-one mixed products.** For `p > 2` and `1 < q ≤ p`, the product of a locally bounded
`W^{1,p}_loc` map with a `W^{1,q}_loc` map with finite-dimensional values is in
`W^{1,q}_loc`. At `q = p` this is the algebra property of `W^{1,p}_loc` under continuous bilinear
maps. -/
theorem MemWkpLoc.bilin_of_memLpLoc_top [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H) (hp : 2 < p)
    (hq : 1 < q) (hqp : q ≤ p) {f : ℂ → F} {g : ℂ → G} (hf : MemWkpLoc p Ω 1 f)
    (hfi : MemLpLoc ∞ Ω f) (hg : MemWkpLoc q Ω 1 g) :
    MemWkpLoc q Ω 1 (fun z => B (f z) (g z)) := by
  let _ : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq.le⟩
  obtain ⟨Df, hDf, hDfp⟩ := hf.exists_weakFDeriv_of_isOpen
  obtain ⟨Dg, hDg, hDgq⟩ := hg.exists_weakFDeriv_of_isOpen
  have hgq := hg.memLpLoc
  rw [memWkpLoc_zero_iff] at hDfp hDgq
  have hD := hDf.bilin_of_memLpLoc B hp hq hqp (hfi.mono_exponent le_top) hDfp hDg hgq hDgq
  refine memWkpLoc_succ_iff_of_isOpen.2 ⟨memLpLoc_iff.2 fun K hKΩ hK => ?_, _, hD,
    memWkpLoc_zero_iff.2 (memLpLoc_iff.2 fun K hKΩ hK => ?_)⟩
  · exact B.memLp_of_bilin q (memLpLoc_iff.1 hfi K hKΩ hK) (memLpLoc_iff.1 hgq K hKΩ hK)
  · exact (memLpLoc_iff.1 (MemLpLoc.bilin_of_memWkpLoc (B.precompL ℂ) hp hqp hDfp hg) K hKΩ
      hK).add ((B.precompR ℂ).memLp_of_bilin q (memLpLoc_iff.1 hfi K hKΩ hK)
        (memLpLoc_iff.1 hDgq K hKΩ hK))

/-- **Order-one mixed products with finite-dimensional factors.** For `p > 2` and
`1 < q ≤ p`, the product of a `W^{1,p}_loc` map with a `W^{1,q}_loc` map, both with
finite-dimensional values, is in `W^{1,q}_loc`. The first factor is locally bounded by the local
gain of integrability at `q = p`. -/
theorem MemWkpLoc.bilin [FiniteDimensional ℝ F] [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H)
    (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p) {f : ℂ → F} {g : ℂ → G} (hf : MemWkpLoc p Ω 1 f)
    (hg : MemWkpLoc q Ω 1 g) : MemWkpLoc q Ω 1 (fun z => B (f z) (g z)) := by
  let _ : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hq.le.trans hqp⟩
  exact hf.bilin_of_memLpLoc_top B hp hq hqp (hf.memLpLoc_of_holderTriple hp le_rfl) hg

end TauCeti
