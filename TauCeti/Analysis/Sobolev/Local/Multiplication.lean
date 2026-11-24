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
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Calculus.LineDeriv.Bilinear
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Normed.Operator.Bilinear
import TauCeti.Analysis.Sobolev.Mollification.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Holder
import TauCeti.Analysis.Sobolev.WeakDeriv.Limit
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.Data.ENNReal.Holder
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity

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
* `TauCeti.HasWeakLineDerivOn.bilin_of_continuousOn` and
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

section Endpoint

open Filter Set
open scoped Convolution Distributions LineDeriv Topology

omit [FiniteDimensional ℝ G] in
/-- If `f₀` is bounded on a measurable set `s` and `g_m → g` in `L¹(s)`, then `B(f₀, g_m) →
B(f₀, g)` in `L¹(s)`. -/
private theorem tendsto_setLIntegral_enorm_bilin_sub_of_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α} (hs : MeasurableSet s)
    (B : F →L[ℝ] G →L[ℝ] H) {f₀ : α → F} {C : ℝ} (hC : ∀ x ∈ s, ‖f₀ x‖ ≤ C)
    {ι : Type*} {l : Filter ι} {g_m : ι → α → G} {g : α → G}
    (hg : Tendsto (fun m => ∫⁻ x in s, ‖g_m m x - g x‖ₑ ∂μ) l (𝓝 0)) :
    Tendsto (fun m => ∫⁻ x in s, ‖B (f₀ x) (g_m m x) - B (f₀ x) (g x)‖ₑ ∂μ) l (𝓝 0) := by
  have hmul : Tendsto (fun m => ENNReal.ofReal (‖B‖ * C) * ∫⁻ x in s, ‖g_m m x - g x‖ₑ ∂μ)
      l (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hg (Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul (fun _ => zero_le)
    fun m => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono_ae' hs (.of_forall fun x hx => ?_)
  rw [← ContinuousLinearMap.map_sub]
  exact B.enorm_apply_apply_le_of_norm_le (hC x hx)

omit [FiniteDimensional ℝ G] in
/-- Extending a locally integrable field on `Ω` by zero outside a relatively compact open subset
`W` with `closure W ⊆ Ω` gives an integrable function. -/
private theorem integrable_indicator_of_locallyIntegrableOn {X : Type*} [NormedAddCommGroup X]
    {W : Opens ℂ} (hWΩ : closure (W : Set ℂ) ⊆ Ω) (hWc : IsCompact (closure (W : Set ℂ)))
    {u : ℂ → X} (hu : LocallyIntegrableOn u Ω volume) :
    Integrable ((W : Set ℂ).indicator u) volume :=
  (integrable_indicator_iff W.isOpen.measurableSet).2
    ((hu.integrableOn_compact_subset hWΩ hWc).mono_set subset_closure)

omit [FiniteDimensional ℝ G] in
/-- Convolution of `1_W u` with a normed bump is continuous. -/
private theorem continuous_normed_convolution_indicator {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] (ρ : ContDiffBump (0 : ℂ))
    (W : Set ℂ) {u : ℂ → X} (hu : Integrable (W.indicator u) volume) :
    Continuous (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] W.indicator u) :=
  ρ.hasCompactSupport_normed.continuous_convolution_left _ ρ.continuous_normed hu.locallyIntegrable

omit [FiniteDimensional ℝ G] in
/-- Normed bump mollifications of `1_W u` converge to `u` in `L¹(W₀)` when `W₀ ⊆ W`. -/
private theorem tendsto_lintegral_enorm_normed_convolution_sub_of_subset {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] {W₀ W : Opens ℂ}
    (hW₀W : (W₀ : Set ℂ) ⊆ W) {ρ : ℕ → ContDiffBump (0 : ℂ)}
    (hρ0 : Tendsto (fun m => (ρ m).rOut) atTop (𝓝 0)) {u : ℂ → X}
    (hu : Integrable ((W : Set ℂ).indicator u) volume) :
    Tendsto (fun m => ∫⁻ z in (W₀ : Set ℂ),
        ‖((ρ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (W : Set ℂ).indicator u) z - u z‖ₑ) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_lintegral_enorm_normed_convolution_sub hρ0 hu) (fun _ => zero_le) fun m => by
      refine (setLIntegral_mono_ae' W₀.isOpen.measurableSet (.of_forall fun z hz => ?_)).trans
        (setLIntegral_le_lintegral _ _)
      rw [Set.indicator_of_mem (hW₀W hz)]

omit [FiniteDimensional ℝ G] in
/-- Stage 1 of the endpoint weak Leibniz rule: if `f₀` is continuous and has continuous directional
derivative `f'₀` along `v` on `W₀`, and `g` has weak directional derivative `g'` on `Ω`, then
`B(f₀, g)` has weak directional derivative `B(f'₀, g) + B(f₀, g')` on `W₀`, obtained by mollifying
`(g, g')` on a larger relatively compact open set `W` and passing to the `L¹(W₀)` limit. -/
private theorem hasWeakLineDerivOn_bilin_of_hasLineDerivAt_left
    [CompleteSpace G] [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H)
    {v : ℂ} {W₀ W : Opens ℂ} (hW₀W : closure (W₀ : Set ℂ) ⊆ W)
    (hW₀c : IsCompact (closure (W₀ : Set ℂ))) (hWΩ : closure (W : Set ℂ) ⊆ Ω)
    {ρ : ℕ → ContDiffBump (0 : ℂ)} (hρ0 : Tendsto (fun m => (ρ m).rOut) atTop (𝓝 0))
    (hball : ∀ m, ∀ x ∈ (W₀ : Set ℂ), ∀ y ∈ tsupport ((ρ m).normed volume), x - y ∈ W)
    {f₀ f'₀ : ℂ → F} (hf₀c : Continuous f₀) (hf'₀c : Continuous f'₀)
    (hfd : ∀ x ∈ (W₀ : Set ℂ), HasLineDerivAt ℝ f₀ (f'₀ x) x v)
    {g g' : ℂ → G} (hg : HasWeakLineDerivOn volume Ω g g' v)
    (hg_int : Integrable ((W : Set ℂ).indicator g) volume)
    (hg'_int : Integrable ((W : Set ℂ).indicator g') volume) :
    HasWeakLineDerivOn volume W₀ (fun z => B (f₀ z) (g z))
      (fun z => B (f'₀ z) (g z) + B (f₀ z) (g' z)) v := by
  let g_m (m : ℕ) :=
    (ρ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator g
  let g'_m (m : ℕ) :=
    (ρ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator g'
  have hgm_cont (m : ℕ) : Continuous (g_m m) :=
    continuous_normed_convolution_indicator (ρ m) W hg_int
  have hg'm_cont (m : ℕ) : Continuous (g'_m m) :=
    continuous_normed_convolution_indicator (ρ m) W hg'_int
  have hW₀Ω : (W₀ : Set ℂ) ⊆ Ω := subset_closure.trans (hW₀W.trans (subset_closure.trans hWΩ))
  have hW₀W' : (W₀ : Set ℂ) ⊆ W := subset_closure.trans hW₀W
  -- Classical Leibniz rule for `(f₀, g_m)` on `W₀`.
  have hweak_m (m : ℕ) : HasWeakLineDerivOn volume W₀ (fun z => B (f₀ z) (g_m m z))
      (fun z => B (f'₀ z) (g_m m z) + B (f₀ z) (g'_m m z)) v := by
    refine hasWeakLineDerivOn_of_hasLineDerivAt
      ((B.continuous₂.comp (hf₀c.prodMk (hgm_cont m))).locallyIntegrable.locallyIntegrableOn _)
      (((B.continuous₂.comp (hf'₀c.prodMk (hgm_cont m))).add
        (B.continuous₂.comp (hf₀c.prodMk (hg'm_cont m)))).locallyIntegrable.locallyIntegrableOn _)
      fun x hx => ?_
    have hgd := ((hg.mono (subset_closure.trans hWΩ)).indicator).hasLineDerivAt_convolution_right
      hg_int.locallyIntegrable _ (ρ m).contDiff_normed (ρ m).hasCompactSupport_normed x
      (hball m x hx)
    rw [convolution_flip, convolution_flip] at hgd
    exact (hfd x hx).clm_bilin B hgd
  -- Local integrability of the limit functions and `L¹(W₀)` convergence of `B(f₀, g_m)` and
  -- `B(f'₀, g_m) + B(f₀, g'_m)`.
  have hBf_g := (hg.locallyIntegrableOn.mono_set hW₀Ω).continuousOn_clm_apply
    W₀.isOpen.isLocallyClosed (B.continuous.comp_continuousOn hf₀c.continuousOn)
  have hBf'_g := (hg.locallyIntegrableOn.mono_set hW₀Ω).continuousOn_clm_apply
    W₀.isOpen.isLocallyClosed (B.continuous.comp_continuousOn hf'₀c.continuousOn)
  have hBf_g' := (hg.locallyIntegrableOn_deriv.mono_set hW₀Ω).continuousOn_clm_apply
    W₀.isOpen.isLocallyClosed (B.continuous.comp_continuousOn hf₀c.continuousOn)
  obtain ⟨C₁, hC₁⟩ := hW₀c.exists_bound_of_continuousOn hf₀c.continuousOn
  obtain ⟨C₂, hC₂⟩ := hW₀c.exists_bound_of_continuousOn hf'₀c.continuousOn
  have hC₁' : ∀ z ∈ (W₀ : Set ℂ), ‖f₀ z‖ ≤ C₁ := fun z hz => hC₁ z (subset_closure hz)
  have hC₂' : ∀ z ∈ (W₀ : Set ℂ), ‖f'₀ z‖ ≤ C₂ := fun z hz => hC₂ z (subset_closure hz)
  have hgm_lim := tendsto_lintegral_enorm_normed_convolution_sub_of_subset hW₀W' hρ0 hg_int
  have hg'm_lim := tendsto_lintegral_enorm_normed_convolution_sub_of_subset hW₀W' hρ0 hg'_int
  have hL₁ := tendsto_setLIntegral_enorm_bilin_sub_of_bound W₀.isOpen.measurableSet B hC₁' hgm_lim
  have hL₂ : Tendsto (fun m => ∫⁻ z in (W₀ : Set ℂ),
      ‖(B (f'₀ z) (g_m m z) + B (f₀ z) (g'_m m z)) -
        (B (f'₀ z) (g z) + B (f₀ z) (g' z))‖ₑ) atTop (𝓝 0) := by
    have hm1 :=
      tendsto_setLIntegral_enorm_bilin_sub_of_bound W₀.isOpen.measurableSet B hC₂' hgm_lim
    have hm2 :=
      tendsto_setLIntegral_enorm_bilin_sub_of_bound W₀.isOpen.measurableSet B hC₁' hg'm_lim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hm1.add hm2) (fun _ => zero_le) fun m => ?_
    have hint : AEMeasurable (fun z => ‖B (f'₀ z) (g_m m z) - B (f'₀ z) (g z)‖ₑ)
        (volume.restrict (W₀ : Set ℂ)) :=
      ((B.continuous₂.comp (hf'₀c.prodMk (hgm_cont m))).aestronglyMeasurable.sub
        hBf'_g.aestronglyMeasurable).eNorm
    calc ∫⁻ z in (W₀ : Set ℂ),
          ‖(B (f'₀ z) (g_m m z) + B (f₀ z) (g'_m m z)) -
            (B (f'₀ z) (g z) + B (f₀ z) (g' z))‖ₑ
        ≤ ∫⁻ z in (W₀ : Set ℂ),
            (‖B (f'₀ z) (g_m m z) - B (f'₀ z) (g z)‖ₑ +
              ‖B (f₀ z) (g'_m m z) - B (f₀ z) (g' z)‖ₑ) := by
          refine setLIntegral_mono_ae' W₀.isOpen.measurableSet (.of_forall fun z _ => ?_)
          have hsub : (B (f'₀ z) (g_m m z) + B (f₀ z) (g'_m m z)) -
              (B (f'₀ z) (g z) + B (f₀ z) (g' z)) =
              (B (f'₀ z) (g_m m z) - B (f'₀ z) (g z)) +
                (B (f₀ z) (g'_m m z) - B (f₀ z) (g' z)) := by abel
          rw [hsub]
          exact eNorm_add_le _ _
      _ = (∫⁻ z in (W₀ : Set ℂ), ‖B (f'₀ z) (g_m m z) - B (f'₀ z) (g z)‖ₑ) +
            ∫⁻ z in (W₀ : Set ℂ), ‖B (f₀ z) (g'_m m z) - B (f₀ z) (g' z)‖ₑ :=
          lintegral_add_left' hint _
  exact hasWeakLineDerivOn_of_tendsto_lintegral_enorm_sub
    hBf_g (hBf'_g.add hBf_g') hweak_m hL₁ hL₂

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
  -- Two-stage mollify-and-pass-to-limit on nested relatively compact neighborhoods `W₀ ⋐ W ⋐ Ω`
  -- around `tsupport φ`.
  obtain ⟨W, hφW, hWΩ, hWc⟩ :=
    Opens.exists_between_and_isCompact_closure φ.hasCompactSupport φ.tsupport_subset
  obtain ⟨W₀, hφW₀, hW₀W, hW₀c⟩ :=
    Opens.exists_between_and_isCompact_closure φ.hasCompactSupport hφW
  obtain ⟨ρ, hρ0, hball⟩ := ContDiffBump.exists_seq_sub_tsupport_subset (μ := volume) hW₀c hW₀W
  have hf_int := integrable_indicator_of_locallyIntegrableOn hWΩ hWc hf.locallyIntegrableOn
  have hf'_int := integrable_indicator_of_locallyIntegrableOn hWΩ hWc hf.locallyIntegrableOn_deriv
  have hg_int := integrable_indicator_of_locallyIntegrableOn hWΩ hWc hg.locallyIntegrableOn
  have hg'_int := integrable_indicator_of_locallyIntegrableOn hWΩ hWc hg.locallyIntegrableOn_deriv
  have hf'W : MemLp f' p (volume.restrict W) := hf'p.memLp_restrict_of_isCompact_closure hWc hWΩ
  have hgW : MemLp g q (volume.restrict W) := hgq.memLp_restrict_of_isCompact_closure hWc hWΩ
  let f_n (n : ℕ) :=
    (ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator f
  let f'_n (n : ℕ) :=
    (ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator f'
  have hfn_cont (n : ℕ) : Continuous (f_n n) :=
    continuous_normed_convolution_indicator (ρ n) W hf_int
  have hf'n_cont (n : ℕ) : Continuous (f'_n n) :=
    continuous_normed_convolution_indicator (ρ n) W hf'_int
  have hW₀Ω : (W₀ : Set ℂ) ⊆ Ω := subset_closure.trans (hW₀W.trans (subset_closure.trans hWΩ))
  -- Stage 1: mollify `g` and pass `m → ∞` in `L¹(W₀)` to get the weak Leibniz rule for `(f_n, g)`.
  have hweak_n (n : ℕ) : HasWeakLineDerivOn volume W₀ (fun z => B (f_n n z) (g z))
      (fun z => B (f'_n n z) (g z) + B (f_n n z) (g' z)) v :=
    hasWeakLineDerivOn_bilin_of_hasLineDerivAt_left B hW₀W hW₀c hWΩ hρ0 hball
      (hfn_cont n) (hf'n_cont n) (fun x hx => by
        have hfd := ((hf.mono (subset_closure.trans hWΩ)).indicator
          ).hasLineDerivAt_convolution_right hf_int.locallyIntegrable _ (ρ n).contDiff_normed
          (ρ n).hasCompactSupport_normed x (hball n x hx)
        rwa [convolution_flip, convolution_flip] at hfd)
      hg hg_int hg'_int
  -- Stage 2: test against `φ` and pass `n → ∞` using `f_n → f` uniformly on `tsupport φ` (`ht1`,
  -- `ht3`) and `f'_n → f'` weakly in `Lᵖ(W)` against `φ • g ∈ L^{p'}` (`ht2`).
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
    simp only [TestFunction.lineDeriv_eq_fderiv] at h
    rwa [integral_add hi1 hi2] at h
  have hunif : TendstoUniformlyOn f_n f atTop (tsupport (φ : ℂ → ℝ)) :=
    ContDiffBump.tendstoUniformlyOn_normed_convolution_indicator (μ := volume) hρ0 W.isOpen
      φ.hasCompactSupport hφW (hfc.mono (subset_closure.trans hWΩ))
  let P : ℝ →L[ℝ] H →L[ℝ] H := ContinuousLinearMap.lsmul ℝ ℝ
  have ht1 : Tendsto (fun n => ∫ z, fderiv ℝ (φ : ℂ → ℝ) z v • B (f_n n z) (g z))
      atTop (𝓝 (∫ z, fderiv ℝ (φ : ℂ → ℝ) z v • B (f z) (g z))) := by
    simpa only [P, TestFunction.lineDerivOp_apply_eq_fderiv, ContinuousLinearMap.lsmul_apply,
        Function.comp_apply] using
      (∂_{v} φ).tendsto_integral_bilin_clm_of_tendstoUniformlyOn P hg.locallyIntegrableOn
        (.of_forall fun n => B.continuous.comp_continuousOn (hfn_cont n).continuousOn)
        (B.uniformContinuous.comp_tendstoUniformlyOn (hunif.mono (φ.tsupport_lineDerivOp_subset v)))
  have ht3 : Tendsto (fun n => ∫ z, (φ : ℂ → ℝ) z • B (f_n n z) (g' z))
      atTop (𝓝 (∫ z, (φ : ℂ → ℝ) z • B (f z) (g' z))) := by
    simpa only [P, ContinuousLinearMap.lsmul_apply, Function.comp_apply] using
      φ.tendsto_integral_bilin_clm_of_tendstoUniformlyOn P hg.locallyIntegrableOn_deriv
        (.of_forall fun n => B.continuous.comp_continuousOn (hfn_cont n).continuousOn)
        (B.uniformContinuous.comp_tendstoUniformlyOn hunif)
  have ht2 : Tendsto (fun n => ∫ z, (φ : ℂ → ℝ) z • B (f'_n n z) (g z))
      atTop (𝓝 (∫ z, (φ : ℂ → ℝ) z • B (f' z) (g z))) := by
    simpa only [P, f'_n, ContinuousLinearMap.lsmul_apply] using
      φ.tendsto_integral_bilin_normed_convolution P B hpq
        W.isOpen.measurableSet.nullMeasurableSet hφW hf'W hgW hρ0
  have hrhs := (ht2.add ht3).neg
  have heq : (fun z => (φ : ℂ → ℝ) z • (B (f' z) (g z) + B (f z) (g' z))) =
      fun z => (φ : ℂ → ℝ) z • B (f' z) (g z) + (φ : ℂ → ℝ) z • B (f z) (g' z) :=
    funext fun z => smul_add _ _ _
  rw [heq, integral_add (φ.integrable_smul hBf'g) (φ.integrable_smul hBfg')]
  simp only [TestFunction.lineDeriv_eq_fderiv]
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
