/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.GelfandTriple
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.Analysis.Sobolev.Mollification.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Function.Lp.Holder
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Function.UnifTight
import TauCeti.Analysis.Sobolev.WeakDeriv.Limit
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# The weak derivative of the positive part in a Gelfand triple over `L²`

Let `ι : V →L[ℝ] L²(ν)` be a continuous linear map from a real Banach space into a real `L²`
space, so that `V ↪ L²(ν) ↪ V*` through `ι.gelfandDual`. Suppose that `V` carries a positive part
`P : V → V` compatible with the positive part of `L²(ν)`, `ι (P w) = (ι w)⁺`, which is continuous
and does not increase the norm. The model is `V = H¹₀(Ω)` with its value map
`TauCeti.W1p0.valueL` into `L²(Ω)` and `P = TauCeti.W1p0.posPart`.

Let `u ∈ L²(Ω'; V)` be indexed by an open set `Ω'` of a finite-dimensional space, and suppose that
its image in `V*` has a weak derivative `u' ∈ L²(Ω'; V*)` in a direction `v`. This file proves the
chain rule

`∂_v ‖(ι u)⁺‖²_{L²(ν)} = 2 u'(P u)` weakly on `Ω'`

(`TauCeti.HasWeakLineDerivOn.norm_posPart_sq_of_gelfandDual`). For `Ω' ⊆ ℝ`, `v = 1` and
`V = H¹₀(Ω)` it is the identity `d/dt ‖u(t)⁺‖² = 2 ⟨u'(t), u(t)⁺⟩` for `u ∈ L²(0, T; H¹₀(Ω))` with
`u' ∈ L²(0, T; H⁻¹(Ω))`, the truncated counterpart of the energy identity
(`TauCeti.HasWeakLineDerivOn.norm_sq_of_gelfandDual`). Testing a parabolic equation against `u⁺`
with this identity is how weak maximum principles for parabolic equations are proved.

## The argument

Mollify `u` in the variable of `Ω'`: the mollifications `g = ρ ⋆ u` are smooth `V`-valued, and
`ρ ⋆ u'` is the derivative of `ι g` paired through the triple
(`TauCeti.HasWeakLineDerivOn.convolution_eq_apply_fderiv_convolution`). The map
`f ↦ ‖f⁺‖²` is differentiable on `L²(ν)` with derivative `2 ⟪f⁺, ·⟫`
(`MeasureTheory.Lp.hasFDerivAt_norm_posPart_sq`), and `(ι g)⁺ = ι (P g)`, so the classical chain
rule gives `∂_v ‖(ι g)⁺‖² = 2 (ρ ⋆ u')(P g)`. As the kernels shrink, `g → u` in `L²(Ω'; V)`. Since
`P` is continuous and does not increase the norm, Vitali's convergence theorem gives
`P g → P u` in `L²(Ω'; V)` as well (`MeasureTheory.tendsto_eLpNorm_comp_sub_comp_of_tendsto`). Both
sides of the mollified chain rule are bilinear expressions in `P g` and `ρ ⋆ u'`, so they converge
in `L¹` on relatively compact subdomains, and the weak derivative passes to the limit.

## References

* G. Stampacchia, *Le problème de Dirichlet pour les équations elliptiques du second ordre à
  coefficients discontinus*, Ann. Inst. Fourier **15** (1965), for truncation in Sobolev spaces.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.9.2, Theorem 3, whose mollification
  proof of the energy identity is adapted here.
-/

public section

open MeasureTheory Filter Set TopologicalSpace
open scoped Convolution ContDiff ENNReal Topology InnerProductSpace

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {v : E}
  {X : Type*} [MeasurableSpace X] {ν : Measure X}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  {ι : V →L[ℝ] Lp ℝ 2 ν} {P : V → V}

omit [CompleteSpace V] in
/-- The squared `L²` norm of `(ι w)⁺` is the Gelfand-triple quadratic form at `P w`. -/
private theorem norm_posPart_sq_eq_gelfandDual (hιP : ∀ w, ι (P w) = Lp.posPart (ι w)) (w : V) :
    ‖Lp.posPart (ι w)‖ ^ 2 = (ι.gelfandDual.comp ι) (P w) (P w) := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.gelfandDual_apply, hιP,
    real_inner_self_eq_norm_sq]

/-- **The chain rule for a mollified family.** Let `U` be locally integrable with values in `V`,
let its image in `V*` have weak derivative `U'` on `Ω'`, and let `ρ` be a smooth compactly supported
kernel with `x - tsupport ρ ⊆ Ω'`. Then `g = ρ ⋆ U` satisfies `∂_v ‖(ι g)⁺‖² = 2 (ρ ⋆ U')(P g)`
at `x`. -/
private theorem hasLineDerivAt_norm_posPart_sq_convolution
    (hιP : ∀ w, ι (P w) = Lp.posPart (ι w)) {U : E → V} {U' : E → StrongDual ℝ V}
    (hind : HasWeakLineDerivOn μ Ω (fun y ↦ ι.gelfandDual (ι (U y))) U' v)
    (hU : LocallyIntegrable U μ) {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    {x : E} (hx : ∀ y ∈ tsupport ρ, x - y ∈ Ω) :
    HasLineDerivAt ℝ (fun y ↦ ‖Lp.posPart (ι ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U) y))‖ ^ 2)
      (2 * (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U') x
        (P ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U) x))) x v := by
  have hkx := HasWeakLineDerivOn.convolution_eq_apply_fderiv_convolution
    (L := ι.gelfandDual.comp ι) hind hU hρ hρc hx
  have hgd : HasFDerivAt (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U)
      (fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U) x) x :=
    ((hρc.contDiff_convolution_left _ (hρ.of_le (by simp)) hU :
      ContDiff ℝ 1 (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U)).differentiable one_ne_zero
        x).hasFDerivAt
  have hF := (Lp.hasFDerivAt_norm_posPart_sq
    (ι ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U) x))).comp x (ι.hasFDerivAt.comp x hgd)
  rw [hkx]
  convert hF.hasLineDerivAt v using 1
  · rfl
  · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.gelfandDual_apply, hιP,
      smul_apply, innerSL_apply_apply, smul_eq_mul]
    rw [real_inner_comm]

/-- **The mollified chain rule holds weakly on a subdomain.** Let `U` and `U'` be locally
integrable, let the image of `U` in `V*` have weak derivative `U'` on `Ω'`, and let `ρ` be a
normalized bump kernel with `x - tsupport ρ ⊆ Ω'` for every `x ∈ W`. Then
`y ↦ ‖(ι (g y))⁺‖²` has weak derivative `2 (ρ ⋆ U')(P (g y))` on `W`, where `g = ρ ⋆ U`. -/
private theorem hasWeakLineDerivOn_norm_posPart_sq_convolution (hP : Continuous P)
    (hιP : ∀ w, ι (P w) = Lp.posPart (ι w)) {U : E → V} {U' : E → StrongDual ℝ V}
    (hind : HasWeakLineDerivOn μ Ω (fun y ↦ ι.gelfandDual (ι (U y))) U' v)
    (hUloc : LocallyIntegrable U μ) (hU'loc : LocallyIntegrable U' μ) {W : Opens E}
    {ρ : ContDiffBump (0 : E)}
    (hsupp : ∀ x ∈ (W : Set E), ∀ y ∈ tsupport (ρ.normed μ), x - y ∈ Ω) :
    HasWeakLineDerivOn μ W
      (fun y ↦ ‖Lp.posPart (ι ((ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U) y))‖ ^ 2)
      (fun y ↦ 2 * (ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U') y
        (P ((ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U) y))) v := by
  have hgc : Continuous (ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U) :=
    ρ.hasCompactSupport_normed.continuous_convolution_left _ ρ.continuous_normed hUloc
  have hkc : Continuous (ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U') :=
    ρ.hasCompactSupport_normed.continuous_convolution_left _ ρ.continuous_normed hU'loc
  refine hasWeakLineDerivOn_of_hasLineDerivAt ?_ ?_ fun x hx ↦
    hasLineDerivAt_norm_posPart_sq_convolution hιP hind hUloc ρ.contDiff_normed
      ρ.hasCompactSupport_normed (hsupp x hx)
  · exact ((Lp.continuous_posPart.comp (ι.continuous.comp hgc)).norm.pow 2
      ).locallyIntegrable.locallyIntegrableOn _
  · exact (continuous_const.mul ((ContinuousLinearMap.id ℝ (StrongDual ℝ V)).continuous₂.comp
      (hkc.prodMk (hP.comp hgc)))).locallyIntegrable.locallyIntegrableOn _

/-- **The weak chain rule for the positive part in a Gelfand triple over `L²`.** Let
`ι : V →L[ℝ] L²(ν)`, and let `P : V → V` be continuous with `‖P w‖ ≤ ‖w‖` and `ι (P w) = (ι w)⁺`.
Let `u ∈ L²(Ω'; V)`, and suppose that its image in `V*` under `V → L²(ν) → V*` has weak derivative
`u' ∈ L²(Ω'; V*)` in the direction `v` on `Ω'`. Then `x ↦ ‖(ι (u x))⁺‖²` has weak derivative
`x ↦ 2 u'(x)(P (u x))` in the direction `v` on `Ω'`. -/
theorem HasWeakLineDerivOn.norm_posPart_sq_of_gelfandDual (hP : Continuous P)
    (hPb : ∀ w, ‖P w‖ ≤ ‖w‖) (hιP : ∀ w, ι (P w) = Lp.posPart (ι w)) {u : E → V}
    {u' : E → StrongDual ℝ V} (h : HasWeakLineDerivOn μ Ω (fun x ↦ ι.gelfandDual (ι (u x))) u' v)
    (hu : MemLp u 2 (μ.restrict Ω)) (hu' : MemLp u' 2 (μ.restrict Ω)) :
    HasWeakLineDerivOn μ Ω (fun x ↦ ‖Lp.posPart (ι (u x))‖ ^ 2) (fun x ↦ 2 * u' x (P (u x))) v := by
  have hΩm : NullMeasurableSet (Ω : Set E) μ := Ω.isOpen.measurableSet.nullMeasurableSet
  have hP0 : P 0 = 0 := norm_le_zero_iff.1 ((hPb 0).trans_eq norm_zero)
  -- Extend `u` and `u'` by zero; the extensions are `L²` on the whole space.
  set U : E → V := (Ω : Set E).indicator u
  set U' : E → StrongDual ℝ V := (Ω : Set E).indicator u'
  have hU : MemLp U 2 μ := (memLp_indicator_iff_restrict (f := u) hΩm).2 hu
  have hU' : MemLp U' 2 μ := (memLp_indicator_iff_restrict (f := u') hΩm).2 hu'
  have hUloc : LocallyIntegrable U μ := hU.locallyIntegrable one_le_two
  have hU'loc : LocallyIntegrable U' μ := hU'.locallyIntegrable one_le_two
  have hind : HasWeakLineDerivOn μ Ω (fun x ↦ ι.gelfandDual (ι (U x))) U' v := by
    have hLU : (fun x ↦ ι.gelfandDual (ι (U x))) =
        (Ω : Set E).indicator fun x ↦ ι.gelfandDual (ι (u x)) := by
      ext1 x
      by_cases hx : x ∈ (Ω : Set E) <;> simp [U, hx]
    rw [hLU]
    exact h.indicator
  -- `P ∘ u` is square integrable on `Ω`, and `P ∘ U` is its extension by zero.
  have hPu : MemLp (fun x ↦ P (u x)) 2 (μ.restrict Ω) :=
    hu.mono (hP.comp_aestronglyMeasurable hu.aestronglyMeasurable)
      (Eventually.of_forall fun x ↦ hPb (u x))
  have hPU_eq : (fun x ↦ P (U x)) = (Ω : Set E).indicator fun x ↦ P (u x) := by
    ext1 x
    by_cases hx : x ∈ (Ω : Set E) <;> simp [U, hx, hP0]
  have hPU : MemLp ((Ω : Set E).indicator fun x ↦ P (u x)) 2 μ :=
    (memLp_indicator_iff_restrict hΩm).2 hPu
  -- The limits are integrable on `Ω`.
  have hlim : IntegrableOn (fun x ↦ ‖Lp.posPart (ι (u x))‖ ^ 2) Ω μ := by
    have := memLp_one_iff_integrable.1 ((ι.gelfandDual.comp ι).memLp_of_bilin 1 hPu hPu)
    simp only [← norm_posPart_sq_eq_gelfandDual hιP] at this
    exact this
  have hlim' : IntegrableOn (fun x ↦ 2 * u' x (P (u x))) Ω μ :=
    (memLp_one_iff_integrable.1 ((ContinuousLinearMap.id ℝ (StrongDual ℝ V)).memLp_of_bilin 1
      hu' hPu)).const_mul 2
  rw [hasWeakLineDerivOn_iff_forall_isCompact_closure]
  intro W hWc hWΩ
  have hWΩ' : (W : Set E) ⊆ Ω := subset_closure.trans hWΩ
  have hWμ : μ (W : Set E) < ⊤ := lt_of_le_of_lt (measure_mono subset_closure)
    hWc.measure_lt_top
  obtain ⟨φ, hφ, hsupp⟩ := ContDiffBump.exists_seq_sub_tsupport_subset (μ := μ) hWc hWΩ
  set g : ℕ → E → V := fun n ↦ (φ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U
  set k : ℕ → E → StrongDual ℝ V := fun n ↦
    (φ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U'
  -- Each mollified family satisfies the chain rule classically on `W`.
  have hweak (n : ℕ) : HasWeakLineDerivOn μ W (fun y ↦ ‖Lp.posPart (ι (g n y))‖ ^ 2)
      (fun y ↦ 2 * k n y (P (g n y))) v :=
    hasWeakLineDerivOn_norm_posPart_sq_convolution hP hιP hind hUloc hU'loc (hsupp n)
  -- The mollifications converge in `L²`, and by Vitali so do their positive parts.
  have hgLp (n : ℕ) : normedBumpLp ENNReal.ofNat_ne_top (φ n) μ (hU.toLp U) =ᵐ[μ] g n :=
    normedBumpLp_ae_eq_convolution ENNReal.ofNat_ne_top (φ n) hU
  have hkLp (n : ℕ) : normedBumpLp ENNReal.ofNat_ne_top (φ n) μ (hU'.toLp U') =ᵐ[μ] k n :=
    normedBumpLp_ae_eq_convolution ENNReal.ofNat_ne_top (φ n) hU'
  have hkt := tendsto_normedBumpLp (mu := μ) ENNReal.ofNat_ne_top hφ (hU'.toLp U')
  have hgmem (n : ℕ) : MemLp (g n) 2 μ := (Lp.memLp _).ae_eq (hgLp n)
  have hgconv : Tendsto (fun n ↦ eLpNorm (g n - U) 2 μ) atTop (𝓝 0) :=
    tendsto_eLpNorm_normed_convolution_sub ENNReal.ofNat_ne_top hφ hU
  have hPgmem (n : ℕ) : MemLp (fun x ↦ P (g n x)) 2 μ :=
    (hgmem n).mono (hP.comp_aestronglyMeasurable (hgmem n).aestronglyMeasurable)
      (Eventually.of_forall fun x ↦ hPb (g n x))
  have hPgt : Tendsto (fun n ↦ (hPgmem n).toLp fun x ↦ P (g n x)) atTop
      (𝓝 (hPU.toLp ((Ω : Set E).indicator fun x ↦ P (u x)))) := by
    refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hPgmem _ hPU).2 ?_
    rw [← hPU_eq]
    exact tendsto_eLpNorm_comp_sub_comp_of_tendsto one_le_two ENNReal.ofNat_ne_top hP hPb hgmem hU
      hgconv
  have hPext := hPU.coeFn_toLp_indicator_restrict W.isOpen.measurableSet hWΩ'
  have hext' := hU'.coeFn_toLp_indicator_restrict W.isOpen.measurableSet hWΩ'
  -- Both sides of the mollified chain rule are bilinear in `P g` and `k`, so they converge.
  refine hasWeakLineDerivOn_of_tendsto_lintegral_enorm_sub (l := atTop)
    (hlim.mono_set hWΩ').locallyIntegrableOn (hlim'.mono_set hWΩ').locallyIntegrableOn hweak ?_ ?_
  · simpa only [norm_posPart_sq_eq_gelfandDual hιP] using
      tendsto_setLIntegral_enorm_bilin_sub (r := 1) (ι.gelfandDual.comp ι) hWμ hPgt hPgt
        (fun n ↦ (hPgmem n).coeFn_toLp) hPext (fun n ↦ (hPgmem n).coeFn_toLp) hPext
  · refine (tendsto_setLIntegral_enorm_bilin_sub (r := 1)
      ((2 : ℝ) • ContinuousLinearMap.id ℝ (StrongDual ℝ V)) hWμ hkt hPgt hkLp hext'
      (fun n ↦ (hPgmem n).coeFn_toLp) hPext).congr fun n ↦ ?_
    simp

end TauCeti
