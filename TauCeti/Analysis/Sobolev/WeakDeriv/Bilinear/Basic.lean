/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.GelfandTriple
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.MeasureTheory.Function.Lp.Holder
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Convolution.Basic
import TauCeti.Analysis.Sobolev.Mollification.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Limit
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.MeasureTheory.Function.Holder

/-!
# Weak product rules for symmetric bilinear forms

Let `B : V →L[ℝ] V →L[ℝ] ℝ` be a continuous symmetric bilinear form on a real Banach space `V`,
and let `u : E → V` be square integrable on an open set `Ω` of a finite-dimensional space `E`.
Suppose that the `V*`-valued function `x ↦ B (u x)` has a weak derivative `u'` in a direction
`v`, square integrable on `Ω`. This file proves the product rule

`∂_v B(u, u) = 2 u'(u)` weakly on `Ω`

(`TauCeti.HasWeakLineDerivOn.bilin_self`). Neither `u` itself nor `x ↦ B(u x, u x)` is assumed to
be differentiable in any sense: only the image of `u` in `V*` has a derivative, and it is paired
back with `u`.

Polarization gives the mixed rule `∂_v B(u, w) = u'(w) + w'(u)`
(`TauCeti.HasWeakLineDerivOn.bilin`).

The case of interest is a Gelfand triple `V ↪ H ↪ V*` given by `ι : V →L[ℝ] H`, with
`B(x, y) = ⟪ι x, ι y⟫`. Then the rule reads `∂_v ‖ι u‖² = 2 u'(u)`
(`TauCeti.HasWeakLineDerivOn.norm_sq_of_gelfandDual`). For `E = ℝ` and `v = 1` this is the
identity `d/dt ‖u(t)‖²_H = 2 ⟨u'(t), u(t)⟩` for `u ∈ L²(0, T; V)` with `u' ∈ L²(0, T; V*)`, the
energy identity behind existence and uniqueness for linear parabolic equations.

## Main declarations

* `TauCeti.HasWeakLineDerivOn.bilin`: the mixed product rule for two functions.
* `TauCeti.HasWeakLineDerivOn.bilin_self`: the weak product rule `∂_v B(u, u) = 2 u'(u)`.
* `TauCeti.HasWeakLineDerivOn.norm_sq_of_gelfandDual`: its Gelfand-triple form
  `∂_v ‖ι u‖² = 2 u'(u)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.9.2, Theorem 3.
* E. Zeidler, *Nonlinear Functional Analysis and its Applications II/A*, Chapter 23.
-/

public section

open MeasureTheory Filter Set TopologicalSpace Metric
open scoped Convolution ContDiff ENNReal Topology InnerProductSpace

namespace TauCeti

variable {E V : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] {Ω : Opens E} {v : E}

/-- **The product rule for a mollified quadratic form.** Let `U` be locally integrable, let the
`V*`-valued function `y ↦ B (U y)` have weak derivative `U'` on `Ω`, and let `ρ` be a smooth
compactly supported kernel with `x - tsupport ρ ⊆ Ω`. Then `g = ρ ⋆ U` satisfies
`∂_v B(g, g) = 2 (ρ ⋆ U')(g)` at `x`. -/
private theorem hasLineDerivAt_bilin_self_convolution {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : B.flip = B)
    {U : E → V} {U' : E → StrongDual ℝ V} (hind : HasWeakLineDerivOn μ Ω (fun y ↦ B (U y)) U' v)
    (hU : LocallyIntegrable U μ) {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    {x : E} (hx : ∀ y ∈ tsupport ρ, x - y ∈ Ω) :
    HasLineDerivAt ℝ
      (fun y ↦ B ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U) y)
        ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U) y))
      (2 * (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U') x
        ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U) x)) x v := by
  set g := ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U with hg_def
  have hgd : HasFDerivAt g (fderiv ℝ g x) x :=
    ((hρc.contDiff_convolution_left _ (hρ.of_le (by simp)) hU :
      ContDiff ℝ 1 g).differentiable one_ne_zero x).hasFDerivAt
  -- `B ∘ g` is the mollification of `B ∘ U`, so its derivative is the mollification of `U'`.
  have hBg : (fun y ↦ B (g y)) =
      (fun y ↦ B (U y)) ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, μ] ρ := by
    ext1 y
    rw [convolution_flip, hg_def,
      B.convolution_lsmul_comp_comm (hρc.convolutionExists_left _ hρ.continuous hU y)]
  have h₁ : HasLineDerivAt ℝ (fun y ↦ B (g y))
      ((U' ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, μ] ρ) x) x v := by
    rw [hBg]
    exact hind.hasLineDerivAt_convolution_right
      (fun y ↦ B.integrableAtFilter_comp (hU y)) ρ hρ hρc x hx
  have hkx : (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U') x = B (fderiv ℝ g x v) := by
    rw [← convolution_flip]
    exact h₁.unique ((B.hasFDerivAt.comp x hgd).hasLineDerivAt v)
  convert (B.hasFDerivAt_of_bilinear hgd hgd).hasLineDerivAt v using 1
  have hsymm : B (g x) (fderiv ℝ g x v) = B (fderiv ℝ g x v) (g x) := by
    rw [← ContinuousLinearMap.flip_apply B, hB]
  simp [hkx, hsymm, two_mul]

/-- **The weak product rule for a quadratic form.** Let `B` be a continuous symmetric bilinear
form on `V`, and let `u ∈ L²(Ω; V)`. If the `V*`-valued function `x ↦ B (u x)` has weak derivative
`u' ∈ L²(Ω; V*)` in the direction `v` on `Ω`, then `x ↦ B (u x) (u x)` has weak derivative
`x ↦ 2 u'(x)(u x)` in the direction `v` on `Ω`. -/
theorem HasWeakLineDerivOn.bilin_self {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : B.flip = B) {u : E → V}
    {u' : E → StrongDual ℝ V} (h : HasWeakLineDerivOn μ Ω (fun x ↦ B (u x)) u' v)
    (hu : MemLp u 2 (μ.restrict Ω)) (hu' : MemLp u' 2 (μ.restrict Ω)) :
    HasWeakLineDerivOn μ Ω (fun x ↦ B (u x) (u x)) (fun x ↦ 2 * u' x (u x)) v := by
  have hΩm : NullMeasurableSet (Ω : Set E) μ := Ω.isOpen.measurableSet.nullMeasurableSet
  -- Extend `u` and `u'` by zero; the extensions are `L²` on the whole space.
  set U : E → V := (Ω : Set E).indicator u with hU_def
  set U' : E → StrongDual ℝ V := (Ω : Set E).indicator u' with hU'_def
  have hU : MemLp U 2 μ := (memLp_indicator_iff_restrict (f := u) hΩm).2 hu
  have hU' : MemLp U' 2 μ := (memLp_indicator_iff_restrict (f := u') hΩm).2 hu'
  have hUloc : LocallyIntegrable U μ := hU.locallyIntegrable one_le_two
  have hU'loc : LocallyIntegrable U' μ := hU'.locallyIntegrable one_le_two
  have hBU : (fun x ↦ B (U x)) = (Ω : Set E).indicator fun x ↦ B (u x) := by
    ext1 x
    by_cases hx : x ∈ (Ω : Set E) <;> simp [U, hx]
  have hind : HasWeakLineDerivOn μ Ω (fun x ↦ B (U x)) U' v := by
    rw [hBU]
    exact h.indicator
  -- The limits are integrable on `Ω`.
  have hlim : IntegrableOn (fun x ↦ B (u x) (u x)) Ω μ :=
    memLp_one_iff_integrable.1 (B.memLp_of_bilin 1 hu hu)
  have hlim' : IntegrableOn (fun x ↦ 2 * u' x (u x)) Ω μ :=
    (memLp_one_iff_integrable.1 ((ContinuousLinearMap.id ℝ (StrongDual ℝ V)).memLp_of_bilin 1
      hu' hu)).const_mul 2
  rw [hasWeakLineDerivOn_iff_forall_isCompact_closure]
  intro W hWc hWΩ
  have hWΩ' : (W : Set E) ⊆ Ω := subset_closure.trans hWΩ
  have hWμ : μ (W : Set E) < ⊤ := lt_of_le_of_lt (measure_mono subset_closure)
    hWc.measure_lt_top
  obtain ⟨φ, hφ, hsupp⟩ := ContDiffBump.exists_seq_sub_tsupport_subset (μ := μ) hWc hWΩ
  -- Each mollified quadratic form has its classical derivative as weak derivative on `W`.
  set g : ℕ → E → V := fun n ↦ (φ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U
  set k : ℕ → E → StrongDual ℝ V := fun n ↦
    (φ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U'
  have hweak (n : ℕ) : HasWeakLineDerivOn μ W (fun y ↦ B (g n y) (g n y))
      (fun y ↦ 2 * k n y (g n y)) v := by
    have hgc : Continuous (g n) :=
      (φ n).hasCompactSupport_normed.continuous_convolution_left _ (φ n).continuous_normed hUloc
    have hkc : Continuous (k n) :=
      (φ n).hasCompactSupport_normed.continuous_convolution_left _ (φ n).continuous_normed
        hU'loc
    refine hasWeakLineDerivOn_of_hasLineDerivAt ?_ ?_ fun x hx ↦
      hasLineDerivAt_bilin_self_convolution hB hind hUloc (φ n).contDiff_normed
        (φ n).hasCompactSupport_normed (hsupp n x hx)
    · exact (B.continuous₂.comp (hgc.prodMk hgc)).locallyIntegrable.locallyIntegrableOn _
    · exact (continuous_const.mul ((ContinuousLinearMap.id ℝ (StrongDual ℝ V)).continuous₂.comp
        (hkc.prodMk hgc))).locallyIntegrable.locallyIntegrableOn _
  -- The mollifications converge in `L²`, so the forms and their derivatives converge in `L¹(W)`.
  have hgLp (n : ℕ) : normedBumpLp ENNReal.ofNat_ne_top (φ n) μ (hU.toLp U) =ᵐ[μ] g n :=
    normedBumpLp_ae_eq_convolution ENNReal.ofNat_ne_top (φ n) hU
  have hkLp (n : ℕ) : normedBumpLp ENNReal.ofNat_ne_top (φ n) μ (hU'.toLp U') =ᵐ[μ] k n :=
    normedBumpLp_ae_eq_convolution ENNReal.ofNat_ne_top (φ n) hU'
  have hgt := tendsto_normedBumpLp (mu := μ) ENNReal.ofNat_ne_top hφ (hU.toLp U)
  have hkt := tendsto_normedBumpLp (mu := μ) ENNReal.ofNat_ne_top hφ (hU'.toLp U')
  have hext := hU.coeFn_toLp_indicator_restrict W.isOpen.measurableSet hWΩ'
  have hext' := hU'.coeFn_toLp_indicator_restrict W.isOpen.measurableSet hWΩ'
  refine hasWeakLineDerivOn_of_tendsto_lintegral_enorm_sub
    (hlim.mono_set hWΩ').locallyIntegrableOn (hlim'.mono_set hWΩ').locallyIntegrableOn hweak
    (tendsto_setLIntegral_enorm_bilin_sub (r := 1) B hWμ hgt hgt hgLp hext hgLp hext) ?_
  refine (tendsto_setLIntegral_enorm_bilin_sub (r := 1)
    ((2 : ℝ) • ContinuousLinearMap.id ℝ (StrongDual ℝ V)) hWμ hkt hgt hkLp hext' hgLp hext).congr
    fun n ↦ ?_
  simp

/-- **The mixed weak product rule for a symmetric bilinear form.** For square-integrable
`u` and `w`, if `B u` and `B w` have square-integrable weak derivatives `u'` and `w'`, then
`B(u, w)` has weak derivative
`u'(w) + w'(u)`. Only the dual-valued images need to be weakly differentiable. -/
theorem HasWeakLineDerivOn.bilin {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : B.flip = B)
    {u w : E → V} {u' w' : E → StrongDual ℝ V}
    (h : HasWeakLineDerivOn μ Ω (fun x ↦ B (u x)) u' v)
    (hw : HasWeakLineDerivOn μ Ω (fun x ↦ B (w x)) w' v)
    (hu : MemLp u 2 (μ.restrict Ω)) (hu' : MemLp u' 2 (μ.restrict Ω))
    (hwL : MemLp w 2 (μ.restrict Ω)) (hw' : MemLp w' 2 (μ.restrict Ω)) :
    HasWeakLineDerivOn μ Ω (fun x ↦ B (u x) (w x))
      (fun x ↦ u' x (w x) + w' x (u x)) v := by
  have hsum : HasWeakLineDerivOn μ Ω (fun x ↦ B ((u + w) x)) (u' + w') v := by
    exact (h.add hw).congr_ae (.of_forall fun x ↦ (map_add B (u x) (w x)).symm)
  have huws : MemLp (u + w) 2 (μ.restrict Ω) := hu.add hwL
  have huws' : MemLp (u' + w') 2 (μ.restrict Ω) := MemLp.add (ε := StrongDual ℝ V) hu' hw'
  have hsum_prod := HasWeakLineDerivOn.bilin_self (μ := μ) (Ω := Ω) (v := v)
    (B := B) (u := u + w) (u' := u' + w') hB hsum huws huws'
  have hu_prod := HasWeakLineDerivOn.bilin_self (B := B) (u := u) (u' := u') hB h hu hu'
  have hw_prod := HasWeakLineDerivOn.bilin_self (B := B) (u := w) (u' := w') hB hw hwL hw'
  have hpolar := ((hsum_prod.sub hu_prod).sub hw_prod).const_smul (1 / 2 : ℝ)
  have hsymm (x : E) : B (w x) (u x) = B (u x) (w x) := by
    rw [← ContinuousLinearMap.flip_apply, hB]
  refine (hpolar.congr_ae (.of_forall fun x ↦ ?_)).congr_ae_deriv (.of_forall fun x ↦ ?_)
  · simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, map_add,
      add_apply, hsymm]
    ring
  · simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul,
      add_apply, map_add]
    ring

/-- **The weak derivative of `‖ι u‖²` in a Gelfand triple.** Let `ι : V →L[ℝ] H` and
`u ∈ L²(Ω; V)`. If the `V*`-valued function `x ↦ ι.gelfandDual (ι (u x))`, that is `u` viewed in
`V*` through `V → H → V*`, has weak derivative `u' ∈ L²(Ω; V*)` in the direction `v` on `Ω`, then
`x ↦ ‖ι (u x)‖²` has weak derivative `x ↦ 2 u'(x)(u x)` in the direction `v` on `Ω`. -/
theorem HasWeakLineDerivOn.norm_sq_of_gelfandDual {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {ι : V →L[ℝ] H} {u : E → V} {u' : E → StrongDual ℝ V}
    (h : HasWeakLineDerivOn μ Ω (fun x ↦ ι.gelfandDual (ι (u x))) u' v)
    (hu : MemLp u 2 (μ.restrict Ω)) (hu' : MemLp u' 2 (μ.restrict Ω)) :
    HasWeakLineDerivOn μ Ω (fun x ↦ ‖ι (u x)‖ ^ 2) (fun x ↦ 2 * u' x (u x)) v := by
  simpa using HasWeakLineDerivOn.bilin_self (B := ι.gelfandDual.comp ι)
    ι.flip_gelfandDual_comp h hu hu'

end TauCeti
