/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs

/-!
# Limits of rescaled secants under differentiation along a filter

Suppose endpoint pairs tend along a derivative filter, their images agree on a cofinal set,
and their scalar-rescaled difference converges. The derivative annihilates that limit.
The scalars are arbitrary and may vanish. In particular, both endpoints may approach a strict
derivative point.

The argument adapts Mathlib's `HasFDerivWithinAt.lim` from a fixed base point to pairs of
endpoints.
-/

public section

open Asymptotics Filter
open scoped Topology

variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousSMul 𝕜 E] [ContinuousAdd E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousSMul 𝕜 F]
  [T2Space F]

/-- If endpoint pairs tend along a derivative filter and their images agree on a cofinal set,
the derivative annihilates any limit of their scalar-rescaled difference. This applies to
ordinary and within-set derivatives when the second endpoint is fixed. -/
theorem HasFDerivAtFilter.apply_eq_zero_of_tendsto_smul_sub
    {P : E → F} {L : E →L[𝕜] F} {s : Filter (E × E)} (hP : HasFDerivAtFilter P L s)
    {l : Filter ι} {a b : ι → E} {r : ι → 𝕜} {w : E}
    (hab : Tendsto (fun i ↦ (a i, b i)) l s)
    (hPeq : ∃ᶠ i in l, P (a i) = P (b i))
    (hr : Tendsto (fun i ↦ r i • (a i - b i)) l (𝓝 w)) :
    L w = 0 := by
  let := ContinuousNeg.of_continuousConstSMul 𝕜 F
  let good : Set ι := {i | P (a i) = P (b i)}
  let l' : Filter ι := l ⊓ 𝓟 good
  have : NeBot l' := frequently_iff_neBot.mp hPeq
  have hgood : ∀ᶠ i in l', P (a i) = P (b i) :=
    (eventually_mem_principal good).filter_mono inf_le_right
  let err : ι → F := fun i ↦ P (a i) - P (b i) - L (a i - b i)
  have ho : err =o[𝕜; l'] (fun i ↦ a i - b i) := by
    simpa only [err, Function.comp_def] using
      hP.isLittleOTVS.comp_tendsto (hab.mono_left inf_le_left)
  have hbound : (fun i ↦ r i • (a i - b i)) =O[𝕜; l'] (1 : ι → 𝕜) :=
    (hr.mono_left inf_le_left).isBigOTVS_one 𝕜
  have hlim : Tendsto (fun i ↦ r i • err i) l' (𝓝 0) :=
    isLittleOTVS_one.mp ((ho.smul_left r).trans_isBigOTVS hbound)
  have hscaledError : (fun i ↦ r i • err i) =ᶠ[l']
      (fun i ↦ -L (r i • (a i - b i))) :=
    hgood.mono fun i hi ↦ by
      simp only [err, hi, sub_self, zero_sub, smul_neg, map_smul]
  have hlimv : Tendsto (fun i ↦ -L (r i • (a i - b i))) l' (𝓝 (-L w)) :=
    (L.continuous.tendsto w |>.comp (hr.mono_left inf_le_left)).neg
  have hw : -L w = 0 :=
    tendsto_nhds_unique_of_frequently_eq hlimv hlim hscaledError.symm.frequently
  exact neg_eq_zero.mp hw

/-- If both endpoints tend to the strict derivative point and their images agree on a cofinal
set, the derivative annihilates any limit of their scalar-rescaled difference. The gap may be
much smaller than the distances of the endpoints to the derivative point. -/
theorem HasStrictFDerivAt.apply_eq_zero_of_tendsto_smul_sub
    {P : E → F} {L : E →L[𝕜] F} {x : E} (hP : HasStrictFDerivAt P L x)
    {l : Filter ι} {a b : ι → E} {r : ι → 𝕜} {w : E}
    (ha : Tendsto a l (𝓝 x)) (hb : Tendsto b l (𝓝 x))
    (hPeq : ∃ᶠ i in l, P (a i) = P (b i))
    (hr : Tendsto (fun i ↦ r i • (a i - b i)) l (𝓝 w)) :
    L w = 0 :=
  HasFDerivAtFilter.apply_eq_zero_of_tendsto_smul_sub hP (ha.prodMk_nhds hb) hPeq hr
