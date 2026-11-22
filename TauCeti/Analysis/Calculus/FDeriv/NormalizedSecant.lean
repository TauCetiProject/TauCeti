/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs

/-!
# Limits of rescaled secants under strict differentiability

Suppose both endpoints approach the point of strict differentiation, their images agree on a
common cofinal set, and their difference is a scalar scale times a convergent factor. If the
scale is nonzero on that set, the derivative annihilates the limit of the factor. The scales
need not be the lengths of the secants.
-/

public section

open Asymptotics Filter
open scoped Topology

namespace HasStrictFDerivAt

variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If both endpoints tend to the strict derivative point and their images agree on a common
cofinal set where the endpoint gap is a nonzero scalar times a convergent factor, the derivative
annihilates the limit of that factor. The gap may be much smaller than the distances of the
endpoints to the derivative point. -/
theorem apply_eq_zero_of_tendsto_normalized_secant
    {P : E → F} {L : E →L[𝕜] F} {x : E} (hP : HasStrictFDerivAt P L x)
    {l : Filter ι} {a b : ι → E} {c : ι → 𝕜} {v : ι → E} {w : E}
    (ha : Tendsto a l (𝓝 x)) (hb : Tendsto b l (𝓝 x))
    (hvalid : ∃ᶠ i in l, c i ≠ 0 ∧ a i - b i = c i • v i ∧
      P (a i) = P (b i))
    (hv : Tendsto v l (𝓝 w)) :
    L w = 0 := by
  let good : Set ι := {i | c i ≠ 0 ∧ a i - b i = c i • v i ∧ P (a i) = P (b i)}
  let l' : Filter ι := l ⊓ 𝓟 good
  have : NeBot l' := frequently_iff_neBot.mp hvalid
  have hgood : ∀ᶠ i in l',
      c i ≠ 0 ∧ a i - b i = c i • v i ∧ P (a i) = P (b i) :=
    (eventually_mem_principal good).filter_mono inf_le_right
  let err : ι → F := fun i ↦ P (a i) - P (b i) - L (a i - b i)
  have ho : err =o[𝕜; l'] (fun i ↦ a i - b i) := by
    simpa only [err, Function.comp_def] using
      hP.isLittleOTVS.comp_tendsto
        ((ha.mono_left inf_le_left).prodMk_nhds (hb.mono_left inf_le_left))
  have hscaled := ho.smul_left (fun i ↦ (c i)⁻¹)
  have hscaledGap : (fun i ↦ (c i)⁻¹ • (a i - b i)) =ᶠ[l'] v :=
    hgood.mono fun i hi ↦ by
      simp only [hi.2.1, inv_smul_smul₀ hi.1]
  have hbound : (fun i ↦ (c i)⁻¹ • (a i - b i)) =O[𝕜; l'] (1 : ι → 𝕜) :=
    ((hv.mono_left inf_le_left).isBigOTVS_one 𝕜).congr' hscaledGap.symm
      (EventuallyEq.rfl)
  have hlim : Tendsto (fun i ↦ (c i)⁻¹ • err i) l' (𝓝 0) :=
    isLittleOTVS_one.mp (hscaled.trans_isBigOTVS hbound)
  have hzero' : ∀ᶠ i in l', P (a i) = P (b i) :=
    hgood.mono fun i hi ↦ hi.2.2
  have hscaledError : (fun i ↦ (c i)⁻¹ • err i) =ᶠ[l']
      (fun i ↦ -L ((c i)⁻¹ • (a i - b i))) :=
    hzero'.mono fun i hi ↦ by
      simp only [err, hi, sub_self, zero_sub, smul_neg, map_smul]
  have heq : (fun i ↦ (c i)⁻¹ • err i) =ᶠ[l'] (fun i ↦ -L (v i)) :=
    hscaledError.trans (hscaledGap.fun_comp fun z ↦ -L z)
  have hlimv : Tendsto (fun i ↦ -L (v i)) l' (𝓝 (-L w)) :=
    (L.continuous.tendsto w |>.comp (hv.mono_left inf_le_left)).neg
  have hw : -L w = 0 :=
    tendsto_nhds_unique_of_frequently_eq hlimv hlim heq.symm.frequently
  exact neg_eq_zero.mp hw

end HasStrictFDerivAt
