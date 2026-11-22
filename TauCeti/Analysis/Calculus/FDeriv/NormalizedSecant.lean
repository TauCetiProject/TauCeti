/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Analysis.Asymptotics.TVS
public import Mathlib.Analysis.Calculus.FDeriv.Defs

/-!
# Limits of rescaled secants under strict differentiability

Suppose two points approach the same limit, their images under a strictly differentiable map
agree eventually, and their difference divided by a scalar scale converges. If the scale is
nonzero frequently, the derivative annihilates the limit of the rescaled secants. The scales
need not be the lengths of the secants.
-/

public section

open Asymptotics Filter
open scoped Topology

namespace HasStrictFDerivAt

variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If the paired values of a strictly differentiable map eventually agree, the derivative
annihilates any limit of their differences rescaled by arbitrary nonzero scalars. The scalars
only need to be nonzero frequently, and the differences may be much smaller than the distances
of the individual points to the base point. -/
theorem apply_eq_zero_of_tendsto_normalized_secant
    {P : E → F} {L : E →L[𝕜] F} {x : E} (hP : HasStrictFDerivAt P L x)
    {l : Filter ι} {a b : ι → E} {c : ι → 𝕜} {v : ι → E} {w : E}
    (ha : Tendsto a l (𝓝 x)) (hb : Tendsto b l (𝓝 x))
    (hc : ∃ᶠ i in l, c i ≠ 0) (hgap : ∀ᶠ i in l, a i - b i = c i • v i)
    (hv : Tendsto v l (𝓝 w)) (hzero : ∀ᶠ i in l, P (a i) = P (b i)) :
    L w = 0 := by
  let l' : Filter ι := l ⊓ 𝓟 {i | c i ≠ 0}
  have : NeBot l' := frequently_iff_neBot.mp hc
  have hc' : ∀ᶠ i in l', c i ≠ 0 :=
    (show ∀ᶠ i in 𝓟 {i | c i ≠ 0}, c i ≠ 0 by simp).filter_mono inf_le_right
  have hgap' := hgap.filter_mono (inf_le_left : l' ≤ l)
  have hzero' := hzero.filter_mono (inf_le_left : l' ≤ l)
  let err : ι → F := fun i ↦ P (a i) - P (b i) - L (a i - b i)
  have ho : err =o[𝕜; l'] (fun i ↦ a i - b i) := by
    simpa only [err, Function.comp_def] using
      hP.isLittleOTVS.comp_tendsto
        ((ha.mono_left inf_le_left).prodMk_nhds (hb.mono_left inf_le_left))
  have hscaled := ho.smul_left (fun i ↦ (c i)⁻¹)
  have hscaledGap : (fun i ↦ (c i)⁻¹ • (a i - b i)) =ᶠ[l'] v :=
    (hc'.and hgap').mono fun i hi ↦ by
      change (c i)⁻¹ • (a i - b i) = v i
      rw [hi.2, inv_smul_smul₀ hi.1]
  have hbound : (fun i ↦ (c i)⁻¹ • (a i - b i)) =O[𝕜; l'] (1 : ι → 𝕜) :=
    ((hv.mono_left inf_le_left).isBigOTVS_one 𝕜).congr' hscaledGap.symm
      (EventuallyEq.rfl)
  have hlim : Tendsto (fun i ↦ (c i)⁻¹ • err i) l' (𝓝 0) :=
    isLittleOTVS_one.mp (hscaled.trans_isBigOTVS hbound)
  have heq : (fun i ↦ (c i)⁻¹ • err i) =ᶠ[l'] (fun i ↦ -L (v i)) :=
    (hc'.and (hgap'.and hzero')).mono fun i hi ↦ by
      change (c i)⁻¹ • (P (a i) - P (b i) - L (a i - b i)) = -L (v i)
      rw [hi.2.2, sub_self, zero_sub, hi.2.1, map_smul]
      simp [smul_neg, inv_smul_smul₀ hi.1]
  have hlimv : Tendsto (fun i ↦ -L (v i)) l' (𝓝 (-L w)) :=
    (L.continuous.tendsto w |>.comp (hv.mono_left inf_le_left)).neg
  have hw : -L w = 0 :=
    tendsto_nhds_unique_of_frequently_eq hlimv hlim heq.symm.frequently
  exact neg_eq_zero.mp hw

end HasStrictFDerivAt
