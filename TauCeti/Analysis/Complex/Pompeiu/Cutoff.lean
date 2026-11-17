/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Topology.Algebra.Support

/-!
# The Cauchy–Green formula with a cutoff

A function `f` holomorphic on an open neighbourhood `U` of a compact set `K ⊆ ℂ` is, on `K`, the
Cauchy transform of a continuous compactly supported density whose closed support lies in `U` and
misses `K`. For a smooth cutoff `α` with compact support in `U`, equal to `1` near `K`, the
compactly supported `C¹` function `u = α f` is the Cauchy transform of `\bar∂ u`
(`HasCompactSupport.cauchyTransform_conjWirtingerDeriv`), and `\bar∂ u` vanishes near `K`, where
`u = f` is holomorphic. This writes `f` on `K` as an integral of simple fractions `ξ ↦ (ξ - z)⁻¹`
whose poles avoid `K`; it is the representation behind Runge's approximation theorem.

## Main results

* `Continuous.sub_inv_smul_of_disjoint_tsupport`: the Cauchy kernel `(z, ξ) ↦ (ξ - z)⁻¹ • h z` is
  jointly continuous on `ℂ × K` when the closed support of the continuous density `h` misses `K`.
* `DifferentiableOn.exists_eqOn_cauchyTransform`: the Cauchy–Green formula with a cutoff.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 10.3.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.9.
-/

public section

open Set Filter Function
open scoped Topology

namespace TauCeti

/-- The Cauchy kernel `(z, ξ) ↦ (ξ - z)⁻¹ • h z` is continuous on `ℂ × K` when the density `h` is
continuous and its closed support misses `K`. -/
theorem _root_.Continuous.sub_inv_smul_of_disjoint_tsupport {F : Type*} [TopologicalSpace F]
    [Zero F] [SMulZeroClass ℂ F] [ContinuousSMul ℂ F] {K : Set ℂ} {h : ℂ → F} (hh : Continuous h)
    (hK : Disjoint (tsupport h) K) : Continuous fun p : ℂ × K ↦ ((p.2 : ℂ) - p.1)⁻¹ • h p.1 :=
  (hh.comp continuous_fst).smul_of_continuousOn_of_tsupport_subset
    (tsupport_comp_subset_preimage h continuous_fst)
    (((continuous_subtype_val.comp continuous_snd).sub continuous_fst).continuousOn.inv₀
      fun p hp ↦ sub_ne_zero.2 fun hξz ↦ hK.notMem_of_mem_left hp (hξz ▸ p.2.property))

/-- **The Cauchy–Green formula with a cutoff.** A function `f` with values in a complex Banach
space, holomorphic on an open neighbourhood `U` of a compact set `K`, is, on `K`, the Cauchy
transform `ξ ↦ π⁻¹ ∫ (ξ - z)⁻¹ • h z` of a continuous compactly supported density `h` whose
closed support lies in `U` and misses `K`. -/
theorem _root_.DifferentiableOn.exists_eqOn_cauchyTransform {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {K U : Set ℂ} {f : ℂ → F} (hf : DifferentiableOn ℂ f U)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ h : ℂ → F, Continuous h ∧ HasCompactSupport h ∧ tsupport h ⊆ U \ K ∧
      EqOn (cauchyTransform h) f K := by
  -- Cut `f` off to a compactly supported `C¹` function `u`, equal to `f` on an open `W ⊇ K`.
  obtain ⟨α, hα, -, hα1, hαc, hαU⟩ := hK.exists_contDiff_cutoff hU hKU
  set u : ℂ → F := fun z ↦ α z • f z
  have hu : ContDiff ℝ 1 u :=
    ((hf.contDiffOn hU).restrict_scalars (𝕜 := ℝ)).contDiff_smul_of_tsupport_subset hU
      (hα.of_le (m := 1) (by simp)).contDiffOn hαU
  have huc : HasCompactSupport u := hαc.smul_right
  set W := interior (α ⁻¹' {1}) ∩ U
  have hW : IsOpen W := isOpen_interior.inter hU
  have huf {z : ℂ} (hz : z ∈ W) : u =ᶠ[𝓝 z] f := by
    filter_upwards [hW.mem_nhds hz] with y hy
    simp [u, mem_singleton_iff.1 (mem_preimage.1 (interior_subset hy.1))]
  -- Its `\bar∂` is supported in `tsupport u ⊆ U` and vanishes on `W`, where `u = f`.
  have hsupp := tsupport_conjWirtingerDeriv_apply_subset u 1
  refine ⟨fun z ↦ conjWirtingerDeriv u z 1, hu.continuous_conjWirtingerDeriv_apply 1,
    huc.conjWirtingerDeriv_apply 1, fun z hz ↦ ⟨?_, fun hzK ↦ ?_⟩, fun ξ hξ ↦ ?_⟩
  · exact hαU (tsupport_smul_subset_left α f (hsupp hz))
  · have hzW : z ∈ W := subset_inter hα1 hKU hzK
    refine (notMem_tsupport_iff_eventuallyEq.2 ?_) hz
    filter_upwards [hW.mem_nhds hzW] with y hy
    simp only [(huf hy).conjWirtingerDeriv_eq,
      (hf.differentiableAt (hU.mem_nhds hy.2)).conjWirtingerDeriv_eq_zero,
      zero_apply, Pi.zero_apply]
  · rw [huc.cauchyTransform_conjWirtingerDeriv hu ξ]
    exact (huf (subset_inter hα1 hKU hξ)).eq_of_nhds

end TauCeti
