/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Reflection.Bound

/-!
# Continuity of higher-order reflection in local Sobolev norms

On each compact subset of the reflection core, convergence of the reflected functions is
controlled by a single compact set in the closed upper half-plane. This transfers interior
continuity results to domains with boundary.
-/

public section

open Filter Set TopologicalSpace
open scoped ENNReal Topology

namespace TauCeti

/-- Higher-order reflection takes local `W^{k,p}` convergence up to the real axis to local
`W^{k,p}` convergence on the open reflection core. -/
theorem tendsto_eLpNormWkp_planarReflection_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {k : ℕ} {Ω : Opens ℂ} {ι : Type*} {l : Filter ι}
    {u : ι → ℂ → F} {v : ℂ → F}
    (hlim : ∀ L ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, IsCompact L →
      Tendsto (fun n ↦ eLpNormWkp p L k (u n - v)) l (𝓝 0))
    {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω.reflectionCore) :
    Tendsto (fun n ↦ eLpNormWkp p K k
      (planarReflection (higherReflectionCoeff k) (u n) -
        planarReflection (higherReflectionCoeff k) v)) l (𝓝 0) := by
  obtain ⟨V, hVc, hVΩ, hKV⟩ := Opens.exists_subset_reflectionCore_and_isCompact_closure hK hKΩ
  let L := closure (V : Set ℂ) ∩ {z | 0 ≤ z.im}
  have hL : IsCompact L := hVc.inter_right (isClosed_le continuous_const Complex.continuous_im)
  have ht := ENNReal.Tendsto.const_mul (hlim L (inter_subset_inter_left _ hVΩ) hL)
    (Or.inr (higherReflectionBound_ne_top k p))
  rw [mul_zero] at ht
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ ↦ zero_le)
    fun n ↦ ?_
  rw [← planarReflection_sub]
  refine (eLpNormWkp_mono_set hKV).trans
    ((eLpNormWkp_planarReflection_higherReflectionCoeff_reflectionCore_le hp _).trans ?_)
  gcongr
  exact eLpNormWkp_mono_set (inter_subset_inter_left _ subset_closure)

end TauCeti
