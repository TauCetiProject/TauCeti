/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Analysis.Sobolev.Local.ChainRule.Bound.Supercritical
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding

/-!
# Continuity of composition in the supercritical Sobolev range

For finite `p > 1` and `kp > 2`, composition with a `C^{k+1}` map preserves
local Sobolev convergence. Morrey's embedding supplies continuous representatives and
controls their images, so the local Lipschitz estimate
`TauCeti.exists_eLpNormWkp_comp_sub_le_of_two_lt_mul` applies on compact subsets.
For a globally defined `C^{k+1}` map, the convergence holds for arbitrary almost-everywhere
representatives, including that of the limit. This includes `p ≤ 2` for `k ≥ 2`, for instance
`k = 2` and `p = 4/3`, outside the range `p > 2` of
`TauCeti.MemWkpLoc.tendsto_eLpNormWkp_succ_comp_sub`.

## Main declarations

* `TauCeti.MemWkpLoc.tendsto_eLpNormWkp_comp_sub_of_two_lt_mul`: continuity of composition with a
  `C^{k+1}` map in `W^{k,p}` on compact subsets, for `kp > 2`.
* `TauCeti.MemWkpLoc.tendsto_eLpNormWkp_comp_sub_of_contDiff`: the same for a globally `C^{k+1}`
  map and arbitrary representatives.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Sobolev multiplication and composition).
-/

public noncomputable section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {p : ℝ≥0} {k : ℕ} {Ω : Opens ℂ} {g : F → G} {W : Set F}

/-- Composition with a `C^{k+1}` map is continuous for `W^{k,p}` convergence on compact
subsets when `kp > 2`. Only the continuous representative of the limit needs to take values
in the open set where the outer map is differentiable. -/
theorem MemWkpLoc.tendsto_eLpNormWkp_comp_sub_of_two_lt_mul (hp : 1 < p)
    (hkp : 2 < (k : ℝ≥0) * p) {ι : Type*} {l : Filter ι} {v : ι → ℂ → F} {u : ℂ → F}
    (hu : MemWkpLoc p Ω k u) (huc : ContinuousOn u Ω) (hW : IsOpen W)
    (hg : ContDiffOn ℝ (k + 1) g W) (huW : MapsTo u Ω W)
    (hlim : ∀ K ⊆ (Ω : Set ℂ), IsCompact K →
      Tendsto (fun n ↦ eLpNormWkp p K k (v n - u)) l (𝓝 0)) :
    ∀ K ⊆ (Ω : Set ℂ), IsCompact K →
      Tendsto (fun n ↦ eLpNormWkp p K k (g ∘ v n - g ∘ u)) l (𝓝 0) := by
  intro K hKΩ hK
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp.le
  have hkp' : 2 < (k : ℝ≥0∞) * p := by exact_mod_cast hkp
  obtain ⟨V, hKV, hVΩ, hVc⟩ := Opens.exists_between_and_isCompact_closure hK hKΩ
  obtain ⟨D, hVD, hDΩ, hDc⟩ := Opens.exists_between_and_isCompact_closure hVc hVΩ
  -- Leave room in the target for small perturbations of the limit on the closure of V.
  let S := u '' closure (V : Set ℂ)
  have hS : IsCompact S := hVc.image_of_continuousOn (huc.mono hVΩ)
  obtain ⟨δ, hδ, hδW⟩ := hS.exists_cthickening_subset_open hW (huW.mono_left hVΩ).image_subset
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_comp_sub_le_of_two_lt_mul (Ω := V) (K := K) hp hkp hW hg
    hS.cthickening hδW hK.closure
    (by simpa [hK.isClosed.closure_eq] using hKV)
  obtain ⟨B, hB⟩ := exists_eLpNorm_top_le_mul_eLpNormWkp_of_two_lt_mul (F := F) hp1 hkp' hVc hVD
  let N := eLpNormWkp p V k u
  have hN : N ≠ ∞ := hu.eLpNormWkp_ne_top_of_closure_subset hVc hVΩ
  let t := fun n ↦ eLpNormWkp p (closure (D : Set ℂ)) k (v n - u)
  have ht : Tendsto t l (𝓝 0) := hlim _ hDΩ hDc
  have hBt : Tendsto (fun n ↦ (B : ℝ≥0∞) * t n) l (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul ht (Or.inr ENNReal.coe_ne_top)
  let M : ℝ≥0∞ := C * (1 + (N + (1 + N))) ^ k
  have hMt : Tendsto (fun n ↦ M * t n) l (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul ht (Or.inr (by finiteness : M ≠ ∞))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hMt
    (.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [ht.eventually (gt_mem_nhds zero_lt_one),
    hBt.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hδ))] with n hn hnδ
  have hd : eLpNormWkp p V k (v n - u) ≤ t n :=
    eLpNormWkp_mono_set (subset_closure.trans (hVD.trans subset_closure))
  -- Morrey controls the perturbation on V by the input norm on the larger open set D.
  have hsup : eLpNorm (v n - u) ∞ (volume.restrict V) ≤ ENNReal.ofReal δ :=
    (hB _).trans ((mul_le_mul' le_rfl (eLpNormWkp_mono_set subset_closure)).trans hnδ.le)
  have hmem := memWkpLoc_of_eLpNormWkp_ne_top
    (ne_top_of_le_ne_top (hn.trans ENNReal.one_lt_top).ne hd)
  obtain ⟨w, hwc, he, hw⟩ := hmem.exists_continuousOn_ae_eq_of_eLpNorm_top_sub_le hp1 hkp'
    (huc.mono (subset_closure.trans hVΩ)) hsup
  have heK : v n =ᵐ[volume.restrict K] w := ae_restrict_of_ae_restrict_of_subset hKV he
  have hdiff : eLpNormWkp p V k (w - u) ≤ t n := by
    rwa [← eLpNormWkp_congr_ae (he.sub EventuallyEq.rfl)]
  have hwN : eLpNormWkp p V k w ≤ 1 + N := by
    calc _ = eLpNormWkp p V k ((w - u) + u) := by rw [sub_add_cancel]
         _ ≤ _ := (eLpNormWkp_add_le hp1).trans (add_le_add (hdiff.trans hn.le) le_rfl)
  rw [eLpNormWkp_congr_ae ((heK.fun_comp g).sub EventuallyEq.rfl)]
  refine (hC u w (huc.mono (subset_closure.trans hVΩ)) hwc
    (fun z hz ↦ self_subset_cthickening _ (mem_image_of_mem _ (subset_closure hz)))
    (hw.mono_right (cthickening_subset_of_subset δ (image_mono subset_closure)))).trans ?_
  exact mul_le_mul' (by dsimp [M]; gcongr) hdiff

/-- A globally `C^{k+1}` map preserves supercritical local Sobolev convergence for arbitrary
representatives of the maps and their limit. -/
theorem MemWkpLoc.tendsto_eLpNormWkp_comp_sub_of_contDiff (hp : 1 < p)
    (hkp : 2 < (k : ℝ≥0) * p) {ι : Type*} {l : Filter ι} {v : ι → ℂ → F} {u : ℂ → F}
    (hu : MemWkpLoc p Ω k u) (hg : ContDiff ℝ (k + 1) g)
    (hlim : ∀ K ⊆ (Ω : Set ℂ), IsCompact K →
      Tendsto (fun n ↦ eLpNormWkp p K k (v n - u)) l (𝓝 0)) :
    ∀ K ⊆ (Ω : Set ℂ), IsCompact K →
      Tendsto (fun n ↦ eLpNormWkp p K k (g ∘ v n - g ∘ u)) l (𝓝 0) := by
  obtain ⟨w, hw, he⟩ := hu.exists_continuousOn_ae_eq_of_two_lt_mul
    (by exact_mod_cast hp.le) (by exact_mod_cast hkp)
  intro K hKΩ hK
  have ht := (hu.congr_ae he).tendsto_eLpNormWkp_comp_sub_of_two_lt_mul hp hkp hw
    isOpen_univ hg.contDiffOn (mapsTo_univ _ _) (fun L hL hLc ↦ (hlim L hL hLc).congr
      fun n ↦ eLpNormWkp_congr_ae (EventuallyEq.rfl.sub
        (ae_restrict_of_ae_restrict_of_subset hL he)))
    K hKΩ hK
  have heK : u =ᵐ[volume.restrict K] w := ae_restrict_of_ae_restrict_of_subset hKΩ he
  exact ht.congr fun n ↦ eLpNormWkp_congr_ae (EventuallyEq.rfl.sub (heK.symm.fun_comp g))


/-- The check at `p = 4/3` and `k = 2`, outside the range `p > 2` of
`TauCeti.MemWkpLoc.tendsto_eLpNormWkp_succ_comp_sub`: squaring is continuous along maps
converging in `W^{2,4/3}` on compact sets. -/
example {ι : Type*} {l : Filter ι} {u : ι → ℂ → ℝ} {u₀ : ℂ → ℝ}
    (hu₀ : MemWkpLoc (4 / 3 : ℝ≥0) Ω 2 u₀)
    (hlim : ∀ K ⊆ (Ω : Set ℂ), IsCompact K →
      Tendsto (fun n => eLpNormWkp (4 / 3 : ℝ≥0) K 2 (u n - u₀)) l (𝓝 0))
    (K : Set ℂ) (hKΩ : K ⊆ Ω) (hK : IsCompact K) :
    Tendsto (fun n => eLpNormWkp (4 / 3 : ℝ≥0) K 2 ((fun x => x ^ 2) ∘ u n - (fun x => x ^ 2) ∘ u₀))
      l (𝓝 0) :=
  hu₀.tendsto_eLpNormWkp_comp_sub_of_contDiff (by norm_num) (by norm_num) (contDiff_id.pow 2)
    hlim K hKΩ hK

end TauCeti
