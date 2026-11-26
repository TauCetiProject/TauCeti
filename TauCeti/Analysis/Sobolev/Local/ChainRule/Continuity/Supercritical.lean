/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Norm.Prod
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.Hadamard.Basic
import TauCeti.Analysis.Sobolev.Local.ChainRule.Bound.Supercritical
import TauCeti.Analysis.Sobolev.Local.Multiplication.Bound.Supercritical
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Continuity of composition in the supercritical Sobolev range

For finite `p > 1` and `kp > 2`, composition with a `C^{k+1}` map is locally Lipschitz
in the following sense. On a compactly contained subset of a planar domain, the Sobolev norm
of `g ∘ v - g ∘ u` is bounded by the Sobolev norm of `v - u` on the larger domain, times a
polynomial in the two input norms. The constant is uniform for images in a fixed compact
subset of the domain of `g`.

Hadamard's formula expresses the difference as a linear map depending on the pair `(u, v)`
applied to `v - u`. The coefficient is `Cᵏ` in the two endpoints, so the local Sobolev
composition and product estimates apply even when `p ≤ 2`. Morrey's embedding then turns
convergence in local Sobolev norms into continuity of composition. For a target map defined
on the whole space this holds for arbitrary almost-everywhere representatives.

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

/-- Local Lipschitz estimate for supercritical Sobolev composition. The constant is uniform for
continuous maps taking their values in the prescribed compact set `L ⊆ W`. -/
theorem exists_eLpNormWkp_comp_sub_le_of_two_lt_mul (hp : 1 < p) (hkp : 2 < (k : ℝ≥0) * p)
    (hW : IsOpen W) (hg : ContDiffOn ℝ (k + 1) g W) {L : Set F} (hL : IsCompact L)
    (hLW : L ⊆ W) {K : Set ℂ} (hK : IsCompact (closure K)) (hKΩ : closure K ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (u v : ℂ → F), ContinuousOn u Ω → ContinuousOn v Ω →
      MapsTo u Ω L → MapsTo v Ω L →
        eLpNormWkp p K k (g ∘ v - g ∘ u) ≤
          C * (1 + (eLpNormWkp p Ω k u + eLpNormWkp p Ω k v)) ^ k * eLpNormWkp p Ω k (v - u) := by
  obtain ⟨f, hf, -, heq⟩ := hL.exists_contDiff_eventuallyEq (k + 1)
    fun x hx ↦ (hg.contDiffAt (hW.mem_nhds (hLW hx)))
  let A : F × F → F →L[ℝ] G := fun q ↦ hadamardFactor f q.1 q.2
  have hA : ContDiff ℝ k A :=
    ContDiff.contDiff_hadamardFactor_uncurry_of_succ k f (by simpa using hf)
  obtain ⟨V, hKV, hVΩ, hVc⟩ := Opens.exists_between_and_isCompact_closure hK hKΩ
  obtain ⟨a, ha⟩ := exists_eLpNormWkp_clm_apply_le_of_two_lt_mul (F := F) (G := G) hp hkp hK hKV
  obtain ⟨b, hb⟩ := exists_eLpNormWkp_comp_le_of_two_lt_mul hp hkp isOpen_univ hA.contDiffOn
    (hL.prod hL) (subset_univ _) hVc hVΩ
  refine ⟨a * b, fun u v huc hvc hu hv ↦ ?_⟩
  let P := fun z ↦ (u z, v z)
  have hcoeff := hb P (huc.prodMk hvc) (fun z hz ↦ ⟨hu hz, hv hz⟩)
  have hfactor : (g ∘ v - g ∘ u) =ᵐ[volume.restrict K] fun z ↦ A (P z) ((v - u) z) := by
    -- Restrict from the open domain since the norm set itself need not be measurable.
    apply ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hKΩ)
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with z hz
    simp only [Pi.sub_apply, Function.comp_apply]
    rw [← (heq _ (hu hz)).eq_of_nhds, ← (heq _ (hv hz)).eq_of_nhds]
    exact ContDiff.sub_eq_hadamardFactor_apply f (hf.of_le (by norm_cast; omega)) _ _
  rw [eLpNormWkp_congr_ae hfactor, ENNReal.coe_mul, mul_assoc (a : ℝ≥0∞)]
  refine (ha (A ∘ P) (v - u)).trans (mul_le_mul' (mul_le_mul' le_rfl (hcoeff.trans ?_))
    (eLpNormWkp_mono_set (subset_closure.trans hVΩ)))
  gcongr
  exact eLpNormWkp_prodMk_le (by exact_mod_cast hp.le)

/-- A Sobolev perturbation whose essential supremum is small has a continuous representative
taking its values in the corresponding thickening of the original image. -/
private theorem exists_continuousOn_perturbation {q : ℝ≥0∞} (hq : 1 ≤ q)
    (hkq : 2 < (k : ℝ≥0∞) * q) {u v : ℂ → F} (hu : ContinuousOn u Ω)
    (hd : MemWkpLoc q Ω k (v - u)) {δ : ℝ}
    (hδ : eLpNorm (v - u) ∞ (volume.restrict Ω) ≤ ENNReal.ofReal δ) :
    ∃ w : ℂ → F, ContinuousOn w Ω ∧ v =ᵐ[volume.restrict Ω] w ∧
      MapsTo w Ω (cthickening δ (u '' (Ω : Set ℂ))) := by
  obtain ⟨d, hdc, he⟩ := hd.exists_continuousOn_ae_eq_of_two_lt_mul hq hkq
  have hb : ∀ z ∈ Ω, ‖d z‖ₑ ≤ ENNReal.ofReal δ := by
    refine ContinuousOn.le_of_ae_le (μ := volume) Ω.isOpen hdc.eNorm continuousOn_const ?_
    filter_upwards [he, eNorm_ae_le_eLpNormEssSup (v - u) (volume.restrict Ω)] with z hz hzle
    exact hz ▸ hzle.trans (eLpNormEssSup_le_eLpNorm_top.trans hδ)
  refine ⟨d + u, hdc.add hu, ?_, fun z hz ↦ mem_cthickening_of_edist_le _ (u z) _ _
    (mem_image_of_mem _ hz) (by simpa [eDist_eq_eNorm_sub] using hb z hz)⟩
  filter_upwards [he] with z hz
  simpa only [Pi.sub_apply, Pi.add_apply, sub_eq_iff_eq_add] using hz

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
  obtain ⟨w, hwc, he, hw⟩ := exists_continuousOn_perturbation hp1 hkp'
    (huc.mono (subset_closure.trans hVΩ))
    (memWkpLoc_of_eLpNormWkp_ne_top (ne_top_of_le_ne_top (hn.trans ENNReal.one_lt_top).ne hd)) hsup
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

end TauCeti
