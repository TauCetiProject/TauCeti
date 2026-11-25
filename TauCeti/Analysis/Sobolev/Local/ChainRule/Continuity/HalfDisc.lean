/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.ChainRule.Continuity.Higher
public import TauCeti.Analysis.Sobolev.Local.Reflection.Bound

/-!
# Continuity of composition in `W^{k,p}_loc` up to the real axis

Let `p > 2`, let `Ω` be an open planar domain and let `U = Ω ∩ {0 ≤ im}` be the corresponding
relatively open subset of the closed upper half-plane. Let `F` and `G` be finite-dimensional real
normed spaces, let `g : F → G` be `C^{k+1}` on an open set `W`, and let
`u₀ ∈ MemWkpLoc p U (k + 1)` map `U` into `W`. If maps `uₙ`, eventually continuous on every
compact subset of `U`, converge to `u₀` uniformly on compact subsets of `U` and in `W^{k+1,p}` on
every compact subset of `U`, then `g ∘ uₙ → g ∘ u₀` in `W^{k+1,p}` on every compact subset of `U`
(`TauCeti.MemWkpLoc.tendsto_eLpNormWkp_succ_comp_sub_inter_setOf_im_nonneg`). Compact subsets of
`U` may meet the real axis. This is the half-disc form of
`TauCeti.MemWkpLoc.tendsto_eLpNormWkp_succ_comp_sub`.

The proof reflects. Fix a compact `K ⊆ U` and an open `V ⊇ K` whose closure is compact and
contained in `Ω`, and let `R` be the order-`(k + 1)` higher reflection
`TauCeti.planarReflection (higherReflectionCoeff (k + 1))`. On the reflection core of `V`, an open
set between `V ∩ {0 ≤ im}` and `V`:

* `R u₀` is in `W^{k+1,p}_loc`
  (`TauCeti.MemWkpLoc.planarReflection_higherReflectionCoeff_reflectionCore`) and is continuous
  (`TauCeti.continuousOn_planarReflection`), since `u₀` is continuous on `U` as a locally uniform
  limit;
* `R uₙ → R u₀` uniformly (`TendstoUniformlyOn.planarReflection`), since below the real axis the
  reflection only samples the closed upper half of `V`, whose closure is a compact subset of `U`;
* `‖R uₙ - R u₀‖_{W^{k+1,p}} = ‖R (uₙ - u₀)‖_{W^{k+1,p}}` is at most a constant times
  `‖uₙ - u₀‖_{W^{k+1,p}}` on that compact set
  (`TauCeti.MemWkpLoc.eLpNormWkp_planarReflection_higherReflectionCoeff_reflectionCore_le`).

The reflection `R u₀` need not take values in `W` away from the real axis: for `k ≥ 1` it is a
combination of values of `u₀` with weights of both signs. It does take values in `W` on an open
neighbourhood `O` of `K`, because it is continuous and equals `u₀` on `K`. The interior theorem on
`O` gives `g ∘ R uₙ → g ∘ R u₀` in `W^{k+1,p}(K)`, and on `K`, which lies in the closed upper
half-plane, `g ∘ R uₙ - g ∘ R u₀ = g ∘ uₙ - g ∘ u₀`.

## Main declarations

* `TauCeti.MemWkpLoc.tendsto_eLpNormWkp_succ_comp_sub_inter_setOf_im_nonneg`: continuity of
  composition with a `C^{k+1}` map in `W^{k+1,p}` on compact subsets of `Ω ∩ {0 ≤ im}`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (composition in local Sobolev spaces).
* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 5.19 (extension by higher
  order reflection).
-/

public noncomputable section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal Topology

namespace TauCeti

universe uF uG

variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {Ω : Opens ℂ} {p : ℝ≥0}

omit [FiniteDimensional ℝ F] in
/-- Let `L` contain the closed upper half of `V`. If `uₙ` are eventually continuous on `L` and
converge to `u₀` uniformly on `L`, then on the reflection core of `V` the order-`(k + 1)`
reflection of `u₀` is continuous, those of the `uₙ` are eventually continuous, and they converge
to it uniformly. -/
private theorem continuousOn_and_tendstoUniformlyOn_planarReflection {k : ℕ} {ι : Type*}
    {l : Filter ι} [l.NeBot] {u : ι → ℂ → F} {u₀ : ℂ → F} {V : Opens ℂ} {L : Set ℂ}
    (hVL : (V : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ L) (huc : ∀ᶠ n in l, ContinuousOn (u n) L)
    (hunif : TendstoUniformlyOn u u₀ l L) :
    ContinuousOn (planarReflection (higherReflectionCoeff (k + 1)) u₀) V.reflectionCore ∧
      (∀ᶠ n in l, ContinuousOn (planarReflection (higherReflectionCoeff (k + 1)) (u n))
        V.reflectionCore) ∧
      TendstoUniformlyOn (fun n => planarReflection (higherReflectionCoeff (k + 1)) (u n))
        (planarReflection (higherReflectionCoeff (k + 1)) u₀) l V.reflectionCore := by
  rw [← Opens.coe_reflectionCore_inter_setOf_im_nonneg] at hVL
  have hsum : ∑ j, higherReflectionCoeff (k + 1) j = 1 := sum_higherReflectionCoeff k.succ_pos
  have hV :=
    Opens.imDilation_higherReflectionNode_mem_reflectionCore_of_im_neg (V := V) (n := k + 1)
  exact ⟨continuousOn_planarReflection hsum hV ((hunif.continuousOn huc.frequently).mono hVL),
    huc.mono fun n hn => continuousOn_planarReflection hsum hV (hn.mono hVL),
    (hunif.mono hVL).planarReflection hV _⟩

omit [FiniteDimensional ℝ F] in
/-- Let `L` be a set containing the closed upper half of `V`. If `uₙ → u₀` in `W^{k+1,p}(L)`, then
the order-`(k + 1)` reflections converge in `W^{k+1,p}` on every subset of the reflection core of
`V`. -/
private theorem tendsto_eLpNormWkp_planarReflection_sub (hp1 : (1 : ℝ≥0∞) ≤ p) {k : ℕ}
    {ι : Type*} {l : Filter ι} {u : ι → ℂ → F} {u₀ : ℂ → F} {V : Opens ℂ} {L : Set ℂ}
    (hVL : (V : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ L)
    (hlim : Tendsto (fun n => eLpNormWkp p L (k + 1) (u n - u₀)) l (𝓝 0)) {K : Set ℂ}
    (hK : K ⊆ V.reflectionCore) :
    Tendsto (fun n => eLpNormWkp p K (k + 1)
      (planarReflection (higherReflectionCoeff (k + 1)) (u n) -
        planarReflection (higherReflectionCoeff (k + 1)) u₀)) l (𝓝 0) := by
  have hbd : ∀ᶠ n in l, eLpNormWkp p K (k + 1) (planarReflection (higherReflectionCoeff (k + 1))
      (u n) - planarReflection (higherReflectionCoeff (k + 1)) u₀) ≤
        higherReflectionBound (k + 1) p * eLpNormWkp p L (k + 1) (u n - u₀) := by
    filter_upwards [hlim.eventually (gt_mem_nhds ENNReal.zero_lt_top)] with n hn
    rw [← planarReflection_sub]
    have hmem : MemWkpLoc p ((V : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) (u n - u₀) :=
      (memWkpLoc_of_eLpNormWkp_ne_top hn.ne).mono hVL
    refine (eLpNormWkp_mono_set hK).trans
      ((hmem.eLpNormWkp_planarReflection_higherReflectionCoeff_reflectionCore_le hp1).trans ?_)
    gcongr
    exact eLpNormWkp_mono_set hVL
  have h0 := ENNReal.Tendsto.const_mul hlim (Or.inr (higherReflectionBound_ne_top (k + 1) p))
  rw [mul_zero] at h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
    (.of_forall fun _ => zero_le) hbd

/-- **Continuity of composition in `W^{k+1,p}_loc` up to the real axis.** Let `p > 2`, let `F`
and `G` be finite-dimensional, let `g : F → G` be `C^{k+1}` on an open set `W`, and let
`u₀ ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) (k + 1)` map `Ω ∩ {0 ≤ im}` into `W`. Let maps `uₙ` converge to
`u₀` locally uniformly on `Ω ∩ {0 ≤ im}`, and for every compact `K ⊆ Ω ∩ {0 ≤ im}` let `uₙ` be
eventually continuous on `K` with `‖uₙ - u₀‖_{W^{k+1,p}(K)} → 0`. Then
`‖g ∘ uₙ - g ∘ u₀‖_{W^{k+1,p}(K)} → 0` for every compact `K ⊆ Ω ∩ {0 ≤ im}`, including compact
sets that meet the real axis. -/
theorem MemWkpLoc.tendsto_eLpNormWkp_succ_comp_sub_inter_setOf_im_nonneg {G : Type uG}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] (hp : 2 < p) {k : ℕ}
    {ι : Type*} {l : Filter ι} {u : ι → ℂ → F} {u₀ : ℂ → F} {g : F → G} {W : Set F}
    (hu₀ : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) u₀) (hW : IsOpen W)
    (hg : ContDiffOn ℝ (k + 1) g W) (hu₀W : MapsTo u₀ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) W)
    (huc : ∀ K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, IsCompact K → ∀ᶠ n in l, ContinuousOn (u n) K)
    (hunif : TendstoLocallyUniformlyOn u u₀ l ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hlim : ∀ K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, IsCompact K →
      Tendsto (fun n => eLpNormWkp p K (k + 1) (u n - u₀)) l (𝓝 0)) :
    ∀ K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, IsCompact K →
      Tendsto (fun n => eLpNormWkp p K (k + 1) (g ∘ u n - g ∘ u₀)) l (𝓝 0) := by
  intro K hKU hK
  rcases l.eq_or_neBot with rfl | _
  · exact tendsto_bot
  set R : (ℂ → F) → ℂ → F := TauCeti.planarReflection (higherReflectionCoeff (k + 1)) with hR
  -- A relatively compact open neighbourhood `V` of `K` in `Ω`, and the compact set
  -- `L = closure V ∩ {0 ≤ im}`, which contains the closed upper half of `V`.
  obtain ⟨V₀, hVo, hKV, hVΩ, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK Ω.isOpen (hKU.trans inter_subset_left)
  let V : Opens ℂ := ⟨V₀, hVo⟩
  set L := closure V₀ ∩ {z : ℂ | 0 ≤ z.im}
  have hL : IsCompact L := hVc.inter_right (isClosed_le continuous_const Complex.continuous_im)
  have hLU : L ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} := inter_subset_inter_left _ hVΩ
  have hVL : (V : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ L := inter_subset_inter_left _ subset_closure
  obtain ⟨hRc, hRuc, hRunif⟩ := continuousOn_and_tendstoUniformlyOn_planarReflection (k := k) hVL
    (huc L hLU hL) ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hL).1
      (hunif.mono hLU))
  -- The open neighbourhood `O` of `K` on which `R u₀` takes values in `W`.
  let O : Opens ℂ := ⟨V.reflectionCore ∩ R u₀ ⁻¹' W,
    hRc.isOpen_inter_preimage V.reflectionCore.isOpen hW⟩
  have hOV : (O : Set ℂ) ⊆ V.reflectionCore := inter_subset_left
  have hKO : K ⊆ O := fun z hz => ⟨V.inter_setOf_im_nonneg_subset_reflectionCore
    ⟨hKV hz, (hKU hz).2⟩, by
      simpa only [mem_preimage, hR, planarReflection_of_nonneg _ _ (hKU hz).2] using hu₀W (hKU hz)⟩
  -- The interior theorem on `O`, applied to the reflections.
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast (one_lt_two.trans hp).le
  have hRu₀ : MemWkpLoc p O (k + 1) (R u₀) :=
    ((hu₀.mono (hVL.trans hLU)).planarReflection_higherReflectionCoeff_reflectionCore
      hp1).mono hOV
  have h := hRu₀.tendsto_eLpNormWkp_succ_comp_sub hp hW hg (fun z hz => hz.2)
    (fun K' hK'O _ => hRuc.mono fun n hn => hn.mono (hK'O.trans hOV))
    (hRunif.tendstoLocallyUniformlyOn.mono hOV)
    (fun K' hK'O _ => tendsto_eLpNormWkp_planarReflection_sub hp1 hVL (hlim L hLU hL)
      (hK'O.trans hOV))
    K hKO hK
  -- On `K`, which lies in the closed upper half-plane, the reflections are the maps themselves.
  refine h.congr fun n => eLpNormWkp_congr_ae ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  simp only [Pi.sub_apply, Function.comp_apply, hR, planarReflection_of_nonneg _ _ (hKU hz).2]

end TauCeti
