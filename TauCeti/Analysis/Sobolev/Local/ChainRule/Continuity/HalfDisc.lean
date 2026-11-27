/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.ChainRule.Continuity.Higher
public import TauCeti.Analysis.Sobolev.Local.ChainRule.Continuity.Supercritical
public import TauCeti.Analysis.Sobolev.Local.Reflection.Continuity

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
  (`TauCeti.eLpNormWkp_planarReflection_higherReflectionCoeff_reflectionCore_le`).

The reflection `R u₀` need not take values in `W` away from the real axis: for `k ≥ 1` it is a
combination of values of `u₀` with weights of both signs. It does take values in `W` on an open
neighbourhood `O` of `K`, because it is continuous and equals `u₀` on `K`. The interior theorem on
`O` gives `g ∘ R uₙ → g ∘ R u₀` in `W^{k+1,p}(K)`, and on `K`, which lies in the closed upper
half-plane, `g ∘ R uₙ - g ∘ R u₀ = g ∘ uₙ - g ∘ u₀`.

For `1 < p` and `kp > 2`, a `C^{k+1}` outer map acts continuously for convergence in the
local `W^{k,p}` norms alone. The limit has a continuous representative up to the real axis by
Morrey's embedding. Reflecting that representative and the approximating maps reduces
the result to continuity of supercritical composition on the open reflection core.

## Main declarations

* `TauCeti.MemWkpLoc.tendsto_eLpNormWkp_succ_comp_sub_inter_setOf_im_nonneg`: continuity of
  composition with a `C^{k+1}` map in `W^{k+1,p}` on compact subsets of `Ω ∩ {0 ≤ im}`.
* `TauCeti.MemWkpLoc.tendsto_eLpNormWkp_comp_sub_of_two_lt_mul_inter_setOf_im_nonneg`:
  continuity in the full supercritical range for `g` defined near the image of the limit.
* `TauCeti.MemWkpLoc.tendsto_eLpNormWkp_comp_sub_of_contDiff_inter_setOf_im_nonneg`: the same
  for a globally `C^{k+1}` map and arbitrary representatives.

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
/-- On a subset of the closed upper half-plane, composition with reflected maps gives
the same Sobolev differences as composition with the original maps. -/
private theorem tendsto_comp_sub_of_planarReflection {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {ι : Type*} {l : Filter ι} {v : ι → ℂ → F} {u : ℂ → F} {g : F → G}
    {k : ℕ} {K : Set ℂ} (hKU : K ⊆ {z | 0 ≤ z.im})
    (ht : Tendsto (fun n ↦ eLpNormWkp p K k
      (g ∘ planarReflection (higherReflectionCoeff k) (v n) -
        g ∘ planarReflection (higherReflectionCoeff k) u)) l (𝓝 0)) :
    Tendsto (fun n ↦ eLpNormWkp p K k (g ∘ v n - g ∘ u)) l (𝓝 0) := by
  have he (w : ℂ → F) : planarReflection (higherReflectionCoeff k) w =ᵐ[volume.restrict K] w := by
    simpa only [inter_eq_self_of_subset_left hKU] using
      planarReflection_ae_eq_inter_setOf_im_nonneg (higherReflectionCoeff k) w K
  exact ht.congr fun n ↦ eLpNormWkp_congr_ae (((he (v n)).fun_comp g).sub ((he u).fun_comp g))

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
    (fun _ hK'O hK' => tendsto_eLpNormWkp_planarReflection_sub hp1 hlim hK'
      (hK'O.trans (hOV.trans (Opens.reflectionCore_mono (subset_closure.trans hVΩ)))))
    K hKO hK
  exact tendsto_comp_sub_of_planarReflection (hKU.trans inter_subset_right) h

/-- For `kp > 2` and finite `p > 1`, composition with a `C^{k+1}` map is continuous in local
`W^{k,p}` norms up to the real axis. The compact sets of convergence may meet the boundary. -/
theorem MemWkpLoc.tendsto_eLpNormWkp_comp_sub_of_two_lt_mul_inter_setOf_im_nonneg
    {G : Type uG} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (hp : 1 < p) {k : ℕ} (hkp : 2 < (k : ℝ≥0) * p)
    {ι : Type*} {l : Filter ι} {v : ι → ℂ → F} {u : ℂ → F} {g : F → G} {W : Set F}
    (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k u)
    (huc : ContinuousOn u ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) (hW : IsOpen W)
    (hg : ContDiffOn ℝ (k + 1) g W) (huW : MapsTo u ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) W)
    (hlim : ∀ K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, IsCompact K →
      Tendsto (fun n ↦ eLpNormWkp p K k (v n - u)) l (𝓝 0)) :
    ∀ K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, IsCompact K →
      Tendsto (fun n ↦ eLpNormWkp p K k (g ∘ v n - g ∘ u)) l (𝓝 0) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp.le
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hkp)
  let R := TauCeti.planarReflection (F := F) (higherReflectionCoeff k)
  have hc : ContinuousOn (R u) Ω.reflectionCore :=
    continuousOn_planarReflection (sum_higherReflectionCoeff hk)
      Opens.imDilation_higherReflectionNode_mem_reflectionCore_of_im_neg (by simpa using huc)
  let O : Opens ℂ := ⟨Ω.reflectionCore ∩ R u ⁻¹' W,
    hc.isOpen_inter_preimage Ω.reflectionCore.isOpen hW⟩
  have hO : (O : Set ℂ) ⊆ Ω.reflectionCore := inter_subset_left
  have hR := (hu.planarReflection_higherReflectionCoeff_reflectionCore hp1).mono hO
  intro K hKU hK
  have hKO : K ⊆ O := fun z hz ↦ ⟨Ω.inter_setOf_im_nonneg_subset_reflectionCore (hKU hz), by
    simpa only [mem_preimage, R, planarReflection_of_nonneg _ _ (hKU hz).2] using huW (hKU hz)⟩
  have ht := hR.tendsto_eLpNormWkp_comp_sub_of_two_lt_mul hp hkp (hc.mono hO) hW hg
    (fun z hz ↦ hz.2) (fun _ hK'O hK' ↦
      tendsto_eLpNormWkp_planarReflection_sub hp1 hlim hK' (hK'O.trans hO)) K hKO hK
  exact tendsto_comp_sub_of_planarReflection (hKU.trans inter_subset_right) ht

/-- A globally `C^{k+1}` map preserves supercritical local Sobolev convergence up to the real
axis for arbitrary almost-everywhere representatives. -/
theorem MemWkpLoc.tendsto_eLpNormWkp_comp_sub_of_contDiff_inter_setOf_im_nonneg
    {G : Type uG} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (hp : 1 < p) {k : ℕ} (hkp : 2 < (k : ℝ≥0) * p)
    {ι : Type*} {l : Filter ι} {v : ι → ℂ → F} {u : ℂ → F} {g : F → G}
    (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k u) (hg : ContDiff ℝ (k + 1) g)
    (hlim : ∀ K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, IsCompact K →
      Tendsto (fun n ↦ eLpNormWkp p K k (v n - u)) l (𝓝 0)) :
    ∀ K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, IsCompact K →
      Tendsto (fun n ↦ eLpNormWkp p K k (g ∘ v n - g ∘ u)) l (𝓝 0) := by
  intro K hKU hK
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp.le
  apply tendsto_comp_sub_of_planarReflection (hKU.trans inter_subset_right)
  have hR := hu.planarReflection_higherReflectionCoeff_reflectionCore hp1
  exact hR.tendsto_eLpNormWkp_comp_sub_of_contDiff
    hp hkp hg (fun _ hK'Ω hK' ↦ tendsto_eLpNormWkp_planarReflection_sub hp1 hlim hK' hK'Ω)
    K (hKU.trans Ω.inter_setOf_im_nonneg_subset_reflectionCore) hK


/-- The check at `p = 4/3` and `k = 2`, outside the range `p > 2` of
`TauCeti.MemWkpLoc.tendsto_eLpNormWkp_succ_comp_sub_inter_setOf_im_nonneg`: squaring is continuous
along maps converging in `W^{2,4/3}` on compact subsets of `Ω ∩ {0 ≤ im}`. -/
example {ι : Type*} {l : Filter ι} {u : ι → ℂ → ℝ} {u₀ : ℂ → ℝ}
    (hu₀ : MemWkpLoc (4 / 3 : ℝ≥0) ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 2 u₀)
    (hlim : ∀ K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, IsCompact K →
      Tendsto (fun n => eLpNormWkp (4 / 3 : ℝ≥0) K 2 (u n - u₀)) l (𝓝 0))
    (K : Set ℂ) (hKS : K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (hK : IsCompact K) :
    Tendsto (fun n => eLpNormWkp (4 / 3 : ℝ≥0) K 2 ((fun x => x ^ 2) ∘ u n - (fun x => x ^ 2) ∘ u₀))
      l (𝓝 0) :=
  hu₀.tendsto_eLpNormWkp_comp_sub_of_contDiff_inter_setOf_im_nonneg (by norm_num) (by norm_num)
    (contDiff_id.pow 2) hlim K hKS hK

end TauCeti
