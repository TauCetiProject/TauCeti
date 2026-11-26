/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.Hadamard.Basic
import TauCeti.Analysis.Sobolev.Local.ChainRule.Bound.Supercritical
import TauCeti.Analysis.Sobolev.Local.Multiplication.Bound.Supercritical
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Topology.Sets.Opens
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp

/-!
# Continuity of composition in `W^{k,p}_loc` for `kp > 2`, including `p ≤ 2`

Let `Ω ⊆ ℂ` be open, let `1 < p` and `k p > 2`, and let `F` and `G` be finite-dimensional. Let
`g : F → G` be `C^{k+1}` on an open set `W` and let `u₀ ∈ W^{k,p}_loc(Ω)` be continuous with
`u₀(Ω) ⊆ W`. If continuous maps `uₙ` converge to `u₀` in `W^{k,p}` on every compact subset of
`Ω`, then `g ∘ uₙ → g ∘ u₀` in `W^{k,p}` on every compact subset of `Ω`
(`TauCeti.MemWkpLoc.tendsto_eLpNormWkp_comp_sub_of_two_lt_mul`). This includes `p ≤ 2` for
`k ≥ 2`, for instance `k = 2` and `p = 4/3`. No locally uniform convergence is assumed: for
`kp > 2` it follows from the convergence in `W^{k,p}`
(`TauCeti.tendstoLocallyUniformlyOn_of_tendsto_eLpNormWkp_of_two_lt_mul`).

The continuity comes from a local Lipschitz bound
(`TauCeti.exists_eLpNormWkp_comp_sub_le_of_two_lt_mul`): for a globally `C^{k+1}` map `g`, a
compact set `L` and a set `U` with compact closure in `Ω`,

`‖g ∘ v - g ∘ u‖_{W^{k,p}(U)} ≤ C (1 + ‖u‖_{W^{k,p}(Ω)} + ‖v‖_{W^{k,p}(Ω)})^k ‖v - u‖_{W^{k,p}(Ω)}`

for all continuous `u` and `v` mapping `Ω` into `L`. By Hadamard's lemma
(`ContDiff.sub_eq_hadamardFactor_apply`), `g (v z) - g (u z) = H(u z, v z) (v z - u z)` for the
averaged derivative `H = TauCeti.hadamardFactor g`, which is `Cᵏ` jointly in both points. The
composition bound `TauCeti.exists_eLpNormWkp_comp_le_of_two_lt_mul` for `H` on `L × L` and the
product bound `TauCeti.exists_eLpNormWkp_clm_apply_le_of_two_lt_mul` for evaluation give the
estimate. For `g` that is `C^{k+1}` only on `W`, the continuity theorem replaces `g` by a global
`C^{k+1}` map that agrees with it on a compact neighbourhood of `u₀(K)` in `W`, which contains
`uₙ(K)` eventually by the locally uniform convergence.

For `p > 2` the theorem `TauCeti.MemWkpLoc.tendsto_eLpNormWkp_succ_comp_sub` needs only `g ∈ Cᵏ`
at order `k`, under a locally uniform convergence hypothesis;
`TauCeti.MemWkpLoc.tendsto_eLpNormWkp_succ_comp_sub_of_continuousOn` is that theorem without it.

## Main declarations

* `TauCeti.exists_eLpNormWkp_comp_sub_le_of_two_lt_mul`: the local Lipschitz bound for
  composition with a `C^{k+1}` map in `W^{k,p}`, for `kp > 2`.
* `TauCeti.MemWkpLoc.tendsto_eLpNormWkp_comp_sub_of_two_lt_mul`: continuity of composition with a
  `C^{k+1}` map in `W^{k,p}` on compact subsets, for `kp > 2`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (composition in local Sobolev spaces).
-/

public noncomputable section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] {Ω : Opens ℂ}

/-- **Local Lipschitz bound for composition for `kp > 2`.** Let `1 < p` and `k p > 2`, let
`g : F → G` be `C^{k+1}`, let `L ⊆ F` be compact and let `U` have compact closure contained in
`Ω`. There is a constant `C` such that
`‖g ∘ v - g ∘ u‖_{W^{k,p}(U)} ≤ C (1 + ‖u‖_{W^{k,p}(Ω)} + ‖v‖_{W^{k,p}(Ω)})^k ‖v - u‖_{W^{k,p}(Ω)}`
for all `u` and `v` continuous on `Ω` with `u(Ω), v(Ω) ⊆ L`. This includes `p ≤ 2` for
`k ≥ 2`. -/
theorem exists_eLpNormWkp_comp_sub_le_of_two_lt_mul {p : ℝ≥0} (hp : 1 < p) {k : ℕ}
    (hkp : 2 < (k : ℝ≥0) * p) {g : F → G} (hg : ContDiff ℝ (k + 1) g) {L : Set F}
    (hL : IsCompact L) {U : Set ℂ} (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ u v : ℂ → F, ContinuousOn u Ω → MapsTo u Ω L → ContinuousOn v Ω →
      MapsTo v Ω L →
      eLpNormWkp p U k (fun z => g (v z) - g (u z)) ≤
        C * (1 + (eLpNormWkp p Ω k u + eLpNormWkp p Ω k v)) ^ k *
          eLpNormWkp p Ω k (v - u) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp.le
  obtain ⟨V, hUV, hVΩ, hVc⟩ := Opens.exists_between_and_isCompact_closure hU hUΩ
  -- The product bound for evaluation `(A, w) ↦ A w`, from `V` to `U`.
  obtain ⟨N, hN⟩ := exists_eLpNormWkp_clm_apply_le_of_two_lt_mul (F := F) (G := G) (Ω := V) hp hkp
    hU hUV
  -- The composition bound for the averaged derivative `H`, from `Ω` to `V`.
  obtain ⟨M, hM⟩ := exists_eLpNormWkp_comp_le_of_two_lt_mul (Ω := Ω) hp hkp
    (g := fun q : F × F => hadamardFactor g q.1 q.2) isOpen_univ
    (ContDiff.contDiff_hadamardFactor_uncurry_of_succ k g (by exact_mod_cast hg)).contDiffOn
    (hL.prod hL) (subset_univ _) hVc hVΩ
  refine ⟨N * M, fun u v huc huL hvc hvL => ?_⟩
  -- Hadamard's lemma: `g (v z) - g (u z) = H(u z, v z) (v z - u z)`.
  have hfun : (fun z => g (v z) - g (u z)) = fun z =>
      hadamardFactor g (u z) (v z) ((v - u) z) :=
    funext fun z => by
      simp [ContDiff.sub_eq_hadamardFactor_apply g (hg.of_le (by simp)) (u z) (v z)]
  have hH := hM (fun z => (u z, v z)) (huc.prodMk hvc) fun z hz => ⟨huL hz, hvL hz⟩
  rw [hfun]
  calc
    _ ≤ N * eLpNormWkp p V k (fun z => hadamardFactor g (u z) (v z)) *
        eLpNormWkp p V k (v - u) :=
      hN (fun z => hadamardFactor g (u z) (v z)) (v - u)
    _ ≤ N * (M * (1 + eLpNormWkp p Ω k (fun z => (u z, v z))) ^ k) *
        eLpNormWkp p Ω k (v - u) := by
      gcongr
      exact eLpNormWkp_mono_set (subset_closure.trans hVΩ)
    _ ≤ N * (M * (1 + (eLpNormWkp p Ω k u + eLpNormWkp p Ω k v)) ^ k) *
        eLpNormWkp p Ω k (v - u) := by
      gcongr
      exact eLpNormWkp_prodMk_le hp1
    _ = _ := by
      push_cast
      ring

/-- The bound in `TauCeti.MemWkpLoc.tendsto_eLpNormWkp_comp_sub_of_two_lt_mul` tends to `0`:
if `cₙ → 0` and `a` is finite, then `C (1 + (a + (a + cₙ)))^k cₙ → 0`. -/
private theorem tendsto_mul_one_add_pow_mul {ι : Type*} {l : Filter ι} {c : ι → ℝ≥0∞}
    (hc : Tendsto c l (𝓝 0)) {a : ℝ≥0∞} (ha : a ≠ ∞) (C : ℝ≥0) (k : ℕ) :
    Tendsto (fun n => C * (1 + (a + (a + c n))) ^ k * c n) l (𝓝 0) := by
  have h₁ : Tendsto (fun n => (C : ℝ≥0∞) * (1 + (a + (a + c n))) ^ k) l
      (𝓝 (C * (1 + (a + (a + 0))) ^ k)) :=
    ENNReal.Tendsto.const_mul (ENNReal.Tendsto.pow (tendsto_const_nhds.add
      (tendsto_const_nhds.add (tendsto_const_nhds.add hc)))) (Or.inr ENNReal.coe_ne_top)
  have hfin : (C : ℝ≥0∞) * (1 + (a + (a + 0))) ^ k ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top (by simp [ha]))
  simpa using ENNReal.Tendsto.mul h₁ (Or.inr ENNReal.zero_ne_top) hc (Or.inr hfin)

/-- **Continuity of composition in `W^{k,p}_loc` for `kp > 2`.** Let `1 < p` and `k p > 2`, let
`g : F → G` be `C^{k+1}` on an open set `W`, and let `u₀ ∈ W^{k,p}_loc(Ω)` be continuous on `Ω`
with `u₀(Ω) ⊆ W`. For every compact `K ⊆ Ω` let maps `uₙ` be eventually continuous on `K` with
`‖uₙ - u₀‖_{W^{k,p}(K)} → 0`. Then `‖g ∘ uₙ - g ∘ u₀‖_{W^{k,p}(K)} → 0` for every compact
`K ⊆ Ω`. This includes `p ≤ 2` for `k ≥ 2`. -/
theorem MemWkpLoc.tendsto_eLpNormWkp_comp_sub_of_two_lt_mul {p : ℝ≥0} (hp : 1 < p) {k : ℕ}
    (hkp : 2 < (k : ℝ≥0) * p) {ι : Type*} {l : Filter ι} {u : ι → ℂ → F} {u₀ : ℂ → F}
    {g : F → G} {W : Set F} (hu₀ : MemWkpLoc p Ω k u₀) (hu₀c : ContinuousOn u₀ Ω)
    (hW : IsOpen W) (hg : ContDiffOn ℝ (k + 1) g W) (hu₀W : MapsTo u₀ Ω W)
    (huc : ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∀ᶠ n in l, ContinuousOn (u n) K)
    (hlim : ∀ K ⊆ (Ω : Set ℂ), IsCompact K →
      Tendsto (fun n => eLpNormWkp p K k (u n - u₀)) l (𝓝 0)) :
    ∀ K ⊆ (Ω : Set ℂ), IsCompact K →
      Tendsto (fun n => eLpNormWkp p K k (g ∘ u n - g ∘ u₀)) l (𝓝 0) := by
  intro K hKΩ hK
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp.le
  have hunif := tendstoLocallyUniformlyOn_of_tendsto_eLpNormWkp_of_two_lt_mul hp1
    (by exact_mod_cast hkp) huc hu₀c hlim
  obtain ⟨V, hKV, hVΩ, hVc⟩ := Opens.exists_between_and_isCompact_closure hK hKΩ
  -- A compact neighbourhood `L` of `u₀(closure V)` in `W`, and a global `C^{k+1}` map `g'` that
  -- agrees with `g` on `L`.
  have hcpt : IsCompact (u₀ '' closure V) := hVc.image_of_continuousOn (hu₀c.mono hVΩ)
  obtain ⟨L, hL, hL₀, hLW⟩ :=
    exists_compact_between hcpt hW (image_subset_iff.2 (hu₀W.mono_left hVΩ))
  obtain ⟨g', hg', -, -, -, hg'g⟩ :=
    hg.exists_contDiff_eventuallyEq_on_isCompact (n := k + 1) hL hW hLW
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_comp_sub_le_of_two_lt_mul hp hkp
    (by exact_mod_cast hg' : ContDiff ℝ (k + 1) g') hL (U := K) (Ω := V)
    (by rwa [hK.isClosed.closure_eq]) (by rw [hK.isClosed.closure_eq]; exact hKV)
  -- Eventually `uₙ` is continuous on `closure V` and maps it into `L`.
  have hunifV : TendstoUniformlyOn u u₀ l (closure V) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact Ω.isOpen).1 hunif _ hVΩ hVc
  have hmaps := hunifV.eventually_mapsTo (mapsTo_image u₀ _) hcpt
    (isOpen_interior.mem_nhdsSet.2 hL₀)
  have hu₀L : MapsTo u₀ V L := fun z hz =>
    interior_subset (hL₀ (mem_image_of_mem u₀ (subset_closure hz)))
  have hu₀V : eLpNormWkp p V k u₀ ≠ ∞ := hu₀.eLpNormWkp_ne_top_of_closure_subset hVc hVΩ
  have hT := hlim (closure V) hVΩ hVc
  have key : ∀ᶠ n in l, eLpNormWkp p K k (g ∘ u n - g ∘ u₀) ≤
      C * (1 + (eLpNormWkp p V k u₀ + (eLpNormWkp p V k u₀ +
        eLpNormWkp p (closure V) k (u n - u₀)))) ^ k * eLpNormWkp p (closure V) k (u n - u₀) := by
    filter_upwards [huc _ hVΩ hVc, hmaps] with n hnc hnL
    have hnL' : MapsTo (u n) V L := fun z hz => interior_subset (hnL (subset_closure hz))
    -- On `K`, the maps `g` and `g'` agree along `uₙ` and `u₀`.
    have hae : (g ∘ u n - g ∘ u₀) =ᵐ[volume.restrict K] fun z => g' (u n z) - g' (u₀ z) :=
      (ae_restrict_mem hK.measurableSet).mono fun z hz => by
        simp [(hg'g _ (hnL' (hKV hz))).eq_of_nhds, (hg'g _ (hu₀L (hKV hz))).eq_of_nhds]
    have hVcl : eLpNormWkp p V k (u n - u₀) ≤ eLpNormWkp p (closure V) k (u n - u₀) :=
      eLpNormWkp_mono_set subset_closure
    rw [eLpNormWkp_congr_ae hae]
    refine (hC u₀ (u n) (hu₀c.mono fun z hz => hVΩ (subset_closure hz)) hu₀L
      (hnc.mono subset_closure) hnL').trans ?_
    gcongr
    calc eLpNormWkp p V k (u n) = eLpNormWkp p V k ((u n - u₀) + u₀) := by rw [sub_add_cancel]
      _ ≤ eLpNormWkp p V k (u n - u₀) + eLpNormWkp p V k u₀ := eLpNormWkp_add_le hp1
      _ ≤ _ := by rw [add_comm]; gcongr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_mul_one_add_pow_mul hT hu₀V C k) (.of_forall fun _ => zero_le) key

/-- The check at `p = 4/3` and `k = 2`, outside the range `p > 2` of
`TauCeti.MemWkpLoc.tendsto_eLpNormWkp_succ_comp_sub`: squaring is continuous along continuous maps
converging in `W^{2,4/3}` on compact sets. -/
example {ι : Type*} {l : Filter ι} {u : ι → ℂ → ℝ} {u₀ : ℂ → ℝ}
    (hu₀ : MemWkpLoc (4 / 3 : ℝ≥0) Ω 2 u₀) (hu₀c : ContinuousOn u₀ Ω)
    (huc : ∀ n, ContinuousOn (u n) Ω)
    (hlim : ∀ K ⊆ (Ω : Set ℂ), IsCompact K →
      Tendsto (fun n => eLpNormWkp (4 / 3 : ℝ≥0) K 2 (u n - u₀)) l (𝓝 0))
    (K : Set ℂ) (hKΩ : K ⊆ Ω) (hK : IsCompact K) :
    Tendsto (fun n => eLpNormWkp (4 / 3 : ℝ≥0) K 2 ((fun x => x ^ 2) ∘ u n - (fun x => x ^ 2) ∘ u₀))
      l (𝓝 0) :=
  hu₀.tendsto_eLpNormWkp_comp_sub_of_two_lt_mul (by norm_num) (by norm_num) hu₀c isOpen_univ
    (contDiff_id.pow 2).contDiffOn (mapsTo_univ _ _)
    (fun K hKΩ _ => .of_forall fun n => (huc n).mono hKΩ) hlim K hKΩ hK

end TauCeti
