/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.Hadamard.Basic
import TauCeti.Analysis.Sobolev.Local.ChainRule.Bound.HalfDisc
import TauCeti.Analysis.Sobolev.Local.Morrey.HalfDisc.Higher
import TauCeti.Analysis.Sobolev.Local.Multiplication.HalfDisc.Bound.Supercritical
import TauCeti.Topology.Instances.ENNReal
import TauCeti.Topology.Sets.Opens
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp

/-!
# Continuity of composition in `W^{k,p}_loc` up to the real axis for `kp > 2`

Let `Ω ⊆ ℂ` be open and write `Ω⁺ = Ω ∩ {0 ≤ im}`. Let `1 < p` and `k p > 2`, and let `F` and `G`
be finite-dimensional. Let `g : F → G` be `C^{k+1}` on an open set `W` and let
`u₀ ∈ MemWkpLoc p Ω⁺ k` be continuous on `Ω⁺` with `u₀(Ω⁺) ⊆ W`. If maps `uₙ`, eventually
continuous on every compact subset of `Ω⁺`, converge to `u₀` in `W^{k,p}` on every compact subset
of `Ω⁺`, then `g ∘ uₙ → g ∘ u₀` in `W^{k,p}` on every compact subset of `Ω⁺`, including compact
sets that meet the real axis
(`TauCeti.MemWkpLoc.tendsto_eLpNormWkp_comp_sub_of_two_lt_mul_inter_setOf_im_nonneg`). This
includes `p ≤ 2` for `k ≥ 2`, for instance `k = 2` and `p = 4/3`. No locally uniform convergence
is assumed: for `kp > 2` it follows from the convergence in `W^{k,p}`
(`TauCeti.tendstoLocallyUniformlyOn_of_tendsto_eLpNormWkp_of_two_lt_mul_inter_setOf_im_nonneg`).

The continuity comes from a local Lipschitz bound on half-discs
(`TauCeti.exists_eLpNormWkp_comp_sub_le_of_two_lt_mul_halfPlane`): for a globally `C^{k+1}` map
`g`, a compact set `L` and a set `U` with compact closure in `Ω`, with `U⁺ = U ∩ {0 ≤ im}` and
`‖·‖_k = ‖·‖_{W^{k,p}(Ω⁺)}`,

`‖g ∘ v - g ∘ u‖_{W^{k,p}(U⁺)} ≤ C (1 + ‖u‖_k + ‖v‖_k)^k ‖v - u‖_k`

for all continuous `u` and `v` mapping `Ω⁺` into `L`. By Hadamard's lemma
(`ContDiff.sub_eq_hadamardFactor_apply`), `g (v z) - g (u z) = H(u z, v z) (v z - u z)` for the
averaged derivative `H = TauCeti.hadamardFactor g`, which is `Cᵏ` jointly in both points. The
half-disc composition bound `TauCeti.exists_eLpNormWkp_comp_le_of_two_lt_mul_halfPlane` for `H` on
`L × L` and the half-disc product bound
`TauCeti.exists_eLpNormWkp_clm_apply_le_of_two_lt_mul_halfPlane` for evaluation give the estimate.
For `g` that is `C^{k+1}` only on `W`, the continuity theorem replaces `g` by a global `C^{k+1}` map
that agrees with it on a compact neighbourhood of the image under `u₀` of a compact neighbourhood of
`K` in `Ω⁺`, which contains the image under `uₙ` eventually, by the locally uniform convergence.

For `p > 2`, `TauCeti.MemWkpLoc.tendsto_eLpNormWkp_succ_comp_sub_inter_setOf_im_nonneg` needs only
`g ∈ C^{k+1}` at order `k + 1`, under a locally uniform convergence hypothesis.

## Main declarations

* `TauCeti.exists_eLpNormWkp_comp_sub_le_of_two_lt_mul_halfPlane`: the local Lipschitz bound for
  composition with a `C^{k+1}` map in `W^{k,p}` on half-discs, for `kp > 2`.
* `TauCeti.MemWkpLoc.tendsto_eLpNormWkp_comp_sub_of_two_lt_mul_inter_setOf_im_nonneg`: continuity
  of composition with a `C^{k+1}` map in `W^{k,p}` on compact subsets of `Ω ∩ {0 ≤ im}`, for
  `kp > 2`.

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

/-- **Local Lipschitz bound for composition on half-discs for `kp > 2`.** Let `1 < p` and
`k p > 2`, let `g : F → G` be `C^{k+1}`, let `L ⊆ F` be compact and let `U` have compact closure
contained in `Ω`. There is a constant `C` such that, with `U⁺ = U ∩ {0 ≤ im}` and
`Ω⁺ = Ω ∩ {0 ≤ im}` and `‖·‖_k = ‖·‖_{W^{k,p}(Ω⁺)}`,
`‖g ∘ v - g ∘ u‖_{W^{k,p}(U⁺)} ≤ C (1 + ‖u‖_k + ‖v‖_k)^k ‖v - u‖_k`
for all `u` and `v` continuous on `Ω⁺` with `u(Ω⁺), v(Ω⁺) ⊆ L`. This includes `p ≤ 2` for
`k ≥ 2`; the set `U` may meet the real axis. -/
theorem exists_eLpNormWkp_comp_sub_le_of_two_lt_mul_halfPlane {p : ℝ≥0} (hp : 1 < p) {k : ℕ}
    (hkp : 2 < (k : ℝ≥0) * p) {g : F → G} (hg : ContDiff ℝ (k + 1) g) {L : Set F}
    (hL : IsCompact L) {U : Set ℂ} (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ u v : ℂ → F, ContinuousOn u ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) →
      MapsTo u ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) L →
      ContinuousOn v ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) →
      MapsTo v ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) L →
      eLpNormWkp p (U ∩ {z | 0 ≤ z.im}) k (fun z => g (v z) - g (u z)) ≤
        C * (1 + (eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k u +
          eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k v)) ^ k *
          eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k (v - u) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp.le
  set S := (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}
  obtain ⟨V, hUV, hVΩ, hVc⟩ := Opens.exists_between_and_isCompact_closure hU hUΩ
  -- The product bound for evaluation `(A, w) ↦ A w`, from `V⁺` to `U⁺`.
  obtain ⟨N, hN⟩ := exists_eLpNormWkp_clm_apply_le_of_two_lt_mul_halfPlane (F := F) (G := G)
    (Ω := V) hp hkp hU hUV
  -- The composition bound for the averaged derivative `H`, from `Ω⁺` to `V⁺`.
  obtain ⟨M, hM⟩ := exists_eLpNormWkp_comp_le_of_two_lt_mul_halfPlane (Ω := Ω) hp hkp
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
  have hVS : (V : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ S :=
    inter_subset_inter_left _ (subset_closure.trans hVΩ)
  rw [hfun]
  calc
    _ ≤ N * eLpNormWkp p ((V : Set ℂ) ∩ {z | 0 ≤ z.im}) k
          (fun z => hadamardFactor g (u z) (v z)) *
        eLpNormWkp p ((V : Set ℂ) ∩ {z | 0 ≤ z.im}) k (v - u) :=
      hN (fun z => hadamardFactor g (u z) (v z)) (v - u)
    _ ≤ N * (M * (1 + eLpNormWkp p S k (fun z => (u z, v z))) ^ k) * eLpNormWkp p S k (v - u) := by
      gcongr
      exact eLpNormWkp_mono_set hVS
    _ ≤ N * (M * (1 + (eLpNormWkp p S k u + eLpNormWkp p S k v)) ^ k) *
        eLpNormWkp p S k (v - u) := by
      gcongr
      exact eLpNormWkp_prodMk_le hp1
    _ = _ := by
      push_cast
      ring

/-- **Continuity of composition in `W^{k,p}_loc` up to the real axis for `kp > 2`.** Let `1 < p`
and `k p > 2`, let `g : F → G` be `C^{k+1}` on an open set `W`, and let
`u₀ ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) k` be continuous on `Ω ∩ {0 ≤ im}` with
`u₀(Ω ∩ {0 ≤ im}) ⊆ W`. For every compact `K ⊆ Ω ∩ {0 ≤ im}` let maps `uₙ` be eventually
continuous on `K` with `‖uₙ - u₀‖_{W^{k,p}(K)} → 0`. Then `‖g ∘ uₙ - g ∘ u₀‖_{W^{k,p}(K)} → 0` for
every compact `K ⊆ Ω ∩ {0 ≤ im}`, including compact sets that meet the real axis. This includes
`p ≤ 2` for `k ≥ 2`. -/
theorem MemWkpLoc.tendsto_eLpNormWkp_comp_sub_of_two_lt_mul_inter_setOf_im_nonneg {p : ℝ≥0}
    (hp : 1 < p) {k : ℕ} (hkp : 2 < (k : ℝ≥0) * p) {ι : Type*} {l : Filter ι} {u : ι → ℂ → F}
    {u₀ : ℂ → F} {g : F → G} {W : Set F}
    (hu₀ : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k u₀)
    (hu₀c : ContinuousOn u₀ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) (hW : IsOpen W)
    (hg : ContDiffOn ℝ (k + 1) g W) (hu₀W : MapsTo u₀ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) W)
    (huc : ∀ K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, IsCompact K → ∀ᶠ n in l, ContinuousOn (u n) K)
    (hlim : ∀ K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, IsCompact K →
      Tendsto (fun n => eLpNormWkp p K k (u n - u₀)) l (𝓝 0)) :
    ∀ K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, IsCompact K →
      Tendsto (fun n => eLpNormWkp p K k (g ∘ u n - g ∘ u₀)) l (𝓝 0) := by
  intro K hKS hK
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp.le
  have hunif := tendstoLocallyUniformlyOn_of_tendsto_eLpNormWkp_of_two_lt_mul_inter_setOf_im_nonneg
    hp1 (by exact_mod_cast hkp) huc hu₀c hlim
  -- An open `V ⊇ K` with compact closure in `Ω`, and the compact set `T = closure V ∩ {0 ≤ im}`.
  obtain ⟨V, hKV, hVΩ, hVc⟩ :=
    Opens.exists_between_and_isCompact_closure hK (hKS.trans inter_subset_left)
  set T := closure (V : Set ℂ) ∩ {z | 0 ≤ z.im}
  have hT : IsCompact T := hVc.inter_right (Complex.isClosed_setOfPred_le_im 0)
  have hTS : T ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} := inter_subset_inter_left _ hVΩ
  set P := (V : Set ℂ) ∩ {z | 0 ≤ z.im}
  have hVT : P ⊆ T := inter_subset_inter_left _ subset_closure
  -- A compact neighbourhood `L` of `u₀(T)` in `W`, and a global `C^{k+1}` map `g'` that agrees
  -- with `g` on `L`.
  have hcpt : IsCompact (u₀ '' T) := hT.image_of_continuousOn (hu₀c.mono hTS)
  obtain ⟨L, hL, hL₀, hLW⟩ :=
    exists_compact_between hcpt hW (image_subset_iff.2 (hu₀W.mono_left hTS))
  obtain ⟨g', hg', -, -, -, hg'g⟩ :=
    hg.exists_contDiff_eventuallyEq_on_isCompact (n := k + 1) hL hW hLW
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_comp_sub_le_of_two_lt_mul_halfPlane hp hkp
    (by exact_mod_cast hg' : ContDiff ℝ (k + 1) g') hL (U := K) (Ω := V)
    (by rwa [hK.isClosed.closure_eq]) (by rw [hK.isClosed.closure_eq]; exact hKV)
  -- Eventually `uₙ` is continuous on `T` and maps it into `L`.
  have hmaps := ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hT).1
    (hunif.mono hTS)).eventually_mapsTo (mapsTo_image u₀ _) hcpt
    (isOpen_interior.mem_nhdsSet.2 hL₀)
  have hu₀L : MapsTo u₀ P L := fun z hz => interior_subset (hL₀ (mem_image_of_mem u₀ (hVT hz)))
  have hu₀V : eLpNormWkp p P k u₀ ≠ ∞ :=
    ne_top_of_le_ne_top (hu₀.eLpNormWkp_ne_top_of_isCompact hTS hT) (eLpNormWkp_mono_set hVT)
  have hKH : K ∩ {z | 0 ≤ z.im} = K := inter_eq_left.2 (hKS.trans inter_subset_right)
  have key : ∀ᶠ n in l, eLpNormWkp p K k (g ∘ u n - g ∘ u₀) ≤
      C * (1 + (eLpNormWkp p P k u₀ + (eLpNormWkp p P k u₀ + eLpNormWkp p T k (u n - u₀)))) ^ k *
        eLpNormWkp p T k (u n - u₀) := by
    filter_upwards [huc T hTS hT, hmaps] with n hnc hnL
    have hnL' : MapsTo (u n) P L := fun z hz => interior_subset (hnL (hVT hz))
    -- On `K`, the maps `g` and `g'` agree along `uₙ` and `u₀`.
    have hae : (g ∘ u n - g ∘ u₀) =ᵐ[volume.restrict K] fun z => g' (u n z) - g' (u₀ z) :=
      (ae_restrict_mem hK.measurableSet).mono fun z hz => by
        simp [(hg'g _ (hnL' ⟨hKV hz, (hKS hz).2⟩)).eq_of_nhds,
          (hg'g _ (hu₀L ⟨hKV hz, (hKS hz).2⟩)).eq_of_nhds]
    have hVcl : eLpNormWkp p P k (u n - u₀) ≤ eLpNormWkp p T k (u n - u₀) :=
      eLpNormWkp_mono_set hVT
    rw [eLpNormWkp_congr_ae hae, ← hKH]
    refine (hC u₀ (u n) (hu₀c.mono (hVT.trans hTS)) hu₀L (hnc.mono hVT) hnL').trans ?_
    gcongr
    calc eLpNormWkp p P k (u n) ≤ eLpNormWkp p P k (u n - u₀) + eLpNormWkp p P k u₀ := by
          simpa using eLpNormWkp_add_le (U := P) (f := u n - u₀) (g := u₀) hp1
      _ ≤ _ := by rw [add_comm]; gcongr
  have hbd := ENNReal.tendsto_mul_add_pow_mul_of_tendsto_zero (hlim T hTS hT) (C := C)
    ENNReal.coe_ne_top (b := 1 + (eLpNormWkp p P k u₀ + eLpNormWkp p P k u₀)) (by simp [hu₀V]) k
  simp only [add_assoc] at hbd
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbd
    (.of_forall fun _ => zero_le) key

/-- The check at `p = 4/3` and `k = 2`, outside the range `p > 2` of
`TauCeti.MemWkpLoc.tendsto_eLpNormWkp_succ_comp_sub_inter_setOf_im_nonneg`: squaring is continuous
along continuous maps converging in `W^{2,4/3}` on compact subsets of `Ω ∩ {0 ≤ im}`. -/
example {ι : Type*} {l : Filter ι} {u : ι → ℂ → ℝ} {u₀ : ℂ → ℝ}
    (hu₀ : MemWkpLoc (4 / 3 : ℝ≥0) ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 2 u₀)
    (hu₀c : ContinuousOn u₀ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (huc : ∀ n, ContinuousOn (u n) ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hlim : ∀ K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, IsCompact K →
      Tendsto (fun n => eLpNormWkp (4 / 3 : ℝ≥0) K 2 (u n - u₀)) l (𝓝 0))
    (K : Set ℂ) (hKS : K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (hK : IsCompact K) :
    Tendsto (fun n => eLpNormWkp (4 / 3 : ℝ≥0) K 2 ((fun x => x ^ 2) ∘ u n - (fun x => x ^ 2) ∘ u₀))
      l (𝓝 0) :=
  hu₀.tendsto_eLpNormWkp_comp_sub_of_two_lt_mul_inter_setOf_im_nonneg (by norm_num) (by norm_num)
    hu₀c isOpen_univ (contDiff_id.pow 2).contDiffOn (mapsTo_univ _ _)
    (fun K hKS _ => .of_forall fun n => (huc n).mono hKS) hlim K hKS hK

end TauCeti
