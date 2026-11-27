/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Analysis.Calculus.Hadamard.Basic
import TauCeti.Analysis.Sobolev.Local.ChainRule.Bound.HalfDisc
import TauCeti.Analysis.Sobolev.Local.Multiplication.HalfDisc.Bound.Supercritical
import TauCeti.Topology.Sets.Opens

/-!
# Local Lipschitz bound for composition on half-discs for `kp > 2`

Let `Ω ⊆ ℂ` be open and write `Ω⁺ = Ω ∩ {0 ≤ im}`. Let `1 < p` and `k p > 2`, and let `F` and `G`
be finite-dimensional. This file proves a local Lipschitz bound on half-discs
(`TauCeti.exists_eLpNormWkp_comp_sub_le_of_two_lt_mul_halfPlane`): for a globally `C^{k+1}` map
`g`, a compact set `L` and a set `U` with compact closure in `Ω`, with `U⁺ = U ∩ {0 ≤ im}` and
`‖·‖_k = ‖·‖_{W^{k,p}(Ω⁺)}`,

`‖g ∘ v - g ∘ u‖_{W^{k,p}(U⁺)} ≤ C (1 + ‖u‖_k + ‖v‖_k)^k ‖v - u‖_k`

for all continuous `u` and `v` mapping `Ω⁺` into `L`. This includes `p ≤ 2` for `k ≥ 2`, and the
set `U` may meet the real axis. By Hadamard's lemma (`ContDiff.sub_eq_hadamardFactor_apply`),
`g (v z) - g (u z) = H(u z, v z) (v z - u z)` for the averaged derivative
`H = TauCeti.hadamardFactor g`, which is `Cᵏ` jointly in both points. The half-disc composition
bound `TauCeti.exists_eLpNormWkp_comp_le_of_two_lt_mul_halfPlane` for `H` on `L × L` and the
half-disc product bound `TauCeti.exists_eLpNormWkp_clm_apply_le_of_two_lt_mul_halfPlane` for
evaluation give the estimate.

Continuity of composition in `W^{k,p}` on compact subsets of `Ω⁺` for `kp > 2` is
`TauCeti.MemWkpLoc.tendsto_eLpNormWkp_comp_sub_of_two_lt_mul_inter_setOf_im_nonneg`, proved by
higher-order reflection.

## Main declarations

* `TauCeti.exists_eLpNormWkp_comp_sub_le_of_two_lt_mul_halfPlane`: the local Lipschitz bound for
  composition with a `C^{k+1}` map in `W^{k,p}` on half-discs, for `kp > 2`.

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

end TauCeti
