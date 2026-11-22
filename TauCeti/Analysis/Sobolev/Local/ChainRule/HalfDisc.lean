/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.ChainRule.Higher
import TauCeti.Analysis.Complex.ReImTopology
import TauCeti.Analysis.Sobolev.Local.HalfPlane
import TauCeti.Analysis.Sobolev.Local.Locality
import TauCeti.Analysis.Sobolev.Local.Reflection

/-!
# Composition of local Sobolev maps on half-discs at every order

Let `p > 2` and `k ≥ 0`. If `u` is continuous on the relatively open set `Ω ∩ {0 ≤ im}` of the
closed upper half-plane and belongs to `W^{k+1,p}_loc(Ω ∩ {0 ≤ im})` with finite-dimensional
values, and `g` is `C^{k+1}` on an open set `W` containing the image of `Ω ∩ {0 ≤ im}` under `u`,
with finite-dimensional values, then `g ∘ u ∈ W^{k+1,p}_loc(Ω ∩ {0 ≤ im})`. This is the half-disc
form of `TauCeti.MemWkpLoc.contDiffOn_comp_succ`.

Near a boundary point of a pseudoholomorphic curve with boundary on a totally real submanifold,
the curve is modelled on a half-disc, and the boundary bootstrap needs the coefficients
`J(z, u)` of the Cauchy-Riemann operator in the same local Sobolev class as `u`, up to the real
axis. That is the domain-dependent form `TauCeti.MemWkpLoc.contDiffOn_comp_graph_succ_halfPlane`,
in which `g(z, y)` need only be `C^{k+1}` for `z` in the closed upper half-plane, as the
coefficients in a boundary chart are.

## Main declarations

* `TauCeti.MemWkpLoc.contDiffOn_comp_succ_halfPlane`: composition with maps that are `C^{k+1}`
  on an open neighbourhood of the image, on half-discs.
* `TauCeti.MemWkpLoc.contDiffOn_comp_graph_succ_halfPlane`: the domain-dependent composition
  `z ↦ g(z, u z)` on half-discs, for `g` that is `C^{k+1}` on `{q | 0 ≤ q.1.im}` near the graph.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (composition in local Sobolev spaces).
-/

public noncomputable section

open Set TopologicalSpace Filter Metric
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {F G H : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

variable [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] [FiniteDimensional ℝ H]
  {Ω : Opens ℂ} {p : ℝ≥0}

/-- **Composition of continuous local Sobolev maps with `C^{k+1}` maps on half-discs.** For
`p > 2`, if `u` is continuous on `Ω ∩ {0 ≤ im}` and belongs to `W^{k+1,p}_loc(Ω ∩ {0 ≤ im})`, and
`g` is `C^{k+1}` on an open set `W` containing the image of `Ω ∩ {0 ≤ im}` under `u`, then `g ∘ u`
belongs to `W^{k+1,p}_loc(Ω ∩ {0 ≤ im})`. -/
theorem MemWkpLoc.contDiffOn_comp_succ_halfPlane (hp : 2 < p) {k : ℕ} {u : ℂ → F} {g : F → G}
    {W : Set F} (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) u)
    (huc : ContinuousOn u ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) (hW : IsOpen W)
    (hg : ContDiffOn ℝ (k + 1) g W) (huW : MapsTo u ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) W) :
    MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) (fun z => g (u z)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast one_lt_two.le.trans hp.le
  refine inter_setOf_im_nonneg_induction (MemWkpLoc p · (k + 1) fun z => g (u z))
    memWkpLoc_iff_locally.2
    ((hu.mono Ω.coe_upperHalf_subset).contDiffOn_comp_succ hp (huc.mono Ω.coe_upperHalf_subset)
      hW hg (huW.mono_left Ω.coe_upperHalf_subset))
    fun x r _ hrΩ => ?_
  -- On a half-disc centred on the axis, extend `u` by reflection to the disc, on which it is
  -- continuous, and restrict to the open part of the disc where the extension takes values in `W`.
  set v := TauCeti.planarReflection (higherReflectionCoeff (k + 1)) u
  have hv : MemWkpLoc p (ball (x : ℂ) r) (k + 1) v :=
    MemWkpLoc.planarReflection_higherReflectionCoeff_ball hp1 x r
      (hu.mono (inter_subset_inter_left _ hrΩ))
  have hvc : ContinuousOn v (ball (x : ℂ) r) :=
    continuousOn_planarReflection (sum_higherReflectionCoeff k.succ_pos)
      (fun _ hw _ j => imDilation_higherReflectionNode_mem_ball x r j hw)
      (huc.mono (inter_subset_inter_left _ hrΩ))
  let O : Opens ℂ := ⟨ball (x : ℂ) r ∩ v ⁻¹' W, hvc.isOpen_inter_preimage isOpen_ball hW⟩
  refine (MemWkpLoc.contDiffOn_comp_succ (Ω := O) hp (hv.mono inter_subset_left)
      (hvc.mono inter_subset_left) hW hg fun w hw => hw.2).congr_mono
    (fun w hw => by simp only [v, planarReflection_of_nonneg _ _ hw.2]) fun w hw => ⟨hw.1, ?_⟩
  simp only [mem_preimage, v, planarReflection_of_nonneg _ _ hw.2]
  exact huW ⟨hrΩ hw.1, hw.2⟩

/-- **Composition with domain dependence on half-discs at every order.** For `p > 2`, if `u` is
continuous on `Ω ∩ {0 ≤ im}` and belongs to `W^{k+1,p}_loc(Ω ∩ {0 ≤ im})`, and `g : ℂ × F → H` is
`C^{k+1}` on `W ∩ {q | 0 ≤ q.1.im}` for an open set `W` containing the graph of `u` over
`Ω ∩ {0 ≤ im}`, then `z ↦ g (z, u z)` belongs to `W^{k+1,p}_loc(Ω ∩ {0 ≤ im})`. The map `g` need
only be defined for `z` in the closed upper half-plane, as for the coefficients of a
Cauchy-Riemann operator in a boundary chart. -/
theorem MemWkpLoc.contDiffOn_comp_graph_succ_halfPlane (hp : 2 < p) {k : ℕ} {u : ℂ → F}
    {g : ℂ × F → H} {W : Set (ℂ × F)}
    (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) u)
    (huc : ContinuousOn u ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) (hW : IsOpen W)
    (hg : ContDiffOn ℝ (k + 1) g (W ∩ {q | 0 ≤ q.1.im}))
    (huW : ∀ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, (z, u z) ∈ W) :
    MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) (fun z => g (z, u z)) := by
  have hgrc : ContinuousOn (fun z => (z, u z)) ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :=
    continuousOn_id.prodMk huc
  refine memWkpLoc_iff_locally.2 fun z hz => ?_
  obtain ⟨T, hTo, hzT, G, hG, hGg⟩ :=
    exists_contDiffOn_eqOn_inter_setOf_fst_im_nonneg hW hg ⟨huW z hz, mem_ofPred.1 hz.2⟩
  obtain ⟨O, hO, hOeq⟩ := continuousOn_iff'.1 hgrc T hTo
  have hzO : z ∈ O := by
    have h : z ∈ (fun z => (z, u z)) ⁻¹' T ∩ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := ⟨hzT, hz⟩
    rw [hOeq] at h
    exact h.1
  let Ω' : Opens ℂ := Ω ⊓ ⟨O, hO⟩
  have hsub : (Ω' : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} :=
    inter_subset_inter_left _ inter_subset_left
  have hmaps : MapsTo (fun z => (z, u z)) ((Ω' : Set ℂ) ∩ {z | 0 ≤ z.im}) T := fun w hw => by
    have h : w ∈ O ∩ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := ⟨hw.1.2, hw.1.1, hw.2⟩
    rw [← hOeq] at h
    exact h.1
  refine ⟨(Ω' : Set ℂ) ∩ {z | 0 ≤ z.im}, ?_, ?_⟩
  · refine mem_of_superset (inter_mem_nhdsWithin _ (hO.mem_nhds hzO)) fun w hw => ?_
    exact ⟨⟨hw.1.1, hw.2⟩, hw.1.2⟩
  refine (((contDiff_id.memWkpLoc).prodMk (hu.mono hsub)).contDiffOn_comp_succ_halfPlane hp
    (hgrc.mono hsub) hTo hG hmaps).congr_mono
    (fun w hw => (hGg ⟨⟨huW w (hsub hw), hw.2⟩, hmaps hw⟩).symm) subset_rfl

end TauCeti
