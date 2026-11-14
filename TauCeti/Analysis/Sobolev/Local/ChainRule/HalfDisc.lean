/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.ChainRule.Higher
public import TauCeti.Analysis.Sobolev.Local.Reflection
import Mathlib.Analysis.Complex.ReImTopology
import TauCeti.Analysis.Complex.ReImTopology
import TauCeti.Analysis.Sobolev.Local.Locality

/-!
# Composition of local Sobolev maps on half-discs at every order

Let `p > 2` and `k ≥ 0`. If `u` is continuous on the relatively open set `Ω ∩ {0 ≤ im}` of the
closed upper half-plane and belongs to `W^{k+1,p}_loc(Ω ∩ {0 ≤ im})` with finite-dimensional
values, and `g` is `C^{k+1}` on an open set `W` containing the image of `Ω ∩ {0 ≤ im}` under `u`,
with finite-dimensional values, then `g ∘ u ∈ W^{k+1,p}_loc(Ω ∩ {0 ≤ im})`, with bounds up to the
real axis. This is the half-disc form of `TauCeti.MemWkpLoc.contDiffOn_comp_succ`.

Near a boundary point of a pseudoholomorphic curve with boundary on a totally real submanifold,
the curve is modelled on a half-disc, and the boundary bootstrap needs the coefficients
`J(z, u)` of the Cauchy-Riemann operator in the same local Sobolev class as `u`, up to the real
axis. That is the domain-dependent form `TauCeti.MemWkpLoc.contDiffOn_comp_graph_succ_halfPlane`.

## Main declarations

* `TauCeti.continuousOn_planarReflection`: the reflection `TauCeti.planarReflection d u` with
  weights of sum one is continuous across the real axis when `u` is continuous up to it.
* `TauCeti.MemWkpLoc.contDiffOn_comp_succ_halfPlane`: composition with maps that are `C^{k+1}`
  on an open neighbourhood of the image, on half-discs.
* `TauCeti.MemWkpLoc.contDiffOn_comp_graph_succ_halfPlane`: the domain-dependent composition
  `z ↦ g(z, u z)` on half-discs.

## Implementation notes

Near a point `x` of the real axis, `u` is extended to a disc about `x` by the higher-order
reflection `TauCeti.MemWkpLoc.planarReflection_higherReflectionCoeff_ball`. The reflection is
continuous (`TauCeti.continuousOn_planarReflection`) and takes the value `u x ∈ W` at `x`, so on a
smaller disc it takes values in `W`. There the interior theorem applies, and the result is
restricted back to the half-disc, where the reflection agrees with `u`. Near a point off the axis
the interior theorem applies directly. `TauCeti.memWkpLoc_iff_locally` glues the two cases.

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

/-- **Continuity of the reflection.** If the node dilations map the lower part of `Ω` into `Ω` and
the weights sum to one, the reflection of a map continuous on `Ω ∩ {0 ≤ im}` is continuous on
`Ω`: on the real axis every reflected copy takes the value of the map itself. -/
theorem continuousOn_planarReflection {k : ℕ} {d : Fin k → ℝ} (hd : ∑ j, d j = 1) {Ω : Set ℂ}
    (hΩ : ∀ z ∈ Ω, z.im < 0 → ∀ j : Fin k, imDilation (higherReflectionNode j) z ∈ Ω)
    {u : ℂ → F} (hu : ContinuousOn u (Ω ∩ {z | 0 ≤ z.im})) :
    ContinuousOn (planarReflection d u) Ω := by
  have hmaps (j : Fin k) :
      MapsTo (imDilation (higherReflectionNode j)) (Ω ∩ {z | z.im ≤ 0}) (Ω ∩ {z | 0 ≤ z.im}) := by
    rintro z ⟨hzΩ, hz : z.im ≤ 0⟩
    refine ⟨?_, ?_⟩
    · rcases hz.lt_or_eq with hz | hz
      · exact hΩ z hzΩ hz j
      · rwa [imDilation_of_im_eq_zero _ hz]
    · simpa [imDilation_apply_im] using
        mul_nonneg_of_nonpos_of_nonpos (higherReflectionNode_neg j).le hz
  have heq : planarReflection d u = fun z => if 0 ≤ z.im then u z else
      ∑ j, d j • u (imDilation (higherReflectionNode j) z) := by
    funext z
    split_ifs with hz
    · exact planarReflection_of_nonneg _ _ hz
    · exact planarReflection_of_neg _ _ (not_le.1 hz)
  rw [heq]
  refine ContinuousOn.if (fun z hz => ?_) ?_ ?_
  · rw [Complex.frontier_setOfPred_le_im] at hz
    simp only [imDilation_of_im_eq_zero _ hz.2, ← Finset.sum_smul, hd, one_smul]
  · rwa [(isClosed_le continuous_const Complex.continuous_im).closure_eq]
  · simp_rw [not_le, Complex.closure_setOfPred_im_lt]
    exact continuousOn_finsetSum _ fun j _ =>
      (hu.comp (imDilation (higherReflectionNode j)).continuous.continuousOn (hmaps j)).const_smul _

variable [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] [FiniteDimensional ℝ H]
  {Ω : Opens ℂ} {p : ℝ≥0}

/-- **Composition of continuous local Sobolev maps with `C^{k+1}` maps on half-discs.** For
`p > 2`, if `u` is continuous on `Ω ∩ {0 ≤ im}` and belongs to `W^{k+1,p}_loc(Ω ∩ {0 ≤ im})`, and
`g` is `C^{k+1}` on an open set `W` containing the image of `Ω ∩ {0 ≤ im}` under `u`, then `g ∘ u`
belongs to `W^{k+1,p}_loc(Ω ∩ {0 ≤ im})`, with bounds up to the real axis. -/
theorem MemWkpLoc.contDiffOn_comp_succ_halfPlane (hp : 2 < p) {k : ℕ} {u : ℂ → F} {g : F → G}
    {W : Set F} (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) u)
    (huc : ContinuousOn u ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) (hW : IsOpen W)
    (hg : ContDiffOn ℝ (k + 1) g W) (huW : MapsTo u ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) W) :
    MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) (fun z => g (u z)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast one_lt_two.le.trans hp.le
  refine memWkpLoc_iff_locally.2 fun z hz => ?_
  rcases (show 0 ≤ z.im from hz.2).lt_or_eq with hz0 | hz0
  · -- Off the axis, the interior theorem applies on the upper half of `Ω`.
    refine ⟨Ω.upperHalf, mem_nhdsWithin_of_mem_nhds (Ω.upperHalf.isOpen.mem_nhds
      (Opens.mem_upperHalf.2 ⟨hz.1, hz0⟩)), ?_⟩
    exact (hu.mono Ω.coe_upperHalf_subset).contDiffOn_comp_succ hp
      (huc.mono Ω.coe_upperHalf_subset) hW hg (huW.mono_left Ω.coe_upperHalf_subset)
  · -- On the axis, extend `u` by reflection to a disc about `x = z.re`, on which it is
    -- continuous, and shrink the disc so that the extension takes values in `W`.
    set x := z.re
    have hzx : ((x : ℝ) : ℂ) = z := Complex.ext (by simp [x]) (by simp [hz0])
    obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen _ hz.1
    rw [← hzx] at hrΩ
    set v := TauCeti.planarReflection (higherReflectionCoeff (k + 1)) u
    have hv : MemWkpLoc p (ball (x : ℂ) r) (k + 1) v :=
      MemWkpLoc.planarReflection_higherReflectionCoeff_ball hp1 x r
        (hu.mono (inter_subset_inter_left _ hrΩ))
    have hvc : ContinuousOn v (ball (x : ℂ) r) :=
      continuousOn_planarReflection (sum_higherReflectionCoeff k.succ_pos)
        (fun _ hw _ j => imDilation_higherReflectionNode_mem_ball x r j hw)
        (huc.mono (inter_subset_inter_left _ hrΩ))
    have hvx : v x ∈ W := by
      simp only [v]
      rw [planarReflection_of_nonneg _ _ (by simp)]
      exact huW ⟨hrΩ (mem_ball_self hr), by simp⟩
    obtain ⟨ε, hε, hεr⟩ := Metric.mem_nhds_iff.1 (inter_mem (ball_mem_nhds _ hr)
      ((hvc.continuousAt (ball_mem_nhds _ hr)).preimage_mem_nhds (hW.mem_nhds hvx)))
    refine ⟨ball (x : ℂ) ε ∩ {w | 0 ≤ w.im}, ?_, ?_⟩
    · rw [← hzx]
      exact mem_nhdsWithin.2 ⟨ball (x : ℂ) ε, isOpen_ball, mem_ball_self hε,
        fun w hw => ⟨hw.1, hw.2.2⟩⟩
    exact (MemWkpLoc.contDiffOn_comp_succ (Ω := ⟨_, isOpen_ball⟩) hp
        (hv.mono fun w hw => (hεr hw).1) (hvc.mono fun w hw => (hεr hw).1) hW hg
        (fun w hw => (hεr hw).2)).congr_mono
      (fun w hw => by simp only [v, planarReflection_of_nonneg _ _ hw.2]) inter_subset_left

/-- **Composition with domain dependence on half-discs at every order.** For `p > 2`, if `u` is
continuous on `Ω ∩ {0 ≤ im}` and belongs to `W^{k+1,p}_loc(Ω ∩ {0 ≤ im})`, and `g : ℂ × F → H` is
`C^{k+1}` on an open set containing the graph of `u` over `Ω ∩ {0 ≤ im}`, then `z ↦ g (z, u z)`
belongs to `W^{k+1,p}_loc(Ω ∩ {0 ≤ im})`, with bounds up to the real axis. -/
theorem MemWkpLoc.contDiffOn_comp_graph_succ_halfPlane (hp : 2 < p) {k : ℕ} {u : ℂ → F}
    {g : ℂ × F → H} {W : Set (ℂ × F)}
    (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) u)
    (huc : ContinuousOn u ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) (hW : IsOpen W)
    (hg : ContDiffOn ℝ (k + 1) g W) (huW : ∀ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, (z, u z) ∈ W) :
    MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) (fun z => g (z, u z)) :=
  ((contDiff_id.memWkpLoc).prodMk hu).contDiffOn_comp_succ_halfPlane hp
    (continuousOn_id.prodMk huc) hW hg huW

end TauCeti
