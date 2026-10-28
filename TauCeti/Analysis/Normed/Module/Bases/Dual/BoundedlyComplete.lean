/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Bases.Dual.Basic

/-!
# Shrinking bases and bounded completeness of the dual basic sequence

A Schauder basis is shrinking if and only if its coordinate functionals, regarded as a
basis of their closed linear span, are boundedly complete. This connects density of the
coordinate functionals in the continuous dual with convergence of their bounded partial sums.
All series converge along initial segments.

The implication from bounded completeness works over any nontrivially normed field.
The converse uses weak-star compactness of dual balls and assumes a proper scalar field;
in particular it applies over both the real and complex numbers.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 3, duality of bases.
-/

public section

noncomputable section

open Filter Set Topology

namespace SchauderBasis

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (b : SchauderBasis 𝕜 E)

/-- Bounded completeness of the dual basic sequence forces the original basis to be shrinking. -/
theorem isShrinking_of_isBoundedlyComplete_dualBasis
    (hb : b.dualBasis.IsBoundedlyComplete) : b.IsShrinking := by
  rw [b.isShrinking_iff, Submodule.eq_top_iff']
  intro f
  have hbound : BddAbove (range fun n ↦
      ‖∑ i ∈ Finset.range n, f (b i) • b.dualBasis i‖) := by
    refine ⟨‖f‖ * b.nnnormProjBound, ?_⟩
    rintro _ ⟨n, rfl⟩
    dsimp only
    rw [← Submodule.norm_coe]
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower,
      b.coe_dualBasis_apply, ← b.comp_proj_eq_sum]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (b.norm_proj_le_nnnormProjBound n) (norm_nonneg f))
  obtain ⟨g, hg⟩ := b.dualBasis.isBoundedlyComplete_iff.mp hb _ hbound
  have hgf : (g : StrongDual 𝕜 E) = f := by
    have heval (i : ℕ) : (g : StrongDual 𝕜 E) (b i) = f (b i) := by
      simpa only [b.dualBasis_coord_apply] using hg i
    have hproj (n : ℕ) : (g : StrongDual 𝕜 E).comp (b.proj n) = f.comp (b.proj n) := by
      simp only [b.comp_proj_eq_sum, heval]
    ext x
    exact tendsto_nhds_unique
      ((g : StrongDual 𝕜 E).continuous.tendsto x |>.comp (b.tendsto_proj x))
      (((f.continuous.tendsto x).comp (b.tendsto_proj x)).congr
        fun n ↦ DFunLike.congr_fun (hproj n).symm x)
  exact hgf ▸ g.property

/-- For a shrinking basis, its basis of the whole continuous dual is boundedly complete. -/
theorem IsShrinking.isBoundedlyComplete_dualBasis [ProperSpace 𝕜]
    {b : SchauderBasis 𝕜 E} (hb : b.IsShrinking) :
    hb.dualBasis.IsBoundedlyComplete := by
  rw [hb.dualBasis.isBoundedlyComplete_iff]
  intro a ⟨C, hC⟩
  let s (n : ℕ) := ∑ i ∈ Finset.range n, a i • hb.dualBasis i
  have hbound (n : ℕ) : ‖s n‖ ≤ C := hC (mem_range_self n)
  obtain ⟨f, _, hf⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual 𝕜 E) C).exists_mapClusterPt
    (u := fun n ↦ StrongDual.toWeakDual (s n)) (f := atTop)
    (by
      rw [Filter.map_le_iff_le_comap, Filter.comap_principal, Filter.le_principal_iff]
      exact Eventually.of_forall fun n ↦ by
        simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
          StrongDual.toStrongDual_toWeakDual] using hbound n)
  refine ⟨WeakDual.toStrongDual f, fun i ↦ ?_⟩
  have hc := hf.continuousAt_comp (WeakDual.eval_continuous (b i)).continuousAt
  have ht : Tendsto (fun n ↦ s n (b i)) atTop (𝓝 (a i)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop i] with n hn
    symm
    simpa only [IsShrinking.dualBasis_coord_apply] using
      hb.dualBasis.coord_sum_range a hn
  simpa only [IsShrinking.dualBasis_coord_apply, WeakDual.toStrongDual_apply] using
    eq_of_nhds_neBot (hc.clusterPt.mono ht)

/-- A Schauder basis is shrinking exactly when its dual basic sequence is boundedly complete. -/
theorem isShrinking_iff_isBoundedlyComplete_dualBasis [ProperSpace 𝕜] :
    b.IsShrinking ↔ b.dualBasis.IsBoundedlyComplete := by
  refine ⟨fun hb ↦ ?_, b.isShrinking_of_isBoundedlyComplete_dualBasis⟩
  rw [b.dualBasis.isBoundedlyComplete_iff]
  intro a ha
  have hbound : BddAbove (range fun n ↦
      ‖∑ i ∈ Finset.range n, a i • hb.dualBasis i‖) := by
    simpa only [← Submodule.norm_coe, Submodule.coe_sum, Submodule.coe_smul_of_tower,
      b.coe_dualBasis_apply, IsShrinking.dualBasis_apply] using ha
  obtain ⟨f, hf⟩ := hb.dualBasis.isBoundedlyComplete_iff.mp
    hb.isBoundedlyComplete_dualBasis a hbound
  have hmem : f ∈ (Submodule.span 𝕜 (range b.coord)).topologicalClosure := by
    rw [b.isShrinking_iff.mp hb]
    trivial
  refine ⟨⟨f, hmem⟩, fun i ↦ ?_⟩
  simpa only [b.dualBasis_coord_apply, IsShrinking.dualBasis_coord_apply] using hf i

end SchauderBasis
