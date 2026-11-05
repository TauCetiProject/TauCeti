/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Strong convergence after a compact operator

A uniformly norm-bounded family of operators converging strongly to zero converges in
operator norm after precomposition with a compact operator. This is the compact-set
uniformity principle used to control compact remainders in finite-section methods.
-/

public section

open Filter Metric Set Topology

namespace ContinuousLinearMap

variable {𝕜 E F G ι : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Uniformly bounded, strongly null operators converge in norm after precomposition
with a compact operator. No completeness assumption is needed. -/
theorem tendsto_comp_zero_of_isCompactOperator {l : Filter ι} {A : ι → F →L[𝕜] G} {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    (hlim : ∀ x, Tendsto (fun i ↦ A i x) l (𝓝 0))
    (K : E →L[𝕜] F) (hK : IsCompactOperator K) :
    Tendsto (fun i ↦ A i ∘L K) l (𝓝 0) := by
  obtain ⟨s, hs, hKs⟩ := hK.image_closedBall_subset_compact (f := K.toLinearMap) 1
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs
  have hequi : Equicontinuous (fun i (x : s) ↦ A i x) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ ⟨C, hC⟩
    intro i
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact ((A i).lipschitzWith.dist_le_mul (x : F) (y : F)).trans
      (mul_le_mul_of_nonneg_right (hA i) dist_nonneg)
  have hu := (hequi.tendsto_uniformFun_iff_pi l (fun _ ↦ (0 : G))).mpr
    (tendsto_pi_nhds.mpr fun x ↦ hlim x)
  have hunif : TendstoUniformly (fun i (x : s) ↦ A i x) (fun _ ↦ (0 : G)) l :=
    UniformFun.tendsto_iff_tendstoUniformly.mp hu
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  have hcpos : 0 < ‖c‖ := lt_trans zero_lt_one hc
  have he := Metric.tendstoUniformly_iff.mp hunif (ε / 2 / ‖c‖)
    (div_pos (half_pos hε) hcpos)
  filter_upwards [he] with i hi
  rw [dist_zero_right, norm_norm]
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  apply opNorm_le_of_shell one_pos (le_of_lt (half_pos hε)) hc
  intro x hcx hx
  have hmem : K x ∈ s := hKs (mem_image_of_mem K (by
    simpa only [mem_closedBall, dist_zero_right] using hx.le))
  calc
    ‖(A i ∘L K) x‖ ≤ ε / 2 / ‖c‖ :=
      le_of_lt (by simpa using hi (⟨K x, hmem⟩ : s))
    _ = (ε / 2) * (1 / ‖c‖) := by ring
    _ ≤ (ε / 2) * ‖x‖ := mul_le_mul_of_nonneg_left hcx (le_of_lt (half_pos hε))

end ContinuousLinearMap
