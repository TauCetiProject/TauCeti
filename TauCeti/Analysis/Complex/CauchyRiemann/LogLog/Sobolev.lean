/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.LogLog.Example
public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import TauCeti.Analysis.Sobolev.Local.Morrey

/-!
# The `log log` example in Sobolev terms

Elliptic bootstrapping for pseudoholomorphic curves turns a `W^{1,p}_loc` solution of the weak
Cauchy-Riemann equation for a `C¹` structure into a `W^{2,p}_loc` one, but only for finite
`p > 2`. The function `f(z) = z² log log (1 / ‖z‖)` (`TauCeti.logLogExample`) shows that the
endpoint `p = ∞` fails. This file states the example in the local Sobolev classes `MemWkpLoc`
and for the weak equation `IsWeakCauchyRiemannOn`, in which the bootstrapping theorem is phrased.

## Main results

* `TauCeti.memWkpLoc_one_logLogExample`, `TauCeti.memWkpLoc_one_graph_logLogExample`: `f` and
  its graph `z ↦ (z, f z)` are `W^{1,p}_loc` on the unit disc for every `p`, including `p = ∞`.
* `TauCeti.isWeakCauchyRiemannOn_graph_logLogExample`: the graph is a weak solution, for every
  exponent, of the homogeneous equation for the `C¹` graph structure
  `TauCeti.conjWirtingerGraphStructure f`.
* `TauCeti.not_memWkpLoc_two_top_logLogExample`,
  `TauCeti.not_memWkpLoc_two_top_graph_logLogExample`: neither `f` nor its graph is
  `W^{2,∞}_loc` on any neighbourhood of the origin.

## Implementation notes

The failure of `W^{2,∞}_loc` follows from the unboundedness of the classical second derivative of
`f` near the origin through the general criterion
`TauCeti.not_memWkpLoc_two_top_of_not_isBoundedUnder`, a consequence of the Morrey embedding.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B.4
  (elliptic bootstrapping).
-/

public section

open Complex Filter Metric Set MeasureTheory TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal Topology

namespace TauCeti

/-- The graph `z ↦ (z, f z)` of the example is `C¹` on the unit disc. -/
private theorem contDiffOn_graph_logLogExample :
    ContDiffOn ℝ 1 (fun z ↦ WithLp.toLp 2 (z, logLogExample z)) (ball 0 1) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm.contDiff.comp_contDiffOn
    (contDiffOn_id.prodMk contDiffOn_logLogExample)

/-- **The example is `W^{1,p}_loc` on the unit disc** for every exponent, including `p = ∞`. -/
theorem memWkpLoc_one_logLogExample (p : ℝ≥0∞) :
    MemWkpLoc p (ball 0 1) 1 logLogExample :=
  ContDiffOn.memWkpLoc (Ω := ⟨ball 0 1, isOpen_ball⟩) (by exact_mod_cast contDiffOn_logLogExample)
    subset_rfl

/-- **The graph of the example is `W^{1,p}_loc` on the unit disc** for every exponent, including
`p = ∞`. -/
theorem memWkpLoc_one_graph_logLogExample (p : ℝ≥0∞) :
    MemWkpLoc p (ball 0 1) 1 (fun z ↦ WithLp.toLp 2 (z, logLogExample z)) :=
  ContDiffOn.memWkpLoc (Ω := ⟨ball 0 1, isOpen_ball⟩)
    (by exact_mod_cast contDiffOn_graph_logLogExample) subset_rfl

/-- **The graph of the example is a weak pseudoholomorphic curve.** For every exponent, including
`p = ∞`, the graph `z ↦ (z, f z)` solves the weak homogeneous Cauchy-Riemann equation on the unit
disc for the graph structure `J_f`, which is `C¹` there
(`TauCeti.contDiffOn_conjWirtingerGraphStructure_logLogExample`). -/
theorem isWeakCauchyRiemannOn_graph_logLogExample (p : ℝ≥0∞) :
    IsWeakCauchyRiemannOn p (ball 0 1) (fun _ ↦ conjWirtingerGraphStructure logLogExample)
      (fun _ _ ↦ 0) (fun z ↦ WithLp.toLp 2 (z, logLogExample z)) :=
  isWeakCauchyRiemannOn_graph_conjWirtingerGraphStructure (Ω := ⟨ball 0 1, isOpen_ball⟩) p
    contDiffOn_logLogExample

/-- **The example is not `W^{2,∞}_loc` on any neighbourhood of the origin.** -/
theorem not_memWkpLoc_two_top_logLogExample {U : Set ℂ} (hU : U ∈ 𝓝 0) :
    ¬ MemWkpLoc ∞ U 2 logLogExample := fun h ↦
  not_memWkpLoc_two_top_of_not_isBoundedUnder
    (Ω := ⟨interior U ∩ ball 0 1, isOpen_interior.inter isOpen_ball⟩)
    (contDiffOn_logLogExample.mono inter_subset_right)
    ⟨mem_interior_iff_mem_nhds.2 hU, mem_ball_self one_pos⟩
    not_isBoundedUnder_norm_fderiv_fderiv_logLogExample
    (h.mono (inter_subset_left.trans interior_subset))

/-- **The graph of the example is not `W^{2,∞}_loc` on any neighbourhood of the origin.**
Together with `TauCeti.isWeakCauchyRiemannOn_graph_logLogExample`, it is a `W^{1,∞}_loc` weak
solution for a `C¹` structure that is not `W^{2,∞}_loc`, so elliptic bootstrapping fails at
`p = ∞`. -/
theorem not_memWkpLoc_two_top_graph_logLogExample {U : Set ℂ} (hU : U ∈ 𝓝 0) :
    ¬ MemWkpLoc ∞ U 2 (fun z ↦ WithLp.toLp 2 (z, logLogExample z)) := fun h ↦
  not_memWkpLoc_two_top_logLogExample hU
    (h.clm_comp ((ContinuousLinearMap.snd ℝ ℂ ℂ).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ : WithLp 2 (ℂ × ℂ) →L[ℝ] ℂ × ℂ)))

end TauCeti
