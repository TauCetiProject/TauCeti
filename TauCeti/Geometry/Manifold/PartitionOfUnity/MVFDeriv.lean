/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The differential of a partition-of-unity sum at a common zero

Let `φ` be a smooth partition of unity on a set `s`, subordinate to sets `U i`, and let `ρ i` be
real functions which vanish at a point `q ∈ s` whenever `q ∈ U i`. Near `q` the sum
`∑ᶠ i, φ i • ρ i` is the finite sum over the indices `i` with `q` in the topological support of
`φ i`, and since every such `ρ i` vanishes at `q`, its differential at `q` is
`∑ φ i q • dρ_i`. So if every `dρ_i` with `q ∈ U i` is positive on a tangent vector `v`, so is the
differential of the sum (`SmoothPartitionOfUnity.mvfderiv_finsum_smul_pos`). This is how local
defining functions of a hypersurface glue to a global one.

## Main results

* `SmoothPartitionOfUnity.mvfderiv_finsum_smul_pos`: positivity of the glued differential.
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff

namespace SmoothPartitionOfUnity

variable {ι E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- **The glued differential at a common zero.** Let `φ` be a smooth partition of unity on a set
`s` subordinate to `U`, let `q ∈ s`, and let `ρ i` be differentiable at `q` and vanish there
whenever `q ∈ U i`. If `dρ_i (v) > 0` for every such `i`, then the differential of
`∑ᶠ i, φ i • ρ i` at `q` is positive on `v`. -/
theorem mvfderiv_finsum_smul_pos {s : Set M} {φ : SmoothPartitionOfUnity ι I M s}
    {U : ι → Set M} (hφ : φ.IsSubordinate U) {q : M} (hq : q ∈ s) {ρ : ι → M → ℝ}
    {v : TangentSpace I q}
    (hd : ∀ i, q ∈ U i → MDifferentiableAt I 𝓘(ℝ) (ρ i) q) (h0 : ∀ i, q ∈ U i → ρ i q = 0)
    (hpos : ∀ i, q ∈ U i → 0 < mvfderiv I (ρ i) q v) :
    0 < mvfderiv I (fun x ↦ ∑ᶠ i, φ i x • ρ i x) q v := by
  have hU {i : ι} (hi : i ∈ φ.fintsupport q) : q ∈ U i :=
    hφ i ((φ.mem_fintsupport_iff q i).mp hi)
  -- Near `q` the sum runs over the finite set of `i` with `q` in the topological support of `φ i`.
  have heq : (fun x ↦ ∑ᶠ i, φ i x • ρ i x) =ᶠ[𝓝 q]
      fun x ↦ ∑ i ∈ φ.fintsupport q, φ i x • ρ i x := by
    filter_upwards [φ.eventually_fintsupport_subset q] with y hy
    refine finsum_eq_sum_of_support_subset _ fun i hi ↦ hy ?_
    exact (φ.mem_fintsupport_iff y i).mpr (subset_tsupport _ (left_ne_zero_of_smul hi))
  have hdφ (i : ι) : MDifferentiableAt I 𝓘(ℝ) (φ i) q :=
    (φ i).contMDiff.mdifferentiableAt (by simp)
  have hterm (i : ι) (hi : i ∈ φ.fintsupport q) :
      mvfderiv I (fun x ↦ φ i x • ρ i x) q v = φ i q * mvfderiv I (ρ i) q v := by
    rw [mvfderiv_fun_smul (hdφ i) (hd i (hU hi)), h0 i (hU hi)]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul, mul_zero,
      add_zero]
  rw [heq.mvfderiv_eq, TauCeti.mvfderiv_fun_sum (f := fun i x ↦ φ i x • ρ i x) fun i hi ↦
      (hdφ i).smul (hd i (hU hi)), sum_apply, Finset.sum_congr rfl hterm]
  obtain ⟨j, hj⟩ := φ.exists_pos_of_mem hq
  have hjF : j ∈ φ.fintsupport q := (φ.mem_fintsupport_iff q j).mpr (subset_tsupport _ hj.ne')
  exact Finset.sum_pos' (fun i hi ↦ mul_nonneg (φ.nonneg i q) (hpos i (hU hi)).le)
    ⟨j, hjF, mul_pos hj (hpos j (hU hjF))⟩

end SmoothPartitionOfUnity
