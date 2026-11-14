/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# A subgroup with compact quotient spans a finite-dimensional space

Let `𝕜` be a complete nontrivially normed field (such as `ℝ`, `ℂ` or `ℚ_[p]`). An additive
subgroup `L` of a finite-dimensional Hausdorff topological vector space `V` over `𝕜` whose quotient
`V ⧸ L` is compact spans `V` over `𝕜`. Otherwise a nonzero linear functional vanishes on the span
of `L`; it is continuous because `V` is finite-dimensional, so it descends to a continuous
surjection `V ⧸ L → 𝕜`, whose range would be compact, and `𝕜` is not.

Over `ℝ`, this is the half of the characterisation of lattices that produces the spanning
condition of `IsZLattice` from compactness of the quotient; the other half, that a discrete
subgroup is closed and that a lattice has compact quotient, is Mathlib's.

## Main results

* `AddSubgroup.span_eq_top_of_compactSpace_quotient`: an additive subgroup with compact quotient
  spans the space.

## References

* N. Bourbaki, *General Topology*, Chapters 5–10, Springer (1989), Chapter VII (The additive
  groups `ℝⁿ`), § 1 (Subgroups and quotient groups of `ℝⁿ`).
-/

public section

namespace AddSubgroup

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup V]
  [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V] [T2Space V]
  [FiniteDimensional 𝕜 V]

/-- **An additive subgroup of a finite-dimensional Hausdorff vector space over a complete
nontrivially normed field with compact quotient spans the space.** -/
theorem span_eq_top_of_compactSpace_quotient (L : AddSubgroup V) [CompactSpace (V ⧸ L)] :
    Submodule.span 𝕜 (L : Set V) = ⊤ := by
  -- A functional vanishing on the span descends to the compact quotient, so its range in `𝕜`
  -- is compact; a nonzero functional is surjective, and `𝕜` is not compact.
  by_contra hne
  obtain ⟨f, hf0, hfker⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (Ne.lt_top hne) inferInstance
  have hker : L ≤ f.toAddMonoidHom.ker := fun x hx =>
    AddMonoidHom.mem_ker.mpr <| LinearMap.mem_ker.mp <|
      LinearMap.le_ker_iff_map.mpr hfker (Submodule.subset_span hx)
  let φ := QuotientAddGroup.lift L f.toAddMonoidHom hker
  have hφ : Continuous φ :=
    (QuotientAddGroup.isQuotientMap_mk L).continuous_iff.mpr
      (LinearMap.continuous_of_finiteDimensional f)
  have hsurj : Function.Surjective φ := fun r => by
    obtain ⟨X, hX⟩ := LinearMap.surjective hf0 r
    exact ⟨QuotientAddGroup.mk X, by rw [QuotientAddGroup.lift_mk]; exact hX⟩
  exact noncompact_univ 𝕜 (Set.range_eq_univ.mpr hsurj ▸ isCompact_range hφ)

end AddSubgroup
