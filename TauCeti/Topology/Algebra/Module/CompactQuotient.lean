/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# A subgroup with compact quotient spans a finite-dimensional real space

An additive subgroup `L` of a finite-dimensional Hausdorff real topological vector space `V`
whose quotient `V ⧸ L` is compact spans `V` over `ℝ`. Otherwise a nonzero linear functional
vanishes on the span of `L`; it is continuous because `V` is finite-dimensional, so it descends to
a continuous surjection `V ⧸ L → ℝ`, whose range would be compact, and `ℝ` is not.

This is the half of the characterisation of lattices that produces the spanning condition of
`IsZLattice` from compactness of the quotient; the other half, that a discrete subgroup is
closed and that a lattice has compact quotient, is Mathlib's.

## Main results

* `AddSubgroup.span_eq_top_of_compactSpace_quotient`: an additive subgroup with compact quotient
  spans the space.

## References

* N. Bourbaki, *General Topology*, Chapters 5–10, Springer (1989), Chapter VII (The additive
  groups `ℝⁿ`), § 1 (Subgroups and quotient groups of `ℝⁿ`).
-/

public section

namespace AddSubgroup

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V]

/-- **An additive subgroup of a finite-dimensional real space with compact quotient spans the
space.** -/
theorem span_eq_top_of_compactSpace_quotient (L : AddSubgroup V) [CompactSpace (V ⧸ L)] :
    Submodule.span ℝ (L : Set V) = ⊤ := by
  -- A functional vanishing on the span descends to the compact quotient, so its range in `ℝ`
  -- is compact; a nonzero functional is surjective, and `ℝ` is not compact.
  by_contra hne
  obtain ⟨f, hf0, hfker⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
  have hker : L ≤ f.toAddMonoidHom.ker := fun X hX => by
    have hmem : f X ∈ (Submodule.span ℝ (L : Set V)).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span hX)
    rwa [hfker, Submodule.mem_bot] at hmem
  let φ := QuotientAddGroup.lift L f.toAddMonoidHom hker
  have hφ : Continuous φ :=
    (QuotientAddGroup.isQuotientMap_mk L).continuous_iff.mpr
      (LinearMap.continuous_of_finiteDimensional f)
  have hsurj : Function.Surjective φ := fun r => by
    obtain ⟨X, hX⟩ := LinearMap.surjective hf0 r
    exact ⟨QuotientAddGroup.mk X, by rw [QuotientAddGroup.lift_mk]; exact hX⟩
  exact noncompact_univ ℝ (Set.range_eq_univ.mpr hsurj ▸ isCompact_range hφ)

end AddSubgroup
