/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.QuotientProd
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Connectivity

/-!
# Aspherical quotients of a product with a closed manifold

For a contractible topological group `A`, a compact simply connected manifold `K` with a topological
group structure, and a discrete subgroup `Γ` of `A × K`, the quotient `(A × K) ⧸ Γ` has the higher
homotopy groups of `K` (`Subgroup.isAspherical_quotient_iff`). A compact manifold that is simply
connected and aspherical is a point (`TauCeti.IsAspherical.subsingleton_of_simplyConnectedSpace`),
so the quotient is aspherical exactly when it is path connected and `K` is a single point
(`Subgroup.isAspherical_quotient_iff_subsingleton`). A compact connected Lie group `G` is such a
quotient `(ℝʳ × K) ⧸ Γ`, with `K` compact, simply connected and semisimple, so `G` is a `K(π, 1)`
exactly when `K` is trivial. This uses only that `K` is a compact simply connected manifold, not
its Lie structure.

## Main results

* `Subgroup.isAspherical_quotient_iff_subsingleton`: for `A` contractible and `K` a compact
  simply connected manifold, `(A × K) ⧸ Γ` is aspherical exactly when it is path connected and `K`
  is a point.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4 (Example 6.30 and
  Proposition 6.31).
-/

public section

open TauCeti

namespace Subgroup

variable {A : Type*} {K : Type} [Group A] [Group K] [TopologicalSpace A] [TopologicalSpace K]
  [IsTopologicalGroup A] [IsTopologicalGroup K] (Γ : Subgroup (A × K))

/-- **A quotient of `A × K` with `A` contractible and `K` a closed simply connected manifold is
aspherical exactly when `K` is a point.** For a discrete subgroup `Γ` of `A × K`, where `K` is a
compact simply connected topological manifold with a topological group structure, the quotient
`(A × K) ⧸ Γ` is aspherical exactly when it is path connected and `K` is trivial. Applied to a
compact connected Lie group `(ℝʳ × K) ⧸ Γ`, this says it is a `K(π, 1)` exactly when `K` is
trivial. -/
theorem isAspherical_quotient_iff_subsingleton {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E K] [ContractibleSpace A] [DiscreteTopology Γ]
    [T2Space K] [CompactSpace K] [SimplyConnectedSpace K] (x : (A × K) ⧸ Γ) :
    IsAspherical ((A × K) ⧸ Γ) x ↔ PathConnectedSpace ((A × K) ⧸ Γ) ∧ Subsingleton K := by
  rw [Γ.isAspherical_quotient_iff]
  exact and_congr_right fun _ ↦ ⟨fun h ↦ IsAspherical.subsingleton_of_simplyConnectedSpace (E := E)
    (IsAspherical.mk (x := (1 : K)) inferInstance h), fun _ _ ↦ inferInstance⟩

end Subgroup
