/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.Finite
public import TauCeti.Topology.VectorBundle.FiniteRank.HomotopyInvariance.Basic

/-!
# Relative cylinder extension over finite CW complexes for finite-rank bundle cores

This module specializes `TauCeti.FiniteRankBundleCore.exists_iso_cylinder_of_isClosed` to
subcomplexes of finite CW complexes and finite relative CW complexes with compact base.

## Main results

* `TauCeti.FiniteRankBundleCore.exists_iso_cylinder_of_relSubcomplex`: relative cylinder extension
  from a subcomplex of a finite relative CW structure over a compact base.
* `TauCeti.FiniteRankBundleCore.exists_iso_cylinder_of_subcomplex`: relative cylinder extension from
  a subcomplex of a finite CW structure on an R₁ space.
-/

public section

open CategoryTheory Set
open scoped ContinuousMap unitInterval

namespace TauCeti.FiniteRankBundleCore

universe u v

variable {𝕜 : Type v} [RCLike 𝕜]
  {X : Type u} [TopologicalSpace X]

/-- Relative cylinder extension from a subcomplex `E` of a finite relative CW structure on `X` over
a compact base `D`. -/
theorem exists_iso_cylinder_of_relSubcomplex [R1Space X] {D : Set X}
    [Topology.RelCWComplex (univ : Set X) D] [Topology.RelCWComplex.Finite (univ : Set X)]
    (hD : IsCompact D) (E : Topology.RelCWComplex.Subcomplex (univ : Set X))
    (A : FiniteRankBundleCore 𝕜 (X × I))
    (e₀ : ((A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst).pullback
        (cylinderSetIncl (E : Set X)) ≅ A.pullback (cylinderSetIncl (E : Set X)))
    (he₀ : ∀ x : (E : Set X),
      e₀.hom.fiberMap (x, 0) = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) :
    ∃ e : (A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst ≅ A,
      (∀ x : X, e.hom.fiberMap (x, 0) = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) ∧
      (pullbackFunctor (cylinderSetIncl (E : Set X))).mapIso e = e₀ := by
  have : CompactSpace X := ⟨Topology.RelCWComplex.isCompact_of_finite hD⟩
  exact exists_iso_cylinder_of_isClosed E.closed A e₀ he₀

/-- Relative cylinder extension from a subcomplex `E` of a finite CW structure on an R₁ space `X`
(for instance any Hausdorff finite CW complex). -/
theorem exists_iso_cylinder_of_subcomplex [R1Space X]
    [Topology.CWComplex (univ : Set X)] [Topology.RelCWComplex.Finite (univ : Set X)]
    (E : Topology.CWComplex.Subcomplex (univ : Set X))
    (A : FiniteRankBundleCore 𝕜 (X × I))
    (e₀ : ((A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst).pullback
        (cylinderSetIncl (E : Set X)) ≅ A.pullback (cylinderSetIncl (E : Set X)))
    (he₀ : ∀ x : (E : Set X),
      e₀.hom.fiberMap (x, 0) = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) :
    ∃ e : (A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst ≅ A,
      (∀ x : X, e.hom.fiberMap (x, 0) = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) ∧
      (pullbackFunctor (cylinderSetIncl (E : Set X))).mapIso e = e₀ :=
  exists_iso_cylinder_of_relSubcomplex isCompact_empty E A e₀ he₀

end TauCeti.FiniteRankBundleCore
