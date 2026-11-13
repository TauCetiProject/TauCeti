/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Isogeny
public import TauCeti.Geometry.Lie.Subgroup.Kernel
public import TauCeti.Analysis.Matrix.UnitaryGroup.CentralIsogeny

/-!
# Period lattices under the central isogeny of the torus of `U(2)`

The diagonal torus `T ≅ S¹ × S¹` of `U(2)` receives the central isogeny `Z × T_ss → T`,
`(a, b) ↦ (a b, a b⁻¹)` (`TauCeti.unitaryTorusCentralIsogeny`), from the product of the identity
component `Z = {diag(a, a)}` of the centre and the torus `T_ss = {diag(b, b⁻¹)}` of `SU(2)`. Its
kernel `{(1, 1), (-1, -1)}` has two elements, so by
`ContinuousMonoidHom.relIndex_map_lieMap_periodLattice` the real splitting `𝔱 = 𝔷 ⊕ 𝔱_ss` of the
Lie algebra does not split the period lattice of `T` integrally: `Λ_ℤ(Z) ⊕ Λ_ℤ(T_ss)` has index
two in `Λ_ℤ(T)`.

## Main results

* `TauCeti.relIndex_map_lieMap_unitaryTorusCentralIsogeny_periodLattice`: the period lattice of
  the source of the central isogeny of the torus of `U(2)` has index two in that of its target.

## References

* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 15 (Tori).
-/

public section

open scoped Manifold

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **The period lattices of the central isogeny of the torus of `U(2)`.** The period lattice
`Λ_ℤ(Z) ⊕ Λ_ℤ(T_ss)` of `Z × T_ss` has index two in the period lattice of the diagonal torus `T`
of `U(2)`: the splitting of the Lie algebra into its central and semisimple parts does not split
the period lattice integrally. -/
theorem relIndex_map_lieMap_unitaryTorusCentralIsogeny_periodLattice :
    ((periodLattice ((𝓡 1).prod (𝓡 1)) (Circle × Circle)).map
        (unitaryTorusCentralIsogeny.lieMap (I := (𝓡 1).prod (𝓡 1))
          (I' := (𝓡 1).prod (𝓡 1))).toLinearMap.toAddMonoidHom).relIndex
      (periodLattice ((𝓡 1).prod (𝓡 1)) (Circle × Circle)) = 2 := by
  have : Finite unitaryTorusCentralIsogeny.ker := Nat.finite_of_card_ne_zero (by
    rw [card_ker_unitaryTorusCentralIsogeny]; exact two_ne_zero)
  have : FiniteDimensional ℝ (LeftInvariantDerivation ((𝓡 1).prod (𝓡 1)) (Circle × Circle)) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  -- The Lie map is injective because the kernel is finite, hence bijective in finite dimension.
  let L := (unitaryTorusCentralIsogeny.lieMap (I := (𝓡 1).prod (𝓡 1))
    (I' := (𝓡 1).prod (𝓡 1))).toLinearMap
  have hinj : Function.Injective L :=
    unitaryTorusCentralIsogeny.lieMap_injective_of_discreteTopology_ker
  rw [unitaryTorusCentralIsogeny.relIndex_map_lieMap_periodLattice
    ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩, card_ker_unitaryTorusCentralIsogeny]

end TauCeti
