/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Isogeny
public import TauCeti.Geometry.Lie.Subgroup.Kernel
public import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# The power maps of the circle: period lattices

For a natural number `n`, the power map `z ↦ zⁿ` of the circle is the continuous homomorphism
`ContinuousMonoidHom.id Circle ^ n`. For `n ≠ 0` it is an isogeny of the circle onto itself, and
this file computes how it acts on the period lattice of the circle as a compact connected
commutative Lie group.

The kernel of the power map is the group of `n`-th roots of unity, of order `n`
(`TauCeti.natCard_powMonoidHom_ker`), so by the general index formula for isogenies
(`ContinuousMonoidHom.relIndex_map_lieMap_periodLattice`) the Lie map of `z ↦ zⁿ` carries the
period lattice `Λ_ℤ = (2π)⁻¹ ker(exp)` of the source onto a sublattice of index `n` in that of the
target (`TauCeti.relIndex_map_lieMap_id_circle_pow_periodLattice`). On the dual side, a character
of the circle factors through `z ↦ zⁿ` exactly when its exponent is divisible by `n`
(`ContinuousMonoidHom.exists_eq_comp_id_pow_iff`).

The case `n = 2` is the restriction of the double cover `SU(2) → SO(3)` to the maximal tori, read
in circle coordinates in `TauCeti.RepresentationTheory.SU2.RotationTorus`.

## Main results

* `TauCeti.relIndex_map_lieMap_id_circle_pow_periodLattice`: the image of the period lattice under
  the Lie map of `z ↦ zⁿ` has index `n`.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 3 (The Exponential Map) and Chapter II, § 8 (Characters of tori).
-/

public section

open scoped Manifold

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **The period lattices of a power map of the circle.** For `n > 0`, the Lie map of the power
map `z ↦ zⁿ` carries the period lattice `Λ_ℤ = (2π)⁻¹ ker(exp)` of the circle onto a sublattice of
index `n` in the period lattice of the circle. -/
theorem relIndex_map_lieMap_id_circle_pow_periodLattice (n : ℕ) [NeZero n] :
    ((periodLattice (𝓡 1) Circle).map
        ((ContinuousMonoidHom.id Circle ^ n).lieMap (I := 𝓡 1)
          (I' := 𝓡 1)).toLinearMap.toAddMonoidHom).relIndex
      (periodLattice (𝓡 1) Circle) = n := by
  -- The kernel of `z ↦ zⁿ` is the group of `n`-th roots of unity, which has `n` elements.
  have hcard : Nat.card (ContinuousMonoidHom.id Circle ^ n).ker = n := by
    have hker : (ContinuousMonoidHom.id Circle ^ n).ker = (powMonoidHom n : Circle →* Circle).ker :=
      by ext; simp [MonoidHom.mem_ker]
    rw [hker]
    exact natCard_powMonoidHom_ker Circle n
  have : Finite (ContinuousMonoidHom.id Circle ^ n).ker :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact NeZero.ne n)
  have : FiniteDimensional ℝ (LeftInvariantDerivation (𝓡 1) Circle) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  -- The Lie map is injective because the kernel is finite, hence bijective in finite dimension.
  have hinj : Function.Injective
      ((ContinuousMonoidHom.id Circle ^ n).lieMap (I := 𝓡 1) (I' := 𝓡 1)).toLinearMap :=
    (ContinuousMonoidHom.id Circle ^ n).lieMap_injective_of_discreteTopology_ker
  rw [(ContinuousMonoidHom.id Circle ^ n).relIndex_map_lieMap_periodLattice
    ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩, hcard]

end TauCeti
