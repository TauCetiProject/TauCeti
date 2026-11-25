/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Basic

/-!
# The group action on a valuation spectrum by algebra automorphisms

Let a group `G` act on an `A`-algebra `B` by `A`-algebra automorphisms, for instance on a finite
étale `G`-torsor over `A` (`TauCeti.Algebra.IsFiniteEtaleTorsor G A B`). The group `G` acts on
`Spv B` by transport of structure, `(g • y)(b) = y(g⁻¹ • b)`, that is `g • y = comap (g⁻¹ • ·) y`.
This file shows that points in one orbit have the same image in `Spv A`
(`TauCeti.ValuationSpectrum.comap_algebraMap_comap_toRingHom`), since `G` fixes `A`. No
finiteness or torsor hypothesis is needed.

For the converse, that the fibres of `Spv B → Spv A` are exactly the `G`-orbits when `G` is
finite and `Algebra.IsInvariant A B G` holds, see
`TauCeti.ValuationSpectrum.comap_algebraMap_eq_comap_algebraMap_iff_of_isInvariant`.
-/

public section

namespace TauCeti.ValuationSpectrum

variable {G A B : Type*} [Group G] [CommRing A] [CommRing B] [Algebra A B]
  [MulSemiringAction G B] [SMulCommClass G A B]

/-- Pulling back along the action of `g ∈ G` does not change the image in `Spv A`, since `G` acts
by `A`-algebra automorphisms. -/
@[simp]
theorem comap_algebraMap_comap_toRingHom (g : G) (y : Spv B) :
    comap (algebraMap A B) (comap (MulSemiringAction.toRingHom G B g) y) =
      comap (algebraMap A B) y := by
  rw [comap_comap]
  congr 1
  exact RingHom.ext fun a ↦ smul_algebraMap g a

end TauCeti.ValuationSpectrum
