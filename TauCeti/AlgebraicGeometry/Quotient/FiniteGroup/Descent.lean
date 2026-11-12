/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import TauCeti.RingTheory.Invariant.AlgebraDescent

/-!
# Galois descent of affine schemes along a free finite-group quotient

Let a finite group `G` act freely on a commutative `A`-algebra `B` by `A`-algebra automorphisms
with ring of invariants `A`, so that `Spec B ⟶ Spec A` is the quotient of `Spec B` by `G`, a
finite étale `G`-torsor when `A → B` is injective. An affine scheme `Spec C` over `Spec B` on
which `G` acts compatibly with its action on `Spec B` (a `B`-algebra `C` with a semilinear action
of `G`) is the base change along `Spec B ⟶ Spec A` of the affine scheme `Spec Cᴳ` of its
fixed points (`TauCeti.MulSemiringAction.isPullback_SpecMap_fixedPoints`). This is the geometric
form of `TauCeti.MulSemiringAction.isPushout_fixedPoints`; morphisms descend by
`TauCeti.MulSemiringAction.existsUnique_algHom_extend_fixedPoints`.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII, §1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u v

namespace TauCeti.MulSemiringAction

variable {A B C : Type u} {G : Type v} [CommRing A] [CommRing B] [Algebra A B] [Group G]
  [MulSemiringAction G B] [SMulCommClass G A B] [CommRing C] [Algebra A C] [Algebra B C]
  [IsScalarTower A B C] [MulSemiringAction G C] [SMulDistribClass G B C] [SMulCommClass G A C]

/-- **Galois descent of affine schemes.** For a free action of a finite group `G` on `B` with ring
of invariants `A`, an affine scheme `Spec C` over `Spec B` with a compatible action of `G` is the
base change of `Spec Cᴳ` along `Spec B ⟶ Spec A`: the square formed by `Spec C ⟶ Spec B`,
`Spec C ⟶ Spec Cᴳ`, `Spec B ⟶ Spec A` and `Spec Cᴳ ⟶ Spec A` is cartesian. -/
theorem isPullback_SpecMap_fixedPoints [Finite G] [Algebra.IsInvariant A B G]
    (hG : ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun b : B ↦ g • b - b) = ⊤) :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap B C)))
      (Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra A C G) C)))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A (FixedPoints.subalgebra A C G)))) :=
  have := isPushout_fixedPoints A B G C hG
  isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout A B _ C)

end TauCeti.MulSemiringAction
