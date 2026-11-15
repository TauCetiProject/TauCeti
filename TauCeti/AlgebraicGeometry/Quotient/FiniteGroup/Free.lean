/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import TauCeti.AlgebraicGeometry.Quotient.FiniteGroup.Affine
public import TauCeti.RingTheory.Invariant.Free

/-!
# Affine quotients by free actions of finite groups

Let a finite group `G` act on a commutative ring `A`, and suppose that the action on `Spec A` is
free: for every `g ≠ 1`, the elements `g • a - a` generate the unit ideal of `A`, so that no
geometric point of `Spec A` is fixed by `g`. Then the projection `Spec A ⟶ Spec Aᴳ` to the affine
invariant quotient is finite and étale; it is also surjective, so it is a finite locally free
surjection. Both statements are the geometric form of the Chase–Harrison–Rosenberg
theorem in `TauCeti.RingTheory.Invariant.Free`, which also identifies
`Spec A ×_{Spec Aᴳ} Spec A` with the disjoint union of `|G|` copies of `Spec A`
(`TauCeti.MulSemiringAction.tensorToPi_bijective`).

## Main results

* `TauCeti.AffineInvariantQuotient.isFinite_projection_of_free`: the projection is finite.
* `TauCeti.AffineInvariantQuotient.etale_projection`: the projection is étale.

## References

* S. U. Chase, D. K. Harrison and A. Rosenberg, *Galois theory and Galois cohomology of
  commutative rings*, Mem. Amer. Math. Soc. **52** (1965), 15–33, Theorem 1.3.
* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §4.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AffineInvariantQuotient

variable {A G : Type*} [CommRing A] [Group G] [MulSemiringAction G A] [Finite G]

/-- For a free action of a finite group, the projection to the affine invariant quotient is
finite. -/
theorem isFinite_projection_of_free
    (hG : ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤) :
    IsFinite (projection A G) := by
  have := MulSemiringAction.moduleFinite (R := FixedPoints.subring A G) hG
  exact isFinite_projection A G

/-- For a free action of a finite group, the projection to the affine invariant quotient is
étale. -/
theorem etale_projection
    (hG : ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤) :
    Etale (projection A G) := by
  have := MulSemiringAction.etale (R := FixedPoints.subring A G) hG
  rw [projection_def]
  exact HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr this)

end TauCeti.AffineInvariantQuotient
