/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import TauCeti.AlgebraicGeometry.Quotient.Affine
public import TauCeti.RingTheory.Invariant.Basic

/-!
# Affine invariant quotients by finite groups

For a finite group acting on a commutative ring `A`, the invariant-spectrum projection is
integral and surjective, and its topological fibres are precisely the orbits of prime ideals.
If `A` is of finite type over its fixed subring, the projection is finite; in particular,
this holds when `A` is of finite type over an invariant base semiring `R`.
These results supplement the affine-target universal property in
`TauCeti.AlgebraicGeometry.Quotient.Affine`.

Neither flatness nor finite presentation of the quotient projection is asserted.

## Main results

* The projection is integral and surjective for finite groups.
* `isFinite_projection`: the projection is finite when `A` is of finite type over its
  fixed subring.
* `isFinite_projection_of_finiteType`: finiteness over an invariant base semiring suffices.
* `isQuotientMap_projection`: the projection is a topological quotient map.
* `projection_eq_iff_exists_smul`: its fibres are prime-ideal orbits.

## References

* Formal sources: Mathlib's `Algebra.IsInvariant.isIntegral` and
  `Algebra.IsInvariant.exists_smul_of_under_eq`.
* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §1.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped Pointwise

namespace TauCeti.AffineInvariantQuotient

universe u v w

section Group

variable (A : Type u) (G : Type v) [CommRing A] [Group G] [MulSemiringAction G A] [Finite G]

/-- The invariant-spectrum projection is integral for a finite group action. -/
instance : IsIntegralHom (projection A G) := by
  rw [projection_def]
  exact IsIntegralHom.SpecMap_iff.mpr
    (algebraMap_isIntegral_iff.mpr (Algebra.IsInvariant.isIntegral _ _ G))

/-- The quotient projection is surjective for a finite group action. -/
instance : Surjective (projection A G) := by
  rw [projection_def]
  let := Algebra.IsInvariant.isIntegral (FixedPoints.subring A G) A G
  exact ⟨Algebra.IsIntegral.comap_surjective _ _⟩

/-- The quotient projection is finite when `A` is of finite type over its fixed subring. -/
theorem isFinite_projection [Algebra.FiniteType (FixedPoints.subring A G) A] :
    IsFinite (projection A G) := by
  rw [projection_def]
  let := Algebra.IsInvariant.isIntegral (FixedPoints.subring A G) A G
  exact IsFinite.SpecMap_iff _ |>.mpr (RingHom.finite_algebraMap.mpr Algebra.IsIntegral.finite)

/-- The quotient projection is finite when `A` is of finite type over an invariant base `R`. -/
theorem isFinite_projection_of_finiteType (R : Type w) [CommSemiring R] [Algebra R A]
    [SMulCommClass G R A] [Algebra.FiniteType R A] : IsFinite (projection A G) := by
  let : Algebra.FiniteType (FixedPoints.subring A G) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (FixedPoints.subalgebra R A G) A
  exact isFinite_projection A G

/-- The projection is a quotient map of topological spaces. -/
theorem isQuotientMap_projection : Topology.IsQuotientMap (projection A G) :=
  (projection A G).isClosedMap.isQuotientMap
    (projection A G).continuous (Surjective.surj (f := projection A G))

/-- Two points have the same image exactly when they are in the same spectrum orbit. -/
theorem projection_eq_iff_exists_smul (x y : PrimeSpectrum A) :
    projection A G x = projection A G y ↔
      ∃ g : G, y = g • x := by
  simp only [projection_base_apply]
  -- Rewrite matching cannot reduce the carrier of `quotient` to `PrimeSpectrum`.
  -- Only the carrier changes here; `projection_base_apply` already identifies the point map.
  change PrimeSpectrum.comap (algebraMap (FixedPoints.subring A G) A) x =
    PrimeSpectrum.comap (algebraMap (FixedPoints.subring A G) A) y ↔ _
  rw [PrimeSpectrum.ext_iff]
  simp only [PrimeSpectrum.comap_asIdeal, ← Ideal.under_def]
  constructor
  · intro h
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
      (FixedPoints.subring A G) A G x.asIdeal y.asIdeal h
    exact ⟨g, PrimeSpectrum.ext hg⟩
  · rintro ⟨g, hg⟩
    simpa only [hg, PrimeSpectrum.asIdeal_smul] using
      (Ideal.under_smul (FixedPoints.subring A G) x.asIdeal g).symm

end Group

end TauCeti.AffineInvariantQuotient
