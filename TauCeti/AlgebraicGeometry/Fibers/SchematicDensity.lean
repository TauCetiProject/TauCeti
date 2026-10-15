/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Fibers
public import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Schematic density of the generic fibre

For a flat scheme over a commutative ring, scalar extension along an injective algebra map is
scheme-theoretically dominant. For a domain and its fraction field, this is the canonical
generic-fibre inclusion.
Consequently, two morphisms into a separated target agree whenever their restrictions to this
fibre agree. Neither reducedness nor finite presentation of the source is needed.

This is the density argument used for uniqueness of extensions on flat models over valuation
rings; see Q. Liu, *Algebraic Geometry and Arithmetic Curves*, §4.3. The construction uses
Mathlib's stability of schematic dominance under flat base change.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

universe u

variable (R K : Type u) [CommRing R]
variable [CommRing K] [Algebra R K]
variable {X Y : Scheme.{u}}

/-- Scalar extension of a flat scheme along an injective algebra map is schematically dominant.
For a domain and its fraction field, the generic fibre is schematically dense in the total space. -/
theorem isSchemeTheoreticallyDominant_genericFiberι
    (hRK : Function.Injective (algebraMap R K)) (toBase : X ⟶ Spec (.of R)) [Flat toBase] :
    IsSchemeTheoreticallyDominant (genericFiberι R K toBase) := by
  have : IsSchemeTheoreticallyDominant
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    rwa [isSchemeTheoreticallyDominant_SpecMap_iff, CommRingCat.hom_ofHom]
  exact IsSchemeTheoreticallyDominant.of_isPullback
    (isPullback_genericFiber R K toBase).flip

/-- Morphisms over a ring from a flat source to a separated target are determined by their
restriction after an injective scalar extension. In particular the source need not be reduced. -/
theorem ext_of_genericFiberι_eq (hRK : Function.Injective (algebraMap R K))
    (toBase : X ⟶ Spec (.of R)) [Flat toBase]
    (s : Y ⟶ Spec (.of R)) [IsSeparated s] {f g : X ⟶ Y}
    (h : f ≫ s = g ≫ s) (hK : genericFiberι R K toBase ≫ f = genericFiberι R K toBase ≫ g) :
    f = g := by
  have := isSchemeTheoreticallyDominant_genericFiberι R K hRK toBase
  exact ext_of_isSchemeTheoreticallyDominant (genericFiberι R K toBase) s h hK

end TauCeti
