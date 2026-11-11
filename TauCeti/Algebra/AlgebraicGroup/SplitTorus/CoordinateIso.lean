/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.FiniteType

/-!
# Universe lifting of split-torus coordinate algebras

For every rank, lifting the finite coordinate indices to the base ring's universe identifies
the two split-torus coordinate Hopf algebras. On points, this identification reads the
coordinate tuple at the lifted indices. This is the adapter used by chosen split maximal tori.

The coordinate construction follows
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.MaximalTorus`, using Mathlib's
`MonoidAlgebra.domCongrBialgEquiv` and `Finsupp.domCongr`.
-/

public section

namespace TauCeti.SplitTorus

universe u v

variable (R : Type u) [CommRing R] (n : ℕ)

/-- Lift the coordinate indices of a rank-`n` split torus to the base ring's universe. -/
noncomputable def uliftCoordinateRingIso :
    (DiagonalizableGroup.coordinateRing R (characterGroup (Fin n))).obj ≅
      (DiagonalizableGroup.coordinateRing R (characterGroup (ULift.{u} (Fin n)))).obj :=
  -- Specify the unbundled character types so elaboration does not seek an additive
  -- structure on the bundled multiplicative character groups.
  _root_.CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv R R
    (show Multiplicative (Fin n →₀ ℤ) ≃* Multiplicative (ULift.{u} (Fin n) →₀ ℤ) from
      AddEquiv.toMultiplicative (Finsupp.domCongr (M := ℤ) Equiv.ulift.symm)))

/-- The lifted coordinate map is Mathlib's reindexing of the monoid algebra. -/
@[simp↓]
theorem uliftCoordinateRingIso_hom_apply
    (x : MonoidAlgebra R (Multiplicative (Fin n →₀ ℤ))) :
    (uliftCoordinateRingIso R n).hom.hom x =
      MonoidAlgebra.domCongr R R
        (AddEquiv.toMultiplicative
          (Finsupp.domCongr (M := ℤ) (Equiv.ulift.symm : Fin n ≃ ULift.{u} (Fin n)))) x :=
  (rfl)

/-- Lifting split-torus coordinates reads a point's coordinate at the lifted index. -/
-- Apply before `BialgHom.mapDomain_apply` expands point precomposition.
@[simp↓]
theorem pointsMulEquiv_mapDomain_uliftCoordinateRingIso
    {A : Type v} [CommRing A] [Algebra R A]
    (q : WithConv (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) →ₐ[R] A))
    (i : Fin n) :
    pointsMulEquiv (BialgHom.mapDomain (uliftCoordinateRingIso R n).hom.hom q) i =
      pointsMulEquiv q (ULift.up i) := by
  apply Units.ext
  rw [pointsMulEquiv_apply_coe, pointsMulEquiv_apply_coe,
    BialgHom.mapDomain_apply, AlgHom.comp_apply, BialgHom.coe_toAlgHom]
  rw [uliftCoordinateRingIso_hom_apply, MonoidAlgebra.domCongr_single]
  simp [AddEquiv.toMultiplicative_apply_apply, Finsupp.domCongr_apply]

end TauCeti.SplitTorus
