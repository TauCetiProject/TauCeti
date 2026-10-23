/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.IsotropicFlag.Basic
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Smooth
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.IsotropicFlag.Lift

/-!
# Smoothness of the symplectic isotropic flag subgroup

The standard complete isotropic flag stabilizer in `Sp₂ₘ` is smooth over every commutative
ring. Its matrix points lift across square-zero quotients by lifting the upper-triangular
Levi factor and the symmetric upper-unipotent block. Finite presentation follows from the
finite set of flag equations in the smooth symplectic coordinate algebra.

This gives the smoothness condition needed to recognize the flag stabilizer as a Borel
subgroup and to use it in a symplectic pinning. Characteristic two requires no exception.

The infinitesimal criterion follows the organization of
`TauCeti.Algebra.AlgebraicGroup.Symplectic.Smooth`.

## References

* SGA 3, Exposé XXII, for the split symplectic group and its Borel subgroups.
* J. S. Milne, *Algebraic Groups* (2017), §24.6.
-/

public section

open WithConv

namespace TauCeti.Symplectic.IsotropicFlag

universe u

variable (R : Type u) [CommRing R] (m : ℕ)

private instance instFormallySmoothCoordinateHopfAlgebra :
    Algebra.FormallySmooth R (coordinateHopfAlgebra R m) := by
  apply Algebra.FormallySmooth.of_comp_surjective
  intro B _ _ I hI f
  let : IsLocalHom (Ideal.Quotient.mk I) :=
    ⟨fun _ hx ↦ (IsNilpotent.isUnit_quotient_mk_iff (I := I) ⟨2, hI⟩).mp hx⟩
  obtain ⟨t, ht⟩ :=
    GLSymplecticFin.IsotropicFlag.map_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
      (pointsMulEquiv R m (A := B ⧸ I) (toConv f))
  let g : WithConv (coordinateHopfAlgebra R m →ₐ[R] B) :=
    (pointsMulEquiv R m (A := B)).symm t
  refine ⟨g.ofConv, ?_⟩
  apply toConv_injective
  apply (pointsMulEquiv R m (A := B ⧸ I)).injective
  rw [← AlgHom.mapValue_apply, pointsMulEquiv_mapValue]
  have hg : pointsMulEquiv R m (A := B) g = t := MulEquiv.apply_symm_apply _ _
  rw [hg, ← AlgHom.toRingHom_eq_coe, Ideal.Quotient.mkₐ_toRingHom]
  exact ht

/-- The coordinate algebra of the standard complete isotropic flag stabilizer in `Sp₂ₘ`
is smooth over every commutative base ring, in every rank. -/
instance instSmoothCoordinateHopfAlgebra :
    Algebra.Smooth R (coordinateHopfAlgebra R m) := by
  let _ : Algebra.FinitePresentation R (coordinateHopfAlgebra R m) :=
    Algebra.FinitePresentation.quotient (definingHopfIdeal_toIdeal_fg R m)
  exact ⟨inferInstance, inferInstance⟩

/-- The commutative Hopf algebra representing the standard complete isotropic flag stabilizer
in `Sp₂ₘ` satisfies the smoothness object property over every commutative base ring. -/
theorem smoothCommHopfAlgProperty_coordinateHopfAlgebra :
    smoothCommHopfAlgProperty R (coordinateHopfAlgebra R m) := by
  rw [smoothCommHopfAlgProperty_iff]
  infer_instance

end TauCeti.Symplectic.IsotropicFlag
