/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Symplectic.Basic

/-!
# The integral type-C carrier as the symplectic group scheme

The full-weight type-`C_(n+1)` Kostant carrier is the standard symplectic group scheme over
`ℤ`. This file packages the integral defining-ideal equality as a group-scheme isomorphism
compatible with the ambient matrix realization. In particular, the comparison retains the
integral model, rather than identifying only its field fibres.

The ambient compatibility transports the carrier's numbered root subgroups and weight torus
to the symplectic scheme without changing their matrices. It does not construct a Borel subgroup
or assert a complete pinning. Scalar extension to every commutative ring is
provided by `SpStd.baseChangeSymplecticIso` in the imported module.

The construction uses `SpStd.definingIdeal_eq_symplecticDefiningHopfIdeal` and the
quotient-spectrum transport API `CommHopfAlgCat.eqToHom_comp_quotientSpecι`.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§26--27.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3--4.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.SpStd

variable (n : ℕ)

/-- The integral full-weight type-`C_(n+1)` Kostant carrier is canonically isomorphic to
`Sp_(2n+2)` over `ℤ`. The comparison uses the same ambient general-linear coordinates. -/
noncomputable def symplecticIso :
    groupScheme n ≅ Symplectic.groupScheme ℤ (n + 1) :=
  eqToIso (groupScheme_def n) ≪≫
    eqToIso (congrArg
      (CommHopfAlgCat.quotientSpec
        (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))))
      (definingIdeal_eq_symplecticDefiningHopfIdeal n)) ≪≫
    (eqToIso (Symplectic.groupScheme_def ℤ (n + 1))).symm

/-- The integral carrier--symplectic isomorphism preserves the closed immersion into the
ambient general linear group. Thus it preserves the full matrix-valued functor of points. -/
@[reassoc (attr := simp)]
theorem symplecticIso_hom_comp_inclusion :
    (symplecticIso n).hom ≫ Symplectic.inclusion ℤ (n + 1) = carrierι n := by
  rw [symplecticIso, Iso.trans_hom, Iso.trans_hom,
    Symplectic.inclusion_def, carrierι_eq_eqToHom_comp_hopfIdealInclusion,
    GeneralLinear.hopfIdealInclusion_def, GeneralLinear.hopfIdealInclusion_def]
  simp only [eqToIso.hom, Iso.symm_hom, eqToIso.inv, eqToHom_refl, Category.id_comp,
    Category.assoc]
  rw [← Category.assoc (eqToHom _) (CommHopfAlgCat.quotientSpecι _ _) _,
    CommHopfAlgCat.eqToHom_comp_quotientSpecι _
      (definingIdeal_eq_symplecticDefiningHopfIdeal n)]

/-- The inverse integral comparison also preserves the ambient matrix realization. -/
@[reassoc (attr := simp)]
theorem symplecticIso_inv_comp_carrierι :
    (symplecticIso n).inv ≫ carrierι n = Symplectic.inclusion ℤ (n + 1) := by
  rw [← symplecticIso_hom_comp_inclusion, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

end TauCeti.SpStd
