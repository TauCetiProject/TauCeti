/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.CoordinatePower
public import TauCeti.LinearAlgebra.IntegralLattice.CoordinatePower
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Pi

/-!
# Discriminant forms of coordinate powers

The coordinate power `L^ι` is the orthogonal sum of the constant family at `L`, so the canonical
equivalence `TauCeti.IntegralLattice.discriminantGroupPiEquiv` specialises to

```text
A_(L^ι) ≃ (A_L)^ι,
```

which sends the class of `x` to the family of classes of its coordinates. This file proves that it
is an isometry from the discriminant pairing of `L^ι` to the coordinate power of the discriminant
pairing of `L`, and, when `L` is even, of the half-norm discriminant quadratic modules.

Composing with a coordinatewise alphabet isometry gives the interface through which codes enter
lattice constructions: an isometry `A ≅ A_L` from a finite quadratic alphabet induces an isometry
from the coordinate module `A^ι` to the actual discriminant module of the orthogonal sum `L^ι`.
An additive code `C ≤ A^ι` is carried to a subgroup of `A_(L^ι)`, and quadratic isotropy and the
Lagrangian condition transfer along this isometry by
`TauCeti.FiniteQuadraticModule.Isometry.isIsotropic_map_iff` and
`TauCeti.FiniteQuadraticModule.Isometry.isLagrangian_map_iff`.

## Main declarations

* `TauCeti.IntegralLattice.discriminantBilinearIsometryCoordinatePower`: the equivalence
  `A_(L^ι) ≃ (A_L)^ι` is an isometry of finite bilinear modules.
* `TauCeti.IntegralLattice.discriminantQuadraticIsometryCoordinatePower`: for even `L`, it is an
  isometry of finite quadratic modules, the constant-family case of
  `TauCeti.IntegralLattice.discriminantQuadraticIsometryPi`.
* `TauCeti.FiniteQuadraticModule.Isometry.coordinatePowerDiscriminant`: the isometry
  `A^ι ≅ A_(L^ι)` induced by an alphabet isometry `A ≅ A_L`, with the bilinear analogue
  `TauCeti.FiniteBilinearModule.Isometry.coordinatePowerDiscriminant`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §3.
* `TauCeti/LinearAlgebra/IntegralLattice/Discriminant/Operations.lean`: the binary orthogonal-sum
  isometries `A_(L ⊥ M) ≃ A_L × A_M` (`discriminantBilinearIsometryOrthogonalSum` and
  `discriminantQuadraticIsometryOrthogonalSum`). The isometries of this file are their analogue
  for the `ι`-fold orthogonal sum `L^ι`.
-/

public section

namespace TauCeti.IntegralLattice

universe u v w

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable (L : IntegralLattice V) (ι : Type v) [Fintype ι]

/-! ## The discriminant bilinear module -/

/-- The equivalence `A_(L^ι) ≃ (A_L)^ι` of discriminant groups is an isometry from the
discriminant pairing of `L^ι` to the coordinate power of the discriminant pairing of `L`. -/
noncomputable def discriminantBilinearIsometryCoordinatePower [L.IsNondegenerate] :
    FiniteBilinearModule.Isometry (L.coordinatePower ι).discriminantBilinearModule
      (L.discriminantBilinearModule.coordinatePower ι) where
  toAddEquiv := (discriminantGroupPiEquiv fun _ : ι ↦ L).toAddEquiv
  map_pairing' := by
    intro x y
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        -- The isometry's carrier is definitionally the discriminant group, but this conversion
        -- is intentionally not part of the public reduction API.
        change ∑ i, L.discriminantPairing
            (discriminantGroupPiEquiv (fun _ : ι ↦ L) (Submodule.Quotient.mk x) i)
            (discriminantGroupPiEquiv (fun _ : ι ↦ L) (Submodule.Quotient.mk y) i) =
          (L.coordinatePower ι).discriminantPairing
            (Submodule.Quotient.mk x) (Submodule.Quotient.mk y)
        simp only [discriminantGroupPiEquiv_mk, discriminantPairing_mk, pi_form, piForm_apply,
          coe_piDualCarrierEquiv_apply]
        exact (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))) _ _).symm

/-- The underlying additive equivalence of the coordinate-power discriminant-bilinear isometry is
the canonical equivalence `A_(L^ι) ≃ (A_L)^ι` of discriminant groups. -/
@[simp]
theorem discriminantBilinearIsometryCoordinatePower_toAddEquiv [L.IsNondegenerate] :
    (L.discriminantBilinearIsometryCoordinatePower ι).toAddEquiv =
      (discriminantGroupPiEquiv fun _ : ι ↦ L).toAddEquiv :=
  (rfl)

/-- The coordinate-power discriminant-bilinear isometry acts through the canonical
equivalence `A_(L^ι) ≃ (A_L)^ι` of discriminant groups. -/
@[simp]
theorem discriminantBilinearIsometryCoordinatePower_apply [L.IsNondegenerate]
    (x : (L.coordinatePower ι).DiscriminantGroup) :
    L.discriminantBilinearIsometryCoordinatePower ι x =
      discriminantGroupPiEquiv (fun _ : ι ↦ L) x :=
  (rfl)

/-! ## The discriminant quadratic module -/

/-- For an even lattice `L`, the equivalence `A_(L^ι) ≃ (A_L)^ι` of discriminant groups is an
isometry from the half-norm discriminant quadratic module of `L^ι` to the coordinate power of the
discriminant quadratic module of `L`. -/
noncomputable def discriminantQuadraticIsometryCoordinatePower [L.IsNondegenerate]
    (hL : L.IsEven) :
    FiniteQuadraticModule.Isometry
      ((L.coordinatePower ι).discriminantQuadraticModule (hL.coordinatePower ι))
      ((L.discriminantQuadraticModule hL).coordinatePower ι) :=
  -- The coordinate power of a finite quadratic module has definitionally the same quadratic map
  -- as the orthogonal sum of the constant family.
  discriminantQuadraticIsometryPi (fun _ : ι ↦ L) fun _ ↦ hL

/-- The underlying additive equivalence of the coordinate-power discriminant-quadratic isometry is
the canonical equivalence `A_(L^ι) ≃ (A_L)^ι` of discriminant groups. -/
@[simp]
theorem discriminantQuadraticIsometryCoordinatePower_toAddEquiv [L.IsNondegenerate]
    (hL : L.IsEven) :
    (L.discriminantQuadraticIsometryCoordinatePower ι hL).toAddEquiv =
      (discriminantGroupPiEquiv fun _ : ι ↦ L).toAddEquiv :=
  AddEquiv.ext (discriminantQuadraticIsometryPi_apply (fun _ : ι ↦ L) fun _ ↦ hL)

/-- The coordinate-power discriminant-quadratic isometry acts through the canonical
equivalence `A_(L^ι) ≃ (A_L)^ι` of discriminant groups. -/
@[simp]
theorem discriminantQuadraticIsometryCoordinatePower_apply [L.IsNondegenerate] (hL : L.IsEven)
    (x : (L.coordinatePower ι).DiscriminantGroup) :
    L.discriminantQuadraticIsometryCoordinatePower ι hL x =
      discriminantGroupPiEquiv (fun _ : ι ↦ L) x :=
  discriminantQuadraticIsometryPi_apply (fun _ : ι ↦ L) (fun _ ↦ hL) x

/-- Forgetting the quadratic maps from the coordinate-power discriminant isometry recovers the
coordinate-power discriminant-bilinear isometry. -/
@[simp]
theorem discriminantQuadraticIsometryCoordinatePower_toFiniteBilinearModule [L.IsNondegenerate]
    (hL : L.IsEven) :
    (L.discriminantQuadraticIsometryCoordinatePower ι hL).toFiniteBilinearModule =
      L.discriminantBilinearIsometryCoordinatePower ι := by
  apply FiniteBilinearModule.Isometry.toAddEquiv_injective
  rw [FiniteQuadraticModule.Isometry.toFiniteBilinearModule_toAddEquiv,
    discriminantQuadraticIsometryCoordinatePower_toAddEquiv,
    discriminantBilinearIsometryCoordinatePower_toAddEquiv]

end TauCeti.IntegralLattice

/-! ## Coordinate alphabets -/

namespace TauCeti

universe u v w

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V} [L.IsNondegenerate]

open IntegralLattice

/-- An isometry `A ≅ A_L` from a finite bilinear alphabet to the discriminant bilinear module of a
nondegenerate lattice induces, coordinatewise, an isometry from the coordinate module `A^ι` to the
discriminant bilinear module of the orthogonal sum `L^ι`. -/
noncomputable def FiniteBilinearModule.Isometry.coordinatePowerDiscriminant
    {A : FiniteBilinearModule.{w}} (f : Isometry A L.discriminantBilinearModule)
    (ι : Type v) [Fintype ι] :
    Isometry (A.coordinatePower ι) (L.coordinatePower ι).discriminantBilinearModule :=
  (f.coordinatePower ι).trans (L.discriminantBilinearIsometryCoordinatePower ι).symm

/-- The coordinatewise bilinear alphabet isometry applies the alphabet isometry in each
coordinate and then identifies `(A_L)^ι` with `A_(L^ι)`. -/
@[simp]
theorem FiniteBilinearModule.Isometry.coordinatePowerDiscriminant_apply
    {ι : Type v} [Fintype ι] {A : FiniteBilinearModule.{w}}
    (f : Isometry A L.discriminantBilinearModule) (x : ι → A) :
    f.coordinatePowerDiscriminant ι x =
      (L.discriminantBilinearIsometryCoordinatePower ι).symm (f.coordinatePower ι x) := by
  rw [coordinatePowerDiscriminant, trans_apply]

/-- An isometry `A ≅ A_L` from a finite quadratic alphabet to the discriminant module of an even
lattice induces, coordinatewise, an isometry from the coordinate module `A^ι` to the discriminant
module of the orthogonal sum `L^ι`. -/
noncomputable def FiniteQuadraticModule.Isometry.coordinatePowerDiscriminant {hL : L.IsEven}
    {A : FiniteQuadraticModule.{w}} (f : Isometry A (L.discriminantQuadraticModule hL))
    (ι : Type v) [Fintype ι] :
    Isometry (A.coordinatePower ι)
      ((L.coordinatePower ι).discriminantQuadraticModule (hL.coordinatePower ι)) :=
  (f.coordinatePower ι).trans (L.discriminantQuadraticIsometryCoordinatePower ι hL).symm

/-- The coordinatewise quadratic alphabet isometry applies the alphabet isometry in each
coordinate and then identifies `(A_L)^ι` with `A_(L^ι)`. -/
@[simp]
theorem FiniteQuadraticModule.Isometry.coordinatePowerDiscriminant_apply {hL : L.IsEven}
    {ι : Type v} [Fintype ι] {A : FiniteQuadraticModule.{w}}
    (f : Isometry A (L.discriminantQuadraticModule hL))
    (x : ι → A) :
    f.coordinatePowerDiscriminant ι x =
      (L.discriminantQuadraticIsometryCoordinatePower ι hL).symm (f.coordinatePower ι x) := by
  rw [coordinatePowerDiscriminant, trans_apply]

end TauCeti
