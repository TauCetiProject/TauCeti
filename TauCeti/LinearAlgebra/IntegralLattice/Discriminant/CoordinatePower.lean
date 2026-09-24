/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Pi
public import TauCeti.LinearAlgebra.FiniteBilinearModule.CoordinatePower
public import TauCeti.LinearAlgebra.IntegralLattice.CoordinatePower
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic

/-!
# Discriminant forms of coordinate powers

The dual carrier of the coordinate power `L^ι` consists of the functions all of whose values lie
in the dual carrier of `L`. Passing to quotients coordinatewise gives the canonical equivalence

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

* `TauCeti.IntegralLattice.dualCarrier_coordinatePower`: the dual carrier of `L^ι` is the
  coordinatewise dual carrier.
* `TauCeti.IntegralLattice.discriminantGroupCoordinatePowerEquiv`: `A_(L^ι) ≃ (A_L)^ι`.
* `TauCeti.IntegralLattice.discriminantBilinearIsometryCoordinatePower`: this equivalence is an
  isometry of finite bilinear modules.
* `TauCeti.IntegralLattice.discriminantQuadraticIsometryCoordinatePower`: for even `L`, it is an
  isometry of finite quadratic modules.
* `TauCeti.FiniteQuadraticModule.Isometry.coordinatePowerDiscriminant`: the isometry
  `A^ι ≅ A_(L^ι)` induced by an alphabet isometry `A ≅ A_L`, with the bilinear analogue
  `TauCeti.FiniteBilinearModule.Isometry.coordinatePowerDiscriminant`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §3.
* `TauCeti/LinearAlgebra/IntegralLattice/Discriminant/Operations.lean`: the binary orthogonal-sum
  isometries `A_(L ⊥ M) ≃ A_L × A_M` (`discriminantBilinearIsometryOrthogonalSum` and
  `discriminantQuadraticIsometryOrthogonalSum`). The isometries of this file are their analogue
  for the `ι`-fold orthogonal sum `L^ι`, and their proofs are adapted from there.
-/

public section

namespace TauCeti.IntegralLattice

universe u v w

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable (L : IntegralLattice V) (ι : Type v) [Fintype ι]

/-! ## The dual carrier -/

/-- A function lies in the dual carrier of a coordinate power exactly when each of its values lies
in the dual carrier of the factor. -/
theorem mem_dualCarrier_coordinatePower_iff (x : ι → V) :
    x ∈ (L.coordinatePower ι).dualCarrier ↔ ∀ i, x i ∈ L.dualCarrier := by
  classical
  simp only [dualCarrier, LinearMap.BilinForm.mem_dualSubmodule]
  constructor
  · intro hx i y hy
    rw [← coordinatePowerForm_single_right L ι x i y,
      ← coordinatePowerForm_apply, ← coordinatePower_form]
    exact hx _ (L.single_mem_coordinatePower_carrier ι i hy)
  · intro hx y hy
    rw [coordinatePower_form, coordinatePowerForm_apply]
    exact Submodule.sum_mem _ fun i _ ↦
      hx i (y i) ((L.mem_coordinatePower_carrier_iff ι y).mp hy i)

/-- The dual carrier of a coordinate power is the coordinatewise dual carrier. -/
@[simp]
theorem dualCarrier_coordinatePower :
    (L.coordinatePower ι).dualCarrier = Submodule.pi Set.univ fun _ ↦ L.dualCarrier := by
  ext x
  rw [L.mem_dualCarrier_coordinatePower_iff ι x, Submodule.mem_pi]
  simp

/-- The dual carrier of a coordinate power is canonically the function space on the dual carrier
of the factor. -/
def coordinatePowerDualCarrierEquiv :
    (L.coordinatePower ι).dualCarrier ≃ₗ[ℤ] (ι → L.dualCarrier) where
  toFun x i := ⟨(x : ι → V) i, (L.mem_dualCarrier_coordinatePower_iff ι x).mp x.2 i⟩
  invFun x := ⟨fun i ↦ x i, (L.mem_dualCarrier_coordinatePower_iff ι _).mpr fun i ↦ (x i).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The dual-carrier equivalence of a coordinate power reads off the coordinates. -/
@[simp]
theorem coe_coordinatePowerDualCarrierEquiv_apply (x : (L.coordinatePower ι).dualCarrier)
    (i : ι) : (L.coordinatePowerDualCarrierEquiv ι x i : V) = (x : ι → V) i :=
  (rfl)

/-- The inverse dual-carrier equivalence of a coordinate power assembles the coordinates. -/
@[simp]
theorem coe_coordinatePowerDualCarrierEquiv_symm_apply (x : ι → L.dualCarrier) :
    ((L.coordinatePowerDualCarrierEquiv ι).symm x : ι → V) = fun i ↦ (x i : V) :=
  (rfl)

/-- Under the dual-carrier equivalence, the embedded carrier of a coordinate power is the
coordinatewise embedded carrier. -/
theorem map_carrierInDual_coordinatePower :
    (L.coordinatePower ι).carrierInDual.map (L.coordinatePowerDualCarrierEquiv ι).toLinearMap =
      Submodule.pi Set.univ fun _ ↦ L.carrierInDual := by
  ext x
  rw [Submodule.mem_map_equiv, Submodule.mem_pi, mem_carrierInDual_iff,
    mem_coordinatePower_carrier_iff]
  simp

/-! ## The discriminant group -/

/-- The discriminant group of a coordinate power is canonically the function space on the
discriminant group of the factor. -/
noncomputable def discriminantGroupCoordinatePowerEquiv :
    (L.coordinatePower ι).DiscriminantGroup ≃ₗ[ℤ] (ι → L.DiscriminantGroup) := by
  classical
  exact (Submodule.Quotient.equiv (L.coordinatePower ι).carrierInDual
      (Submodule.pi Set.univ fun _ ↦ L.carrierInDual) (L.coordinatePowerDualCarrierEquiv ι)
      (L.map_carrierInDual_coordinatePower ι)).trans
    (Submodule.quotientPi fun _ ↦ L.carrierInDual)

/-- The coordinate-power discriminant-group equivalence maps a representative to the family of
classes of its coordinates. -/
@[simp]
theorem discriminantGroupCoordinatePowerEquiv_mk (x : (L.coordinatePower ι).dualCarrier) :
    L.discriminantGroupCoordinatePowerEquiv ι (Submodule.Quotient.mk x) =
      fun i ↦ Submodule.Quotient.mk (L.coordinatePowerDualCarrierEquiv ι x i) := by
  rw [discriminantGroupCoordinatePowerEquiv, LinearEquiv.trans_apply,
    Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  rfl

/-- The inverse coordinate-power discriminant-group equivalence sends a family of classes to the
class of the assembled representative. -/
@[simp]
theorem discriminantGroupCoordinatePowerEquiv_symm_mk (x : ι → L.dualCarrier) :
    (L.discriminantGroupCoordinatePowerEquiv ι).symm (fun i ↦ Submodule.Quotient.mk (x i)) =
      Submodule.Quotient.mk ((L.coordinatePowerDualCarrierEquiv ι).symm x) := by
  rw [LinearEquiv.symm_apply_eq, discriminantGroupCoordinatePowerEquiv_mk,
    LinearEquiv.apply_symm_apply]

/-! ## The discriminant bilinear module -/

/-- The coordinate-power equivalence of discriminant groups is an isometry from the discriminant
pairing of `L^ι` to the coordinate power of the discriminant pairing of `L`. -/
noncomputable def discriminantBilinearIsometryCoordinatePower [L.IsNondegenerate] :
    FiniteBilinearModule.Isometry (L.coordinatePower ι).discriminantBilinearModule
      (L.discriminantBilinearModule.coordinatePower ι) where
  toAddEquiv := (L.discriminantGroupCoordinatePowerEquiv ι).toAddEquiv
  map_pairing' := by
    intro x y
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        -- The isometry's carrier is definitionally the discriminant group, but this conversion
        -- is intentionally not part of the public reduction API.
        change ∑ i, L.discriminantPairing
            (L.discriminantGroupCoordinatePowerEquiv ι (Submodule.Quotient.mk x) i)
            (L.discriminantGroupCoordinatePowerEquiv ι (Submodule.Quotient.mk y) i) =
          (L.coordinatePower ι).discriminantPairing
            (Submodule.Quotient.mk x) (Submodule.Quotient.mk y)
        simp only [discriminantGroupCoordinatePowerEquiv_mk, discriminantPairing_mk,
          coordinatePower_form, coordinatePowerForm_apply,
          coe_coordinatePowerDualCarrierEquiv_apply]
        exact (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))) _ _).symm

/-- The underlying additive equivalence of the coordinate-power discriminant-bilinear isometry is
the canonical coordinate-power equivalence of discriminant groups. -/
@[simp]
theorem discriminantBilinearIsometryCoordinatePower_toAddEquiv [L.IsNondegenerate] :
    (L.discriminantBilinearIsometryCoordinatePower ι).toAddEquiv =
      (L.discriminantGroupCoordinatePowerEquiv ι).toAddEquiv :=
  (rfl)

/-- The coordinate-power discriminant-bilinear isometry acts through the canonical
coordinate-power equivalence of discriminant groups. -/
@[simp]
theorem discriminantBilinearIsometryCoordinatePower_apply [L.IsNondegenerate]
    (x : (L.coordinatePower ι).DiscriminantGroup) :
    L.discriminantBilinearIsometryCoordinatePower ι x =
      L.discriminantGroupCoordinatePowerEquiv ι x :=
  (rfl)

/-- The coordinate-power discriminant-bilinear isometry maps a representative to the family of
classes of its coordinates. -/
theorem discriminantBilinearIsometryCoordinatePower_mk [L.IsNondegenerate]
    (x : (L.coordinatePower ι).dualCarrier) :
    L.discriminantBilinearIsometryCoordinatePower ι (Submodule.Quotient.mk x) =
      fun i ↦ Submodule.Quotient.mk (L.coordinatePowerDualCarrierEquiv ι x i) :=
  L.discriminantGroupCoordinatePowerEquiv_mk ι x

/-! ## The discriminant quadratic module -/

/-- For an even lattice `L`, the coordinate-power equivalence of discriminant groups is an
isometry from the half-norm discriminant quadratic module of `L^ι` to the coordinate power of the
discriminant quadratic module of `L`. -/
noncomputable def discriminantQuadraticIsometryCoordinatePower [L.IsNondegenerate]
    (hL : L.IsEven) :
    FiniteQuadraticModule.Isometry
      ((L.coordinatePower ι).discriminantQuadraticModule (hL.coordinatePower ι))
      ((L.discriminantQuadraticModule hL).coordinatePower ι) where
  toLinearEquiv := L.discriminantGroupCoordinatePowerEquiv ι
  map_app' := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      -- The isometry's carrier is definitionally the discriminant group, but this conversion
      -- is intentionally not part of the public reduction API.
      change ((L.discriminantQuadraticModule hL).coordinatePower ι).quadratic
          (L.discriminantGroupCoordinatePowerEquiv ι (Submodule.Quotient.mk x)) =
        (L.coordinatePower ι).discriminantQuadraticMap _ (Submodule.Quotient.mk x)
      refine (FiniteQuadraticModule.coordinatePower_quadratic _ ι _).trans ?_
      simp only [discriminantGroupCoordinatePowerEquiv_mk, discriminantQuadraticModule_quadratic,
        discriminantQuadraticMap_mk, coordinatePower_form, coordinatePowerForm_apply,
        Finset.sum_div, coe_coordinatePowerDualCarrierEquiv_apply]
      exact (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))) _ _).symm

/-- The underlying additive equivalence of the coordinate-power discriminant-quadratic isometry is
the canonical coordinate-power equivalence of discriminant groups. -/
@[simp]
theorem discriminantQuadraticIsometryCoordinatePower_toAddEquiv [L.IsNondegenerate]
    (hL : L.IsEven) :
    (L.discriminantQuadraticIsometryCoordinatePower ι hL).toAddEquiv =
      (L.discriminantGroupCoordinatePowerEquiv ι).toAddEquiv :=
  (rfl)

/-- The coordinate-power discriminant-quadratic isometry acts through the canonical
coordinate-power equivalence of discriminant groups. -/
@[simp]
theorem discriminantQuadraticIsometryCoordinatePower_apply [L.IsNondegenerate] (hL : L.IsEven)
    (x : (L.coordinatePower ι).DiscriminantGroup) :
    L.discriminantQuadraticIsometryCoordinatePower ι hL x =
      L.discriminantGroupCoordinatePowerEquiv ι x :=
  (rfl)

/-- The coordinate-power discriminant-quadratic isometry maps a representative to the family of
classes of its coordinates. -/
theorem discriminantQuadraticIsometryCoordinatePower_mk [L.IsNondegenerate] (hL : L.IsEven)
    (x : (L.coordinatePower ι).dualCarrier) :
    L.discriminantQuadraticIsometryCoordinatePower ι hL (Submodule.Quotient.mk x) =
      fun i ↦ Submodule.Quotient.mk (L.coordinatePowerDualCarrierEquiv ι x i) :=
  L.discriminantGroupCoordinatePowerEquiv_mk ι x

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
