/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Pi
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Pi
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.Pi

import Mathlib.Algebra.BigOperators.Field

/-!
# Discriminant forms of orthogonal sums of finite families

The dual carrier of the orthogonal sum `⊥ i, L i` of a finite family of integral lattices consists
of the families whose values lie in the dual carriers of the summands.  Passing to quotients
coordinatewise gives the canonical equivalence

```text
A_(⊥ i, L i) ≃ Π i, A_(L i),
```

which sends the class of `x` to the family of classes of its coordinates.  When every summand is
even and nondegenerate, this file proves that it is an isometry from the half-norm discriminant
quadratic module of the orthogonal sum to the orthogonal sum
`TauCeti.FiniteQuadraticModule.pi` of the discriminant quadratic modules of the summands.

Composing with summandwise alphabet isometries `A_i ≅ A_(L i)` gives the interface through which
glue words enter lattice constructions: an isometry from the coordinate module `Π i, A_i` to the
actual discriminant module of the orthogonal sum
(`TauCeti.IntegralLattice.discriminantQuadraticIsometryPiOfIsometry`).

## Main declarations

* `TauCeti.IntegralLattice.dualCarrier_pi`: the dual carrier of an orthogonal sum is the product
  of the dual carriers.
* `TauCeti.IntegralLattice.discriminantGroupPiEquiv`: `A_(⊥ i, L i) ≃ Π i, A_(L i)`.
* `TauCeti.IntegralLattice.discriminantQuadraticIsometryPi`: for even nondegenerate summands, this
  equivalence is an isometry of finite quadratic modules.
* `TauCeti.IntegralLattice.discriminantQuadraticIsometryPiOfIsometry`: the isometry
  `Π i, A_i ≅ A_(⊥ i, L i)` induced by summandwise isometries `A_i ≅ A_(L i)`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §3.
* `TauCeti/LinearAlgebra/IntegralLattice/Discriminant/CoordinatePower.lean`: the coordinate-power
  isometries `A_(L^ι) ≃ (A_L)^ι`. The dual-carrier, quotient and isometry constructions here are
  adapted from the coordinate-power case, generalised from a constant family `L^ι` to arbitrary
  families; that file obtains its isometries as their constant-family case.
-/

public section

namespace TauCeti.IntegralLattice

universe u v

variable {ι : Type v} [Fintype ι] {V : ι → Type u} [∀ i, AddCommGroup (V i)]
  [∀ i, Module ℚ (V i)]
variable (L : ∀ i, IntegralLattice (V i))

/-! ## The dual carrier -/

/-- A family lies in the dual carrier of an orthogonal sum exactly when each of its values lies in
the dual carrier of its summand. -/
theorem mem_dualCarrier_pi_iff (x : ∀ i, V i) :
    x ∈ (pi L).dualCarrier ↔ ∀ i, x i ∈ (L i).dualCarrier := by
  classical
  simp only [dualCarrier, LinearMap.BilinForm.mem_dualSubmodule]
  constructor
  · intro hx i y hy
    rw [← piForm_single_right L x i y, ← pi_form]
    exact hx _ (single_mem_pi_carrier L i hy)
  · intro hx y hy
    rw [pi_form, piForm_apply]
    exact Submodule.sum_mem _ fun i _ ↦ hx i (y i) ((mem_pi_carrier_iff L y).mp hy i)

/-- The dual carrier of an orthogonal sum is the product of the dual carriers. -/
@[simp]
theorem dualCarrier_pi : (pi L).dualCarrier = Submodule.pi Set.univ fun i ↦ (L i).dualCarrier := by
  ext x
  rw [mem_dualCarrier_pi_iff, Submodule.mem_pi]
  simp

/-- The dual carrier of an orthogonal sum is canonically the product of the dual carriers. -/
def piDualCarrierEquiv : (pi L).dualCarrier ≃ₗ[ℤ] ∀ i, (L i).dualCarrier where
  toFun x i := ⟨(x : ∀ i, V i) i, (mem_dualCarrier_pi_iff L x).mp x.2 i⟩
  invFun x := ⟨fun i ↦ x i, (mem_dualCarrier_pi_iff L _).mpr fun i ↦ (x i).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The dual-carrier equivalence of an orthogonal sum reads off the coordinates. -/
@[simp]
theorem coe_piDualCarrierEquiv_apply (x : (pi L).dualCarrier) (i : ι) :
    (piDualCarrierEquiv L x i : V i) = (x : ∀ i, V i) i :=
  (rfl)

/-- The inverse dual-carrier equivalence of an orthogonal sum assembles the coordinates. -/
@[simp]
theorem coe_piDualCarrierEquiv_symm_apply (x : ∀ i, (L i).dualCarrier) :
    ((piDualCarrierEquiv L).symm x : ∀ i, V i) = fun i ↦ (x i : V i) :=
  (rfl)

/-- Under the dual-carrier equivalence, the embedded carrier of an orthogonal sum is the product
of the embedded carriers. -/
theorem map_carrierInDual_pi :
    (pi L).carrierInDual.map (piDualCarrierEquiv L).toLinearMap =
      Submodule.pi Set.univ fun i ↦ (L i).carrierInDual := by
  ext x
  rw [Submodule.mem_map_equiv, Submodule.mem_pi, mem_carrierInDual_iff, mem_pi_carrier_iff]
  simp

/-! ## The discriminant group -/

/-- The discriminant group of an orthogonal sum is canonically the product of the discriminant
groups of its summands. -/
noncomputable def discriminantGroupPiEquiv :
    (pi L).DiscriminantGroup ≃ₗ[ℤ] ∀ i, (L i).DiscriminantGroup := by
  classical
  exact (Submodule.Quotient.equiv (pi L).carrierInDual
      (Submodule.pi Set.univ fun i ↦ (L i).carrierInDual) (piDualCarrierEquiv L)
      (map_carrierInDual_pi L)).trans
    (Submodule.quotientPi fun i ↦ (L i).carrierInDual)

/-- The orthogonal-sum discriminant-group equivalence maps a representative to the family of
classes of its coordinates. -/
@[simp]
theorem discriminantGroupPiEquiv_mk (x : (pi L).dualCarrier) :
    discriminantGroupPiEquiv L (Submodule.Quotient.mk x) =
      fun i ↦ Submodule.Quotient.mk (piDualCarrierEquiv L x i) := by
  rw [discriminantGroupPiEquiv, LinearEquiv.trans_apply, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply]
  rfl

/-- The inverse orthogonal-sum discriminant-group equivalence sends a family of classes to the
class of the assembled representative. -/
@[simp]
theorem discriminantGroupPiEquiv_symm_mk (x : ∀ i, (L i).dualCarrier) :
    (discriminantGroupPiEquiv L).symm (fun i ↦ Submodule.Quotient.mk (x i)) =
      Submodule.Quotient.mk ((piDualCarrierEquiv L).symm x) := by
  rw [LinearEquiv.symm_apply_eq, discriminantGroupPiEquiv_mk, LinearEquiv.apply_symm_apply]

/-! ## The discriminant quadratic module -/

/-- For even nondegenerate summands, the orthogonal-sum equivalence of discriminant groups is an
isometry from the half-norm discriminant quadratic module of `⊥ i, L i` to the orthogonal sum of
the discriminant quadratic modules of the summands. -/
noncomputable def discriminantQuadraticIsometryPi [∀ i, (L i).IsNondegenerate]
    (hL : ∀ i, (L i).IsEven) :
    FiniteQuadraticModule.Isometry ((pi L).discriminantQuadraticModule (isEven_pi hL))
      (FiniteQuadraticModule.pi fun i ↦ (L i).discriminantQuadraticModule (hL i)) where
  toLinearEquiv := discriminantGroupPiEquiv L
  map_app' := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      -- The isometry's carrier is definitionally the discriminant group, but this conversion
      -- is intentionally not part of the public reduction API.
      change (FiniteQuadraticModule.pi fun i ↦ (L i).discriminantQuadraticModule (hL i)).quadratic
          (discriminantGroupPiEquiv L (Submodule.Quotient.mk x)) =
        (pi L).discriminantQuadraticMap _ (Submodule.Quotient.mk x)
      refine (FiniteQuadraticModule.pi_quadratic _ _).trans ?_
      simp only [discriminantGroupPiEquiv_mk, discriminantQuadraticModule_quadratic,
        discriminantQuadraticMap_mk, pi_form, piForm_apply, Finset.sum_div,
        coe_piDualCarrierEquiv_apply]
      exact (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))) _ _).symm

/-- The orthogonal-sum discriminant-quadratic isometry acts through the canonical equivalence of
discriminant groups. -/
@[simp]
theorem discriminantQuadraticIsometryPi_apply [∀ i, (L i).IsNondegenerate]
    (hL : ∀ i, (L i).IsEven) (x : (pi L).DiscriminantGroup) :
    discriminantQuadraticIsometryPi L hL x = discriminantGroupPiEquiv L x :=
  (rfl)

/-- The inverse orthogonal-sum discriminant-quadratic isometry acts through the inverse of the
canonical equivalence of discriminant groups. -/
@[simp]
theorem discriminantQuadraticIsometryPi_symm_apply [∀ i, (L i).IsNondegenerate]
    (hL : ∀ i, (L i).IsEven) (x : ∀ i, (L i).DiscriminantGroup) :
    (discriminantQuadraticIsometryPi L hL).symm x = (discriminantGroupPiEquiv L).symm x :=
  (rfl)

/-! ## Summandwise alphabets -/

/-- Summandwise isometries `A_i ≅ A_(L i)` from finite quadratic alphabets to the discriminant
modules of even nondegenerate lattices induce an isometry from the orthogonal sum `Π i, A_i` to
the discriminant module of the orthogonal sum `⊥ i, L i`. -/
noncomputable def discriminantQuadraticIsometryPiOfIsometry [∀ i, (L i).IsNondegenerate]
    {hL : ∀ i, (L i).IsEven} {A : ι → FiniteQuadraticModule.{u}}
    (f : ∀ i, FiniteQuadraticModule.Isometry (A i) ((L i).discriminantQuadraticModule (hL i))) :
    FiniteQuadraticModule.Isometry (FiniteQuadraticModule.pi A)
      ((pi L).discriminantQuadraticModule (isEven_pi hL)) :=
  (QuadraticMap.IsometryEquiv.pi f).trans (discriminantQuadraticIsometryPi L hL).symm

/-- The isometry induced by summandwise alphabet isometries applies them coordinatewise and then
identifies `Π i, A_(L i)` with `A_(⊥ i, L i)`. -/
@[simp]
theorem discriminantQuadraticIsometryPiOfIsometry_apply [∀ i, (L i).IsNondegenerate]
    {hL : ∀ i, (L i).IsEven} {A : ι → FiniteQuadraticModule.{u}}
    (f : ∀ i, FiniteQuadraticModule.Isometry (A i) ((L i).discriminantQuadraticModule (hL i)))
    (x : ∀ i, A i) :
    discriminantQuadraticIsometryPiOfIsometry L f x =
      (discriminantGroupPiEquiv L).symm fun i ↦ f i (x i) :=
  (rfl)

end TauCeti.IntegralLattice
