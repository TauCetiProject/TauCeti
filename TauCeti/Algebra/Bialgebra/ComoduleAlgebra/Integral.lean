/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra
public import TauCeti.LinearAlgebra.Charpoly.Projective
import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Integrality over the coinvariants of a finite locally free group action

If a commutative Hopf algebra `H` is finite projective over `R`, every commutative
`H`-comodule algebra `A` is integral over its coinvariants. No freeness of the action,
reducedness, finite type, or invertibility of the group order is required.

For `a : A`, multiplication by its coaction on `A ⊗[R] H` has a reversed characteristic
polynomial with coinvariant coefficients. The Hopf tensor shear identifies its two pullbacks
along the coaction and the inclusion of `A`. Cayley–Hamilton then gives a monic polynomial
over the coinvariants annihilating `a`. The reversed characteristic polynomial accommodates
finite locally free group schemes whose rank varies over the base. The Cayley–Hamilton descent
is shared with finite locally free equivalence relations through
`RingHom.isIntegral_of_coeff_projectiveCharpolyRev_mem_eqLocus`.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §4.
* The Stacks Project, Tags 03BH and 03BJ, for the characteristic-polynomial argument for finite
  locally free groupoids. The proof here uses the action groupoid without assuming freeness.
* Formal precursor: `RingHom.IsSpecEquivRel.coeff_projectiveCharpolyRev_mem_eqLocus` and
  `RingHom.IsSpecEquivRel.isIntegral`.
-/

public section

open Polynomial TensorProduct Algebra.TensorProduct

namespace TauCeti.ComoduleAlgebra

variable {R H A : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [CommRing A] [Algebra R A] [ComoduleAlgebra R H A]

private theorem orbitShear_coact (a : A) :
    HopfAlgebra.tensorShearMulRightBaseChange A (Algebra.TensorProduct.rTensor H
        (includeLeft : A →ₐ[R] A ⊗[R] H) (Comodule.coact a)) =
      Algebra.TensorProduct.rTensor H (coactAlgHom R H A) (Comodule.coact a) := by
  rw [HopfAlgebra.tensorShearMulRightBaseChange_rTensor_includeLeft, ← Comodule.coassoc_apply,
    ← AlgEquiv.toLinearEquiv_apply, AlgEquiv.toLinearEquiv_symm,
    Algebra.TensorProduct.assoc_toLinearEquiv, TensorProduct.AlgebraTensorModule.assoc_eq,
    LinearEquiv.symm_apply_apply, ← toLinearMap_coactAlgHom, AlgHom.rTensor_toLinearMap_apply]

variable [Module.Finite R H] [Module.Projective R H]

/-- The reversed characteristic polynomial of multiplication by the orbit function `coact a`
on `A ⊗[R] H` has coinvariant coefficients, even when the action has stabilizers. -/
theorem coeff_projectiveCharpolyRev_lmul_coact_mem_coinvariants (a : A) (i : ℕ) :
    (LinearMap.projectiveCharpolyRev
      (Algebra.lmul A (A ⊗[R] H) (Comodule.coact a))).coeff i ∈ coinvariants R H A := by
  have h :=
    (HopfAlgebra.tensorShearMulRightBaseChange (R := R) (H := H) A).projectiveCharpolyRev_lmul
    (Algebra.TensorProduct.rTensor H (includeLeft : A →ₐ[R] A ⊗[R] H) (Comodule.coact a))
  rw [orbitShear_coact, Algebra.coe_lmul_eq_mul, AlgHom.projectiveCharpolyRev_lmul_rTensor,
    AlgHom.projectiveCharpolyRev_lmul_rTensor, ← Algebra.coe_lmul_eq_mul] at h
  apply mem_coinvariants.mpr
  simpa only [coeff_map, AlgHom.coe_toRingHom, coactAlgHom_apply, includeLeft_apply] using
    congrArg (fun p ↦ p.coeff i) h

/-- A commutative comodule algebra for a finite projective commutative Hopf algebra is integral
over its coinvariants. This includes non-free finite locally free group-scheme actions. -/
theorem isIntegral_coinvariants : Algebra.IsIntegral (coinvariants R H A) A := by
  have hS : (coinvariants R H A).toSubring =
      (algebraMap A (A ⊗[R] H)).eqLocus (coactAlgHom R H A).toRingHom :=
    SetLike.coe_injective (eqLocus_coactAlgHom ..).symm
  have hinj : Function.Injective (coactAlgHom R H A).toRingHom := fun x y hxy ↦
    Comodule.coact_injective (R := R) (C := H) (by simpa using hxy)
  refine ⟨fun a ↦ ?_⟩
  have ha := (coactAlgHom R H A).toRingHom.isIntegral_of_coeff_projectiveCharpolyRev_mem_eqLocus
    hinj a fun i ↦ by
      rw [← hS, Subalgebra.mem_toSubring]
      simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, coactAlgHom_apply] using
        coeff_projectiveCharpolyRev_lmul_coact_mem_coinvariants (R := R) (H := H) a i
  rw [← hS] at ha
  exact ha

end TauCeti.ComoduleAlgebra
