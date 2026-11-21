/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra
public import TauCeti.RingTheory.Norm.CharpolyRev
public import Mathlib.RingTheory.Polynomial.Subring
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
finite locally free group schemes whose rank varies over the base.

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
  [CommRing A] [Algebra R A]

private theorem orbitShear_rTensor_includeLeft (z : A ⊗[R] H) :
    HopfAlgebra.tensorShearMulRightBaseChange A (Algebra.TensorProduct.rTensor H
        (includeLeft : A →ₐ[R] A ⊗[R] H) z) =
      (Algebra.TensorProduct.assoc R R R A H H).symm
        ((Coalgebra.comul (R := R) (A := H)).lTensor A z) := by
  induction z with
  | tmul a h => simp [← Algebra.TensorProduct.one_def]
  | add x y hx hy => simp only [map_add, hx, hy]

variable [ComoduleAlgebra R H A]

private theorem orbitShear_coact (a : A) :
    HopfAlgebra.tensorShearMulRightBaseChange A (Algebra.TensorProduct.rTensor H
        (includeLeft : A →ₐ[R] A ⊗[R] H) (Comodule.coact a)) =
      Algebra.TensorProduct.rTensor H (coactAlgHom R H A) (Comodule.coact a) := by
  rw [orbitShear_rTensor_includeLeft, ← Comodule.coassoc_apply]
  -- The algebra associator and the module associator have the same underlying map.
  change (TensorProduct.assoc R A H H).symm
    ((TensorProduct.assoc R A H H) _) = _
  rw [LinearEquiv.symm_apply_apply]
  rw [← toLinearMap_coactAlgHom, AlgHom.rTensor_toLinearMap_apply]

variable [Module.Finite R H] [Module.Projective R H]

/-- The reversed characteristic polynomial of multiplication by the orbit function `coact a`
has coinvariant coefficients, even when the action has stabilizers. -/
theorem coeff_projectiveCharpolyRev_coact_mem_coinvariants (a : A) (i : ℕ) :
    (LinearMap.projectiveCharpolyRev
      (Algebra.lmul A (A ⊗[R] H) (Comodule.coact a))).coeff i ∈ coinvariants R H A := by
  have h :=
    (HopfAlgebra.tensorShearMulRightBaseChange (R := R) (H := H) A).projectiveCharpolyRev_lmul
    (Algebra.TensorProduct.rTensor H (includeLeft : A →ₐ[R] A ⊗[R] H) (Comodule.coact a))
  rw [orbitShear_coact, AlgHom.projectiveCharpolyRev_lmul_rTensor,
    AlgHom.projectiveCharpolyRev_lmul_rTensor] at h
  apply mem_coinvariants.mpr
  simpa only [coeff_map, AlgHom.coe_toRingHom, coactAlgHom_apply, includeLeft_apply] using
    congrArg (fun p ↦ p.coeff i) h

/-- A commutative comodule algebra for a finite projective commutative Hopf algebra is integral
over its coinvariants. This includes non-free finite locally free group-scheme actions. -/
theorem isIntegral_coinvariants : Algebra.IsIntegral (coinvariants R H A) A := by
  refine ⟨fun a ↦ ?_⟩
  set Q := LinearMap.projectiveCharpolyRev
    (Algebra.lmul A (A ⊗[R] H) (Comodule.coact a))
  obtain ⟨n, hn, hQn⟩ := LinearMap.exists_aeval_reflect_projectiveCharpolyRev_eq_zero
    (Algebra.lmul A (A ⊗[R] H) (Comodule.coact a))
  have hroot : aeval (Comodule.coact (R := R) (C := H) a) (Q.reflect n) = 0 := by
    have h := congr($hQn 1)
    rw [Polynomial.aeval_algHom_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', mul_one] at h
    exact h
  have hS : ((Q.reflect n).coeffs : Set A) ⊆ (coinvariants R H A).toSubring := by
    intro c hc
    obtain ⟨i, -, rfl⟩ := mem_coeffs_iff.mp hc
    rw [coeff_reflect]
    exact coeff_projectiveCharpolyRev_coact_mem_coinvariants a _
  have hp : (Q.reflect n).map (coactAlgHom R H A) =
      (Q.reflect n).map (algebraMap A (A ⊗[R] H)) := by
    ext i
    simp only [coeff_map, coeff_reflect]
    simpa only [AlgHom.coe_toRingHom, coactAlgHom_apply,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, Q] using
      mem_coinvariants.mp
        (coeff_projectiveCharpolyRev_coact_mem_coinvariants (R := R) (H := H) a ((revAt n) i))
  have heval : eval a (Q.reflect n) = 0 := by
    apply Comodule.coact_injective (R := R) (C := H)
    rw [map_zero, ← hroot, aeval_def, ← eval_map, ← hp, eval_map]
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, coactAlgHom_apply] using
      (eval₂_at_apply (p := Q.reflect n) (coactAlgHom R H A).toRingHom a).symm
  refine ⟨(Q.reflect n).toSubring _ hS,
    (monic_toSubring _ _ _).mpr (LinearMap.monic_reflect_projectiveCharpolyRev _ hn), ?_⟩
  rw [← eval_map]
  convert heval
  simpa only [Subalgebra.algebraMap_eq, Algebra.algebraMap_self, RingHom.id_comp,
    Subalgebra.toSubring_subtype] using map_toSubring (Q.reflect n) _ hS

end TauCeti.ComoduleAlgebra
