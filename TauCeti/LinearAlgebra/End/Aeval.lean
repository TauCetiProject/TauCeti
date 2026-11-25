/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Polynomials in intertwined endomorphisms

A (semi)linear map `f` intertwining two endomorphisms `g` and `g₂` intertwines every polynomial
in them: polynomial evaluation at `g₂` after `f` agrees with `f` after evaluation at `g`, with the
coefficients transported along the ring homomorphism of `f`. This extends Mathlib's
`Module.End.commute_pow_left_of_commute` from powers to polynomials. The linear case, where no
transport of coefficients is needed, is `Module.End.aeval_comp_of_comp_eq`.

Consequently a linear map intertwining two endomorphisms with coprime minimal polynomials is zero
(`Module.End.eq_zero_of_comp_eq_of_isCoprime_minpoly`): the minimal polynomial of the source
endomorphism kills it, while evaluated at the target endomorphism it is invertible.

Polynomial identities in an endomorphism are local on `Spec R`: a polynomial kills `f` once its
image kills the base change of `f` to the localization at every maximal ideal
(`Module.End.aeval_eq_zero_of_forall_baseChange_localization`).
-/

public section

open Polynomial

namespace Module.End

section CommSemiring

variable {R M M₂ : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂]

/-- A semilinear map intertwining two endomorphisms intertwines every polynomial in them, with
coefficients transported along the ring homomorphism. -/
theorem aeval_map_comp_of_comp_eq {R₂ : Type*} [CommSemiring R₂] [Module R₂ M₂] {σ : R →+* R₂}
    {f : M →ₛₗ[σ] M₂} {g : End R M} {g₂ : End R₂ M₂} (h : g₂.comp f = f.comp g) (p : R[X]) :
    (aeval g₂ (p.map σ)).comp f = f.comp (aeval g p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.map_add, LinearMap.add_comp, LinearMap.comp_add, hp, hq]
  | monomial n a =>
    ext x
    have hn := LinearMap.congr_fun (commute_pow_left_of_commute h n) x
    simp only [LinearMap.comp_apply] at hn
    simp [aeval_monomial, Algebra.algebraMap_eq_smul_one, hn]

/-- A linear map intertwining two endomorphisms intertwines every polynomial in them. -/
theorem aeval_comp_of_comp_eq [Module R M₂] {f : M →ₗ[R] M₂} {g : End R M} {g₂ : End R M₂}
    (h : g₂.comp f = f.comp g) (p : R[X]) : (aeval g₂ p).comp f = f.comp (aeval g p) := by
  simpa using aeval_map_comp_of_comp_eq h p

open scoped TensorProduct in
/-- **Local-to-global for polynomial identities.** A polynomial `p` kills `f` once its image kills
the base change of `f` to the localization at every maximal ideal. -/
theorem aeval_eq_zero_of_forall_baseChange_localization (f : End R M) (p : R[X])
    (h : ∀ (P : Ideal R) [P.IsMaximal], aeval (f.baseChange (Localization.AtPrime P))
      (p.map (algebraMap R (Localization.AtPrime P))) = 0) :
    aeval f p = 0 := by
  ext x
  refine Module.eq_zero_of_localization_maximal (fun P _ ↦ Localization.AtPrime P ⊗[R] M)
    (fun P _ ↦ TensorProduct.mk R (Localization.AtPrime P) M 1) _ fun P _ ↦ ?_
  let A := Localization.AtPrime P
  have hbase : (aeval f p).baseChange A = 0 := by
    rw [show (aeval f p).baseChange A = aeval (f.baseChange A) p from
        (aeval_algHom_apply (baseChangeHom R A M) f p).symm,
      aeval_eq_aeval_map (IsScalarTower.algebraMap_eq R A (End A (A ⊗[R] M))).symm]
    exact h P
  rw [TensorProduct.mk_apply, ← LinearMap.baseChange_tmul, hbase, LinearMap.zero_apply]

end CommSemiring

section CommRing

variable {R M M₂ : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M₂]
  [Module R M₂]

/-- A linear map intertwining two endomorphisms with coprime minimal polynomials is zero. -/
theorem eq_zero_of_comp_eq_of_isCoprime_minpoly {f : M →ₗ[R] M₂} {g : End R M} {g₂ : End R M₂}
    (h : g₂.comp f = f.comp g) (hc : IsCoprime (minpoly R g) (minpoly R g₂)) : f = 0 := by
  obtain ⟨u, v, huv⟩ := hc
  have hf : (aeval g₂ (minpoly R g)).comp f = 0 := by
    simpa using aeval_map_comp_of_comp_eq h (minpoly R g)
  have h₁ : aeval g₂ u * aeval g₂ (minpoly R g) = 1 := by
    simpa using congrArg (aeval g₂) huv
  calc f = (aeval g₂ u * aeval g₂ (minpoly R g)).comp f := by
        rw [h₁, Module.End.one_eq_id, LinearMap.id_comp]
    _ = 0 := by rw [Module.End.mul_eq_comp, LinearMap.comp_assoc, hf, LinearMap.comp_zero]

end CommRing

end Module.End
