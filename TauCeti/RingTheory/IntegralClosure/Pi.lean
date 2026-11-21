/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Noetherian.Basic
import TauCeti.RingTheory.Ideal.MinimalPrime.Basic

/-!
# Integral closure in a finite product

An element of a finite product of algebras is integral exactly when each coordinate is
integral. Consequently, integral closure commutes with finite products. This comparison
allows normalization and étaleness questions for finite products of fields to be checked
on the individual field factors.

In particular, for a reduced algebra `B` with finitely many minimal primes over a Noetherian ring
`P`, finiteness of `integralClosure P B` reduces to finiteness of `integralClosure P Q.ResidueField`
for each minimal prime `Q` of `B`
(`TauCeti.finite_integralClosure_of_isReduced_of_forall_minimalPrimes`).

The finiteness assumption is essential: the integral equations for infinitely many
coordinates need not have a common degree or common coefficients.
-/

public section

open Polynomial

namespace TauCeti

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]

/-- A tuple in a finite product of algebras is integral if and only if every coordinate is
integral. A common monic equation is the product of the coordinate equations. -/
@[simp]
theorem isIntegral_pi_iff {B : ι → Type*} [∀ i, Ring (B i)] [∀ i, Algebra R (B i)]
    {x : ∀ i, B i} : IsIntegral R x ↔ ∀ i, IsIntegral R (x i) := by
  classical
  let := Fintype.ofFinite ι
  refine ⟨fun hx i ↦ hx.map (Pi.evalAlgHom R B i), fun hx ↦ ?_⟩
  choose p hp hroot using hx
  refine ⟨∏ i, p i, monic_prod_of_monic _ _ (fun i _ ↦ hp i), ?_⟩
  ext i
  exact (aeval_algHom_apply (Pi.evalAlgHom R B i) x _).symm.trans (by
    rw [Fintype.prod_eq_mul_prod_compl i, aeval_mul]
    exact mul_eq_zero_of_left (hroot i) _)

variable (R) (B : ι → Type*) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]

/-- Integral closure commutes with finite products, by taking coordinates of integral tuples. -/
def integralClosurePiAlgEquiv :
    integralClosure R (∀ i, B i) ≃ₐ[R] ∀ i, integralClosure R (B i) where
  toFun x i := ⟨x.val i, (isIntegral_pi_iff.mp x.property) i⟩
  invFun x := ⟨fun i ↦ (x i).val, isIntegral_pi_iff.mpr fun i ↦ (x i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The product comparison takes an integral tuple to its coordinates. -/
@[simp]
theorem integralClosurePiAlgEquiv_apply (x : integralClosure R (∀ i, B i)) (i : ι) :
    (integralClosurePiAlgEquiv R B x i : B i) = x.val i := (rfl)

/-- The inverse product comparison assembles the coordinates into an integral tuple. -/
@[simp]
theorem integralClosurePiAlgEquiv_symm_apply (x : ∀ i, integralClosure R (B i)) (i : ι) :
    ((integralClosurePiAlgEquiv R B).symm x : ∀ i, B i) i = x i := (rfl)

/-- Let `P` be a Noetherian ring and `B` a reduced `P`-algebra with finitely many minimal primes.
If the integral closure of `P` in the residue field `Q.ResidueField` of every minimal prime `Q` of
`B` is a finite `P`-module, then `integralClosure P B` is a finite `P`-module. -/
theorem finite_integralClosure_of_isReduced_of_forall_minimalPrimes {P B : Type*} [CommRing P]
    [IsNoetherianRing P] [CommRing B] [Algebra P B] [IsReduced B] [Finite (minimalPrimes B)]
    (hfin : ∀ (Q : Ideal B) (hQ : Q ∈ minimalPrimes B), haveI := hQ.1.1;
      Module.Finite P (integralClosure P Q.ResidueField)) :
    Module.Finite P (integralClosure P B) := by
  let F (i : minimalPrimes B) : Type _ := letI := i.property.1.1; i.val.ResidueField
  let (i : minimalPrimes B) : Field (F i) := by letI := i.property.1.1; infer_instance
  let (i : minimalPrimes B) : Algebra B (F i) := by letI := i.property.1.1; infer_instance
  let (i : minimalPrimes B) : Algebra P (F i) := by letI := i.property.1.1; infer_instance
  have (i : minimalPrimes B) : IsScalarTower P B (F i) := by have := i.property.1.1; infer_instance
  have (i : minimalPrimes B) : Module.Finite P (integralClosure P (F i)) := hfin i.val i.property
  have : Module.Finite P (integralClosure P (∀ i : minimalPrimes B, F i)) :=
    Module.Finite.equiv (integralClosurePiAlgEquiv P F).toLinearEquiv.symm
  let ψ : B →ₐ[P] ∀ i : minimalPrimes B, F i :=
    AlgHom.pi fun i ↦ IsScalarTower.toAlgHom P B (F i)
  have hψ_inj : Function.Injective ψ := by
    let φ₁ : B →+* ∀ i : minimalPrimes B, B ⧸ i.val :=
      RingHom.pi fun i ↦ Ideal.Quotient.mk i.val
    let φ₂ : (∀ i : minimalPrimes B, B ⧸ i.val) → ∀ i : minimalPrimes B, F i :=
      fun g i ↦ algebraMap (B ⧸ i.val) (F i) (g i)
    have hcomp : (ψ : B → ∀ i : minimalPrimes B, F i) = φ₂ ∘ φ₁ := by
      ext x i
      exact IsScalarTower.algebraMap_apply B (B ⧸ i.val) (F i) x
    have hφ₂ : Function.Injective φ₂ := fun u v huv ↦ funext fun i ↦ by
      have := i.property.1.1
      exact IsFractionRing.injective (B ⧸ i.val) (F i) (congrFun huv i)
    exact hcomp ▸ hφ₂.comp (Ideal.injective_pi_quotient_mk_minimalPrimes B)
  exact Module.Finite.of_injective ψ.mapIntegralClosure.toLinearMap
    fun _ _ h ↦ Subtype.ext (hψ_inj (congrArg Subtype.val h))

end TauCeti
