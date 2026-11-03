/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Derivations on quotient algebras

A derivation into a module over `A ⧸ I` descends to `A ⧸ I` precisely when it kills `I`.
`Derivation.liftQuotient` constructs this descent, retaining its value on representatives.
This is useful for presenting modules of differentials by equations.
-/

public section

namespace Derivation

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) {M : Type*} [AddCommGroup M] [Module R M] [Module A M]
  [Module (A ⧸ I) M] [IsScalarTower A (A ⧸ I) M]

/-- Descend a derivation killing `I` to the quotient algebra `A ⧸ I`. -/
def liftQuotient (D : Derivation R A M) (hD : ∀ a ∈ I, D a = 0) :
    Derivation R (A ⧸ I) M where
  __ := ((I.restrictScalars R).liftQ D.toLinearMap (fun x hx ↦
    LinearMap.mem_ker.mpr (hD x ((I.restrictScalars_mem R x).mp hx)))).comp
      (Submodule.Quotient.restrictScalarsEquiv R I).symm.toLinearMap
  map_one_eq_zero' := D.map_one_eq_zero
  leibniz' x y := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      ← Ideal.Quotient.mk_eq_mk, Submodule.Quotient.restrictScalarsEquiv_symm_mk,
      Submodule.liftQ_apply]
    exact (D.leibniz a b).trans (congrArg₂ (· + ·)
      (algebraMap_smul (A ⧸ I) a (D b)).symm (algebraMap_smul (A ⧸ I) b (D a)).symm)

/-- Descent preserves the value on every representative. -/
@[simp]
theorem liftQuotient_mk (D : Derivation R A M) (hD : ∀ a ∈ I, D a = 0) (a : A) :
    D.liftQuotient I hD (Ideal.Quotient.mk I a) = D a :=
  (rfl)

/-- A descended derivation is uniquely determined by its values on representatives. -/
theorem liftQuotient_unique (D : Derivation R A M) (hD : ∀ a ∈ I, D a = 0)
    (E : Derivation R (A ⧸ I) M) (hE : ∀ a, E (Ideal.Quotient.mk I a) = D a) :
    E = D.liftQuotient I hD := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact hE a

end Derivation
