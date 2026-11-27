/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinIdeal.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import TauCeti.RingTheory.Ideal.TensorProduct

/-!
# Base change of Eisenstein ideals

Tensoring the cuspidal Hecke algebra with a new coefficient algebra carries the operator
differences to the differences for the transported Eisenstein eigenvalues. For flat
coefficient extensions, including localizations, the coefficient Eisenstein ideal of the
transported system is the extension of the original coefficient Eisenstein ideal.
-/

public section

open scoped TensorProduct

namespace TauCeti

open Algebra.TensorProduct (includeRight)

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
  {ι : Type*} (t : ι → T) (a : ι → R)
  (S : Type*) [CommRing S] [Algebra R S]

/-- Arbitrary scalar extension of the cuspidal algebra extends its Eisenstein ideal. -/
theorem map_eisensteinIdeal_includeRight :
    (eisensteinIdeal t a).map (includeRight : T →ₐ[R] S ⊗[R] T) =
      eisensteinIdeal ((includeRight : T →ₐ[R] S ⊗[R] T) ∘ t) (algebraMap R S ∘ a) := by
  apply map_eisensteinIdeal
  ext r
  exact ((includeRight : T →ₐ[R] S ⊗[R] T).commutes r).trans
    (IsScalarTower.algebraMap_apply R S (S ⊗[R] T) r)

/-- The coefficient Eisenstein ideal commutes with flat scalar extension of the cuspidal
algebra and its prescribed eigenvalues. -/
theorem map_coefficientEisensteinIdeal_eq_of_flat [Module.Flat R S] :
    (coefficientEisensteinIdeal t a).map (algebraMap R S) =
      coefficientEisensteinIdeal ((includeRight : T →ₐ[R] S ⊗[R] T) ∘ t)
        (algebraMap R S ∘ a) := by
  rw [coefficientEisensteinIdeal_eq_comap, coefficientEisensteinIdeal_eq_comap,
    Ideal.map_comap_algebraMap_eq_of_flat, map_eisensteinIdeal_includeRight]
  ext s
  simp only [Ideal.mem_comap, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]

end TauCeti
