/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Basic
public import TauCeti.Algebra.Module.ProjectiveCover.Multiplicity

/-!
# Ext-Euler characteristics of projective covers against simple modules

Let `P ⟶ S` be a projective cover of a simple module over an algebra `A` over a field `k`. Since
`P` is projective, its Ext-Euler characteristic against a simple module `T` is
`χ(P, T) = dim_k Hom_A(P, T)`. This is the dimension of the division algebra `End_A(S)` when
`T ≅ S`, and `0` otherwise.

## Main results

* `TauCeti.IsProjectiveCover.extEuler_eq_finrank_end`: `χ(P, T) = dim_k End_A(S)` if `T ≅ S`.
* `TauCeti.IsProjectiveCover.extEuler_eq_zero`: `χ(P, T) = 0` if `T` is not isomorphic to `S`.
-/

public section

namespace TauCeti

open CategoryTheory
open scoped ModuleCat

universe u

variable {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A]
variable {P T : ModuleCat.{u} A} {S : Type*} [AddCommGroup S] [Module A S] {f : P →ₗ[A] S}

/-- **The diagonal Ext-Euler value.** For a projective cover `P ⟶ S` of a simple module and a
simple module `T ≅ S`, `χ(P, T)` is the dimension of the division algebra `End_A(S)`. -/
theorem IsProjectiveCover.extEuler_eq_finrank_end [Module k S] [IsScalarTower k A S]
    (hf : IsProjectiveCover f) [IsSimpleModule A T] (e : T ≃ₗ[A] S)
    (h : IsEulerAdmissible.{u} k P T) :
    extEuler.{u} k h = Module.finrank k (Module.End A S) := by
  have : Module.Projective A P := hf.projective
  rw [extEuler_projective k h, (ModuleCat.homLinearEquiv (S := k)).finrank_eq,
    hf.finrank_linearMap_eq_finrank_end e]

/-- **The off-diagonal Ext-Euler value.** For a projective cover `P ⟶ S` of a simple module and a
simple module `T` not isomorphic to `S`, `χ(P, T) = 0`. -/
theorem IsProjectiveCover.extEuler_eq_zero [IsSimpleModule A S] (hf : IsProjectiveCover f)
    [IsSimpleModule A T] (he : IsEmpty (T ≃ₗ[A] S)) (h : IsEulerAdmissible.{u} k P T) :
    extEuler.{u} k h = 0 := by
  have : Module.Projective A P := hf.projective
  rw [extEuler_projective k h, (ModuleCat.homLinearEquiv (S := k)).finrank_eq,
    hf.finrank_linearMap_eq_zero he, Nat.cast_zero]

end TauCeti
