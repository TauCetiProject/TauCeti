/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Length
public import TauCeti.CategoryTheory.Abelian.LengthFunction
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The length of modules is a length function

The length `Module.length A M` of modules is additive on short exact sequences and vanishes exactly
on the zero modules, so it is a length function on the abelian category `ModuleCat A`
(`ModuleCat.isLengthFunction_length`). Through it, the statements about abelian categories with a
length function, such as the Harada–Sai lemma (`TauCeti.map_eq_zero_of_length_le`), apply to
modules.

## Main results

* `ModuleCat.isLengthFunction_length`: `M ↦ Module.length A M` is a length function on
  `ModuleCat A`.
-/

public section

open CategoryTheory

universe v u

/-- **The length of modules is a length function** on `ModuleCat A`: it is additive on short exact
sequences (`Module.length_eq_add_of_exact`) and vanishes exactly on the zero modules. -/
theorem ModuleCat.isLengthFunction_length (A : Type u) [Ring A] :
    TauCeti.IsLengthFunction (fun M : ModuleCat.{v} A ↦ Module.length A M) where
  add S hS := Module.length_eq_add_of_exact _ _ hS.moduleCat_injective_f hS.moduleCat_surjective_g
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
  eq_zero_iff M := by
    rw [Module.length_eq_zero_iff, ModuleCat.isZero_iff_subsingleton]
