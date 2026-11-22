/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Simple submodules over a commutative local ring

Over a commutative local ring `R` with maximal ideal `𝔪`, every simple `R`-module has annihilator
`𝔪`, so every simple submodule of an `R`-module lies in the `𝔪`-torsion submodule `M[𝔪]`
(`IsAtom.le_torsionBySet_maximalIdeal`). No Noetherian hypothesis is needed.

## Main results

* `IsAtom.le_torsionBySet_maximalIdeal`: every simple submodule of a module over a commutative
  local ring is annihilated by the maximal ideal.
-/

public section

open IsLocalRing Submodule

/-- Every simple submodule of a module over a commutative local ring is annihilated by the
maximal ideal. -/
theorem IsAtom.le_torsionBySet_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] {a : Submodule R M} (ha : IsAtom a) :
    a ≤ torsionBySet R M (maximalIdeal R) := by
  have : IsSimpleModule R a := isSimpleModule_iff_isAtom.mpr ha
  have hann : Module.annihilator R a = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal IsSimpleModule.annihilator_isMaximal
  intro x hx
  rw [mem_torsionBySet_iff]
  intro m
  have hm : (m : R) ∈ Module.annihilator R a := hann.symm ▸ m.prop
  exact congrArg Subtype.val (Module.mem_annihilator.mp hm ⟨x, hx⟩)
