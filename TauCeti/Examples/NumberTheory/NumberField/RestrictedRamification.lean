/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.RestrictedRamification.Basic
import TauCeti.NumberTheory.NumberField.ExistsRamified

/-!
# Checks for the maximal extension unramified outside `S`

* For `K = ℚ` and `S = ∅` (no finite places allowed to ramify), `K_S = ℚ`: every number field of
  degree `> 1` has `|disc| > 2`, so some prime ramifies in it (Minkowski, through Mathlib's
  `NumberField.exists_not_isUnramifiedAt_int` in its relative form
  `NumberField.finrank_eq_one_of_finrank_eq_one_of_isUnramifiedIn`). A definition of `K_S` that
  ignored ramification would give all of `Ω`.
* For `S` the set of all finite places, `K_S = Ω` for `Ω` algebraic over `K`
  (`TauCeti.RestrictedRamification.maxUnramifiedOutside_univ`).
-/

public section

open IntermediateField

open scoped NumberField

namespace TauCeti.Examples.RestrictedRamification

open TauCeti.RestrictedRamification

variable (Ω : Type*) [Field Ω] [Algebra ℚ Ω]

/-- **`ℚ` has no nontrivial extension unramified at every finite prime**: `ℚ_∅ = ℚ`. -/
theorem maxUnramifiedOutside_rat_empty : maxUnramifiedOutside ℚ Ω ∅ = ⊥ := by
  refine eq_bot_iff.2 (maxUnramifiedOutside_le fun L hfin hL ↦ ?_)
  -- the `ℚ`-algebra structure of `L` as an intermediate field, as in `maxUnramifiedOutside`
  let : Algebra ℚ L := L.algebra'
  have : NumberField L := NumberField.of_module_finite ℚ L
  -- Minkowski over the degree-one base `ℚ`, applicable as no prime of `𝓞 ℚ` lies outside `∅`
  have h := NumberField.finrank_eq_one_of_finrank_eq_one_of_isUnramifiedIn (F := ℚ) (M := L)
    (Module.finrank_self ℚ) fun q hq h0 ↦ hL ⟨q, hq, h0⟩ (Set.notMem_empty _)
  -- `h` uses the module structure of `L.algebra'`, `finrank_eq_one_iff` that of `L.module'`;
  -- the only remaining goal is that these two `ℚ`-module structures agree, which holds as
  -- `Module ℚ L` is a subsingleton
  refine (IntermediateField.finrank_eq_one_iff.1 ?_).le
  convert h
  exact Subsingleton.elim _ _

/-- For `S` the set of all finite places of `ℚ`, `K_S` is all of an algebraic closure. -/
example : maxUnramifiedOutside ℚ (AlgebraicClosure ℚ) Set.univ = ⊤ :=
  maxUnramifiedOutside_univ

end TauCeti.Examples.RestrictedRamification
