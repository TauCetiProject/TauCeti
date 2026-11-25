/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.Padics.SpecialLinearGroup.FirstCongruence
import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Basic

/-!
# Regression examples: the first congruence subgroup of `SL₂(ℤ_p)`

These examples check from a downstream module that

* the index of `G₁` in `SL₂(ℤ_p)` is `|SL₂(𝔽₃)| = 24` for `p = 3` and `|SL₂(𝔽₅)| = 120` for
  `p = 5`, and that of `G₁²` in `SL₂(ℤ₃)²` is `24² = 576`;
* `G₁` and `G₁^m` are found to be compact topological groups by instance search, so their Iwasawa
  algebras `ℤ_p[[G₁]]` and `ℤ_p[[G₁^m]]` are available;
* the identity lies in `G₁`, and `-1` does for `p = 2` but not for `p = 3`.
-/

open TauCeti

example : (firstCongruenceSubgroup (Fin 2) 3).index = 24 :=
  index_firstCongruenceSubgroup_fin_two 3

-- `5` is prime (`Nat.prime_five`), but `Fact (Nat.Prime 5)` is not a global instance.
example [Fact (Nat.Prime 5)] : (firstCongruenceSubgroup (Fin 2) 5).index = 120 :=
  index_firstCongruenceSubgroup_fin_two 5

example : (firstCongruenceProduct (Fin 2) 3 (Fin 2)).index = 576 :=
  index_firstCongruenceProduct_fin_two 3 (Fin 2)

section Compact

variable (p : ℕ) [Fact p.Prime] (m : ℕ)

example : CompactSpace (firstCongruenceSubgroup (Fin 2) p) := inferInstance

example : IsTopologicalGroup (firstCongruenceSubgroup (Fin 2) p) := inferInstance

example : CompactSpace (firstCongruenceProduct (Fin 2) p (Fin m)) := inferInstance

example : IsTopologicalGroup (firstCongruenceProduct (Fin 2) p (Fin m)) := inferInstance

noncomputable example :
    Ring (completedGroupAlgebra ℤ_[p] (firstCongruenceProduct (Fin 2) p (Fin m))) :=
  inferInstance

example : (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ_[p]) ∈ firstCongruenceSubgroup (Fin 2) p :=
  one_mem _

end Compact

example : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ_[2]) ∈ firstCongruenceSubgroup (Fin 2) 2 :=
  neg_one_mem_firstCongruenceSubgroup_iff.mpr rfl

example : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ_[3]) ∉ firstCongruenceSubgroup (Fin 2) 3 :=
  fun h ↦ by simpa using neg_one_mem_firstCongruenceSubgroup_iff.mp h
