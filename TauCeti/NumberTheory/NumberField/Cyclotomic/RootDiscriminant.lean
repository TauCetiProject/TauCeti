/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Discriminant.Tower
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification

/-!
# Root discriminant bounds for cyclotomic extensions

In a cyclotomic extension of number fields the root discriminant grows by at most a factor of
its level: the level belongs to the relative different. This bound does not require that the
level and the discriminant of the base field are coprime.
-/

public section

namespace IsCyclotomicExtension

open NumberField

/-- In a cyclotomic extension of level `n > 0`, the root discriminant lies between that of the
base and `n` times that of the base. -/
theorem rootDiscr_mem_Icc (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] {n : ℕ} [IsCyclotomicExtension {n} K L] (hn : 0 < n) :
    rootDiscr L ∈ Set.Icc (rootDiscr K) (rootDiscr K * n) :=
  TauCeti.NumberField.rootDiscr_mem_Icc_of_natCast_mem_differentIdeal K L hn
    (natCast_mem_differentIdeal K L n)

end IsCyclotomicExtension
