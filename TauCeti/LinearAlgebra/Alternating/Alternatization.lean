/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic

/-!
# Alternatization and reindexing of arguments

Alternatizing a multilinear map commutes with reindexing its arguments along an equivalence
`e : ι ≃ ι'`: `(m.domDomCongr e).alternatization = m.alternatization.domDomCongr e`. The two
signed permutation sums are matched by conjugating permutations of `ι` by `e`, which preserves
their signs. This is how a wedge product defined by alternatizing over `Fin (k + l)` is compared
with `AlternatingMap.domCoprod`, which lives on `Fin k ⊕ Fin l`.
-/

public section

namespace MultilinearMap

variable {R M N ι ι' : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommGroup N]
  [Module R N] [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

/-- Alternatization commutes with reindexing the arguments along an equivalence. -/
theorem alternatization_domDomCongr (e : ι ≃ ι') (m : MultilinearMap R (fun _ : ι ↦ M) N) :
    (m.domDomCongr e).alternatization = m.alternatization.domDomCongr e := by
  ext v
  simp only [alternatization_apply, AlternatingMap.domDomCongr_apply, domDomCongr_apply]
  exact (Fintype.sum_equiv e.permCongr _ _ fun σ ↦ by
    simp [Equiv.Perm.sign_permCongr, Equiv.permCongr_apply]).symm

end MultilinearMap
