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

The same cancellation of signed permutation sums gives `Equiv.Perm.sum_sign_smul_comp_eq_zero`: the
alternating sum `∑ σ, sign σ • F (v ∘ σ)` vanishes for any function `F` of a family `v` that is
invariant under swapping two of its arguments, multilinear or not.
-/

public section

namespace MultilinearMap

variable {R M N ι ι' : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommGroup N]
  [Module R N] [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

/-- Alternatization commutes with reindexing the arguments along an equivalence. -/
theorem alternatization_domDomCongr (e : ι ≃ ι') (m : MultilinearMap (RingHom.id R) (fun _ : ι ↦ M)
    N) :
    (m.domDomCongr e).alternatization = m.alternatization.domDomCongr e := by
  ext v
  simp only [alternatization_apply, AlternatingMap.domDomCongr_apply, domDomCongr_apply]
  exact (Fintype.sum_equiv e.permCongr _ _ fun σ ↦ by
    simp [Equiv.Perm.sign_permCongr, Equiv.permCongr_apply]).symm

end MultilinearMap

namespace Equiv.Perm

variable {ι α N : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup N]

/-- **A signed sum over permutations vanishes on a function invariant under a transposition**: if
`F (v ∘ swap i j) = F v` for all `v` and some `i ≠ j`, then `∑ σ, sign σ • F (v ∘ σ) = 0`, since the
terms of `σ` and `σ * swap i j` cancel. -/
theorem sum_sign_smul_comp_eq_zero {F : (ι → α) → N} {i j : ι} (hij : i ≠ j)
    (hF : ∀ v, F (v ∘ swap i j) = F v) (v : ι → α) :
    ∑ σ : Perm ι, sign σ • F (v ∘ σ) = 0 :=
  Finset.sum_involution (fun σ _ ↦ σ * swap i j)
    (fun σ _ ↦ by
      rw [coe_mul, ← Function.comp_assoc, hF, sign_mul, sign_swap hij, mul_neg, mul_one,
        Units.neg_smul, add_neg_cancel])
    (fun σ _ _ ↦ (not_congr mul_swap_eq_iff).mpr hij) (fun σ _ ↦ Finset.mem_univ _)
    (fun σ _ ↦ by rw [mul_assoc, swap_mul_self, mul_one])

end Equiv.Perm
