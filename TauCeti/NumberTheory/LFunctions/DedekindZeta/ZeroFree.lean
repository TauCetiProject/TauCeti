/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.ZeroFree
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Cyclotomic
public import TauCeti.NumberTheory.DirichletCharacter.Conductor
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel

/-!
# Zero-free half-planes for cyclotomic Dedekind zeta functions

The order of the zeta function of an `n`-th cyclotomic field is the sum of the orders of the
primitive Dirichlet L-functions indexed by the characters modulo `n`. Only the principal
factor has a pole, at `1`, where none of the other factors vanishes. Thus the zeros are the
union of those of the factors. In the open right half-plane one can test the ambient level-`n`
characters instead: the deleted Euler factors are nonvanishing there. At threshold `1 / 2`,
this gives the zero-free half-plane equivalence between cyclotomic zeta and Dirichlet L-functions.

The factorization used here is Washington, *Introduction to Cyclotomic Fields*, Theorem 4.3,
in the punctured-germ form `dedekindZetaC_eventuallyEq_prod_LFunction_primitiveCharacter`.
-/

public section

namespace TauCeti.LFunctions

open DirichletCharacter

variable {K : Type*} [Field K] [NumberField K]
variable (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ K]

/-- The meromorphic order of cyclotomic Dedekind zeta is the sum of the orders of the
primitive Dirichlet L-factors, including at the pole `s = 1`. -/
theorem meromorphicOrderAt_dedekindZetaC_eq_sum_primitiveCharacter (s : ℂ) :
    meromorphicOrderAt (dedekindZetaC K) s =
      ∑ χ : DirichletCharacter ℂ n, meromorphicOrderAt χ.primitiveCharacter.LFunction s := by
  rw [meromorphicOrderAt_congr
    (dedekindZetaC_eventuallyEq_prod_LFunction_primitiveCharacter (K := K) (n := n) s)]
  exact meromorphicOrderAt_fun_prod fun χ _ ↦ χ.primitiveCharacter.meromorphic_LFunction s

/-- A point is a zero of cyclotomic Dedekind zeta exactly when it is a zero of one of
its primitive Dirichlet L-factors. The only pole does not cancel a zero. -/
theorem meromorphicOrderAt_dedekindZetaC_pos_iff_exists_primitiveCharacter (s : ℂ) :
    0 < meromorphicOrderAt (dedekindZetaC K) s ↔
      ∃ χ : DirichletCharacter ℂ n, 0 < meromorphicOrderAt χ.primitiveCharacter.LFunction s := by
  rw [meromorphicOrderAt_dedekindZetaC_eq_sum_primitiveCharacter n]
  constructor
  · intro h
    by_contra! hnone
    exact h.not_ge (Finset.sum_nonpos fun χ _ ↦ hnone χ)
  · rintro ⟨χ, hχ⟩
    have hs : s ≠ 1 := by
      rintro rfl
      obtain ⟨hz, hguard⟩ := χ.primitiveCharacter.meromorphicOrderAt_LFunction_pos_iff.mp hχ
      exact LFunction_ne_zero_of_one_le_re χ.primitiveCharacter hguard.symm (by simp) hz
    exact hχ.trans_le (Finset.single_le_sum
      (fun ψ _ ↦ (ψ.primitiveCharacter.analyticAt_LFunction (.inl hs)).meromorphicOrderAt_nonneg)
      (Finset.mem_univ χ))

/-- Cyclotomic Dedekind zeta is zero-free right of any threshold if and only if all of its
primitive Dirichlet L-factors are zero-free there. -/
theorem zeroFreeRightOf_dedekindZetaC_iff_forall_primitiveCharacter {σ : ℝ} :
    ZeroFreeRightOf σ (dedekindZetaC K) ↔
      ∀ χ : DirichletCharacter ℂ n, ZeroFreeRightOf σ χ.primitiveCharacter.LFunction := by
  simp only [zeroFreeRightOf_iff, ← not_lt,
    meromorphicOrderAt_dedekindZetaC_pos_iff_exists_primitiveCharacter n, not_exists]
  exact ⟨fun h χ s hs ↦ h s hs χ, fun h s hs χ ↦ h χ s hs⟩

/-- For a nonnegative threshold, cyclotomic Dedekind zeta is zero-free to its right if and
only if the L-functions of all Dirichlet characters at the cyclotomic level are. The latter
need not be primitive. -/
theorem zeroFreeRightOf_dedekindZetaC_iff_forall_LFunction {σ : ℝ} (hσ : 0 ≤ σ) :
    ZeroFreeRightOf σ (dedekindZetaC K) ↔
      ∀ χ : DirichletCharacter ℂ n, ZeroFreeRightOf σ χ.LFunction := by
  rw [zeroFreeRightOf_dedekindZetaC_iff_forall_primitiveCharacter n]
  simp only [zeroFreeRightOf_iff]
  refine forall_congr' fun χ ↦ forall₂_congr fun s hs ↦ ?_
  conv_rhs => rw [← χ.changeLevel_primitiveCharacter,
    meromorphicOrderAt_LFunction_changeLevel _ _ (hσ.trans_lt hs)]

end TauCeti.LFunctions
