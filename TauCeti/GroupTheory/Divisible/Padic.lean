/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Nat.Prime.Basic
public import TauCeti.GroupTheory.Divisible.Classification
public import TauCeti.NumberTheory.Padics.PruferQuotient

import Mathlib.Algebra.DirectSum.Module

/-!
# Classification of divisible abelian groups using p-adic quotients

A divisible abelian group is a direct sum of copies of `ℚ` and of `ℚ_p/ℤ_p`.
The multiplicities are indexed by bases of its torsion-free quotient and its `p`-torsion.
-/

public section

namespace TauCeti

open scoped AddSubgroup DirectSum

/-- **Classification of divisible abelian groups in the p-adic quotient model.** Rational
copies are indexed by a basis of the torsion-free quotient, and copies of `ℚ_p/ℤ_p` by a basis
of the `p`-torsion. -/
theorem nonempty_addEquiv_rat_padicQuotientSum {A ι₀ : Type*} [AddCommGroup A]
    [DivisibleBy A ℕ] [Module ℚ (A ⧸ AddCommGroup.torsion A)]
    [∀ p : Nat.Primes, Module (ZMod p) A[(p : ℤ)]] {ι : Nat.Primes → Type*}
    (b₀ : Module.Basis ι₀ ℚ (A ⧸ AddCommGroup.torsion A))
    (b : ∀ p : Nat.Primes, Module.Basis (ι p) (ZMod p) A[(p : ℤ)]) :
    Nonempty (A ≃+ (ι₀ →₀ ℚ) ×
      (⨁ p : Nat.Primes, (ι p →₀ ℚ_[p] ⧸ (1 : Submodule ℤ_[p] ℚ_[p])))) := by
  obtain ⟨e⟩ := nonempty_addEquiv_rat_pruferSum b₀ b
  refine ⟨e.trans (AddEquiv.prodCongr (AddEquiv.refl _) ?_)⟩
  exact DirectSum.congrAddEquiv fun p ↦
    Finsupp.mapRange.addEquiv (ratCirclePrimaryEquivPadicQuotient p)

end TauCeti
