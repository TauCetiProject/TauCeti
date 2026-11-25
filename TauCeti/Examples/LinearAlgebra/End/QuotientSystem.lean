/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.LinearAlgebra.End.QuotientSystem
import TauCeti.NumberTheory.Padics.RingHoms
import Mathlib.Analysis.Complex.Basic

/-!
# Examples of finite quotient systems

* On the `p`-adic integers, the filtration `J n = (p ^ n)` is a finite quotient system for every
  `ℤ_[p]`-linear endomorphism, and `ℤ_[p]` is compact for its inverse-limit topology.
* A module that is finite as a set has the one-term system `J = ⊥`; here multiplication by `2`
  on `ZMod 6` as a `ℤ`-module, whose induced endomorphism of `ZMod 6 ⧸ ⊥` is again
  multiplication by `2`.
* Multiplication by `2` on `ℂ` admits no finite quotient system over `ℂ`: the only finite-index
  `ℂ`-subspace of `ℂ` is `ℂ` itself, so separation fails.
-/

open IsLocalRing Module.End

example (p : ℕ) [Fact p.Prime] (U : Module.End ℤ_[p] ℤ_[p]) :
    ∃ h : U.FiniteQuotientSystem ℕ, (∀ n, h.submodule n = Ideal.span {(p : ℤ_[p]) ^ n}) ∧
      @CompactSpace ℤ_[p] h.topology := by
  have : Finite (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) := PadicInt.finite_residueField
  let h := FiniteQuotientSystem.ofModuleFinite (maximalIdeal ℤ_[p])
    (Ideal.fg_of_isNoetherianRing _) U
  refine ⟨h, fun n ↦ ?_, h.compactSpace⟩
  rw [FiniteQuotientSystem.ofModuleFinite_submodule, PadicInt.maximalIdeal_eq_span_p,
    Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]

example (x : ZMod 6) :
    (FiniteQuotientSystem.ofFinite (2 : Module.End ℤ (ZMod 6))).mapQ ()
      (Submodule.Quotient.mk x) = Submodule.Quotient.mk (2 * x) := by
  rw [FiniteQuotientSystem.mapQ_mk]
  simp

example : IsEmpty ((2 : Module.End ℂ ℂ).FiniteQuotientSystem ℕ) :=
  FiniteQuotientSystem.isEmpty_of_infinite _ _
