/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.RingTheory.QuotSMulTop
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Reduction modulo `p` of finite free `ℤ_p`-modules

A finite free `ℤ_p`-module `M` of rank `r` is isomorphic to `ℤ_p ^ r`, so its reduction
`M / pM` is isomorphic to `(ℤ_p / p) ^ r ≃ 𝔽_p ^ r` and has `p ^ r` elements.

## Main results

* `TauCeti.natCard_quotient_padicInt_smul_top`: reduction modulo `p` of a finite free
  `ℤ_p`-module of rank `r` has `p^r` elements.
-/

public section

namespace TauCeti

open scoped Pointwise

universe u

variable (p : ℕ) [Fact p.Prime]

/-- **The reduction of a finite free `ℤ_p`-module has the expected cardinality.** If `M` is
free of finite rank over `ℤ_p`, then `M / pM` has `p ^ finrank M` elements. -/
theorem natCard_quotient_padicInt_smul_top (M : Type u) [AddCommGroup M] [Module ℤ_[p] M]
    [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M] :
    Nat.card (M ⧸ (p : ℤ_[p]) • (⊤ : Submodule ℤ_[p] M)) =
      p ^ Module.finrank ℤ_[p] M := by
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ_[p] M
  let b := Module.Free.chooseBasis ℤ_[p] M
  let e : (M ⧸ (p : ℤ_[p]) • (⊤ : Submodule ℤ_[p] M)) ≃ₗ[ℤ_[p]]
      ((i : ι) → ℤ_[p]) ⧸ (p : ℤ_[p]) • (⊤ : Submodule ℤ_[p] (ι → ℤ_[p])) :=
    QuotSMulTop.congr (p : ℤ_[p]) b.equivFun
  have hpi : (p : ℤ_[p]) • (⊤ : Submodule ℤ_[p] (ι → ℤ_[p])) =
      Submodule.pi Set.univ (fun _ : ι ↦ Ideal.span {(p : ℤ_[p])}) := by
    ext x
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top,
      Submodule.mem_pi, Set.mem_univ, forall_const, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, -, hy⟩ i
      exact ⟨y i, (congrFun hy i).symm⟩
    · intro hx
      choose y hy using hx
      exact ⟨y, trivial, (funext hy).symm⟩
  let q : (((i : ι) → ℤ_[p]) ⧸ (p : ℤ_[p]) •
      (⊤ : Submodule ℤ_[p] (ι → ℤ_[p]))) ≃ₗ[ℤ_[p]]
      ((i : ι) → (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])})) :=
    (Submodule.quotEquivOfEq _ _ hpi).trans
      (Submodule.quotientPi fun _ : ι ↦ Ideal.span {(p : ℤ_[p])})
  rw [Nat.card_congr e.toEquiv, Nat.card_congr q.toEquiv, Nat.card_pi,
    PadicInt.natCard_quotient_span (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero),
    PadicInt.valuation_p, pow_one, Finset.prod_const, Finset.card_univ,
    ← Module.finrank_eq_card_chooseBasisIndex]

end TauCeti
