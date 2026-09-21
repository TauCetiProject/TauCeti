/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.Ring

/-!
# Subalgebra lattice lemmas

For an injective `algebraMap R A`, `Algebra.botEquivOfInjective` identifies the bottom subalgebra
`⊥` of `A` with `R`. Mathlib states it without `@[simps]` — unlike `Algebra.botEquiv`, which
carries `@[simps! symm_apply]` — so nothing names its value on an element. This file supplies the
equation in the direction a caller needs: applying `algebraMap R A` to the result returns the
element itself.

It also records that if a subalgebra meets every residue class modulo a principal ideal and
contains a generator of that ideal, then it meets every residue class modulo every power.

## Main results

* `Algebra.algebraMap_botEquivOfInjective`: `algebraMap R A (botEquivOfInjective h x) = x` for
  `x : (⊥ : Subalgebra R A)`.
* `TauCeti.Subalgebra.sup_pow_eq_top`: generation modulo a principal ideal propagates to every
  power of that ideal.
-/

public section

namespace Algebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- **`algebraMap R A` undoes `botEquivOfInjective`.** The equiv sends an element of `⊥` to the
scalar it comes from, so mapping that scalar back into `A` returns the element.

The proof is the inverse equiv's `AlgEquiv.commutes`, read through `Subalgebra.coe_algebraMap`. -/
@[simp]
theorem algebraMap_botEquivOfInjective (h : Function.Injective (algebraMap R A))
    (x : (⊥ : Subalgebra R A)) : algebraMap R A (botEquivOfInjective h x) = (x : A) := by
  have hx := (botEquivOfInjective h).symm.commutes (botEquivOfInjective h x)
  simp only [algebraMap_self_apply, AlgEquiv.symm_apply_apply] at hx
  conv_rhs => rw [hx]
  exact (Subalgebra.coe_algebraMap _ _).symm

end Algebra

namespace TauCeti.Subalgebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- If a subalgebra `T` meets every residue class of `S` modulo a principal ideal `I` and contains
a generator of `I`, then it meets every residue class modulo any power of `I`. -/
theorem sup_pow_eq_top {T : Subalgebra R S} {I : Ideal S} {π : S}
    (hπ : Ideal.span {π} = I) (hπT : π ∈ T)
    (h : T.toSubmodule ⊔ I.restrictScalars R = ⊤) (n : ℕ) :
    T.toSubmodule ⊔ (I ^ n).restrictScalars R = ⊤ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow : I ^ n = Ideal.span {π ^ n} := by
      rw [← hπ, Ideal.span_singleton_pow]
    refine eq_top_iff.mpr fun s _ => ?_
    obtain ⟨t, ht, m, hm, rfl⟩ := Submodule.mem_sup.mp (ih.ge Submodule.mem_top : s ∈ _)
    obtain ⟨u, rfl⟩ : ∃ u, m = π ^ n * u := by
      rw [Submodule.restrictScalars_mem, hpow, Ideal.mem_span_singleton] at hm
      exact hm
    obtain ⟨t', ht', m', hm', rfl⟩ := Submodule.mem_sup.mp (h.ge Submodule.mem_top : u ∈ _)
    refine Submodule.mem_sup.mpr ⟨t + π ^ n * t', ?_, π ^ n * m', ?_, by ring⟩
    · rw [Subalgebra.mem_toSubmodule] at ht ht' ⊢
      exact add_mem ht (mul_mem (pow_mem hπT n) ht')
    · rw [Submodule.restrictScalars_mem, pow_succ]
      exact Ideal.mul_mem_mul (hpow ▸ Ideal.mem_span_singleton_self _) hm'

end TauCeti.Subalgebra

end
