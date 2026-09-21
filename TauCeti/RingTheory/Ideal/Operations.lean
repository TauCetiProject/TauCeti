/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Ideal.Operations

import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Ring

/-!
# Complements on ideal multiplication and the ideal action

This file collects general facts about the multiplication of ideals and about the action `I • N`
of an ideal on a module, complementing `Mathlib/RingTheory/Ideal/Operations.lean`.

## Main results

* `Ideal.eq_one_of_mul_eq_one`: the only factorization of the unit ideal is the trivial one, so a
  factor of `1` is `1`. This is the ideal-theoretic cancellation step behind the fact that the
  divisor antidiagonal of the unit ideal is a singleton.
* `Ideal.smul_top_eq_top_of_pi`: an ideal that expands the whole of a product of modules expands
  the whole of every factor.
* `Ideal.span_insert_eq_top_of_subset`: a generating set `S` may be replaced by a set `S'`, both
  taken together with a common element `a`, as soon as every element of `S` is `a` itself or
  belongs to `S'`.
* `Subalgebra.toSubmodule_sup_pow_restrictScalars_eq_top`: a subalgebra meeting every
  residue class modulo a principal ideal and containing a generator of it meets every residue
  class modulo each power of that ideal.
-/

public section

namespace Ideal

section Mul

variable {R : Type*} [CommSemiring R] {I J : Ideal R}

/-- If two ideals multiply to the unit ideal, then the first ideal is the unit ideal. -/
theorem eq_one_of_mul_eq_one (h : I * J = 1) : I = 1 := by
  have hle : (1 : Ideal R) ≤ I := by
    rw [← h]
    exact Ideal.mul_le_left
  rw [Ideal.one_eq_top, eq_top_iff]
  simpa [Ideal.one_eq_top] using hle

end Mul

section Pi

variable {R : Type*} [Semiring R] {ι : Type*} {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)]

/-- **Expanding a product expands every factor**: if `I • ⊤ = ⊤` in `∀ i, M i` then `I • ⊤ = ⊤` in
each `M i`. Faithful flatness of a product is decided factorwise through this, since
`Module.FaithfullyFlat` is flatness together with `m • ⊤ ≠ ⊤` at every maximal ideal. -/
theorem smul_top_eq_top_of_pi (I : Ideal R) (h : I • (⊤ : Submodule R (∀ i, M i)) = ⊤) (i : ι) :
    I • (⊤ : Submodule R (M i)) = ⊤ := by
  have := congrArg (Submodule.map (LinearMap.proj (R := R) (φ := M) i)) h
  rwa [Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr (Function.surjective_eval i)] at this

end Pi

section Span

variable {R : Type*} [CommSemiring R] {a : R} {S S' : Set R}

/-- **Replacing one generating set by another**: if every element of `S` is either `a` itself or an
element of `S'`, then `S'` together with `a` generates the unit ideal as soon as `S` together with
`a` does. Note that `S'` need not be contained in `S`, and may be larger: the hypothesis constrains
only where the elements of `S` are found. Both spans contain `a`, so only the rest of `S` has to be
accounted for. -/
theorem span_insert_eq_top_of_subset (hsub : S ⊆ insert a S')
    (hspan : Ideal.span (insert a S) = ⊤) : Ideal.span (insert a S') = ⊤ :=
  eq_top_mono (Ideal.span_mono <| Set.insert_subset (Set.mem_insert _ _) hsub) hspan

end Span

end Ideal

namespace Subalgebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- If a subalgebra `T` meets every residue class of `S` modulo a principal ideal `I` and contains
a generator of `I`, then it meets every residue class modulo any power of `I`. -/
theorem toSubmodule_sup_pow_restrictScalars_eq_top {T : Subalgebra R S} {I : Ideal S} {π : S}
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

end Subalgebra

end
