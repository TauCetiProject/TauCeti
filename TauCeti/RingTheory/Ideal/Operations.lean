/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Ring.Subgroup
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
* `Ideal.toAddSubgroup_mul_eq_closure_mul`: additive generators of a product of ideals.
* `Ideal.smul_top_eq_top_of_pi`: an ideal that expands the whole of a product of modules expands
  the whole of every factor.
* `Ideal.span_insert_eq_top_of_subset`: a generating set `S` may be replaced by a set `S'`, both
  taken together with a common element `a`, as soon as every element of `S` is `a` itself or
  belongs to `S'`.
* `Ideal.sup_pow_le_sup_pow_right`: modulo a two-sided ideal `I`, powers of
  `I ⊔ J` are controlled by the corresponding power of the two-sided ideal `J`.
* `Subalgebra.toSubmodule_sup_pow_restrictScalars_eq_top`: a subalgebra meeting every
  residue class modulo a principal ideal and containing a generator of it meets every residue
  class modulo each power of that ideal.
-/

public section

open scoped Pointwise

namespace Ideal

variable {R : Type*} [Ring R] {I J : Ideal R} {S T : Set R}

/-- If `S` and `T` additively generate the ideals `I` and `J`, then their pairwise products
additively generate `I * J`. -/
theorem toAddSubgroup_mul_eq_closure_mul
    (hI : I.toAddSubgroup = AddSubgroup.closure S)
    (hJ : J.toAddSubgroup = AddSubgroup.closure T) :
    (I * J).toAddSubgroup = AddSubgroup.closure (S * T) := by
  apply AddSubgroup.toAddSubmonoid_injective
  rw [Submodule.toAddSubgroup_toAddSubmonoid, _root_.Submodule.mul_toAddSubmonoid,
    ← Submodule.toAddSubgroup_toAddSubmonoid I, ← Submodule.toAddSubgroup_toAddSubmonoid J,
    hI, hJ, ← _root_.AddSubgroup.mul_toAddSubmonoid,
    AddSubgroup.closure_mul_closure]

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

universe u

/-- For two-sided ideals, the `n`-th power of a supremum is contained in the first ideal
plus the `n`-th power of the second. -/
theorem Ideal.sup_pow_le_sup_pow_right {R : Type u} [Semiring R] (I J : Ideal R)
    [I.IsTwoSided] [J.IsTwoSided] (n : ℕ) :
    (I ⊔ J) ^ n ≤ I ⊔ J ^ n := by
  let : (I ⊔ J).IsTwoSided :=
    ⟨fun b ha ↦ by
      obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.mp ha
      rw [add_mul]
      exact Submodule.add_mem _ (Ideal.mem_sup_left (I.mul_mem_right b hi))
        (Ideal.mem_sup_right (J.mul_mem_right b hj))⟩
  induction n with
  | zero =>
      rw [Submodule.pow_zero, Submodule.pow_zero]
      exact le_sup_right
  | succ n ih =>
      rw [Ideal.IsTwoSided.pow_succ (I := I ⊔ J),
        Ideal.IsTwoSided.pow_succ (I := J)]
      refine (Ideal.mul_mono_right ih).trans ?_
      rw [Ideal.mul_sup, Ideal.sup_mul, Ideal.sup_mul]
      exact sup_le
        (sup_le (Ideal.mul_le_left.trans le_sup_left)
          (Ideal.mul_le_right.trans le_sup_left))
        (sup_le (Ideal.mul_le_left.trans le_sup_left) le_sup_right)

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
