/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Finiteness.Projective

/-!
# Finite projective modules have finite free complements

A finitely generated projective left module `P` over a ring `R` is a direct summand of a finite
free module: there are a finitely generated projective module `N` and a natural number `n` with
`P × N ≃ₗ[R] (Fin n → R)`. The complement is the kernel of a surjection `Rⁿ → P`, which splits
because `P` is projective; it is finitely generated as a quotient of `Rⁿ`, so no noetherian
hypothesis on `R` is needed, and `R` need not be commutative.

This is the step that lets a stabilisation witness in the split Grothendieck group of finitely
generated projective modules be replaced by a finite free module: if `P × T ≃ₗ[R] Q × T` with
`T` finite projective, then adding a complement of `T` gives `P × Rⁿ ≃ₗ[R] Q × Rⁿ`.

## Main results

* `Module.Projective.exists_prod_linearEquiv_fin`: a finitely generated projective module `P` has
  a finitely generated projective complement `N`, in the universe of `R`, with
  `P × N ≃ₗ[R] (Fin n → R)` for some `n`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter I, Section 2,
  pp. 6–7: a finitely generated projective module is a direct summand of a finite free module.
-/

public section

universe u v

namespace Module.Projective

open LinearMap

variable (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module R P]

/-- A finitely generated projective module `P` over a ring `R` has a finitely generated projective
complement `N` in a finite free module: `P × N ≃ₗ[R] (Fin n → R)` for some `n`. The complement
lives in the universe of `R`, whatever the universe of `P`. -/
theorem exists_prod_linearEquiv_fin [Module.Finite R P] [Module.Projective R P] :
    ∃ (N : Type u) (_ : AddCommGroup N) (_ : Module R N) (_ : Module.Finite R N)
      (_ : Module.Projective R N) (n : ℕ), Nonempty ((P × N) ≃ₗ[R] (Fin n → R)) := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R P
  -- The section `g` splits `Rⁿ` as the kernel of `f` times `P`.
  let e : (Fin n → R) ≃ₗ[R] ker f × P :=
    ((exact_subtype_ker_map f).splitSurjectiveEquiv (ker f).injective_subtype ⟨g, hfg⟩).1
  have : Module.Finite R (ker f × P) := Module.Finite.equiv e
  have : Module.Projective R (ker f × P) := .of_equiv' e
  have : Module.Finite R (ker f) := .of_surjective (fst R (ker f) P) fst_surjective
  have : Module.Projective R (ker f) :=
    .of_split (inl R (ker f) P) (fst R (ker f) P) (fst_comp_inl ..)
  exact ⟨ker f, _, _, ‹_›, ‹_›, n, ⟨(LinearEquiv.prodComm R P (ker f)).trans e.symm⟩⟩

end Module.Projective
