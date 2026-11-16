/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.Data.Set.Countable

/-!
# Countable approximation of polynomials modulo ideals

Over a ring, if the quotients by the ideals of a countable family are countable, every set of
polynomials has a countable subset that approximates each of its members coefficientwise modulo
every ideal of the family. The approximants stay in the original set, so constraints such as
monicity, a degree condition or the Eisenstein condition are preserved without separate
stability arguments.

The main case is the family of powers of one ideal, which gives countable families of defining
polynomials when root counts are locally constant under ideal-adic perturbations. No topology
on the coefficient ring is required.
-/

public section

open Polynomial

namespace Ideal

variable {R : Type*} [Ring R]

/-- A set of polynomials has a countable subset approximating all its members coefficientwise
modulo every ideal of a countable family whose quotients are countable.
The approximants belong to the given set.
-/
theorem exists_countable_polynomial_approximations {ι : Type*} [Countable ι]
    (I : ι → Ideal R) (hI : ∀ k, Countable (R ⧸ I k)) (s : Set R[X]) :
    ∃ t ⊆ s, t.Countable ∧ ∀ f ∈ s, ∀ k, ∃ g ∈ t, ∀ i, g.coeff i - f.coeff i ∈ I k := by
  -- For each `k`, keep one member of `s` for each coefficientwise residue that occurs. These
  -- residues are finitely supported, so there are only countably many of them.
  choose u hus hu using fun k ↦ s.exists_subset_bijOn fun f : R[X] ↦
    f.coeff.mapRange (Submodule.Quotient.mk (p := I k)) (Submodule.Quotient.mk_zero _)
  refine ⟨⋃ k, u k, Set.iUnion_subset hus, Set.countable_iUnion fun k ↦ ?_, fun f hf k ↦ ?_⟩
  · have := hI k
    exact Set.countable_of_injective_of_countable_image (hu k).injOn (Set.to_countable _)
  obtain ⟨g, hg, hgf⟩ := (hu k).surjOn (Set.mem_image_of_mem _ hf)
  refine ⟨g, Set.mem_iUnion_of_mem k hg, fun i ↦ ?_⟩
  -- Read off the `i`-th coefficient of the equal residues.
  have hi := DFunLike.congr_fun hgf i
  rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply] at hi
  exact (Submodule.Quotient.eq _).mp hi

end Ideal
