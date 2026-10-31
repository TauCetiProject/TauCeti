/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.Squarefree.Basic

/-!
# Squarefree products of distinct polynomial variables

A finite product of distinct variables over an integral domain is squarefree.
This supplies the reduced coordinate boundaries in algebraic normal crossings charts.
-/

public section

namespace TauCeti.MvPolynomial

open _root_.MvPolynomial

variable {R ι σ : Type*} [CommRing R] [IsDomain R]

/-- A finite product of variables indexed by an injective map is squarefree. -/
theorem squarefree_prod_X_of_injective {f : ι → σ} (hf : Function.Injective f)
    (s : Finset ι) : Squarefree (∏ i ∈ s, X (R := R) (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    intro a ha
    rcases prime_X.left_dvd_or_dvd_right_of_dvd_mul ha with h | h
    · have hia : X (f i) ∣ a := (prime_X.dvd_mul.mp h).elim id id
      have his : X (f i) ∣ ∏ j ∈ s, X (R := R) (f j) :=
        (mul_dvd_mul_iff_left (X_ne_zero (f i))).mp ((mul_dvd_mul hia hia).trans ha)
      obtain ⟨j, hj, hij⟩ := prime_X.exists_mem_finset_dvd his
      exact (hi (hf (X_dvd_X.mp hij) ▸ hj)).elim
    · exact ih a h

end TauCeti.MvPolynomial
