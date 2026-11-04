/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Lifts

/-!
# Polynomials fixed by coefficient automorphisms

Let `f : A →+* B` be a ring map and `S` a set of automorphisms of `B` whose common fixed points
lie in the image of `f`. A polynomial over `B` whose coefficients are fixed by every member of
`S` then lifts along `f`. This is the coefficient step of Galois descent, stated without any
algebraicity or Galois hypothesis on `B` over `A`.

## Main results

* `Polynomial.mem_lifts_of_forall_map_eq`: a polynomial over `B` fixed by `Polynomial.map σ` for
  every `σ ∈ S` lifts along `f`.
-/

public section

namespace Polynomial

variable {A B : Type*} [Semiring A] [Semiring B] {f : A →+* B}

/-- **Polynomials fixed by a set of automorphisms lift.** Let `S` be a set of automorphisms of
`B` whose common fixed points lie in the image of `f`. A polynomial over `B` fixed by
`Polynomial.map σ` for every `σ ∈ S` lifts along `f`. -/
theorem mem_lifts_of_forall_map_eq {S : Set (B ≃+* B)}
    (hS : ∀ c : B, (∀ σ ∈ S, σ c = c) → c ∈ Set.range f) {p : B[X]}
    (hp : ∀ σ ∈ S, p.map (σ : B →+* B) = p) : p ∈ lifts f :=
  (lifts_iff_coeff_lifts p).mpr fun n ↦ hS _ fun σ hσ ↦ by
    simpa using congr($(hp σ hσ).coeff n)

end Polynomial
