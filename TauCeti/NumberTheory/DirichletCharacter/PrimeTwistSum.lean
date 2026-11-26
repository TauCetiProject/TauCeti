/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Even

/-!
# Sums over even prime twists

Fix a natural number `f` and a scale `Q`. For a family `L q χ` indexed by levels `q` and Dirichlet
characters `χ` of level `q`, the *even prime-twist sum* is the finite sum
`∑_{Q < q ≤ 2Q, q prime, q ∤ f} ∑_{χ mod q, χ even, χ ≠ 1} L q χ`.

Luo, Rudnick and Sarnak take `f` to be the conductor of a cuspidal automorphic representation `π`
of `GL_m` over `ℚ`, and `L q χ = L(β, (π ⊗ χ) × π')` with `π'` the contragredient of `π`. They
show that for `β` in a suitable range this sum is asymptotic to `(1/2) ∑_q q`, hence nonzero for
large `Q`. A nonzero sum has a nonzero summand
(`TauCeti.DirichletCharacter.exists_ne_zero_of_evenPrimeTwistSum_ne_zero`), so some twist does not
vanish at `β`. The definition fixes only the finite index set; it makes no analytic assumption on
the family. A family depending on a further parameter, such as the point `β`, is summed at a fixed
value of it.

With values in a domain with enough roots of unity there are `(q - 1) / 2 - 1` even nontrivial
characters at a prime `q`, so a constant family `c` has sum `∑_q ((q - 1) / 2 - 1) • c`
(`TauCeti.DirichletCharacter.evenPrimeTwistSum_const`). At `q = 2` and `q = 3` there are none.

## Main definitions

* `TauCeti.DirichletCharacter.primeTwistModuli f Q`: the primes `q` with `Q < q ≤ 2Q` not
  dividing `f`.
* `TauCeti.DirichletCharacter.evenPrimeTwistSum f Q L`: the sum of `L q χ` over these primes `q`
  and the even nontrivial Dirichlet characters `χ` of level `q`.

## Main results

* `TauCeti.DirichletCharacter.evenPrimeTwistSum_congr`,
  `TauCeti.DirichletCharacter.evenPrimeTwistSum_eq_zero`: the sum depends only on the selected
  values of the family.
* `TauCeti.DirichletCharacter.exists_ne_zero_of_evenPrimeTwistSum_ne_zero`: a nonzero sum has a
  nonzero selected value.
* `TauCeti.DirichletCharacter.evenPrimeTwistSum_const`: the sum of a constant family.

## References

* W. Luo, Z. Rudnick and P. Sarnak, *On Selberg's eigenvalue conjecture*, Geom. Funct. Anal. 5
  (1995), 387–401, equation (3.4) and Proposition 3.1.
-/

public section

open Finset

namespace TauCeti.DirichletCharacter

/-- The moduli of the prime twists at scale `Q` away from `f`: the primes `q` with `Q < q ≤ 2Q`
that do not divide `f`. -/
def primeTwistModuli (f Q : ℕ) : Finset ℕ :=
  {q ∈ Ioc Q (2 * Q) | q.Prime ∧ ¬q ∣ f}

@[simp]
theorem mem_primeTwistModuli {f Q q : ℕ} :
    q ∈ primeTwistModuli f Q ↔ (Q < q ∧ q ≤ 2 * Q) ∧ q.Prime ∧ ¬q ∣ f := by
  rw [primeTwistModuli, mem_filter, mem_Ioc]

/-- Every prime divides `0`, so there are no prime twists away from `0`. -/
@[simp]
theorem primeTwistModuli_zero_left (Q : ℕ) : primeTwistModuli 0 Q = ∅ := by
  ext q
  simp

/-- The dyadic interval `(0, 0]` is empty. -/
@[simp]
theorem primeTwistModuli_zero_right (f : ℕ) : primeTwistModuli f 0 = ∅ := by
  ext q
  simp only [mem_primeTwistModuli, mul_zero, notMem_empty, iff_false]
  omega

variable {R : Type*} [CommRing R] [IsDomain R] {M : Type*}

section AddCommMonoid

variable [AddCommMonoid M] {f Q : ℕ}

open scoped Classical in
/-- The *even prime-twist sum* of a family `L q χ` at scale `Q` away from `f`: the sum of
`L q χ` over the primes `Q < q ≤ 2Q` not dividing `f` and the even nontrivial Dirichlet characters
`χ` of level `q`. -/
noncomputable def evenPrimeTwistSum (f Q : ℕ) (L : (q : ℕ) → DirichletCharacter R q → M) : M :=
  ∑ q ∈ primeTwistModuli f Q, ∑ χ : DirichletCharacter R q with χ.Even ∧ χ ≠ 1, L q χ

open scoped Classical in
theorem evenPrimeTwistSum_def (f Q : ℕ) (L : (q : ℕ) → DirichletCharacter R q → M) :
    evenPrimeTwistSum f Q L =
      ∑ q ∈ primeTwistModuli f Q, ∑ χ : DirichletCharacter R q with χ.Even ∧ χ ≠ 1, L q χ :=
  (rfl)

/-- The even prime-twist sum depends only on the values `L q χ` at the selected primes `q` and
even nontrivial characters `χ`. -/
theorem evenPrimeTwistSum_congr {L L' : (q : ℕ) → DirichletCharacter R q → M}
    (h : ∀ q ∈ primeTwistModuli f Q, ∀ χ : DirichletCharacter R q, χ.Even → χ ≠ 1 →
      L q χ = L' q χ) :
    evenPrimeTwistSum f Q L = evenPrimeTwistSum f Q L' := by
  classical
  rw [evenPrimeTwistSum_def, evenPrimeTwistSum_def]
  refine sum_congr rfl fun q hq ↦ sum_congr rfl fun χ hχ ↦ ?_
  rw [mem_filter] at hχ
  exact h q hq χ hχ.2.1 hχ.2.2

/-- The even prime-twist sum of a family vanishing at the selected primes and even nontrivial
characters is zero. -/
theorem evenPrimeTwistSum_eq_zero {L : (q : ℕ) → DirichletCharacter R q → M}
    (h : ∀ q ∈ primeTwistModuli f Q, ∀ χ : DirichletCharacter R q, χ.Even → χ ≠ 1 → L q χ = 0) :
    evenPrimeTwistSum f Q L = 0 := by
  classical
  rw [evenPrimeTwistSum_congr (L' := fun _ _ ↦ 0) h, evenPrimeTwistSum_def]
  simp

/-- A nonzero even prime-twist sum has a nonzero summand: some prime `Q < q ≤ 2Q` not dividing
`f` and some even nontrivial character `χ` of level `q` have `L q χ ≠ 0`. -/
theorem exists_ne_zero_of_evenPrimeTwistSum_ne_zero {L : (q : ℕ) → DirichletCharacter R q → M}
    (h : evenPrimeTwistSum f Q L ≠ 0) :
    ∃ q ∈ primeTwistModuli f Q, ∃ χ : DirichletCharacter R q, χ.Even ∧ χ ≠ 1 ∧ L q χ ≠ 0 := by
  contrapose! h
  exact evenPrimeTwistSum_eq_zero h

@[simp]
theorem evenPrimeTwistSum_zero (f Q : ℕ) :
    evenPrimeTwistSum f Q (0 : (q : ℕ) → DirichletCharacter R q → M) = 0 :=
  evenPrimeTwistSum_eq_zero fun _ _ _ _ _ ↦ rfl

@[simp]
theorem evenPrimeTwistSum_add (f Q : ℕ) (L L' : (q : ℕ) → DirichletCharacter R q → M) :
    evenPrimeTwistSum f Q (L + L') = evenPrimeTwistSum f Q L + evenPrimeTwistSum f Q L' := by
  classical
  simp only [evenPrimeTwistSum_def, Pi.add_apply, sum_add_distrib]

/-- The even prime-twist sum of a constant family `c`: each prime `q` contributes
`(q - 1) / 2 - 1` copies of `c`, one for each even nontrivial character of level `q`. -/
theorem evenPrimeTwistSum_const
    (hR : ∀ q ∈ primeTwistModuli f Q, HasEnoughRootsOfUnity R (Monoid.exponent (ZMod q)ˣ))
    (c : M) :
    evenPrimeTwistSum f Q (fun (q : ℕ) (_ : DirichletCharacter R q) ↦ c) =
      ∑ q ∈ primeTwistModuli f Q, ((q - 1) / 2 - 1) • c := by
  classical
  rw [evenPrimeTwistSum_def]
  refine sum_congr rfl fun q hq ↦ ?_
  have := hR q hq
  have hq' := (mem_primeTwistModuli.mp hq).2.1
  rw [sum_const, DirichletCharacter.card_even_ne_one, Nat.totient_prime hq']

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup M]

@[simp]
theorem evenPrimeTwistSum_neg (f Q : ℕ) (L : (q : ℕ) → DirichletCharacter R q → M) :
    evenPrimeTwistSum f Q (-L) = -evenPrimeTwistSum f Q L := by
  classical
  simp only [evenPrimeTwistSum_def, Pi.neg_apply, sum_neg_distrib]

@[simp]
theorem evenPrimeTwistSum_sub (f Q : ℕ) (L L' : (q : ℕ) → DirichletCharacter R q → M) :
    evenPrimeTwistSum f Q (L - L') = evenPrimeTwistSum f Q L - evenPrimeTwistSum f Q L' := by
  classical
  simp only [evenPrimeTwistSum_def, Pi.sub_apply, sum_sub_distrib]

end AddCommGroup

/-! ### Examples

The sums below are over a domain `R` with enough roots of unity at the levels involved, such as
`ℂ`. -/

section Examples

variable (L : (q : ℕ) → DirichletCharacter R q → M) [AddCommMonoid M]

/-- The interval `(0, 0]` is empty, and every prime divides `0`. -/
example : evenPrimeTwistSum 1 0 L = 0 ∧ evenPrimeTwistSum 0 5 L = 0 := by
  simp [evenPrimeTwistSum_def]

/-- At `Q = 1` the only prime is `2`, which has no nontrivial character. -/
example : evenPrimeTwistSum 1 1 (fun (q : ℕ) (_ : DirichletCharacter R q) ↦ (1 : ℤ)) = 0 := by
  have h : primeTwistModuli 1 1 = {2} := by decide
  rw [evenPrimeTwistSum_const fun q hq ↦ ?_, h]
  · simp
  · rw [h, mem_singleton] at hq
    subst hq
    rw [Monoid.exp_eq_one_iff.mpr inferInstance]
    infer_instance

variable [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod 3)ˣ)]
  [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod 5)ˣ)]

/-- At `Q = 2` the only prime is `3`, which has no even nontrivial character. -/
example : evenPrimeTwistSum 1 2 (fun (q : ℕ) (_ : DirichletCharacter R q) ↦ (1 : ℤ)) = 0 := by
  have h : primeTwistModuli 1 2 = {3} := by decide
  rw [evenPrimeTwistSum_const fun q hq ↦ ?_, h]
  · simp
  · rw [h, mem_singleton] at hq
    rwa [hq]

/-- At `Q = 3` the only prime is `5`, with the quadratic character as its one even nontrivial
character. -/
example : evenPrimeTwistSum 1 3 (fun (q : ℕ) (_ : DirichletCharacter R q) ↦ (1 : ℤ)) = 1 := by
  have h : primeTwistModuli 1 3 = {5} := by decide
  rw [evenPrimeTwistSum_const fun q hq ↦ ?_, h]
  · simp
  · rw [h, mem_singleton] at hq
    rwa [hq]

/-- Away from `f = 5` the prime `5` is excluded, and no prime is left at `Q = 3`. -/
example : evenPrimeTwistSum 5 3 (fun (q : ℕ) (_ : DirichletCharacter R q) ↦ (1 : ℤ)) = 0 := by
  rw [evenPrimeTwistSum_def, show primeTwistModuli 5 3 = ∅ by decide, sum_empty]

end Examples

end TauCeti.DirichletCharacter
