/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Over

/-!
# Moving primes between fibres

For an `A`-algebra `B`, Mathlib's `Ideal.primesOver p B` is the set of primes of `B` lying over a
prime `p` of `A`. This file records how that set behaves under the two operations used to compare
fibres: translating by a group acting by `A`-algebra automorphisms, and contracting to an
intermediate ring of a tower `A → C → B`. Translation preserves the fibre, contraction sends the
fibre over `p` in `B` into the fibre over `p` in `C`, and for `B` integral and faithful over `C`
every prime of the smaller fibre is such a contraction.

These are the membership forms of Mathlib's instances `Ideal.IsPrime.smul`,
`Ideal.LiesOver.smul` and `Ideal.nonempty_primesOver`, for use where a prime is carried as an
element of `primesOver` rather than with instance arguments.

## Main results

* `Ideal.smul_mem_primesOver`: a translate of a prime over `p` lies over `p`.
* `Ideal.under_mem_primesOver`: the contraction of a prime over `p` lies over `p`.
* `Ideal.exists_mem_primesOver_under_eq`: in an integral extension, every prime over `p` is the
  contraction of a prime over `p` upstairs.
-/

public section

namespace Ideal

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {p : Ideal A}

open scoped Pointwise in
/-- **Translation preserves the fibre.** If `G` acts on `B` by `A`-algebra automorphisms, a
translate of a prime of `B` over `p` is again a prime over `p`. -/
theorem smul_mem_primesOver {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (g : G) {Q : Ideal B} (hQ : Q ∈ p.primesOver B) : g • Q ∈ p.primesOver B :=
  have := hQ.1
  have := hQ.2
  ⟨inferInstance, inferInstance⟩

variable {C : Type*} [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B]

/-- **Contraction maps fibres to fibres.** In a tower `A → C → B`, the contraction to `C` of a
prime of `B` over `p` is a prime of `C` over `p`. -/
theorem under_mem_primesOver {Q : Ideal B} (hQ : Q ∈ p.primesOver B) :
    Q.under C ∈ p.primesOver C :=
  have := hQ.1
  have := hQ.2
  ⟨inferInstance, ⟨by rw [under_under]; exact over_def Q p⟩⟩

/-- **Contraction onto a fibre is surjective.** In a tower `A → C → B` with `B` integral and
faithful over `C`, every prime of `C` over `p` is the contraction of a prime of `B` over `p`. -/
theorem exists_mem_primesOver_under_eq [Algebra.IsIntegral C B] [FaithfulSMul C B]
    {P : Ideal C} (hP : P ∈ p.primesOver C) : ∃ Q ∈ p.primesOver B, Q.under C = P := by
  have := hP.1
  have := hP.2
  obtain ⟨⟨Q, _, _⟩⟩ := (inferInstance : Nonempty (P.primesOver B))
  exact ⟨Q, ⟨inferInstance, LiesOver.trans Q P p⟩, (over_def Q P).symm⟩

end Ideal
