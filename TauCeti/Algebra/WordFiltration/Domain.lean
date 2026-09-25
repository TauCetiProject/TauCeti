/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.WordFiltration.AssociatedGraded

/-!
# Zero divisors in a word-filtered algebra are seen in its associated graded

Let `f : M →ₗ[R] A` be a linear family of generators of an algebra `A` and let
`TauCeti.Algebra.wordFiltration f` be the filtration it generates. This file proves the
**filtered-to-graded transfer of the domain property**: if the associated graded algebra
`TauCeti.Algebra.wordFiltration.AssociatedGraded f` has no zero divisors and the filtration is
exhaustive, then `A` has no zero divisors, and is a domain as soon as it is nontrivial. The
specialization to the PBW filtration of a universal enveloping algebra is
`TauCeti/Algebra/Lie/UniversalEnveloping/PBW/Domain.lean`.

The argument is the classical leading-term computation. An exhaustive filtration gives every
nonzero `a : A` a *leading degree*: the least `i` with `a ∈ F i`, which is the same as an `i` with
`a ∈ F i` and `a ∉ F_{i-1}`. Its **symbol** — the class of `a` in the graded piece `F i / F_{i-1}`
— is then nonzero, precisely because `a` is not in the preceding step. Symbols multiply: the
symbol of `a` in degree `i` times the symbol of `b` in degree `j` is the class of `a * b` in degree
`i + j`. If the graded product of the two nonzero symbols is nonzero, then `a * b` misses the step
`F_{i+j-1}`; in particular `a * b ≠ 0`, since `0` lies in every step. Nothing is needed of the
graded algebra beyond the vanishing behaviour of products of *homogeneous* classes, so the
hypothesis is stated in that form first and only then packaged as `NoZeroDivisors` of the whole
associated graded ring.

The converse fails, so this is a genuinely one-way transfer: the Clifford algebra of the
negative definite line over `ℝ` is `ℂ`, a field, while the associated graded of its degree
filtration is the exterior algebra of a line, which squares its generator to zero. What the
transfer buys is the standard route to the domain property for an algebra presented by generators
and relations — replace the relations by their leading terms and count there.

## Main results

* `TauCeti.Algebra.wordFiltration.mul_notMem_wordFiltrationPrevious`: leading degrees add, when
  homogeneous products of nonzero classes are nonzero.
* `TauCeti.Algebra.wordFiltration.noZeroDivisors_of_gradedMul_ne_zero`: the transfer, from the
  homogeneous hypothesis.
* `TauCeti.Algebra.wordFiltration.gradedMul_ne_zero_of_noZeroDivisors`: that homogeneous
  hypothesis, read off the associated graded ring.
* `TauCeti.Algebra.wordFiltration.noZeroDivisors_of_noZeroDivisors_associatedGraded` and
  `TauCeti.Algebra.wordFiltration.isDomain_of_noZeroDivisors_associatedGraded`: the transfer, from
  the associated graded ring.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
* J. C. McConnell and J. C. Robson, *Noncommutative Noetherian Rings*, §1.6.
-/

public section

open scoped DirectSum

universe u v w

namespace TauCeti.Algebra.wordFiltration

variable {R : Type u} {M : Type v} {A : Type w}
variable [CommRing R] [AddCommMonoid M] [Module R M] [Ring A] [Algebra R A]
variable (f : M →ₗ[R] A)

/-- **Leading degrees add.** If products of nonzero homogeneous classes in the associated graded
are nonzero, then an element of leading degree `i` times an element of leading degree `j` has
leading degree `i + j`: their product misses the step preceding `i + j`. -/
theorem mul_notMem_wordFiltrationPrevious
    (hgr : ∀ (i j : ℕ) (x : GradedPiece f i) (y : GradedPiece f j),
      x ≠ 0 → y ≠ 0 → gradedMul f i j x y ≠ 0)
    {i j : ℕ} {a b : A} (ha : a ∈ wordFiltration f i)
    (ha' : a ∉ wordFiltrationPrevious f i) (hb : b ∈ wordFiltration f j)
    (hb' : b ∉ wordFiltrationPrevious f j) :
    a * b ∉ wordFiltrationPrevious f (i + j) := by
  have hx : (Submodule.Quotient.mk ⟨a, ha⟩ : GradedPiece f i) ≠ 0 := fun hzero =>
    ha' ((gradedPiece_mk_eq_zero_iff f ⟨a, ha⟩).mp hzero)
  have hy : (Submodule.Quotient.mk ⟨b, hb⟩ : GradedPiece f j) ≠ 0 := fun hzero =>
    hb' ((gradedPiece_mk_eq_zero_iff f ⟨b, hb⟩).mp hzero)
  have hxy := hgr i j _ _ hx hy
  rw [gradedMul_apply_mk] at hxy
  exact fun hmem => hxy ((gradedPiece_mk_eq_zero_iff f _).mpr hmem)

/-- **The filtered-to-graded transfer of the domain property**, in its homogeneous form: an
exhaustively word-filtered algebra has no zero divisors as soon as products of nonzero homogeneous
classes of its associated graded are nonzero. -/
theorem noZeroDivisors_of_gradedMul_ne_zero
    (hex : ∀ a : A, ∃ k, a ∈ wordFiltration f k)
    (hgr : ∀ (i j : ℕ) (x : GradedPiece f i) (y : GradedPiece f j),
      x ≠ 0 → y ≠ 0 → gradedMul f i j x y ≠ 0) :
    NoZeroDivisors A := by
  refine ⟨fun {a b} hab => ?_⟩
  by_cases ha : a = 0
  · exact Or.inl ha
  by_cases hb : b = 0
  · exact Or.inr hb
  -- Two nonzero elements have leading degrees `i` and `j`, and their product misses the step
  -- preceding `i + j`; but `0` lies in every step, so the product is nonzero.
  obtain ⟨i, hai, hai'⟩ := exists_mem_notMem_wordFiltrationPrevious f ha (hex a)
  obtain ⟨j, hbj, hbj'⟩ := exists_mem_notMem_wordFiltrationPrevious f hb (hex b)
  refine absurd ?_ (mul_notMem_wordFiltrationPrevious f hgr hai hai' hbj hbj')
  rw [hab]
  exact Submodule.zero_mem _

/-- The homogeneous hypothesis of
`TauCeti.Algebra.wordFiltration.noZeroDivisors_of_gradedMul_ne_zero`, read off the associated
graded ring. -/
theorem gradedMul_ne_zero_of_noZeroDivisors [NoZeroDivisors (AssociatedGraded f)]
    {i j : ℕ} {x : GradedPiece f i} {y : GradedPiece f j} (hx : x ≠ 0) (hy : y ≠ 0) :
    gradedMul f i j x y ≠ 0 := by
  intro hzero
  -- The homogeneous product is the ring product of the corresponding direct-sum generators.
  have hprod :
      (DirectSum.of (GradedPiece f) i x * DirectSum.of (GradedPiece f) j y :
        AssociatedGraded f) = 0 := by
    rw [associatedGraded_of_mul_of, hzero, map_zero]
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hprod with hcase | hcase
  · exact hx (DirectSum.of_injective i (hcase.trans (map_zero _).symm))
  · exact hy (DirectSum.of_injective j (hcase.trans (map_zero _).symm))

/-- **An exhaustively word-filtered algebra whose associated graded has no zero divisors has
none.** -/
theorem noZeroDivisors_of_noZeroDivisors_associatedGraded
    [NoZeroDivisors (AssociatedGraded f)]
    (hex : ∀ a : A, ∃ k, a ∈ wordFiltration f k) : NoZeroDivisors A :=
  noZeroDivisors_of_gradedMul_ne_zero f hex fun _ _ _ _ hx hy =>
    gradedMul_ne_zero_of_noZeroDivisors f hx hy

/-- **An exhaustively word-filtered nontrivial algebra whose associated graded has no zero divisors
is a domain.** -/
theorem isDomain_of_noZeroDivisors_associatedGraded [Nontrivial A]
    [NoZeroDivisors (AssociatedGraded f)]
    (hex : ∀ a : A, ∃ k, a ∈ wordFiltration f k) : IsDomain A := by
  have : NoZeroDivisors A := noZeroDivisors_of_noZeroDivisors_associatedGraded f hex
  exact NoZeroDivisors.to_isDomain A

end TauCeti.Algebra.wordFiltration
