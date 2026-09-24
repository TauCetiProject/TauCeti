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
exhaustive, then `A` has no zero divisors, and is a domain as soon as it is nontrivial.

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

* `TauCeti.Algebra.wordFiltration.exists_mem_notMem_wordFiltrationPrevious`: every nonzero element
  of an exhaustively filtered algebra has a leading degree.
* `TauCeti.Algebra.wordFiltration.mul_notMem_wordFiltrationPrevious`: leading degrees add, when
  homogeneous products of nonzero classes are nonzero.
* `TauCeti.Algebra.wordFiltration.noZeroDivisors_of_gradedMul_ne_zero`: the transfer, from the
  homogeneous hypothesis.
* `TauCeti.Algebra.wordFiltration.noZeroDivisors_of_noZeroDivisors_associatedGraded` and
  `TauCeti.Algebra.wordFiltration.isDomain_of_noZeroDivisors_associatedGraded`: the transfer, from
  the associated graded ring.

## Roadmap

`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, Layer 3 ("PBW, a substantial
sub-project"), asks for `isDomain_universalEnvelopingAlgebra`, "`U(L)` is a **domain**, by transfer
from the associated graded symmetric algebra". This file is that transfer, stated for the word
filtrations the PBW filtration is an instance of; the specialization to the enveloping algebra is
`TauCeti/Algebra/Lie/UniversalEnveloping/PBW/Domain.lean`.

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

/-- The class of a filtered element in the graded piece of its degree vanishes exactly when the
element already lies in the preceding filtration step. -/
theorem gradedPiece_mk_eq_zero_iff {k : ℕ} (x : wordFiltration f k) :
    (Submodule.Quotient.mk x : GradedPiece f k) = 0 ↔
      (x : A) ∈ wordFiltrationPrevious f k := by
  rw [Submodule.Quotient.mk_eq_zero, mem_previousRestricted_iff]

/-- **An exhaustive word filtration gives every nonzero element a leading degree**: a degree it
belongs to but whose preceding step it misses. In that degree the element has a nonzero symbol, by
`TauCeti.Algebra.wordFiltration.gradedPiece_mk_eq_zero_iff`.

Degree zero is the case where the element itself is nonzero while the preceding step is trivial;
in a successor degree the preceding step is the previous filtration step, which minimality of the
degree excludes. -/
theorem exists_mem_notMem_wordFiltrationPrevious {a : A} (ha : a ≠ 0)
    (hex : ∃ k, a ∈ wordFiltration f k) :
    ∃ k, a ∈ wordFiltration f k ∧ a ∉ wordFiltrationPrevious f k := by
  classical
  obtain ⟨k, hk, hmin⟩ :
      ∃ k, a ∈ wordFiltration f k ∧ ∀ m, m < k → a ∉ wordFiltration f m :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  refine ⟨k, hk, ?_⟩
  cases k with
  | zero => simpa using ha
  | succ m =>
      rw [wordFiltrationPrevious_succ]
      exact hmin m (Nat.lt_succ_self m)

/-- A word filtration whose generators generate the whole algebra is exhaustive: every element
lies in some step. This is the hypothesis the transfer below runs on, read off
`TauCeti.Algebra.iSup_wordFiltration_eq_adjoin` and the directedness of the filtration. -/
theorem exists_mem_wordFiltration_of_adjoin_eq_top
    (h : _root_.Algebra.adjoin R (Set.range f) = ⊤) (a : A) :
    ∃ k, a ∈ wordFiltration f k := by
  have hmem : a ∈ ⨆ k, wordFiltration f k := by
    rw [iSup_wordFiltration_eq_adjoin, h, _root_.Algebra.top_toSubmodule]
    exact Submodule.mem_top
  rwa [Submodule.mem_iSup_of_directed _ (wordFiltration_mono f).directed_le] at hmem

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
classes of its associated graded are nonzero.

Two nonzero elements have leading degrees `i` and `j`, and their product misses the step preceding
`i + j`; but `0` lies in every step, so the product is nonzero. -/
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
  obtain ⟨i, hai, hai'⟩ := exists_mem_notMem_wordFiltrationPrevious f ha (hex a)
  obtain ⟨j, hbj, hbj'⟩ := exists_mem_notMem_wordFiltrationPrevious f hb (hex b)
  refine absurd ?_ (mul_notMem_wordFiltrationPrevious f hgr hai hai' hbj hbj')
  rw [hab]
  exact Submodule.zero_mem _

/-- The homogeneous hypothesis of
`TauCeti.Algebra.wordFiltration.noZeroDivisors_of_gradedMul_ne_zero`, read off the associated
graded ring: the homogeneous product is the ring product of the corresponding direct-sum
generators, and a direct-sum generator vanishes only when its component does. -/
theorem gradedMul_ne_zero_of_noZeroDivisors (h : NoZeroDivisors (AssociatedGraded f))
    {i j : ℕ} {x : GradedPiece f i} {y : GradedPiece f j} (hx : x ≠ 0) (hy : y ≠ 0) :
    gradedMul f i j x y ≠ 0 := by
  intro hzero
  have hprod :
      (DirectSum.of (GradedPiece f) i x * DirectSum.of (GradedPiece f) j y :
        AssociatedGraded f) = 0 := by
    rw [associatedGraded_of_mul_of, hzero, map_zero]
  rcases h.eq_zero_or_eq_zero_of_mul_eq_zero hprod with hcase | hcase
  · exact hx (by simpa using congrArg (fun z : AssociatedGraded f => z i) hcase)
  · exact hy (by simpa using congrArg (fun z : AssociatedGraded f => z j) hcase)

/-- **An exhaustively word-filtered algebra whose associated graded has no zero divisors has
none.** -/
theorem noZeroDivisors_of_noZeroDivisors_associatedGraded
    (hex : ∀ a : A, ∃ k, a ∈ wordFiltration f k)
    (h : NoZeroDivisors (AssociatedGraded f)) : NoZeroDivisors A :=
  noZeroDivisors_of_gradedMul_ne_zero f hex fun _ _ _ _ hx hy =>
    gradedMul_ne_zero_of_noZeroDivisors f h hx hy

/-- **An exhaustively word-filtered nontrivial algebra whose associated graded has no zero divisors
is a domain.** -/
theorem isDomain_of_noZeroDivisors_associatedGraded [Nontrivial A]
    (hex : ∀ a : A, ∃ k, a ∈ wordFiltration f k)
    (h : NoZeroDivisors (AssociatedGraded f)) : IsDomain A :=
  @NoZeroDivisors.to_isDomain A _ _ (noZeroDivisors_of_noZeroDivisors_associatedGraded f hex h)

end TauCeti.Algebra.wordFiltration
