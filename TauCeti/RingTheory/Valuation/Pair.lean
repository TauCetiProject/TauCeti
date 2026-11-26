/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Valuation pairs of commutative rings

A subring `R` of a commutative ring `A` is a *valuation pair* (`Subring.IsValuationPair R`) if
for all `a b : A` there exists an idempotent `e : R` such that both `a` and `b` are `R`-multiples
of `a - e * (a - b) = (1 - e) * a + e * b`.

Every `PreValuationRing A` (in particular every `ValuationRing A`) is a valuation pair inside
itself (`Subring.isValuationPair_top`), and every `ValuationSubring F` of a field `F` is a
valuation pair inside `F` (`ValuationSubring.isValuationPair_toSubring`). More generally, a ring
of integral adeles inside the finite adeles satisfies `Subring.IsValuationPair`.

## Main definitions and results

* `Subring.IsValuationPair`: valuation-pair condition on a subring `R` of a commutative ring `A`.
* `Subring.isValuationPair_iff` and `Subring.IsValuationPair.exists_idempotent`: characterization
  and elimination lemma for `Subring.IsValuationPair`.
* `Subring.IsValuationPair.top`: if `R ⊆ A` is a valuation pair, then `⊤ : Subring R` is a
  valuation pair.
* `Subring.isValuationPair_top`: every `PreValuationRing A` is a valuation pair inside itself.
* `ValuationSubring.isValuationPair_toSubring`: every valuation subring of a field is a valuation
  pair inside that field.

## References

* L. Alpöge and L. Sernau, Lean formalization of the generalized Riemann hypothesis for Dirichlet
  `L`-functions (`Lib/General/LinearAlgebra/IntegralLattices.lean`, `New.IsValuationPair`),
  <https://github.com/lsernau/grh-lean> (Apache 2.0).
* N. Bourbaki, *Commutative Algebra*, Chapter VI (valuation rings and finitely generated ideals).
-/

public section

open Submodule

namespace Subring

variable {A : Type*} [CommRing A]

/-- A subring `R` of a commutative ring `A` is a valuation pair if for all `a b : A` there exists
an idempotent `e : R` such that `a` and `b` are `R`-multiples of `a - e * (a - b)`. -/
def IsValuationPair (R : Subring A) : Prop :=
  ∀ a b : A, ∃ e : R, IsIdempotentElem e ∧ R ∙ a ⊔ R ∙ b ≤ R ∙ (a - e * (a - b))

/-- Characterization of `Subring.IsValuationPair`. -/
theorem isValuationPair_iff {R : Subring A} :
    R.IsValuationPair ↔
      ∀ a b : A, ∃ e : R, IsIdempotentElem e ∧ R ∙ a ⊔ R ∙ b ≤ R ∙ (a - e * (a - b)) :=
  Iff.rfl

/-- Elimination lemma for `Subring.IsValuationPair`: given `a, b : A`, produce an idempotent
`e : R` whose patch `a - e * (a - b)` generates an `R`-submodule containing `a` and `b`. -/
theorem IsValuationPair.exists_idempotent {R : Subring A} (hR : R.IsValuationPair) (a b : A) :
    ∃ e : R, IsIdempotentElem e ∧ R ∙ a ⊔ R ∙ b ≤ R ∙ (a - e * (a - b)) :=
  hR a b

/-- If `R ⊆ A` is a valuation pair, then `R` is a valuation pair inside itself. -/
theorem IsValuationPair.top {R : Subring A} (hR : R.IsValuationPair) :
    (⊤ : Subring R).IsValuationPair := by
  refine isValuationPair_iff.2 fun a b ↦ ?_
  obtain ⟨e, he, hle⟩ := hR.exists_idempotent a.val b.val
  let e' : (⊤ : Subring R) := ⟨e, trivial⟩
  have lift_mem {x : R} (hx : x.val ∈ R ∙ (a.val - e * (a.val - b.val))) :
      x ∈ (⊤ : Subring R) ∙ (a - e' * (a - b)) := by
    obtain ⟨r, hr⟩ := mem_span_singleton.1 hx
    exact mem_span_singleton.2
      ⟨⟨r, trivial⟩, Subtype.ext (by simpa [Subring.smul_def, e'] using hr)⟩
  refine ⟨e', Subtype.ext he.eq, sup_le ((span_singleton_le_iff_mem _ _).2 ?_)
    ((span_singleton_le_iff_mem _ _).2 ?_)⟩
  · exact lift_mem (le_sup_left.trans hle (mem_span_singleton_self _))
  · exact lift_mem (le_sup_right.trans hle (mem_span_singleton_self _))

/-- Every `PreValuationRing A` (in particular every `ValuationRing A`) is a valuation pair inside
itself. -/
theorem isValuationPair_top [PreValuationRing A] : (⊤ : Subring A).IsValuationPair := by
  refine isValuationPair_iff.2 fun a b ↦ ?_
  obtain ⟨c, hc | hc⟩ := PreValuationRing.cond a b
  · refine ⟨0, IsIdempotentElem.zero, sup_le ((span_singleton_le_iff_mem _ _).2 ?_)
      ((span_singleton_le_iff_mem _ _).2 ?_)⟩
    · exact mem_span_singleton.2 ⟨1, by simp⟩
    · exact mem_span_singleton.2 ⟨⟨c, trivial⟩, by simp [Subring.smul_def, mul_comm, hc]⟩
  · refine ⟨1, IsIdempotentElem.one, sup_le ((span_singleton_le_iff_mem _ _).2 ?_)
      ((span_singleton_le_iff_mem _ _).2 ?_)⟩
    · exact mem_span_singleton.2 ⟨⟨c, trivial⟩, by simp [Subring.smul_def, mul_comm, hc]⟩
    · exact mem_span_singleton.2 ⟨1, by simp⟩

end Subring

namespace ValuationSubring

variable {F : Type*} [Field F]

/-- Every valuation subring `O` of a field `F` is a valuation pair inside `F`. -/
theorem isValuationPair_toSubring (O : ValuationSubring F) : O.toSubring.IsValuationPair := by
  refine Subring.isValuationPair_iff.2 fun a b ↦ ?_
  have h_dvd : (∃ y ∈ O, a = b * y) ∨ ∃ y ∈ O, b = a * y := by
    by_cases ha : a = 0
    · exact Or.inl ⟨0, O.zero_mem, by simp [ha]⟩
    · by_cases hb : b = 0
      · exact Or.inr ⟨0, O.zero_mem, by simp [hb]⟩
      · rcases O.mem_or_inv_mem (a / b) with h | h
        · exact Or.inl ⟨a / b, h, by field_simp⟩
        · exact Or.inr ⟨(a / b)⁻¹, h, by field_simp⟩
  rcases h_dvd with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
  · refine ⟨1, IsIdempotentElem.one, sup_le ((span_singleton_le_iff_mem _ _).2 ?_)
      ((span_singleton_le_iff_mem _ _).2 ?_)⟩
    · exact mem_span_singleton.2 ⟨⟨y, hy⟩, by simp [Subring.smul_def]; ring⟩
    · exact mem_span_singleton.2 ⟨1, by simp⟩
  · refine ⟨0, IsIdempotentElem.zero, sup_le ((span_singleton_le_iff_mem _ _).2 ?_)
      ((span_singleton_le_iff_mem _ _).2 ?_)⟩
    · exact mem_span_singleton.2 ⟨1, by simp⟩
    · exact mem_span_singleton.2 ⟨⟨y, hy⟩, by simp [Subring.smul_def]; ring⟩

end ValuationSubring
