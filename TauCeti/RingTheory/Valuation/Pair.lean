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

/-!
# Valuation pairs of commutative rings

A subring `R` of a commutative ring `A` is a *valuation pair* (`Subring.IsValuationPair R`) if
for all `a b : A` there exists an idempotent `e : R` such that both `a` and `b` are `R`-multiples
of `a - e * (a - b) = (1 - e) * a + e * b`.

Every `PreValuationRing A` (in particular every `ValuationRing A`) is a valuation pair inside
itself (`Subring.isValuationPair_top`), and every `ValuationSubring F` of a field `F` is a
valuation pair inside `F` (`ValuationSubring.isValuationPair_toSubring`).

## Main definitions and results

* `Subring.IsValuationPair`: valuation-pair condition on a subring `R` of a commutative ring `A`.
* `Subring.isValuationPair_iff`: characterization of `Subring.IsValuationPair`.
* `Subring.isValuationPair_of_mem_or_mem`: sufficient condition when `R`-spans of singletons are
  totally ordered (no nontrivial idempotents needed).
* `Subring.IsValuationPair.top_subring`: if `R ⊆ A` is a valuation pair, then `⊤ : Subring R` is a
  valuation pair.
* `Subring.isValuationPair_top`: every `PreValuationRing A` is a valuation pair inside itself.
* `Subring.IsValuationPair.pi`: the product `⨅ w, (R w).comap (Pi.evalRingHom B w)` of valuation
  pairs `R w ⊆ B w` is a valuation pair in `∀ w, B w`.
* `Subring.IsValuationPair.comap`: a valuation pair `R ⊆ B` pulls back along an injective ring
  homomorphism `A →+* B` whose range contains `R`; for instance, the integral finite adeles of a
  Dedekind domain form a valuation pair, as the pullback of the full product of local integers.
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

/-- If for all `a b : A` either `a ∈ R ∙ b` or `b ∈ R ∙ a`, then `R` is a valuation pair. -/
theorem isValuationPair_of_mem_or_mem {R : Subring A} (h : ∀ a b : A, a ∈ R ∙ b ∨ b ∈ R ∙ a) :
    R.IsValuationPair := by
  refine isValuationPair_iff.2 fun a b ↦ ?_
  rcases h a b with hab | hba
  · refine ⟨1, IsIdempotentElem.one, ?_⟩
    simpa [sup_le_iff, span_singleton_le_iff_mem] using hab
  · refine ⟨0, IsIdempotentElem.zero, ?_⟩
    simpa [sup_le_iff, span_singleton_le_iff_mem] using hba

/-- If `R ⊆ A` is a valuation pair, then `R` is a valuation pair inside itself. -/
theorem IsValuationPair.top_subring {R : Subring A} (hR : R.IsValuationPair) :
    (⊤ : Subring R).IsValuationPair := by
  refine isValuationPair_iff.2 fun a b ↦ ?_
  obtain ⟨e, he, hle⟩ := isValuationPair_iff.1 hR a.val b.val
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
theorem isValuationPair_top [PreValuationRing A] : (⊤ : Subring A).IsValuationPair :=
  isValuationPair_of_mem_or_mem fun a b ↦ by
    obtain ⟨c, hc | hc⟩ := PreValuationRing.cond a b
    · exact Or.inr (mem_span_singleton.2 ⟨⟨c, trivial⟩, by simp [Subring.smul_def, mul_comm, hc]⟩)
    · exact Or.inl (mem_span_singleton.2 ⟨⟨c, trivial⟩, by simp [Subring.smul_def, mul_comm, hc]⟩)

section Pi

variable {σ : Type*} {B : σ → Type*} [∀ w, CommRing (B w)]

/-- If every `R w ⊆ B w` is a valuation pair, then so is the product subring
`⨅ w, (R w).comap (Pi.evalRingHom B w)` of `∀ w, B w`, the families `x` with `x w ∈ R w` for all
`w`. For instance, the integers `∏ w, O w` of a product of fields `∏ w, F w` with valuation
subrings `O w` form a valuation pair (with `ValuationSubring.isValuationPair_toSubring`). -/
theorem IsValuationPair.pi {R : ∀ w, Subring (B w)} (hR : ∀ w, (R w).IsValuationPair) :
    (⨅ w, (R w).comap (Pi.evalRingHom B w)).IsValuationPair := by
  set S := ⨅ w, (R w).comap (Pi.evalRingHom B w)
  have hS (x : ∀ w, B w) : x ∈ S ↔ ∀ w, x w ∈ R w := by simp [S, mem_iInf]
  refine isValuationPair_iff.2 fun a b ↦ ?_
  choose e he hle using fun w ↦ isValuationPair_iff.1 (hR w) (a w) (b w)
  have mul_mem {x : ∀ w, B w} (hx : ∀ w, x w ∈ R w ∙ (a w - e w * (a w - b w))) :
      x ∈ S ∙ (a - (fun w ↦ (e w : B w)) * (a - b)) := by
    choose r hr using fun w ↦ mem_span_singleton.1 (hx w)
    refine mem_span_singleton.2
      ⟨⟨fun w ↦ r w, (hS _).2 fun w ↦ (r w).property⟩, funext fun w ↦ ?_⟩
    simpa [Subring.smul_def] using hr w
  refine ⟨⟨fun w ↦ e w, (hS _).2 fun w ↦ (e w).property⟩,
    Subtype.ext (funext fun w ↦ congrArg Subtype.val (he w).eq), sup_le ?_ ?_⟩ <;>
    refine (span_singleton_le_iff_mem _ _).2 (mul_mem fun w ↦ ?_)
  · exact le_sup_left.trans (hle w) (mem_span_singleton_self _)
  · exact le_sup_right.trans (hle w) (mem_span_singleton_self _)

end Pi

section Comap

variable {B : Type*} [CommRing B]

/-- A valuation pair `R ⊆ B` pulls back along an injective ring homomorphism `f : A →+* B` whose
range contains `R`: then `R.comap f` is a valuation pair in `A`. The idempotent and the
multipliers that witness the condition in `B` lie in `R`, hence come from `A`. -/
theorem IsValuationPair.comap {R : Subring B} (hR : R.IsValuationPair) {f : A →+* B}
    (hf : Function.Injective f) (hRf : R ≤ f.range) : (R.comap f).IsValuationPair := by
  have lift (x : R) : ∃ y : R.comap f, f y = x := by
    obtain ⟨y, hy⟩ := hRf x.property
    exact ⟨⟨y, by simp [hy]⟩, hy⟩
  refine isValuationPair_iff.2 fun a b ↦ ?_
  obtain ⟨e, he, hle⟩ := isValuationPair_iff.1 hR (f a) (f b)
  obtain ⟨e', he'⟩ := lift e
  -- a multiple in `B` of `f (a - e' * (a - b))` by an element of `R` is a multiple in `A`
  have mem_of_mem {x : A} (hx : f x ∈ R ∙ (f a - e * (f a - f b))) :
      x ∈ R.comap f ∙ (a - e' * (a - b)) := by
    obtain ⟨r, hr⟩ := mem_span_singleton.1 hx
    obtain ⟨r', hr'⟩ := lift r
    refine mem_span_singleton.2 ⟨r', hf ?_⟩
    simpa [Subring.smul_def, hr', he'] using hr
  refine ⟨e', ?_, sup_le ((span_singleton_le_iff_mem _ _).2 ?_)
    ((span_singleton_le_iff_mem _ _).2 ?_)⟩
  · refine Subtype.ext (hf ?_)
    simpa [he'] using congrArg Subtype.val he.eq
  · exact mem_of_mem (le_sup_left.trans hle (mem_span_singleton_self _))
  · exact mem_of_mem (le_sup_right.trans hle (mem_span_singleton_self _))

end Comap

end Subring

namespace ValuationSubring

variable {F : Type*} [Field F]

/-- Every valuation subring `O` of a field `F` is a valuation pair inside `F`. -/
theorem isValuationPair_toSubring (O : ValuationSubring F) : O.toSubring.IsValuationPair :=
  Subring.isValuationPair_of_mem_or_mem fun a b ↦ (le_total (O.valuation a) (O.valuation b)).imp
    (fun h ↦ let ⟨y, hy⟩ := (O.valuation_le_iff a b).1 h
      mem_span_singleton.2 ⟨y, by simpa [Subring.smul_def, mul_comm] using hy⟩)
    (fun h ↦ let ⟨y, hy⟩ := (O.valuation_le_iff b a).1 h
      mem_span_singleton.2 ⟨y, by simpa [Subring.smul_def, mul_comm] using hy⟩)

end ValuationSubring
