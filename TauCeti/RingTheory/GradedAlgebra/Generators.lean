/-
Copyright (c) 2026 Mei contributors and The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import TauCeti.RingTheory.GradedAlgebra.DirectSum

/-!
# Homogeneous words in algebra generators

For an arbitrary map of generators `e : S → A` equipped with degrees `deg : S → Γ` in an
additive monoid `Γ`, `TauCeti.GradedAlgebra.wordSpan R e deg n` is the `R`-submodule spanned by
products of generators whose degrees sum to `n`. These spans form a `SetLike.GradedMonoid`
whose supremum over all degrees is `(Algebra.adjoin R (Set.range e)).toSubmodule`. Given any
target family `ℬ : Γ' → S'` whose pieces are closed under addition, `R`-scalar multiplication,
and graded multiplication (`AddSubmonoidClass`, `SMulMemClass`, `SetLike.GradedMonoid`), an
`R`-algebra homomorphism carrying each generator of degree `d` into degree `σ d` for an additive
degree map `σ : Γ →+ Γ'` carries `wordSpan R e deg c` into `ℬ (σ c)`.

If a family of homogeneous elements generates a graded algebra, each graded piece is spanned by
the words in that family whose total degree is exactly the degree of the piece. No basis,
commutativity of the algebra, or positivity of the grading is required.

This reduces questions about a graded piece to words of a prescribed total degree, so that bounds
on the degrees of the generators control the lengths of those words.

## Main definitions and results

* `TauCeti.GradedAlgebra.wordSpan`: the `R`-submodule spanned by generator words of a given total
  degree, with `wordSpan_gradedMonoid`, `iSup_wordSpan`, `map_mem_wordSpan`, and
  `algHom_apply_of_mem_wordSpan`.
* `TauCeti.GradedAlgebra.grade_eq_span_list_prod_map`: a homogeneous generating family spans each
  graded piece by its words of that total degree.

## Attribution

Adapted from `Mei/RingTheory/GradedAlgebra/Generators.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`9cf969cdee9748087aae45dbf4888a130890655c` (Apache 2.0). Original copyright and author credit
are retained. The generic `wordSpan` construction and lemmas are generalized from
`TauCeti.UniversalEnvelopingAlgebra.homogeneousSubmodule` (itself adapted from
`Mei/Algebra/Lie/UniversalEnveloping/Grading.lean`, commit
`68536122a97fed8e87bc6870b9427151971b9ab2`).
-/

public section

open scoped DirectSum

namespace TauCeti.GradedAlgebra

open _root_.GradedAlgebra

section WordSpan

variable (R : Type*) {A S Γ : Type*} [AddMonoid Γ]
  [CommSemiring R] [Semiring A] [Algebra R A]

/-- The `R`-submodule spanned by products of generators `e : S → A` whose degrees under
`deg : S → Γ` sum to `n`. -/
def wordSpan (e : S → A) (deg : S → Γ) (n : Γ) : Submodule R A :=
  Submodule.span R {a | ∃ l : List S, (l.map deg).sum = n ∧ (l.map e).prod = a}

/-- The defining word-span formula for `wordSpan R e deg n`. -/
theorem wordSpan_def (e : S → A) (deg : S → Γ) (n : Γ) :
    wordSpan R e deg n =
      Submodule.span R {a | ∃ l : List S, (l.map deg).sum = n ∧ (l.map e).prod = a} :=
  (rfl)

variable {R}

/-- A submodule contains `wordSpan R e deg n` exactly when it contains every word of degree `n`. -/
theorem wordSpan_le_iff {e : S → A} {deg : S → Γ} (n : Γ) (p : Submodule R A) :
    wordSpan R e deg n ≤ p ↔
      ∀ l : List S, (l.map deg).sum = n → (l.map e).prod ∈ p := by
  rw [wordSpan_def, Submodule.span_le]
  exact ⟨fun h l hl => h ⟨l, hl, rfl⟩, by rintro h _ ⟨l, hl, rfl⟩; exact h l hl⟩

/-- A word in `e` lies in the `wordSpan` piece indexed by its total `deg`-degree. -/
theorem prod_mem_wordSpan (e : S → A) (deg : S → Γ) (l : List S) :
    (l.map e).prod ∈ wordSpan R e deg (l.map deg).sum :=
  Submodule.subset_span ⟨l, rfl, rfl⟩

/-- A word in `e` whose `deg`-degrees sum to `n` lies in `wordSpan R e deg n`. -/
theorem prod_mem_wordSpan_of_eq {e : S → A} {deg : S → Γ} {n : Γ} {l : List S}
    (hl : (l.map deg).sum = n) : (l.map e).prod ∈ wordSpan R e deg n :=
  hl ▸ prod_mem_wordSpan e deg l

/-- Structural induction on `wordSpan R e deg n` from generator words of degree `n` under zero,
addition, and `R`-scalar multiplication. -/
@[elab_as_elim]
theorem wordSpan_induction {e : S → A} {deg : S → Γ} {n : Γ} {x : A}
    {P : (x : A) → x ∈ wordSpan R e deg n → Prop} (hx : x ∈ wordSpan R e deg n)
    (word : ∀ l : List S, (hl : (l.map deg).sum = n) →
      P (l.map e).prod (prod_mem_wordSpan_of_eq hl))
    (zero : P 0 (Submodule.zero_mem _))
    (add : ∀ x y hx hy, P x hx → P y hy → P (x + y) (Submodule.add_mem _ hx hy))
    (smul : ∀ (r : R) x hx, P x hx → P (r • x) (Submodule.smul_mem _ r hx)) : P x hx :=
  Submodule.span_induction (by rintro _ ⟨l, hl, rfl⟩; exact word l hl) zero add smul hx

/-- Each generator `e s` lies in `wordSpan R e deg (deg s)`. -/
theorem mem_wordSpan_self (e : S → A) (deg : S → Γ) (s : S) :
    e s ∈ wordSpan R e deg (deg s) := by
  simpa using prod_mem_wordSpan e deg [s]

/-- The supremum of `wordSpan R e deg` over all degrees is the `R`-subalgebra generated by `e`. -/
theorem iSup_wordSpan (e : S → A) (deg : S → Γ) :
    ⨆ n, wordSpan R e deg n = (Algebra.adjoin R (Set.range e)).toSubmodule := by
  apply le_antisymm
  · refine iSup_le fun n => (wordSpan_le_iff n _).mpr fun l _ => ?_
    exact Subalgebra.list_prod_mem _ fun a ha => by
      obtain ⟨s, -, rfl⟩ := List.mem_map.mp ha
      exact Algebra.subset_adjoin ⟨s, rfl⟩
  · have hclosure : (Submonoid.closure (Set.range e) : Set A) =
        Set.range (fun l : List S => (l.map e).prod) := by
      rw [← FreeMonoid.mrange_lift, MonoidHom.coe_mrange]
      have hlift : (FreeMonoid.lift e : FreeMonoid S → A) =
          (fun l : List S => (l.map e).prod) ∘ FreeMonoid.toList :=
        funext (FreeMonoid.lift_apply e)
      rw [hlift]
      exact FreeMonoid.toListEquiv.surjective.range_comp _
    rw [Algebra.adjoin_eq_span, hclosure, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    exact Submodule.mem_iSup_of_mem (l.map deg).sum (prod_mem_wordSpan e deg l)

/-- Multiplication maps `wordSpan` pieces into the piece of the sum of their degrees. -/
instance wordSpan_gradedMonoid (e : S → A) (deg : S → Γ) :
    SetLike.GradedMonoid (wordSpan R e deg) where
  one_mem := Submodule.subset_span ⟨[], by simp, rfl⟩
  mul_mem := by
    intro m n a b ha hb
    have hmul : wordSpan R e deg m * wordSpan R e deg n ≤ wordSpan R e deg (m + n) := by
      rw [wordSpan_def, wordSpan_def, Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨_, ⟨l, hl, rfl⟩, _, ⟨t, ht, rfl⟩, rfl⟩
      simpa [hl, ht] using prod_mem_wordSpan e deg (l ++ t)
    exact hmul (Submodule.mul_mem_mul ha hb)

/-- An `R`-algebra homomorphism carrying each generator `e s` into `ℬ (σ (deg s))` carries
`wordSpan R e deg c` into `ℬ (σ c)`. -/
theorem map_mem_wordSpan {B S' Γ' F : Type*} [Semiring B] [Algebra R B]
    [AddMonoid Γ'] [SetLike S' B] [AddSubmonoidClass S' B] [SMulMemClass S' R B]
    {ℬ : Γ' → S'} [SetLike.GradedMonoid ℬ] [FunLike F A B] [AlgHomClass F R A B]
    (f : F) (σ : Γ →+ Γ') {e : S → A} {deg : S → Γ}
    (hf : ∀ s, f (e s) ∈ ℬ (σ (deg s))) {c : Γ} {x : A} (hx : x ∈ wordSpan R e deg c) :
    f x ∈ ℬ (σ c) := by
  induction hx using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨l, hl, rfl⟩ := h
    have hprod := SetLike.list_prod_map_mem_graded l (fun s => σ (deg s)) (fun s => f (e s))
      fun s _ => hf s
    have hsum : (l.map fun s => σ (deg s)).sum = σ c := by
      simpa only [List.map_map, Function.comp_def, map_list_sum] using congrArg σ hl
    simpa only [map_list_prod, List.map_map, Function.comp_def, hsum] using hprod
  | zero => simp [zero_mem]
  | add _ _ _ _ ha hb => simpa only [map_add] using add_mem ha hb
  | smul r _ _ ha => simpa only [map_smul] using SMulMemClass.smul_mem r ha

/-- An `R`-algebra homomorphism to `⨁ n, wordSpan R e deg n` with `DirectSum.coeAlgHom` as a left
inverse that places each generator `e s` in its `(deg s)`-th summand sends every element of
`wordSpan R e deg c` to its canonical summand injection. -/
theorem algHom_apply_of_mem_wordSpan {F : Type*} [DecidableEq Γ]
    {e : S → A} {deg : S → Γ}
    [FunLike F A (⨁ n, wordSpan R e deg n)] [AlgHomClass F R A (⨁ n, wordSpan R e deg n)]
    (f : F) (hcoe : ∀ x, DirectSum.coeAlgHom (wordSpan R e deg) (f x) = x)
    (hf : ∀ s, f (e s) ∈ DirectSum.summand R (fun n => ↥(wordSpan R e deg n)) (deg s))
    {c : Γ} {x : A} (hx : x ∈ wordSpan R e deg c) :
    f x = DirectSum.of (fun n => ↥(wordSpan R e deg n)) c ⟨x, hx⟩ := by
  obtain ⟨y, hy⟩ := DirectSum.mem_summand.mp <|
    map_mem_wordSpan (ℬ := DirectSum.summand R fun n => ↥(wordSpan R e deg n))
      f (AddMonoidHom.id Γ) hf hx
  rw [← hy]
  congr 1
  apply Subtype.ext
  simpa only [DirectSum.coeAlgHom_of, hcoe] using
    congrArg (DirectSum.coeAlgHom (wordSpan R e deg)) hy

end WordSpan

variable {Γ R A S : Type*} [AddMonoid Γ] [DecidableEq Γ]
  [CommSemiring R] [Semiring A] [Algebra R A]
  (𝒜 : Γ → Submodule R A) [_root_.GradedAlgebra 𝒜]

/-- A homogeneous generating family spans each graded piece by its words of exactly that total
degree. -/
theorem grade_eq_span_list_prod_map (e : S → A) (deg : S → Γ)
    (he : Algebra.adjoin R (Set.range e) = ⊤) (hhom : ∀ s, e s ∈ 𝒜 (deg s)) (n : Γ) :
    𝒜 n = Submodule.span R {a | ∃ l : List S, (l.map deg).sum = n ∧ (l.map e).prod = a} := by
  rw [← wordSpan_def]
  have hle (m : Γ) : wordSpan R e deg m ≤ 𝒜 m :=
    (wordSpan_le_iff m (𝒜 m)).mpr fun l hl =>
      hl ▸ SetLike.list_prod_map_mem_graded l deg e fun s _ => hhom s
  refine le_antisymm ?_ (hle n)
  intro x hx
  have hsup : x ∈ ⨆ m, wordSpan R e deg m := by
    rw [iSup_wordSpan, he, Algebra.top_toSubmodule]
    trivial
  have hproj : proj 𝒜 n x ∈ wordSpan R e deg n := by
    refine Submodule.iSup_induction (wordSpan R e deg)
      (motive := fun y => proj 𝒜 n y ∈ wordSpan R e deg n) hsup
      (fun m y hy => ?_) (by simp) (fun y z hy hz => by simpa only [map_add] using add_mem hy hz)
    by_cases hm : m = n
    · subst hm
      simpa only [proj_apply, DirectSum.decompose_of_mem_same 𝒜 (hle m hy)] using hy
    · simp only [proj_apply, DirectSum.decompose_of_mem_ne 𝒜 (hle m hy) hm, Submodule.zero_mem]
  simpa only [proj_apply, DirectSum.decompose_of_mem_same 𝒜 hx] using hproj

end TauCeti.GradedAlgebra
