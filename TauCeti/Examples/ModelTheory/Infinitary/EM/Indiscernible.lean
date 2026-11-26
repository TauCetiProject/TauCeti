/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.EM.Template
public import TauCeti.ModelTheory.Order
import Mathlib.Data.Finset.Sort

/-!
# Regression examples: indiscernible sequences, templates and the Morley seed

These examples exercise indiscernibility, templates and the Morley seed from a downstream module,
through public statements only.

Indiscernibility:
* in `(ℕ, <)` the identity sequence is indiscernible for `x₀ < x₁`;
* in `(ℤ, <)` the sequence `n ↦ (-1)ⁿ n` is not, since `x₀ < x₁` holds at `(0, 2)` and fails at
  `(0, 1)`;
* every sequence is indiscernible for every sentence;
* quantification does not preserve indiscernibility: in `(ℕ, <)` the identity sequence is
  indiscernible for `¬(x₁ < x₀)` but not for `∀ x₁, ¬(x₁ < x₀)`.

Templates:
* over a one-point index order the template of any sequence contains every formula of arity `2`,
  `⊥` included;
* for the identity sequence of a pure set `ℕ`, the template contains `x₀ ≠ x₁` and `x₀ = x₀` and
  omits `x₀ = x₁`, its relabelling `x₀ = x₂` and `⊥`; the template is coherent on the equations
  between variables, and the sequence realizes it there;
* a template declaring `x₀ = x₁` true at arity `2` and `x₀ = x₂` false at arity `3` is not coherent,
  and no sequence over an infinite index order realizes it on these two formulas.

The Morley seed:
* an injective sequence in any model of `φ` is indiscernible for the Morley seed of `φ`; for
  `φ = ⊤` both members lie in its template;
* a constant sequence over a two-point order is indiscernible for the Morley seed, with `x₀ ≠ x₁`
  false, so it does not realize the template of an injective sequence;
* over a one-point index order every sequence in a model of `φ` realizes the template of an
  injective sequence in a model of `φ` on the Morley seed.
-/

public section

namespace TauCeti.Examples.Indiscernible

open FirstOrder FirstOrder.Language

attribute [local instance] orderStructure Language.emptyStructure

/-- The increasing pair `(a, b)` of natural numbers. -/
def pair (a b : ℕ) (h : a < b) : Fin 2 ↪o ℕ :=
  .ofStrictMono ![a, b] <| Fin.strictMono_iff_lt_succ.2 fun i ↦ by
    simpa [Fin.fin_one_eq_zero i] using h

@[simp] theorem pair_zero (a b : ℕ) (h : a < b) : pair a b h 0 = a := by simp [pair]

@[simp] theorem pair_one (a b : ℕ) (h : a < b) : pair a b h 1 = b := by simp [pair]

/-- The variable in bound position `i`. -/
abbrev x {L : Language} {n : ℕ} (i : Fin n) : L.Term (Empty ⊕ Fin n) := Term.var (Sum.inr i)

/-- The formula `xᵢ < xⱼ` of the language of orders. -/
def lt {n : ℕ} (i j : Fin n) : Language.order.BoundedFormulaω Empty n :=
  ((x i).lt (x j)).toOmega

@[simp]
theorem realize_lt {M : Type*} [Preorder M] {n : ℕ} (i j : Fin n) (xs : Fin n → M) :
    (lt i j).Realize (Empty.elim : Empty → M) xs ↔ xs i < xs j := by
  simp [lt]

/-! ### Indiscernibility -/

-- In `(ℕ, <)` the identity sequence is indiscernible for `x₀ < x₁`.
example : IsIndiscernibleOn (id : ℕ → ℕ) {⟨2, lt 0 1⟩} := by
  simp [OrderEmbedding.lt_iff_lt]

-- In `(ℤ, <)` the sequence `0, -1, 2, -3, …` is not indiscernible for `x₀ < x₁`.
example : ¬IsIndiscernibleOn (fun n : ℕ ↦ (-1 : ℤ) ^ n * n) {⟨2, lt 0 1⟩} := by
  rw [isIndiscernibleOn_singleton]
  intro h
  have := (h (pair 0 2 (by decide)) (pair 0 1 (by decide))).1
  norm_num at this

-- Every sequence is indiscernible for every sentence.
example {L : Language} {M : Type*} [L.Structure M] (a : ℤ → M) (φ : L.Sentenceω) :
    IsIndiscernibleOn a {⟨0, φ⟩} :=
  isIndiscernibleOn_of_forall_fst_eq_zero a (by simp)

/-- The formula `¬(x₁ < x₀)`. -/
def notGt : Language.order.BoundedFormulaω Empty 2 :=
  (lt 1 0).not

-- In `(ℕ, <)` the identity sequence is indiscernible for `¬(x₁ < x₀)` ...
example : IsIndiscernibleOn (id : ℕ → ℕ) {⟨2, notGt⟩} := by
  simp [notGt, OrderEmbedding.lt_iff_lt]

-- ... but not for `∀ x₁, ¬(x₁ < x₀)`, which holds at `0` and fails at `1`.
example : ¬IsIndiscernibleOn (id : ℕ → ℕ) {⟨1, notGt.all⟩} := by
  rw [isIndiscernibleOn_singleton]
  intro h
  have := (h (.ofStrictMono (fun _ ↦ 0) (Subsingleton.strictMono _))
    (.ofStrictMono (fun _ ↦ 1) (Subsingleton.strictMono _))).1
  simp only [notGt, BoundedFormulaInf.realize_all, BoundedFormulaInf.realize_not,
    realize_lt] at this
  exact this (fun y ↦ by simp) 0 (by simp [Fin.snoc])

/-! ### Templates -/

-- Over a one-point index order the template of any sequence contains every formula of arity
-- `2`, `⊥` included: there are no increasing pairs.
example {L : Language} {M : Type*} [L.Structure M] (a : Unit → M)
    (φ : L.BoundedFormulaω Empty 2) : φ ∈ (L.templateOf a).formulas 2 ∧
      ⊥ ∈ (L.templateOf a).formulas 2 := by
  have (t : Fin 2 ↪o Unit) : False :=
    absurd (t.injective (Subsingleton.elim (t 0) (t 1))) (by decide)
  exact ⟨mem_templateOf_formulas.2 fun t ↦ (this t).elim,
    mem_templateOf_formulas.2 fun t ↦ (this t).elim⟩

/-- The equation `xᵢ = xⱼ`. -/
def eq {L : Language} {n : ℕ} (i j : Fin n) : L.BoundedFormulaω Empty n :=
  .equal (x i) (x j)

@[simp]
theorem realize_eq {L : Language} {M : Type*} [L.Structure M] {n : ℕ} (i j : Fin n)
    (xs : Fin n → M) : (eq (L := L) i j).Realize (Empty.elim : Empty → M) xs ↔ xs i = xs j := by
  simp [eq]

/-- The order embedding `0 ↦ 0, 1 ↦ 2` of bound positions. -/
def skipOne : Fin 2 ↪o Fin 3 :=
  .ofStrictMono ![0, 2] <| Fin.strictMono_iff_lt_succ.2 fun i ↦ by
    simp [Fin.fin_one_eq_zero i]

/-- Relabelling `x₀ = x₁` along `0 ↦ 0, 1 ↦ 2` gives `x₀ = x₂`. -/
theorem mapBound_eq_skipOne {L : Language} : (eq (L := L) 0 1).mapBound skipOne = eq 0 2 := by
  simp [eq, skipOne]

/-- The equations between two variables. -/
def equations (L : Language) : Set (Σ n, L.BoundedFormulaω Empty n) :=
  Set.range fun p : Σ n, Fin n × Fin n ↦ ⟨p.1, eq p.2.1 p.2.2⟩

-- The identity sequence of the pure set `ℕ` is indiscernible for the equations between
-- variables, so its template is coherent there and it realizes its template there.
example : (Language.empty.templateOf (id : ℕ → ℕ)).IsCoherentOn (equations _) ∧
    (Language.empty.templateOf (id : ℕ → ℕ)).RealizesOn (id : ℕ → ℕ) (equations _) := by
  have h : IsIndiscernibleOn (id : ℕ → ℕ) (equations Language.empty) := by
    refine isIndiscernibleOn_def.2 ?_
    rintro _ ⟨⟨n, i, j⟩, rfl⟩
    exact (isIndiscernibleOn_equal_var (a := (id : ℕ → ℕ)) Function.injective_id i j).realize_iff
      rfl
  exact ⟨h.isCoherentOn_templateOf, isIndiscernibleOn_iff_realizesOn_templateOf.1 h⟩

-- Its template contains `x₀ ≠ x₁` and `x₀ = x₀`, and omits `x₀ = x₁`, `x₀ = x₂` and `⊥`.
example : Language.empty.disEq ∈ (Language.empty.templateOf (id : ℕ → ℕ)).formulas 2 ∧
    eq 0 0 ∈ (Language.empty.templateOf (id : ℕ → ℕ)).formulas 2 ∧
    eq 0 1 ∉ (Language.empty.templateOf (id : ℕ → ℕ)).formulas 2 ∧
    (eq 0 1).mapBound skipOne ∉ (Language.empty.templateOf (id : ℕ → ℕ)).formulas 3 ∧
    ⊥ ∉ (Language.empty.templateOf (id : ℕ → ℕ)).formulas 2 := by
  refine ⟨disEq_mem_templateOf Function.injective_id, mem_templateOf_formulas.2 fun _ ↦ by simp,
    fun h ↦ ?_, fun h ↦ ?_,
    fun h ↦ by simpa using mem_templateOf_formulas.1 h (pair 0 1 (by decide))⟩
  · simpa using mem_templateOf_formulas.1 h (pair 0 1 (by decide))
  · rw [mapBound_eq_skipOne, mem_templateOf_formulas] at h
    simpa using h (Finset.orderEmbOfFin {0, 1, 2} (by decide))

/-- A template declaring every formula of arity `2` true and every other formula false; in
particular `x₀ = x₁` is declared true and `x₀ = x₂` false. -/
def arityTwo (L : Language) : L.EMTemplate :=
  ⟨fun n ↦ {_φ | n = 2}⟩

-- It is not coherent on `x₀ = x₁` ...
example : ¬(arityTwo Language.empty).IsCoherentOn {⟨2, eq 0 1⟩} := fun h ↦ by
  simpa [arityTwo] using h.mapBound_mem_iff rfl skipOne

-- ... and no sequence over an infinite index order realizes it on `x₀ = x₁` and `x₀ = x₂`.
example {M : Type*} {J : Type*} [LinearOrder J] [Infinite J] (a : J → M) :
    ¬(arityTwo Language.empty).RealizesOn a {⟨2, eq 0 1⟩, ⟨3, eq 0 2⟩} := fun h ↦ by
  have := h.mapBound_mem_iff (φ := eq 0 1) (r := skipOne) (by simp)
    (by simp [mapBound_eq_skipOne])
  simp [arityTwo] at this

/-! ### The Morley seed -/

-- An injective sequence in any model of `φ` is indiscernible for the Morley seed of `φ`.
example {L : Language} {M : Type*} [L.Structure M] {J : Type*} [LinearOrder J] {a : J → M}
    (ha : Function.Injective a) (φ : L.Sentenceω) : IsIndiscernibleOn a (morleySeed φ) :=
  isIndiscernibleOn_morleySeed φ ha

-- For `φ = ⊤`, both members of the Morley seed lie in the template of an injective sequence.
example {L : Language} {M : Type*} [L.Structure M] {J : Type*} [LinearOrder J] {a : J → M}
    (ha : Function.Injective a) :
    ⊤ ∈ (L.templateOf a).formulas 0 ∧ L.disEq ∈ (L.templateOf a).formulas 2 :=
  ⟨mem_templateOf_formulas_zero_iff.2 (by simp [SentenceInf.realize_def]),
    disEq_mem_templateOf ha⟩

-- A constant sequence over a two-point order is indiscernible for the Morley seed, with
-- `x₀ ≠ x₁` false, so it does not realize the template of an injective sequence.
example {L : Language} {M N : Type*} [L.Structure M] [L.Structure N]
    {J : Type*} [LinearOrder J] {a : J → M} (ha : Function.Injective a) (φ : L.Sentenceω)
    (c : N) :
    IsIndiscernibleOn (fun _ : Fin 2 ↦ c) (morleySeed φ) ∧
      L.disEq ∉ (L.templateOf fun _ : Fin 2 ↦ c).formulas 2 ∧
      ¬(L.templateOf a).RealizesOn (fun _ : Fin 2 ↦ c) (morleySeed φ) := by
  refine ⟨?_, fun h ↦ by simpa using mem_templateOf_formulas.1 h (OrderIso.refl _).toOrderEmbedding,
    fun h ↦ ?_⟩
  · rw [morleySeed_def, isIndiscernibleOn_insert]
    exact ⟨isIndiscernibleOn_of_forall_fst_eq_zero _ (by simp), by simp⟩
  · have := h.injective (by simp) (disEq_mem_templateOf ha)
    exact absurd (this (a₁ := 0) (a₂ := 1) rfl) (by decide)

-- Over a one-point index order, every sequence in a model of `φ` realizes the template of an
-- injective sequence in a model of `φ` on the Morley seed: there are no increasing pairs.
example {L : Language} {M N : Type*} [L.Structure M] [L.Structure N] {J : Type*}
    [LinearOrder J] {a : J → M} (φ : L.Sentenceω) (hM : SentenceInf.Realize φ M)
    (hN : SentenceInf.Realize φ N) (b : Unit → N) :
    (L.templateOf a).RealizesOn b (morleySeed φ) := by
  refine EMTemplate.realizesOn_def.2 fun p hp t ↦ ?_
  rcases mem_morleySeed_iff.1 hp with rfl | rfl
  · refine ⟨fun _ ↦ mem_templateOf_formulas_zero_iff.2 hM, fun _ ↦ ?_⟩
    rw [SentenceInf.realize_def, FormulaInf.realize_def] at hN
    rwa [Subsingleton.elim (b ∘ t) default]
  · exact absurd (t.injective (Subsingleton.elim (t 0) (t 1))) (by simp)

end TauCeti.Examples.Indiscernible
