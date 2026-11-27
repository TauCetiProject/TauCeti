/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.EM.Template
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Set.Finite.Lattice

/-!
# Regression example: realizability of templates is not of finite character

Over unary predicates `Pᵢ` (`i : ℕ`), interpret `Pᵢ x` on `ℕ` as `i ≤ x`, so that `x` has height
`x`, and let `a` be the identity sequence. Every `Pᵢ(x₀)` is eventually true along `a`, while
`⋀ᵢ Pᵢ(x₀)` is never true. The template declaring every formula true except `⋀ᵢ Pᵢ(x₀)` therefore
records, on `Δ = {Pᵢ(x₀) | i} ∪ {⋀ᵢ Pᵢ(x₀)}`, what is eventually true along `a`. Each finite part of
`Δ` is realized by a tail of `a`, but no sequence over a nonempty index order, in any structure,
realizes the template on all of `Δ`. So `L_{ω₁ω}` has no compactness for templates, and templates
used for stretching must carry witness conditions instead.

## References

* C. Freer, `cameronfreer/infinitary-logic` (Apache-2.0) at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`: the same height counterexample is
  `T_counterexample`, over `HeightCex.Lang`, in
  `InfinitaryLogic/Conditional/MorleyHanfTransfer.lean`.
-/

public section

namespace TauCeti.Examples.Height

open FirstOrder FirstOrder.Language Filter

/-- The language of the unary predicates `Pᵢ`, `i : ℕ`. Its body is exposed so that its symbol
types reduce in the definitions below. -/
@[expose] def heightLang : Language :=
  ⟨fun _ ↦ Empty, fun k ↦ PLift (k = 1) × ℕ⟩

/-- The structure on `ℕ` in which `Pᵢ x` holds when `i ≤ x`. -/
instance : heightLang.Structure ℕ where
  funMap f := Empty.elim f
  RelMap R xs := R.2 ≤ xs ⟨0, by rw [R.1.down]; exact Nat.one_pos⟩

/-- The relation symbol `Pᵢ`. -/
def Psym (i : ℕ) : heightLang.Relations 1 :=
  (⟨rfl⟩, i)

/-- The formula `Pᵢ(x₀)`. -/
def P (i : ℕ) : heightLang.BoundedFormulaω Empty 1 :=
  .rel (Psym i) ![Term.var (Sum.inr 0)]

/-- The formula `⋀ᵢ Pᵢ(x₀)`. -/
def allP : heightLang.BoundedFormulaω Empty 1 :=
  .iInf P

theorem realize_P {N : Type*} [heightLang.Structure N] (i : ℕ) (xs : Fin 1 → N) :
    (P i).Realize (Empty.elim : Empty → N) xs ↔
      Structure.RelMap (Psym i) xs := by
  rw [P, BoundedFormulaInf.realize_rel]
  exact iff_of_eq (congrArg _ (funext fun j ↦ by simp [Fin.fin_one_eq_zero j]))

/-- `Pᵢ` holds at `x` in `ℕ` exactly when `i ≤ x`. This is the instance's `RelMap` unfolded: the
relation symbol `Psym i` carries `i`, and the index `⟨0, _⟩` it reads is `(0 : Fin 1)`. -/
@[simp]
theorem relMap_Psym_nat (i : ℕ) (xs : Fin 1 → ℕ) : Structure.RelMap (Psym i) xs ↔ i ≤ xs 0 :=
  Iff.rfl

@[simp]
theorem realize_P_nat (i : ℕ) (xs : Fin 1 → ℕ) :
    (P i).Realize (Empty.elim : Empty → ℕ) xs ↔ i ≤ xs 0 := by
  rw [realize_P, relMap_Psym_nat]

/-- The formulas `Pᵢ(x₀)` and `⋀ᵢ Pᵢ(x₀)`. -/
def Δ : Set (Σ n, heightLang.BoundedFormulaω Empty n) :=
  insert ⟨1, allP⟩ (Set.range fun i ↦ ⟨1, P i⟩)

/-- The template declaring every formula true except `⋀ᵢ Pᵢ(x₀)`. -/
def Φ : heightLang.EMTemplate :=
  ⟨fun n ↦ {φ | (⟨n, φ⟩ : Σ n, heightLang.BoundedFormulaω Empty n) ≠ ⟨1, allP⟩}⟩

theorem P_mem_Φ (i : ℕ) : P i ∈ Φ.formulas 1 := by
  simp [Φ, P, allP]

theorem allP_notMem_Φ : allP ∉ Φ.formulas 1 := by
  simp [Φ]

/-- Every `Pᵢ(x₀)` is eventually true along the identity sequence. -/
theorem eventually_realize_P (i : ℕ) :
    ∀ᶠ k in atTop, (P i).Realize (Empty.elim : Empty → ℕ) ![k] :=
  eventually_atTop.2 ⟨i, fun k hk ↦ by simpa using hk⟩

/-- `⋀ᵢ Pᵢ(x₀)` is never true in `ℕ`. -/
theorem not_realize_allP (xs : Fin 1 → ℕ) : ¬allP.Realize (Empty.elim : Empty → ℕ) xs := by
  simp only [allP, BoundedFormulaInf.realize_iInf, realize_P_nat, not_forall, not_le]
  exact ⟨xs 0 + 1, Nat.lt_succ_self _⟩

/-- **Finite parts are realized.** Every finite part of `Δ` is realized by a tail of the identity
sequence of `ℕ`. -/
theorem exists_realizesOn_of_finite {Δ₀ : Set (Σ n, heightLang.BoundedFormulaω Empty n)}
    (hΔ₀ : Δ₀.Finite) (hsub : Δ₀ ⊆ Δ) : ∃ N : ℕ, Φ.RealizesOn (fun k : ℕ ↦ k + N) Δ₀ := by
  -- Only finitely many `Pᵢ(x₀)` occur in `Δ₀`; shift past all their indices.
  have hfin : {i | (⟨1, P i⟩ : Σ n, heightLang.BoundedFormulaω Empty n) ∈ Δ₀}.Finite :=
    hΔ₀.preimage fun i _ j _ hij ↦ by
      obtain ⟨-, h, -⟩ := BoundedFormulaInf.rel.inj (by simpa only [P, Sigma.mk.injEq, heq_eq_eq,
        true_and] using hij)
      exact congrArg (fun R : heightLang.Relations 1 ↦ R.2) (eq_of_heq h)
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine ⟨N, EMTemplate.realizesOn_def.2 fun p hp t ↦ ?_⟩
  rcases hsub hp with rfl | ⟨i, rfl⟩
  · exact iff_of_false (not_realize_allP _) allP_notMem_Φ
  · exact iff_of_true (by simpa using (hN hp).trans (Nat.le_add_left _ _)) (P_mem_Φ i)

/-- **The whole is not realized.** No sequence over a nonempty index order, in any structure,
realizes the template on `Δ`. -/
theorem not_realizesOn {K : Type*} [LinearOrder K] [Nonempty K] {N : Type*}
    [heightLang.Structure N] (b : K → N) : ¬Φ.RealizesOn b Δ := fun h ↦ by
  let t : Fin 1 ↪o K := .ofStrictMono (fun _ ↦ Classical.arbitrary K) (Subsingleton.strictMono _)
  have hP (i : ℕ) := (h.realize_iff (Set.mem_insert_of_mem _ ⟨i, rfl⟩) t).2 (P_mem_Φ i)
  have hall := (h.realize_iff (Set.mem_insert _ _) t).1
  exact allP_notMem_Φ (hall (by simpa [allP] using hP))

end TauCeti.Examples.Height
