/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Satisfiability
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite

/-!
# Regression examples: satisfiability and entailment of `L_{ω₁ω}` theories

These examples exercise satisfiability and entailment from a downstream module, through public
statements only:

* **`L_{ω₁ω}` is not compact.** In the language `{0, S, c}`, the theory consisting of
  `⋁ₖ c = Sᵏ0` and of `c ≠ Sᵏ0` for every `k` is unsatisfiable, while each of its finite subsets
  has a model, namely `ℕ` with `c` interpreted as a large number. Consequently the union of an
  increasing chain of satisfiable theories need not be satisfiable.
* a theory containing `⊥` is unsatisfiable and entails every sentence;
* first-order entailment between sentences is recovered from `L_{ω₁ω}` entailment.
-/

@[expose] public section

namespace TauCeti

open FirstOrder FirstOrder.Language Filter

namespace NonCompactnessExample

/-- The function symbols of the language `{0, S, c}`. -/
inductive Func : ℕ → Type
  | zero : Func 0
  | const : Func 0
  | succ : Func 1

/-- The language `{0, S, c}`, with no relation symbols. -/
abbrev lang : Language.{0, 0} :=
  ⟨Func, fun _ => Empty⟩

/-- The numeral `Sᵏ0`, as a closed term. -/
def numeral : ℕ → lang.Term (Empty ⊕ Fin 0)
  | 0 => .func Func.zero default
  | k + 1 => .func Func.succ ![numeral k]

/-- The sentence `c = Sᵏ0`. -/
def eqNumeral (k : ℕ) : lang.Sentenceω :=
  .equal (.func Func.const default) (numeral k)

/-- The theory `{⋁ₖ c = Sᵏ0} ∪ {c ≠ Sᵏ0 : k ∈ ℕ}`. -/
def theory : lang.Theoryω :=
  insert (.iSup eqNumeral) (Set.range fun k => (eqNumeral k).not)

/-- The natural numbers, interpreting `c` as `N`. -/
def NatWith (_N : ℕ) : Type :=
  ℕ

instance (N : ℕ) : Nonempty (NatWith N) :=
  ⟨(0 : ℕ)⟩

instance (N : ℕ) : lang.Structure (NatWith N) where
  funMap
    | .zero, _ => (0 : ℕ)
    | .const, _ => N
    | .succ, x => Nat.succ (x 0)
  RelMap r := Empty.elim r

/-- In `NatWith N`, the numeral `Sᵏ0` denotes `k`. -/
theorem realize_numeral (N k : ℕ) (v : Empty ⊕ Fin 0 → NatWith N) :
    (numeral k).realize v = (k : ℕ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg Nat.succ ih

/-- `NatWith N` satisfies `c = Sᵏ0` exactly when `N = k`. -/
theorem realize_eqNumeral_iff (N k : ℕ) :
    SentenceInf.Realize (eqNumeral k) (NatWith N) ↔ N = k := by
  rw [SentenceInf.realize_def, FormulaInf.realize_def, eqNumeral,
    BoundedFormulaInf.realize_equal, realize_numeral]
  exact Iff.rfl

/-- `NatWith N` satisfies `c ≠ Sᵏ0` exactly when `N ≠ k`. -/
theorem realize_not_eqNumeral_iff (N k : ℕ) :
    SentenceInf.Realize (eqNumeral k).not (NatWith N) ↔ N ≠ k := by
  rw [ne_eq, ← realize_eqNumeral_iff]
  simp only [SentenceInf.realize_def, FormulaInf.realize_def, BoundedFormulaInf.realize_not]

/-- Every `NatWith N` satisfies `⋁ₖ c = Sᵏ0`. -/
theorem realize_iSup_eqNumeral (N : ℕ) :
    SentenceInf.Realize (.iSup eqNumeral) (NatWith N) := by
  have h := (realize_eqNumeral_iff N N).2 rfl
  simp only [SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_iSup] at h ⊢
  exact ⟨N, h⟩

/-- The theory is unsatisfiable: a model satisfies `c = Sᵏ0` for some `k`, against `c ≠ Sᵏ0`. -/
theorem not_isSatisfiable : ¬ theory.IsSatisfiable := by
  rw [Theoryω.isSatisfiable_iff]
  rintro ⟨M, _, _, hM⟩
  rw [theory, Theoryω.model_insert_iff] at hM
  obtain ⟨hdisj, hneg⟩ := hM
  simp only [SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_iSup] at hdisj
  obtain ⟨k, hk⟩ := hdisj
  have := hneg.realize_of_mem (Set.mem_range_self k)
  simp only [SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_not] at this
  exact this hk

/-- Each sentence of the theory holds in `ℕ` once `c` is interpreted as a large enough number. -/
theorem eventually_realize {ψ : lang.Sentenceω} (hψ : ψ ∈ theory) :
    ∀ᶠ N in atTop, SentenceInf.Realize ψ (NatWith N) := by
  obtain rfl | ⟨k, rfl⟩ := hψ
  · exact Eventually.of_forall realize_iSup_eqNumeral
  · filter_upwards [eventually_gt_atTop k] with N hN
    exact (realize_not_eqNumeral_iff N k).2 hN.ne'

end NonCompactnessExample

open NonCompactnessExample

-- The theory `{⋁ₖ c = Sᵏ0} ∪ {c ≠ Sᵏ0 : k ∈ ℕ}` is unsatisfiable.
example : ¬ theory.IsSatisfiable :=
  not_isSatisfiable

-- Every finite subset of `{⋁ₖ c = Sᵏ0} ∪ {c ≠ Sᵏ0 : k ∈ ℕ}` is satisfiable.
example (T₀ : Finset lang.Sentenceω) (hT₀ : (T₀ : lang.Theoryω) ⊆ theory) :
    Theoryω.IsSatisfiable (T₀ : lang.Theoryω) := by
  obtain ⟨N, hN⟩ :=
    ((eventually_all_finset T₀).2 fun ψ hψ => eventually_realize (hT₀ hψ)).exists
  exact Theoryω.Model.isSatisfiable (M := NatWith N) (Theoryω.model_iff.2 hN)

-- The union of an increasing chain of satisfiable `L_{ω₁ω}` theories need not be satisfiable.
example : ∃ S : ℕ → lang.Theoryω, Monotone S ∧ (∀ n, (S n).IsSatisfiable) ∧
    ¬ Theoryω.IsSatisfiable (⋃ n, S n) := by
  refine ⟨fun n => insert (.iSup eqNumeral) ((fun k => (eqNumeral k).not) '' Set.Iio n),
    fun m n hmn => Set.insert_subset_insert (Set.image_mono (Set.Iio_subset_Iio hmn)),
    fun n => Theoryω.Model.isSatisfiable (M := NatWith n) ?_,
    fun h => not_isSatisfiable (h.mono ?_)⟩
  · rw [Theoryω.model_insert_iff, Theoryω.model_iff, Set.forall_mem_image]
    exact ⟨realize_iSup_eqNumeral n, fun k hk => (realize_not_eqNumeral_iff n k).2
      (Set.mem_Iio.1 hk).ne'⟩
  · rintro ψ (rfl | ⟨k, rfl⟩)
    · exact Set.mem_iUnion.2 ⟨0, Set.mem_insert _ _⟩
    · exact Set.mem_iUnion.2 ⟨k + 1, Set.mem_insert_of_mem _ ⟨k, Set.mem_Iio.2 k.lt_succ_self,
        rfl⟩⟩

-- A theory containing `⊥` is unsatisfiable and entails every sentence.
example {L : Language} {T : L.Theoryω} (h : ⊥ ∈ T) (φ : L.Sentenceω) :
    ¬ T.IsSatisfiable ∧ T.Entails φ := by
  have hbot : T.Entails ⊥ := Theoryω.entails_of_mem h
  have hT : ¬ T.IsSatisfiable := fun hs => Theoryω.isSatisfiable_iff_not_entails_bot.1 hs hbot
  exact ⟨hT, Theoryω.entails_iff_not_isSatisfiable.2 fun hs =>
    hT (hs.mono (Set.subset_insert _ _))⟩

-- First-order entailment between sentences is `L_{ω₁ω}` entailment of their images.
example {L : Language} (φ : L.Sentence) : {φ} ⊨ᵇ φ :=
  Sentenceω.entails_toOmega_iff.1 (Sentenceω.Entails.refl _)

end TauCeti
