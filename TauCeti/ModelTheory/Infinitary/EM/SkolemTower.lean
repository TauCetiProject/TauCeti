/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.LanguageMap
public import TauCeti.ModelTheory.Infinitary.SubstBounds

/-!
# One step of the Skolem tower

For a set `Γ` of `Lω₁ω` formulas in bound positions, the **Skolem language** `skolemLanguage Γ` has
one `n`-ary function symbol `f_ψ` for each formula `ψ ∈ Γ` of arity `n + 1`, and no relation
symbols. The last bound position of `ψ` is the witnessed variable. When `Γ` is countable, so are the
new symbols.

In the sum `L.sum (skolemLanguage Γ)`, the **witness formula** of `ψ` is
`∃y ψ(xs, y) → ψ(xs, f_ψ(xs))` in the bound tuple `xs`, of arity `n`, and the **witness axiom** is
its universal closure. A structure satisfies the witness axiom exactly when `f_ψ` supplies a
witness at every tuple where one exists. For `n = 0`, the symbol `f_ψ` is a constant, and the
witness axiom says that the constant witnesses `∃y ψ(y)` when that holds.

This is one successor step `L_k ↦ L_{k+1}` of the countable Skolem tower.

## Main definitions

* `FirstOrder.Language.skolemLanguage Γ`: the Skolem symbols of a set of formulas.
* `FirstOrder.Language.skolemWitnessFormula f`: the witness formula of a Skolem symbol.
* `FirstOrder.Language.skolemWitnessAxiom f`: its universal closure, a sentence.

## Main results

* `FirstOrder.Language.countable_skolemLanguage_functions`: the Skolem symbols of a countable set of
  formulas are countable.
* `FirstOrder.Language.realize_skolemWitnessFormula` and
  `FirstOrder.Language.realize_skolemWitnessAxiom`: the witness axiom holds exactly when the Skolem
  function supplies a witness wherever one exists.
-/

public section

universe u v w

namespace FirstOrder.Language

open Structure

variable {L : Language.{u, v}}

/-- The **Skolem language** of a set `Γ` of `Lω₁ω` formulas in bound positions: one `n`-ary
function symbol for each formula of `Γ` of arity `n + 1`, witnessing its last bound position, and
no relation symbols. -/
@[expose]
def skolemLanguage (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) : Language.{max u v, 0} where
  Functions n :=
    {ψ : L.BoundedFormulaω Empty (n + 1) // (⟨n + 1, ψ⟩ : Σ m, L.BoundedFormulaω Empty m) ∈ Γ}
  Relations _ := Empty

variable {Γ : Set (Σ n, L.BoundedFormulaω Empty n)}

/-- The Skolem language has no relation symbols. -/
instance isAlgebraic_skolemLanguage : (skolemLanguage Γ).IsAlgebraic :=
  fun _ => inferInstanceAs (IsEmpty Empty)

/-- The **countability** of the Skolem symbols: a countable set of formulas has countably many
Skolem symbols. -/
theorem countable_skolemLanguage_functions (hΓ : Γ.Countable) :
    Countable (Σ n, (skolemLanguage Γ).Functions n) := by
  have : Countable Γ := hΓ.to_subtype
  refine Function.Injective.countable
    (f := fun f : Σ n, (skolemLanguage Γ).Functions n =>
      (⟨⟨f.1 + 1, f.2.val⟩, f.2.property⟩ : Γ)) ?_
  rintro ⟨n, f⟩ ⟨m, g⟩ h
  simp only [Subtype.mk.injEq, Sigma.mk.injEq, Nat.add_right_cancel_iff] at h
  obtain ⟨rfl, h⟩ := h
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext (eq_of_heq h)))

/-- The term `f(x₀, …, x_{n-1})` of a Skolem symbol applied to the bound variables. -/
def skolemTerm {n : ℕ} (f : (skolemLanguage Γ).Functions n) :
    (L.sum (skolemLanguage Γ)).Term (Empty ⊕ Fin n) :=
  Term.func (Sum.inr f : (L.sum (skolemLanguage Γ)).Functions n) fun i => Term.var (Sum.inr i)

/-- The **witness formula** of a Skolem symbol `f` for `ψ ∈ Γ` of arity `n + 1`: the arity-`n`
formula `∃y ψ(xs, y) → ψ(xs, f(xs))` of `L.sum (skolemLanguage Γ)`, in the bound tuple `xs`. -/
def skolemWitnessFormula {n : ℕ} (f : (skolemLanguage Γ).Functions n) :
    (L.sum (skolemLanguage Γ)).BoundedFormulaω Empty n :=
  let ψ := LHom.sumInl.onBoundedFormulaInf f.val
  ψ.ex.imp (ψ.substBounds (Fin.lastCases (skolemTerm f) fun i => Term.var (Sum.inr i)))

/-- The **witness axiom** of a Skolem symbol: the universal closure of its witness formula. -/
def skolemWitnessAxiom {n : ℕ} (f : (skolemLanguage Γ).Functions n) :
    (L.sum (skolemLanguage Γ)).Sentenceω :=
  (skolemWitnessFormula f).alls

variable {M : Type w} [L.Structure M] [(skolemLanguage Γ).Structure M]

/-- The witness formula holds at a tuple exactly when the Skolem function supplies a witness there,
if one exists. -/
theorem realize_skolemWitnessFormula {n : ℕ} (f : (skolemLanguage Γ).Functions n)
    (xs : Fin n → M) :
    (skolemWitnessFormula f).Realize Empty.elim xs ↔
      ((∃ y, f.val.Realize Empty.elim (Fin.snoc xs y)) →
        f.val.Realize Empty.elim (Fin.snoc xs (funMap f xs))) := by
  have hσ : (fun i : Fin (n + 1) =>
      (Fin.lastCases (skolemTerm f) (fun i => Term.var (Sum.inr i)) i :
        (L.sum (skolemLanguage Γ)).Term (Empty ⊕ Fin n)).realize (Sum.elim Empty.elim xs)) =
      Fin.snoc xs (funMap f xs) := by
    funext i
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.lastCases_last, Fin.snoc_last]
      rfl
    | cast i => simp
  simp only [skolemWitnessFormula, BoundedFormulaInf.realize_imp, BoundedFormulaInf.realize_ex,
    BoundedFormulaInf.realize_substBounds, hσ, LHom.realize_onBoundedFormulaInf]

/-- **The witness axiom.** A structure satisfies the witness axiom of `f` exactly when, at every
tuple where the formula `ψ` of `f` has a witness, the Skolem function supplies one. -/
theorem realize_skolemWitnessAxiom {n : ℕ} (f : (skolemLanguage Γ).Functions n) :
    SentenceInf.Realize (skolemWitnessAxiom f) M ↔ ∀ xs : Fin n → M,
      (∃ y, f.val.Realize Empty.elim (Fin.snoc xs y)) →
        f.val.Realize Empty.elim (Fin.snoc xs (funMap f xs)) := by
  simp only [skolemWitnessAxiom, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_alls, realize_skolemWitnessFormula]

end FirstOrder.Language
