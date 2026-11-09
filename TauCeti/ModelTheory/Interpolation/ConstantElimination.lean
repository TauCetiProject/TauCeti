/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Polarity
public import TauCeti.ModelTheory.Infinitary.Satisfiability

/-!
# Polarity-preserving elimination of constants from separators

A sentence separating two theories may mention auxiliary constants. If a constant is absent
from the left theory, universally quantifying its abstraction preserves separation. Dually,
if it is absent from the right theory, existential quantification preserves separation.
Neither operation changes either polarity of relation occurrences or adds function symbols.
These are the constant-elimination steps needed when interpolation arguments introduce fresh
constants as quantifier witnesses.

The finite elimination theorem removes any finite set of extra constants from a separator,
provided the left theory already uses only the allowed constants. The theories need not be
finite, countable, satisfiable, or relational.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, §4.2.
* E. G. K. López-Escobar, *An interpolation theorem for denumerably long formulas*,
  Fundamenta Mathematicae **57** (1965), 253–272.
* The finite elimination argument generalizes the unsigned argument in
  `TauCeti.ModelTheory.Interpolation.Craig`, following the constant-abstraction method of
  `cameronfreer/infinitary-logic`, checkpoint `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  `InfinitaryLogic/Methods/Interpolation/ConstantElimination.lean`. Here both signed occurrence
  sets are preserved exactly, constants may have any index type, and universes are arbitrary.
-/

public section

universe u v uγ

namespace FirstOrder.Language

open BoundedFormulaInf

variable {L : Language.{u, v}} {γ : Type uγ} [DecidableEq γ]

namespace Theoryω

/-- An entailed sentence can be universally quantified over a constant absent from the theory. -/
theorem Entails.all_abstractConst {Γ : L[[γ]].Theoryω} {θ : L[[γ]].Sentenceω}
    (h : Γ.Entails θ) {c : γ} (hc : ∀ φ ∈ Γ, c ∉ φ.constantSupport) :
    Γ.Entails (abstractConst c θ).all := by
  refine entails_iff.2 fun M iM _ hM => ?_
  let S : L.Structure M := (L.lhomWithConstants γ).reduct M
  let e : γ → M := fun d => (L.con d : M)
  have hS : iM = @withConstantsStructure L M S γ (constantsOn.structure e) :=
    (withConstantsStructure_reduct_eq (L := L) (γ := γ) M).symm
  rw [hS] at hM ⊢
  simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_all]
  intro m
  have hReal := entails_iff.1 h
  apply (realize_abstractConst e c θ Empty.elim default m).2
  simpa only [SentenceInf.realize_def, FormulaInf.realize_def] using
    @hReal M
      (@withConstantsStructure L M S γ (constantsOn.structure (Function.update e c m)))
      ‹Nonempty M› ((model_constantsOn_update_iff e m hc).2 hM)

/-- Refuting a sentence also refutes its existential abstraction over a constant absent from
the theory. -/
theorem Entails.not_ex_abstractConst {Γ : L[[γ]].Theoryω} {θ : L[[γ]].Sentenceω}
    (h : Γ.Entails θ.not) {c : γ} (hc : ∀ φ ∈ Γ, c ∉ φ.constantSupport) :
    Γ.Entails (abstractConst c θ).ex.not := by
  have hall := h.all_abstractConst hc
  refine entails_iff.2 fun M _ _ hM => ?_
  have hr := (entails_iff.1 hall) M hM
  simpa [SentenceInf.realize_def, FormulaInf.realize_def, realize_all, realize_ex,
    realize_not] using hr

/-- Universally abstracting a constant absent from the left theory preserves a separator. -/
theorem entails_all_abstractConst_separator {Γ Δ : L[[γ]].Theoryω}
    {θ : L[[γ]].Sentenceω} {c : γ} (hc : ∀ φ ∈ Γ, c ∉ φ.constantSupport)
    (hΓ : Γ.Entails θ) (hΔ : Δ.Entails θ.not) :
    Γ.Entails (abstractConst c θ).all ∧ Δ.Entails (abstractConst c θ).all.not := by
  refine ⟨hΓ.all_abstractConst hc, entails_iff.2 fun M iM _ hM => ?_⟩
  let S : L.Structure M := (L.lhomWithConstants γ).reduct M
  let e : γ → M := fun d => (L.con d : M)
  have hS : iM = @withConstantsStructure L M S γ (constantsOn.structure e) :=
    (withConstantsStructure_reduct_eq (L := L) (γ := γ) M).symm
  have hn := (entails_iff.1 hΔ) M hM
  simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_not] at hn
  rw [hS] at hn ⊢
  simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_not, realize_all]
  intro hall
  have hr := (realize_abstractConst e c θ Empty.elim default (e c)).1 (hall (e c))
  rw [Function.update_eq_self] at hr
  exact hn hr

/-- Existentially abstracting a constant absent from the right theory preserves a separator. -/
theorem entails_ex_abstractConst_separator {Γ Δ : L[[γ]].Theoryω}
    {θ : L[[γ]].Sentenceω} {c : γ} (hc : ∀ φ ∈ Δ, c ∉ φ.constantSupport)
    (hΓ : Γ.Entails θ) (hΔ : Δ.Entails θ.not) :
    Γ.Entails (abstractConst c θ).ex ∧ Δ.Entails (abstractConst c θ).ex.not := by
  refine ⟨entails_iff.2 fun M iM _ hM => ?_, hΔ.not_ex_abstractConst hc⟩
  let S : L.Structure M := (L.lhomWithConstants γ).reduct M
  let e : γ → M := fun d => (L.con d : M)
  have hS : iM = @withConstantsStructure L M S γ (constantsOn.structure e) :=
    (withConstantsStructure_reduct_eq (L := L) (γ := γ) M).symm
  have hr := (entails_iff.1 hΓ) M hM
  simp only [SentenceInf.realize_def, FormulaInf.realize_def] at hr
  rw [hS] at hr ⊢
  simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_ex]
  refine ⟨e c, (realize_abstractConst e c θ Empty.elim default (e c)).2 ?_⟩
  rw [Function.update_eq_self]
  exact hr

omit [DecidableEq γ] in
/-- Remove finitely many extra constants from a separator without changing either relation
polarity or adding function symbols. Only the left theory's support must lie in the allowed set.
The allowed set itself can be infinite. -/
theorem exists_separator_constantSupport_subset {Γ Δ : L[[γ]].Theoryω} {K E : Set γ}
    (hE : E.Finite) (hΓK : ∀ φ ∈ Γ, φ.constantSupport ⊆ K)
    {θ : L[[γ]].Sentenceω} (hθ : θ.constantSupport ⊆ K ∪ E)
    (hΓ : Γ.Entails θ) (hΔ : Δ.Entails θ.not) :
    ∃ χ : L[[γ]].Sentenceω, (∀ s, χ.relationsInSigned s = θ.relationsInSigned s) ∧
      χ.functionsIn ⊆ θ.functionsIn ∧ χ.constantSupport ⊆ K ∧
      Γ.Entails χ ∧ Δ.Entails χ.not := by
  classical
  have hfin : (E \ K).Finite := hE.subset Set.sdiff_subset
  suffices ∀ S : Finset γ, (∀ c ∈ S, c ∉ K) → ∀ θ : L[[γ]].Sentenceω,
      θ.constantSupport ⊆ K ∪ ↑S → Γ.Entails θ → Δ.Entails θ.not →
      ∃ χ : L[[γ]].Sentenceω, (∀ s, χ.relationsInSigned s = θ.relationsInSigned s) ∧
        χ.functionsIn ⊆ θ.functionsIn ∧ χ.constantSupport ⊆ K ∧
        Γ.Entails χ ∧ Δ.Entails χ.not from
    this hfin.toFinset (fun _ hc => (hfin.mem_toFinset.1 hc).2) θ
      (fun c hc => if h : c ∈ K then .inl h else
        .inr (hfin.mem_toFinset.2 ⟨(hθ hc).resolve_left h, h⟩)) hΓ hΔ
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ θ hθ hΓ hΔ
    exact ⟨θ, fun _ => rfl, subset_rfl, by simpa using hθ, hΓ, hΔ⟩
  | @insert c S _ ih =>
    intro hSK θ hθ hΓ hΔ
    have hcK := hSK c (Finset.mem_insert_self c S)
    obtain ⟨hΓ', hΔ'⟩ := entails_all_abstractConst_separator
      (fun φ hφ hc => hcK (hΓK φ hφ hc)) hΓ hΔ
    have hs : (abstractConst c θ).all.constantSupport ⊆ K ∪ ↑S := by
      rw [constantSupport_all, constantSupport_abstractConst]
      intro d hd
      exact (hθ hd.1).imp_right fun h => (Finset.mem_insert.1 h).resolve_left hd.2
    obtain ⟨χ, hr, hf, hk, hΓχ, hΔχ⟩ :=
      ih (fun d hd => hSK d (Finset.mem_insert_of_mem hd)) _ hs hΓ' hΔ'
    refine ⟨χ, fun s => by simpa using hr s, ?_, hk, hΓχ, hΔχ⟩
    exact hf.trans (by simp [functionsIn_abstractConst, Set.sdiff_subset])

end Theoryω

end FirstOrder.Language
