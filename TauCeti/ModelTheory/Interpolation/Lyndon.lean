/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Polarity
public import TauCeti.ModelTheory.Infinitary.Satisfiability
import TauCeti.ModelTheory.Infinitary.GraphTranslation.Polarity
import TauCeti.ModelTheory.Infinitary.GraphTranslation.Reconstruction
import TauCeti.ModelTheory.Interpolation.ConstantElimination
import TauCeti.ModelTheory.Interpolation.SignedInseparability
import TauCeti.ModelTheory.ModelExistence.CountableModel
import TauCeti.ModelTheory.ModelExistence.ModelExistence

/-!
# Lyndon interpolation for `L_{ω₁ω}`

López-Escobar's interpolation theorem refines Craig interpolation by tracking syntactic polarity:
whenever an `L_{ω₁ω}` sentence `φ` entails `ψ`, there is an interpolant `θ` with `φ ⊨ θ` and
`θ ⊨ ψ` whose occurring function symbols lie in `φ.functionsIn ∩ ψ.functionsIn`, whose positively
occurring relation symbols lie in `φ.positiveRelationsIn ∩ ψ.positiveRelationsIn`, and whose
negatively occurring relation symbols lie in `φ.negativeRelationsIn ∩ ψ.negativeRelationsIn`.
This is the relation-polarity, logical-equality form of Lyndon interpolation: logical equality
contributes to neither polarity (`relationsInSigned_equal = ∅`), so `θ` may use equality freely.

The proof proceeds in two stages, first for relational languages and then for arbitrary languages
via the graph translation:

* **Relational core (`lyndon_interpolation_relational`).** Over the Henkin expansion `L[[ℕ]]` of a
  relational language `L`, a member of the consistency property `lyndonConsistencyProperty` is the
  union `Γ ∪ Δ` of two finite theories with finite constant supports whose signed relation
  occurrences lie in two polarity-indexed budgets `B₁` and `B₂`, such that `(Γ, Δ)` is
  `Theoryω.SignedInseparable` with separator relation budget `fun s => B₁ s ∩ B₂ (!s)` and constant
  budget `pairSupport Γ Δ`. Flipping `!s` on `B₂` makes `LyndonPair` symmetric under swapping
  `(B₁, B₂)` and `(Γ, Δ)`: negating a separator reverses its polarities (`SignedInseparable.symm`).
  All propositional and countable-connective clauses reduce directly to `Theoryω.SignedInseparable`,
  quantifier and reflexivity clauses eliminate temporary constants via
  `Theoryω.exists_separator_constantSupport_subset`, `Theoryω.entails_ex_abstractConst_separator`,
  and `Theoryω.Entails.of_insert_inst`, and mixed equality substitution uses `equal t t' ⊓ θ`. At
  the root `({φ'}, {¬ψ'})`, taking `B₁ s = φ'.relationsInSigned s` and
  `B₂ s = ψ'.not.relationsInSigned s` gives `B₁ s ∩ B₂ (!s) = φ'.relationsInSigned s ∩
  ψ'.relationsInSigned s`, and empty constant support descends any separator to `L`. Restricting to
  the countable symbol sublanguage `symbSublang ∅ (φ.relationsIn ∪ ψ.relationsIn)` removes all
  countability hypotheses on `L`.
* **Arbitrary languages (`lyndon_interpolation`).** Through `Sentenceω.entails_iff_graphTranslation`
  and the countable conjunction `(graphAxioms F).conjunction`, the entailment `φ ⊨ ψ` becomes an
  entailment in the relational language `L.graphLanguage`. Applying
  `lyndon_interpolation_relational` yields a graph-language interpolant `θ`. By
  `relationsInSigned_conjunction_graphAxioms_inf_relationalize`,
  `relationsInSigned_conjunction_graphAxioms_imp_relationalize`, and `relSym_inter`, its signed
  occurrences at polarity `s` lie in
  `relSym (φ.functionsIn ∩ ψ.functionsIn) (φ.relationsInSigned s ∩ ψ.relationsInSigned s)`.
  Back-translating turns graph-relation atoms into equations, so `relationsInSigned_backTranslate`
  preserves both base-relation polarity bounds while `functionsIn_backTranslate` gives the shared
  function-symbol bound. Countable-theory Lyndon interpolation (`Theoryω.lyndon_interpolation`)
  follows via `Theoryω.conjunction`.

## Main results

* `FirstOrder.Language.lyndon_interpolation_relational`: relational Lyndon interpolation for
  `L_{ω₁ω}` sentences over a relational language of arbitrary cardinality and universes.
* `FirstOrder.Language.lyndon_interpolation`: Lyndon interpolation for `L_{ω₁ω}` sentences over an
  arbitrary language, bounding function symbols as well as positive and negative relation symbols.
* `FirstOrder.Language.Theoryω.lyndon_interpolation`: Lyndon interpolation for a countable theory
  `T` entailing a sentence `ψ`.

## References

* E. G. K. López-Escobar, *An interpolation theorem for denumerably long formulas*, Fundamenta
  Mathematicae **57** (1965), 253–272.
* H. J. Keisler, *Model Theory for Infinitary Logic*, North-Holland, 1971, §4.
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge
  University Press, 2016, §4.2.
* Adapted from `InfinitaryLogic/Methods/Interpolation/{LyndonSublanguage,LyndonArbitrary}.lean` in
  `cameronfreer/infinitary-logic` at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, refining
  the paired-inseparability consistency-property pattern of
  `TauCeti.ModelTheory.Interpolation.Craig`. Divergences from `cameronfreer/infinitary-logic`:
  languages and models live in arbitrary universes rather than `Language.{0, 0}` and `Type`; the
  consistency property reuses `Theoryω.SignedInseparable` and the polarity-preserving
  constant-elimination API on `L[[ℕ]]`; countability assumptions on `L` are discharged via
  `symbSublang`; and the transfer to languages with function symbols uses the exact
  signed-occurrence equalities for `(graphAxioms F).conjunction` paired with `relationalize`.
-/

public section

universe u v

namespace FirstOrder.Language

open BoundedFormulaInf

section Engine

variable {L : Language.{u, v}}

/-- Combined constant support of a pair `(Γ, Δ)` of theories over `L[[ℕ]]`. -/
private def pairSupport (Γ Δ : L[[ℕ]].Theoryω) : Set ℕ :=
  (⋃ χ ∈ Γ, χ.constantSupport) ∪ (⋃ χ ∈ Δ, χ.constantSupport)

private theorem pairSupport_comm (Γ Δ : L[[ℕ]].Theoryω) : pairSupport Γ Δ = pairSupport Δ Γ :=
  Set.union_comm _ _

private theorem subset_pairSupport_left {Γ Δ : L[[ℕ]].Theoryω} {χ : L[[ℕ]].Sentenceω}
    (hχ : χ ∈ Γ) : χ.constantSupport ⊆ pairSupport Γ Δ :=
  (Set.subset_biUnion_of_mem hχ).trans Set.subset_union_left

private theorem subset_pairSupport_right {Γ Δ : L[[ℕ]].Theoryω} {χ : L[[ℕ]].Sentenceω}
    (hχ : χ ∈ Δ) : χ.constantSupport ⊆ pairSupport Γ Δ :=
  (Set.subset_biUnion_of_mem hχ).trans Set.subset_union_right

private theorem pairSupport_insert_left {Γ Δ : L[[ℕ]].Theoryω} (χ : L[[ℕ]].Sentenceω) :
    pairSupport (insert χ Γ) Δ = pairSupport Γ Δ ∪ χ.constantSupport := by
  rw [pairSupport, Set.biUnion_insert, Set.union_comm χ.constantSupport, Set.union_right_comm]
  rfl

private theorem pairSupport_insert_left_of_subset {Γ Δ : L[[ℕ]].Theoryω} {χ : L[[ℕ]].Sentenceω}
    (h : χ.constantSupport ⊆ pairSupport Γ Δ) :
    pairSupport (insert χ Γ) Δ = pairSupport Γ Δ := by
  rw [pairSupport_insert_left, Set.union_eq_self_of_subset_right h]

private theorem pairSupport_insert_right_of_subset {Γ Δ : L[[ℕ]].Theoryω} {χ : L[[ℕ]].Sentenceω}
    (h : χ.constantSupport ⊆ pairSupport Γ Δ) :
    pairSupport Γ (insert χ Δ) = pairSupport Γ Δ := by
  rw [pairSupport_comm, pairSupport_insert_left_of_subset (pairSupport_comm Γ Δ ▸ h),
    pairSupport_comm]

/-- A finite pair `(Γ, Δ)` of theories over `L[[ℕ]]` with finite constant supports and signed
relation occurrences bounded by `B₁` and `B₂`, admitting no signed separator in
`fun s => B₁ s ∩ B₂ (!s)` with constants in `pairSupport Γ Δ`. -/
private structure LyndonPair (B₁ B₂ : Bool → Set (Σ n, L[[ℕ]].Relations n))
    (Γ Δ : L[[ℕ]].Theoryω) : Prop where
  finite_left : Γ.Finite
  finite_right : Δ.Finite
  rel_left : ∀ χ ∈ Γ, ∀ s, χ.relationsInSigned s ⊆ B₁ s
  rel_right : ∀ χ ∈ Δ, ∀ s, χ.relationsInSigned s ⊆ B₂ s
  supp_left : ∀ χ ∈ Γ, χ.constantSupport.Finite
  supp_right : ∀ χ ∈ Δ, χ.constantSupport.Finite
  insep : Theoryω.SignedInseparable Γ Δ (fun s => B₁ s ∩ B₂ (!s)) (pairSupport Γ Δ)

namespace LyndonPair

variable {B₁ B₂ : Bool → Set (Σ n, L[[ℕ]].Relations n)} {Γ Δ : L[[ℕ]].Theoryω}

private theorem finite_pairSupport (h : LyndonPair B₁ B₂ Γ Δ) : (pairSupport Γ Δ).Finite :=
  (h.finite_left.biUnion h.supp_left).union (h.finite_right.biUnion h.supp_right)

/-- Swapping `(Γ, Δ)` and `(B₁, B₂)` preserves `LyndonPair`: negating a separator flips its signed
occurrences, exchanging `B₁ s ∩ B₂ (!s)` with `B₂ s ∩ B₁ (!s)`. -/
private theorem symm (h : LyndonPair B₁ B₂ Γ Δ) : LyndonPair B₂ B₁ Δ Γ :=
  ⟨h.finite_right, h.finite_left, h.rel_right, h.rel_left, h.supp_right, h.supp_left, by
    simpa only [Bool.not_not, Set.inter_comm, pairSupport_comm Γ Δ] using h.insep.symm⟩

private theorem insert_left (h : LyndonPair B₁ B₂ Γ Δ) {χ : L[[ℕ]].Sentenceω}
    (hrel : ∀ s, χ.relationsInSigned s ⊆ B₁ s) (hfin : χ.constantSupport.Finite)
    (hinsep : Theoryω.SignedInseparable (insert χ Γ) Δ (fun s => B₁ s ∩ B₂ (!s))
      (pairSupport (insert χ Γ) Δ)) :
    LyndonPair B₁ B₂ (insert χ Γ) Δ :=
  ⟨h.finite_left.insert χ, h.finite_right,
    fun _ hψ => hψ.elim (fun e => e ▸ hrel) (h.rel_left _), h.rel_right,
    fun _ hψ => hψ.elim (fun e => e ▸ hfin) (h.supp_left _), h.supp_right, hinsep⟩

/-- Extending `Γ` by a sentence whose signed occurrences lie in `B₁`, whose constants already lie in
`pairSupport Γ Δ`, and which preserves `SignedInseparable` keeps `LyndonPair`. -/
private theorem insert_left_of_subset (h : LyndonPair B₁ B₂ Γ Δ) {χ : L[[ℕ]].Sentenceω}
    (hrel : ∀ s, χ.relationsInSigned s ⊆ B₁ s) (hsupp : χ.constantSupport ⊆ pairSupport Γ Δ)
    (hinsep : Theoryω.SignedInseparable (insert χ Γ) Δ (fun s => B₁ s ∩ B₂ (!s))
      (pairSupport Γ Δ)) :
    LyndonPair B₁ B₂ (insert χ Γ) Δ :=
  h.insert_left hrel (h.finite_pairSupport.subset hsupp)
    (pairSupport_insert_left_of_subset hsupp ▸ hinsep)

private theorem not_bot_left (h : LyndonPair B₁ B₂ Γ Δ) (hbot : ⊥ ∈ Γ) : False :=
  (Theoryω.isSatisfiable_iff_not_entails_bot.1 h.insep.isSatisfiable_left)
    (Theoryω.entails_of_mem hbot)

private theorem not_contradiction_same (h : LyndonPair B₁ B₂ Γ Δ) {φ : L[[ℕ]].Sentenceω}
    (hφ : φ ∈ Γ) (hnφ : φ.not ∈ Γ) : False :=
  (Theoryω.isSatisfiable_iff_not_entails_bot.1 h.insep.isSatisfiable_left)
    (Theoryω.entails_iff.2 fun _ _ _ hM => (hM.not_notMem hφ hnφ).elim)

/-- A sentence `φ ∈ Γ` whose negation lies in `Δ` separates `(Γ, Δ)` directly: its occurrences at
polarity `s` appear in `φ.not` at polarity `!s`, hence in `B₁ s ∩ B₂ (!s)`. -/
private theorem not_contradiction_cross (h : LyndonPair B₁ B₂ Γ Δ) {φ : L[[ℕ]].Sentenceω}
    (hφ : φ ∈ Γ) (hnφ : φ.not ∈ Δ) : False :=
  Theoryω.signedInseparable_iff.1 h.insep φ
    (fun s => Set.subset_inter (h.rel_left φ hφ s) (by simpa using h.rel_right φ.not hnφ (!s)))
    (subset_pairSupport_left hφ) (Theoryω.entails_of_mem hφ) (Theoryω.entails_of_mem hnφ)

private theorem imp_left (h : LyndonPair B₁ B₂ Γ Δ) {φ ψ : L[[ℕ]].Sentenceω}
    (himp : φ.imp ψ ∈ Γ) :
    LyndonPair B₁ B₂ (insert φ.not Γ) Δ ∨ LyndonPair B₁ B₂ (insert ψ Γ) Δ := by
  have hsupp :=
    Set.union_subset_iff.1 (constantSupport_imp φ ψ ▸ subset_pairSupport_left (Δ := Δ) himp)
  refine (h.insep.imp_left himp).imp
    (h.insert_left_of_subset ?_ (by simpa using hsupp.1))
    (h.insert_left_of_subset ?_ hsupp.2)
  · intro s
    simpa using Set.subset_union_left.trans (relationsInSigned_imp s φ ψ ▸ h.rel_left _ himp s)
  · intro s
    exact Set.subset_union_right.trans (relationsInSigned_imp s φ ψ ▸ h.rel_left _ himp s)

private theorem not_imp_left (h : LyndonPair B₁ B₂ Γ Δ) {φ ψ : L[[ℕ]].Sentenceω}
    (hnimp : (φ.imp ψ).not ∈ Γ) :
    LyndonPair B₁ B₂ (insert φ Γ) Δ ∧ LyndonPair B₁ B₂ (insert ψ.not Γ) Δ := by
  have hsupp : φ.constantSupport ∪ ψ.constantSupport ⊆ pairSupport Γ Δ := by
    simpa using subset_pairSupport_left (Δ := Δ) hnimp
  obtain ⟨h₁, h₂⟩ := h.insep.not_imp_left hnimp
  refine ⟨h.insert_left_of_subset ?_ (Set.union_subset_iff.1 hsupp).1 h₁,
    h.insert_left_of_subset ?_ (by simpa using (Set.union_subset_iff.1 hsupp).2) h₂⟩
  · intro s
    exact Set.subset_union_left.trans (by simpa using h.rel_left _ hnimp s)
  · intro s
    exact Set.subset_union_right.trans (by simpa using h.rel_left _ hnimp s)

private theorem iInf_left (h : LyndonPair B₁ B₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hiInf : BoundedFormulaInf.iInf φs ∈ Γ) (k : ℕ) :
    LyndonPair B₁ B₂ (insert (φs k) Γ) Δ :=
  h.insert_left_of_subset
    (fun s => (Set.subset_iUnion (fun i => (φs i).relationsInSigned s) k).trans
      (by simpa using h.rel_left _ hiInf s))
    ((Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
      (by simpa using subset_pairSupport_left (Δ := Δ) hiInf))
    (h.insep.iInf_left hiInf k)

private theorem not_iInf_left (h : LyndonPair B₁ B₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hniInf : (BoundedFormulaInf.iInf φs).not ∈ Γ) :
    ∃ k, LyndonPair B₁ B₂ (insert (φs k).not Γ) Δ := by
  obtain ⟨k, hk⟩ := h.insep.not_iInf_left hniInf
  refine ⟨k, h.insert_left_of_subset (fun s => ?_) ?_ hk⟩
  · simpa using (Set.subset_iUnion (fun i => (φs i).relationsInSigned (!s)) k).trans
      (by simpa using h.rel_left _ hniInf s)
  · simpa using (Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
      (by simpa using subset_pairSupport_left (Δ := Δ) hniInf)

private theorem iSup_left (h : LyndonPair B₁ B₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hiSup : BoundedFormulaInf.iSup φs ∈ Γ) :
    ∃ k, LyndonPair B₁ B₂ (insert (φs k) Γ) Δ := by
  obtain ⟨k, hk⟩ := h.insep.iSup_left hiSup
  exact ⟨k, h.insert_left_of_subset
    (fun s => (Set.subset_iUnion (fun i => (φs i).relationsInSigned s) k).trans
      (by simpa using h.rel_left _ hiSup s))
    ((Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
      (by simpa using subset_pairSupport_left (Δ := Δ) hiSup)) hk⟩

private theorem not_iSup_left (h : LyndonPair B₁ B₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hniSup : (BoundedFormulaInf.iSup φs).not ∈ Γ) (k : ℕ) :
    LyndonPair B₁ B₂ (insert (φs k).not Γ) Δ :=
  h.insert_left_of_subset
    (fun s => by
      simpa using (Set.subset_iUnion (fun i => (φs i).relationsInSigned (!s)) k).trans
        (by simpa using h.rel_left _ hniSup s))
    (by
      simpa using (Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
        (by simpa using subset_pairSupport_left (Δ := Δ) hniSup))
    (h.insep.not_iSup_left hniSup k)

/-- Universal instantiation on the left: the instance follows from `Γ`, and any extra occurrence of
`c` in a separator is universally abstracted via `exists_separator_constantSupport_subset`. -/
private theorem all_left (h : LyndonPair B₁ B₂ Γ Δ) {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (hall : φ.all ∈ Γ) (c : ℕ) :
    LyndonPair B₁ B₂ (insert (φ.inst (L.con c).term) Γ) Δ := by
  have hsupp : (φ.inst (L.con c).term).constantSupport ⊆ pairSupport Γ Δ ∪ {c} :=
    (constantSupport_inst_subset φ (L.con c).term).trans
      (Set.union_subset_union (by simpa using subset_pairSupport_left (Δ := Δ) hall) (by simp))
  refine h.insert_left (fun s => by simpa using h.rel_left _ hall s)
    ((h.finite_pairSupport.union (Set.finite_singleton c)).subset hsupp)
    (Theoryω.signedInseparable_iff.2 fun θ hr hs hΓθ hΔθ => ?_)
  have hent : Γ.Entails θ := (Theoryω.entails_iff.2 fun _ _ _ hM =>
    SentenceInf.realize_inst_of_realize_all (hM.realize_of_mem hall) _).cut hΓθ
  obtain ⟨χ, hχr, -, hχk, hΓχ, hΔχ⟩ := Theoryω.exists_separator_constantSupport_subset
    (Set.finite_singleton c) (fun _ => subset_pairSupport_left)
    (hs.trans (pairSupport_insert_left _ ▸ Set.union_subset Set.subset_union_left hsupp))
    hent hΔθ
  exact Theoryω.signedInseparable_iff.1 h.insep χ
    (fun s => (hχr s).trans_subset (hr s)) hχk hΓχ hΔχ

/-- Existential witness on the left: pick `c` outside `pairSupport Γ Δ`, existentially abstract `c`
from any separator of the extended pair, and discharge the witness hypothesis via
`Theoryω.Entails.of_insert_inst`. -/
private theorem not_all_left (h : LyndonPair B₁ B₂ Γ Δ) {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (hn : φ.all.not ∈ Γ) :
    ∃ c, LyndonPair B₁ B₂ (insert (φ.inst (L.con c).term).not Γ) Δ := by
  obtain ⟨c, hc⟩ := h.finite_pairSupport.infinite_compl.nonempty
  have hφK : φ.constantSupport ⊆ pairSupport Γ Δ := by
    simpa using subset_pairSupport_left (Δ := Δ) hn
  have hsupp : (φ.inst (L.con c).term).not.constantSupport ⊆ pairSupport Γ Δ ∪ {c} := by
    rw [constantSupport_not]
    exact (constantSupport_inst_subset φ (L.con c).term).trans
      (Set.union_subset_union hφK (by simp))
  refine ⟨c, h.insert_left (fun s => by simpa using h.rel_left _ hn s)
    ((h.finite_pairSupport.union (Set.finite_singleton c)).subset hsupp)
    (Theoryω.signedInseparable_iff.2 fun θ hr hs hΓθ hΔθ => ?_)⟩
  have hs' : θ.constantSupport ⊆ pairSupport Γ Δ ∪ {c} :=
    hs.trans (pairSupport_insert_left _ ▸ Set.union_subset Set.subset_union_left hsupp)
  obtain ⟨hΓ', hΔ'⟩ := Theoryω.entails_ex_abstractConst_separator
    (fun _ hψ hcψ => hc (subset_pairSupport_right hψ hcψ)) hΓθ hΔθ
  refine Theoryω.signedInseparable_iff.1 h.insep (abstractConst c θ).ex
    (fun s => by simpa using hr s) ?_ ?_ hΔ'
  · rw [constantSupport_ex, constantSupport_abstractConst]
    exact fun d hd => (hs' hd.1).resolve_right hd.2
  · refine Theoryω.Entails.of_insert_inst (φ := φ.not)
      (fun _ hψ hcψ => hc (subset_pairSupport_left hψ hcψ))
      (fun hcφ => hc (hφK (by simpa using hcφ))) (by simp)
      (Theoryω.entails_of_mem hn).ex_not_of_not_all ?_
    rwa [inst_def, substBounds_not, ← inst_def]

private theorem eq_refl_left (h : LyndonPair B₁ B₂ Γ Δ) (t : L[[ℕ]].Term (Empty ⊕ Fin 0)) :
    LyndonPair B₁ B₂ (insert (equal t t) Γ) Δ := by
  refine h.insert_left (by simp) (by simpa using t.finite_constantSupport)
    (Theoryω.signedInseparable_iff.2 fun θ hr hs hΓθ hΔθ => ?_)
  have hent : Γ.Entails θ :=
    (Theoryω.entails_iff.2 fun _ _ _ _ => SentenceInf.realize_equal_self t).cut hΓθ
  obtain ⟨χ, hχr, -, hχk, hΓχ, hΔχ⟩ := Theoryω.exists_separator_constantSupport_subset
    t.finite_constantSupport (fun _ => subset_pairSupport_left)
    (by simpa [pairSupport_insert_left] using hs) hent hΔθ
  exact Theoryω.signedInseparable_iff.1 h.insep χ
    (fun s => (hχr s).trans_subset (hr s)) hχk hΓχ hΔχ

private theorem eq_subst_same (h : LyndonPair B₁ B₂ Γ Δ)
    {t t' : L[[ℕ]].Term (Empty ⊕ Fin 0)} {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (heq : equal t t' ∈ Γ) (hinst : φ.inst t ∈ Γ) :
    LyndonPair B₁ B₂ (insert (φ.inst t') Γ) Δ := by
  have htK :=
    Set.union_subset_iff.1 (constantSupport_equal t t' ▸ subset_pairSupport_left (Δ := Δ) heq)
  have hsupp : (φ.inst t').constantSupport ⊆ pairSupport Γ Δ :=
    (constantSupport_inst_subset φ t').trans
      (Set.union_subset
        ((constantSupport_subset_inst φ t).trans (subset_pairSupport_left (Δ := Δ) hinst)) htK.2)
  exact h.insert_left_of_subset (fun s => by simpa using h.rel_left _ hinst s) hsupp
    (h.insep.insert_left_of_entails (Theoryω.entails_iff.2 fun _ _ _ hM =>
      SentenceInf.realize_inst_of_realize_equal
        (hM.realize_of_mem heq) (hM.realize_of_mem hinst)))

/-- Mixed equality substitution (`equal t t' ∈ Γ` and `φ.inst t ∈ Δ`): because logical equality
contributes to neither polarity (`relationsInSigned_equal = ∅`), `θ ↦ equal t t' ⊓ θ` transfers any
separator of `(Γ, insert (φ.inst t') Δ)` back to `(Γ, Δ)`. -/
private theorem eq_subst_cross (h : LyndonPair B₁ B₂ Γ Δ)
    {t t' : L[[ℕ]].Term (Empty ⊕ Fin 0)} {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (heq : equal t t' ∈ Γ) (hinst : φ.inst t ∈ Δ) :
    LyndonPair B₁ B₂ Γ (insert (φ.inst t') Δ) := by
  have htK :=
    Set.union_subset_iff.1 (constantSupport_equal t t' ▸ subset_pairSupport_left (Δ := Δ) heq)
  have hsupp : (φ.inst t').constantSupport ⊆ pairSupport Γ Δ :=
    (constantSupport_inst_subset φ t').trans
      (Set.union_subset
        ((constantSupport_subset_inst φ t).trans (subset_pairSupport_right (Γ := Γ) hinst)) htK.2)
  refine (h.symm.insert_left (fun s => by simpa using h.rel_right _ hinst s)
    (h.finite_pairSupport.subset hsupp) ?_).symm
  rw [pairSupport_comm, pairSupport_insert_right_of_subset hsupp]
  have hinsep : Theoryω.SignedInseparable Γ (insert (φ.inst t') Δ)
      (fun s => B₁ s ∩ B₂ (!s)) (pairSupport Γ Δ) := by
    refine Theoryω.signedInseparable_iff.2 fun θ hr hs hΓθ hΔθ => ?_
    refine Theoryω.signedInseparable_iff.1 h.insep (equal t t' ⊓ θ)
      (fun s => by simpa using hr s) (by simp [htK.1, htK.2, hs])
      (Theoryω.entails_iff.2 fun M _ _ hM =>
        SentenceInf.realize_inf.2 ⟨hM.realize_of_mem heq, Theoryω.entails_iff.1 hΓθ M hM⟩)
      (Theoryω.entails_iff.2 fun M _ _ hM => ?_)
    rw [SentenceInf.realize_not, SentenceInf.realize_inf]
    rintro ⟨htM, hθM⟩
    exact SentenceInf.realize_not.1
      (Theoryω.entails_iff.1 hΔθ M (Theoryω.model_insert_iff.2
        ⟨SentenceInf.realize_inst_of_realize_equal htM (hM.realize_of_mem hinst), hM⟩)) hθM
  simpa only [Bool.not_not, Set.inter_comm] using hinsep.symm

private theorem eq_name_left [L.IsRelational] (h : LyndonPair B₁ B₂ Γ Δ)
    (t : L[[ℕ]].Term (Empty ⊕ Fin 0)) :
    ∃ c, LyndonPair B₁ B₂ (insert (equal (L.con c).term t) Γ) Δ := by
  obtain ⟨d, rfl⟩ := Term.exists_eq_con_of_isRelational t
  exact ⟨d, h.eq_refl_left _⟩

end LyndonPair

/-- **The Lyndon paired-inseparability consistency property** over `L[[ℕ]]` for a relational
language `L`. Right-hand and symmetric mixed cases reduce to the left-hand clauses via
`LyndonPair.symm`. -/
private def lyndonConsistencyProperty [L.IsRelational]
    (B₁ B₂ : Bool → Set (Σ n, L[[ℕ]].Relations n)) : ConsistencyProperty L where
  sets := {s | ∃ Γ Δ, s = Γ ∪ Δ ∧ LyndonPair B₁ B₂ Γ Δ}
  no_falsum := by rintro _ ⟨_, _, rfl, hp⟩ h; exact h.elim hp.not_bot_left hp.symm.not_bot_left
  no_contradiction := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φ (hφ | hφ) (hnφ | hnφ)
    · exact hp.not_contradiction_same hφ hnφ
    · exact hp.not_contradiction_cross hφ hnφ
    · exact hp.symm.not_contradiction_cross hφ hnφ
    · exact hp.symm.not_contradiction_same hφ hnφ
  imp := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φ ψ (himp | himp)
    · exact (hp.imp_left himp).imp (⟨_, _, Set.insert_union.symm, ·⟩)
        (⟨_, _, Set.insert_union.symm, ·⟩)
    · exact (hp.symm.imp_left himp).imp (fun h => ⟨_, _, Set.union_insert.symm, h.symm⟩)
        (fun h => ⟨_, _, Set.union_insert.symm, h.symm⟩)
  not_imp := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φ ψ (hnimp | hnimp)
    · exact (hp.not_imp_left hnimp).imp (⟨_, _, Set.insert_union.symm, ·⟩)
        (⟨_, _, Set.insert_union.symm, ·⟩)
    · exact (hp.symm.not_imp_left hnimp).imp (fun h => ⟨_, _, Set.union_insert.symm, h.symm⟩)
        (fun h => ⟨_, _, Set.union_insert.symm, h.symm⟩)
  iInf := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φs (hiInf | hiInf) k
    · exact ⟨_, _, Set.insert_union.symm, hp.iInf_left hiInf k⟩
    · exact ⟨_, _, Set.union_insert.symm, (hp.symm.iInf_left hiInf k).symm⟩
  not_iInf := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φs (hniInf | hniInf)
    · exact (hp.not_iInf_left hniInf).imp fun _ hk => ⟨_, _, Set.insert_union.symm, hk⟩
    · exact (hp.symm.not_iInf_left hniInf).imp fun _ hk => ⟨_, _, Set.union_insert.symm, hk.symm⟩
  iSup := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φs (hiSup | hiSup)
    · exact (hp.iSup_left hiSup).imp fun _ hk => ⟨_, _, Set.insert_union.symm, hk⟩
    · exact (hp.symm.iSup_left hiSup).imp fun _ hk => ⟨_, _, Set.union_insert.symm, hk.symm⟩
  not_iSup := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φs (hniSup | hniSup) k
    · exact ⟨_, _, Set.insert_union.symm, hp.not_iSup_left hniSup k⟩
    · exact ⟨_, _, Set.union_insert.symm, (hp.symm.not_iSup_left hniSup k).symm⟩
  all := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φ (hall | hall) c
    · exact ⟨_, _, Set.insert_union.symm, hp.all_left hall c⟩
    · exact ⟨_, _, Set.union_insert.symm, (hp.symm.all_left hall c).symm⟩
  not_all := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φ (hnall | hnall)
    · exact (hp.not_all_left hnall).imp fun _ hc => ⟨_, _, Set.insert_union.symm, hc⟩
    · exact (hp.symm.not_all_left hnall).imp fun _ hc => ⟨_, _, Set.union_insert.symm, hc.symm⟩
  eq_refl := by rintro _ ⟨_, _, rfl, hp⟩ t; exact ⟨_, _, Set.insert_union.symm, hp.eq_refl_left t⟩
  eq_subst := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ t t' φ _ (heq | heq) (hinst | hinst)
    · exact ⟨_, _, Set.insert_union.symm, hp.eq_subst_same heq hinst⟩
    · exact ⟨_, _, Set.union_insert.symm, hp.eq_subst_cross heq hinst⟩
    · exact ⟨_, _, Set.insert_union.symm, (hp.symm.eq_subst_cross heq hinst).symm⟩
    · exact ⟨_, _, Set.union_insert.symm, (hp.symm.eq_subst_same heq hinst).symm⟩
  eq_name := by
    rintro _ ⟨_, _, rfl, hp⟩ t
    exact (hp.eq_name_left t).imp fun _ hc => ⟨_, _, Set.insert_union.symm, hc⟩

end Engine

/-! ### Lyndon interpolation -/

section Lyndon

variable {L : Language.{u, v}}

/-- The root pair `({φ'}, {¬ψ'})` of the images of `φ` and `ψ` in `L[[ℕ]]` satisfies `LyndonPair`
whenever `φ` and `ψ` admit no Lyndon interpolant in `L`: a separator of the root pair has empty
constant support and therefore descends to `L`. -/
private theorem lyndonPair_root (φ ψ : L.Sentenceω)
    (hno : ¬ ∃ θ : L.Sentenceω,
      θ.positiveRelationsIn ⊆ φ.positiveRelationsIn ∩ ψ.positiveRelationsIn ∧
      θ.negativeRelationsIn ⊆ φ.negativeRelationsIn ∩ ψ.negativeRelationsIn ∧
      φ.Entails θ ∧ θ.Entails ψ) :
    LyndonPair
      (fun s => ((L.lhomWithConstants ℕ).onBoundedFormulaInf φ).relationsInSigned s)
      (fun s => (((L.lhomWithConstants ℕ).onBoundedFormulaInf ψ).not).relationsInSigned s)
      {(L.lhomWithConstants ℕ).onBoundedFormulaInf φ}
      {((L.lhomWithConstants ℕ).onBoundedFormulaInf ψ).not} := by
  have hg : Function.Injective fun r : Σ n, L.Relations n =>
      (⟨r.1, (L.lhomWithConstants ℕ).onRelation r.2⟩ : Σ n, L[[ℕ]].Relations n) :=
    Function.injective_id.sigma_map fun _ => (L.lhomWithConstants_injective ℕ).onRelation
  refine ⟨Set.finite_singleton _, Set.finite_singleton _,
    fun _ hχ _ => (Set.mem_singleton_iff.1 hχ) ▸ subset_rfl,
    fun _ hχ _ => (Set.mem_singleton_iff.1 hχ) ▸ subset_rfl,
    fun _ hχ => by rw [Set.mem_singleton_iff.1 hχ]; simp,
    fun _ hχ => by rw [Set.mem_singleton_iff.1 hχ]; simp,
    Theoryω.signedInseparable_iff.2 fun θ' hθ'rel hθ'supp hφθ' hψθ' => ?_⟩
  have hK : pairSupport ({(L.lhomWithConstants ℕ).onBoundedFormulaInf φ} : L[[ℕ]].Theoryω)
      {((L.lhomWithConstants ℕ).onBoundedFormulaInf ψ).not} = ∅ := by simp [pairSupport]
  obtain ⟨θ, rfl⟩ := constantSupport_eq_empty_iff.1 (Set.subset_empty_iff.1 (hK ▸ hθ'supp))
  have hrel (s : Bool) : θ.relationsInSigned s ⊆ φ.relationsInSigned s ∩ ψ.relationsInSigned s := by
    have hs := hθ'rel s
    simp only [relationsInSigned_not, Bool.not_not,
      LHom.relationsInSigned_onBoundedFormulaInf] at hs
    rw [← Set.image_inter hg] at hs
    exact (Set.image_subset_image_iff hg).1 hs
  refine hno ⟨θ, hrel true, hrel false, ?_, ?_⟩
  · exact (Sentenceω.entails_onBoundedFormulaInf_iff (L.lhomWithConstants_injective ℕ)).1
      (Sentenceω.entails_def.2 hφθ')
  · have hnot : Sentenceω.Entails ψ.not θ.not :=
      (Sentenceω.entails_onBoundedFormulaInf_iff (L.lhomWithConstants_injective ℕ)).1
        (by simpa using Sentenceω.entails_def.2 hψθ')
    exact Sentenceω.entails_iff.2 fun M _ _ hθM => by
      by_contra hψM
      exact SentenceInf.realize_not.1 (hnot.realize M (SentenceInf.realize_not.2 hψM)) hθM

/-- Countable relational core: over a relational language with countably many relation symbols,
every valid entailment `φ ⊨ ψ` admits a Lyndon interpolant. -/
private theorem lyndon_interpolation_relational_of_countable [L.IsRelational]
    [Countable (Σ n, L.Relations n)] (φ ψ : L.Sentenceω) (h : φ.Entails ψ) :
    ∃ θ : L.Sentenceω,
      θ.positiveRelationsIn ⊆ φ.positiveRelationsIn ∩ ψ.positiveRelationsIn ∧
      θ.negativeRelationsIn ⊆ φ.negativeRelationsIn ∩ ψ.negativeRelationsIn ∧
      φ.Entails θ ∧ θ.Entails ψ := by
  have : IsEmpty (Σ n, L.Functions n) := ⟨fun s => isEmptyElim s.2⟩
  by_contra hno
  let g := L.lhomWithConstants ℕ
  obtain ⟨M, _, _, _, hM, _⟩ := (lyndonConsistencyProperty
    (fun s => (g.onBoundedFormulaInf φ).relationsInSigned s)
    (fun s => ((g.onBoundedFormulaInf ψ).not).relationsInSigned s)).model_existence.{u, v, max u v}
      ⟨_, _, rfl, lyndonPair_root φ ψ hno⟩
      ((Set.countable_singleton _).union (Set.countable_singleton _))
  let : L.Structure M := g.reduct M
  have hφM : SentenceInf.Realize φ M :=
    (LHom.realize_sentenceInf_onBoundedFormulaInf g φ).1
      (hM.realize_of_mem (.inl (Set.mem_singleton _)))
  exact SentenceInf.realize_not.1 (hM.realize_of_mem (.inr (Set.mem_singleton _)))
    ((LHom.realize_sentenceInf_onBoundedFormulaInf g ψ).2 (h.realize M hφM))

/-- **Relational Lyndon interpolation for `L_{ω₁ω}`.** Over any relational language `L` (of any
cardinality and in any universes), if an `L_{ω₁ω}` sentence `φ` entails `ψ`, there is an `L_{ω₁ω}`
sentence `θ` whose positively occurring relation symbols occur positively in both `φ` and `ψ` and
whose negatively occurring relation symbols occur negatively in both `φ` and `ψ`, with `φ ⊨ θ` and
`θ ⊨ ψ`. Equality is logical, so `θ` may use it freely. -/
theorem lyndon_interpolation_relational [L.IsRelational] (φ ψ : L.Sentenceω) (h : φ.Entails ψ) :
    ∃ θ : L.Sentenceω,
      θ.positiveRelationsIn ⊆ φ.positiveRelationsIn ∩ ψ.positiveRelationsIn ∧
      θ.negativeRelationsIn ⊆ φ.negativeRelationsIn ∩ ψ.negativeRelationsIn ∧
      φ.Entails θ ∧ θ.Entails ψ := by
  let F : Set (Σ n, L.Functions n) := ∅
  let R : Set (Σ n, L.Relations n) := φ.relationsIn ∪ ψ.relationsIn
  have : Countable R := (φ.relationsIn_countable.union ψ.relationsIn_countable).to_subtype
  have hFφ : φ.functionsIn ⊆ F := fun s _ => isEmptyElim s.2
  have hFψ : ψ.functionsIn ⊆ F := fun s _ => isEmptyElim s.2
  let φ₀ : (symbSublang F R).Sentenceω := φ.restrictSymbols hFφ Set.subset_union_left
  let ψ₀ : (symbSublang F R).Sentenceω := ψ.restrictSymbols hFψ Set.subset_union_right
  have hφ₀ : (symbSublangIncl F R).onBoundedFormulaInf φ₀ = φ :=
    onBoundedFormulaInf_restrictSymbols φ hFφ Set.subset_union_left
  have hψ₀ : (symbSublangIncl F R).onBoundedFormulaInf ψ₀ = ψ :=
    onBoundedFormulaInf_restrictSymbols ψ hFψ Set.subset_union_right
  have h₀ : φ₀.Entails ψ₀ :=
    (Sentenceω.entails_onBoundedFormulaInf_iff (symbSublangIncl_injective F R)).1
      (by rwa [hφ₀, hψ₀])
  obtain ⟨θ₀, hpos₀, hneg₀, hφθ₀, hθψ₀⟩ := lyndon_interpolation_relational_of_countable φ₀ ψ₀ h₀
  have hlift (s : Bool) (hs : θ₀.relationsInSigned s ⊆
      φ₀.relationsInSigned s ∩ ψ₀.relationsInSigned s) :
      ((symbSublangIncl F R).onBoundedFormulaInf θ₀).relationsInSigned s ⊆
        φ.relationsInSigned s ∩ ψ.relationsInSigned s := by
    rw [LHom.relationsInSigned_onBoundedFormulaInf]
    refine ((Set.image_mono hs).trans (Set.image_inter_subset _ _ _)).trans ?_
    rw [← LHom.relationsInSigned_onBoundedFormulaInf,
      ← LHom.relationsInSigned_onBoundedFormulaInf, hφ₀, hψ₀]
  exact ⟨(symbSublangIncl F R).onBoundedFormulaInf θ₀, hlift true hpos₀, hlift false hneg₀,
    hφ₀ ▸ hφθ₀.onBoundedFormulaInf (symbSublangIncl F R),
    hψ₀ ▸ hθψ₀.onBoundedFormulaInf (symbSublangIncl F R)⟩

/-- Rewrites the graph-translation entailment `Sentenceω.entails_iff_graphTranslation` using
`Theoryω.conjunction` on `graphAxioms`, matching the signed-occurrence identities for
`graphAxioms` paired with `relationalize`. -/
private theorem entails_conjunction_graphAxioms_of_entails {φ ψ : L.Sentenceω}
    (h : φ.Entails ψ) :
    Sentenceω.Entails
      ((graphAxioms φ.functionsIn).conjunction φ.functionsIn_countable.graphAxioms ⊓
        φ.relationalize)
      (((graphAxioms ψ.functionsIn).conjunction ψ.functionsIn_countable.graphAxioms).imp
        ψ.relationalize) := by
  have hA {F : Set (Σ n, L.Functions n)} (hF : F.Countable)
      (M : Type (max u v)) [L.graphLanguage.Structure M] :
      SentenceInf.Realize ((graphAxioms F).conjunction hF.graphAxioms) M ↔
        SentenceInf.Realize (graphAxiomsSentence F hF) M := by
    rw [Theoryω.realize_conjunction_iff, model_graphAxioms_iff, realize_graphAxiomsSentence,
      Sigma.forall]
  have hgt := Sentenceω.entails_iff_graphTranslation.1 h
  refine Sentenceω.entails_iff.2 fun M _ _ hM => ?_
  rw [SentenceInf.realize_inf, hA φ.functionsIn_countable] at hM
  have hM' := Sentenceω.entails_iff.1 hgt M (SentenceInf.realize_inf.2 hM)
  rw [SentenceInf.realize_imp, ← hA ψ.functionsIn_countable] at hM'
  exact SentenceInf.realize_imp.2 hM'

/-- **Lyndon interpolation for `L_{ω₁ω}`.** Over any language `L` (of any cardinality, with
function symbols, and in any universes), if an `L_{ω₁ω}` sentence `φ` entails `ψ`, there is an
`L_{ω₁ω}` sentence `θ` whose occurring function symbols lie in `φ.functionsIn ∩ ψ.functionsIn`,
whose positively occurring relation symbols lie in `φ.positiveRelationsIn ∩ ψ.positiveRelationsIn`,
and whose negatively occurring relation symbols lie in
`φ.negativeRelationsIn ∩ ψ.negativeRelationsIn`, with `φ ⊨ θ` and `θ ⊨ ψ`. Equality is logical, so
`θ` may use it freely. -/
theorem lyndon_interpolation (φ ψ : L.Sentenceω) (h : φ.Entails ψ) :
    ∃ θ : L.Sentenceω,
      θ.functionsIn ⊆ φ.functionsIn ∩ ψ.functionsIn ∧
      θ.positiveRelationsIn ⊆ φ.positiveRelationsIn ∩ ψ.positiveRelationsIn ∧
      θ.negativeRelationsIn ⊆ φ.negativeRelationsIn ∩ ψ.negativeRelationsIn ∧
      φ.Entails θ ∧ θ.Entails ψ := by
  obtain ⟨θ, hpos, hneg, hφθ, hθψ⟩ :=
    lyndon_interpolation_relational _ _ (entails_conjunction_graphAxioms_of_entails h)
  have hsym (s : Bool)
      (hs : θ.relationsInSigned s ⊆
        ((graphAxioms φ.functionsIn).conjunction φ.functionsIn_countable.graphAxioms ⊓
          φ.relationalize).relationsInSigned s ∩
        (((graphAxioms ψ.functionsIn).conjunction ψ.functionsIn_countable.graphAxioms).imp
          ψ.relationalize).relationsInSigned s) :
      θ.relationsInSigned s ⊆
        relSym (φ.functionsIn ∩ ψ.functionsIn)
          (φ.relationsInSigned s ∩ ψ.relationsInSigned s) := by
    rwa [relationsInSigned_conjunction_graphAxioms_inf_relationalize _ _ _ subset_rfl,
      relationsInSigned_conjunction_graphAxioms_imp_relationalize _ _ _ subset_rfl,
      relSym_inter] at hs
  have hrel : θ.relationsIn ⊆
      relSym (φ.functionsIn ∩ ψ.functionsIn)
        ((φ.positiveRelationsIn ∩ ψ.positiveRelationsIn) ∪
          (φ.negativeRelationsIn ∩ ψ.negativeRelationsIn)) := by
    rw [← relationsInSigned_union_not true θ]
    exact (Set.union_subset_union (hsym true hpos) (hsym false hneg)).trans
      (by rw [← relSym_union, Set.union_self])
  refine ⟨θ.backTranslate, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using Set.preimage_mono (f := graphRelSym) hrel
  · simpa using Set.preimage_mono (f := baseRelSym) (hsym true hpos)
  · simpa using Set.preimage_mono (f := baseRelSym) (hsym false hneg)
  · refine Sentenceω.entails_iff.2 fun M _ _ hφM => ?_
    let := graphExpansion L M
    have hθM := hφθ.realize M (SentenceInf.realize_inf.2
      ⟨(Theoryω.realize_conjunction_iff _).2 (model_graphAxioms_graphExpansion L M _), by
        simpa only [SentenceInf.realize_def, FormulaInf.realize_def, realize_relationalize]
          using hφM⟩)
    simpa only [SentenceInf.realize_def, FormulaInf.realize_def, realize_backTranslate] using hθM
  · refine Sentenceω.entails_iff.2 fun M _ _ hθM => ?_
    let := graphExpansion L M
    have hψM := hθψ.realize M (by
      simpa only [SentenceInf.realize_def, FormulaInf.realize_def, realize_backTranslate]
        using hθM)
    have hψM' := (SentenceInf.realize_imp.1 hψM)
      ((Theoryω.realize_conjunction_iff _).2 (model_graphAxioms_graphExpansion L M _))
    simpa only [SentenceInf.realize_def, FormulaInf.realize_def, realize_relationalize] using hψM'

/-- **Countable-theory Lyndon interpolation.** If a countable `L_{ω₁ω}` theory `T` entails `ψ`,
there is an interpolant `θ` whose occurring function symbols lie in
`(⋃ φ ∈ T, φ.functionsIn) ∩ ψ.functionsIn`, whose positively occurring relation symbols lie in
`(⋃ φ ∈ T, φ.positiveRelationsIn) ∩ ψ.positiveRelationsIn`, and whose negatively occurring relation
symbols lie in `(⋃ φ ∈ T, φ.negativeRelationsIn) ∩ ψ.negativeRelationsIn`, with `T ⊨ θ` and
`θ ⊨ ψ`. -/
theorem Theoryω.lyndon_interpolation {T : L.Theoryω} (hT : T.Countable) (ψ : L.Sentenceω)
    (h : T.Entails ψ) :
    ∃ θ : L.Sentenceω,
      θ.functionsIn ⊆ (⋃ φ ∈ T, φ.functionsIn) ∩ ψ.functionsIn ∧
      θ.positiveRelationsIn ⊆ (⋃ φ ∈ T, φ.positiveRelationsIn) ∩ ψ.positiveRelationsIn ∧
      θ.negativeRelationsIn ⊆ (⋃ φ ∈ T, φ.negativeRelationsIn) ∩ ψ.negativeRelationsIn ∧
      T.Entails θ ∧ θ.Entails ψ := by
  obtain ⟨θ, hfun, hpos, hneg, hTθ, hθψ⟩ := Language.lyndon_interpolation (T.conjunction hT) ψ
    ((Theoryω.entails_iff_conjunction_entails hT).1 h)
  simp only [BoundedFormulaInf.positiveRelationsIn, Theoryω.relationsInSigned_conjunction] at hpos ⊢
  simp only [BoundedFormulaInf.negativeRelationsIn, Theoryω.relationsInSigned_conjunction] at hneg ⊢
  refine ⟨θ, hfun.trans (Set.inter_subset_inter_left _ ?_), hpos, hneg,
    (Theoryω.entails_iff_conjunction_entails hT).2 hTθ, hθψ⟩
  rw [Theoryω.conjunction_def, functionsIn_iInfAlong]
  exact Set.iUnion_subset fun φ => Set.subset_biUnion_of_mem φ.2

end Lyndon

end FirstOrder.Language
