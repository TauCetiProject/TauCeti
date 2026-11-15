/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.GraphTranslation.Polarity
public import TauCeti.ModelTheory.Interpolation.ConstantElimination
public import TauCeti.ModelTheory.Interpolation.SignedInseparability
public import TauCeti.ModelTheory.ModelExistence.CountableModel
public import TauCeti.ModelTheory.ModelExistence.ModelExistence

/-!
# Lyndon interpolation for `L_{ω₁ω}`

Lyndon interpolation refines Craig interpolation for `L_{ω₁ω}` by tracking syntactic polarity of
relation symbols: if an `L_{ω₁ω}` sentence `φ` entails `ψ`, there is an interpolant `θ` with
`φ ⊨ θ` and `θ ⊨ ψ` whose occurring function symbols lie in `φ.functionsIn ∩ ψ.functionsIn`, whose
positively occurring relation symbols lie in
`φ.relationsInSigned true ∩ ψ.relationsInSigned true`, and whose negatively occurring relation
symbols lie in `φ.relationsInSigned false ∩ ψ.relationsInSigned false`. Equality is treated as
logical (`BoundedFormulaInf.relationsInSigned_equal` is empty at both polarities), so `θ` may use
equality freely even when neither `φ` nor `ψ` mentions `=`.

The proof proceeds in two stages:

* **Relational core** (`FirstOrder.Language.lyndon_interpolation_relational`). Over the Henkin
  expansion `L[[ℕ]]` of a countable relational language `L`, a member of the consistency property
  is a union `Γ ∪ Δ` of two finite theories with finite constant supports whose signed relation
  occurrences lie in two signed budgets `R₁` and `R₂`, such that `Γ` and `Δ` are signed-inseparable
  (`Theoryω.SignedInseparable`) with respect to the shared polarity budget
  `s ↦ R₁ s ∩ R₂ (!s)` and the combined constant support of `(Γ, Δ)`. Swapping `(Γ, Δ)` flips the
  polarity of a separator and therefore exchanges `R₁` and `R₂`. Propositional decomposition
  delegates to `Theoryω.SignedInseparable`, finite constant elimination in `all` and `eq_refl`
  delegates to `Theoryω.exists_separator_constantSupport_subset`, and fresh-witness elimination in
  `not_all` combines `Theoryω.entails_ex_abstractConst_separator` with existential instantiation
  `Theoryω.Entails.of_insert_inst`. Restricting `φ` and `ψ` to their countable symbol sublanguage
  removes any countability assumption on `L`.
* **Transfer to arbitrary languages** (`FirstOrder.Language.lyndon_interpolation`). Passing to the
  relational graph language `L.graphLanguage` turns `φ ⊨ ψ` into an entailment between
  `(graphAxioms φ.functionsIn).conjunction _ ⊓ φ.relationalize` and
  `((graphAxioms ψ.functionsIn).conjunction _).imp ψ.relationalize`. By
  `relationsInSigned_conjunction_graphAxioms_inf_relationalize`,
  `relationsInSigned_conjunction_graphAxioms_imp_relationalize`, and `relSym_inter`, a relational
  Lyndon interpolant in `L.graphLanguage` mentions only base symbols of shared same-polarity
  relations and graph symbols of shared functions; `BoundedFormulaInf.backTranslate` turns graph
  relations back into equations while preserving base-relation polarities.

Replacing a countable theory `T` by `T.conjunction` yields countable-theory Lyndon interpolation
(`FirstOrder.Language.Theoryω.lyndon_interpolation`). Joining the two signed bounds via
`BoundedFormulaInf.relationsInSigned_union_not` recovers Craig interpolation in
`TauCeti.ModelTheory.Interpolation.Craig`.

## Main results

* `FirstOrder.Language.lyndon_interpolation_relational`: relational Lyndon interpolation for
  `L_{ω₁ω}` sentences over a relational language of arbitrary cardinality.
* `FirstOrder.Language.lyndon_interpolation`: Lyndon interpolation for `L_{ω₁ω}` sentences over an
  arbitrary language, bounding positive relation occurrences, negative relation occurrences, and
  function symbols.
* `FirstOrder.Language.Theoryω.lyndon_interpolation`: Lyndon interpolation for a countable
  `L_{ω₁ω}` theory `T` entailing a sentence `ψ`.

## References

* E. G. K. López-Escobar, *An interpolation theorem for denumerably long formulas*, Fundamenta
  Mathematicae **57** (1965), 253–272.
* H. J. Keisler, *Model Theory for Infinitary Logic*, North-Holland, 1971, §4.
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge
  University Press, 2016, Chapter 4.
* Adapted from `InfinitaryLogic/Methods/Interpolation/{Lyndon,LyndonArbitrary}.lean` in
  `cameronfreer/infinitary-logic` at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`.
  Divergences from that source: languages live in arbitrary universes and may have arbitrary
  cardinality (via `symbSublang`); propositional clauses delegate to `Theoryω.SignedInseparable`;
  quantifier and reflexivity clauses delegate to `Theoryω.exists_separator_constantSupport_subset`,
  `Theoryω.entails_ex_abstractConst_separator`, and `Theoryω.Entails.of_insert_inst`; and the
  countable-theory form `Theoryω.lyndon_interpolation` is included.
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
  ext c
  simp only [pairSupport, Set.mem_union, Set.mem_iUnion, Set.mem_insert_iff]
  aesop

private theorem pairSupport_insert_left_of_subset {Γ Δ : L[[ℕ]].Theoryω} {χ : L[[ℕ]].Sentenceω}
    (h : χ.constantSupport ⊆ pairSupport Γ Δ) :
    pairSupport (insert χ Γ) Δ = pairSupport Γ Δ := by
  rw [pairSupport_insert_left, Set.union_eq_self_of_subset_right h]

/-- The separator relation budget of a signed pair `(R₁, R₂)`: a separator `θ` entailed by `Γ` and
refuted by `Δ` may use at polarity `s` only symbols allowed at `s` in `R₁` and at `!s` in `R₂`
(matching `θ.not` on the right). -/
private def sharedSigned (R₁ R₂ : Bool → Set (Σ n, L[[ℕ]].Relations n)) (s : Bool) :
    Set (Σ n, L[[ℕ]].Relations n) :=
  R₁ s ∩ R₂ (!s)

private theorem sharedSigned_flip (R₁ R₂ : Bool → Set (Σ n, L[[ℕ]].Relations n)) :
    (fun s => sharedSigned R₁ R₂ (!s)) = sharedSigned R₂ R₁ := by
  funext s
  simp [sharedSigned, Set.inter_comm]

/-- A finite pair `(Γ, Δ)` over `L[[ℕ]]` bounded by signed relation budgets `R₁` and `R₂` and
admitting no signed separator within `sharedSigned R₁ R₂` and `pairSupport Γ Δ`. -/
private structure LyndonPair (R₁ R₂ : Bool → Set (Σ n, L[[ℕ]].Relations n))
    (Γ Δ : L[[ℕ]].Theoryω) : Prop where
  finite_left : Γ.Finite
  finite_right : Δ.Finite
  rel_left : ∀ χ ∈ Γ, ∀ s, χ.relationsInSigned s ⊆ R₁ s
  rel_right : ∀ χ ∈ Δ, ∀ s, χ.relationsInSigned s ⊆ R₂ s
  supp_left : ∀ χ ∈ Γ, χ.constantSupport.Finite
  supp_right : ∀ χ ∈ Δ, χ.constantSupport.Finite
  insep : Theoryω.SignedInseparable Γ Δ (sharedSigned R₁ R₂) (pairSupport Γ Δ)

namespace LyndonPair

variable {R₁ R₂ : Bool → Set (Σ n, L[[ℕ]].Relations n)} {Γ Δ : L[[ℕ]].Theoryω}

private theorem finite_pairSupport (h : LyndonPair R₁ R₂ Γ Δ) : (pairSupport Γ Δ).Finite :=
  (h.finite_left.biUnion h.supp_left).union (h.finite_right.biUnion h.supp_right)

/-- Swapping the two theories exchanges the two signed relation budgets. -/
private theorem symm (h : LyndonPair R₁ R₂ Γ Δ) : LyndonPair R₂ R₁ Δ Γ :=
  ⟨h.finite_right, h.finite_left, h.rel_right, h.rel_left, h.supp_right, h.supp_left, by
    simpa only [sharedSigned_flip, pairSupport_comm] using h.insep.symm⟩

private theorem insert_left (h : LyndonPair R₁ R₂ Γ Δ) {χ : L[[ℕ]].Sentenceω}
    (hrel : ∀ s, χ.relationsInSigned s ⊆ R₁ s) (hfin : χ.constantSupport.Finite)
    (hinsep : Theoryω.SignedInseparable (insert χ Γ) Δ (sharedSigned R₁ R₂)
      (pairSupport (insert χ Γ) Δ)) :
    LyndonPair R₁ R₂ (insert χ Γ) Δ :=
  ⟨h.finite_left.insert χ, h.finite_right,
    fun _ hψ => hψ.elim (fun e => e ▸ hrel) (h.rel_left _), h.rel_right,
    fun _ hψ => hψ.elim (fun e => e ▸ hfin) (h.supp_left _), h.supp_right, hinsep⟩

private theorem insert_left_of_insep (h : LyndonPair R₁ R₂ Γ Δ) {χ : L[[ℕ]].Sentenceω}
    (hrel : ∀ s, χ.relationsInSigned s ⊆ R₁ s) (hsupp : χ.constantSupport ⊆ pairSupport Γ Δ)
    (hinsep : Theoryω.SignedInseparable (insert χ Γ) Δ (sharedSigned R₁ R₂) (pairSupport Γ Δ)) :
    LyndonPair R₁ R₂ (insert χ Γ) Δ :=
  h.insert_left hrel (h.finite_pairSupport.subset hsupp)
    (by rwa [pairSupport_insert_left_of_subset hsupp])

private theorem not_bot_left (hp : LyndonPair R₁ R₂ Γ Δ) (hbot : ⊥ ∈ Γ) : False :=
  (Theoryω.isSatisfiable_iff_not_entails_bot.1 hp.insep.isSatisfiable_left)
    (Theoryω.entails_of_mem hbot)

private theorem not_contradiction_same (hp : LyndonPair R₁ R₂ Γ Δ) {φ : L[[ℕ]].Sentenceω}
    (hφ : φ ∈ Γ) (hnφ : φ.not ∈ Γ) : False :=
  (Theoryω.isSatisfiable_iff_not_entails_bot.1 hp.insep.isSatisfiable_left)
    (Theoryω.entails_iff.2 fun _ _ _ hM => (hM.not_notMem hφ hnφ).elim)

private theorem not_contradiction_cross (hp : LyndonPair R₁ R₂ Γ Δ) {φ : L[[ℕ]].Sentenceω}
    (hφ : φ ∈ Γ) (hnφ : φ.not ∈ Δ) : False :=
  Theoryω.signedInseparable_iff.1 hp.insep φ
    (fun s => Set.subset_inter (hp.rel_left φ hφ s) (by simpa using hp.rel_right φ.not hnφ (!s)))
    (subset_pairSupport_left hφ) (Theoryω.entails_of_mem hφ) (Theoryω.entails_of_mem hnφ)

private theorem imp_left (hp : LyndonPair R₁ R₂ Γ Δ) {φ ψ : L[[ℕ]].Sentenceω}
    (himp : φ.imp ψ ∈ Γ) :
    LyndonPair R₁ R₂ (insert φ.not Γ) Δ ∨ LyndonPair R₁ R₂ (insert ψ Γ) Δ := by
  have hsupp :=
    Set.union_subset_iff.1 (constantSupport_imp φ ψ ▸ subset_pairSupport_left (Δ := Δ) himp)
  refine (hp.insep.imp_left himp).imp
    (hp.insert_left_of_insep (fun s => ?_) (by simpa using hsupp.1))
    (hp.insert_left_of_insep (fun s => ?_) hsupp.2)
  · simpa using Set.subset_union_left.trans (by simpa using hp.rel_left _ himp s)
  · exact Set.subset_union_right.trans (by simpa using hp.rel_left _ himp s)

private theorem not_imp_left (hp : LyndonPair R₁ R₂ Γ Δ) {φ ψ : L[[ℕ]].Sentenceω}
    (hnimp : (φ.imp ψ).not ∈ Γ) :
    LyndonPair R₁ R₂ (insert φ Γ) Δ ∧ LyndonPair R₁ R₂ (insert ψ.not Γ) Δ := by
  have hsupp : φ.constantSupport ∪ ψ.constantSupport ⊆ pairSupport Γ Δ := by
    simpa using subset_pairSupport_left (Δ := Δ) hnimp
  obtain ⟨h₁, h₂⟩ := hp.insep.not_imp_left hnimp
  refine ⟨hp.insert_left_of_insep (fun s => ?_) (Set.union_subset_iff.1 hsupp).1 h₁,
    hp.insert_left_of_insep (fun s => ?_) (by simpa using (Set.union_subset_iff.1 hsupp).2) h₂⟩
  · exact Set.subset_union_left.trans (by simpa using hp.rel_left _ hnimp s)
  · simpa using Set.subset_union_right.trans (by simpa using hp.rel_left _ hnimp s)

private theorem iInf_left (hp : LyndonPair R₁ R₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hiInf : BoundedFormulaInf.iInf φs ∈ Γ) (k : ℕ) :
    LyndonPair R₁ R₂ (insert (φs k) Γ) Δ :=
  hp.insert_left_of_insep
    (fun s => (Set.subset_iUnion (fun i => (φs i).relationsInSigned s) k).trans
      (by simpa using hp.rel_left _ hiInf s))
    ((Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
      (by simpa using subset_pairSupport_left (Δ := Δ) hiInf))
    (hp.insep.iInf_left hiInf k)

private theorem not_iInf_left (hp : LyndonPair R₁ R₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hniInf : (BoundedFormulaInf.iInf φs).not ∈ Γ) :
    ∃ k, LyndonPair R₁ R₂ (insert (φs k).not Γ) Δ :=
  (hp.insep.not_iInf_left hniInf).imp fun k hk =>
    hp.insert_left_of_insep
      (fun s => by
        simpa using (Set.subset_iUnion (fun i => (φs i).relationsInSigned (!s)) k).trans
          (by simpa using hp.rel_left _ hniInf s))
      (by
        simpa using (Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
          (by simpa using subset_pairSupport_left (Δ := Δ) hniInf))
      hk

private theorem iSup_left (hp : LyndonPair R₁ R₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hiSup : BoundedFormulaInf.iSup φs ∈ Γ) :
    ∃ k, LyndonPair R₁ R₂ (insert (φs k) Γ) Δ :=
  (hp.insep.iSup_left hiSup).imp fun k hk =>
    hp.insert_left_of_insep
      (fun s => (Set.subset_iUnion (fun i => (φs i).relationsInSigned s) k).trans
        (by simpa using hp.rel_left _ hiSup s))
      ((Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
        (by simpa using subset_pairSupport_left (Δ := Δ) hiSup))
      hk

private theorem not_iSup_left (hp : LyndonPair R₁ R₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hniSup : (BoundedFormulaInf.iSup φs).not ∈ Γ) (k : ℕ) :
    LyndonPair R₁ R₂ (insert (φs k).not Γ) Δ :=
  hp.insert_left_of_insep
    (fun s => by
      simpa using (Set.subset_iUnion (fun i => (φs i).relationsInSigned (!s)) k).trans
        (by simpa using hp.rel_left _ hniSup s))
    (by
      simpa using (Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
        (by simpa using subset_pairSupport_left (Δ := Δ) hniSup))
    (hp.insep.not_iSup_left hniSup k)

private theorem all_left (hp : LyndonPair R₁ R₂ Γ Δ) {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (hall : φ.all ∈ Γ) (c : ℕ) :
    LyndonPair R₁ R₂ (insert (φ.inst (L.con c).term) Γ) Δ := by
  have hsupp : (φ.inst (L.con c).term).constantSupport ⊆ pairSupport Γ Δ ∪ {c} :=
    (constantSupport_inst_subset φ (L.con c).term).trans
      (Set.union_subset_union (by simpa using subset_pairSupport_left (Δ := Δ) hall) (by simp))
  refine hp.insert_left (fun s => by simpa using hp.rel_left φ.all hall s)
    ((hp.finite_pairSupport.union (Set.finite_singleton c)).subset hsupp)
    (Theoryω.signedInseparable_iff.2 fun θ hr hs hΓ hΔ => ?_)
  have hent : Γ.Entails (φ.inst (L.con c).term) := Theoryω.entails_iff.2 fun _ _ _ hM =>
    SentenceInf.realize_inst_of_realize_all (hM.realize_of_mem hall) _
  obtain ⟨χ, hχr, -, hχk, hΓχ, hΔχ⟩ := Theoryω.exists_separator_constantSupport_subset
    (Set.finite_singleton c) (fun _ => subset_pairSupport_left)
    (hs.trans (pairSupport_insert_left _ ▸ Set.union_subset Set.subset_union_left hsupp))
    (hent.cut hΓ) hΔ
  exact Theoryω.signedInseparable_iff.1 hp.insep χ (fun s => hχr s ▸ hr s) hχk hΓχ hΔχ

private theorem not_all_left (hp : LyndonPair R₁ R₂ Γ Δ) {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (hnall : φ.all.not ∈ Γ) :
    ∃ c, LyndonPair R₁ R₂ (insert (φ.inst (L.con c).term).not Γ) Δ := by
  classical
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset hp.finite_pairSupport.toFinset
  have hcK : c ∉ pairSupport Γ Δ := fun h => hc (hp.finite_pairSupport.mem_toFinset.2 h)
  have hφK : φ.constantSupport ⊆ pairSupport Γ Δ := by
    simpa using subset_pairSupport_left (Δ := Δ) hnall
  have hsupp : (φ.inst (L.con c).term).not.constantSupport ⊆ pairSupport Γ Δ ∪ {c} := by
    rw [constantSupport_not]
    exact (constantSupport_inst_subset φ (L.con c).term).trans
      (Set.union_subset_union hφK (by simp))
  refine ⟨c, hp.insert_left (fun s => by simpa using hp.rel_left φ.all.not hnall s)
    ((hp.finite_pairSupport.union (Set.finite_singleton c)).subset hsupp)
    (Theoryω.signedInseparable_iff.2 fun θ hr hs hΓ hΔ => ?_)⟩
  have hθ : θ.constantSupport ⊆ pairSupport Γ Δ ∪ {c} :=
    hs.trans (pairSupport_insert_left _ ▸ Set.union_subset Set.subset_union_left hsupp)
  obtain ⟨hΓ', hΔ'⟩ := Theoryω.entails_ex_abstractConst_separator
    (fun _ hχ h => hcK (subset_pairSupport_right hχ h)) hΓ hΔ
  refine Theoryω.signedInseparable_iff.1 hp.insep (abstractConst c θ).ex
    (fun s => by simpa using hr s) ?_ ?_ hΔ'
  · rw [constantSupport_ex, constantSupport_abstractConst]
    exact fun d hd => (hθ hd.1).resolve_right hd.2
  · refine Theoryω.Entails.of_insert_inst (φ := φ.not)
      (fun _ hχ h => hcK (subset_pairSupport_left hχ h))
      (fun h => hcK (hφK (by simpa using h))) (by simp)
      (Theoryω.entails_of_mem hnall).ex_not_of_not_all ?_
    rwa [inst_def, substBounds_not, ← inst_def]

private theorem eq_refl_left (hp : LyndonPair R₁ R₂ Γ Δ) (t : L[[ℕ]].Term (Empty ⊕ Fin 0)) :
    LyndonPair R₁ R₂ (insert (equal t t) Γ) Δ := by
  refine hp.insert_left (by simp) (by simpa using t.finite_constantSupport)
    (Theoryω.signedInseparable_iff.2 fun θ hr hs hΓ hΔ => ?_)
  have hent : Γ.Entails (equal t t) :=
    Theoryω.entails_iff.2 fun _ _ _ _ => SentenceInf.realize_equal_self t
  obtain ⟨χ, hχr, -, hχk, hΓχ, hΔχ⟩ := Theoryω.exists_separator_constantSupport_subset
    t.finite_constantSupport (fun _ => subset_pairSupport_left)
    (by simpa [pairSupport_insert_left] using hs) (hent.cut hΓ) hΔ
  exact Theoryω.signedInseparable_iff.1 hp.insep χ (fun s => hχr s ▸ hr s) hχk hΓχ hΔχ

private theorem eq_subst_same (hp : LyndonPair R₁ R₂ Γ Δ)
    {t t' : L[[ℕ]].Term (Empty ⊕ Fin 0)} {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (heq : equal t t' ∈ Γ) (hinst : φ.inst t ∈ Γ) :
    LyndonPair R₁ R₂ (insert (φ.inst t') Γ) Δ := by
  have htK :=
    Set.union_subset_iff.1 (constantSupport_equal t t' ▸ subset_pairSupport_left (Δ := Δ) heq)
  have hsupp : (φ.inst t').constantSupport ⊆ pairSupport Γ Δ :=
    (constantSupport_inst_subset φ t').trans
      (Set.union_subset
        ((constantSupport_subset_inst φ t).trans (subset_pairSupport_left (Δ := Δ) hinst)) htK.2)
  exact hp.insert_left_of_insep (fun s => by simpa using hp.rel_left (φ.inst t) hinst s) hsupp
    (hp.insep.insert_left_of_entails (Theoryω.entails_iff.2 fun _ _ _ hM =>
      SentenceInf.realize_inst_of_realize_equal (hM.realize_of_mem heq) (hM.realize_of_mem hinst)))

/-- Mixed equality substitution (`equal t t' ∈ Γ` and `φ.inst t ∈ Δ`): equality contributes no
signed relation occurrences, so `θ ↦ equal t t' ⊓ θ` pulls a separator back to `(Γ, Δ)`. -/
private theorem eq_subst_cross (hp : LyndonPair R₁ R₂ Γ Δ)
    {t t' : L[[ℕ]].Term (Empty ⊕ Fin 0)} {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (heq : equal t t' ∈ Γ) (hinst : φ.inst t ∈ Δ) :
    LyndonPair R₁ R₂ Γ (insert (φ.inst t') Δ) := by
  have htK :=
    Set.union_subset_iff.1 (constantSupport_equal t t' ▸ subset_pairSupport_left (Δ := Δ) heq)
  have hsupp : (φ.inst t').constantSupport ⊆ pairSupport Γ Δ :=
    (constantSupport_inst_subset φ t').trans
      (Set.union_subset
        ((constantSupport_subset_inst φ t).trans (subset_pairSupport_right (Γ := Γ) hinst)) htK.2)
  refine (hp.symm.insert_left_of_insep
    (fun s => by simpa using hp.rel_right (φ.inst t) hinst s)
    (pairSupport_comm Γ Δ ▸ hsupp) ?_).symm
  rw [← sharedSigned_flip, pairSupport_comm, Theoryω.SignedInseparable.symm_iff,
    Theoryω.signedInseparable_iff]
  intro θ hr hs hΓθ hΔθ
  refine Theoryω.signedInseparable_iff.1 hp.insep (equal t t' ⊓ θ) (fun s => by simpa using hr s)
    (by simp [htK.1, htK.2, hs])
    (Theoryω.entails_iff.2 fun M _ _ hM =>
      SentenceInf.realize_inf.2 ⟨hM.realize_of_mem heq, (Theoryω.entails_iff.1 hΓθ) M hM⟩)
    (Theoryω.entails_iff.2 fun M _ _ hM => ?_)
  rw [SentenceInf.realize_not, SentenceInf.realize_inf]
  rintro ⟨htM, hθM⟩
  exact SentenceInf.realize_not.1 ((Theoryω.entails_iff.1 hΔθ) M (Theoryω.model_insert_iff.2
    ⟨SentenceInf.realize_inst_of_realize_equal htM (hM.realize_of_mem hinst), hM⟩)) hθM

private theorem eq_name_left [L.IsRelational] (hp : LyndonPair R₁ R₂ Γ Δ)
    (t : L[[ℕ]].Term (Empty ⊕ Fin 0)) :
    ∃ c, LyndonPair R₁ R₂ (insert (equal (L.con c).term t) Γ) Δ := by
  obtain ⟨d, rfl⟩ := Term.exists_eq_con_of_isRelational t
  exact ⟨d, hp.eq_refl_left _⟩

end LyndonPair

/-- **The signed paired-inseparability consistency property** over `L[[ℕ]]` for a relational
language `L`. Right-hand and symmetric mixed cases reduce to the left-hand clauses via
`LyndonPair.symm`. -/
private def lyndonConsistencyProperty [L.IsRelational]
    (R₁ R₂ : Bool → Set (Σ n, L[[ℕ]].Relations n)) : ConsistencyProperty L where
  sets := {s | ∃ Γ Δ, s = Γ ∪ Δ ∧ LyndonPair R₁ R₂ Γ Δ}
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
unless `φ` and `ψ` already admit a Lyndon interpolant in `L`. -/
private theorem lyndonPair_root (φ ψ : L.Sentenceω)
    (hno : ¬ ∃ θ : L.Sentenceω,
      θ.relationsInSigned true ⊆ φ.relationsInSigned true ∩ ψ.relationsInSigned true ∧
      θ.relationsInSigned false ⊆ φ.relationsInSigned false ∩ ψ.relationsInSigned false ∧
      φ.Entails θ ∧ θ.Entails ψ) :
    LyndonPair
      (fun s => ((L.lhomWithConstants ℕ).onBoundedFormulaInf φ).relationsInSigned s)
      (fun s => ((L.lhomWithConstants ℕ).onBoundedFormulaInf ψ).not.relationsInSigned s)
      {(L.lhomWithConstants ℕ).onBoundedFormulaInf φ}
      {((L.lhomWithConstants ℕ).onBoundedFormulaInf ψ).not} := by
  let g := L.lhomWithConstants ℕ
  refine ⟨Set.finite_singleton _, Set.finite_singleton _,
    fun _ hχ _ => (Set.mem_singleton_iff.1 hχ) ▸ subset_rfl,
    fun _ hχ _ => (Set.mem_singleton_iff.1 hχ) ▸ subset_rfl,
    fun _ hχ => by rw [Set.mem_singleton_iff.1 hχ]; simp,
    fun _ hχ => by rw [Set.mem_singleton_iff.1 hχ]; simp,
    Theoryω.signedInseparable_iff.2 fun θ' hθ'rel hθ'supp hφθ' hψθ' => ?_⟩
  have hK : pairSupport ({g.onBoundedFormulaInf φ} : L[[ℕ]].Theoryω)
      {(g.onBoundedFormulaInf ψ).not} = ∅ := by simp [pairSupport, g]
  obtain ⟨θ, rfl⟩ := constantSupport_eq_empty_iff.1 (Set.subset_empty_iff.1 (hK ▸ hθ'supp))
  have hrel (s : Bool) : θ.relationsInSigned s ⊆ φ.relationsInSigned s ∩ ψ.relationsInSigned s := by
    have hsub := Set.preimage_mono
      (f := fun r : Σ k, L.Relations k =>
        (⟨r.1, (L.lhomWithConstants ℕ).onRelation r.2⟩ : Σ k, L[[ℕ]].Relations k))
      (hθ'rel s)
    simpa only [sharedSigned, relationsInSigned_not, Bool.not_not, Set.preimage_inter,
      (L.lhomWithConstants ℕ).preimage_relationsInSigned_onBoundedFormulaInf
        (fun _ => (L.lhomWithConstants_injective ℕ).onRelation)] using hsub
  refine hno ⟨θ, hrel true, hrel false, ?_, ?_⟩
  · exact (Sentenceω.entails_onBoundedFormulaInf_iff (L.lhomWithConstants_injective ℕ)).1
      (Sentenceω.entails_def.2 hφθ')
  · have hnot : Sentenceω.Entails ψ.not θ.not :=
      (Sentenceω.entails_onBoundedFormulaInf_iff (L.lhomWithConstants_injective ℕ)).1
        (by simpa [g] using Sentenceω.entails_def.2 hψθ')
    exact Sentenceω.entails_iff.2 fun M _ _ hθM => by
      by_contra hψM
      exact SentenceInf.realize_not.1 (hnot.realize M (SentenceInf.realize_not.2 hψM)) hθM

/-- Countable relational core: over a relational language with countably many relation symbols, any
valid entailment `φ ⊨ ψ` has a Lyndon interpolant. -/
private theorem lyndon_interpolation_relational_of_countable [L.IsRelational]
    [Countable (Σ n, L.Relations n)] (φ ψ : L.Sentenceω) (h : φ.Entails ψ) :
    ∃ θ : L.Sentenceω,
      θ.relationsInSigned true ⊆ φ.relationsInSigned true ∩ ψ.relationsInSigned true ∧
      θ.relationsInSigned false ⊆ φ.relationsInSigned false ∩ ψ.relationsInSigned false ∧
      φ.Entails θ ∧ θ.Entails ψ := by
  have : IsEmpty (Σ n, L.Functions n) := ⟨fun s => isEmptyElim s.2⟩
  by_contra hno
  let g := L.lhomWithConstants ℕ
  obtain ⟨M, _, _, _, hM, _⟩ :=
    (lyndonConsistencyProperty
      (fun s => (g.onBoundedFormulaInf φ).relationsInSigned s)
      (fun s => (g.onBoundedFormulaInf ψ).not.relationsInSigned s)).model_existence.{u, v, max u v}
        ⟨_, _, rfl, lyndonPair_root φ ψ hno⟩
        ((Set.countable_singleton _).union (Set.countable_singleton _))
  let : L.Structure M := g.reduct M
  have hφM : SentenceInf.Realize φ M :=
    (LHom.realize_sentenceInf_onBoundedFormulaInf g φ).1
      (hM.realize_of_mem (.inl (Set.mem_singleton _)))
  exact SentenceInf.realize_not.1 (hM.realize_of_mem (.inr (Set.mem_singleton _)))
    ((LHom.realize_sentenceInf_onBoundedFormulaInf g ψ).2 (h.realize M hφM))

/-- **Relational Lyndon interpolation for `L_{ω₁ω}`.** In any relational language `L` (of any
cardinality and in any universes), if an `L_{ω₁ω}` sentence `φ` entails `ψ`, there is an `L_{ω₁ω}`
sentence `θ` whose positively occurring relation symbols lie in
`φ.relationsInSigned true ∩ ψ.relationsInSigned true` and whose negatively occurring relation
symbols lie in `φ.relationsInSigned false ∩ ψ.relationsInSigned false`, with `φ ⊨ θ` and `θ ⊨ ψ`.
Equality is logical, so `θ` may use it freely. -/
theorem lyndon_interpolation_relational [L.IsRelational] (φ ψ : L.Sentenceω)
    (h : φ.Entails ψ) :
    ∃ θ : L.Sentenceω,
      θ.relationsInSigned true ⊆ φ.relationsInSigned true ∩ ψ.relationsInSigned true ∧
      θ.relationsInSigned false ⊆ φ.relationsInSigned false ∩ ψ.relationsInSigned false ∧
      φ.Entails θ ∧ θ.Entails ψ := by
  let F : Set (Σ n, L.Functions n) := ∅
  let R : Set (Σ n, L.Relations n) := φ.relationsIn ∪ ψ.relationsIn
  have : Countable R := (φ.relationsIn_countable.union ψ.relationsIn_countable).to_subtype
  have hFφ : φ.functionsIn ⊆ F := fun s _ => isEmptyElim s.2
  have hFψ : ψ.functionsIn ⊆ F := fun s _ => isEmptyElim s.2
  let φ₀ : (symbSublang F R).Sentenceω := φ.restrictSymbols hFφ Set.subset_union_left
  let ψ₀ : (symbSublang F R).Sentenceω := ψ.restrictSymbols hFψ Set.subset_union_right
  let incl := symbSublangIncl F R
  have hφ₀ : incl.onBoundedFormulaInf φ₀ = φ :=
    onBoundedFormulaInf_restrictSymbols φ hFφ Set.subset_union_left
  have hψ₀ : incl.onBoundedFormulaInf ψ₀ = ψ :=
    onBoundedFormulaInf_restrictSymbols ψ hFψ Set.subset_union_right
  have h₀ : φ₀.Entails ψ₀ :=
    (Sentenceω.entails_onBoundedFormulaInf_iff (symbSublangIncl_injective F R)).1
      (by rwa [hφ₀, hψ₀])
  obtain ⟨θ₀, hpos₀, hneg₀, hφθ₀, hθψ₀⟩ :=
    lyndon_interpolation_relational_of_countable φ₀ ψ₀ h₀
  have hlift (s : Bool)
      (hs₀ : θ₀.relationsInSigned s ⊆ φ₀.relationsInSigned s ∩ ψ₀.relationsInSigned s) :
      (incl.onBoundedFormulaInf θ₀).relationsInSigned s ⊆
        φ.relationsInSigned s ∩ ψ.relationsInSigned s := by
    rw [incl.relationsInSigned_onBoundedFormulaInf]
    refine ((Set.image_mono hs₀).trans (Set.image_inter_subset _ _ _)).trans ?_
    rw [← incl.relationsInSigned_onBoundedFormulaInf,
      ← incl.relationsInSigned_onBoundedFormulaInf, hφ₀, hψ₀]
  exact ⟨incl.onBoundedFormulaInf θ₀, hlift true hpos₀, hlift false hneg₀,
    hφ₀ ▸ hφθ₀.onBoundedFormulaInf incl, hψ₀ ▸ hθψ₀.onBoundedFormulaInf incl⟩

/-- Forward graph-translation entailment using `Theoryω.conjunction` of `graphAxioms`. -/
private theorem entails_relationalize_of_entails {φ ψ : L.Sentenceω} (h : φ.Entails ψ) :
    Sentenceω.Entails
      ((graphAxioms φ.functionsIn).conjunction φ.functionsIn_countable.graphAxioms ⊓
        φ.relationalize)
      (((graphAxioms ψ.functionsIn).conjunction ψ.functionsIn_countable.graphAxioms).imp
        ψ.relationalize) := by
  refine Sentenceω.entails_iff.2 fun N _ _ hN => ?_
  obtain ⟨hA₁, hφN⟩ := SentenceInf.realize_inf.1 hN
  refine SentenceInf.realize_imp.2 fun hA₂ => ?_
  have hU : (graphAxioms (φ.functionsIn ∪ ψ.functionsIn)).Model N := by
    rw [graphAxioms_union, Theoryω.model_union_iff]
    exact ⟨(Theoryω.realize_conjunction_iff _).1 hA₁, (Theoryω.realize_conjunction_iff _).1 hA₂⟩
  rw [SentenceInf.realize_def, FormulaInf.realize_def] at hφN ⊢
  let : L.Structure N := reconstructStructure L N
  have hφ' : SentenceInf.Realize φ N := by
    rw [SentenceInf.realize_def, FormulaInf.realize_def]
    exact (φ.realize_relationalize_reconstructStructure hU Set.subset_union_left _ _).1 hφN
  have hψ' := h.realize N hφ'
  rw [SentenceInf.realize_def, FormulaInf.realize_def] at hψ'
  exact (ψ.realize_relationalize_reconstructStructure hU Set.subset_union_right _ _).2 hψ'

/-- **Lyndon interpolation for `L_{ω₁ω}`.** In any language `L` (of any cardinality, with function
symbols, and in any universes), if an `L_{ω₁ω}` sentence `φ` entails `ψ`, there is an `L_{ω₁ω}`
sentence `θ` whose occurring function symbols lie in `φ.functionsIn ∩ ψ.functionsIn`, whose
positively occurring relation symbols lie in `φ.relationsInSigned true ∩ ψ.relationsInSigned true`,
and whose negatively occurring relation symbols lie in
`φ.relationsInSigned false ∩ ψ.relationsInSigned false`, such that `φ` entails `θ` and `θ` entails
`ψ`. Equality is logical, so `θ` may use it freely. -/
theorem lyndon_interpolation (φ ψ : L.Sentenceω) (h : φ.Entails ψ) :
    ∃ θ : L.Sentenceω, θ.functionsIn ⊆ φ.functionsIn ∩ ψ.functionsIn ∧
      θ.relationsInSigned true ⊆ φ.relationsInSigned true ∩ ψ.relationsInSigned true ∧
      θ.relationsInSigned false ⊆ φ.relationsInSigned false ∩ ψ.relationsInSigned false ∧
      φ.Entails θ ∧ θ.Entails ψ := by
  have hF₁ : (graphAxioms φ.functionsIn).Countable := φ.functionsIn_countable.graphAxioms
  have hF₂ : (graphAxioms ψ.functionsIn).Countable := ψ.functionsIn_countable.graphAxioms
  obtain ⟨θ, hpos, hneg, hφθ, hθψ⟩ :=
    lyndon_interpolation_relational _ _ (entails_relationalize_of_entails h)
  have hsym (s : Bool) : θ.relationsInSigned s ⊆
      relSym (φ.functionsIn ∩ ψ.functionsIn) (φ.relationsInSigned s ∩ ψ.relationsInSigned s) := by
    rw [← relSym_inter,
      ← relationsInSigned_conjunction_graphAxioms_inf_relationalize s hF₁ φ subset_rfl,
      ← relationsInSigned_conjunction_graphAxioms_imp_relationalize s hF₂ ψ subset_rfl]
    cases s
    · exact hneg
    · exact hpos
  refine ⟨θ.backTranslate, ?_, ?_, ?_, ?_, ?_⟩
  · rw [functionsIn_backTranslate, ← θ.relationsInSigned_union_not true, Set.preimage_union]
    exact Set.union_subset (by simpa using Set.preimage_mono (f := graphRelSym) (hsym true))
      (by simpa using Set.preimage_mono (f := graphRelSym) (hsym (!true)))
  · simpa using Set.preimage_mono (f := baseRelSym) (hsym true)
  · simpa using Set.preimage_mono (f := baseRelSym) (hsym false)
  · refine Sentenceω.entails_iff.2 fun M _ _ hφM => ?_
    let := graphExpansion L M
    have hA₁ : SentenceInf.Realize ((graphAxioms φ.functionsIn).conjunction hF₁) M :=
      (Theoryω.realize_conjunction_iff hF₁).2 (model_graphAxioms_graphExpansion L M _)
    have hθM := hφθ.realize M (SentenceInf.realize_inf.2 ⟨hA₁, by
      simpa only [SentenceInf.realize_def, FormulaInf.realize_def, realize_relationalize]
        using hφM⟩)
    simpa only [SentenceInf.realize_def, FormulaInf.realize_def, realize_backTranslate] using hθM
  · refine Sentenceω.entails_iff.2 fun M _ _ hθM => ?_
    let := graphExpansion L M
    have hA₂ : SentenceInf.Realize ((graphAxioms ψ.functionsIn).conjunction hF₂) M :=
      (Theoryω.realize_conjunction_iff hF₂).2 (model_graphAxioms_graphExpansion L M _)
    have hψM := SentenceInf.realize_imp.1 (hθψ.realize M (by
      simpa only [SentenceInf.realize_def, FormulaInf.realize_def, realize_backTranslate]
        using hθM)) hA₂
    simpa only [SentenceInf.realize_def, FormulaInf.realize_def, realize_relationalize] using hψM

/-- **Countable-theory Lyndon interpolation.** If a countable `L_{ω₁ω}` theory `T` entails `ψ`,
there is an interpolant `θ` whose occurring function symbols appear in both `T` and `ψ`, whose
positively occurring relation symbols appear positively in some sentence of `T` and positively in
`ψ`, and whose negatively occurring relation symbols appear negatively in some sentence of `T` and
negatively in `ψ`, with `T ⊨ θ` and `θ ⊨ ψ`. -/
theorem Theoryω.lyndon_interpolation {T : L.Theoryω} (hT : T.Countable) (ψ : L.Sentenceω)
    (h : T.Entails ψ) :
    ∃ θ : L.Sentenceω, θ.functionsIn ⊆ (⋃ φ ∈ T, φ.functionsIn) ∩ ψ.functionsIn ∧
      θ.relationsInSigned true ⊆
        (⋃ φ ∈ T, φ.relationsInSigned true) ∩ ψ.relationsInSigned true ∧
      θ.relationsInSigned false ⊆
        (⋃ φ ∈ T, φ.relationsInSigned false) ∩ ψ.relationsInSigned false ∧
      T.Entails θ ∧ θ.Entails ψ := by
  obtain ⟨θ, hfun, hpos, hneg, hTθ, hθψ⟩ := Language.lyndon_interpolation (T.conjunction hT) ψ
    ((Theoryω.entails_iff_conjunction_entails hT).1 h)
  rw [Theoryω.relationsInSigned_conjunction] at hpos hneg
  refine ⟨θ, hfun.trans (Set.inter_subset_inter_left _ ?_), hpos, hneg,
    (Theoryω.entails_iff_conjunction_entails hT).2 hTθ, hθψ⟩
  rw [Theoryω.conjunction_def, functionsIn_iInfAlong]
  exact Set.iUnion_subset fun φ => Set.subset_biUnion_of_mem φ.2

end Lyndon

end FirstOrder.Language
