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

López-Escobar's polarity-sensitive interpolation theorem refines Craig interpolation for `L_{ω₁ω}`
by tracking positive and negative occurrences of relation symbols separately: whenever an `L_{ω₁ω}`
sentence `φ` entails `ψ`, there is an `L_{ω₁ω}` sentence `θ` with `φ ⊨ θ` and `θ ⊨ ψ` such that
every relation symbol occurring positively in `θ` occurs positively in both `φ` and `ψ`, every
relation symbol occurring negatively in `θ` occurs negatively in both `φ` and `ψ`, and every
function symbol occurring in `θ` occurs in both `φ` and `ψ`. Logical equality contributes to
neither relation polarity (`BoundedFormulaInf.relationsInSigned_equal`), so `θ` may use equality
freely; López-Escobar's separate condition on where equality occurs is not part of the statements
here.

The file establishes Lyndon interpolation in arbitrary universes for relational languages of
arbitrary cardinality (`lyndon_interpolation_relational`), transfers it to arbitrary languages with
function symbols (`lyndon_interpolation`), deduces the countable-theory form
(`Theoryω.lyndon_interpolation`), and recovers unsigned Craig interpolation from the two signed
relation bounds (`craig_of_lyndon_interpolation`).

## Main results

* `FirstOrder.Language.lyndon_interpolation_relational`: relational Lyndon interpolation for
  `L_{ω₁ω}` sentences over a relational language of arbitrary cardinality.
* `FirstOrder.Language.lyndon_interpolation`: Lyndon interpolation for `L_{ω₁ω}` sentences over an
  arbitrary language, bounding the function symbols and both relation polarities of the
  interpolant.
* `FirstOrder.Language.Theoryω.lyndon_interpolation`: Lyndon interpolation for a countable
  `L_{ω₁ω}` theory `T` entailing a sentence `ψ`.
* `FirstOrder.Language.craig_of_lyndon_interpolation`: unsigned Craig interpolation recovered from
  `lyndon_interpolation`.

## References

* E. G. K. López-Escobar, *An interpolation theorem for denumerably long formulas*, Fundamenta
  Mathematicae **57** (1965), 253–272.
* H. J. Keisler, *Model Theory for Infinitary Logic*, North-Holland, 1971, §4.
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge
  University Press, 2016, §4.2.
* The proof structure refines the paired-inseparability consistency property of
  `TauCeti.ModelTheory.Interpolation.Craig` and adapts
  `InfinitaryLogic/Methods/Interpolation/{LyndonSublanguage,LyndonRelationalize,
  LyndonArbitrary}.lean` in `cameronfreer/infinitary-logic` at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`. Divergences from `cameronfreer/infinitary-logic`:
  the signed paired-inseparability consistency property is formulated over `L[[ℕ]]` in arbitrary
  universes without assuming `[L.IsRelational]`, using `Theoryω.SignedInseparable` for
  propositional decomposition and `BoundedFormulaInf.abstractConst` for polarity-preserving
  constant elimination; symbol countability is removed by restricting to `symbSublang`; and the
  transfer to languages with function symbols uses the exact signed occurrence identities for the
  conjunction of `graphAxioms` paired with `BoundedFormulaInf.relationalize`.
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
  simp only [pairSupport, Set.biUnion_insert, Set.union_assoc, Set.union_comm]

private theorem pairSupport_insert_left_of_subset {Γ Δ : L[[ℕ]].Theoryω} {χ : L[[ℕ]].Sentenceω}
    (h : χ.constantSupport ⊆ pairSupport Γ Δ) :
    pairSupport (insert χ Γ) Δ = pairSupport Γ Δ := by
  rw [pairSupport_insert_left, Set.union_eq_self_of_subset_right h]

private theorem pairSupport_insert_right_of_subset {Γ Δ : L[[ℕ]].Theoryω} {χ : L[[ℕ]].Sentenceω}
    (h : χ.constantSupport ⊆ pairSupport Γ Δ) :
    pairSupport Γ (insert χ Δ) = pairSupport Γ Δ := by
  rw [pairSupport_comm, pairSupport_insert_left_of_subset (pairSupport_comm Γ Δ ▸ h),
    pairSupport_comm]

/-- The signed relation budget of separators for a pair with left budget `B₁` and right budget
`B₂`: a sentence entailed on the left and refuted on the right pairs polarity `s` on the left with
the flipped polarity `!s` on the right. -/
private abbrev sepBudget (B₁ B₂ : Bool → Set (Σ n, L[[ℕ]].Relations n)) (s : Bool) :
    Set (Σ n, L[[ℕ]].Relations n) :=
  B₁ s ∩ B₂ (!s)

private theorem sepBudget_flip (B₁ B₂ : Bool → Set (Σ n, L[[ℕ]].Relations n)) :
    (fun s => sepBudget B₁ B₂ (!s)) = sepBudget B₂ B₁ := by
  funext s
  simp [sepBudget, Set.inter_comm]

/-- A valid `(B₁, B₂)`-signed-inseparable finite pair `(Γ, Δ)` over `L[[ℕ]]`. -/
private structure SignedPair (B₁ B₂ : Bool → Set (Σ n, L[[ℕ]].Relations n))
    (Γ Δ : L[[ℕ]].Theoryω) : Prop where
  finite_left : Γ.Finite
  finite_right : Δ.Finite
  rel_left : ∀ χ ∈ Γ, ∀ s, χ.relationsInSigned s ⊆ B₁ s
  rel_right : ∀ χ ∈ Δ, ∀ s, χ.relationsInSigned s ⊆ B₂ s
  supp_left : ∀ χ ∈ Γ, χ.constantSupport.Finite
  supp_right : ∀ χ ∈ Δ, χ.constantSupport.Finite
  insep : Theoryω.SignedInseparable Γ Δ (sepBudget B₁ B₂) (pairSupport Γ Δ)

namespace SignedPair

variable {B₁ B₂ : Bool → Set (Σ n, L[[ℕ]].Relations n)} {Γ Δ : L[[ℕ]].Theoryω}

private theorem finite_pairSupport (hp : SignedPair B₁ B₂ Γ Δ) : (pairSupport Γ Δ).Finite :=
  (hp.finite_left.biUnion hp.supp_left).union (hp.finite_right.biUnion hp.supp_right)

/-- Swapping `(Γ, Δ)` swaps `(B₁, B₂)` because negating a separator flips its polarities. -/
private theorem symm (hp : SignedPair B₁ B₂ Γ Δ) : SignedPair B₂ B₁ Δ Γ :=
  ⟨hp.finite_right, hp.finite_left, hp.rel_right, hp.rel_left, hp.supp_right, hp.supp_left,
    sepBudget_flip B₁ B₂ ▸ pairSupport_comm Γ Δ ▸ hp.insep.symm⟩

private theorem insert_left (hp : SignedPair B₁ B₂ Γ Δ) {χ : L[[ℕ]].Sentenceω}
    (hrel : ∀ s, χ.relationsInSigned s ⊆ B₁ s) (hfin : χ.constantSupport.Finite)
    (hinsep : Theoryω.SignedInseparable (insert χ Γ) Δ (sepBudget B₁ B₂)
      (pairSupport (insert χ Γ) Δ)) :
    SignedPair B₁ B₂ (insert χ Γ) Δ :=
  ⟨hp.finite_left.insert χ, hp.finite_right,
    fun _ hψ => hψ.elim (fun e => e ▸ hrel) (hp.rel_left _), hp.rel_right,
    fun _ hψ => hψ.elim (fun e => e ▸ hfin) (hp.supp_left _), hp.supp_right, hinsep⟩

private theorem insert_left_of_insep (hp : SignedPair B₁ B₂ Γ Δ) {χ : L[[ℕ]].Sentenceω}
    (hrel : ∀ s, χ.relationsInSigned s ⊆ B₁ s) (hsupp : χ.constantSupport ⊆ pairSupport Γ Δ)
    (hinsep : Theoryω.SignedInseparable (insert χ Γ) Δ (sepBudget B₁ B₂) (pairSupport Γ Δ)) :
    SignedPair B₁ B₂ (insert χ Γ) Δ :=
  hp.insert_left hrel (hp.finite_pairSupport.subset hsupp)
    (pairSupport_insert_left_of_subset hsupp ▸ hinsep)

private theorem not_bot_left (hp : SignedPair B₁ B₂ Γ Δ) (hbot : ⊥ ∈ Γ) : False :=
  (Theoryω.isSatisfiable_iff_not_entails_bot.1 hp.insep.isSatisfiable_left)
    (Theoryω.entails_of_mem hbot)

private theorem not_contradiction_same (hp : SignedPair B₁ B₂ Γ Δ) {φ : L[[ℕ]].Sentenceω}
    (hφ : φ ∈ Γ) (hnφ : φ.not ∈ Γ) : False :=
  (Theoryω.isSatisfiable_iff_not_entails_bot.1 hp.insep.isSatisfiable_left)
    (Theoryω.entails_iff.2 fun _ _ _ hM => (hM.not_notMem hφ hnφ).elim)

private theorem not_contradiction_cross (hp : SignedPair B₁ B₂ Γ Δ) {φ : L[[ℕ]].Sentenceω}
    (hφ : φ ∈ Γ) (hnφ : φ.not ∈ Δ) : False :=
  Theoryω.signedInseparable_iff.1 hp.insep φ
    (fun s => Set.subset_inter (hp.rel_left φ hφ s) (by simpa using hp.rel_right φ.not hnφ (!s)))
    (subset_pairSupport_left hφ) (Theoryω.entails_of_mem hφ) (Theoryω.entails_of_mem hnφ)

private theorem imp_left (hp : SignedPair B₁ B₂ Γ Δ) {φ ψ : L[[ℕ]].Sentenceω}
    (himp : φ.imp ψ ∈ Γ) :
    SignedPair B₁ B₂ (insert φ.not Γ) Δ ∨ SignedPair B₁ B₂ (insert ψ Γ) Δ := by
  have hrel : ∀ s, φ.relationsInSigned (!s) ∪ ψ.relationsInSigned s ⊆ B₁ s := fun s => by
    simpa only [relationsInSigned_imp] using hp.rel_left (φ.imp ψ) himp s
  have hsupp : φ.constantSupport ∪ ψ.constantSupport ⊆ pairSupport Γ Δ := by
    simpa only [constantSupport_imp] using subset_pairSupport_left (Δ := Δ) himp
  exact (hp.insep.imp_left himp).imp
    (hp.insert_left_of_insep
      (fun s => by simpa only [relationsInSigned_not] using Set.subset_union_left.trans (hrel s))
      (by simpa only [constantSupport_not] using Set.subset_union_left.trans hsupp))
    (hp.insert_left_of_insep
      (fun s => Set.subset_union_right.trans (hrel s))
      (Set.subset_union_right.trans hsupp))

private theorem not_imp_left (hp : SignedPair B₁ B₂ Γ Δ) {φ ψ : L[[ℕ]].Sentenceω}
    (hnimp : (φ.imp ψ).not ∈ Γ) :
    SignedPair B₁ B₂ (insert φ Γ) Δ ∧ SignedPair B₁ B₂ (insert ψ.not Γ) Δ := by
  have hrel := hp.rel_left (φ.imp ψ).not hnimp
  have hsupp : φ.constantSupport ∪ ψ.constantSupport ⊆ pairSupport Γ Δ := by
    simpa using subset_pairSupport_left (Δ := Δ) hnimp
  exact (hp.insep.not_imp_left hnimp).imp
    (hp.insert_left_of_insep
      (fun s => Set.subset_union_left.trans (by simpa using hrel s))
      (Set.subset_union_left.trans hsupp))
    (hp.insert_left_of_insep
      (fun s => by simpa using Set.subset_union_right.trans (by simpa using hrel s))
      (by simpa using Set.subset_union_right.trans hsupp))

private theorem iInf_left (hp : SignedPair B₁ B₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hiInf : BoundedFormulaInf.iInf φs ∈ Γ) (k : ℕ) :
    SignedPair B₁ B₂ (insert (φs k) Γ) Δ :=
  hp.insert_left_of_insep
    (fun s => (Set.subset_iUnion (fun i => (φs i).relationsInSigned s) k).trans
      (by simpa using hp.rel_left _ hiInf s))
    ((Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
      (by simpa using subset_pairSupport_left (Δ := Δ) hiInf))
    (hp.insep.iInf_left hiInf k)

private theorem not_iInf_left (hp : SignedPair B₁ B₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hniInf : (BoundedFormulaInf.iInf φs).not ∈ Γ) :
    ∃ k, SignedPair B₁ B₂ (insert (φs k).not Γ) Δ :=
  (hp.insep.not_iInf_left hniInf).imp fun k hk =>
    hp.insert_left_of_insep
      (fun s => by
        simpa using (Set.subset_iUnion (fun i => (φs i).relationsInSigned (!s)) k).trans
          (by simpa using hp.rel_left _ hniInf s))
      (by
        simpa using (Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
          (by simpa using subset_pairSupport_left (Δ := Δ) hniInf))
      hk

private theorem iSup_left (hp : SignedPair B₁ B₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hiSup : BoundedFormulaInf.iSup φs ∈ Γ) :
    ∃ k, SignedPair B₁ B₂ (insert (φs k) Γ) Δ :=
  (hp.insep.iSup_left hiSup).imp fun k hk =>
    hp.insert_left_of_insep
      (fun s => (Set.subset_iUnion (fun i => (φs i).relationsInSigned s) k).trans
        (by simpa using hp.rel_left _ hiSup s))
      ((Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
        (by simpa using subset_pairSupport_left (Δ := Δ) hiSup))
      hk

private theorem not_iSup_left (hp : SignedPair B₁ B₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hniSup : (BoundedFormulaInf.iSup φs).not ∈ Γ) (k : ℕ) :
    SignedPair B₁ B₂ (insert (φs k).not Γ) Δ :=
  hp.insert_left_of_insep
    (fun s => by
      simpa using (Set.subset_iUnion (fun i => (φs i).relationsInSigned (!s)) k).trans
        (by simpa using hp.rel_left _ hniSup s))
    (by
      simpa using (Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
        (by simpa using subset_pairSupport_left (Δ := Δ) hniSup))
    (hp.insep.not_iSup_left hniSup k)

/-- Extending the separator constant budget of `hp` by any finite set `E` preserves signed
inseparability, via universal abstraction of the extra constants absent from `Γ`. -/
private theorem insep_union_finite (hp : SignedPair B₁ B₂ Γ Δ) {E : Set ℕ} (hE : E.Finite) :
    Theoryω.SignedInseparable Γ Δ (sepBudget B₁ B₂) (pairSupport Γ Δ ∪ E) := by
  rw [Theoryω.signedInseparable_iff]
  intro θ hr hk hΓ hΔ
  obtain ⟨χ, hχr, -, hχk, hΓχ, hΔχ⟩ :=
    Theoryω.exists_separator_constantSupport_subset hE (fun _ => subset_pairSupport_left) hk hΓ hΔ
  exact Theoryω.signedInseparable_iff.1 hp.insep χ (fun s => (hχr s).trans_subset (hr s))
    hχk hΓχ hΔχ

/-- Witness-introduction step on `SignedPair`: if `Γ` entails `ψ.ex` and `c` is fresh for `Γ`, `Δ`,
`ψ`, and a finite extra constant set `E`, adjoining `ψ.inst (L.con c).term` preserves signed
inseparability within `pairSupport Γ Δ ∪ E ∪ {c}`. -/
private theorem insep_insert_inst_of_ex (hp : SignedPair B₁ B₂ Γ Δ) {E : Set ℕ} (hE : E.Finite)
    {ψ : L[[ℕ]].BoundedFormulaω Empty 1} {c : ℕ}
    (hc : c ∉ pairSupport Γ Δ ∪ E) (hcψ : c ∉ ψ.constantSupport) (hex : Γ.Entails ψ.ex) :
    Theoryω.SignedInseparable (insert (ψ.inst (L.con c).term) Γ) Δ (sepBudget B₁ B₂)
      ((pairSupport Γ Δ ∪ E) ∪ {c}) := by
  rw [Theoryω.signedInseparable_iff]
  intro θ hr hk hΓ hΔ
  obtain ⟨hΓ', hΔ'⟩ := Theoryω.entails_ex_abstractConst_separator
    (fun _ hχ h => hc (.inl (subset_pairSupport_right hχ h))) hΓ hΔ
  have hk' : (abstractConst c θ).ex.constantSupport ⊆ pairSupport Γ Δ ∪ E := by
    rw [constantSupport_ex, constantSupport_abstractConst]
    exact fun d hd => (hk hd.1).resolve_right hd.2
  exact Theoryω.signedInseparable_iff.1 (hp.insep_union_finite hE) (abstractConst c θ).ex
    (by simpa using hr) hk'
    (Theoryω.Entails.of_insert_inst
      (fun _ hχ h => hc (.inl (subset_pairSupport_left hχ h))) hcψ
      (fun h => hc (hk' h)) hex hΓ')
    hΔ'

private theorem all_left (hp : SignedPair B₁ B₂ Γ Δ) {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (hall : φ.all ∈ Γ) (c : ℕ) :
    SignedPair B₁ B₂ (insert (φ.inst (L.con c).term) Γ) Δ := by
  have hsupp : (φ.inst (L.con c).term).constantSupport ⊆ pairSupport Γ Δ ∪ {c} :=
    (constantSupport_inst_subset φ (L.con c).term).trans
      (Set.union_subset_union (by simpa using subset_pairSupport_left (Δ := Δ) hall) (by simp))
  refine hp.insert_left (fun s => by simpa using hp.rel_left φ.all hall s)
    ((hp.finite_pairSupport.union (Set.finite_singleton c)).subset hsupp) ?_
  have hent : Γ.Entails (φ.inst (L.con c).term) :=
    Theoryω.entails_iff.2 fun _ _ _ hM =>
      SentenceInf.realize_inst_of_realize_all (hM.realize_of_mem hall) _
  exact ((hp.insep_union_finite (Set.finite_singleton c)).insert_left_of_entails hent).mono_budget
    (fun _ => subset_rfl)
    (pairSupport_insert_left _ ▸ Set.union_subset Set.subset_union_left hsupp)

private theorem not_all_left (hp : SignedPair B₁ B₂ Γ Δ) {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (hnall : φ.all.not ∈ Γ) :
    ∃ c, SignedPair B₁ B₂ (insert (φ.inst (L.con c).term).not Γ) Δ := by
  obtain ⟨c, hc⟩ := hp.finite_pairSupport.infinite_compl.nonempty
  have hφK : φ.constantSupport ⊆ pairSupport Γ Δ := by
    simpa using subset_pairSupport_left (Δ := Δ) hnall
  have hsupp : (φ.inst (L.con c).term).not.constantSupport ⊆ pairSupport Γ Δ ∪ {c} := by
    rw [constantSupport_not]
    exact (constantSupport_inst_subset φ (L.con c).term).trans
      (Set.union_subset_union hφK (by simp))
  refine ⟨c, hp.insert_left (fun s => by simpa using hp.rel_left φ.all.not hnall s)
    ((hp.finite_pairSupport.union (Set.finite_singleton c)).subset hsupp) ?_⟩
  have hinsep := hp.insep_insert_inst_of_ex Set.finite_empty (ψ := φ.not)
    (by simpa using hc) (by simpa using fun h => hc (hφK h))
    (Theoryω.entails_of_mem hnall).ex_not_of_not_all
  rw [Set.union_empty, inst_def, substBounds_not, ← inst_def] at hinsep
  exact hinsep.mono_budget (fun _ => subset_rfl)
    (pairSupport_insert_left _ ▸ Set.union_subset Set.subset_union_left hsupp)

private theorem eq_refl_left (hp : SignedPair B₁ B₂ Γ Δ) (t : L[[ℕ]].Term (Empty ⊕ Fin 0)) :
    SignedPair B₁ B₂ (insert (equal t t) Γ) Δ := by
  refine hp.insert_left (by simp) (by simpa using t.finite_constantSupport) ?_
  have hent : Γ.Entails (equal t t) :=
    Theoryω.entails_iff.2 fun _ _ _ _ => SentenceInf.realize_equal_self t
  exact ((hp.insep_union_finite t.finite_constantSupport).insert_left_of_entails hent).mono_budget
    (fun _ => subset_rfl) (by simp [pairSupport_insert_left])

private theorem eq_subst_same (hp : SignedPair B₁ B₂ Γ Δ)
    {t t' : L[[ℕ]].Term (Empty ⊕ Fin 0)} {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (heq : equal t t' ∈ Γ) (hinst : φ.inst t ∈ Γ) :
    SignedPair B₁ B₂ (insert (φ.inst t') Γ) Δ := by
  have htK :=
    Set.union_subset_iff.1 (constantSupport_equal t t' ▸ subset_pairSupport_left (Δ := Δ) heq)
  have hsupp : (φ.inst t').constantSupport ⊆ pairSupport Γ Δ :=
    (constantSupport_inst_subset φ t').trans
      (Set.union_subset
        ((constantSupport_subset_inst φ t).trans (subset_pairSupport_left (Δ := Δ) hinst)) htK.2)
  refine hp.insert_left_of_insep (fun s => by simpa using hp.rel_left (φ.inst t) hinst s) hsupp
    (hp.insep.insert_left_of_entails (Theoryω.entails_iff.2 fun _ _ _ hM =>
      SentenceInf.realize_inst_of_realize_equal (hM.realize_of_mem heq) (hM.realize_of_mem hinst)))

/-- Mixed equality substitution (`equal t t' ∈ Γ` and `φ.inst t ∈ Δ`): logical equality contributes
to neither relation polarity, so `θ ↦ equal t t' ⊓ θ` transfers any signed separator of
`(Γ, insert (φ.inst t') Δ)` back to `(Γ, Δ)`. -/
private theorem eq_subst_cross (hp : SignedPair B₁ B₂ Γ Δ)
    {t t' : L[[ℕ]].Term (Empty ⊕ Fin 0)} {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (heq : equal t t' ∈ Γ) (hinst : φ.inst t ∈ Δ) :
    SignedPair B₁ B₂ Γ (insert (φ.inst t') Δ) := by
  have htK :=
    Set.union_subset_iff.1 (constantSupport_equal t t' ▸ subset_pairSupport_left (Δ := Δ) heq)
  have hsupp : (φ.inst t').constantSupport ⊆ pairSupport Γ Δ :=
    (constantSupport_inst_subset φ t').trans
      (Set.union_subset
        ((constantSupport_subset_inst φ t).trans (subset_pairSupport_right (Γ := Γ) hinst)) htK.2)
  refine (hp.symm.insert_left (fun s => by simpa using hp.rel_right (φ.inst t) hinst s)
    (hp.finite_pairSupport.subset hsupp) ?_).symm
  rw [pairSupport_comm, pairSupport_insert_right_of_subset hsupp, ← sepBudget_flip B₁ B₂]
  refine Theoryω.SignedInseparable.symm_iff.2 (Theoryω.signedInseparable_iff.2 ?_)
  intro θ hr hk hΓ hΔ
  refine Theoryω.signedInseparable_iff.1 hp.insep (equal t t' ⊓ θ)
    (by simpa using hr) (by simp [htK.1, htK.2, hk])
    (Theoryω.entails_iff.2 fun M _ _ hM =>
      SentenceInf.realize_inf.2 ⟨hM.realize_of_mem heq, (Theoryω.entails_iff.1 hΓ) M hM⟩)
    (Theoryω.entails_iff.2 fun M _ _ hM => ?_)
  rw [SentenceInf.realize_not, SentenceInf.realize_inf]
  rintro ⟨htM, hθM⟩
  exact SentenceInf.realize_not.1 ((Theoryω.entails_iff.1 hΔ) M (Theoryω.model_insert_iff.2
    ⟨SentenceInf.realize_inst_of_realize_equal htM (hM.realize_of_mem hinst), hM⟩)) hθM

private theorem eq_name_left (hp : SignedPair B₁ B₂ Γ Δ) (t : L[[ℕ]].Term (Empty ⊕ Fin 0)) :
    ∃ c, SignedPair B₁ B₂ (insert (equal (L.con c).term t) Γ) Δ := by
  have hKt := hp.finite_pairSupport.union t.finite_constantSupport
  obtain ⟨c, hc⟩ := hKt.infinite_compl.nonempty
  let ψ : L[[ℕ]].BoundedFormulaω Empty 1 :=
    equal (Term.var (Sum.inr 0)) (t.relabel (Sum.map id Fin.elim0))
  have hinst_eq (u : L[[ℕ]].Term (Empty ⊕ Fin 0)) : ψ.inst u = equal u t := by
    have hcomp :
        (Sum.elim (Term.var ∘ Sum.inl) fun _ : Fin 1 => u) ∘ Sum.map id Fin.elim0 = Term.var := by
      ext (e | i)
      · exact e.elim
      · exact i.elim0
    simp [ψ, inst_def, hcomp]
  have hcψ : c ∉ ψ.constantSupport := by
    intro h
    simp only [ψ, constantSupport_equal, Set.mem_union] at h
    rcases h with h | h
    · simp at h
    · rw [Term.mem_constantSupport] at h
      exact hc (.inr (Term.mem_constantSupport.2 (by simpa using h)))
  have hex : Γ.Entails ψ.ex := Theoryω.entails_iff.2 fun M _ _ _ => by
    rw [SentenceInf.realize_def, FormulaInf.realize_def, realize_ex]
    refine ⟨t.realize (Sum.elim Empty.elim default), ?_⟩
    rw [Fin.snoc_zero]
    have hself := SentenceInf.realize_equal_self (ι := ℕ) (M := M) t
    rwa [← hinst_eq t, SentenceInf.realize_def, realize_inst] at hself
  refine ⟨c, hp.insert_left (by simp)
    (by rw [constantSupport_equal, Term.constantSupport_con]
        exact (Set.finite_singleton c).union t.finite_constantSupport) ?_⟩
  have hinsep := hp.insep_insert_inst_of_ex t.finite_constantSupport hc hcψ hex
  rw [hinst_eq] at hinsep
  rwa [pairSupport_insert_left, constantSupport_equal, Term.constantSupport_con,
    Set.union_comm {c}, ← Set.union_assoc]

end SignedPair

/-- **The signed paired-inseparability consistency property** over `L[[ℕ]]`, requiring no relational
or countability assumption on `L`. Right-hand and symmetric mixed cases reduce to the left-hand
clauses via `SignedPair.symm`. -/
private def lyndonConsistencyProperty (B₁ B₂ : Bool → Set (Σ n, L[[ℕ]].Relations n)) :
    ConsistencyProperty L where
  sets := {s | ∃ Γ Δ, s = Γ ∪ Δ ∧ SignedPair B₁ B₂ Γ Δ}
  no_falsum := by
    rintro _ ⟨_, _, rfl, hp⟩ h
    exact h.elim hp.not_bot_left hp.symm.not_bot_left
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
  eq_refl := by
    rintro _ ⟨_, _, rfl, hp⟩ t
    exact ⟨_, _, Set.insert_union.symm, hp.eq_refl_left t⟩
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

/-- If `φ` and `ψ` admit no Lyndon interpolant in `L`, their images `{φ'}` and `{¬ψ'}` in `L[[ℕ]]`
form a `SignedPair`. -/
private theorem signedPair_root (φ ψ : L.Sentenceω)
    (hno : ¬ ∃ θ : L.Sentenceω,
      θ.relationsInSigned true ⊆ φ.relationsInSigned true ∩ ψ.relationsInSigned true ∧
      θ.relationsInSigned false ⊆ φ.relationsInSigned false ∩ ψ.relationsInSigned false ∧
      φ.Entails θ ∧ θ.Entails ψ) :
    SignedPair
      (fun s => ((L.lhomWithConstants ℕ).onBoundedFormulaInf φ).relationsInSigned s)
      (fun s => ((L.lhomWithConstants ℕ).onBoundedFormulaInf ψ).not.relationsInSigned s)
      {(L.lhomWithConstants ℕ).onBoundedFormulaInf φ}
      {((L.lhomWithConstants ℕ).onBoundedFormulaInf ψ).not} := by
  let g := L.lhomWithConstants ℕ
  refine ⟨Set.finite_singleton _, Set.finite_singleton _,
    fun _ hχ _ => by rw [Set.mem_singleton_iff.1 hχ],
    fun _ hχ _ => by rw [Set.mem_singleton_iff.1 hχ],
    fun _ hχ => by rw [Set.mem_singleton_iff.1 hχ]; simp,
    fun _ hχ => by rw [Set.mem_singleton_iff.1 hχ]; simp,
    Theoryω.signedInseparable_iff.2 fun θ' hθ'rel hθ'supp hφ'θ' hψ'θ' => ?_⟩
  have hK : pairSupport ({g.onBoundedFormulaInf φ} : L[[ℕ]].Theoryω)
      {(g.onBoundedFormulaInf ψ).not} = ∅ := by simp [pairSupport, g]
  obtain ⟨θ, rfl⟩ := constantSupport_eq_empty_iff.1 (Set.subset_empty_iff.1 (hK ▸ hθ'supp))
  have hpull (s : Bool) : θ.relationsInSigned s ⊆
      φ.relationsInSigned s ∩ ψ.relationsInSigned s := by
    have hg_inj : ∀ k, Function.Injective (g.onRelation (n := k)) :=
      fun _ => (L.lhomWithConstants_injective ℕ).onRelation
    rw [← g.preimage_relationsInSigned_onBoundedFormulaInf hg_inj s θ,
      ← g.preimage_relationsInSigned_onBoundedFormulaInf hg_inj s φ,
      ← g.preimage_relationsInSigned_onBoundedFormulaInf hg_inj s ψ, ← Set.preimage_inter]
    exact Set.preimage_mono ((hθ'rel s).trans (by simp [sepBudget, g]))
  refine hno ⟨θ, hpull true, hpull false,
    (Sentenceω.entails_onBoundedFormulaInf_iff (L.lhomWithConstants_injective ℕ)).1
      (Sentenceω.entails_def.2 hφ'θ'), ?_⟩
  have hnot : Sentenceω.Entails ψ.not θ.not :=
    (Sentenceω.entails_onBoundedFormulaInf_iff (L.lhomWithConstants_injective ℕ)).1
      (by simpa [g] using Sentenceω.entails_def.2 hψ'θ')
  exact Sentenceω.entails_iff.2 fun M _ _ hθM => by
    by_contra hψM
    exact SentenceInf.realize_not.1 (hnot.realize M (SentenceInf.realize_not.2 hψM)) hθM

/-- Countable relational core: if `L` is relational with countably many relation symbols, every
valid entailment `φ ⊨ ψ` between `L_{ω₁ω}` sentences admits a Lyndon interpolant. -/
private theorem lyndon_interpolation_relational_of_countable [L.IsRelational]
    [Countable (Σ n, L.Relations n)] (φ ψ : L.Sentenceω) (h : φ.Entails ψ) :
    ∃ θ : L.Sentenceω,
      θ.relationsInSigned true ⊆ φ.relationsInSigned true ∩ ψ.relationsInSigned true ∧
      θ.relationsInSigned false ⊆ φ.relationsInSigned false ∩ ψ.relationsInSigned false ∧
      φ.Entails θ ∧ θ.Entails ψ := by
  have : IsEmpty (Σ n, L.Functions n) := ⟨fun s => isEmptyElim s.2⟩
  by_contra hno
  let g := L.lhomWithConstants ℕ
  obtain ⟨M, _, _, _, hM, _⟩ := (lyndonConsistencyProperty
    (fun s => (g.onBoundedFormulaInf φ).relationsInSigned s)
    (fun s => (g.onBoundedFormulaInf ψ).not.relationsInSigned s)).model_existence.{u, v, max u v}
      ⟨_, _, rfl, signedPair_root φ ψ hno⟩
      ((Set.countable_singleton _).union (Set.countable_singleton _))
  let : L.Structure M := g.reduct M
  have hφM : SentenceInf.Realize φ M :=
    (LHom.realize_sentenceInf_onBoundedFormulaInf g φ).1
      (hM.realize_of_mem (.inl (Set.mem_singleton _)))
  exact SentenceInf.realize_not.1 (hM.realize_of_mem (.inr (Set.mem_singleton _)))
    ((LHom.realize_sentenceInf_onBoundedFormulaInf g ψ).2 (h.realize M hφM))

/-- **Relational Lyndon interpolation for `L_{ω₁ω}`.** Over any relational language `L` (of any
cardinality and in any universes), if an `L_{ω₁ω}` sentence `φ` entails `ψ`, there is an `L_{ω₁ω}`
sentence `θ` with `φ ⊨ θ` and `θ ⊨ ψ` whose positively occurring relation symbols lie in
`φ.relationsInSigned true ∩ ψ.relationsInSigned true` and whose negatively occurring relation
symbols lie in `φ.relationsInSigned false ∩ ψ.relationsInSigned false`. Logical equality may occur
in `θ` regardless of whether it occurs in `φ` or `ψ`. -/
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
  have hφ₀ : (symbSublangIncl F R).onBoundedFormulaInf φ₀ = φ :=
    onBoundedFormulaInf_restrictSymbols φ hFφ Set.subset_union_left
  have hψ₀ : (symbSublangIncl F R).onBoundedFormulaInf ψ₀ = ψ :=
    onBoundedFormulaInf_restrictSymbols ψ hFψ Set.subset_union_right
  have h₀ : φ₀.Entails ψ₀ :=
    (Sentenceω.entails_onBoundedFormulaInf_iff (symbSublangIncl_injective F R)).1
      (by rwa [hφ₀, hψ₀])
  obtain ⟨θ₀, hpos₀, hneg₀, hφθ₀, hθψ₀⟩ := lyndon_interpolation_relational_of_countable φ₀ ψ₀ h₀
  have hlift (s : Bool)
      (hs₀ : θ₀.relationsInSigned s ⊆ φ₀.relationsInSigned s ∩ ψ₀.relationsInSigned s) :
      ((symbSublangIncl F R).onBoundedFormulaInf θ₀).relationsInSigned s ⊆
        φ.relationsInSigned s ∩ ψ.relationsInSigned s := by
    rw [LHom.relationsInSigned_onBoundedFormulaInf]
    refine ((Set.image_mono hs₀).trans (Set.image_inter_subset _ _ _)).trans ?_
    rw [← LHom.relationsInSigned_onBoundedFormulaInf, ← LHom.relationsInSigned_onBoundedFormulaInf,
      hφ₀, hψ₀]
  exact ⟨(symbSublangIncl F R).onBoundedFormulaInf θ₀, hlift true hpos₀, hlift false hneg₀,
    hφ₀ ▸ hφθ₀.onBoundedFormulaInf (symbSublangIncl F R),
    hψ₀ ▸ hθψ₀.onBoundedFormulaInf (symbSublangIncl F R)⟩

/-- **Lyndon interpolation for `L_{ω₁ω}`.** Over any language `L` (of any cardinality, with
function symbols, and in any universes), if an `L_{ω₁ω}` sentence `φ` entails `ψ`, there is an
`L_{ω₁ω}` sentence `θ` with `φ ⊨ θ` and `θ ⊨ ψ` whose function symbols lie in
`φ.functionsIn ∩ ψ.functionsIn`, whose positively occurring relation symbols lie in
`φ.relationsInSigned true ∩ ψ.relationsInSigned true`, and whose negatively occurring relation
symbols lie in `φ.relationsInSigned false ∩ ψ.relationsInSigned false`. Logical equality may occur
in `θ` regardless of whether it occurs in `φ` or `ψ`. -/
theorem lyndon_interpolation (φ ψ : L.Sentenceω) (h : φ.Entails ψ) :
    ∃ θ : L.Sentenceω, θ.functionsIn ⊆ φ.functionsIn ∩ ψ.functionsIn ∧
      θ.relationsInSigned true ⊆ φ.relationsInSigned true ∩ ψ.relationsInSigned true ∧
      θ.relationsInSigned false ⊆ φ.relationsInSigned false ∩ ψ.relationsInSigned false ∧
      φ.Entails θ ∧ θ.Entails ψ := by
  let Aφ := (graphAxioms φ.functionsIn).conjunction φ.functionsIn_countable.graphAxioms
  let Aψ := (graphAxioms ψ.functionsIn).conjunction ψ.functionsIn_countable.graphAxioms
  have htr : (Aφ ⊓ φ.relationalize).Entails (Aψ.imp ψ.relationalize) := by
    have hg := Sentenceω.entails_iff_graphTranslation.1 h
    refine Sentenceω.entails_iff.2 fun N _ _ hN => ?_
    have hconj {F : Set (Σ n, L.Functions n)} (hF : F.Countable) :
        SentenceInf.Realize ((graphAxioms F).conjunction hF.graphAxioms) N ↔
          SentenceInf.Realize (graphAxiomsSentence F hF) N := by
      rw [Theoryω.realize_conjunction_iff, model_graphAxioms_iff, realize_graphAxiomsSentence,
        Sigma.forall]
    rw [SentenceInf.realize_inf, hconj φ.functionsIn_countable] at hN
    have hψN := hg.realize N (SentenceInf.realize_inf.2 hN)
    rw [SentenceInf.realize_imp, ← hconj ψ.functionsIn_countable] at hψN
    exact SentenceInf.realize_imp.2 hψN
  obtain ⟨θ, hpos, hneg, hφθ, hθψ⟩ := lyndon_interpolation_relational _ _ htr
  have hsym (s : Bool)
      (hs : θ.relationsInSigned s ⊆
        (Aφ ⊓ φ.relationalize).relationsInSigned s ∩
          (Aψ.imp ψ.relationalize).relationsInSigned s) :
      θ.relationsInSigned s ⊆
        relSym (φ.functionsIn ∩ ψ.functionsIn)
          (φ.relationsInSigned s ∩ ψ.relationsInSigned s) := by
    rwa [relationsInSigned_conjunction_graphAxioms_inf_relationalize s _ φ subset_rfl,
      relationsInSigned_conjunction_graphAxioms_imp_relationalize s _ ψ subset_rfl,
      relSym_inter] at hs
  have hsym_pos := hsym true hpos
  have hsym_neg := hsym false hneg
  refine ⟨θ.backTranslate, ?_, ?_, ?_, ?_, ?_⟩
  · rw [functionsIn_backTranslate, ← relationsInSigned_union_not true θ, Set.preimage_union]
    exact Set.union_subset
      (by simpa using Set.preimage_mono (f := graphRelSym) hsym_pos)
      (by simpa using Set.preimage_mono (f := graphRelSym) hsym_neg)
  · simpa using Set.preimage_mono (f := baseRelSym) hsym_pos
  · simpa using Set.preimage_mono (f := baseRelSym) hsym_neg
  · refine Sentenceω.entails_iff.2 fun M _ _ hφM => ?_
    let := graphExpansion L M
    have hAφ : SentenceInf.Realize Aφ M :=
      (Theoryω.realize_conjunction_iff _).2 (model_graphAxioms_graphExpansion L M _)
    have hθM := hφθ.realize M (SentenceInf.realize_inf.2 ⟨hAφ, by
      simpa only [SentenceInf.realize_def, FormulaInf.realize_def, realize_relationalize]
        using hφM⟩)
    simpa only [SentenceInf.realize_def, FormulaInf.realize_def, realize_backTranslate] using hθM
  · refine Sentenceω.entails_iff.2 fun M _ _ hθM => ?_
    let := graphExpansion L M
    have hAψ : SentenceInf.Realize Aψ M :=
      (Theoryω.realize_conjunction_iff _).2 (model_graphAxioms_graphExpansion L M _)
    have hψM := SentenceInf.realize_imp.1 (hθψ.realize M (by
      simpa only [SentenceInf.realize_def, FormulaInf.realize_def, realize_backTranslate]
        using hθM)) hAψ
    simpa only [SentenceInf.realize_def, FormulaInf.realize_def, realize_relationalize] using hψM

/-- **Countable-theory Lyndon interpolation.** If a countable `L_{ω₁ω}` theory `T` entails `ψ`,
there is an interpolant `θ` with `T ⊨ θ` and `θ ⊨ ψ` whose occurring function symbols appear in
both `T` and `ψ`, and whose positively (respectively negatively) occurring relation symbols appear
positively (respectively negatively) in both some sentence of `T` and `ψ`. -/
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

/-- **Craig interpolation recovered from Lyndon interpolation**: joining the positive and negative
relation bounds of `lyndon_interpolation` yields the unsigned relation bound of Craig
interpolation. -/
theorem craig_of_lyndon_interpolation (φ ψ : L.Sentenceω) (h : φ.Entails ψ) :
    ∃ θ : L.Sentenceω, θ.functionsIn ⊆ φ.functionsIn ∩ ψ.functionsIn ∧
      θ.relationsIn ⊆ φ.relationsIn ∩ ψ.relationsIn ∧ φ.Entails θ ∧ θ.Entails ψ := by
  obtain ⟨θ, hfun, hpos, hneg, hφθ, hθψ⟩ := lyndon_interpolation φ ψ h
  refine ⟨θ, hfun, ?_, hφθ, hθψ⟩
  rw [← relationsInSigned_union_not true θ]
  exact Set.union_subset
    (hpos.trans (Set.inter_subset_inter (relationsInSigned_subset_relationsIn true φ)
      (relationsInSigned_subset_relationsIn true ψ)))
    (hneg.trans (Set.inter_subset_inter (relationsInSigned_subset_relationsIn false φ)
      (relationsInSigned_subset_relationsIn false ψ)))

end Lyndon

end FirstOrder.Language
