/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.QuantifierClass
public import TauCeti.ModelTheory.Interpolation.ConstantElimination
public import TauCeti.ModelTheory.ModelExistence.CountableModel
public import TauCeti.ModelTheory.ModelExistence.ModelExistence

/-!
# Malitz interpolation for `L_{ω₁ω}`

Malitz's interpolation theorem refines Craig interpolation by quantifier class: over a relational
language, if an `L_{ω₁ω}` sentence `φ` entails a universal sentence `ψ`, then some universal
sentence `θ` in the shared relation symbols of `φ` and `ψ` satisfies `φ ⊨ θ` and `θ ⊨ ψ`. Here
universal is the `∀₁` class `BoundedFormulaInf.IsUniversal`, closed under countable conjunctions
and disjunctions; equality is logical, so `θ` may use it freely. The language may have any
cardinality.

The proof is by model existence. Over the Henkin expansion `L[[ℕ]]`, a member of the consistency
property is a union `Γ ∪ Δ` of two finite sets of sentences whose constant supports are finite,
whose relation symbols lie in two budgets `R₁` and `R₂`, and with every sentence of `Δ`
existential, such that no **universal** sentence in the shared relation symbols `R₁ ∩ R₂`, with
constants among those of `Δ`, is entailed by `Γ` and refuted on `Δ`. Two features of this
property differ from the paired-inseparability property behind Craig interpolation:

* **Only the constants of `Δ` may occur in a separator.** A witness constant introduced on the
  left therefore never occurs in a separator, and existential instantiation
  (`Theoryω.Entails.of_insert_inst`) discharges it without introducing an existential quantifier.
  A witness introduced on the right is abstracted by a universal quantifier
  (`Theoryω.entails_all_abstractConst_separator`).
* **The right side is existential.** It never contains a universal quantifier to instantiate, so
  the left-side constants never enter `Δ` through instantiation. They can enter only through the
  mixed case of equality substitution, an equation `t = t'` on the left and an atom `φ t` on the
  right. Then either the atom does not depend on its argument, or `t` is a constant of `Δ`; a
  separator `θ` of the extension then gives `t = t' ⊓ θ` when the constant `d` of `t'` occurs in
  `Δ`, and otherwise `θ` with `t` substituted for `d` (`realize_inst_abstractConst`). This is the
  only use of relationality: closed terms of `L[[ℕ]]` are constants.

At the root `({φ'}, {¬ψ'})`, the right side is existential exactly because `ψ` is universal, and
a separator has no constants, so it descends to a universal interpolant in `L`. Passing to the
countable symbol sublanguage of `φ` and `ψ` removes the countability assumption on `L`.

## Main results

* `FirstOrder.Language.malitz_interpolation`: Malitz interpolation for `L_{ω₁ω}` sentences over a
  relational language of arbitrary cardinality.

## References

* J. Malitz, *Universal classes in infinitary languages*, Duke Mathematical Journal **36** (1969),
  621–630.
* M. Harrison-Trainor and M. Kretschmer, *Infinitary logic has no expressive efficiency over
  finitary logic*, Journal of Symbolic Logic **89** (2024), Theorem 4.5.
* H. J. Keisler, *Model Theory for Infinitary Logic*, North-Holland, 1971, §4.
* The consistency-property framework and the shape of the separator argument follow the
  paired-inseparability property of `TauCeti.ModelTheory.Interpolation.Craig`, which follows the
  interpolation construction of `cameronfreer/infinitary-logic` at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`. The universal separator class, the right-hand
  constant budget and the existential right side are specific to this file.
-/

public section

universe u v

namespace FirstOrder.Language

open BoundedFormulaInf

section Engine

variable {L : Language.{u, v}}

/-- The constants occurring in some sentence of a theory over `L[[ℕ]]`. -/
private def theorySupport (T : L[[ℕ]].Theoryω) : Set ℕ :=
  ⋃ χ ∈ T, χ.constantSupport

private theorem subset_theorySupport {T : L[[ℕ]].Theoryω} {χ : L[[ℕ]].Sentenceω} (hχ : χ ∈ T) :
    χ.constantSupport ⊆ theorySupport T :=
  Set.subset_biUnion_of_mem hχ

private theorem theorySupport_insert (χ : L[[ℕ]].Sentenceω) (T : L[[ℕ]].Theoryω) :
    theorySupport (insert χ T) = χ.constantSupport ∪ theorySupport T :=
  Set.biUnion_insert _ _ _

private theorem notMem_of_notMem_theorySupport {T : L[[ℕ]].Theoryω} {c : ℕ}
    (hc : c ∉ theorySupport T) : ∀ χ ∈ T, c ∉ χ.constantSupport :=
  fun _ hχ h => hc (subset_theorySupport hχ h)

/-- A universal separator of `(Γ, Δ)`: a universal sentence with relation symbols in `R` and
constants in `K`, entailed by `Γ` and refuted on `Δ`. -/
private def HasUSep (R : Set (Σ n, L[[ℕ]].Relations n)) (K : Set ℕ)
    (Γ Δ : L[[ℕ]].Theoryω) : Prop :=
  ∃ θ : L[[ℕ]].Sentenceω, θ.IsUniversal ∧ θ.relationsIn ⊆ R ∧ θ.constantSupport ⊆ K ∧
    Γ.Entails θ ∧ Δ.Entails θ.not

/-- A member of the Malitz consistency property, presented as a pair `(Γ, Δ)`: finite sets with
finite constant supports and relation symbols in `R₁` and `R₂`, with `Δ` existential, admitting
no universal separator in the shared symbols with constants among those of `Δ`. -/
private structure MalitzPair (R₁ R₂ : Set (Σ n, L[[ℕ]].Relations n))
    (Γ Δ : L[[ℕ]].Theoryω) : Prop where
  finite_left : Γ.Finite
  finite_right : Δ.Finite
  rel_left : ∀ χ ∈ Γ, χ.relationsIn ⊆ R₁
  rel_right : ∀ χ ∈ Δ, χ.relationsIn ⊆ R₂
  supp_left : ∀ χ ∈ Γ, χ.constantSupport.Finite
  supp_right : ∀ χ ∈ Δ, χ.constantSupport.Finite
  existential_right : ∀ χ ∈ Δ, χ.IsExistential
  insep : ¬ HasUSep (R₁ ∩ R₂) (theorySupport Δ) Γ Δ

namespace MalitzPair

variable {R₁ R₂ : Set (Σ n, L[[ℕ]].Relations n)} {Γ Δ : L[[ℕ]].Theoryω}

private theorem finite_theorySupport_right (h : MalitzPair R₁ R₂ Γ Δ) :
    (theorySupport Δ).Finite :=
  h.finite_right.biUnion h.supp_right

/-- A constant occurring in neither side of the pair. -/
private theorem exists_fresh (h : MalitzPair R₁ R₂ Γ Δ) :
    ∃ c, c ∉ theorySupport Γ ∧ c ∉ theorySupport Δ := by
  obtain ⟨c, hc⟩ := ((h.finite_left.biUnion h.supp_left).union
    h.finite_theorySupport_right).infinite_compl.nonempty
  exact ⟨c, fun h' => hc (.inl h'), fun h' => hc (.inr h')⟩

private theorem insert_left (h : MalitzPair R₁ R₂ Γ Δ) {χ : L[[ℕ]].Sentenceω}
    (hrel : χ.relationsIn ⊆ R₁) (hfin : χ.constantSupport.Finite)
    (hinsep : ¬ HasUSep (R₁ ∩ R₂) (theorySupport Δ) (insert χ Γ) Δ) :
    MalitzPair R₁ R₂ (insert χ Γ) Δ :=
  ⟨h.finite_left.insert χ, h.finite_right,
    fun _ hψ => hψ.elim (fun e => e ▸ hrel) (h.rel_left _), h.rel_right,
    fun _ hψ => hψ.elim (fun e => e ▸ hfin) (h.supp_left _), h.supp_right,
    h.existential_right, hinsep⟩

private theorem insert_right (h : MalitzPair R₁ R₂ Γ Δ) {χ : L[[ℕ]].Sentenceω}
    (hrel : χ.relationsIn ⊆ R₂) (hfin : χ.constantSupport.Finite) (hex : χ.IsExistential)
    (hinsep : ¬ HasUSep (R₁ ∩ R₂) (theorySupport (insert χ Δ)) Γ (insert χ Δ)) :
    MalitzPair R₁ R₂ Γ (insert χ Δ) :=
  ⟨h.finite_left, h.finite_right.insert χ, h.rel_left,
    fun _ hψ => hψ.elim (fun e => e ▸ hrel) (h.rel_right _), h.supp_left,
    fun _ hψ => hψ.elim (fun e => e ▸ hfin) (h.supp_right _),
    fun _ hψ => hψ.elim (fun e => e ▸ hex) (h.existential_right _), hinsep⟩

/-- Adding a consequence of `Γ` on the left preserves the pair. -/
private theorem insert_left_of_entails (h : MalitzPair R₁ R₂ Γ Δ) {χ : L[[ℕ]].Sentenceω}
    (hrel : χ.relationsIn ⊆ R₁) (hfin : χ.constantSupport.Finite) (hent : Γ.Entails χ) :
    MalitzPair R₁ R₂ (insert χ Γ) Δ :=
  h.insert_left hrel hfin fun ⟨θ, hu, hr, hs, hΓ, hΔ⟩ => h.insep ⟨θ, hu, hr, hs, hent.cut hΓ, hΔ⟩

/-- Adding an existential consequence of `Δ` with no new constants on the right preserves the
pair. -/
private theorem insert_right_of_entails (h : MalitzPair R₁ R₂ Γ Δ) {χ : L[[ℕ]].Sentenceω}
    (hrel : χ.relationsIn ⊆ R₂) (hsupp : χ.constantSupport ⊆ theorySupport Δ)
    (hex : χ.IsExistential) (hent : Δ.Entails χ) : MalitzPair R₁ R₂ Γ (insert χ Δ) := by
  refine h.insert_right hrel (h.finite_theorySupport_right.subset hsupp) hex ?_
  rw [theorySupport_insert, Set.union_eq_self_of_subset_left hsupp]
  exact fun ⟨θ, hu, hr, hs, hΓ, hΔ⟩ => h.insep ⟨θ, hu, hr, hs, hΓ, hent.cut hΔ⟩

private theorem hasUSep_of_not_insert_left (h : MalitzPair R₁ R₂ Γ Δ) {χ : L[[ℕ]].Sentenceω}
    (hrel : χ.relationsIn ⊆ R₁) (hfin : χ.constantSupport.Finite)
    (hnot : ¬ MalitzPair R₁ R₂ (insert χ Γ) Δ) :
    HasUSep (R₁ ∩ R₂) (theorySupport Δ) (insert χ Γ) Δ := by
  by_contra hsep
  exact hnot (h.insert_left hrel hfin hsep)

private theorem hasUSep_of_not_insert_right (h : MalitzPair R₁ R₂ Γ Δ) {χ : L[[ℕ]].Sentenceω}
    (hrel : χ.relationsIn ⊆ R₂) (hsupp : χ.constantSupport ⊆ theorySupport Δ)
    (hex : χ.IsExistential) (hnot : ¬ MalitzPair R₁ R₂ Γ (insert χ Δ)) :
    HasUSep (R₁ ∩ R₂) (theorySupport Δ) Γ (insert χ Δ) := by
  by_contra hsep
  refine hnot (h.insert_right hrel (h.finite_theorySupport_right.subset hsupp) hex ?_)
  rwa [theorySupport_insert, Set.union_eq_self_of_subset_left hsupp]

/-- A countable disjunction entailed by `Γ` has a disjunct that can be added on the left: the
disjunction of separators of all extensions would separate the pair. -/
private theorem exists_insert_left (h : MalitzPair R₁ R₂ Γ Δ) (ψs : ℕ → L[[ℕ]].Sentenceω)
    (hrel : ∀ k, (ψs k).relationsIn ⊆ R₁) (hfin : ∀ k, (ψs k).constantSupport.Finite)
    (hent : Γ.Entails (BoundedFormulaInf.iSup ψs)) :
    ∃ k, MalitzPair R₁ R₂ (insert (ψs k) Γ) Δ := by
  by_contra! hnone
  choose θs hu hr hs hΓ hΔ using fun k =>
    h.hasUSep_of_not_insert_left (hrel k) (hfin k) (hnone k)
  refine h.insep ⟨.iSup θs, (universalSigned_iSup _ _).2 hu,
    by rw [relationsIn_iSup]; exact Set.iUnion_subset hr,
    by rw [constantSupport_iSup]; exact Set.iUnion_subset hs,
    Theoryω.entails_iff.2 fun M _ _ hM => ?_, Theoryω.entails_iff.2 fun M _ _ hM => ?_⟩
  · obtain ⟨k, hk⟩ := SentenceInf.realize_iSup.1 (Theoryω.entails_iff.1 hent M hM)
    exact SentenceInf.realize_iSup.2
      ⟨k, Theoryω.entails_iff.1 (hΓ k) M (Theoryω.model_insert_iff.2 ⟨hk, hM⟩)⟩
  · rw [SentenceInf.realize_not, SentenceInf.realize_iSup]
    exact fun ⟨k, hk⟩ => SentenceInf.realize_not.1 (Theoryω.entails_iff.1 (hΔ k) M hM) hk

/-- A countable disjunction entailed by `Δ` has a disjunct that can be added on the right: the
conjunction of separators of all extensions would separate the pair. -/
private theorem exists_insert_right (h : MalitzPair R₁ R₂ Γ Δ) (ψs : ℕ → L[[ℕ]].Sentenceω)
    (hrel : ∀ k, (ψs k).relationsIn ⊆ R₂) (hsupp : ∀ k, (ψs k).constantSupport ⊆ theorySupport Δ)
    (hex : ∀ k, (ψs k).IsExistential) (hent : Δ.Entails (BoundedFormulaInf.iSup ψs)) :
    ∃ k, MalitzPair R₁ R₂ Γ (insert (ψs k) Δ) := by
  by_contra! hnone
  choose θs hu hr hs hΓ hΔ using fun k =>
    h.hasUSep_of_not_insert_right (hrel k) (hsupp k) (hex k) (hnone k)
  refine h.insep ⟨.iInf θs, (universalSigned_iInf _ _).2 hu,
    by rw [relationsIn_iInf]; exact Set.iUnion_subset hr,
    by rw [constantSupport_iInf]; exact Set.iUnion_subset hs,
    Theoryω.entails_iff.2 fun M _ _ hM => SentenceInf.realize_iInf.2 fun k =>
      Theoryω.entails_iff.1 (hΓ k) M hM,
    Theoryω.entails_iff.2 fun M _ _ hM => ?_⟩
  obtain ⟨k, hk⟩ := SentenceInf.realize_iSup.1 (Theoryω.entails_iff.1 hent M hM)
  rw [SentenceInf.realize_not, SentenceInf.realize_iInf]
  exact fun hall => SentenceInf.realize_not.1
    (Theoryω.entails_iff.1 (hΔ k) M (Theoryω.model_insert_iff.2 ⟨hk, hM⟩)) (hall k)

/-- `Γ` is satisfiable: otherwise `⊥` would separate the pair. -/
private theorem not_entails_bot_left (h : MalitzPair R₁ R₂ Γ Δ) (hΓ : Γ.Entails ⊥) : False :=
  h.insep ⟨⊥, universalSigned_bot _, by simp, by simp, hΓ,
    Theoryω.entails_iff.2 fun _ _ _ _ => by simp [SentenceInf.realize_not]⟩

/-- `Δ` is satisfiable: otherwise `⊤` would separate the pair. -/
private theorem not_entails_bot_right (h : MalitzPair R₁ R₂ Γ Δ) (hΔ : Δ.Entails ⊥) : False :=
  h.insep ⟨⊤, universalSigned_top _, by simp, by simp,
    Theoryω.entails_iff.2 fun _ _ _ _ => by simp [SentenceInf.realize_def],
    Theoryω.entails_iff.2 fun M _ _ hM => by
      simpa [SentenceInf.realize_bot] using Theoryω.entails_iff.1 hΔ M hM⟩

/-- A sentence on the left whose negation lies on the right separates the pair: the negation of
an existential sentence is universal. -/
private theorem not_mem_left_of_not_mem_right (h : MalitzPair R₁ R₂ Γ Δ)
    {φ : L[[ℕ]].Sentenceω} (hφ : φ ∈ Γ) (hnφ : φ.not ∈ Δ) : False :=
  h.insep ⟨φ, by simpa using h.existential_right _ hnφ,
    Set.subset_inter (h.rel_left φ hφ) (by simpa using h.rel_right _ hnφ),
    by simpa using subset_theorySupport hnφ, Theoryω.entails_of_mem hφ,
    Theoryω.entails_of_mem hnφ⟩

/-- A sentence on the right whose negation lies on the left: the negation separates the pair. -/
private theorem not_mem_right_of_not_mem_left (h : MalitzPair R₁ R₂ Γ Δ)
    {φ : L[[ℕ]].Sentenceω} (hφ : φ ∈ Δ) (hnφ : φ.not ∈ Γ) : False :=
  h.insep ⟨φ.not, by simpa using h.existential_right _ hφ,
    Set.subset_inter (h.rel_left _ hnφ) (by simpa using h.rel_right _ hφ),
    by simpa using subset_theorySupport hφ, Theoryω.entails_of_mem hnφ,
    Theoryω.entails_iff.2 fun _ _ _ hM => SentenceInf.realize_not.2 fun hn =>
      SentenceInf.realize_not.1 hn (hM.realize_of_mem hφ)⟩

private theorem imp_left (h : MalitzPair R₁ R₂ Γ Δ) {φ ψ : L[[ℕ]].Sentenceω}
    (himp : φ.imp ψ ∈ Γ) :
    MalitzPair R₁ R₂ (insert φ.not Γ) Δ ∨ MalitzPair R₁ R₂ (insert ψ Γ) Δ := by
  by_contra! hboth
  have hrel := Set.union_subset_iff.1 (relationsIn_imp φ ψ ▸ h.rel_left _ himp)
  have hfin : φ.constantSupport.Finite ∧ ψ.constantSupport.Finite := by
    simpa using h.supp_left _ himp
  obtain ⟨θ₁, hu₁, hr₁, hs₁, hΓ₁, hΔ₁⟩ :=
    h.hasUSep_of_not_insert_left (by simpa using hrel.1) (by simpa using hfin.1) hboth.1
  obtain ⟨θ₂, hu₂, hr₂, hs₂, hΓ₂, hΔ₂⟩ :=
    h.hasUSep_of_not_insert_left hrel.2 hfin.2 hboth.2
  refine h.insep ⟨θ₁ ⊔ θ₂, by simp [hu₁, hu₂],
    by rw [relationsIn_sup]; exact Set.union_subset hr₁ hr₂, by simp [hs₁, hs₂],
    Theoryω.entails_iff.2 fun M _ _ hM => SentenceInf.realize_sup.2 ?_,
    Theoryω.entails_iff.2 fun M _ _ hM => ?_⟩
  · exact (hM.realize_of_imp_mem himp).imp
      (fun hn => Theoryω.entails_iff.1 hΓ₁ M (Theoryω.model_insert_iff.2 ⟨hn, hM⟩))
      (fun hψ => Theoryω.entails_iff.1 hΓ₂ M (Theoryω.model_insert_iff.2 ⟨hψ, hM⟩))
  · rw [SentenceInf.realize_not, SentenceInf.realize_sup, not_or]
    exact ⟨SentenceInf.realize_not.1 (Theoryω.entails_iff.1 hΔ₁ M hM),
      SentenceInf.realize_not.1 (Theoryω.entails_iff.1 hΔ₂ M hM)⟩

private theorem imp_right (h : MalitzPair R₁ R₂ Γ Δ) {φ ψ : L[[ℕ]].Sentenceω}
    (himp : φ.imp ψ ∈ Δ) :
    MalitzPair R₁ R₂ Γ (insert φ.not Δ) ∨ MalitzPair R₁ R₂ Γ (insert ψ Δ) := by
  by_contra! hboth
  have hrel := Set.union_subset_iff.1 (relationsIn_imp φ ψ ▸ h.rel_right _ himp)
  have hsupp := Set.union_subset_iff.1
    (constantSupport_imp φ ψ ▸ subset_theorySupport himp)
  have hex : φ.IsUniversal ∧ ψ.IsExistential := by simpa using h.existential_right _ himp
  obtain ⟨θ₁, hu₁, hr₁, hs₁, hΓ₁, hΔ₁⟩ := h.hasUSep_of_not_insert_right (by simpa using hrel.1)
    (by simpa using hsupp.1) (by simpa using hex.1) hboth.1
  obtain ⟨θ₂, hu₂, hr₂, hs₂, hΓ₂, hΔ₂⟩ :=
    h.hasUSep_of_not_insert_right hrel.2 hsupp.2 hex.2 hboth.2
  refine h.insep ⟨θ₁ ⊓ θ₂, by simp [hu₁, hu₂],
    by rw [relationsIn_inf]; exact Set.union_subset hr₁ hr₂, by simp [hs₁, hs₂],
    Theoryω.entails_iff.2 fun M _ _ hM => SentenceInf.realize_inf.2
      ⟨Theoryω.entails_iff.1 hΓ₁ M hM, Theoryω.entails_iff.1 hΓ₂ M hM⟩,
    Theoryω.entails_iff.2 fun M _ _ hM => ?_⟩
  rw [SentenceInf.realize_not, SentenceInf.realize_inf]
  rintro ⟨h₁, h₂⟩
  rcases hM.realize_of_imp_mem himp with hn | hψ
  · exact SentenceInf.realize_not.1
      (Theoryω.entails_iff.1 hΔ₁ M (Theoryω.model_insert_iff.2 ⟨hn, hM⟩)) h₁
  · exact SentenceInf.realize_not.1
      (Theoryω.entails_iff.1 hΔ₂ M (Theoryω.model_insert_iff.2 ⟨hψ, hM⟩)) h₂

private theorem not_imp_left (h : MalitzPair R₁ R₂ Γ Δ) {φ ψ : L[[ℕ]].Sentenceω}
    (hn : (φ.imp ψ).not ∈ Γ) :
    MalitzPair R₁ R₂ (insert φ Γ) Δ ∧ MalitzPair R₁ R₂ (insert ψ.not Γ) Δ := by
  have hrel : φ.relationsIn ⊆ R₁ ∧ ψ.relationsIn ⊆ R₁ := by simpa using h.rel_left _ hn
  have hfin : φ.constantSupport.Finite ∧ ψ.constantSupport.Finite := by
    simpa using h.supp_left _ hn
  exact ⟨h.insert_left_of_entails hrel.1 hfin.1
      (Theoryω.entails_iff.2 fun _ _ _ hM => (hM.realize_of_not_imp_mem hn).1),
    h.insert_left_of_entails (by simpa using hrel.2) (by simpa using hfin.2)
      (Theoryω.entails_iff.2 fun _ _ _ hM => (hM.realize_of_not_imp_mem hn).2)⟩

private theorem not_imp_right (h : MalitzPair R₁ R₂ Γ Δ) {φ ψ : L[[ℕ]].Sentenceω}
    (hn : (φ.imp ψ).not ∈ Δ) :
    MalitzPair R₁ R₂ Γ (insert φ Δ) ∧ MalitzPair R₁ R₂ Γ (insert ψ.not Δ) := by
  have hrel : φ.relationsIn ⊆ R₂ ∧ ψ.relationsIn ⊆ R₂ := by simpa using h.rel_right _ hn
  have hsupp : φ.constantSupport ⊆ theorySupport Δ ∧ ψ.constantSupport ⊆ theorySupport Δ := by
    simpa using subset_theorySupport hn
  have hex : φ.IsExistential ∧ ψ.IsUniversal := by simpa using h.existential_right _ hn
  exact ⟨h.insert_right_of_entails hrel.1 hsupp.1 hex.1
      (Theoryω.entails_iff.2 fun _ _ _ hM => (hM.realize_of_not_imp_mem hn).1),
    h.insert_right_of_entails (by simpa using hrel.2) (by simpa using hsupp.2)
      (by simpa using hex.2)
      (Theoryω.entails_iff.2 fun _ _ _ hM => (hM.realize_of_not_imp_mem hn).2)⟩

private theorem iInf_left (h : MalitzPair R₁ R₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hm : BoundedFormulaInf.iInf φs ∈ Γ) (k : ℕ) : MalitzPair R₁ R₂ (insert (φs k) Γ) Δ :=
  h.insert_left_of_entails
    ((Set.subset_iUnion (fun i => (φs i).relationsIn) k).trans (by simpa using h.rel_left _ hm))
    ((h.supp_left _ hm).subset (by
      rw [constantSupport_iInf]; exact Set.subset_iUnion (fun i => (φs i).constantSupport) k))
    (Theoryω.entails_iff.2 fun _ _ _ hM => SentenceInf.realize_iInf.1 (hM.realize_of_mem hm) k)

private theorem iInf_right (h : MalitzPair R₁ R₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hm : BoundedFormulaInf.iInf φs ∈ Δ) (k : ℕ) : MalitzPair R₁ R₂ Γ (insert (φs k) Δ) :=
  h.insert_right_of_entails
    ((Set.subset_iUnion (fun i => (φs i).relationsIn) k).trans (by simpa using h.rel_right _ hm))
    ((Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
      (by simpa using subset_theorySupport hm))
    ((universalSigned_iInf _ _).1 (h.existential_right _ hm) k)
    (Theoryω.entails_iff.2 fun _ _ _ hM => SentenceInf.realize_iInf.1 (hM.realize_of_mem hm) k)

private theorem not_iInf_left (h : MalitzPair R₁ R₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hm : (BoundedFormulaInf.iInf φs).not ∈ Γ) :
    ∃ k, MalitzPair R₁ R₂ (insert (φs k).not Γ) Δ :=
  h.exists_insert_left (fun k => (φs k).not)
    (fun k => by
      simpa using (Set.subset_iUnion (fun i => (φs i).relationsIn) k).trans
        (by simpa using h.rel_left _ hm))
    (fun k => (h.supp_left _ hm).subset (by
      simpa using Set.subset_iUnion (fun i => (φs i).constantSupport) k))
    (Theoryω.entails_iff.2 fun _ _ _ hM =>
      SentenceInf.realize_iSup.2 (hM.realize_of_not_iInf_mem hm))

private theorem not_iInf_right (h : MalitzPair R₁ R₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hm : (BoundedFormulaInf.iInf φs).not ∈ Δ) :
    ∃ k, MalitzPair R₁ R₂ Γ (insert (φs k).not Δ) :=
  h.exists_insert_right (fun k => (φs k).not)
    (fun k => by
      simpa using (Set.subset_iUnion (fun i => (φs i).relationsIn) k).trans
        (by simpa using h.rel_right _ hm))
    (fun k => by
      simpa using (Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
        (by simpa using subset_theorySupport hm))
    (fun k => by simpa using (by simpa using h.existential_right _ hm : ∀ i, (φs i).IsUniversal) k)
    (Theoryω.entails_iff.2 fun _ _ _ hM =>
      SentenceInf.realize_iSup.2 (hM.realize_of_not_iInf_mem hm))

private theorem iSup_left (h : MalitzPair R₁ R₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hm : BoundedFormulaInf.iSup φs ∈ Γ) : ∃ k, MalitzPair R₁ R₂ (insert (φs k) Γ) Δ :=
  h.exists_insert_left φs
    (fun k => (Set.subset_iUnion (fun i => (φs i).relationsIn) k).trans
      (by simpa using h.rel_left _ hm))
    (fun k => (h.supp_left _ hm).subset (by
      rw [constantSupport_iSup]; exact Set.subset_iUnion (fun i => (φs i).constantSupport) k))
    (Theoryω.entails_of_mem hm)

private theorem iSup_right (h : MalitzPair R₁ R₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hm : BoundedFormulaInf.iSup φs ∈ Δ) : ∃ k, MalitzPair R₁ R₂ Γ (insert (φs k) Δ) :=
  h.exists_insert_right φs
    (fun k => (Set.subset_iUnion (fun i => (φs i).relationsIn) k).trans
      (by simpa using h.rel_right _ hm))
    (fun k => (Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
      (by simpa using subset_theorySupport hm))
    ((universalSigned_iSup _ _).1 (h.existential_right _ hm))
    (Theoryω.entails_of_mem hm)

private theorem not_iSup_left (h : MalitzPair R₁ R₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hm : (BoundedFormulaInf.iSup φs).not ∈ Γ) (k : ℕ) :
    MalitzPair R₁ R₂ (insert (φs k).not Γ) Δ :=
  h.insert_left_of_entails
    (by
      simpa using (Set.subset_iUnion (fun i => (φs i).relationsIn) k).trans
        (by simpa using h.rel_left _ hm))
    ((h.supp_left _ hm).subset (by
      simpa using Set.subset_iUnion (fun i => (φs i).constantSupport) k))
    (Theoryω.entails_iff.2 fun _ _ _ hM => hM.realize_of_not_iSup_mem hm k)

private theorem not_iSup_right (h : MalitzPair R₁ R₂ Γ Δ) {φs : ℕ → L[[ℕ]].Sentenceω}
    (hm : (BoundedFormulaInf.iSup φs).not ∈ Δ) (k : ℕ) :
    MalitzPair R₁ R₂ Γ (insert (φs k).not Δ) :=
  h.insert_right_of_entails
    (by
      simpa using (Set.subset_iUnion (fun i => (φs i).relationsIn) k).trans
        (by simpa using h.rel_right _ hm))
    (by
      simpa using (Set.subset_iUnion (fun i => (φs i).constantSupport) k).trans
        (by simpa using subset_theorySupport hm))
    (by simpa using (by simpa using h.existential_right _ hm : ∀ i, (φs i).IsUniversal) k)
    (Theoryω.entails_iff.2 fun _ _ _ hM => hM.realize_of_not_iSup_mem hm k)

/-- Universal instantiation on the left: the instance is a consequence of `Γ`. -/
private theorem all_left (h : MalitzPair R₁ R₂ Γ Δ) {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (hall : φ.all ∈ Γ) (c : ℕ) : MalitzPair R₁ R₂ (insert (φ.inst (L.con c).term) Γ) Δ :=
  h.insert_left_of_entails (by simpa [inst_def] using h.rel_left _ hall)
    (((h.supp_left _ hall).union (Set.finite_singleton c)).subset
      ((constantSupport_inst_subset φ _).trans (Set.union_subset_union (by simp) (by simp))))
    (Theoryω.entails_iff.2 fun _ _ _ hM =>
      SentenceInf.realize_inst_of_realize_all (hM.realize_of_mem hall) _)

/-- The right side is existential, so it contains no universal quantifier. -/
private theorem not_all_mem_right (h : MalitzPair R₁ R₂ Γ Δ)
    {φ : L[[ℕ]].BoundedFormulaω Empty 1} (hall : φ.all ∈ Δ) : False := by
  simpa using h.existential_right _ hall

/-- A model of `Γ` containing `¬ ∀ x, φ x` satisfies `∃ x, ¬ φ x`. -/
private theorem entails_ex_not_of_not_all_mem {T : L[[ℕ]].Theoryω}
    {φ : L[[ℕ]].BoundedFormulaω Empty 1} (hn : φ.all.not ∈ T) : T.Entails φ.not.ex :=
  Theoryω.entails_iff.2 fun _ _ _ hM => by
    simpa [SentenceInf.realize_def, realize_ex, realize_not] using hM.realize_of_mem hn

/-- Existential witness on the left: a fresh constant never occurs in a separator, so existential
instantiation removes it. -/
private theorem not_all_left (h : MalitzPair R₁ R₂ Γ Δ) {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (hn : φ.all.not ∈ Γ) : ∃ c, MalitzPair R₁ R₂ (insert (φ.inst (L.con c).term).not Γ) Δ := by
  obtain ⟨c, hcΓ, hcΔ⟩ := h.exists_fresh
  have hcφ : c ∉ φ.constantSupport := fun hc => hcΓ (subset_theorySupport hn (by simpa using hc))
  refine ⟨c, h.insert_left (by simpa [inst_def] using h.rel_left _ hn)
    (((h.supp_left _ hn).union (Set.finite_singleton c)).subset ?_)
    fun ⟨θ, hu, hr, hs, hΓθ, hΔθ⟩ => h.insep ⟨θ, hu, hr, hs, ?_, hΔθ⟩⟩
  · rw [constantSupport_not]
    exact (constantSupport_inst_subset φ _).trans (Set.union_subset_union (by simp) (by simp))
  · refine Theoryω.Entails.of_insert_inst (φ := φ.not) (notMem_of_notMem_theorySupport hcΓ)
      (by simpa using hcφ) (fun hc => hcΔ (hs hc)) (entails_ex_not_of_not_all_mem hn) ?_
    rwa [inst_def, substBounds_not, ← inst_def]

/-- Existential witness on the right: the separator is universally quantified over the fresh
constant. -/
private theorem not_all_right (h : MalitzPair R₁ R₂ Γ Δ) {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (hn : φ.all.not ∈ Δ) : ∃ c, MalitzPair R₁ R₂ Γ (insert (φ.inst (L.con c).term).not Δ) := by
  classical
  obtain ⟨c, hcΓ, hcΔ⟩ := h.exists_fresh
  have hφK : φ.constantSupport ⊆ theorySupport Δ := by simpa using subset_theorySupport hn
  have hsupp : (φ.inst (L.con c).term).not.constantSupport ⊆ theorySupport Δ ∪ {c} := by
    rw [constantSupport_not]
    exact (constantSupport_inst_subset φ _).trans (Set.union_subset_union hφK (by simp))
  refine ⟨c, h.insert_right (by simpa [inst_def] using h.rel_right _ hn)
    ((h.finite_theorySupport_right.union (Set.finite_singleton c)).subset hsupp)
    (by simpa using h.existential_right _ hn) fun ⟨θ, hu, hr, hs, hΓθ, hΔθ⟩ => ?_⟩
  have hθ : θ.constantSupport ⊆ theorySupport Δ ∪ {c} := hs.trans <| by
    rw [theorySupport_insert]; exact Set.union_subset hsupp Set.subset_union_left
  obtain ⟨hΓ', hΔ'⟩ := Theoryω.entails_all_abstractConst_separator
    (notMem_of_notMem_theorySupport hcΓ) hΓθ hΔθ
  refine h.insep ⟨(abstractConst c θ).all, by simpa using hu, by simpa using hr, ?_, hΓ', ?_⟩
  · rw [constantSupport_all, constantSupport_abstractConst]
    exact fun d hd => (hθ hd.1).resolve_right hd.2
  · refine Theoryω.Entails.of_insert_inst (φ := φ.not) (notMem_of_notMem_theorySupport hcΔ)
      (fun hc => hcΔ (hφK (by simpa using hc))) (by simp) (entails_ex_not_of_not_all_mem hn) ?_
    rwa [inst_def, substBounds_not, ← inst_def]

private theorem eq_refl_left (h : MalitzPair R₁ R₂ Γ Δ) (t : L[[ℕ]].Term (Empty ⊕ Fin 0)) :
    MalitzPair R₁ R₂ (insert (equal t t) Γ) Δ :=
  h.insert_left_of_entails (by simp) (by simpa using t.finite_constantSupport)
    (Theoryω.entails_iff.2 fun _ _ _ _ => SentenceInf.realize_equal_self t)

private theorem eq_subst_left (h : MalitzPair R₁ R₂ Γ Δ)
    {t t' : L[[ℕ]].Term (Empty ⊕ Fin 0)} {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (heq : equal t t' ∈ Γ) (hinst : φ.inst t ∈ Γ) :
    MalitzPair R₁ R₂ (insert (φ.inst t') Γ) Δ :=
  h.insert_left_of_entails (by simpa [inst_def] using h.rel_left _ hinst)
    ((((h.supp_left _ hinst).subset (constantSupport_subset_inst φ t)).union
      t'.finite_constantSupport).subset (constantSupport_inst_subset φ t'))
    (Theoryω.entails_iff.2 fun _ _ _ hM => SentenceInf.realize_inst_of_realize_equal
      (hM.realize_of_mem heq) (hM.realize_of_mem hinst))

private theorem eq_subst_right (h : MalitzPair R₁ R₂ Γ Δ)
    {t t' : L[[ℕ]].Term (Empty ⊕ Fin 0)} {φ : L[[ℕ]].BoundedFormulaω Empty 1} (hφ : φ.IsAtomic)
    (heq : equal t t' ∈ Δ) (hinst : φ.inst t ∈ Δ) :
    MalitzPair R₁ R₂ Γ (insert (φ.inst t') Δ) :=
  h.insert_right_of_entails (by simpa [inst_def] using h.rel_right _ hinst)
    ((constantSupport_inst_subset φ t').trans (Set.union_subset
      ((constantSupport_subset_inst φ t).trans (subset_theorySupport hinst))
      (by simpa using subset_theorySupport heq : _ ∧ _).2))
    (by simpa using hφ.universalSigned false)
    (Theoryω.entails_iff.2 fun _ _ _ hM => SentenceInf.realize_inst_of_realize_equal
      (hM.realize_of_mem heq) (hM.realize_of_mem hinst))

/-- Equality substitution from the right into the left: a separator `θ` of the extension gives the
separator `t = t' → θ`. -/
private theorem eq_subst_right_left (h : MalitzPair R₁ R₂ Γ Δ)
    {t t' : L[[ℕ]].Term (Empty ⊕ Fin 0)} {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (heq : equal t t' ∈ Δ) (hinst : φ.inst t ∈ Γ) :
    MalitzPair R₁ R₂ (insert (φ.inst t') Γ) Δ := by
  have htK : t.constantSupport ∪ t'.constantSupport ⊆ theorySupport Δ := by
    simpa using subset_theorySupport heq
  refine h.insert_left (by simpa [inst_def] using h.rel_left _ hinst)
    ((((h.supp_left _ hinst).subset (constantSupport_subset_inst φ t)).union
      t'.finite_constantSupport).subset (constantSupport_inst_subset φ t'))
    fun ⟨θ, hu, hr, hs, hΓθ, hΔθ⟩ => h.insep ⟨(equal t t').imp θ, by simpa using hu,
      by simpa using hr, by simpa using Set.union_subset htK hs,
      Theoryω.entails_iff.2 fun M _ _ hM => SentenceInf.realize_imp.2 fun ht =>
        Theoryω.entails_iff.1 hΓθ M (Theoryω.model_insert_iff.2
          ⟨SentenceInf.realize_inst_of_realize_equal ht (hM.realize_of_mem hinst), hM⟩),
      Theoryω.entails_iff.2 fun M _ _ hM => SentenceInf.realize_not.2 fun himp =>
        SentenceInf.realize_not.1 (Theoryω.entails_iff.1 hΔθ M hM)
          (SentenceInf.realize_imp.1 himp (hM.realize_of_mem heq))⟩

/-- Equality substitution from the left into the right. Either the atom ignores its argument, or
`t` is a constant of `Δ`. In the second case a separator `θ` of the extension gives the separator
`t = t' ⊓ θ` when the constant `d` of `t'` occurs in `Δ`, and otherwise the instance of `θ` at `t`
in place of `d`. -/
private theorem eq_subst_left_right [L.IsRelational] (h : MalitzPair R₁ R₂ Γ Δ)
    {t t' : L[[ℕ]].Term (Empty ⊕ Fin 0)} {φ : L[[ℕ]].BoundedFormulaω Empty 1} (hφ : φ.IsAtomic)
    (heq : equal t t' ∈ Γ) (hinst : φ.inst t ∈ Δ) :
    MalitzPair R₁ R₂ Γ (insert (φ.inst t') Δ) := by
  classical
  rcases hφ.inst_eq_or_constantSupport_subset t t' with he | ht
  · rwa [← he, Set.insert_eq_of_mem hinst]
  have htK : t.constantSupport ⊆ theorySupport Δ := ht.trans (subset_theorySupport hinst)
  have hφK : φ.constantSupport ⊆ theorySupport Δ :=
    (constantSupport_subset_inst φ t).trans (subset_theorySupport hinst)
  obtain ⟨d, rfl⟩ := Term.exists_eq_con_of_isRelational t'
  have hsupp : (φ.inst (L.con d).term).constantSupport ⊆ theorySupport Δ ∪ {d} :=
    (constantSupport_inst_subset φ _).trans (Set.union_subset_union hφK (by simp))
  refine h.insert_right (by simpa [inst_def] using h.rel_right _ hinst)
    ((h.finite_theorySupport_right.union (Set.finite_singleton d)).subset hsupp)
    (by simpa using hφ.universalSigned false) fun ⟨θ, hu, hr, hs, hΓθ, hΔθ⟩ => ?_
  have hθ : θ.constantSupport ⊆ theorySupport Δ ∪ {d} := hs.trans <| by
    rw [theorySupport_insert]; exact Set.union_subset hsupp Set.subset_union_left
  by_cases hd : d ∈ theorySupport Δ
  · refine h.insep ⟨equal t (L.con d).term ⊓ θ, by simpa using hu, by simpa using hr, ?_,
      Theoryω.entails_iff.2 fun M _ _ hM => SentenceInf.realize_inf.2
        ⟨hM.realize_of_mem heq, Theoryω.entails_iff.1 hΓθ M hM⟩,
      Theoryω.entails_iff.2 fun M _ _ hM => ?_⟩
    · simp only [constantSupport_inf, constantSupport_equal, Term.constantSupport_con]
      exact Set.union_subset (Set.union_subset htK (by simpa using hd))
        fun x hx => (hθ hx).elim id fun hx => (Set.mem_singleton_iff.1 hx) ▸ hd
    · rw [SentenceInf.realize_not, SentenceInf.realize_inf]
      rintro ⟨htM, hθM⟩
      exact SentenceInf.realize_not.1 (Theoryω.entails_iff.1 hΔθ M (Theoryω.model_insert_iff.2
        ⟨SentenceInf.realize_inst_of_realize_equal htM (hM.realize_of_mem hinst), hM⟩)) hθM
  refine h.insep ⟨(abstractConst d θ).inst t, by simpa using hu, by simpa [inst_def] using hr,
    (constantSupport_inst_subset _ t).trans (Set.union_subset (by
      rw [constantSupport_abstractConst]
      exact fun x hx => (hθ hx.1).resolve_right hx.2) htK),
    (Theoryω.entails_of_mem heq).inst_abstractConst hΓθ, ?_⟩
  have h' := Theoryω.Entails.inst_abstractConst_of_insert_inst
    (notMem_of_notMem_theorySupport hd) (fun hx => hd (hφK hx)) (Theoryω.entails_of_mem hinst) hΔθ
  rwa [abstractConst_not, inst_def, substBounds_not, ← inst_def] at h'

private theorem eq_name_left [L.IsRelational] (h : MalitzPair R₁ R₂ Γ Δ)
    (t : L[[ℕ]].Term (Empty ⊕ Fin 0)) :
    ∃ c, MalitzPair R₁ R₂ (insert (equal (L.con c).term t) Γ) Δ := by
  obtain ⟨d, rfl⟩ := Term.exists_eq_con_of_isRelational t
  exact ⟨d, h.eq_refl_left _⟩

end MalitzPair

/-- **The Malitz consistency property** over `L[[ℕ]]` for a relational language `L`, with
relation budgets `R₁` and `R₂`. -/
private def malitzConsistencyProperty [L.IsRelational] (R₁ R₂ : Set (Σ n, L[[ℕ]].Relations n)) :
    ConsistencyProperty L where
  sets := {s | ∃ Γ Δ, s = Γ ∪ Δ ∧ MalitzPair R₁ R₂ Γ Δ}
  no_falsum := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ (h | h)
    · exact hp.not_entails_bot_left (Theoryω.entails_of_mem h)
    · exact hp.not_entails_bot_right (Theoryω.entails_of_mem h)
  no_contradiction := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φ (hφ | hφ) (hnφ | hnφ)
    · exact hp.not_entails_bot_left
        (Theoryω.entails_iff.2 fun _ _ _ hM => (hM.not_notMem hφ hnφ).elim)
    · exact hp.not_mem_left_of_not_mem_right hφ hnφ
    · exact hp.not_mem_right_of_not_mem_left hφ hnφ
    · exact hp.not_entails_bot_right
        (Theoryω.entails_iff.2 fun _ _ _ hM => (hM.not_notMem hφ hnφ).elim)
  imp := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φ ψ (himp | himp)
    · exact (hp.imp_left himp).imp (⟨_, _, Set.insert_union.symm, ·⟩)
        (⟨_, _, Set.insert_union.symm, ·⟩)
    · exact (hp.imp_right himp).imp (⟨_, _, Set.union_insert.symm, ·⟩)
        (⟨_, _, Set.union_insert.symm, ·⟩)
  not_imp := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φ ψ (hn | hn)
    · exact (hp.not_imp_left hn).imp (⟨_, _, Set.insert_union.symm, ·⟩)
        (⟨_, _, Set.insert_union.symm, ·⟩)
    · exact (hp.not_imp_right hn).imp (⟨_, _, Set.union_insert.symm, ·⟩)
        (⟨_, _, Set.union_insert.symm, ·⟩)
  iInf := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φs (hm | hm) k
    · exact ⟨_, _, Set.insert_union.symm, hp.iInf_left hm k⟩
    · exact ⟨_, _, Set.union_insert.symm, hp.iInf_right hm k⟩
  not_iInf := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φs (hm | hm)
    · exact (hp.not_iInf_left hm).imp fun _ hk => ⟨_, _, Set.insert_union.symm, hk⟩
    · exact (hp.not_iInf_right hm).imp fun _ hk => ⟨_, _, Set.union_insert.symm, hk⟩
  iSup := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φs (hm | hm)
    · exact (hp.iSup_left hm).imp fun _ hk => ⟨_, _, Set.insert_union.symm, hk⟩
    · exact (hp.iSup_right hm).imp fun _ hk => ⟨_, _, Set.union_insert.symm, hk⟩
  not_iSup := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φs (hm | hm) k
    · exact ⟨_, _, Set.insert_union.symm, hp.not_iSup_left hm k⟩
    · exact ⟨_, _, Set.union_insert.symm, hp.not_iSup_right hm k⟩
  all := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φ (hall | hall) c
    · exact ⟨_, _, Set.insert_union.symm, hp.all_left hall c⟩
    · exact (hp.not_all_mem_right hall).elim
  not_all := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ φ (hn | hn)
    · exact (hp.not_all_left hn).imp fun _ hc => ⟨_, _, Set.insert_union.symm, hc⟩
    · exact (hp.not_all_right hn).imp fun _ hc => ⟨_, _, Set.union_insert.symm, hc⟩
  eq_refl := by
    rintro _ ⟨_, _, rfl, hp⟩ t
    exact ⟨_, _, Set.insert_union.symm, hp.eq_refl_left t⟩
  eq_subst := by
    rintro _ ⟨Γ, Δ, rfl, hp⟩ t t' φ hφ (heq | heq) (hinst | hinst)
    · exact ⟨_, _, Set.insert_union.symm, hp.eq_subst_left heq hinst⟩
    · exact ⟨_, _, Set.union_insert.symm, hp.eq_subst_left_right hφ heq hinst⟩
    · exact ⟨_, _, Set.insert_union.symm, hp.eq_subst_right_left heq hinst⟩
    · exact ⟨_, _, Set.union_insert.symm, hp.eq_subst_right hφ heq hinst⟩
  eq_name := by
    rintro _ ⟨_, _, rfl, hp⟩ t
    exact (hp.eq_name_left t).imp fun _ hc => ⟨_, _, Set.insert_union.symm, hc⟩

end Engine

/-! ### Malitz interpolation -/

section Malitz

variable {L : Language.{u, v}}

/-- The root pair `({φ'}, {¬ψ'})` of the images of `φ` and `ψ` in `L[[ℕ]]` is a member of the
Malitz consistency property unless `φ` and `ψ` have a universal interpolant: a separator of the
root pair has no constants, so it is the image of such an interpolant. -/
private theorem malitzPair_root (φ ψ : L.Sentenceω) (hψ : ψ.IsUniversal)
    (hno : ¬ ∃ θ : L.Sentenceω, θ.IsUniversal ∧ θ.relationsIn ⊆ φ.relationsIn ∩ ψ.relationsIn ∧
      φ.Entails θ ∧ θ.Entails ψ) :
    MalitzPair ((L.lhomWithConstants ℕ).onBoundedFormulaInf φ).relationsIn
      ((L.lhomWithConstants ℕ).onBoundedFormulaInf ψ).relationsIn
      {(L.lhomWithConstants ℕ).onBoundedFormulaInf φ}
      {((L.lhomWithConstants ℕ).onBoundedFormulaInf ψ).not} := by
  let g := L.lhomWithConstants ℕ
  have hg : Function.Injective fun r : Σ n, L.Relations n => (⟨r.1, g.onRelation r.2⟩ :
      Σ n, L[[ℕ]].Relations n) :=
    Function.injective_id.sigma_map fun _ => (L.lhomWithConstants_injective ℕ).onRelation
  refine ⟨Set.finite_singleton _, Set.finite_singleton _,
    fun _ hχ => (Set.mem_singleton_iff.1 hχ) ▸ subset_rfl,
    fun _ hχ => by rw [Set.mem_singleton_iff.1 hχ, relationsIn_not],
    fun _ hχ => by rw [Set.mem_singleton_iff.1 hχ]; simp,
    fun _ hχ => by rw [Set.mem_singleton_iff.1 hχ]; simp,
    fun _ hχ => by rw [Set.mem_singleton_iff.1 hχ]; simpa using hψ, ?_⟩
  rintro ⟨θ', hθ'u, hθ'rel, hθ'supp, hφθ', hψθ'⟩
  have hK : theorySupport ({(g.onBoundedFormulaInf ψ).not} : L[[ℕ]].Theoryω) = ∅ := by
    simp [theorySupport, g]
  obtain ⟨θ, rfl⟩ := constantSupport_eq_empty_iff.1 (Set.subset_empty_iff.1 (hK ▸ hθ'supp))
  refine hno ⟨θ, by simpa using hθ'u, ?_, ?_, ?_⟩
  · rw [LHom.relationsIn_onBoundedFormulaInf, LHom.relationsIn_onBoundedFormulaInf,
      LHom.relationsIn_onBoundedFormulaInf, ← Set.image_inter hg] at hθ'rel
    exact (Set.image_subset_image_iff hg).1 hθ'rel
  · exact (Sentenceω.entails_onBoundedFormulaInf_iff (L.lhomWithConstants_injective ℕ)).1
      (Sentenceω.entails_def.2 hφθ')
  · have hnot : Sentenceω.Entails ψ.not θ.not :=
      (Sentenceω.entails_onBoundedFormulaInf_iff (L.lhomWithConstants_injective ℕ)).1
        (by simpa [g] using Sentenceω.entails_def.2 hψθ')
    exact Sentenceω.entails_iff.2 fun M _ _ hθM => by
      by_contra hψM
      exact SentenceInf.realize_not.1 (hnot.realize M (SentenceInf.realize_not.2 hψM)) hθM

/-- Countable core: over a relational language with countably many relation symbols, a valid
entailment `φ ⊨ ψ` with `ψ` universal has a universal Craig interpolant. -/
private theorem malitz_interpolation_of_countable [L.IsRelational]
    [Countable (Σ n, L.Relations n)] (φ ψ : L.Sentenceω) (hψ : ψ.IsUniversal)
    (h : φ.Entails ψ) :
    ∃ θ : L.Sentenceω, θ.IsUniversal ∧ θ.relationsIn ⊆ φ.relationsIn ∩ ψ.relationsIn ∧
      φ.Entails θ ∧ θ.Entails ψ := by
  have : IsEmpty (Σ n, L.Functions n) := ⟨fun s => isEmptyElim s.2⟩
  by_contra hno
  let g := L.lhomWithConstants ℕ
  obtain ⟨M, _, _, _, hM, _⟩ := (malitzConsistencyProperty (g.onBoundedFormulaInf φ).relationsIn
    (g.onBoundedFormulaInf ψ).relationsIn).model_existence.{u, v, max u v}
      ⟨_, _, rfl, malitzPair_root φ ψ hψ hno⟩
      ((Set.countable_singleton _).union (Set.countable_singleton _))
  let : L.Structure M := g.reduct M
  have hφM : SentenceInf.Realize φ M :=
    (LHom.realize_sentenceInf_onBoundedFormulaInf g φ).1
      (hM.realize_of_mem (.inl (Set.mem_singleton _)))
  exact SentenceInf.realize_not.1 (hM.realize_of_mem (.inr (Set.mem_singleton _)))
    ((LHom.realize_sentenceInf_onBoundedFormulaInf g ψ).2 (h.realize M hφM))

/-- **Malitz interpolation for `L_{ω₁ω}`.** Over a relational language `L` of any cardinality,
if an `L_{ω₁ω}` sentence `φ` entails a universal sentence `ψ`, there is a universal sentence `θ`
whose relation symbols occur in both `φ` and `ψ`, with `φ ⊨ θ` and `θ ⊨ ψ`. Universal sentences
are those of the `∀₁` class `BoundedFormulaInf.IsUniversal`, closed under countable conjunctions
and disjunctions; equality is logical, so `θ` may use it freely. -/
theorem malitz_interpolation [L.IsRelational] (φ ψ : L.Sentenceω) (hψ : ψ.IsUniversal)
    (h : φ.Entails ψ) :
    ∃ θ : L.Sentenceω, θ.IsUniversal ∧ θ.relationsIn ⊆ φ.relationsIn ∩ ψ.relationsIn ∧
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
  have h₀ : Sentenceω.Entails φ₀ ψ₀ :=
    (Sentenceω.entails_onBoundedFormulaInf_iff (symbSublangIncl_injective F R)).1
      (by rwa [hφ₀, hψ₀])
  obtain ⟨θ₀, hu₀, hrel₀, hφθ₀, hθψ₀⟩ := malitz_interpolation_of_countable φ₀ ψ₀
    ((LHom.universalSigned_onBoundedFormulaInf (symbSublangIncl F R) true ψ₀).1 (hψ₀ ▸ hψ)) h₀
  refine ⟨(symbSublangIncl F R).onBoundedFormulaInf θ₀, by simpa using hu₀, ?_,
    hφ₀ ▸ hφθ₀.onBoundedFormulaInf (symbSublangIncl F R),
    hψ₀ ▸ hθψ₀.onBoundedFormulaInf (symbSublangIncl F R)⟩
  rw [LHom.relationsIn_onBoundedFormulaInf]
  refine ((Set.image_mono hrel₀).trans (Set.image_inter_subset _ _ _)).trans ?_
  rw [← LHom.relationsIn_onBoundedFormulaInf, ← LHom.relationsIn_onBoundedFormulaInf, hφ₀, hψ₀]

end Malitz

end FirstOrder.Language
