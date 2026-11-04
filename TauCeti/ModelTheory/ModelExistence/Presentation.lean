/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.ModelExistence.Morleyization
public import TauCeti.ModelTheory.Semantics

/-!
# First-order presentations of infinitary fragments

The canonical Morley expansion of a structure can be described by a first-order theory together
with omitted first-order partial types. The theory gives the usual defining equivalences at
finitary constructors, and only one implication at infinitary conjunctions and disjunctions.
Omission supplies their missing implications. Thus the omitted types are essential: the
first-order theory alone need not characterize the canonical expansion.

`morleyTheory A` and `morleyTypes A` give this presentation for any component-closed fragment `A`.
Both are countable when `A` is countable, even over an uncountable language. The characterization
`model_morleyTheory_and_omitsType_iff_eq_morleyExpansion` allows arbitrary structure universes
and empty carriers.

The construction follows D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University
Press, 2016, Chapter 1. It uses the canonical expansion and its uniqueness theorem from
`TauCeti.ModelTheory.ModelExistence.Morleyization`.
-/

public section

universe u v w

namespace FirstOrder.Language

variable {L : Language.{u, v}} (A : Fragment L)

/-- The first-order atom `R_φ(x₀, …, xₙ₋₁)` naming a member of the fragment. -/
def morleyAtom {n : ℕ} (φ : L.BoundedFormulaω Empty n) (hφ : ⟨n, φ⟩ ∈ A) :
    (morleyize L A).BoundedFormula Empty n :=
  (morleyRel φ hφ).boundedFormula fun i => .var (Sum.inr i)

/-- The name of a fragment formula is its relation symbol applied to the bound variables. -/
theorem morleyAtom_def {n : ℕ} (φ : L.BoundedFormulaω Empty n) (hφ : ⟨n, φ⟩ ∈ A) :
    morleyAtom A φ hφ = (morleyRel φ hφ).boundedFormula (fun i => .var (Sum.inr i)) := (rfl)

/-- An atom naming a fragment member holds precisely when its new relation holds. -/
@[simp]
theorem realize_morleyAtom {M : Type w} [S : (morleyize L A).Structure M] {n : ℕ}
    {φ : L.BoundedFormulaω Empty n} (hφ : ⟨n, φ⟩ ∈ A) (a : Fin n → M) :
    (morleyAtom A φ hφ).Realize Empty.elim a ↔ S.RelMap (morleyRel φ hφ) a := by
  simp [morleyAtom]

/-- The first-order axioms for a fragment member. At an infinitary conjunction only the
implications to the conjuncts are asserted; at a disjunction only those from the disjuncts. -/
def morleyAxioms : ∀ {n : ℕ} (φ : L.BoundedFormulaω Empty n) (_hφ : ⟨n, φ⟩ ∈ A),
    Set (morleyize L A).Sentence
  | _, .falsum, h => {(morleyAtom A .falsum h).not.alls}
  | _, .equal t₁ t₂, h =>
      {((morleyAtom A (.equal t₁ t₂) h).iff
        ((lhomMorleyize (A : Set _)).onBoundedFormula (.equal t₁ t₂))).alls}
  | _, .rel R ts, h =>
      {((morleyAtom A (.rel R ts) h).iff
        ((lhomMorleyize (A : Set _)).onBoundedFormula (.rel R ts))).alls}
  | _, .imp φ ψ, h =>
      {((morleyAtom A (φ.imp ψ) h).iff
        ((morleyAtom A φ (A.imp_left_mem h)).imp
          (morleyAtom A ψ (A.imp_right_mem h)))).alls}
  | _, .all φ, h =>
      {((morleyAtom A φ.all h).iff (morleyAtom A φ (A.all_mem h)).all).alls}
  | _, .iInf φs, h => Set.range fun k =>
      ((morleyAtom A (.iInf φs) h).imp (morleyAtom A (φs k) (A.iInf_mem h k))).alls
  | _, .iSup φs, h => Set.range fun k =>
      ((morleyAtom A (φs k) (A.iSup_mem h k)).imp (morleyAtom A (.iSup φs) h)).alls

/-- The axiom for falsum asserts that its name never holds. -/
@[simp]
theorem morleyAxioms_falsum {n : ℕ} (hφ : ⟨n, BoundedFormulaInf.falsum⟩ ∈ A) :
    morleyAxioms A .falsum hφ = {(morleyAtom A .falsum hφ).not.alls} := (rfl)

/-- The axiom for equality identifies its name with the original equality. -/
@[simp]
theorem morleyAxioms_equal {n : ℕ} (t₁ t₂ : L.Term (Empty ⊕ Fin n))
    (hφ : ⟨n, BoundedFormulaInf.equal t₁ t₂⟩ ∈ A) :
    morleyAxioms A (.equal t₁ t₂) hφ =
      {((morleyAtom A (.equal t₁ t₂) hφ).iff
        ((lhomMorleyize (A : Set _)).onBoundedFormula (.equal t₁ t₂))).alls} := (rfl)

/-- The axiom for a relation identifies its name with the original atom. -/
@[simp]
theorem morleyAxioms_rel {n k : ℕ} (R : L.Relations k) (ts : Fin k → L.Term (Empty ⊕ Fin n))
    (hφ : ⟨n, BoundedFormulaInf.rel R ts⟩ ∈ A) :
    morleyAxioms A (.rel R ts) hφ =
      {((morleyAtom A (.rel R ts) hφ).iff
        ((lhomMorleyize (A : Set _)).onBoundedFormula (.rel R ts))).alls} := (rfl)

/-- The name of an implication is equivalent to the implication between the component names. -/
@[simp]
theorem morleyAxioms_imp {n : ℕ} (φ ψ : L.BoundedFormulaω Empty n) (hφ : ⟨n, φ.imp ψ⟩ ∈ A) :
    morleyAxioms A (φ.imp ψ) hφ =
      {((morleyAtom A (φ.imp ψ) hφ).iff
        ((morleyAtom A φ (A.imp_left_mem hφ)).imp
          (morleyAtom A ψ (A.imp_right_mem hφ)))).alls} := (rfl)

/-- The name of a universal formula is equivalent to quantifying the last variable of its
body's name, with the other parameters fixed. -/
@[simp]
theorem morleyAxioms_all {n : ℕ} (φ : L.BoundedFormulaω Empty (n + 1)) (hφ : ⟨n, φ.all⟩ ∈ A) :
    morleyAxioms A φ.all hφ =
      {((morleyAtom A φ.all hφ).iff (morleyAtom A φ (A.all_mem hφ)).all).alls} := (rfl)

/-- A conjunction name implies every component name. -/
@[simp]
theorem morleyAxioms_iInf {n : ℕ} (φs : ℕ → L.BoundedFormulaω Empty n)
    (hφ : ⟨n, BoundedFormulaInf.iInf φs⟩ ∈ A) :
    morleyAxioms A (.iInf φs) hφ = Set.range fun k =>
      ((morleyAtom A (.iInf φs) hφ).imp
        (morleyAtom A (φs k) (A.iInf_mem hφ k))).alls := (rfl)

/-- Each disjunct name implies the disjunction name. -/
@[simp]
theorem morleyAxioms_iSup {n : ℕ} (φs : ℕ → L.BoundedFormulaω Empty n)
    (hφ : ⟨n, BoundedFormulaInf.iSup φs⟩ ∈ A) :
    morleyAxioms A (.iSup φs) hφ = Set.range fun k =>
      ((morleyAtom A (φs k) (A.iSup_mem hφ k)).imp
        (morleyAtom A (.iSup φs) hφ)).alls := (rfl)

/-- The first-order Morley theory of a component-closed infinitary fragment. -/
def morleyTheory : (morleyize L A).Theory :=
  ⋃ p : A, morleyAxioms A p.1.2 p.2

/-- A sentence belongs to the Morley theory iff it is an axiom of a fragment member. -/
theorem mem_morleyTheory_iff {σ : (morleyize L A).Sentence} :
    σ ∈ morleyTheory A ↔ ∃ (n : ℕ) (φ : L.BoundedFormulaω Empty n) (hφ : ⟨n, φ⟩ ∈ A),
      σ ∈ morleyAxioms A φ hφ := by
  simp only [morleyTheory, Set.mem_iUnion, Subtype.exists, Sigma.exists]

/-- All axioms associated with a fragment member belong to the Morley theory. -/
theorem morleyAxioms_subset_morleyTheory {n : ℕ} {φ : L.BoundedFormulaω Empty n}
    (hφ : ⟨n, φ⟩ ∈ A) : morleyAxioms A φ hφ ⊆ morleyTheory A :=
  fun _ h => (mem_morleyTheory_iff A).2 ⟨n, φ, hφ, h⟩

section AxiomSemantics

variable {M : Type w} [S : (morleyize L A).Structure M]

/-- A model of the Morley theory satisfies the axioms of each fragment member. -/
theorem model_morleyAxioms (hT : M ⊨ morleyTheory A) {n : ℕ}
    (φ : L.BoundedFormulaω Empty n) (hφ : ⟨n, φ⟩ ∈ A) :
    M ⊨ morleyAxioms A φ hφ :=
  hT.mono (morleyAxioms_subset_morleyTheory A hφ)

/-- The falsum axiom says that its relation is always false. -/
theorem model_morleyAxioms_falsum_iff {n : ℕ}
    (hφ : ⟨n, BoundedFormulaInf.falsum⟩ ∈ A) :
    M ⊨ morleyAxioms A .falsum hφ ↔
      ∀ a : Fin n → M, ¬S.RelMap (morleyRel .falsum hφ) a := by
  simp [morleyAxioms, Sentence.realize_alls]

/-- The equality axiom identifies its relation with equality in the reduct. -/
theorem model_morleyAxioms_equal_iff [L.Structure M]
    [(lhomMorleyize (A : Set (Σ n, L.BoundedFormulaω Empty n))).IsExpansionOn M] {n : ℕ}
    (t₁ t₂ : L.Term (Empty ⊕ Fin n)) (hφ : ⟨n, BoundedFormulaInf.equal t₁ t₂⟩ ∈ A) :
    M ⊨ morleyAxioms A (.equal t₁ t₂) hφ ↔
      ∀ a : Fin n → M, S.RelMap (morleyRel (.equal t₁ t₂) hφ) a ↔
        t₁.realize (Sum.elim Empty.elim a) = t₂.realize (Sum.elim Empty.elim a) := by
  simp [morleyAxioms, Sentence.realize_alls, BoundedFormula.realize_bdEqual]

/-- The relation axiom identifies its relation with the original atom in the reduct. -/
theorem model_morleyAxioms_rel_iff [L.Structure M]
    [(lhomMorleyize (A : Set (Σ n, L.BoundedFormulaω Empty n))).IsExpansionOn M] {n k : ℕ}
    (R : L.Relations k) (ts : Fin k → L.Term (Empty ⊕ Fin n))
    (hφ : ⟨n, BoundedFormulaInf.rel R ts⟩ ∈ A) :
    M ⊨ morleyAxioms A (.rel R ts) hφ ↔
      ∀ a : Fin n → M, S.RelMap (morleyRel (.rel R ts) hφ) a ↔
        Structure.RelMap R (fun i => (ts i).realize (Sum.elim Empty.elim a)) := by
  simp only [morleyAxioms_rel, Theory.model_singleton_iff, Sentence.realize_alls,
    BoundedFormula.realize_iff, realize_morleyAtom, LHom.realize_onBoundedFormula]
  exact forall_congr' fun _ => iff_congr Iff.rfl BoundedFormula.realize_rel

/-- The implication axiom identifies its relation with implication between component relations. -/
theorem model_morleyAxioms_imp_iff {n : ℕ} (φ ψ : L.BoundedFormulaω Empty n)
    (hφ : ⟨n, φ.imp ψ⟩ ∈ A) :
    M ⊨ morleyAxioms A (φ.imp ψ) hφ ↔
      ∀ a : Fin n → M, S.RelMap (morleyRel (φ.imp ψ) hφ) a ↔
        (S.RelMap (morleyRel φ (A.imp_left_mem hφ)) a →
          S.RelMap (morleyRel ψ (A.imp_right_mem hφ)) a) := by
  simp [morleyAxioms, Sentence.realize_alls]

/-- The universal axiom identifies its relation with quantification over the last variable of
the body relation, with the other parameters fixed. -/
theorem model_morleyAxioms_all_iff {n : ℕ} (φ : L.BoundedFormulaω Empty (n + 1))
    (hφ : ⟨n, φ.all⟩ ∈ A) :
    M ⊨ morleyAxioms A φ.all hφ ↔
      ∀ a : Fin n → M, S.RelMap (morleyRel φ.all hφ) a ↔
        ∀ b, S.RelMap (morleyRel φ (A.all_mem hφ)) (Fin.snoc a b) := by
  simp [morleyAxioms, Sentence.realize_alls]

/-- The conjunction axioms give the implications to each component relation. -/
theorem model_morleyAxioms_iInf_iff {n : ℕ} (φs : ℕ → L.BoundedFormulaω Empty n)
    (hφ : ⟨n, BoundedFormulaInf.iInf φs⟩ ∈ A) :
    M ⊨ morleyAxioms A (.iInf φs) hφ ↔
      ∀ k (a : Fin n → M), S.RelMap (morleyRel (.iInf φs) hφ) a →
        S.RelMap (morleyRel (φs k) (A.iInf_mem hφ k)) a := by
  simp [morleyAxioms, Sentence.realize_alls, Theory.model_iff]

/-- The disjunction axioms give the implications from each component relation. -/
theorem model_morleyAxioms_iSup_iff {n : ℕ} (φs : ℕ → L.BoundedFormulaω Empty n)
    (hφ : ⟨n, BoundedFormulaInf.iSup φs⟩ ∈ A) :
    M ⊨ morleyAxioms A (.iSup φs) hφ ↔
      ∀ k (a : Fin n → M), S.RelMap (morleyRel (φs k) (A.iSup_mem hφ k)) a →
        S.RelMap (morleyRel (.iSup φs) hφ) a := by
  simp [morleyAxioms, Sentence.realize_alls, Theory.model_iff]

end AxiomSemantics

/-- The Morley theory of a countable fragment is countable, without a language-size assumption. -/
theorem countable_morleyTheory (hA : (A : Set (Σ n, L.BoundedFormulaω Empty n)).Countable) :
    (morleyTheory A).Countable := by
  have := hA.to_subtype
  refine Set.countable_iUnion fun p => ?_
  rcases p with ⟨⟨n, φ⟩, hφ⟩
  cases φ <;> simp only [morleyAxioms] <;>
    first | exact Set.countable_singleton _ | exact Set.countable_range _

/-- The obstruction to the converse implication at a countable conjunction. -/
def morleyInfType {n : ℕ} (φs : ℕ → L.BoundedFormulaω Empty n) (hφ : ⟨n, .iInf φs⟩ ∈ A) :
    Set ((morleyize L A).BoundedFormula Empty n) :=
  {(morleyAtom A (.iInf φs) hφ).not} ∪
    Set.range fun k => morleyAtom A (φs k) (A.iInf_mem hφ k)

/-- The obstruction to the converse implication at a countable disjunction. -/
def morleySupType {n : ℕ} (φs : ℕ → L.BoundedFormulaω Empty n) (hφ : ⟨n, .iSup φs⟩ ∈ A) :
    Set ((morleyize L A).BoundedFormula Empty n) :=
  {morleyAtom A (.iSup φs) hφ} ∪
    Set.range fun k => (morleyAtom A (φs k) (A.iSup_mem hφ k)).not

/-- The members of a conjunction obstruction type. -/
@[simp]
theorem mem_morleyInfType {n : ℕ} {φs : ℕ → L.BoundedFormulaω Empty n}
    (hφ : ⟨n, .iInf φs⟩ ∈ A) {ψ : (morleyize L A).BoundedFormula Empty n} :
    ψ ∈ morleyInfType A φs hφ ↔ ψ = (morleyAtom A (.iInf φs) hφ).not ∨
      ∃ k, morleyAtom A (φs k) (A.iInf_mem hφ k) = ψ := by
  simp [morleyInfType]

/-- The members of a disjunction obstruction type. -/
@[simp]
theorem mem_morleySupType {n : ℕ} {φs : ℕ → L.BoundedFormulaω Empty n}
    (hφ : ⟨n, .iSup φs⟩ ∈ A) {ψ : (morleyize L A).BoundedFormula Empty n} :
    ψ ∈ morleySupType A φs hφ ↔ ψ = morleyAtom A (.iSup φs) hφ ∨
      ∃ k, (morleyAtom A (φs k) (A.iSup_mem hφ k)).not = ψ := by
  simp [morleySupType]

/-- A fragment member contributes an omitted type exactly when it is infinitary. -/
private def morleyObstruction : ∀ {n : ℕ} (φ : L.BoundedFormulaω Empty n) (_hφ : ⟨n, φ⟩ ∈ A),
    Option (Σ n, Set ((morleyize L A).BoundedFormula Empty n))
  | n, .iInf φs, h => some ⟨n, morleyInfType A φs h⟩
  | n, .iSup φs, h => some ⟨n, morleySupType A φs h⟩
  | _, _, _ => none

/-- The family of first-order partial types whose omission completes the Morley theory. -/
def morleyTypes : Set (Σ n, Set ((morleyize L A).BoundedFormula Empty n)) :=
  Option.some ⁻¹' Set.range fun p : A => morleyObstruction A p.1.2 p.2

/-- The omitted types are precisely the conjunction and disjunction obstruction types. -/
theorem mem_morleyTypes_iff {p : Σ n, Set ((morleyize L A).BoundedFormula Empty n)} :
    p ∈ morleyTypes A ↔
      (∃ (n : ℕ) (φs : ℕ → L.BoundedFormulaω Empty n) (hφ : ⟨n, .iInf φs⟩ ∈ A),
        p = ⟨n, morleyInfType A φs hφ⟩) ∨
      (∃ (n : ℕ) (φs : ℕ → L.BoundedFormulaω Empty n) (hφ : ⟨n, .iSup φs⟩ ∈ A),
        p = ⟨n, morleySupType A φs hφ⟩) := by
  constructor
  · rintro ⟨⟨⟨n, φ⟩, hφ⟩, hp⟩
    cases φ <;> simp only [morleyObstruction, reduceCtorEq, Option.some.injEq] at hp
    · exact Or.inr ⟨_, _, hφ, hp.symm⟩
    · exact Or.inl ⟨_, _, hφ, hp.symm⟩
  · rintro (⟨n, φs, hφ, rfl⟩ | ⟨n, φs, hφ, rfl⟩)
    · exact ⟨⟨⟨n, .iInf φs⟩, hφ⟩, rfl⟩
    · exact ⟨⟨⟨n, .iSup φs⟩, hφ⟩, rfl⟩

/-- Every conjunction member contributes its obstruction type. -/
@[simp]
theorem morleyInfType_mem_morleyTypes {n : ℕ} (φs : ℕ → L.BoundedFormulaω Empty n)
    (hφ : ⟨n, BoundedFormulaInf.iInf φs⟩ ∈ A) :
    (⟨n, morleyInfType A φs hφ⟩ : Σ n, Set ((morleyize L A).BoundedFormula Empty n)) ∈
      morleyTypes A :=
  (mem_morleyTypes_iff A).2 (Or.inl ⟨n, φs, hφ, rfl⟩)

/-- Every disjunction member contributes its obstruction type. -/
@[simp]
theorem morleySupType_mem_morleyTypes {n : ℕ} (φs : ℕ → L.BoundedFormulaω Empty n)
    (hφ : ⟨n, BoundedFormulaInf.iSup φs⟩ ∈ A) :
    (⟨n, morleySupType A φs hφ⟩ : Σ n, Set ((morleyize L A).BoundedFormula Empty n)) ∈
      morleyTypes A :=
  (mem_morleyTypes_iff A).2 (Or.inr ⟨n, φs, hφ, rfl⟩)

/-- A countable fragment has countably many obstruction types. -/
theorem countable_morleyTypes (hA : (A : Set (Σ n, L.BoundedFormulaω Empty n)).Countable) :
    (morleyTypes A).Countable := by
  have := hA.to_subtype
  exact (Set.countable_range _).preimage (Option.some_injective _)

/-- Every obstruction type is countable, regardless of the size of the fragment or language. -/
theorem countable_of_mem_morleyTypes {p : Σ n, Set ((morleyize L A).BoundedFormula Empty n)}
    (hp : p ∈ morleyTypes A) : p.2.Countable := by
  rcases (mem_morleyTypes_iff A).1 hp with ⟨n, φs, hφ, rfl⟩ | ⟨n, φs, hφ, rfl⟩ <;>
    exact (Set.countable_singleton _).union (Set.countable_range _)

section Semantics

variable {M : Type w} [L.Structure M]

/-- The canonical expansion satisfies every first-order Morley axiom. -/
theorem morleyTheory_model :
    let := morleyExpansion (A : Set (Σ n, L.BoundedFormulaω Empty n)) M
    M ⊨ morleyTheory A := by
  let := morleyExpansion (A : Set (Σ n, L.BoundedFormulaω Empty n)) M
  refine ⟨fun σ hσ => ?_⟩
  obtain ⟨n, φ, hφ, hσ⟩ := (mem_morleyTheory_iff A).1 hσ
  have h : M ⊨ morleyAxioms A φ hφ := by
    cases φ with
    | falsum =>
      apply (model_morleyAxioms_falsum_iff A hφ).2
      intro a
      simp only [morleyExpansion_relMap_morleyRel, BoundedFormulaInf.realize_falsum,
        not_false_eq_true]
    | equal t₁ t₂ =>
      exact (model_morleyAxioms_equal_iff A t₁ t₂ hφ).2 fun a =>
        (morleyExpansion_relMap_morleyRel hφ a).trans BoundedFormulaInf.realize_equal
    | rel R ts =>
      exact (model_morleyAxioms_rel_iff A R ts hφ).2 fun a =>
        (morleyExpansion_relMap_morleyRel hφ a).trans BoundedFormulaInf.realize_rel
    | imp φ ψ =>
      apply (model_morleyAxioms_imp_iff A φ ψ hφ).2
      intro a
      simp only [morleyExpansion_relMap_morleyRel, BoundedFormulaInf.realize_imp]
    | all φ =>
      apply (model_morleyAxioms_all_iff A φ hφ).2
      intro a
      simp only [morleyExpansion_relMap_morleyRel, BoundedFormulaInf.realize_all]
    | iSup φs =>
      apply (model_morleyAxioms_iSup_iff A φs hφ).2
      intro k a hk
      rw [morleyExpansion_relMap_morleyRel, BoundedFormulaInf.realize_iSup]
      exact ⟨k, (morleyExpansion_relMap_morleyRel (A.iSup_mem hφ k) a).1 hk⟩
    | iInf φs =>
      apply (model_morleyAxioms_iInf_iff A φs hφ).2
      intro k a ha
      rw [morleyExpansion_relMap_morleyRel, BoundedFormulaInf.realize_iInf] at ha
      exact (morleyExpansion_relMap_morleyRel (A.iInf_mem hφ k) a).2 (ha k)
  exact h.realize_of_mem σ hσ

omit [L.Structure M] in
/-- Omitting a conjunction obstruction supplies the missing implication to the conjunction's
name. The type is embedded into infinitary syntax only to use the existing omission predicate. -/
theorem omitsType_morleyInfType_iff [S : (morleyize L A).Structure M] {n : ℕ}
    {φs : ℕ → L.BoundedFormulaω Empty n} (hφ : ⟨n, .iInf φs⟩ ∈ A) :
    OmitsType M (BoundedFormula.toOmega '' morleyInfType A φs hφ) ↔
      ∀ a : Fin n → M, (∀ k, S.RelMap (morleyRel (φs k) (A.iInf_mem hφ k)) a) →
        S.RelMap (morleyRel (.iInf φs) hφ) a := by
  classical
  simp only [omitsType_iff, Set.exists_mem_image, BoundedFormula.realize_toInf,
    morleyInfType, Set.exists_mem_union, Set.exists_mem_singleton,
    Set.mem_range, exists_exists_eq_and,
    BoundedFormula.realize_not, not_not, realize_morleyAtom]
  simp only [← not_forall, or_iff_not_imp_right, not_not]

omit [L.Structure M] in
/-- Omitting a disjunction obstruction supplies the missing implication from its name to some
component name. -/
theorem omitsType_morleySupType_iff [S : (morleyize L A).Structure M] {n : ℕ}
    {φs : ℕ → L.BoundedFormulaω Empty n} (hφ : ⟨n, .iSup φs⟩ ∈ A) :
    OmitsType M (BoundedFormula.toOmega '' morleySupType A φs hφ) ↔
      ∀ a : Fin n → M, S.RelMap (morleyRel (.iSup φs) hφ) a →
        ∃ k, S.RelMap (morleyRel (φs k) (A.iSup_mem hφ k)) a := by
  classical
  simp only [omitsType_iff, Set.exists_mem_image, BoundedFormula.realize_toInf,
    morleySupType, Set.exists_mem_union, Set.exists_mem_singleton,
    Set.mem_range, exists_exists_eq_and,
    BoundedFormula.realize_not, not_not, realize_morleyAtom]
  simp only [or_iff_not_imp_left, not_not]

/-- The canonical expansion omits every obstruction type. -/
theorem morleyExpansion_omitsType_of_mem_morleyTypes
    {p : Σ n, Set ((morleyize L A).BoundedFormula Empty n)} (hp : p ∈ morleyTypes A) :
    let := morleyExpansion (A : Set (Σ n, L.BoundedFormulaω Empty n)) M
    OmitsType M (BoundedFormula.toOmega '' p.2) := by
  let := morleyExpansion (A : Set (Σ n, L.BoundedFormulaω Empty n)) M
  rcases (mem_morleyTypes_iff A).1 hp with ⟨n, φs, hφ, rfl⟩ | ⟨n, φs, hφ, rfl⟩
  · exact (omitsType_morleyInfType_iff A hφ).2 (by simp)
  · exact (omitsType_morleySupType_iff A hφ).2 (by simp)

variable [S : (morleyize L A).Structure M]
  [(lhomMorleyize (A : Set (Σ n, L.BoundedFormulaω Empty n))).IsExpansionOn M]

/-- In an expansion satisfying the Morley theory and omitting its obstruction types, every
first-order name has the intended infinitary meaning. -/
theorem realize_morleyAtom_of_model_morleyTheory_of_omitsType (hT : M ⊨ morleyTheory A)
    (hP : ∀ p ∈ morleyTypes A, OmitsType M (BoundedFormula.toOmega '' p.2)) :
    ∀ {n : ℕ} (φ : L.BoundedFormulaω Empty n) (hφ : ⟨n, φ⟩ ∈ A) (a : Fin n → M),
      (morleyAtom A φ hφ).Realize Empty.elim a ↔ φ.Realize Empty.elim a := by
  simp only [realize_morleyAtom]
  intro n φ
  -- Finitary nodes use the defining equivalences. At infinitary nodes the theory supplies
  -- one direction and omission supplies the other, with the induction hypothesis at every tuple.
  induction φ with
  | falsum =>
    intro hφ a
    simpa only [BoundedFormulaInf.realize_falsum, iff_false] using
      (model_morleyAxioms_falsum_iff A hφ).1 (model_morleyAxioms A hT _ hφ) a
  | equal t₁ t₂ | rel t₁ t₂ =>
    intro hφ a
    have h := model_morleyAxioms A hT _ hφ
    simp only [model_morleyAxioms_equal_iff, model_morleyAxioms_rel_iff] at h
    simpa only [BoundedFormulaInf.realize_equal, BoundedFormulaInf.realize_rel] using h a
  | imp φ ψ ihφ ihψ =>
    intro hφ a
    exact ((model_morleyAxioms_imp_iff A φ ψ hφ).1
      (model_morleyAxioms A hT _ hφ) a).trans
      (imp_congr (ihφ (A.imp_left_mem hφ) a) (ihψ (A.imp_right_mem hφ) a))
  | all φ ih =>
    intro hφ a
    exact ((model_morleyAxioms_all_iff A φ hφ).1
      (model_morleyAxioms A hT _ hφ) a).trans
      (forall_congr' fun b => ih (A.all_mem hφ) (Fin.snoc a b))
  | iSup φs ih =>
    intro hφ a
    have h := (model_morleyAxioms_iSup_iff A φs hφ).1 (model_morleyAxioms A hT _ hφ)
    have hp := (omitsType_morleySupType_iff A hφ).1
      (hP _ (morleySupType_mem_morleyTypes A φs hφ)) a
    rw [BoundedFormulaInf.realize_iSup]
    constructor
    · intro ha
      obtain ⟨k, hk⟩ := hp ha
      exact ⟨k, (ih k (A.iSup_mem hφ k) a).1 hk⟩
    · rintro ⟨k, hk⟩
      exact h k a ((ih k (A.iSup_mem hφ k) a).2 hk)
  | iInf φs ih =>
    intro hφ a
    have h := (model_morleyAxioms_iInf_iff A φs hφ).1 (model_morleyAxioms A hT _ hφ)
    have hp := (omitsType_morleyInfType_iff A hφ).1
      (hP _ (morleyInfType_mem_morleyTypes A φs hφ)) a
    rw [BoundedFormulaInf.realize_iInf]
    constructor
    · intro ha k
      exact (ih k (A.iInf_mem hφ k) a).1 (h k a ha)
    · intro ha
      exact hp fun k => (ih k (A.iInf_mem hφ k) a).2 (ha k)

/-- **First-order presentation of a fragment.** Among expansions of an `L`-structure, the
models of the Morley theory omitting all its obstruction types are exactly the canonical
expansion. The theory and types are explicit; no countability assumption is needed for the
characterization itself. -/
theorem model_morleyTheory_and_omitsType_iff_eq_morleyExpansion :
    (M ⊨ morleyTheory A ∧
      ∀ p ∈ morleyTypes A, OmitsType M (BoundedFormula.toOmega '' p.2)) ↔
      S = morleyExpansion (A : Set (Σ n, L.BoundedFormulaω Empty n)) M := by
  constructor
  · rintro ⟨hT, hP⟩
    apply eq_morleyExpansion_of_model_definingTheory
    refine (model_definingTheory_iff S).2 fun φ hφ a => ?_
    exact (realize_morleyAtom A hφ a).symm.trans
      (realize_morleyAtom_of_model_morleyTheory_of_omitsType A hT hP φ hφ a)
  · intro h
    subst S
    exact ⟨morleyTheory_model A, fun _ hp => morleyExpansion_omitsType_of_mem_morleyTypes A hp⟩

end Semantics

section Sentence

variable {M : Type w} [L.Structure M]

/-- The models of a sentence in a fragment are exactly the reducts of expansions satisfying
its first-order presentation with the sentence's name asserted and all obstruction types omitted.
The expansion uses the same carrier, so any nonemptiness or cardinality bound is preserved. -/
theorem realize_iff_exists_model_morleyTheory_omitsType {φ : L.Sentenceω} (hφ : ⟨0, φ⟩ ∈ A) :
    SentenceInf.Realize φ M ↔
      ∃ S : (morleyize L A).Structure M, letI := S;
        (lhomMorleyize (A : Set (Σ n, L.BoundedFormulaω Empty n))).IsExpansionOn M ∧
        M ⊨ insert (morleyAtom A φ hφ).alls (morleyTheory A) ∧
        ∀ p ∈ morleyTypes A, OmitsType M (BoundedFormula.toOmega '' p.2) := by
  constructor
  · intro hM
    let := morleyExpansion (A : Set (Σ n, L.BoundedFormulaω Empty n)) M
    refine ⟨morleyExpansion (A : Set (Σ n, L.BoundedFormulaω Empty n)) M,
      inferInstance, Theory.model_insert_iff.2 ⟨?_, morleyTheory_model A⟩,
      fun _ hp => morleyExpansion_omitsType_of_mem_morleyTypes A hp⟩
    rw [Sentence.realize_alls]
    intro a
    simpa only [realize_morleyAtom, morleyExpansion_relMap_morleyRel,
      SentenceInf.realize_def, FormulaInf.realize_def, Subsingleton.elim a default] using hM
  · rintro ⟨S, he, hS, hP⟩
    let := S
    let := he
    obtain ⟨ha, hT⟩ := Theory.model_insert_iff.1 hS
    rw [Sentence.realize_alls] at ha
    rw [SentenceInf.realize_def, FormulaInf.realize_def]
    exact (realize_morleyAtom_of_model_morleyTheory_of_omitsType A hT hP φ hφ default).1
      (ha default)

end Sentence

end FirstOrder.Language
