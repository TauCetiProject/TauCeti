/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Algebra.Group.QuantifierFree

/-!
# Existential and universal group formulas as solution statements

An existential formula `∃ y₁ … ∃ y_k, φ` in the group language with named coefficients, with
`φ` quantifier-free, holds exactly when one of finitely many systems of word equations and
inequations has a solution in which the witnesses `y₁, …, y_k` are fresh variables. Dually, a
universal formula `∀ y₁ … ∀ y_k, φ` holds exactly when none of the finitely many systems
attached to `¬φ` has a solution. The finite family depends only on the formula, not on the
group or on the interpretation of the coefficients.

For sentences this identifies the existential and universal theories of a group with
coefficients with solvability statements for finite families of equation–inequation systems.

## Main results

* `FirstOrder.Language.group.existential_iff_systems` and
  `FirstOrder.Language.group.universal_iff_systems`: the reductions for bounded formulas,
  keeping free variables and outer bound-variable slots as parameters.
* `FirstOrder.Language.group.existential_iff_solution`: an existential sentence holds exactly
  when one system of a finite family has a solution.
* `FirstOrder.Language.group.universal_iff_no_solution`: a universal sentence holds exactly
  when no system of a finite family has a solution.

The reduction of existential and universal sentences to systems of equations and inequations
follows Kharlampovich and Myasnikov, *Implicit function theorem over free groups*, §2.3.
-/

public section

namespace FirstOrder.Language.group

open FirstOrder TauCeti

variable {X A : Type*} {n : ℕ}

/-- Reindex the last bound slot of `Fin (n + 1)` as the first witness slot, shifting the
other `k` witnesses up by one. -/
private def snocWitness (n k : ℕ) : Fin (n + 1) ⊕ Fin k → Fin n ⊕ Fin (k + 1) :=
  Sum.elim (Fin.lastCases (Sum.inr 0) Sum.inl) fun j => Sum.inr j.succ

private theorem sumElim_cons_comp_snocWitness {G : Type*} {k : ℕ} (xs : Fin n → G) (x : G)
    (ys : Fin k → G) :
    Sum.elim xs (Fin.cons x ys) ∘ snocWitness n k = Sum.elim (Fin.snoc xs x) ys := by
  funext i
  rcases i with i | j
  · induction i using Fin.lastCases <;> simp [snocWitness]
  · simp [snocWitness]

/-- With no witnesses, the relabelled quantifier-free family keeps its solutions. -/
private theorem exists_solution_relabel_inl_iff {G : Type*} [Group G]
    (systems : List (EqIneqSystem (X ⊕ Fin n) A)) (v : X → G) (c : A → G) (xs : Fin n → G) :
    (∃ ys : Fin 0 → G, ∃ S ∈ systems.map (EqIneqSystem.relabel (Sum.map id Sum.inl)),
        S.IsSolution (Sum.elim v (Sum.elim xs ys)) c) ↔
      ∃ S ∈ systems, S.IsSolution (Sum.elim v xs) c := by
  have hcomp (ys : Fin 0 → G) :
      Sum.elim v (Sum.elim xs ys) ∘ Sum.map id Sum.inl = Sum.elim v xs := by
    funext i
    rcases i with x | i <;> rfl
  simp [hcomp]

/-- Existentially quantifying the last bound slot moves it into the witness block. -/
private theorem exists_snoc_iff {G : Type*} [Group G] {k : ℕ}
    (systems : List (EqIneqSystem (X ⊕ (Fin (n + 1) ⊕ Fin k)) A)) (v : X → G) (c : A → G)
    (xs : Fin n → G) :
    (∃ x : G, ∃ ys : Fin k → G, ∃ S ∈ systems,
        S.IsSolution (Sum.elim v (Sum.elim (Fin.snoc xs x) ys)) c) ↔
      ∃ ys : Fin (k + 1) → G,
        ∃ S ∈ systems.map (EqIneqSystem.relabel (Sum.map id (snocWitness n k))),
          S.IsSolution (Sum.elim v (Sum.elim xs ys)) c := by
  have hcomp (x : G) (ys : Fin k → G) :
      Sum.elim v (Sum.elim xs (Fin.cons x ys)) ∘ Sum.map id (snocWitness n k) =
        Sum.elim v (Sum.elim (Fin.snoc xs x) ys) := by
    rw [Sum.elim_comp_map, Function.comp_id, sumElim_cons_comp_snocWitness]
  simp [Fin.exists_fin_succ_pi, hcomp]

/-- An existential group formula is uniformly equivalent to the solvability of one of finitely
many word systems whose variables are the free variables, the bound-variable slots and `k`
fresh witnesses. The same family works for every group and coefficient map. -/
theorem existential_iff_systems
    {φ : Language.group[[A]].BoundedFormula X n} (hφ : φ.IsExistential) :
    ∃ (k : ℕ) (systems : List (EqIneqSystem (X ⊕ (Fin n ⊕ Fin k)) A)),
      ∀ (G : Type*) [Group G] (v : X → G) (c : A → G) (xs : Fin n → G),
        letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
        letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
        φ.Realize v xs ↔
          ∃ ys : Fin k → G, ∃ S ∈ systems, S.IsSolution (Sum.elim v (Sum.elim xs ys)) c := by
  induction hφ with
  | of_isQF h =>
    obtain ⟨systems, hsys⟩ := quantifierFree_iff_systems h
    refine ⟨0, systems.map (EqIneqSystem.relabel (Sum.map id Sum.inl)), fun G _ v c xs => ?_⟩
    rw [exists_solution_relabel_inl_iff]
    exact hsys G v c xs
  | ex _ ih =>
    obtain ⟨k, systems, hsys⟩ := ih
    refine ⟨k + 1, systems.map (EqIneqSystem.relabel (Sum.map id (snocWitness _ k))),
      fun G _ v c xs => ?_⟩
    let : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    let : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    rw [BoundedFormula.realize_ex, ← exists_snoc_iff]
    exact exists_congr fun x => hsys G v c (Fin.snoc xs x)

/-- A universal group formula is uniformly equivalent to the unsolvability of every system in
a finite family whose variables are the free variables, the bound-variable slots and `k`
fresh witnesses; these systems describe the negated quantifier-free matrix. The same family
works for every group and coefficient map. -/
theorem universal_iff_systems
    {φ : Language.group[[A]].BoundedFormula X n} (hφ : φ.IsUniversal) :
    ∃ (k : ℕ) (systems : List (EqIneqSystem (X ⊕ (Fin n ⊕ Fin k)) A)),
      ∀ (G : Type*) [Group G] (v : X → G) (c : A → G) (xs : Fin n → G),
        letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
        letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
        φ.Realize v xs ↔
          ¬∃ ys : Fin k → G, ∃ S ∈ systems, S.IsSolution (Sum.elim v (Sum.elim xs ys)) c := by
  induction hφ with
  | of_isQF h =>
    obtain ⟨systems, hsys⟩ := quantifierFree_iff_systems h.not
    refine ⟨0, systems.map (EqIneqSystem.relabel (Sum.map id Sum.inl)), fun G _ v c xs => ?_⟩
    let : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    let : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    rw [exists_solution_relabel_inl_iff, ← hsys G v c xs, BoundedFormula.realize_not, not_not]
  | all _ ih =>
    obtain ⟨k, systems, hsys⟩ := ih
    refine ⟨k + 1, systems.map (EqIneqSystem.relabel (Sum.map id (snocWitness _ k))),
      fun G _ v c xs => ?_⟩
    let : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    let : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    rw [BoundedFormula.realize_all, ← exists_snoc_iff, not_exists]
    exact forall_congr' fun x => hsys G v c (Fin.snoc xs x)

/-- The variables of a sentence's witness systems are exactly its witnesses. -/
private def sentenceWitness (k : ℕ) : Empty ⊕ (Fin 0 ⊕ Fin k) → Fin k :=
  Sum.elim Empty.elim (Sum.elim Fin.elim0 id)

/-- For a sentence, the witness systems can be read with the witnesses as their only
variables. -/
private theorem exists_solution_relabel_sentenceWitness_iff {G : Type*} [Group G] {k : ℕ}
    (systems : List (EqIneqSystem (Empty ⊕ (Fin 0 ⊕ Fin k)) A)) (c : A → G) :
    (∃ S ∈ systems.map (EqIneqSystem.relabel (sentenceWitness k)),
        ∃ v : Fin k → G, S.IsSolution v c) ↔
      ∃ ys : Fin k → G, ∃ S ∈ systems,
        S.IsSolution (Sum.elim default (Sum.elim default ys)) c := by
  have hcomp (ys : Fin k → G) :
      ys ∘ sentenceWitness k = Sum.elim default (Sum.elim default ys) := by
    funext i
    rcases i with i | i | j
    · exact i.elim
    · exact i.elim0
    · rfl
  simp only [List.mem_map, exists_exists_and_eq_and, EqIneqSystem.isSolution_relabel, hcomp]
  exact ⟨fun ⟨S, hS, ys, h⟩ => ⟨ys, S, hS, h⟩, fun ⟨ys, S, hS, h⟩ => ⟨S, hS, ys, h⟩⟩

/-- An existential group sentence holds exactly when one system in a finite family of word
equation–inequation systems has a solution. The family depends only on the sentence, not on
the group or on the interpretation `c` of the coefficient names. -/
theorem existential_iff_solution
    {σ : Language.group[[A]].Sentence} (hσ : σ.IsExistential) :
    ∃ (k : ℕ) (systems : List (EqIneqSystem (Fin k) A)),
      ∀ (G : Type*) [Group G] (c : A → G),
        letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
        letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
        G ⊨ σ ↔ ∃ S ∈ systems, ∃ v : Fin k → G, S.IsSolution v c := by
  obtain ⟨k, systems, hsys⟩ := existential_iff_systems hσ
  refine ⟨k, systems.map (EqIneqSystem.relabel (sentenceWitness k)), fun G _ c => ?_⟩
  rw [exists_solution_relabel_sentenceWitness_iff]
  exact hsys G default c default

/-- A universal group sentence holds exactly when no system in a finite family of word
equation–inequation systems has a solution. The family depends only on the sentence, not on
the group or on the interpretation `c` of the coefficient names. -/
theorem universal_iff_no_solution
    {σ : Language.group[[A]].Sentence} (hσ : σ.IsUniversal) :
    ∃ (k : ℕ) (systems : List (EqIneqSystem (Fin k) A)),
      ∀ (G : Type*) [Group G] (c : A → G),
        letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
        letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
        G ⊨ σ ↔ ¬∃ S ∈ systems, ∃ v : Fin k → G, S.IsSolution v c := by
  obtain ⟨k, systems, hsys⟩ := universal_iff_systems hσ
  refine ⟨k, systems.map (EqIneqSystem.relabel (sentenceWitness k)), fun G _ c => ?_⟩
  rw [exists_solution_relabel_sentenceWitness_iff]
  exact hsys G default c default

/-! ### The universal commutativity sentence -/

open scoped commutatorElement

/-- The universal sentence `∀ x ∀ y, x * y = y * x` holds exactly when the single inequation
`⁅x, y⁆ ≠ 1` has no solution. -/
example {G : Type*} [Group G] (c : A → G) :
    letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    G ⊨ (Term.bdEqual (&0 * &1 : Language.group[[A]].Term (Empty ⊕ Fin 2)) (&1 * &0)).all.all ↔
      ¬∃ v : Fin 2 → G,
        (⟨[], [⁅(FreeGroup.of (Sum.inl 0) : FreeGroup (Fin 2 ⊕ A)), FreeGroup.of (Sum.inl 1)⁆]⟩ :
          EqIneqSystem (Fin 2) A).IsSolution v c := by
  let : Language.group.Structure G := TauCeti.Group.structureOfGroup G
  let : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
  simp [Sentence.Realize, Formula.Realize, EqIneqSystem.isSolution_iff, map_commutatorElement,
    commutatorElement_eq_one_iff_commute, Fin.exists_fin_succ_pi, commute_iff_eq, Fin.snoc]

/-- In `F(a, b)` the inequation `⁅x, y⁆ ≠ 1` is solved by `x = a`, `y = b`, so the universal
commutativity sentence fails there. -/
example :
    ∃ v : Fin 2 → FreeGroup (Fin 2),
      (⟨[], [⁅(FreeGroup.of (Sum.inl 0) : FreeGroup (Fin 2 ⊕ Fin 2)),
        FreeGroup.of (Sum.inl 1)⁆]⟩ : EqIneqSystem (Fin 2) (Fin 2)).IsSolution v FreeGroup.of := by
  refine ⟨FreeGroup.of, ?_⟩
  simp only [EqIneqSystem.isSolution_iff, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    List.mem_singleton, forall_eq, map_commutatorElement, EqIneqSystem.eval_of, Sum.elim_inl,
    ne_eq, commutatorElement_eq_one_iff_commute, true_and]
  exact fun h => absurd (FreeGroup.eq_of_commute_of_of h) (by decide)

end FirstOrder.Language.group
