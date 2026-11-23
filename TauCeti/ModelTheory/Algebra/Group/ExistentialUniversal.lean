/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Algebra.Group.QuantifierFree
public import TauCeti.ModelTheory.Algebra.Group.SystemFormula

/-!
# Existential and universal group formulas as solution statements

An existential formula `∃ y₁ … ∃ y_k, φ` in the group language with named coefficients, with
`φ` quantifier-free, holds exactly when one of its finitely many systems of word equations and
inequations `FirstOrder.Language.BoundedFormula.eqIneqSystems` has a solution, the witnesses
`y₁, …, y_k` being variables of the systems. Dually, a universal formula `∀ y₁ … ∀ y_k, φ` holds
exactly when none of the finitely many systems of its negation has a solution. The systems depend
only on the formula, not on the group or on the interpretation of the coefficients.

For sentences this identifies the existential and universal theories of a group with
coefficients with solvability statements for finite families of equation–inequation systems.

## Main results

* `FirstOrder.Language.group.existential_iff_systems` and
  `FirstOrder.Language.group.universal_iff_systems`: the reductions for bounded formulas, the
  free variables and the values of the outer bound variables being parameters.
* `FirstOrder.Language.group.existential_iff_solution`: an existential sentence holds exactly
  when one of its systems has a solution.
* `FirstOrder.Language.group.universal_iff_no_solution`: a universal sentence holds exactly
  when no system of its negation has a solution.
* `TauCeti.EqIneqSystem.noSolutionSentence`: conversely, for a system of equations and
  inequations in `n` variables with coefficient names `A`, a universal sentence of the group
  language with coefficient names `A` saying that the system has no solution.
* `TauCeti.EqIneqSystem.exists_isSolution_of_forall_isUniversal`: if every universal sentence
  true in `H` holds in `K`, every system solvable in `K` is solvable in `H`, whatever its type of
  variables.
* `FirstOrder.Language.group.noSolutionSentence`: the same sentence without coefficients, for
  finite sets of words `E` and `I` in `n` variables: no `n`-tuple satisfies `e = 1` for `e ∈ E`
  and `i ≠ 1` for `i ∈ I`.

The reduction of existential and universal sentences to systems of equations and inequations
follows Kharlampovich and Myasnikov, *Implicit function theorem over free groups*, §2.3.
-/

public section

namespace FirstOrder.Language.group

open FirstOrder TauCeti

variable {X A : Type*} {n : ℕ}

/-- An existential group formula holds at the values `xs` of its bound variables exactly when
some assignment `w` of the numbered variables that extends `xs` solves one of its finitely many
systems `φ.eqIneqSystems`: the witnesses of the existential quantifiers are the further values of
`w`. The systems depend only on the formula, so the equivalence holds uniformly in every group
and every interpretation `c` of the coefficient names. -/
theorem existential_iff_systems {φ : Language.group[[A]].BoundedFormula X n}
    (hφ : φ.IsExistential) {G : Type*} [Group G] (v : X → G) (c : A → G) (xs : Fin n → G) :
    letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    φ.Realize v xs ↔
      ∃ w : ℕ → G, (∀ i : Fin n, w i = xs i) ∧
        ∃ S ∈ φ.eqIneqSystems, S.IsSolution (Sum.elim v w) c := by
  let : Language.group.Structure G := TauCeti.Group.structureOfGroup G
  let : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
  induction hφ with
  | @of_isQF _ φ h =>
    refine ⟨fun hr => ?_, fun ⟨w, hw, hS⟩ => funext hw ▸ (quantifierFree_iff_systems h v c w).2 hS⟩
    -- Extend `xs` to an assignment of all numbered variables.
    obtain ⟨w, hw⟩ : ∃ w : ℕ → G, ∀ i : Fin _, w i = xs i :=
      ⟨_, Fin.val_injective.extend_apply xs 1⟩
    exact ⟨w, hw, (quantifierFree_iff_systems h v c w).1 (funext hw ▸ hr)⟩
  | ex _ ih =>
    simp [ih, Fin.forall_fin_succ']

/-- A universal group formula holds at the values `xs` of its bound variables exactly when no
assignment `w` of the numbered variables that extends `xs` solves one of the finitely many
systems `φ.not.eqIneqSystems` of its negation. The systems depend only on the formula, so the
equivalence holds uniformly in every group and every interpretation `c` of the coefficient
names. -/
theorem universal_iff_systems {φ : Language.group[[A]].BoundedFormula X n}
    (hφ : φ.IsUniversal) {G : Type*} [Group G] (v : X → G) (c : A → G) (xs : Fin n → G) :
    letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    φ.Realize v xs ↔
      ¬∃ w : ℕ → G, (∀ i : Fin n, w i = xs i) ∧
        ∃ S ∈ φ.not.eqIneqSystems, S.IsSolution (Sum.elim v w) c := by
  let : Language.group.Structure G := TauCeti.Group.structureOfGroup G
  let : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
  induction hφ with
  | @of_isQF _ φ h =>
    rw [← not_iff_not, not_not, ← BoundedFormula.realize_not]
    exact existential_iff_systems h.not.isExistential v c xs
  | all _ ih =>
    simp only [BoundedFormula.realize_all, ih, BoundedFormula.eqIneqSystems_not_all, ← not_exists]
    exact not_congr (by simp [Fin.forall_fin_succ'])

/-- For a sentence, an assignment of the numbered variables solving one of the systems `L` is the
same as an assignment of all the variables `Empty ⊕ ℕ` solving one of them. -/
private theorem exists_isSolution_sumElim_default_iff {G : Type*} [Group G]
    (L : List (EqIneqSystem (Empty ⊕ ℕ) A)) (c : A → G) :
    (∃ w : ℕ → G, (∀ i : Fin 0, w i = (default : Fin 0 → G) i) ∧
        ∃ S ∈ L, S.IsSolution (Sum.elim default w) c) ↔
      ∃ S ∈ L, ∃ v : Empty ⊕ ℕ → G, S.IsSolution v c := by
  refine ⟨fun ⟨_, _, S, hS, h⟩ => ⟨S, hS, _, h⟩,
    fun ⟨S, hS, v, h⟩ => ⟨v ∘ Sum.inr, nofun, S, hS, ?_⟩⟩
  rwa [Subsingleton.elim default (v ∘ Sum.inl), Sum.elim_comp_inl_inr]

/-- An existential group sentence holds exactly when one of its finitely many word
equation–inequation systems `σ.eqIneqSystems` has a solution. The systems depend only on the
sentence, not on the group or on the interpretation `c` of the coefficient names. -/
theorem existential_iff_solution
    {σ : Language.group[[A]].Sentence} (hσ : σ.IsExistential) {G : Type*} [Group G] (c : A → G) :
    letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    G ⊨ σ ↔ ∃ S ∈ σ.eqIneqSystems, ∃ v : Empty ⊕ ℕ → G, S.IsSolution v c := by
  let : Language.group.Structure G := TauCeti.Group.structureOfGroup G
  let : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
  rw [Sentence.Realize, Formula.Realize, existential_iff_systems hσ default c default,
    exists_isSolution_sumElim_default_iff]

/-- A universal group sentence holds exactly when none of the finitely many word
equation–inequation systems `σ.not.eqIneqSystems` of its negation has a solution. The systems
depend only on the sentence, not on the group or on the interpretation `c` of the coefficient
names. -/
theorem universal_iff_no_solution
    {σ : Language.group[[A]].Sentence} (hσ : σ.IsUniversal) {G : Type*} [Group G] (c : A → G) :
    letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    G ⊨ σ ↔ ¬∃ S ∈ σ.not.eqIneqSystems, ∃ v : Empty ⊕ ℕ → G, S.IsSolution v c := by
  let : Language.group.Structure G := TauCeti.Group.structureOfGroup G
  let : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
  rw [Sentence.Realize, Formula.Realize, universal_iff_systems hσ default c default,
    exists_isSolution_sumElim_default_iff]

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

/-! ### Universal sentences forbidding solutions of systems with coefficients -/

namespace TauCeti.EqIneqSystem

open FirstOrder FirstOrder.Language

variable {A : Type*} {n : ℕ}

/-- The universal sentence of the group language with coefficient names `A` saying that the
system `S` of equations and inequations in the variables `Fin n` has no solution: the negation
of the formula of `S`, with its variables universally quantified. -/
noncomputable def noSolutionSentence (S : EqIneqSystem (Fin n) A) : Language.group[[A]].Sentence :=
  (BoundedFormula.relabel Sum.inr S.toFormula).not.alls

/-- The sentence `S.noSolutionSentence` is the negation of the formula of `S`, with its variables
universally quantified. -/
theorem noSolutionSentence_def (S : EqIneqSystem (Fin n) A) :
    S.noSolutionSentence = (BoundedFormula.relabel Sum.inr S.toFormula).not.alls := (rfl)

/-- The sentence `S.noSolutionSentence` is universal. -/
theorem isUniversal_noSolutionSentence (S : EqIneqSystem (Fin n) A) :
    S.noSolutionSentence.IsUniversal :=
  (S.isQF_toFormula.relabel Sum.inr).not.isUniversal.alls

/-- A group, with the coefficient names `A` read through `c`, satisfies `S.noSolutionSentence`
exactly when the system `S` has no solution in it. -/
@[simp]
theorem realize_noSolutionSentence {G : Type*} [Group G] (S : EqIneqSystem (Fin n) A) (c : A → G) :
    letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    G ⊨ S.noSolutionSentence ↔ ¬∃ v : Fin n → G, S.IsSolution v c := by
  let : Language.group.Structure G := TauCeti.Group.structureOfGroup G
  let : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
  simp [noSolutionSentence_def, Sentence.Realize, Formula.realize_relabel_sumInr,
    -BoundedFormula.realize_relabel]

/-- If every universal sentence of the group language with coefficient names `A` that holds in `H`
also holds in `K`, then every system of equations and inequations with a solution in `K` has a
solution in `H`. -/
theorem exists_isSolution_of_forall_isUniversal {X K H : Type*} [Group K] [Group H] {cK : A → K}
    {cH : A → H} (h : letI : Language.group.Structure K := TauCeti.Group.structureOfGroup K
      letI : (Language.constantsOn A).Structure K := Language.constantsOn.structure cK
      letI : Language.group.Structure H := TauCeti.Group.structureOfGroup H
      letI : (Language.constantsOn A).Structure H := Language.constantsOn.structure cH
      ∀ σ : Language.group[[A]].Sentence, σ.IsUniversal → H ⊨ σ → K ⊨ σ)
    {S : EqIneqSystem X A} (hS : ∃ v : X → K, S.IsSolution v cK) :
    ∃ v : X → H, S.IsSolution v cH := by
  classical
  obtain ⟨v, hv⟩ := hS
  -- Only the finitely many variables `T` occurring in the words of `S` matter: relabel them by
  -- `Fin n`, sending all other variables to one further index.
  let T : Finset X :=
    ((S.eqs ++ S.ineqs).flatMap fun w => w.toWord.filterMap (·.1.getLeft?)).toFinset
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (Option T)
  let g : X → Fin n := fun x => e (if hx : x ∈ T then some ⟨x, hx⟩ else none)
  have hK : (S.relabel g).IsSolution (fun i => (e.symm i).elim 1 fun t => v t) cK := by
    rw [isSolution_relabel]
    rw [← ofWords_toWord S] at hv ⊢
    refine (isSolution_ofWords_congr cK fun w hw x b hx => ?_).1 hv
    have hxT : x ∈ T := by
      simp only [List.mem_append, List.mem_map] at hw
      simp only [T, List.mem_toFinset, List.mem_flatMap, List.mem_append, List.mem_filterMap]
      obtain ⟨w', hw', rfl⟩ | ⟨w', hw', rfl⟩ := hw
      exacts [⟨w', .inl hw', _, hx, rfl⟩, ⟨w', .inr hw', _, hx, rfl⟩]
    simp [g, hxT]
  by_contra hH
  refine (realize_noSolutionSentence _ cK).1 (h _ (S.relabel g).isUniversal_noSolutionSentence
    ((realize_noSolutionSentence _ cH).2 fun ⟨u, hu⟩ => hH ⟨u ∘ g, ?_⟩)) ⟨_, hK⟩
  rwa [isSolution_relabel] at hu

end TauCeti.EqIneqSystem

/-! ### Universal sentences forbidding solutions of systems without coefficients -/

namespace FirstOrder.Language.group

open FirstOrder TauCeti

variable {n : ℕ}

/-- The universal sentence of the group language without coefficients saying that no `n`-tuple
`x` of group elements satisfies the equations `e(x) = 1` for `e ∈ E` and the inequations
`i(x) ≠ 1` for `i ∈ I`: the sentence `EqIneqSystem.noSolutionSentence` of this system with no
coefficient names, read in the group language without constants. -/
noncomputable def noSolutionSentence (E I : Finset (FreeGroup (Fin n))) :
    Language.group.Sentence :=
  (LEquiv.addEmptyConstants Language.group Empty).invLHom.onSentence
    (EqIneqSystem.noSolutionSentence
      ⟨E.toList.map (FreeGroup.map Sum.inl), I.toList.map (FreeGroup.map Sum.inl)⟩)

/-- The sentence `noSolutionSentence E I` is the sentence `EqIneqSystem.noSolutionSentence` of
the system with equations `E` and inequations `I` and no coefficient names, read in the group
language without constants. -/
theorem noSolutionSentence_def (E I : Finset (FreeGroup (Fin n))) :
    noSolutionSentence E I = (LEquiv.addEmptyConstants Language.group Empty).invLHom.onSentence
      (EqIneqSystem.noSolutionSentence
        ⟨E.toList.map (FreeGroup.map Sum.inl), I.toList.map (FreeGroup.map Sum.inl)⟩) := (rfl)

/-- The sentence `noSolutionSentence E I` is universal. -/
theorem isUniversal_noSolutionSentence (E I : Finset (FreeGroup (Fin n))) :
    (noSolutionSentence E I).IsUniversal :=
  (EqIneqSystem.isUniversal_noSolutionSentence _).onBoundedFormula _

section NoSolution

attribute [local instance] TauCeti.Group.structureOfGroup

/-- A group satisfies `noSolutionSentence E I` exactly when no tuple solves the equations `E`
and the inequations `I`. -/
@[simp] theorem realize_noSolutionSentence {G : Type*} [Group G]
    (E I : Finset (FreeGroup (Fin n))) :
    G ⊨ noSolutionSentence E I ↔
      ¬∃ x : Fin n → G, (∀ e ∈ E, FreeGroup.lift x e = 1) ∧ ∀ i ∈ I, FreeGroup.lift x i ≠ 1 := by
  let : (Language.constantsOn Empty).Structure G := Language.constantsOn.structure isEmptyElim
  have : (LEquiv.addEmptyConstants Language.group Empty).invLHom.IsExpansionOn G :=
    LHom.sumElim_isExpansionOn _ _ _
  have heval (x : Fin n → G) (w : FreeGroup (Fin n)) :
      EqIneqSystem.eval x (isEmptyElim : Empty → G) (FreeGroup.map Sum.inl w) =
        FreeGroup.lift x w := by
    rw [← MonoidHom.comp_apply, EqIneqSystem.eval_eq_lift]
    congr 1
    ext
    simp
  rw [noSolutionSentence_def, LHom.realize_onSentence, EqIneqSystem.realize_noSolutionSentence]
  simp [EqIneqSystem.isSolution_iff, heval]

/-- With a single inequation `w ≠ 1`, the sentence `noSolutionSentence E {w}` is the universal
implication `∀ x, (⋀ e ∈ E, e(x) = 1) → w(x) = 1`: a group satisfies it exactly when `w` vanishes
at every tuple at which all words of `E` vanish. -/
theorem realize_noSolutionSentence_singleton {G : Type*} [Group G]
    (E : Finset (FreeGroup (Fin n))) (w : FreeGroup (Fin n)) : G ⊨ noSolutionSentence E {w} ↔
      ∀ x : Fin n → G, (∀ e ∈ E, FreeGroup.lift x e = 1) → FreeGroup.lift x w = 1 := by
  simp

/-- A consequence `w` of the relators `E`, that is an element of their normal closure, vanishes
wherever `E` does, in every group: every group satisfies `∀ x, E(x) = 1 → w(x) = 1`. -/
theorem realize_noSolutionSentence_singleton_of_mem_normalClosure {G : Type*} [Group G]
    {E : Finset (FreeGroup (Fin n))} {w : FreeGroup (Fin n)}
    (hw : w ∈ Subgroup.normalClosure (E : Set (FreeGroup (Fin n)))) :
    G ⊨ noSolutionSentence E {w} :=
  (realize_noSolutionSentence_singleton E w).2 fun x hx =>
    Subgroup.normalClosure_le_normal (N := (FreeGroup.lift x).ker) hx hw

end NoSolution

end FirstOrder.Language.group
