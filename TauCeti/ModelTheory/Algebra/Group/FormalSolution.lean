/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.EqIneqSystem.Basic
public import TauCeti.GroupTheory.GroupAlgGeom.FormalSolution
public import TauCeti.ModelTheory.Algebra.Group.Basic

/-!
# Sentences true in a free group and formal solutions

Let `G` be a nonabelian free group, for instance the free group `F(A)` on an alphabet with at
least two letters, and let `σ` be a sentence of the group language with coefficients `A`,
interpreted in `G` by a map `c : A → G`, that is equivalent in `G` to
`∀ x₀ ∃ y₀ … ∀ x_{k-1} ∃ y_{k-1} (w = 1)` for a single word `w`. Every positive sentence has such
a normal form when `c` takes two letters to non-commuting elements
(`FirstOrder.Language.group.exists_word_realize_sentence_iff_forallExistsAlt`). Then `σ` is true
in `G` exactly when the equation `w = 1` has a formal solution: words `q i` in
`G[x₀, …, x_{k-1}]` that involve only the coefficients and `x₀, …, x_i`, with `w(x, q) = 1`.
One direction is specialisation of the formal solution, the other is Merzljakov's theorem.

## Main results

* `FirstOrder.Language.group.realize_iff_exists_isFormalSolution`: a sentence with a normal form
  `∀ x₀ ∃ y₀ … (w = 1)` in a nonabelian free group `G` is true in `G` exactly when `w = 1` has a
  formal solution over `G`.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §4.4, Merzljakov's theorem and Corollary 9.
* G. S. Makanin, *Decidability of the universal and positive theories of a free group*,
  Math. USSR Izv. 25 (1985), §4, Lemma 5, and §5, Theorem 2.
-/

public section

namespace FirstOrder.Language.group

open FirstOrder TauCeti TauCeti.Group TauCeti.GroupAlgGeom

variable {A : Type*}

attribute [local instance] structureOfGroup

/-- Let `G` be a nonabelian free group, `c : A → G` an interpretation of the coefficients, and
`σ` a sentence of the group language with coefficients `A` that is equivalent in `G` to
`∀ x₀ ∃ y₀ … ∀ x_{k-1} ∃ y_{k-1} (w = 1)` for a word `w` in the variables `x i`, `y i` and the
letters of `A`. Then `σ` is true in `G` exactly when the equation `w = 1` over `G` has a formal
solution in `G[x₀, …, x_{k-1}]`.

For a positive sentence `σ` and a map `c` sending two letters to non-commuting elements, a word `w`
with the hypothesis `hw` is provided by `exists_word_realize_sentence_iff_forallExistsAlt` applied
to `G`. -/
theorem realize_iff_exists_isFormalSolution {G : Type*} [Group G] [IsFreeGroup G]
    (hG : ¬IsMulCommutative G) (c : A → G) {σ : Language.group[[A]].Sentence} {k : ℕ}
    {w : FreeGroup ((Fin k ⊕ Fin k) ⊕ A)} (hw : letI := Language.constantsOn.structure c; G ⊨ σ ↔
      ForallExistsAlt k fun x y : Fin k → G => FreeGroup.lift (Sum.elim (Sum.elim x y) c) w = 1) :
    letI := Language.constantsOn.structure c
    G ⊨ σ ↔ ∃ q : Fin k → GX G (Fin k),
      IsFormalSolution {EqIneqSystem.toGX (Fin k ⊕ Fin k) c w} q := by
  rw [hw, exists_isFormalSolution_iff_forallExistsAlt_of_finite hG (Set.finite_singleton _)]
  simp [mem_V, EqIneqSystem.eval_eq_lift]

/-! ### Checks -/

section Checks

/-- The sentence `∀ x ∃ y (y = x a)` is true in `F(A)`, read off from the formal solution
`q(x) = x a` of the equation `y (x a)⁻¹ = 1` of its normal form. -/
example [Nontrivial A] (a : A) :
    letI := Language.constantsOn.structure (FreeGroup.of : A → FreeGroup A)
    FreeGroup A ⊨ ∀' ∃' ((&1 : Language.group[[A]].Term (Empty ⊕ Fin 2)) =' (&0 *
      (Language.group.con a).term)) := by
  let := Language.constantsOn.structure (FreeGroup.of : A → FreeGroup A)
  rw [realize_iff_exists_isFormalSolution
    (FreeGroup.isMulCommutative_iff_subsingleton.not.2 (not_subsingleton A)) FreeGroup.of
    (k := 1) (w := .of (.inl (.inr 0)) * (.of (.inl (.inl 0)) * .of (.inr a))⁻¹) ?_]
  · refine ⟨![.inr (.of 0) * .inl (.of a)], Fin.forall_fin_one.2 ?_, by simp⟩
    exact mul_mem (GX.inr_of_mem_varSubgroup (by simp)) (GX.inl_mem_varSubgroup _ _)
  · simp [forallExistsAlt_one, Sentence.Realize, Formula.Realize, Fin.snoc, ← mul_assoc,
      mul_inv_eq_iff_eq_mul]

/-- The sentence `∀ x ∃ y (y² = x)` is false in `F(A)`, read off from the absence of a formal
solution of the equation `y² x⁻¹ = 1` of its normal form (`not_isFormalSolution_sq`). -/
example [Nontrivial A] :
    letI := Language.constantsOn.structure (FreeGroup.of : A → FreeGroup A)
    ¬FreeGroup A ⊨ ∀' ∃' (((&1 : Language.group[[A]].Term (Empty ⊕ Fin 2)) * &1) =' &0) := by
  let := Language.constantsOn.structure (FreeGroup.of : A → FreeGroup A)
  rw [realize_iff_exists_isFormalSolution
    (FreeGroup.isMulCommutative_iff_subsingleton.not.2 (not_subsingleton A)) FreeGroup.of
    (k := 1) (w := .of (.inl (.inr 0)) ^ 2 * (.of (.inl (.inl 0)))⁻¹) ?_]
  · exact fun ⟨q, hq⟩ => not_isFormalSolution_sq q (by simpa using hq)
  · simp [forallExistsAlt_one, Sentence.Realize, Formula.Realize, Fin.snoc, sq, mul_inv_eq_one]

/-- The sentence `∀ x₀ ∃ y₀ ∀ x₁ ∃ y₁ (y₀ = x₁)` is false in `F(A)`, read off from the absence of
a formal solution of the equation `y₀ x₁⁻¹ = 1` of its normal form
(`not_isFormalSolution_eq_later`): the equation is solved by `y₀ = x₁` in `F(A)[x₀, x₁]`, but the
word substituted for `y₀` may involve only the coefficients and `x₀`. -/
example [Nontrivial A] :
    letI := Language.constantsOn.structure (FreeGroup.of : A → FreeGroup A)
    ¬FreeGroup A ⊨ ∀' ∃' ∀' ∃' ((&1 : Language.group[[A]].Term (Empty ⊕ Fin 4)) =' &2) := by
  let := Language.constantsOn.structure (FreeGroup.of : A → FreeGroup A)
  rw [realize_iff_exists_isFormalSolution
    (FreeGroup.isMulCommutative_iff_subsingleton.not.2 (not_subsingleton A)) FreeGroup.of
    (k := 2) (w := .of (.inl (.inr 0)) * (.of (.inl (.inl 1)))⁻¹) ?_]
  · exact fun ⟨q, hq⟩ => not_isFormalSolution_eq_later q (by simpa using hq)
  · simp [forallExistsAlt_succ, Sentence.Realize, Formula.Realize, Fin.snoc, mul_inv_eq_one]

end Checks

end FirstOrder.Language.group
