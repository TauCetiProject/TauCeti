/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
public import TauCeti.GroupTheory.GroupAlgGeom.VarSubgroup
public import TauCeti.Logic.ForallExistsAlt
import Mathlib.GroupTheory.Commutator.Basic
import TauCeti.GroupTheory.FreeGroup.ProperPower.Basic

/-!
# Formal solutions of positive sentences

Let `S(x, y) = 1` be a system of equations over a group `G` in the variables `x₀, …, x_{k-1}` and
`y₀, …, y_{k-1}`. A *formal solution* of the positive sentence
`∀ x₀ ∃ y₀ … ∀ x_{k-1} ∃ y_{k-1} (S(x, y) = 1)` is a tuple of words `q₀, …, q_{k-1}` in the free
`G`-group `G[x₀, …, x_{k-1}]` such that `q i` involves only the coefficients and the variables
`x₀, …, x_i`, and such that `S(x, q) = 1` holds in `G[x₀, …, x_{k-1}]`. In other words, the
system has a solution in `G[x₀, …, x_{k-1}]` whose `x`-coordinates are the variables
`x₀, …, x_{k-1}` themselves and whose `y`-coordinates respect the order of the quantifiers.

A formal solution makes the sentence true in every group `H` receiving the coefficients through a
homomorphism `G →* H`: given values of the `x i` in `H`, the values of the words `q i` are
witnesses for the `y i`, and the value of `q i` depends only on `x₀, …, x_i`.
Merzljakov's theorem is the converse for a nonabelian free group `G = H` of finite rank; it is not
proved here.

## Main definitions

* `TauCeti.GroupAlgGeom.IsFormalSolution S q`: `q` is a formal solution of the sentence
  `∀ x₀ ∃ y₀ … ∀ x_{k-1} ∃ y_{k-1} (S(x, y) = 1)`.

## Main results

* `TauCeti.GroupAlgGeom.IsFormalSolution.sumElim_eval_mem_V`: the values of the words of a
  formal solution solve the system, for any values of the universally quantified variables.
* `TauCeti.GroupAlgGeom.IsFormalSolution.forallExistsAlt`: a formal solution makes the sentence
  true in every group receiving the coefficients.
* `TauCeti.GroupAlgGeom.not_forallExistsAlt_sq_freeGroup`,
  `TauCeti.GroupAlgGeom.not_isFormalSolution_sq`: the sentence `∀ x ∃ y (y² = x)` fails in a free
  group on a nonempty alphabet, and has no formal solution.
* `TauCeti.GroupAlgGeom.not_isFormalSolution_eq_later`: `∀ x₀ ∃ y₀ ∀ x₁ ∃ y₁ (y₀ = x₁)` has no
  formal solution, although `y₀ = x₁` is solvable in `G[x₀, x₁]`: the constraint on the variables
  of `q i` cannot be dropped.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §4.4, Merzljakov's theorem, Corollary 9 and Definition 13.
* G. S. Makanin, *Decidability of the universal and positive theories of a free group*,
  Math. USSR Izv. 25 (1985), §4, Lemma 5.
-/

public section

namespace TauCeti.GroupAlgGeom

open Monoid.Coprod FreeGroup

variable {G H : Type*} [Group G] [Group H]

/-! ### Formal solutions -/

variable {k : ℕ}

/-- A *formal solution* of the positive sentence `∀ x₀ ∃ y₀ … ∀ x_{k-1} ∃ y_{k-1} (S(x, y) = 1)`,
for a system of equations `S` over `G` in the variables `x i = Sum.inl i` and `y i = Sum.inr i`:
words `q i` in the free `G`-group on `x₀, …, x_{k-1}` such that `q i` involves only the
coefficients and the variables `x j` with `j ≤ i`, and such that substituting `q i` for `y i`
makes every equation of `S` trivial. -/
@[mk_iff]
structure IsFormalSolution (S : Set (GX G (Fin k ⊕ Fin k))) (q : Fin k → GX G (Fin k)) : Prop where
  /-- The `i`-th word involves only the coefficients and the variables `x j` with `j ≤ i`. -/
  mem_varSubgroup (i : Fin k) : q i ∈ GX.varSubgroup G (Set.Iic i)
  /-- Substituting the words for the variables `y i` solves the system in the free `G`-group on
  the variables `x i`. -/
  sumElim_mem_V : Sum.elim (fun i => inr (of i)) q ∈ V (inl : G →* GX G (Fin k)) S

namespace IsFormalSolution

variable {S T : Set (GX G (Fin k ⊕ Fin k))} {q : Fin k → GX G (Fin k)}

/-- Substituting the words of a formal solution for the variables `y i` makes each equation of
the system trivial in the free `G`-group on the variables `x i`. -/
theorem eval_eq_one (h : IsFormalSolution S q) {s : GX G (Fin k ⊕ Fin k)} (hs : s ∈ S) :
    eval inl (Sum.elim (fun i => inr (of i)) q) s = 1 :=
  mem_V.1 h.sumElim_mem_V s hs

/-- A formal solution of a system is a formal solution of each of its subsystems. -/
theorem anti (h : IsFormalSolution T q) (hST : S ⊆ T) : IsFormalSolution S q :=
  ⟨h.mem_varSubgroup, V_antitone _ hST h.sumElim_mem_V⟩

/-- The value of the `i`-th word of a formal solution depends only on the values of
`x₀, …, x_i`. -/
theorem eval_eq_eval (h : IsFormalSolution S q) (ι : G →* H) {i : Fin k} {x x' : Fin k → H}
    (hx : ∀ j ≤ i, x j = x' j) : eval ι x (q i) = eval ι x' (q i) :=
  GX.eval_eq_eval_of_mem_varSubgroup (h.mem_varSubgroup i) ι hx

/-- Specialising a formal solution: in a group `H` receiving the coefficients, any values `x` of
the universally quantified variables together with the values at `x` of the words of a formal
solution solve the system. -/
theorem sumElim_eval_mem_V (h : IsFormalSolution S q) (ι : G →* H) (x : Fin k → H) :
    Sum.elim x (fun i => eval ι x (q i)) ∈ V ι S := by
  refine mem_V.2 fun s hs => ?_
  have hw : wordMap ι (Sum.elim (fun i => inr (of i)) q) x = Sum.elim x fun i => eval ι x (q i) :=
    funext fun j => by cases j <;> simp
  rw [← hw, ← eval_comp_eval, MonoidHom.comp_apply, h.eval_eq_one hs, _root_.map_one]

/-- A formal solution makes the sentence `∀ x₀ ∃ y₀ … ∀ x_{k-1} ∃ y_{k-1} (S(x, y) = 1)` true in
every group `H` receiving the coefficients through a homomorphism `ι : G →* H`. -/
theorem forallExistsAlt (h : IsFormalSolution S q) (ι : G →* H) :
    ForallExistsAlt k fun x y : Fin k → H => Sum.elim x y ∈ V ι S :=
  forallExistsAlt_of_skolem (fun x i => eval ι x (q i)) (fun _ _ _ => h.eval_eq_eval ι)
    (h.sumElim_eval_mem_V ι)

end IsFormalSolution

variable {S T : Set (GX G (Fin k ⊕ Fin k))} {q : Fin k → GX G (Fin k)}

/-- A tuple of words is a formal solution of a union of two systems exactly when it is a formal
solution of both. -/
@[simp]
theorem isFormalSolution_union :
    IsFormalSolution (S ∪ T) q ↔ IsFormalSolution S q ∧ IsFormalSolution T q := by
  simp only [isFormalSolution_iff, V_union, Set.mem_inter_iff]
  tauto

/-- A formal solution of the empty system is a tuple of words whose `i`-th word involves only the
coefficients and the variables `x j` with `j ≤ i`. -/
@[simp]
theorem isFormalSolution_empty :
    IsFormalSolution (∅ : Set (GX G (Fin k ⊕ Fin k))) q ↔
      ∀ i, q i ∈ GX.varSubgroup G (Set.Iic i) := by
  simp [isFormalSolution_iff]

/-- A system and the normal subgroup it generates have the same formal solutions. -/
@[simp]
theorem isFormalSolution_normalClosure :
    IsFormalSolution (Subgroup.normalClosure S : Set (GX G (Fin k ⊕ Fin k))) q ↔
      IsFormalSolution S q := by
  simp [isFormalSolution_iff]

/-! ### Examples -/

section Examples

open scoped commutatorElement

/-- The sentence `∀ x ∃ y (y = x a)` has the formal solution `q(x) = x a`. -/
example (a : G) :
    IsFormalSolution (k := 1) {inr (of (Sum.inr 0)) * (inr (of (Sum.inl 0)) * inl a)⁻¹}
      ![inr (of 0) * inl a] := by
  refine ⟨fun i => ?_, by simp⟩
  obtain rfl := Subsingleton.elim i 0
  exact mul_mem (GX.inr_of_mem_varSubgroup (by simp)) (GX.inl_mem_varSubgroup _ a)

/-- The sentence `∀ x ∃ y ([x, y] = 1)` has the formal solution `q(x) = x`. -/
example :
    IsFormalSolution (G := G) (k := 1)
      {⁅(inr (of (Sum.inl 0)) : GX G (Fin 1 ⊕ Fin 1)), inr (of (Sum.inr 0))⁆} ![inr (of 0)] := by
  refine ⟨fun i => ?_, by simp [map_commutatorElement]⟩
  obtain rfl := Subsingleton.elim i 0
  exact GX.inr_of_mem_varSubgroup (by simp)

/-- The sentence `∀ x ∃ y ([x, y] = 1)` also has the formal solution `q(x) = 1`. -/
example :
    IsFormalSolution (G := G) (k := 1)
      {⁅(inr (of (Sum.inl 0)) : GX G (Fin 1 ⊕ Fin 1)), inr (of (Sum.inr 0))⁆} ![1] := by
  refine ⟨fun i => ?_, by simp [map_commutatorElement]⟩
  obtain rfl := Subsingleton.elim i 0
  exact one_mem _

/-- With no quantifiers and the trivial equation, the empty tuple is a formal solution. -/
example (q : Fin 0 → GX G (Fin 0)) : IsFormalSolution {1} q :=
  ⟨fun i => i.elim0, by simp⟩

/-- With no quantifiers, a nontrivial coefficient equation `g = 1` has no formal solution. -/
example {g : G} (hg : g ≠ 1) (q : Fin 0 → GX G (Fin 0)) : ¬IsFormalSolution {inl g} q :=
  fun h => by simpa [hg] using h.forallExistsAlt (MonoidHom.id G)

/-- The sentence `∀ x₀ ∃ y₀ ∀ x₁ ∃ y₁ (y₀ = x₀ ∧ y₁ = x₁ x₀)` has the formal solution `q₀ = x₀`,
`q₁ = x₁ x₀`. -/
example :
    IsFormalSolution (G := G) (k := 2)
      {inr (of (Sum.inr 0)) * (inr (of (Sum.inl 0)))⁻¹,
        inr (of (Sum.inr 1)) * (inr (of (Sum.inl 1)) * inr (of (Sum.inl 0)))⁻¹}
      ![inr (of 0), inr (of 1) * inr (of 0)] := by
  refine ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, by simp⟩
  · exact GX.inr_of_mem_varSubgroup (by simp)
  · exact mul_mem (GX.inr_of_mem_varSubgroup (by simp)) (GX.inr_of_mem_varSubgroup (by simp))

/-- The sentence `∀ x ∃ y (y² = x)` is false in a free group on a nonempty alphabet, whatever
the homomorphism receiving the coefficients. -/
theorem not_forallExistsAlt_sq_freeGroup {A : Type*} [Nonempty A] (ι : G →* FreeGroup A) :
    ¬ForallExistsAlt 1 fun x y : Fin 1 → FreeGroup A =>
      Sum.elim x y ∈ V ι {inr (of (Sum.inr 0)) ^ 2 * (inr (of (Sum.inl 0)))⁻¹} := fun h => by
  obtain ⟨a⟩ := ‹Nonempty A›
  have hsq : ∀ x : FreeGroup A, ∃ y, y ^ 2 = x := by
    simpa [forallExistsAlt_one, mul_inv_eq_one] using h
  obtain ⟨y, hy⟩ := hsq (of a)
  exact not_isProperPower_of a (Group.isProperPower_iff.2 ⟨y, 2, le_rfl, hy.symm⟩)

/-- The sentence `∀ x ∃ y (y² = x)` has no formal solution over any group of coefficients. -/
theorem not_isFormalSolution_sq (q : Fin 1 → GX G (Fin 1)) :
    ¬IsFormalSolution {inr (of (Sum.inr 0)) ^ 2 * (inr (of (Sum.inl 0)))⁻¹} q := fun h =>
  not_forallExistsAlt_sq_freeGroup (1 : G →* FreeGroup Unit) (h.forallExistsAlt _)

/-- The equation `y₀ = x₁` is solved in the free `G`-group on `x₀`, `x₁` by `y₀ = x₁`, a word
involving a variable quantified after `y₀`. -/
example :
    Sum.elim (fun i => inr (of i)) ![inr (of 1), 1] ∈
      V (inl : G →* GX G (Fin 2)) {inr (of (Sum.inr 0)) * (inr (of (Sum.inl 1)))⁻¹} := by
  simp

/-- The sentence `∀ x₀ ∃ y₀ ∀ x₁ ∃ y₁ (y₀ = x₁)` has no formal solution, although the equation
`y₀ = x₁` is solvable in the free `G`-group on `x₀`, `x₁`: the words of a formal solution must
respect the order of the quantifiers. -/
theorem not_isFormalSolution_eq_later (q : Fin 2 → GX G (Fin 2)) :
    ¬IsFormalSolution {inr (of (Sum.inr 0)) * (inr (of (Sum.inl 1)))⁻¹} q := fun h => by
  obtain ⟨a, ha⟩ : ∃ a : ℤ, ∀ b : ℤ, a = b := by
    simpa [forallExistsAlt_succ, mul_inv_eq_one] using
      h.forallExistsAlt (1 : G →* Multiplicative ℤ)
  have := ha (a + 1)
  omega

end Examples

end TauCeti.GroupAlgGeom
