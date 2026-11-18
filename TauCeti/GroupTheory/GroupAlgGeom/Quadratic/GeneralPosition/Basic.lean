/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.CSA
public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Basic
import TauCeti.Data.List.Forall2

/-!
# Solutions in general position of standard quadratic equations

A solution of a standard quadratic equation `r₁ ⋯ r_k d = 1` is in general position when the
values of no two consecutive atoms commute (`Standard.IsGeneralPosition`).

The atoms of a standard quadratic equation are words in pairwise disjoint sets of variables, so
their values can be prescribed independently (`Standard.exists_map_eval_atoms_eq`), and the
values an atom takes are closed under conjugation (`Standard.exists_eval_eq_of_mem_atoms`):
standard equations are *separable* and their atoms have *complete spectrum* ([VAR-I], §2). Over a
CSA group a nondegenerate non-commutative solution can therefore be conjugated, atom by atom, into
a solution in general position ([VAR-I], Proposition 3). An equation of genus `0` has no
degenerate point at all, since its atoms are conjugates of nontrivial coefficients, so this
applies to all its non-commutative solutions ([VAR-I], Proposition 5).

## Main results

* `TauCeti.GroupAlgGeom.Quadratic.Standard.exists_map_eval_atoms_eq`: separability.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.exists_eval_eq_of_mem_atoms`: complete spectrum.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.exists_isGeneralPosition_of_not_isDegenerate`: over a
  CSA group, a nondegenerate non-commutative solution gives a solution in general position.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.7, Definition 5.
* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §2,
  Definitions 14–17 and Propositions 3 and 5.
-/

public section

open Monoid.Coprod
open scoped commutatorElement

namespace TauCeti.GroupAlgGeom.Quadratic.Standard

variable {G H X : Type*} [Group G] [Group H]

/-! ### Separability and complete spectrum -/

section Atoms

variable {S : Standard G X} {ι : G →* H}

/-- A point is a solution of `r₁ ⋯ r_k d = 1` exactly when the product of the values of the atoms
is the inverse of the value of `d`. -/
theorem mem_V_toWord_iff {v : X → H} :
    v ∈ V ι {S.toWord} ↔ (S.atoms.map (eval ι v)).prod * ι S.constant = 1 := by
  simp [mem_V, toWord_def, map_list_prod]

-- Values of the words `F i` can be prescribed independently when, along an injective `e`, each
-- `F i` depends only on the variables `e a` with `p a = i`.
private theorem exists_map_eval_ofFn_eq {k : ℕ} {K : Type*} {e : K → X} (he : e.Injective)
    (p : K → Fin k) {F : Fin k → GX G X}
    (hF : ∀ i (v w : X → H), (∀ a, p a = i → v (e a) = w (e a)) → eval ι v (F i) = eval ι w (F i))
    {l : List H} (h : List.Forall₂ (fun r a => ∃ v : X → H, eval ι v r = a) (List.ofFn F) l) :
    ∃ v : X → H, (List.ofFn F).map (eval ι v) = l := by
  obtain ⟨a, ha, rfl⟩ := List.forall₂_ofFn_left_iff.1 h
  choose V hV using ha
  -- The variable `e a` takes the value it has at the point chosen for the word `F (p a)`.
  refine ⟨Function.extend e (fun a => V (p a) (e a)) 1, ?_⟩
  rw [List.map_ofFn, List.ofFn_inj]
  funext i
  exact (hF i _ _ fun a ha => by rw [he.extend_apply, ha]).trans (hV i)

/-- **Separability.** The atoms of a standard quadratic equation are words in pairwise disjoint
sets of variables, so values that each atom takes at some point are taken by all the atoms at one
point. -/
theorem exists_map_eval_atoms_eq {l : List H}
    (h : List.Forall₂ (fun r a => ∃ v : X → H, eval ι v r = a) S.atoms l) :
    ∃ v : X → H, S.atoms.map (eval ι v) = l := by
  cases S with
  | orientable n hn x y inj =>
    rw [atoms_orientable] at h ⊢
    refine exists_map_eval_ofFn_eq inj (Sum.elim id id) (fun i v w hvw => ?_) h
    simp_all [Sum.forall, map_commutatorElement]
  | orientableCoeff n m hnm x y z inj c hc d hd =>
    rw [atoms_orientableCoeff, ← List.ofFn_fin_append] at h ⊢
    refine exists_map_eval_ofFn_eq inj
      (Sum.elim (Sum.elim (Fin.castAdd m) (Fin.castAdd m)) (Fin.natAdd n)) (fun i v w hvw => ?_) h
    induction i using Fin.addCases <;> simp_all [Sum.forall, map_commutatorElement]
  | nonorientable n hn x inj =>
    rw [atoms_nonorientable] at h ⊢
    refine exists_map_eval_ofFn_eq inj id (fun i v w hvw => ?_) h
    simp_all
  | nonorientableCoeff n m hn x z inj c hc d hd =>
    rw [atoms_nonorientableCoeff, ← List.ofFn_fin_append] at h ⊢
    refine exists_map_eval_ofFn_eq inj (Sum.elim (Fin.castAdd m) (Fin.natAdd n))
      (fun i v w hvw => ?_) h
    induction i using Fin.addCases <;> simp_all [Sum.forall]

/-- **Complete spectrum.** The values of an atom of a standard quadratic equation are closed under
conjugation. -/
theorem exists_eval_eq_of_mem_atoms {r : GX G X} (hr : r ∈ S.atoms) (v : X → H) {a : H}
    (ha : IsConj (eval ι v r) a) : ∃ w : X → H, eval ι w r = a := by
  obtain ⟨t, rfl⟩ := isConj_iff.1 ha
  -- For commutators and squares of variables conjugate every variable by `t`; for a conjugate
  -- `z⁻¹ c z` multiply `z` on the right by `t⁻¹`.
  cases S <;> simp only [atoms_orientable, atoms_orientableCoeff, atoms_nonorientable,
    atoms_nonorientableCoeff, List.mem_append, List.mem_ofFn] at hr
  · obtain ⟨i, rfl⟩ := hr
    exact ⟨fun u => t * v u * t⁻¹, by simp [commutatorElement_def, mul_assoc]⟩
  · obtain ⟨i, rfl⟩ | ⟨j, rfl⟩ := hr
    · exact ⟨fun u => t * v u * t⁻¹, by simp [commutatorElement_def, mul_assoc]⟩
    · exact ⟨fun u => v u * t⁻¹, by simp [mul_assoc]⟩
  · obtain ⟨i, rfl⟩ := hr
    exact ⟨fun u => t * v u * t⁻¹, by simp [sq, mul_assoc]⟩
  · obtain ⟨i, rfl⟩ | ⟨j, rfl⟩ := hr
    · exact ⟨fun u => t * v u * t⁻¹, by simp [sq, mul_assoc]⟩
    · exact ⟨fun u => v u * t⁻¹, by simp [mul_assoc]⟩

end Atoms

/-! ### Proposition 3 of [VAR-I] -/

/-- **[VAR-I], Proposition 3.** Over a CSA group, a standard quadratic equation with a
nondegenerate non-commutative solution has a solution in general position. The coefficients may be
mapped into `H` by any homomorphism `ι`. -/
theorem exists_isGeneralPosition_of_not_isDegenerate (hH : Group.IsCSA H) {S : Standard G X}
    {ι : G →* H} {v : X → H} (hv : v ∈ V ι {S.toWord}) (hd : ¬S.IsDegenerate ι v)
    (hc : ¬S.IsCommutative ι v) : ∃ w ∈ V ι {S.toWord}, S.IsGeneralPosition ι w := by
  -- Conjugate the values of the atoms, entry by entry and keeping their product, into general
  -- position, and realise the new values at one point.
  obtain ⟨l, hl, hprod, hgp⟩ := hH.exists_conj_isChain_not_commute
    (l := S.atoms.map (eval ι v)) (by simpa [isDegenerate_iff] using hd)
    ((isCommutative_iff S ι v).not.1 hc)
  obtain ⟨w, hw⟩ := exists_map_eval_atoms_eq (((List.forall₂_and_left _ _).2
    ⟨fun _ h => h, List.forall₂_map_left_iff.1 hl⟩).imp fun _ _ h =>
      exists_eval_eq_of_mem_atoms h.1 v h.2)
  exact ⟨w, by rwa [mem_V_toWord_iff, hw, hprod, ← mem_V_toWord_iff],
    by rwa [isGeneralPosition_iff, hw]⟩

/-! ### Equations of genus `0` -/

/-- A standard quadratic equation of genus `0` has no degenerate point: all its atoms are
conjugates of nontrivial coefficients. So over a CSA group every non-commutative solution of such
an equation gives a solution in general position (`exists_isGeneralPosition_of_not_isDegenerate`).
-/
theorem not_isDegenerate_of_genus_eq_zero {S : Standard G X} (hg : S.genus = 0) (v : X → G) :
    ¬S.IsDegenerate (.id G) v := by
  cases S <;> simp only [genus_orientable, genus_orientableCoeff, genus_nonorientable,
    genus_nonorientableCoeff] at hg <;> subst hg <;>
    simp_all [isDegenerate_iff, List.mem_ofFn, mul_assoc, inv_mul_eq_one]

end TauCeti.GroupAlgGeom.Quadratic.Standard
