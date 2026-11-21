/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coxeter.Basic

/-!
# Diagram automorphisms of a Coxeter system

A *diagram automorphism* of a Coxeter matrix `M` on an index type `B` is a permutation `e` of `B`
preserving the matrix, `M (e i) (e i') = M i i'`. The images `s (e i)` of the simple reflections
then satisfy the Coxeter relations of `M`, so by the universal property of a Coxeter system
`cs : CoxeterSystem M W` the assignment `s i ↦ s (e i)` extends to an endomorphism of `W`, and
the endomorphism built from `e⁻¹` inverts it. This file packages the result as the automorphism
`CoxeterSystem.diagramAut` of `W`. On words it acts letterwise: the word `l` is sent to the word
`l.map e`.

Diagram automorphisms are how the symmetries of a Dynkin diagram, or of an affine Dynkin diagram,
act on the corresponding Weyl group; for instance, they are what moves the bipartite Coxeter
element of a two-coloured Coxeter graph (`TauCeti/GroupTheory/Coxeter/Bipartite.lean`).

## Main definitions

* `CoxeterSystem.diagramAut`: the automorphism of `W` induced by a diagram automorphism of `M`.

## Main results

* `CoxeterSystem.diagramAut_simple`, `CoxeterSystem.diagramAut_symm_simple`: the automorphism and
  its inverse on simple reflections.
* `CoxeterSystem.diagramAut_wordProd`: the automorphism sends the element spelled by a word `l` to
  the element spelled by `l.map e`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. IV, §1, no. 3.
-/

public section

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
  (e : B ≃ B) (he : ∀ i i', M (e i) (e i') = M i i')

include he in
/-- The simple reflections permuted by a diagram automorphism satisfy the Coxeter relations. -/
private theorem isLiftable_simple_comp : M.IsLiftable (cs.simple ∘ e) := fun i i' ↦ by
  rw [Function.comp_apply, Function.comp_apply, ← he]
  exact cs.simple_mul_simple_pow (e i) (e i')

include he in
/-- The inverse of a diagram automorphism preserves the Coxeter matrix too. -/
private theorem symm_apply_symm_apply (i i' : B) : M (e.symm i) (e.symm i') = M i i' := by
  simpa using (he (e.symm i) (e.symm i')).symm

/-- **The automorphism of a Coxeter group induced by a diagram automorphism.** A permutation `e` of
the index type that preserves the Coxeter matrix, `M (e i) (e i') = M i i'`, extends to the
automorphism of `W` sending each simple reflection `s i` to `s (e i)`
(`CoxeterSystem.diagramAut_simple`). -/
noncomputable def diagramAut : W ≃* W :=
  MonoidHom.toMulEquiv (cs.lift ⟨_, cs.isLiftable_simple_comp e he⟩)
    (cs.lift ⟨_, cs.isLiftable_simple_comp e.symm (symm_apply_symm_apply e he)⟩)
    (cs.ext_simple fun i ↦ by simp) (cs.ext_simple fun i ↦ by simp)

/-- The automorphism induced by a diagram automorphism `e` sends the simple reflection `s i` to
`s (e i)`. -/
@[simp]
theorem diagramAut_simple (i : B) : cs.diagramAut e he (cs.simple i) = cs.simple (e i) := by
  simp [diagramAut]

/-- The inverse of the automorphism induced by a diagram automorphism `e` sends the simple
reflection `s i` to `s (e⁻¹ i)`. -/
@[simp]
theorem diagramAut_symm_simple (i : B) :
    (cs.diagramAut e he).symm (cs.simple i) = cs.simple (e.symm i) := by
  rw [MulEquiv.symm_apply_eq, diagramAut_simple, Equiv.apply_symm_apply]

/-- The automorphism induced by a diagram automorphism `e` acts letterwise on words: it sends the
element spelled by `l` to the element spelled by `l.map e`. -/
@[simp]
theorem diagramAut_wordProd (l : List B) :
    cs.diagramAut e he (cs.wordProd l) = cs.wordProd (l.map e) := by
  induction l with
  | nil => simp
  | cons i l ih => simp [wordProd_cons, ih]

end CoxeterSystem
