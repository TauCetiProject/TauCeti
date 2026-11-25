/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Basic

/-!
# Diagram automorphisms of a Coxeter system

A *diagram automorphism* of a Coxeter matrix `M` on an index type `B` is a permutation `e` of `B`
preserving the matrix, `M (e i) (e i') = M i i'`. The images `s (e i)` of the simple reflections
then satisfy the Coxeter relations of `M`, so the assignment `s i ↦ s (e i)` extends to the
endomorphism `CoxeterSystem.parabolicHom cs cs` of `W` along `e`, and the endomorphism built from
`e⁻¹` inverts it. This file packages the result as the automorphism `CoxeterSystem.diagramAut` of
`W`. On words it acts letterwise: the word `l` is sent to the word `l.map e`. The construction is
functorial: the identity permutation gives the identity, inverses give inverses and composites give
composites.

Diagram automorphisms are how the symmetries of a Dynkin diagram, or of an affine Dynkin diagram,
act on the corresponding Weyl group; for instance, they are what moves the bipartite Coxeter
element of a two-coloured Coxeter graph (`TauCeti/GroupTheory/Coxeter/Bipartite.lean`).

## Main definitions

* `CoxeterSystem.diagramAut`: the automorphism of `W` induced by a diagram automorphism of `M`.

## Main results

* `CoxeterSystem.diagramAut_simple`, `CoxeterSystem.diagramAut_symm_simple`: the automorphism and
  its inverse on simple reflections.
* `CoxeterSystem.diagramAut_wordProd`, `CoxeterSystem.diagramAut_symm_wordProd`: the automorphism
  sends the element spelled by a word `l` to the element spelled by `l.map e`, and its inverse
  sends it to the element spelled by `l.map e.symm`.
* `CoxeterSystem.diagramAut_refl`, `CoxeterSystem.diagramAut_symm`,
  `CoxeterSystem.diagramAut_trans`: functoriality in the diagram automorphism.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. IV, §1, no. 3.
-/

public section

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
  (e : B ≃ B) (he : ∀ i i', M (e i) (e i') = M i i')

include he in
/-- The inverse of a diagram automorphism preserves the Coxeter matrix too. -/
private theorem symm_apply_symm_apply (i i' : B) : M (e.symm i) (e.symm i') = M i i' := by
  simpa using (he (e.symm i) (e.symm i')).symm

/-- **The automorphism of a Coxeter group induced by a diagram automorphism.** A permutation `e` of
the index type that preserves the Coxeter matrix, `M (e i) (e i') = M i i'`, extends to the
automorphism of `W` sending each simple reflection `s i` to `s (e i)`
(`CoxeterSystem.diagramAut_simple`). It is `CoxeterSystem.parabolicHom` along `e`, inverted by
`CoxeterSystem.parabolicHom` along `e.symm`. -/
noncomputable def diagramAut : W ≃* W :=
  MonoidHom.toMulEquiv (cs.parabolicHom cs fun i i' ↦ (he i i').symm)
    (cs.parabolicHom cs fun i i' ↦ (symm_apply_symm_apply e he i i').symm)
    (cs.ext_simple fun i ↦ by simp) (cs.ext_simple fun i ↦ by simp)

/-- The automorphism induced by a diagram automorphism `e` sends the simple reflection `s i` to
`s (e i)`. -/
@[simp]
theorem diagramAut_simple (i : B) : cs.diagramAut e he (cs.simple i) = cs.simple (e i) :=
  cs.parabolicHom_simple _ i

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
    cs.diagramAut e he (cs.wordProd l) = cs.wordProd (l.map e) :=
  cs.parabolicHom_wordProd _ l

/-- The inverse of the automorphism induced by a diagram automorphism `e` acts letterwise on words:
it sends the element spelled by `l` to the element spelled by `l.map e.symm`. -/
@[simp]
theorem diagramAut_symm_wordProd (l : List B) :
    (cs.diagramAut e he).symm (cs.wordProd l) = cs.wordProd (l.map e.symm) := by
  rw [MulEquiv.symm_apply_eq, diagramAut_wordProd, List.map_map, Equiv.self_comp_symm,
    List.map_id]

/-- The identity permutation induces the identity automorphism. -/
@[simp]
theorem diagramAut_refl : cs.diagramAut (Equiv.refl B) (fun _ _ ↦ rfl) = MulEquiv.refl W :=
  MulEquiv.toMonoidHom_injective (cs.ext_simple fun i ↦ cs.diagramAut_simple _ _ i)

/-- The inverse of the automorphism induced by `e` is the automorphism induced by `e.symm`. -/
theorem diagramAut_symm (he' : ∀ i i', M (e.symm i) (e.symm i') = M i i') :
    (cs.diagramAut e he).symm = cs.diagramAut e.symm he' :=
  MulEquiv.toMonoidHom_injective (cs.ext_simple fun i ↦ by simp)

/-- **Diagram automorphisms compose**: applying the automorphism induced by `e` and then the one
induced by `e'` is the automorphism induced by `e.trans e'`. -/
theorem diagramAut_trans (e' : B ≃ B) (he' : ∀ i i', M (e' i) (e' i') = M i i')
    (hee' : ∀ i i', M ((e.trans e') i) ((e.trans e') i') = M i i') :
    (cs.diagramAut e he).trans (cs.diagramAut e' he') = cs.diagramAut (e.trans e') hee' :=
  MulEquiv.toMonoidHom_injective (cs.ext_simple fun i ↦ by simp)

/-- Applying the automorphisms induced by `e` and then by `e'` is applying the automorphism induced
by `e.trans e'`. -/
theorem diagramAut_apply_diagramAut (e' : B ≃ B) (he' : ∀ i i', M (e' i) (e' i') = M i i')
    (hee' : ∀ i i', M ((e.trans e') i) ((e.trans e') i') = M i i') (w : W) :
    cs.diagramAut e' he' (cs.diagramAut e he w) = cs.diagramAut (e.trans e') hee' w := by
  rw [← diagramAut_trans cs e he e' he' hee', MulEquiv.trans_apply]

end CoxeterSystem
