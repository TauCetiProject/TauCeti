/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.D4.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Preprojective.CyclicQuotient

/-!
# Characteristic-two cyclic classes from induced `D₄` subdiagrams

An induced copy of `D₄` in a finite graph yields a surjective graded homomorphism of signless
preprojective algebras (`TauCeti.signlessPreprojectiveEmbeddingHom`), so vanishing of a graded
piece of the signless cyclic quotient descends to the embedded `D₄`
(`TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule_of_embedding`). In characteristic two,
the nonzero degree-four cyclic class of `D₄` therefore pulls back to a nonzero degree-four cyclic
class of any finite graph containing an induced copy of `D₄`, in particular the finite `D` and `E`
diagrams. The copy must be induced: an arbitrary graph homomorphism does not give this quotient.

No field hypothesis is required, only a nontrivial commutative ring with `2 = 0`.

## References

* P. Etingof and C.-H. Eu, *Hochschild and cyclic homology of preprojective algebras of ADE
  quivers*, https://arxiv.org/abs/math/0609006.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, for the bad-characteristic cyclic classes.
-/

public section

namespace TauCeti

open DoubledQuiver

variable (k : Type*) [CommRing k] {V : Type*} [Finite V] {G : SimpleGraph V}

/-- An induced `D₄` subdiagram detects a nonzero degree-four cyclic class in characteristic
two. This holds over every nontrivial commutative coefficient ring. -/
theorem exists_mem_signlessPreprojectiveGrade_four_notMem_commutatorSubmodule_of_d4_embedding
    [Nontrivial k] [∀ v, Fintype (G.neighborSet v)] (f : zigzagD4Graph ↪g G) (h2 : (2 : k) = 0) :
    ∃ z : signlessPreprojectiveAlgebra k (DoubledQuiver G),
      z ∈ signlessPreprojectiveGrade k (DoubledQuiver G) 4 ∧
        z ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  let _ := SimpleGraph.neighborSetFintypeOfFinite zigzagD4Graph
  exact IsConcreteLE.not_le_iff_exists.mp fun hG =>
    signlessWord_D4_cyclicWord_not_mem_commutatorSubmodule k h2
      (signlessPreprojectiveGrade_le_commutatorSubmodule_of_embedding k f 4 hG
        (signlessWord_D4_cyclicWord_mem_grade_four k))

end TauCeti
