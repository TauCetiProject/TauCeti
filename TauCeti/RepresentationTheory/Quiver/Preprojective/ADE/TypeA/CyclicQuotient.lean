/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.CyclicQuotient

/-!
# The cyclic quotient of the type-`A` preprojective algebra

The cyclic quotient `Π / [Π, Π]` of an algebra is its zeroth Hochschild homology. For the
preprojective algebra `Π(Q)` of a quiver `Q` whose underlying graph is a tree, Liu and Wang
identify its degree-`(q + 2)` piece with the second Hochschild cohomology `HH^{2,q}` of the
two-dimensional Ginzburg algebra `Π₂(Q)`, which controls the `A∞` deformations of the zigzag
algebra of the tree. Graphs containing an affine diagram have nonzero positive-degree classes, for
instance `TauCeti.exists_mem_signlessPreprojectiveGrade_four_notMem_commutatorSubmodule` for affine
`Dₙ`. This file treats the opposite case for the path `Aₙ`: over every commutative ring, the
cyclic quotient is concentrated in path degree zero, where it is free on the vertices.

## The argument

By `TauCeti.signlessPreprojectiveMk_A_ofPath_eq_zero_or_ladderValley`, a path in the signless
algebra `Π⁺(Aₙ)` is, up to sign, a valley word which descends from its source to some vertex `m`
and climbs to its target, or zero. A path between distinct vertices is `e_b x = e_b x - x e_b`, a
commutator. A closed path of positive length is a valley word descending and climbing the same
number `s > 0` of steps. Rotating its descent past its climb gives a closed path at the bottom
vertex `m`, which is again a valley word, now with bottom `m - s`, or zero. The bottom cannot
descend forever, so every closed valley word of positive length is a sum of commutators
(`TauCeti.ladderValley_mem_commutatorSubmodule`).

Consequently the commutator submodule of `Π⁺(Aₙ)` is exactly the kernel of the augmentation onto
the vertex coefficients, and the augmentation induces `Π⁺(Aₙ) / [Π⁺(Aₙ), Π⁺(Aₙ)] ≃ k^{Aₙ}`. Through
the bipartite sign rescaling, the same vanishing holds for the additive preprojective algebra of
every orientation of `Aₙ`.
These consequences, and the case of a path between distinct vertices, do not depend on the graph;
they are in `TauCeti.RepresentationTheory.Quiver.Preprojective.CyclicQuotient`.

## Main results

* `TauCeti.signlessPreprojectiveMk_A_ofPath_mem_commutatorSubmodule`: every path of positive
  length in `Π⁺(Aₙ)` lies in `[Π⁺(Aₙ), Π⁺(Aₙ)]`.
* `TauCeti.signlessPreprojectiveGrade_A_le_commutatorSubmodule`: every piece of positive path
  degree of `Π⁺(Aₙ)` lies in `[Π⁺(Aₙ), Π⁺(Aₙ)]`.
* `TauCeti.commutatorSubmodule_signlessPreprojectiveAlgebra_A_eq_ker`: the commutator submodule
  is the kernel of the augmentation.
* `TauCeti.finrank_cyclicQuotient_signlessPreprojectiveAlgebra_A`: over a nontrivial commutative
  ring, the cyclic quotient of `Π⁺(Aₙ)` has dimension `n`.
* `TauCeti.preprojectiveMk_A_ofPath_mem_commutatorSubmodule` and
  `TauCeti.preprojectiveGrade_A_le_commutatorSubmodule`: the same vanishing in positive degrees for
  the preprojective algebra `Π(Q)` of every orientation `Q` of `Aₙ`.

## References

* P. Etingof and C.-H. Eu, *Hochschild and cyclic homology of preprojective algebras of ADE
  quivers*, Mosc. Math. J. 7 (2007), https://arxiv.org/abs/math/0609006, for the cyclic quotient
  of the preprojective algebra of a Dynkin quiver.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, for the role of the cyclic quotient in the deformation theory
  of zigzag algebras.
* J.-L. Loday, *Cyclic Homology*, Section 1.1, for the cyclic quotient as zeroth Hochschild
  homology.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

attribute [local instance] finiteNeighborSetFintype

variable (k : Type*) {n : ℕ}

local notation "AG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.A n))
local notation "Q" => DoubledQuiver AG
local notation "Π" => signlessPreprojectiveAlgebra k Q
local notation "σ" => signlessPreprojectiveMk k Q

section CommRing

variable [CommRing k]

/-- **Every path of positive length in the signless algebra of `Aₙ` is a sum of commutators.** -/
theorem signlessPreprojectiveMk_A_ofPath_mem_commutatorSubmodule
    (x : Quiver.TotalPath Q) (hx : 0 < x.2.2.length) :
    σ (ofPath x) ∈ commutatorSubmodule k Π := by
  obtain ⟨a', b', p⟩ := x
  obtain ⟨a, rfl⟩ := exists_eq_vertex AG a'
  obtain ⟨b, rfl⟩ := exists_eq_vertex AG b'
  by_cases hab : a = b
  · -- A closed path is a closed valley word, which begins with the descent from `a`.
    subst hab
    rcases signlessPreprojectiveMk_A_ofPath_eq_zero_or_ladderValley k p with
      h | ⟨m, s, r, ε, hlen, hs, hr, h⟩
    · rw [h]
      exact zero_mem _
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by dsimp only at hx; omega⟩
    obtain rfl : r = t + 1 := by omega
    rw [h, ← ladderValley_mul_d, mul_assoc, signlessArrow_mul_vertexIdempotent,
      ite_eq_left (by omega), ladderValley_mul_d]
    exact Submodule.smul_of_tower_mem _ ε
      (ladderValley_mem_commutatorSubmodule k
        (signlessArrow_A_one_zero_mul_signlessArrow_A_zero_one k)
        (fun w => by simpa [add_comm] using signlessArrow_A_relation k (n := n) (w + 1)) m
        (Nat.succ_pos t))
  · exact signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_ne k p
      fun h => hab (vertex_injective AG h)

/-- **The cyclic quotient of the signless algebra of `Aₙ` vanishes in positive degrees**: every
homogeneous piece of positive path degree lies in the commutator submodule. -/
theorem signlessPreprojectiveGrade_A_le_commutatorSubmodule {d : ℕ} (hd : 0 < d) :
    signlessPreprojectiveGrade k Q d ≤ commutatorSubmodule k Π :=
  signlessPreprojectiveGrade_le_commutatorSubmodule k
    (signlessPreprojectiveMk_A_ofPath_mem_commutatorSubmodule k) hd

/-- **The commutator submodule of the signless algebra of `Aₙ` is the augmentation kernel.**
The augmentation onto the commutative algebra of vertex coefficients kills commutators, and every
element of its kernel is a combination of paths of positive length. -/
theorem commutatorSubmodule_signlessPreprojectiveAlgebra_A_eq_ker :
    commutatorSubmodule k Π =
      LinearMap.ker (signlessPreprojectiveAugmentation (R := Q) k).toLinearMap :=
  commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker k
    (signlessPreprojectiveMk_A_ofPath_mem_commutatorSubmodule k)

/-- **The cyclic quotient of the signless algebra of `Aₙ` has dimension `n`** over every nontrivial
commutative ring, one for each vertex. -/
theorem finrank_cyclicQuotient_signlessPreprojectiveAlgebra_A [Nontrivial k] :
    Module.finrank k (cyclicQuotient k Π) = n := by
  rw [finrank_cyclicQuotient_signlessPreprojectiveAlgebra k
      (signlessPreprojectiveMk_A_ofPath_mem_commutatorSubmodule k),
    ← Nat.card_congr (vertexEquiv AG), Nat.card_fin, DynkinType.rank_A]

end CommRing

/-! ### Orientations -/

section Orientation

variable [CommRing k] (o : Orientation (diagramGraph (DynkinType.A n).cartanMatrix))

/-- **Every path of positive length in the preprojective algebra of an orientation of `Aₙ` is a
sum of commutators.** -/
theorem preprojectiveMk_A_ofPath_mem_commutatorSubmodule
    (x : Quiver.TotalPath (Symmetrify (OrientedQuiver AG o))) (hx : 0 < x.2.2.length) :
    preprojectiveMk k (OrientedQuiver AG o) (ofPath x) ∈
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver AG o)) :=
  (diagramGraphAColoring n).preprojectiveMk_ofPath_mem_commutatorSubmodule k o
    (signlessPreprojectiveMk_A_ofPath_mem_commutatorSubmodule k) x hx

/-- **The cyclic quotient of the preprojective algebra of an orientation of `Aₙ` vanishes in
positive degrees**: every homogeneous piece of positive path degree lies in the commutator
submodule. -/
theorem preprojectiveGrade_A_le_commutatorSubmodule {d : ℕ} (hd : 0 < d) :
    preprojectiveGrade k (OrientedQuiver AG o) d ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver AG o)) :=
  preprojectiveGrade_le_commutatorSubmodule k
    (preprojectiveMk_A_ofPath_mem_commutatorSubmodule k o) hd

end Orientation

end TauCeti
