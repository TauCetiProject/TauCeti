/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Augmentation

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

## Main results

* `TauCeti.signlessPreprojectiveMk_A_ofPath_mem_commutatorSubmodule`: every path of positive
  length in `Π⁺(Aₙ)` lies in `[Π⁺(Aₙ), Π⁺(Aₙ)]`.
* `TauCeti.signlessPreprojectiveGrade_A_le_commutatorSubmodule`: every piece of positive path
  degree of `Π⁺(Aₙ)` lies in `[Π⁺(Aₙ), Π⁺(Aₙ)]`.
* `TauCeti.commutatorSubmodule_signlessPreprojectiveAlgebra_A_eq_ker`: the commutator submodule
  is the kernel of the augmentation.
* `TauCeti.signlessPreprojectiveACyclicQuotientEquiv`: the cyclic quotient of `Π⁺(Aₙ)` is the
  module of vertex coefficients.
* `TauCeti.finrank_cyclicQuotient_signlessPreprojectiveAlgebra_A`: over a field, the cyclic
  quotient of `Π⁺(Aₙ)` has dimension `n`.
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
  · -- A path between distinct vertices is the commutator of the target idempotent with itself.
    have hl :
        σ (vertexIdempotent k (vertex AG b)) * σ (ofPath ⟨_, _, p⟩) = σ (ofPath ⟨_, _, p⟩) := by
      rw [← map_mul, vertexIdempotent_mul_ofPath]
    have hr : σ (ofPath ⟨_, _, p⟩) * σ (vertexIdempotent k (vertex AG b)) = 0 := by
      rw [← map_mul, ofPath_mul_vertexIdempotent_of_ne _
        fun h => hab (vertex_injective AG h).symm, map_zero]
    have hcomm := mul_sub_mul_mem_commutatorSubmodule k Π
      (σ (vertexIdempotent k (vertex AG b))) (σ (ofPath ⟨_, _, p⟩))
    rwa [hl, hr, sub_zero] at hcomm

/-- **The cyclic quotient of the signless algebra of `Aₙ` vanishes in positive degrees**: every
homogeneous piece of positive path degree lies in the commutator submodule. -/
theorem signlessPreprojectiveGrade_A_le_commutatorSubmodule {d : ℕ} (hd : 0 < d) :
    signlessPreprojectiveGrade k Q d ≤ commutatorSubmodule k Π := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_signlessPreprojectiveGrade_iff k Q).1 hx
  rw [grade_eq_span_range] at hy
  refine (Submodule.span_le
    (p := (commutatorSubmodule k Π).comap (σ : pathAlgebra k Q →ₐ[k] Π).toLinearMap)).2 ?_ hy
  rintro _ ⟨⟨p, hp⟩, rfl⟩
  exact signlessPreprojectiveMk_A_ofPath_mem_commutatorSubmodule k p (hp ▸ hd)

/-- **The commutator submodule of the signless algebra of `Aₙ` is the augmentation kernel.**
The augmentation onto the commutative algebra of vertex coefficients kills commutators, and every
element of its kernel is a combination of paths of positive length. -/
theorem commutatorSubmodule_signlessPreprojectiveAlgebra_A_eq_ker :
    commutatorSubmodule k Π =
      LinearMap.ker (signlessPreprojectiveAugmentation (R := Q) k).toLinearMap := by
  refine le_antisymm ((commutatorSubmodule_le_ker_iff _).2 fun x y => ?_) fun x hx => ?_
  · simp only [AlgHom.toLinearMap_apply, map_mul, mul_comm]
  · rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply, ← RingHom.mem_ker,
      ker_signlessPreprojectiveAugmentation,
      Ideal.mem_map_iff_of_surjective _ (signlessPreprojectiveMk_surjective k Q)] at hx
    obtain ⟨f, hf, rfl⟩ := hx
    rw [← (pathAlgebraBasis k Q).linearCombination_repr f, Finsupp.linearCombination_apply,
      Finsupp.sum, map_sum]
    refine Submodule.sum_mem _ fun x hx => ?_
    rw [map_smul, coe_pathAlgebraBasis]
    exact Submodule.smul_mem _ _ (signlessPreprojectiveMk_A_ofPath_mem_commutatorSubmodule k x
      (mem_arrowIdeal_iff.1 hf x (Finsupp.mem_support_iff.1 hx)))

/-- **The cyclic quotient of the signless algebra of `Aₙ` is the module of vertex coefficients**,
by the augmentation. -/
noncomputable def signlessPreprojectiveACyclicQuotientEquiv : cyclicQuotient k Π ≃ₗ[k] (Q → k) :=
  (Submodule.quotEquivOfEq _ _ (commutatorSubmodule_signlessPreprojectiveAlgebra_A_eq_ker k)).trans
    (LinearMap.quotKerEquivOfSurjective _ (signlessPreprojectiveAugmentation_surjective k))

/-- The cyclic class of an element is sent to its augmentation. -/
@[simp]
theorem signlessPreprojectiveACyclicQuotientEquiv_mk (x : Π) :
    signlessPreprojectiveACyclicQuotientEquiv k (n := n) (Submodule.Quotient.mk x) =
      signlessPreprojectiveAugmentation k x :=
  (rfl)

end CommRing

/-- **The cyclic quotient of the signless algebra of `Aₙ` has dimension `n`** over every field, one
for each vertex. -/
theorem finrank_cyclicQuotient_signlessPreprojectiveAlgebra_A [Field k] :
    Module.finrank k (cyclicQuotient k Π) = n := by
  have : Fintype Q := Fintype.ofFinite _
  rw [(signlessPreprojectiveACyclicQuotientEquiv k).finrank_eq, Module.finrank_fintype_fun_eq_card,
    ← Fintype.card_congr (vertexEquiv AG), Fintype.card_fin, DynkinType.rank_A]

/-! ### Orientations -/

section Orientation

variable [CommRing k] (o : Orientation (diagramGraph (DynkinType.A n).cartanMatrix))

/-- **Every path of positive length in the preprojective algebra of an orientation of `Aₙ` is a
sum of commutators.** -/
theorem preprojectiveMk_A_ofPath_mem_commutatorSubmodule
    (x : Quiver.TotalPath (Symmetrify (OrientedQuiver AG o))) (hx : 0 < x.2.2.length) :
    preprojectiveMk k (OrientedQuiver AG o) (ofPath x) ∈
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver AG o)) := by
  let e := (diagramGraphAColoring n).signlessPreprojectiveAlgebraEquiv k o
  have hsymm :
      e.symm (preprojectiveMk k (OrientedQuiver AG o) (ofPath x)) ∈ commutatorSubmodule k Π := by
    simp only [e, SimpleGraph.Coloring.signlessPreprojectiveAlgebraEquiv_symm_preprojectiveMk,
      rescale_ofPath, map_smul, orientationPathAlgebraEquiv_symm_ofPath]
    exact Submodule.smul_mem _ _ (signlessPreprojectiveMk_A_ofPath_mem_commutatorSubmodule k _
      (by rwa [Prefunctor.length_mapTotalPath]))
  have h := map_mem_commutatorSubmodule e hsymm
  rwa [AlgEquiv.apply_symm_apply] at h

/-- **The cyclic quotient of the preprojective algebra of an orientation of `Aₙ` vanishes in
positive degrees**: every homogeneous piece of positive path degree lies in the commutator
submodule. -/
theorem preprojectiveGrade_A_le_commutatorSubmodule {d : ℕ} (hd : 0 < d) :
    preprojectiveGrade k (OrientedQuiver AG o) d ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver AG o)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_preprojectiveGrade_iff k (OrientedQuiver AG o)).1 hx
  rw [grade_eq_span_range] at hy
  refine (Submodule.span_le
    (p := (commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver AG o))).comap
      (preprojectiveMk k (OrientedQuiver AG o)).toLinearMap)).2 ?_ hy
  rintro _ ⟨⟨p, hp⟩, rfl⟩
  exact preprojectiveMk_A_ofPath_mem_commutatorSubmodule k o p (hp ▸ hd)

end Orientation

end TauCeti
