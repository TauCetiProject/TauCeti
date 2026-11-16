/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import TauCeti.Algebra.Algebra.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.Preprojective.GraphOrientation
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Augmentation
import Mathlib.Algebra.Group.Fin.Basic
import TauCeti.Combinatorics.SimpleGraph.CycleGraph
import TauCeti.RepresentationTheory.Quiver.Preprojective.BaseChange.Basic
import TauCeti.RepresentationTheory.Quiver.Preprojective.InducedSubgraph
import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.MatrixRepresentation

/-!
# Cyclic quotients of preprojective algebras from their paths

The cyclic quotient `Π / [Π, Π]` of a preprojective algebra is spanned by the classes of paths.
This file collects the general facts about graded pieces of this cyclic quotient:

* Once every path of positive length is known to be a sum of commutators, the same holds for the
  graded pieces of positive degree, the commutator submodule is the kernel of the augmentation (so
  that the cyclic quotient is the module of vertex coefficients), and, for a two-coloured graph,
  the vanishing transfers to the additive preprojective algebra of every orientation. The only
  paths which need a graph-specific argument are the closed ones: a path between distinct vertices
  is a commutator with its target idempotent.
* Vanishing of a graded piece of the additive preprojective cyclic quotient transfers along any
  coefficient ring homomorphism via `RingHom.preprojectiveBaseChange`.
* Vanishing of a graded piece of the signless cyclic quotient descends along any induced-subgraph
  embedding `f : G ↪g H`, is therefore invariant under graph isomorphisms, and for a two-coloured
  (or bipartite) graph agrees with vanishing of the same graded piece for every orientation.
* Conversely, if a finite simple graph contains a cycle of length `m ≥ 3`, extending the `1 × 1`
  forward-shift matrix family on `Cₘ` by zero along the copy defines a matrix representation of
  both the signless preprojective algebra and the additive preprojective algebra of every
  orientation (without assuming bipartiteness). The closed cycle path has path degree `m` and
  trace `1`, so the degree-`m` piece of the cyclic quotient is nonzero over every nontrivial
  commutative ring.

## Main results

* `TauCeti.signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_ne`: a path between distinct
  vertices is a sum of commutators.
* `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule` and
  `TauCeti.preprojectiveGrade_le_commutatorSubmodule`: if every path of positive length is a sum of
  commutators, then so is every graded piece of positive degree.
* `TauCeti.preprojectiveGrade_le_commutatorSubmodule_of_ringHom`: vanishing of a graded piece of
  the cyclic quotient transfers along any coefficient ring homomorphism.
* `TauCeti.commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker`: if every path of positive
  length is a sum of commutators, the commutator submodule is the augmentation kernel.
* `TauCeti.signlessPreprojectiveCyclicQuotientEquiv` and
  `TauCeti.finrank_cyclicQuotient_signlessPreprojectiveAlgebra`: in that case the augmentation
  identifies the cyclic quotient with the module of vertex coefficients, of dimension the number of
  vertices over a nontrivial ring.
* `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule_of_embedding` and
  `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso`: vanishing of each graded
  piece of the signless cyclic quotient descends along induced-subgraph embeddings and is invariant
  under graph isomorphisms.
* `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_cycleGraph_copy`,
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_cycleGraph_copy`,
  `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic`, and
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic`: any cycle
  in a finite simple graph detects a nonzero cyclic class of degree at least `3` in both the
  signless and every oriented preprojective algebra.
* `SimpleGraph.Coloring.preprojectiveMk_ofPath_mem_commutatorSubmodule`: for a two-coloured graph,
  the vanishing for paths of positive length transfers from the signless algebra to the additive
  preprojective algebra of every orientation.
* `SimpleGraph.Coloring.preprojectiveGrade_le_commutatorSubmodule_iff` and
  `SimpleGraph.IsBipartite.preprojectiveGrade_le_commutatorSubmodule_iff`: for a two-coloured or
  bipartite graph, vanishing of a graded piece agrees between the signless algebra and every
  orientation.

## References

* J.-L. Loday, *Cyclic Homology*, Section 1.1, for the cyclic quotient as zeroth Hochschild
  homology.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

section Signless

variable (k : Type w) [CommRing k] {R : Type u} [Quiver.{v} R] [HasReverse R] [Finite R]
  [∀ x : R, Fintype (Quiver.Star x)]

local notation "Π" => signlessPreprojectiveAlgebra k R
local notation "π" => signlessPreprojectiveMk k R

/-- **A path between distinct vertices is a sum of commutators**: it is the commutator
`e_b * p - p * e_b` of the path `p` with its target idempotent `e_b`. -/
theorem signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_ne {a b : R} (p : Path a b)
    (hab : a ≠ b) : π (ofPath ⟨a, b, p⟩) ∈ commutatorSubmodule k Π := by
  have hcomm := mul_sub_mul_mem_commutatorSubmodule k Π
    (π (vertexIdempotent k b)) (π (ofPath ⟨a, b, p⟩))
  rwa [← map_mul, ← map_mul, vertexIdempotent_mul_ofPath,
    ofPath_mul_vertexIdempotent_of_ne _ hab.symm, map_zero, sub_zero] at hcomm

/-- **If every path of positive length is a sum of commutators, then so is every graded piece of
positive degree** of the signless algebra. -/
theorem signlessPreprojectiveGrade_le_commutatorSubmodule
    (h : ∀ x : Quiver.TotalPath R, 0 < x.2.2.length → π (ofPath x) ∈ commutatorSubmodule k Π)
    {d : ℕ} (hd : 0 < d) : signlessPreprojectiveGrade k R d ≤ commutatorSubmodule k Π := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_signlessPreprojectiveGrade_iff k R).1 hx
  rw [grade_eq_span_range] at hy
  refine (Submodule.span_le
    (p := (commutatorSubmodule k Π).comap (π : pathAlgebra k R →ₐ[k] Π).toLinearMap)).2 ?_ hy
  rintro _ ⟨⟨p, hp⟩, rfl⟩
  exact h p (hp ▸ hd)

/-- **If every path of positive length is a sum of commutators, then the commutator submodule of
the signless algebra is the augmentation kernel.** The augmentation onto the commutative algebra of
vertex coefficients kills commutators, and every element of its kernel is a combination of paths
of positive length. -/
theorem commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker
    (h : ∀ x : Quiver.TotalPath R, 0 < x.2.2.length → π (ofPath x) ∈ commutatorSubmodule k Π) :
    commutatorSubmodule k Π =
      LinearMap.ker (signlessPreprojectiveAugmentation (R := R) k).toLinearMap := by
  refine le_antisymm ((commutatorSubmodule_le_ker_iff _).2 fun x y => ?_) fun x hx => ?_
  · simp only [AlgHom.toLinearMap_apply, map_mul, mul_comm]
  · rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply, ← RingHom.mem_ker,
      ker_signlessPreprojectiveAugmentation,
      Ideal.mem_map_iff_of_surjective _ (signlessPreprojectiveMk_surjective k R)] at hx
    obtain ⟨f, hf, rfl⟩ := hx
    rw [← (pathAlgebraBasis k R).linearCombination_repr f, Finsupp.linearCombination_apply,
      Finsupp.sum, map_sum]
    refine Submodule.sum_mem _ fun x hx => ?_
    rw [map_smul, coe_pathAlgebraBasis]
    exact Submodule.smul_mem _ _ (h x (mem_arrowIdeal_iff.1 hf x (Finsupp.mem_support_iff.1 hx)))

/-- **If every path of positive length is a sum of commutators, then the cyclic quotient of the
signless algebra is the module of vertex coefficients**, by the augmentation. -/
noncomputable def signlessPreprojectiveCyclicQuotientEquiv
    (h : ∀ x : Quiver.TotalPath R, 0 < x.2.2.length → π (ofPath x) ∈ commutatorSubmodule k Π) :
    cyclicQuotient k Π ≃ₗ[k] (R → k) :=
  (Submodule.quotEquivOfEq _ _ (commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker k h)).trans
    (LinearMap.quotKerEquivOfSurjective _ (signlessPreprojectiveAugmentation_surjective k))

/-- The cyclic class of an element is sent to its augmentation. -/
@[simp]
theorem signlessPreprojectiveCyclicQuotientEquiv_mk
    (h : ∀ x : Quiver.TotalPath R, 0 < x.2.2.length → π (ofPath x) ∈ commutatorSubmodule k Π)
    (x : Π) :
    signlessPreprojectiveCyclicQuotientEquiv k h (Submodule.Quotient.mk x) =
      signlessPreprojectiveAugmentation k x :=
  (rfl)

/-- **If every path of positive length is a sum of commutators, then the cyclic quotient of the
signless algebra has dimension the number of vertices** over every nontrivial commutative ring. -/
theorem finrank_cyclicQuotient_signlessPreprojectiveAlgebra [Nontrivial k]
    (h : ∀ x : Quiver.TotalPath R, 0 < x.2.2.length → π (ofPath x) ∈ commutatorSubmodule k Π) :
    Module.finrank k (cyclicQuotient k Π) = Nat.card R := by
  have : Fintype R := Fintype.ofFinite R
  rw [(signlessPreprojectiveCyclicQuotientEquiv k h).finrank_eq,
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end Signless

section Preprojective

variable (k : Type w) [CommRing k] {Q : Type u} [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- **If every path of positive length is a sum of commutators, then so is every graded piece of
positive degree** of the preprojective algebra. -/
theorem preprojectiveGrade_le_commutatorSubmodule
    (h : ∀ x : Quiver.TotalPath (Symmetrify Q), 0 < x.2.2.length →
      preprojectiveMk k Q (ofPath x) ∈ commutatorSubmodule k (preprojectiveAlgebra k Q))
    {d : ℕ} (hd : 0 < d) :
    preprojectiveGrade k Q d ≤ commutatorSubmodule k (preprojectiveAlgebra k Q) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_preprojectiveGrade_iff k Q).1 hx
  rw [grade_eq_span_range] at hy
  refine (Submodule.span_le
    (p := (commutatorSubmodule k (preprojectiveAlgebra k Q)).comap
      (preprojectiveMk k Q).toLinearMap)).2 ?_ hy
  rintro _ ⟨⟨p, hp⟩, rfl⟩
  exact h p (hp ▸ hd)

/-- **Vanishing of a graded piece of the cyclic quotient transfers along any coefficient ring
homomorphism**, via `RingHom.preprojectiveBaseChange`: each path of length `d` over `l` is the
base-change image of the same path over `k`, and ring homomorphisms preserve commutators. -/
theorem preprojectiveGrade_le_commutatorSubmodule_of_ringHom {l : Type*} [CommRing l]
    (f : k →+* l) (d : ℕ)
    (h : preprojectiveGrade k Q d ≤ commutatorSubmodule k (preprojectiveAlgebra k Q)) :
    preprojectiveGrade l Q d ≤ commutatorSubmodule l (preprojectiveAlgebra l Q) := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := (mem_preprojectiveGrade_iff l Q).mp hy
  rw [grade_eq_span_range] at hz
  refine (Submodule.span_le
    (p := (commutatorSubmodule l (preprojectiveAlgebra l Q)).comap
      (preprojectiveMk l Q).toLinearMap)).2 ?_ hz
  rintro _ ⟨⟨p, hp⟩, rfl⟩
  have hx : preprojectiveMk k Q (ofPath p) ∈ preprojectiveGrade k Q d :=
    preprojectiveMk_mem_preprojectiveGrade k Q (ofPath_mem_grade_of_length hp)
  have hmap := map_mem_commutatorSubmodule_of_ringHom (l := l)
    (RingHom.preprojectiveBaseChange (Q := Q) f) (h hx)
  simpa only [SetLike.mem_coe, Submodule.mem_comap, AlgHom.toLinearMap_apply,
    RingHom.preprojectiveBaseChange_preprojectiveMk_ofPath] using hmap

end Preprojective

section Isomorphism

open DoubledQuiver

/-- **Vanishing of a graded piece of the signless cyclic quotient descends to induced subgraphs**:
for any graph embedding `f : G ↪g H`, if the degree-`d` piece of `Π⁺(H)` lies in the commutator
submodule, then so does the degree-`d` piece of `Π⁺(G)`. -/
theorem signlessPreprojectiveGrade_le_commutatorSubmodule_of_embedding (k : Type w) [CommRing k]
    {U V : Type*} [Finite U] [Finite V] {G : SimpleGraph U} {H : SimpleGraph V}
    [∀ i, Fintype (G.neighborSet i)] [∀ j, Fintype (H.neighborSet j)]
    (f : G ↪g H) (d : ℕ)
    (hH : signlessPreprojectiveGrade k (DoubledQuiver H) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H))) :
    signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  intro x hx
  rw [← map_signlessPreprojectiveEmbeddingHom_signlessPreprojectiveGrade k f d] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact map_mem_commutatorSubmodule (signlessPreprojectiveEmbeddingHom k f) (hH hy)

/-- **Vanishing of a graded piece of the signless cyclic quotient is invariant under graph
isomorphism.** -/
theorem signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso (k : Type w) [CommRing k]
    {V W : Type*} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    [∀ i, Fintype (G.neighborSet i)] [∀ j, Fintype (H.neighborSet j)]
    (e : G ≃g H) (d : ℕ) :
    signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) ↔
      signlessPreprojectiveGrade k (DoubledQuiver H) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)) :=
  ⟨signlessPreprojectiveGrade_le_commutatorSubmodule_of_embedding k e.symm.toEmbedding d,
   signlessPreprojectiveGrade_le_commutatorSubmodule_of_embedding k e.toEmbedding d⟩

end Isomorphism

/-! ### Cycle subgraphs and nonzero cyclic classes -/

section Cycle

open DoubledQuiver SimpleGraph Matrix
open scoped Fin.NatCast Kronecker

variable {V : Type u} {G : SimpleGraph V}

section CycleRep

section Path

variable {m : ℕ} [NeZero m]

/-- The `r`-th forward arrow around a copy of `Cₘ`. -/
private def cycleStep (hm : 3 ≤ m) (f : (cycleGraph m).Copy G) (r : ℕ) :
    vertex G (f (r : Fin m)) ⟶ vertex G (f ((r + 1 : ℕ) : Fin m)) :=
  arrow G (f.toHom.map_adj (by
    rw [Nat.cast_succ]
    exact cycleGraph_adj_add_one hm (r : Fin m)))

/-- The directed path of length `r` around a copy of `Cₘ` starting at `f 0`. -/
private def cyclePath (hm : 3 ≤ m) (f : (cycleGraph m).Copy G) :
    ∀ r : ℕ, _root_.Quiver.Path (vertex G (f ((0 : ℕ) : Fin m))) (vertex G (f (r : Fin m)))
  | 0 => .nil
  | r + 1 => (cyclePath hm f r).cons (cycleStep hm f r)

private theorem cyclePath_length (hm : 3 ≤ m) (f : (cycleGraph m).Copy G) (r : ℕ) :
    (cyclePath hm f r).length = r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [cyclePath, ih]

end Path

variable (k : Type w) [CommRing k] {m : ℕ} [NeZero m]

/-- The `1 × 1` forward-shift matrix family on `cycleGraph m`: `1` on forward edges `r → r + 1`
and `0` on all other vertex pairs. -/
private def cycleBlock (r s : Fin m) : Matrix Unit Unit k :=
  if s = r + 1 then 1 else 0

private theorem cycleBlock_mul_symm (hm : 3 ≤ m) (r s : Fin m) :
    cycleBlock k s r * cycleBlock k r s = 0 := by
  simp only [cycleBlock]
  split_ifs with h1 h2
  · exact absurd (h1.trans (congrArg (· + 1) h2)) (add_one_add_one_ne_self hm r).symm
  all_goals simp

variable [DecidableEq V] [DecidableRel (cycleGraph m).Adj]

private theorem extendByZero_cycleBlock_mul_symm (hm : 3 ≤ m) (f : (cycleGraph m).Copy G)
    (v w : V) :
    f.extendByZero (cycleBlock k) w v * f.extendByZero (cycleBlock k) v w = 0 := by
  by_cases hv : v ∈ Set.range f
  · by_cases hw : w ∈ Set.range f
    · obtain ⟨r, rfl⟩ := hv
      obtain ⟨s, rfl⟩ := hw
      simp only [SimpleGraph.Copy.extendByZero_apply_apply]
      split_ifs
      · exact cycleBlock_mul_symm k hm r s
      all_goals simp
    · rw [SimpleGraph.Copy.extendByZero_eq_zero_of_notMem_range_left _ _ hw, zero_mul]
  · rw [SimpleGraph.Copy.extendByZero_eq_zero_of_notMem_range_right _ _ _ hv, zero_mul]

variable [Fintype V]

private theorem matrixPathAlgHom_cycleBlock_ofPath_mul_ofPath (hm : 3 ≤ m)
    (f : (cycleGraph m).Copy G) {u v : DoubledQuiver G} (e₁ : u ⟶ v) (e₂ : v ⟶ u) :
    matrixPathAlgHom k (f.extendByZero (cycleBlock k)) (ofPath ⟨u, v, e₁.toPath⟩) *
      matrixPathAlgHom k (f.extendByZero (cycleBlock k)) (ofPath ⟨v, u, e₂.toPath⟩) = 0 := by
  obtain ⟨i, rfl⟩ := exists_eq_vertex G u
  obtain ⟨j, rfl⟩ := exists_eq_vertex G v
  have he₁ : e₁ = arrow G (by simpa using e₁.down) := Subsingleton.elim _ _
  have he₂ : e₂ = arrow G (by simpa using e₂.down) := Subsingleton.elim _ _
  rw [he₁, he₂, matrixPathAlgHom_ofPath_toPath, matrixPathAlgHom_ofPath_toPath,
    ← mul_kronecker_mul, single_mul_single_same, mul_one,
    extendByZero_cycleBlock_mul_symm k hm f j i, kronecker_zero]

private theorem matrixPathAlgHom_cycleBlock_comp_orientation_preprojectiveRelator (hm : 3 ≤ m)
    (f : (cycleGraph m).Copy G) (o : Orientation G) :
    (matrixPathAlgHom k (f.extendByZero (cycleBlock k))).comp
        (orientationPathAlgebraEquiv o k).symm.toAlgHom
        (preprojectiveRelator k (OrientedQuiver G o)) = 0 := by
  rw [preprojectiveRelator_def, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [map_sub, ← ofArrow_mul_ofArrow_reverse_eq_headBacktrackElem,
    ← ofArrow_reverse_mul_ofArrow_eq_tailBacktrackElem, map_mul, map_mul]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, ofArrow_eq_ofPath,
    orientationPathAlgebraEquiv_symm_ofPath, Prefunctor.mapTotalPath_mk,
    Prefunctor.mapPath_toPath]
  rw [matrixPathAlgHom_cycleBlock_ofPath_mul_ofPath k hm f _ _,
    matrixPathAlgHom_cycleBlock_ofPath_mul_ofPath k hm f _ _, sub_self]

private theorem matrixPathAlgHom_cyclePath (hm : 3 ≤ m) (f : (cycleGraph m).Copy G) (r : ℕ) :
    matrixPathAlgHom k (f.extendByZero (cycleBlock k)) (ofPath ⟨_, _, cyclePath hm f r⟩) =
      single (f (r : Fin m)) (f 0) 1 ⊗ₖ 1 := by
  induction r with
  | zero =>
    rw [cyclePath, ← vertexIdempotent_eq_ofPath, matrixPathAlgHom_vertexIdempotent, Nat.cast_zero]
  | succ r ih =>
    have hadj : (cycleGraph m).Adj (r : Fin m) ((r + 1 : ℕ) : Fin m) := by
      rw [Nat.cast_succ]
      exact cycleGraph_adj_add_one hm (r : Fin m)
    have hadjG : G.Adj (f (r : Fin m)) (f ((r + 1 : ℕ) : Fin m)) := f.toHom.map_adj hadj
    have hstep : cycleStep hm f r = arrow G hadjG := Subsingleton.elim _ _
    rw [cyclePath, ← ofArrow_mul_ofPath, map_mul, ih, hstep, matrixPathAlgHom_ofArrow,
      SimpleGraph.Copy.extendByZero_apply_apply_of_adj _ _ hadj,
      cycleBlock, Nat.cast_succ, ite_eq_left rfl, ← mul_kronecker_mul, single_mul_single_same,
      mul_one, mul_one]

end CycleRep

/-- **A cycle subgraph produces a nonzero cyclic class of the same degree in the signless
preprojective algebra.** If `G` contains a copy of `Cₘ` with `m ≥ 3`, then over every nontrivial
commutative ring some element of path degree `m` of `Π⁺(G)` does not lie in `[Π⁺(G), Π⁺(G)]`. -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_cycleGraph_copy
    (k : Type w) [CommRing k] [Nontrivial k] [Finite V]
    [inst : ∀ v, Fintype (G.neighborSet v)] {m : ℕ} (hm : 3 ≤ m) (f : (cycleGraph m).Copy G) :
    ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) m,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have : NeZero m := ⟨by omega⟩
  obtain rfl : inst = fun v => Subtype.fintype (Membership.mem (G.neighborSet v)) :=
    Subsingleton.elim _ _
  let φ := signlessMatrixRepresentation k (f.extendByZero (cycleBlock k))
    (f.sum_extendByZero_mul_extendByZero (cycleBlock k)
      fun r => Finset.sum_eq_zero fun s _ => cycleBlock_mul_symm k hm r s)
  let x := signlessPreprojectiveMk k (DoubledQuiver G) (ofPath ⟨_, _, cyclePath hm f m⟩)
  refine ⟨x, signlessPreprojectiveMk_mem_grade k _
    (ofPath_mem_grade_of_length (cyclePath_length hm f m)), fun hx => one_ne_zero (α := k) ?_⟩
  have htr := trace_map_eq_zero_of_mem_commutatorSubmodule φ hx
  have hfx : φ x = single (f 0) (f 0) 1 ⊗ₖ (1 : Matrix Unit Unit k) := by
    simpa only [φ, x, signlessMatrixRepresentation_signlessPreprojectiveMk, Fin.natCast_self] using
      matrixPathAlgHom_cyclePath k hm f m
  rw [hfx, trace_kronecker, trace_single_eq_same, Matrix.trace_one, Fintype.card_unit, Nat.cast_one,
    mul_one] at htr
  exact htr

/-- **A cycle subgraph produces a nonzero cyclic class of the same degree in the preprojective
algebra of every orientation.** If `G` contains a copy of `Cₘ` with `m ≥ 3`, then over every
nontrivial commutative ring and for every orientation `o` of `G` (without assuming `G` is
bipartite), some element of path degree `m` of `Π(OrientedQuiver G o)` does not lie in
`[Π(OrientedQuiver G o), Π(OrientedQuiver G o)]`. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_cycleGraph_copy
    (k : Type w) [CommRing k] [Nontrivial k] [Finite V]
    {m : ℕ} (hm : 3 ≤ m) (f : (cycleGraph m).Copy G) (o : Orientation G) :
    ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) m,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have : NeZero m := ⟨by omega⟩
  let ψ := (matrixPathAlgHom k (f.extendByZero (cycleBlock k))).comp
    (orientationPathAlgebraEquiv o k).symm.toAlgHom
  let φ := preprojectiveLift ψ
    (matrixPathAlgHom_cycleBlock_comp_orientation_preprojectiveRelator k hm f o)
  let p := orientationPathAlgebraEquiv o k (ofPath ⟨_, _, cyclePath hm f m⟩)
  let x := preprojectiveMk k (OrientedQuiver G o) p
  have hp : p ∈ grade k (Symmetrify (OrientedQuiver G o)) m := by
    dsimp only [p]
    rw [orientationPathAlgebraEquiv_ofPath]
    exact ofPath_mem_grade_of_length
      ((Prefunctor.length_mapTotalPath _ _).trans (cyclePath_length hm f m))
  refine ⟨x, preprojectiveMk_mem_preprojectiveGrade k _ hp, fun hx => one_ne_zero (α := k) ?_⟩
  have htr := trace_map_eq_zero_of_mem_commutatorSubmodule φ hx
  have hfx : φ x = single (f 0) (f 0) 1 ⊗ₖ (1 : Matrix Unit Unit k) := by
    simpa only [φ, ψ, x, p, preprojectiveLift_preprojectiveMk, AlgHom.comp_apply,
      AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply, Fin.natCast_self] using
      matrixPathAlgHom_cyclePath k hm f m
  rw [hfx, trace_kronecker, trace_single_eq_same, Matrix.trace_one, Fintype.card_unit, Nat.cast_one,
    mul_one] at htr
  exact htr

/-- **A finite graph with a cycle has a nonzero cyclic class in path degree at least three** in its
signless preprojective algebra, over every nontrivial commutative ring. -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic
    (k : Type w) [CommRing k] [Nontrivial k] [Finite V]
    [∀ v, Fintype (G.neighborSet v)] (hG : ¬ G.IsAcyclic) :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  rw [SimpleGraph.isAcyclic_iff_free_cycleGraph] at hG
  push Not at hG
  obtain ⟨m, hm, hmG⟩ := hG
  obtain ⟨f⟩ : Nonempty ((cycleGraph m).Copy G) := by
    simpa only [SimpleGraph.Free, not_isEmpty_iff] using hmG
  exact ⟨m, hm,
    exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_cycleGraph_copy k hm f⟩

/-- **A finite graph with a cycle has a nonzero cyclic class in path degree at least three** in the
preprojective algebra of every orientation, over every nontrivial commutative ring. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic
    (k : Type w) [CommRing k] [Nontrivial k] [Finite V]
    (hG : ¬ G.IsAcyclic) (o : Orientation G) :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  rw [SimpleGraph.isAcyclic_iff_free_cycleGraph] at hG
  push Not at hG
  obtain ⟨m, hm, hmG⟩ := hG
  obtain ⟨f⟩ : Nonempty ((cycleGraph m).Copy G) := by
    simpa only [SimpleGraph.Free, not_isEmpty_iff] using hmG
  exact ⟨m, hm,
    exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_cycleGraph_copy k hm f o⟩

end Cycle

end TauCeti

namespace SimpleGraph.Coloring

open TauCeti TauCeti.DoubledQuiver TauCeti.PathAlgebra _root_.Quiver

universe u w

section Paths

attribute [local instance] Fintype.ofFinite

variable {V : Type u} {G : SimpleGraph V} (k : Type w) [CommRing k] [Finite V]

/-- **The vanishing of cyclic classes of paths transfers to every orientation.** If every path of
positive length in the signless algebra of a two-coloured graph is a sum of commutators, then so is
every path of positive length in the additive preprojective algebra of each of its orientations:
the bipartite sign rescaling identifies the two algebras and rescales each path by a sign. -/
theorem preprojectiveMk_ofPath_mem_commutatorSubmodule (C : G.Coloring Bool) (o : Orientation G)
    (h : ∀ x : Quiver.TotalPath (DoubledQuiver G), 0 < x.2.2.length →
      signlessPreprojectiveMk k (DoubledQuiver G) (ofPath x) ∈
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)))
    (x : Quiver.TotalPath (Symmetrify (OrientedQuiver G o))) (hx : 0 < x.2.2.length) :
    preprojectiveMk k (OrientedQuiver G o) (ofPath x) ∈
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  let e := C.signlessPreprojectiveAlgebraEquiv k o
  have hsymm : e.symm (preprojectiveMk k (OrientedQuiver G o) (ofPath x)) ∈
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
    simp only [e, signlessPreprojectiveAlgebraEquiv_symm_preprojectiveMk, rescale_ofPath, map_smul,
      orientationPathAlgebraEquiv_symm_ofPath]
    exact Submodule.smul_mem _ _ (h _ (by rwa [Prefunctor.length_mapTotalPath]))
  have hmap := map_mem_commutatorSubmodule e hsymm
  rwa [AlgEquiv.apply_symm_apply] at hmap

end Paths

variable {V : Type u} {G : SimpleGraph V}

/-- **For a two-coloured graph, vanishing of a graded piece of the cyclic quotient agrees between
the signless algebra and the additive preprojective algebra of every orientation.** -/
theorem preprojectiveGrade_le_commutatorSubmodule_iff (C : G.Coloring Bool)
    (k : Type w) [CommRing k] [Finite V]
    [inst : ∀ i, Fintype (G.neighborSet i)] (o : Orientation G) (d : ℕ) :
    preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) ↔
      signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  obtain rfl : inst = fun i => Fintype.ofFinite _ := Subsingleton.elim _ _
  let φ := C.signlessPreprojectiveAlgebraEquiv k o
  constructor
  · intro hO x hx
    have hy := hO (C.signlessPreprojectiveAlgebraEquiv_mem_preprojectiveGrade k o hx)
    simpa only [φ, AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule φ.symm hy
  · intro hS y hy
    have hx := hS (C.signlessPreprojectiveAlgebraEquiv_symm_mem_signlessPreprojectiveGrade k o hy)
    simpa only [φ, AlgEquiv.apply_symm_apply] using map_mem_commutatorSubmodule φ hx

end SimpleGraph.Coloring

namespace SimpleGraph.IsBipartite

open TauCeti TauCeti.DoubledQuiver

universe u w

variable {V : Type u} {G : SimpleGraph V}

/-- **For a bipartite graph, vanishing of a graded piece of the cyclic quotient agrees between the
signless algebra and the additive preprojective algebra of every orientation.** -/
theorem preprojectiveGrade_le_commutatorSubmodule_iff (hG : G.IsBipartite)
    (k : Type w) [CommRing k] [Finite V]
    [∀ i, Fintype (G.neighborSet i)] (o : Orientation G) (d : ℕ) :
    preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) ↔
      signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) :=
  hG.coloringBool.preprojectiveGrade_le_commutatorSubmodule_iff k o d

end SimpleGraph.IsBipartite
