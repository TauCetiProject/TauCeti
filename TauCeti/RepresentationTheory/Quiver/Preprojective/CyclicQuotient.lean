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
import TauCeti.Combinatorics.SimpleGraph.CycleGraph
import TauCeti.RepresentationTheory.Quiver.PathAlgebra.OfArrows
import TauCeti.RepresentationTheory.Quiver.Preprojective.Isomorphism

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
* Vanishing of a graded piece of the signless cyclic quotient is invariant under graph
  isomorphisms, and for a bipartite graph it agrees with vanishing of the same graded piece for
  every orientation.
* Conversely, if a finite simple graph contains a cycle of length `m ≥ 3`, sending each forward
  arrow of the cycle to the shift matrix unit `E_{r+1, r}` and every other arrow to zero defines a
  matrix representation of both the signless preprojective algebra and the additive preprojective
  algebra of every orientation (without assuming bipartiteness). The closed cycle path has path
  degree `m` and trace `1`, so the degree-`m` piece of the cyclic quotient is nonzero over every
  nontrivial commutative ring.

## Main results

* `TauCeti.signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_ne`: a path between distinct
  vertices is a sum of commutators.
* `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule` and
  `TauCeti.preprojectiveGrade_le_commutatorSubmodule`: if every path of positive length is a sum of
  commutators, then so is every graded piece of positive degree.
* `TauCeti.commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker`: if every path of positive
  length is a sum of commutators, the commutator submodule is the augmentation kernel.
* `TauCeti.signlessPreprojectiveCyclicQuotientEquiv` and
  `TauCeti.finrank_cyclicQuotient_signlessPreprojectiveAlgebra`: in that case the augmentation
  identifies the cyclic quotient with the module of vertex coefficients, of dimension the number of
  vertices over a nontrivial ring.
* `TauCeti.signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso`: graph isomorphisms
  preserve and reflect vanishing of each graded piece of the signless cyclic quotient.
* `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_cycleGraph_copy`,
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_cycleGraph_copy`,
  `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic`, and
  `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic`: any cycle
  in a finite simple graph detects a nonzero cyclic class of degree at least `3` in both the
  signless and every oriented preprojective algebra.
* `SimpleGraph.Coloring.preprojectiveMk_ofPath_mem_commutatorSubmodule`: for a two-coloured graph,
  the vanishing for paths of positive length transfers from the signless algebra to the additive
  preprojective algebra of every orientation.
* `SimpleGraph.IsBipartite.preprojectiveGrade_le_commutatorSubmodule_iff`: for a bipartite graph,
  vanishing of a graded piece agrees between the signless algebra and every orientation.

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

end Preprojective

section Isomorphism

open DoubledQuiver

/-- **Vanishing of a graded piece of the signless cyclic quotient is invariant under graph
isomorphism.** -/
theorem signlessPreprojectiveGrade_le_commutatorSubmodule_iff_of_iso (k : Type w) [CommRing k]
    {V W : Type*} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    [∀ i, Fintype (G.neighborSet i)] [∀ j, Fintype (H.neighborSet j)]
    (e : G ≃g H) (d : ℕ) :
    signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) ↔
      signlessPreprojectiveGrade k (DoubledQuiver H) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver H)) := by
  let φ := signlessPreprojectiveAlgebraEquiv k e
  constructor
  · intro hG y hy
    have hx : φ.symm y ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d := by
      simpa only [φ, signlessPreprojectiveAlgebraEquiv_symm] using
        (signlessPreprojectiveAlgebraEquiv_mem_signlessPreprojectiveGrade_iff k e.symm).mpr hy
    simpa only [AlgEquiv.apply_symm_apply] using map_mem_commutatorSubmodule φ (hG hx)
  · intro hH x hx
    have hy : φ x ∈ signlessPreprojectiveGrade k (DoubledQuiver H) d :=
      (signlessPreprojectiveAlgebraEquiv_mem_signlessPreprojectiveGrade_iff k e).mpr hx
    simpa only [AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule φ.symm (hH hy)

end Isomorphism

/-! ### Cycle subgraphs and nonzero cyclic classes -/

section Cycle

open DoubledQuiver SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

section CycleRep

section Path

variable {m : ℕ} [NeZero m]

private theorem fin_ofNat_succ (r : ℕ) : Fin.ofNat m (r + 1) = Fin.ofNat m r + 1 :=
  Fin.ext (by simp [Fin.val_add, Nat.add_mod])

/-- The `r`-th forward arrow around a copy of `Cₘ`. -/
private def cycleStep (hm : 3 ≤ m) (f : (cycleGraph m).Copy G) (r : ℕ) :
    vertex G (f (Fin.ofNat m r)) ⟶ vertex G (f (Fin.ofNat m (r + 1))) :=
  arrow G (f.toHom.map_adj (by
    rw [fin_ofNat_succ]
    exact cycleGraph_adj_add_one hm (Fin.ofNat m r)))

/-- The directed path of length `r` around a copy of `Cₘ` starting at `f 0`. -/
private def cyclePath (hm : 3 ≤ m) (f : (cycleGraph m).Copy G) :
    ∀ r : ℕ, _root_.Quiver.Path (vertex G (f (Fin.ofNat m 0))) (vertex G (f (Fin.ofNat m r)))
  | 0 => .nil
  | r + 1 => (cyclePath hm f r).cons (cycleStep hm f r)

private theorem cyclePath_length (hm : 3 ≤ m) (f : (cycleGraph m).Copy G) (r : ℕ) :
    (cyclePath hm f r).length = r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [cyclePath, ih]

end Path

variable (k : Type w) [CommRing k] [DecidableEq V] {m : ℕ}

/-- The projection matrix at a vertex `v` for a copy of `Cₘ` in `G`: `E_{r, r}` if `v = f r`,
and zero outside the image of the cycle. -/
private def cycleVertex (f : (cycleGraph m).Copy G) (v : DoubledQuiver G) :
    Matrix (Fin m) (Fin m) k :=
  ∑ r : Fin m, if f r = (vertexEquiv G).symm v then Matrix.single r r 1 else 0

section Arrows

variable [NeZero m]

/-- The matrix of an arrow `i ⟶ j` for a copy of `Cₘ` in `G`: `E_{r + 1, r}` if `(i, j)` is the
forward edge `(f r, f (r + 1))` of the cycle, and zero otherwise. -/
private def cycleArrow (f : (cycleGraph m).Copy G) {i j : DoubledQuiver G} (_ : i ⟶ j) :
    Matrix (Fin m) (Fin m) k :=
  ∑ r : Fin m,
    if f r = (vertexEquiv G).symm i ∧ f (r + 1) = (vertexEquiv G).symm j then
      Matrix.single (r + 1) r 1
    else 0

private theorem cycleVertex_mul_cycleArrow (f : (cycleGraph m).Copy G)
    {i j : DoubledQuiver G} (a : i ⟶ j) :
    cycleVertex k f j * cycleArrow k f a = cycleArrow k f a := by
  simp only [cycleVertex, cycleArrow]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_mul]
  by_cases hr : f r = (vertexEquiv G).symm i ∧ f (r + 1) = (vertexEquiv G).symm j
  · simp only [hr, and_self, ↓reduceIte]
    rw [Finset.sum_eq_single (r + 1)]
    · simp [hr.2]
    · intro s _ hs
      split_ifs
      · simp [hs]
      · exact zero_mul _
    · intro h
      exact absurd (Finset.mem_univ _) h
  · simp [hr]

private theorem cycleArrow_mul_cycleVertex (f : (cycleGraph m).Copy G)
    {i j : DoubledQuiver G} (a : i ⟶ j) :
    cycleArrow k f a * cycleVertex k f i = cycleArrow k f a := by
  simp only [cycleVertex, cycleArrow]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  by_cases hr : f r = (vertexEquiv G).symm i ∧ f (r + 1) = (vertexEquiv G).symm j
  · simp only [hr, and_self, ↓reduceIte]
    rw [Finset.sum_eq_single r]
    · simp [hr.1]
    · intro s _ hs
      split_ifs
      · simp [hs.symm]
      · exact mul_zero _
    · intro h
      exact absurd (Finset.mem_univ _) h
  · simp [hr]

private theorem cycleArrow_mul_cycleArrow_eq_zero (hm : 3 ≤ m) (f : (cycleGraph m).Copy G)
    {i j : DoubledQuiver G} (a : i ⟶ j) (b : j ⟶ i) :
    cycleArrow k f a * cycleArrow k f b = 0 := by
  simp only [cycleArrow]
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  split_ifs with hr hs
  · rcases eq_or_ne r (s + 1) with rfl | hrs
    · exact absurd (f.toEmbedding.injective (hr.2.trans hs.1.symm))
        (add_one_add_one_ne_self hm s)
    · simp [hrs]
  · exact mul_zero _
  · exact zero_mul _
  · exact mul_zero _

end Arrows

variable [Fintype V]

private theorem completeOrthogonalIdempotents_cycleVertex (f : (cycleGraph m).Copy G) :
    CompleteOrthogonalIdempotents (cycleVertex k f) := by
  rw [CompleteOrthogonalIdempotents.iff_ortho_complete]
  refine ⟨fun v w hvw => ?_, ?_⟩
  · simp only [cycleVertex]
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    split_ifs with hr hs
    · rcases eq_or_ne r s with rfl | hrs
      · exact absurd ((vertexEquiv G).symm.injective (hr.symm.trans hs)) hvw
      · simp [hrs]
    · exact mul_zero _
    · exact zero_mul _
    · exact mul_zero _
  · rw [← (vertexEquiv G).sum_comp]
    simp only [cycleVertex, Equiv.symm_apply_apply]
    rw [Finset.sum_comm]
    ext a b
    simp only [Matrix.sum_apply, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      Matrix.single_apply, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      simp
    · simp only [hab, ↓reduceIte]
      exact Finset.sum_eq_zero fun r _ => ite_eq_right fun ⟨h1, h2⟩ => hab (h1.symm.trans h2)

variable [NeZero m]

/-- The path-algebra homomorphism sending forward edges of a copy of `Cₘ` to shift matrices
and all other arrows to zero. -/
private noncomputable def cyclePathAlgHom (f : (cycleGraph m).Copy G) :
    pathAlgebra k (DoubledQuiver G) →ₐ[k] Matrix (Fin m) (Fin m) k :=
  liftAlgHomOfArrows k (cycleVertex k f) (completeOrthogonalIdempotents_cycleVertex k f)
    (cycleArrow k f) (cycleVertex_mul_cycleArrow k f) (cycleArrow_mul_cycleVertex k f)

private theorem cyclePathAlgHom_signlessPreprojectiveRelator (hm : 3 ≤ m)
    (f : (cycleGraph m).Copy G) [∀ v, Fintype (G.neighborSet v)] (x : DoubledQuiver G) :
    cyclePathAlgHom k f (signlessPreprojectiveRelator k x) = 0 := by
  obtain ⟨v, rfl⟩ := exists_eq_vertex G x
  rw [signlessPreprojectiveRelator_congr k (vertex G v) _ (instFintypeStarVertex G v),
    signlessPreprojectiveRelator_vertex, map_sum]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [← ofArrow_symm_mul_ofArrow, map_mul, ofArrow_eq_ofPath, ofArrow_eq_ofPath,
    cyclePathAlgHom, liftAlgHomOfArrows_ofPath_toPath, liftAlgHomOfArrows_ofPath_toPath]
  exact cycleArrow_mul_cycleArrow_eq_zero k hm f _ _

private theorem cyclePathAlgHom_comp_orientation_preprojectiveRelator (hm : 3 ≤ m)
    (f : (cycleGraph m).Copy G) (o : Orientation G) :
    (cyclePathAlgHom k f).comp (orientationPathAlgebraEquiv o k).symm.toAlgHom
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
    Prefunctor.mapPath_toPath, cyclePathAlgHom, liftAlgHomOfArrows_ofPath_toPath]
  rw [cycleArrow_mul_cycleArrow_eq_zero k hm f _ _,
    cycleArrow_mul_cycleArrow_eq_zero k hm f _ _, sub_self]

private theorem cyclePathAlgHom_cyclePath (hm : 3 ≤ m) (f : (cycleGraph m).Copy G) (r : ℕ) :
    cyclePathAlgHom k f (ofPath ⟨_, _, cyclePath hm f r⟩) = Matrix.single (Fin.ofNat m r) 0 1 := by
  induction r with
  | zero =>
    rw [cyclePath, cyclePathAlgHom, liftAlgHomOfArrows_ofPath_nil, cycleVertex]
    have h0 : Fin.ofNat m 0 = 0 := rfl
    rw [h0, vertexEquiv_symm_vertex, Finset.sum_eq_single (0 : Fin m)]
    · simp
    · intro s _ hs
      exact ite_eq_right fun h => absurd (f.toEmbedding.injective h) hs
    · intro h
      exact absurd (Finset.mem_univ _) h
  | succ r ih =>
    have harr : cycleArrow k f (cycleStep hm f r) =
        Matrix.single (Fin.ofNat m r + 1) (Fin.ofNat m r) 1 := by
      simp only [cycleArrow, vertexEquiv_symm_vertex, fin_ofNat_succ]
      rw [Finset.sum_eq_single (Fin.ofNat m r)]
      · simp
      · intro s _ hs
        exact ite_eq_right fun ⟨h, _⟩ => absurd (f.toEmbedding.injective h) hs
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [cyclePath, cyclePathAlgHom, liftAlgHomOfArrows_ofPath_cons, ← cyclePathAlgHom, ih, harr,
      Matrix.single_mul_single_same, one_mul, fin_ofNat_succ]

end CycleRep

/-- **A cycle subgraph produces a nonzero cyclic class of the same degree in the signless
preprojective algebra.** If `G` contains a copy of `Cₘ` with `m ≥ 3`, then over every nontrivial
commutative ring some element of path degree `m` of `Π⁺(G)` does not lie in `[Π⁺(G), Π⁺(G)]`. -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_cycleGraph_copy
    (k : Type w) [CommRing k] [Nontrivial k] [Finite V]
    [∀ v, Fintype (G.neighborSet v)] {m : ℕ} (hm : 3 ≤ m) (f : (cycleGraph m).Copy G) :
    ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) m,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have : NeZero m := ⟨by omega⟩
  let φ := signlessPreprojectiveLift (cyclePathAlgHom k f)
    (cyclePathAlgHom_signlessPreprojectiveRelator k hm f)
  let x := signlessPreprojectiveMk k (DoubledQuiver G) (ofPath ⟨_, _, cyclePath hm f m⟩)
  refine ⟨x, signlessPreprojectiveMk_mem_grade k _
    (ofPath_mem_grade_of_length (cyclePath_length hm f m)), fun hx => one_ne_zero (α := k) ?_⟩
  have htr := trace_map_eq_zero_of_mem_commutatorSubmodule φ hx
  have hm0 : Fin.ofNat m m = 0 := Fin.ext (by simp)
  have hfx : φ x = Matrix.single (0 : Fin m) 0 1 := by
    simpa only [φ, x, signlessPreprojectiveLift_signlessPreprojectiveMk, hm0] using
      cyclePathAlgHom_cyclePath k hm f m
  rw [hfx, Matrix.trace_single_eq_same] at htr
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
  let ψ := (cyclePathAlgHom k f).comp (orientationPathAlgebraEquiv o k).symm.toAlgHom
  let φ := preprojectiveLift ψ (cyclePathAlgHom_comp_orientation_preprojectiveRelator k hm f o)
  let p := orientationPathAlgebraEquiv o k (ofPath ⟨_, _, cyclePath hm f m⟩)
  let x := preprojectiveMk k (OrientedQuiver G o) p
  have hp : p ∈ grade k (Symmetrify (OrientedQuiver G o)) m := by
    dsimp only [p]
    rw [orientationPathAlgebraEquiv_ofPath]
    exact ofPath_mem_grade_of_length
      ((Prefunctor.length_mapTotalPath _ _).trans (cyclePath_length hm f m))
  refine ⟨x, preprojectiveMk_mem_preprojectiveGrade k _ hp, fun hx => one_ne_zero (α := k) ?_⟩
  have htr := trace_map_eq_zero_of_mem_commutatorSubmodule φ hx
  have hm0 : Fin.ofNat m m = 0 := Fin.ext (by simp)
  have hfx : φ x = Matrix.single (0 : Fin m) 0 1 := by
    simpa only [φ, ψ, x, p, preprojectiveLift_preprojectiveMk, AlgHom.comp_apply,
      AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply, hm0] using
      cyclePathAlgHom_cyclePath k hm f m
  rw [hfx, Matrix.trace_single_eq_same] at htr
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

end SimpleGraph.Coloring

namespace SimpleGraph.IsBipartite

open TauCeti TauCeti.DoubledQuiver

universe u w

variable {V : Type u} {G : SimpleGraph V}

/-- **For a bipartite graph, vanishing of a graded piece of the cyclic quotient agrees between the
signless algebra and the additive preprojective algebra of every orientation.** -/
theorem preprojectiveGrade_le_commutatorSubmodule_iff (hG : G.IsBipartite)
    (k : Type w) [CommRing k] [Finite V]
    [inst : ∀ i, Fintype (G.neighborSet i)] (o : Orientation G) (d : ℕ) :
    preprojectiveGrade k (OrientedQuiver G o) d ≤
        commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) ↔
      signlessPreprojectiveGrade k (DoubledQuiver G) d ≤
        commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  obtain rfl : inst = fun i => Fintype.ofFinite _ := Subsingleton.elim _ _
  let φ := hG.signlessPreprojectiveAlgebraEquiv k o
  constructor
  · intro hO x hx
    have hy := hO (hG.signlessPreprojectiveAlgebraEquiv_mem_preprojectiveGrade k o hx)
    simpa only [φ, AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule φ.symm hy
  · intro hS y hy
    have hx := hS (hG.signlessPreprojectiveAlgebraEquiv_symm_mem_signlessPreprojectiveGrade k o hy)
    simpa only [φ, AlgEquiv.apply_symm_apply] using map_mem_commutatorSubmodule φ hx

end SimpleGraph.IsBipartite
