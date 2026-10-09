/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.BacktrackRelator
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Basic

/-!
# The Koszul complex of a vertex module of a signless preprojective algebra

Let `R` be a finite quiver with an involutive reversal of arrows, such as the doubled quiver of a
simple graph, and let `Π = Π^s_k(R)` be its signless preprojective algebra over a commutative ring
`k`, the quotient of the path algebra by the signless relators `s_v = ∑_{b : i ⟶ v} b b*`. For a
vertex `v` the Koszul complex of the vertex module `S_v` is

```text
0 ⟶ e_v Π ⟶ ⨁_{b : i ⟶ v} e_i Π ⟶ e_v Π ⟶ S_v ⟶ 0,
       y ↦ (b* y)_b,   (z_b) ↦ ∑_b b z_b,
```

the sum running over the arrows `b` of `R` into `v`. It differs from the Koszul complex of the
preprojective algebra (`TauCeti.RepresentationTheory.Quiver.Preprojective.KoszulComplex`) only in
carrying no signs. For the doubled quiver of a simple graph `G` the signless algebra is the
quadratic dual of the zigzag algebra of `G`; when `G` is bipartite it is isomorphic to the
preprojective algebra of a source--sink orientation
(`TauCeti.symmetrifySignlessPreprojectiveAlgebraEquiv`), but when `G` is not bipartite and `2 ≠ 0`
in `k` it is a different algebra, and its Koszul complex must be treated on its own.

This file proves that the two maps compose to zero, that the complex is exact at its middle term,
and that the left-hand map is injective whenever `R` admits a **non-backtracking choice of arrows**:
an arrow `α_u` out of every vertex `u` such that the arrow chosen at the head of `α_u` is never the
reverse of `α_u`. For the doubled quiver of a graph `G` such a choice is a map `f` sending every
vertex to a neighbour with `f (f v) ≠ v`. Following `f` from any vertex eventually runs around a
cycle of `G`, so such an `f` exists only when every connected component of `G` contains a cycle;
conversely every such graph admits one. Exactness at `e_v Π` itself, the statement that the classes
of positive degree are the sums `∑_b b z_b`, is not addressed here.

## Main results

* `TauCeti.signlessPreprojectiveRelator_eq_sum_ofArrow_mul`: the signless relator at `v` is
  `∑_{b : i ⟶ v} b b*`, decomposed along the last arrow of its paths.
* `TauCeti.sum_signlessPreprojectiveMk_ofArrow_mul_ofArrow_reverse_mul_eq_zero`: the two maps
  compose to zero.
* `TauCeti.sum_signlessPreprojectiveMk_ofArrow_mul_eq_zero_iff`: **exactness at the middle term.**
* `TauCeti.forall_signlessPreprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_ne_reverse`:
  **exactness at the left end** for a non-backtracking choice of arrows.
* `TauCeti.forall_signlessPreprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_adj`: the same for
  the doubled quiver of a simple graph, given a neighbour map `f` with `f (f v) ≠ v`.

## References

* S. Huerfano and M. Khovanov, *A category for the adjoint representation*, J. Algebra 246 (2001),
  Section 3, for the signless relation of the quadratic dual of the zigzag algebra.
* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, Math.
  Res. Lett. 14 (2007), Sections 2 and 3, for the Koszul complex of a vertex module.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

variable (k : Type w) {R : Type u} [CommRing k] [Quiver.{v} R] [HasInvolutiveReverse R]
  [∀ x : R, Fintype (Quiver.Star x)]

section Finite

variable [Finite R]

variable (R) in
/-- `signlessPreprojectiveMk` presents the signless algebra as the quotient by the ideal its
relators generate, in the form taken by the weighted backtrack relators of
`TauCeti.RepresentationTheory.Quiver.PathAlgebra.BacktrackRelator` with all weights `1`. -/
private theorem signlessPreprojectiveMk_eq_zero_iff_mem_span (f : pathAlgebra k R) :
    signlessPreprojectiveMk k R f = 0 ↔
      f ∈ TwoSidedIdeal.span (Set.range fun v : R => signlessPreprojectiveRelator k v) := by
  rw [signlessPreprojectiveMk_eq_zero_iff, signlessPreprojectiveIdeal_eq_span]

end Finite

section Fintype

variable [Fintype R] [∀ i j : R, Fintype (i ⟶ j)]

/-- **The signless relator along the last arrow of its paths**: in the later-factor-first
convention `s_v = ∑_{b : i ⟶ v} b b*`, the sum over the arrows of `R` into `v`. -/
theorem signlessPreprojectiveRelator_eq_sum_ofArrow_mul (v : R) :
    signlessPreprojectiveRelator k v = ∑ i, ∑ b : i ⟶ v, ofArrow b * ofArrow (reverse b) := by
  -- Reindex the arrows `e` out of `v` by their reverses `e*` into `v`.
  rw [signlessPreprojectiveRelator_def, ← Fintype.sum_sigma (fun s : Costar v =>
      (ofArrow s.2 * ofArrow (reverse s.2) : pathAlgebra k R)),
    ← (starEquivCostar v).sum_comp]
  refine Fintype.sum_congr _ _ fun e => ?_
  rw [← ofPath_mul_ofPath_of_comp, ← ofArrow_eq_ofPath, ← ofArrow_eq_ofPath]
  exact congrArg (ofArrow (reverse e.2) * ·) (congrArg ofArrow (reverse_reverse e.2)).symm

/-- The signless relator as a weighted backtrack relator with all weights `1`. -/
private theorem signlessPreprojectiveRelator_eq_sum_ofArrow_mul_smul (v : R) :
    signlessPreprojectiveRelator k v =
      ∑ i, ∑ b : i ⟶ v, ofArrow b * ((1 : k) • ofArrow (reverse b)) := by
  simp only [one_smul, signlessPreprojectiveRelator_eq_sum_ofArrow_mul]

/-- **The Koszul complex is a complex**: the composite `y ↦ ∑_b b (b* y)` is left multiplication by
the signless relator `s_v`, which vanishes in the signless algebra. -/
theorem sum_signlessPreprojectiveMk_ofArrow_mul_ofArrow_reverse_mul_eq_zero (v : R)
    (y : signlessPreprojectiveAlgebra k R) :
    ∑ i, ∑ b : i ⟶ v, signlessPreprojectiveMk k R (ofArrow b) *
      (signlessPreprojectiveMk k R (ofArrow (reverse b)) * y) = 0 := by
  simpa only [one_smul] using sum_map_ofArrow_mul_smul_map_ofArrow_reverse_mul_eq_zero k
    (ε := fun _ _ _ => 1) (signlessPreprojectiveRelator_eq_sum_ofArrow_mul_smul k)
    (signlessPreprojectiveMk_eq_zero_iff_mem_span k R) v y

/-- **Exactness of the Koszul complex at its middle term.** Let `z_b ∈ e_i Π` for the arrows
`b : i ⟶ v` of `R`. Then `∑_b b z_b = 0` exactly when there is one `y ∈ e_v Π` with `z_b = b* y` for
every `b`. -/
theorem sum_signlessPreprojectiveMk_ofArrow_mul_eq_zero_iff (v : R)
    {z : (i : R) → (i ⟶ v) → signlessPreprojectiveAlgebra k R}
    (hz : ∀ i b, signlessPreprojectiveMk k R (vertexIdempotent k i) * z i b = z i b) :
    ∑ i, ∑ b, signlessPreprojectiveMk k R (ofArrow b) * z i b = 0 ↔
      ∃ y, signlessPreprojectiveMk k R (vertexIdempotent k v) * y = y ∧
        ∀ i b, z i b = signlessPreprojectiveMk k R (ofArrow (reverse b)) * y := by
  simpa only [one_smul] using sum_map_ofArrow_mul_eq_zero_iff k (ε := fun _ _ _ => 1)
    (signlessPreprojectiveRelator_eq_sum_ofArrow_mul_smul k)
    (signlessPreprojectiveMk_eq_zero_iff_mem_span k R) (signlessPreprojectiveMk_surjective k R) v
    hz

end Fintype

section LeftEnd

variable [Finite R]

/-- **Exactness of the Koszul complex at its left end, for a non-backtracking choice of arrows.**
Let `σ` choose an arrow `α_u` out of every vertex `u` of `R` such that the arrow chosen at the head
of `α_u` is never the reverse of `α_u`. Then for `y ∈ e_v Π`, `b* y = 0` for every arrow `b` into
`v` exactly when `y = 0`: the map `y ↦ (b* y)_b` is injective. -/
theorem forall_signlessPreprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_ne_reverse
    {σ : ∀ v : R, Quiver.Star v} (hσ : ∀ v, σ (σ v).1 ≠ Quiver.Star.mk (reverse (σ v).2)) (v : R)
    {y : signlessPreprojectiveAlgebra k R}
    (hy : signlessPreprojectiveMk k R (vertexIdempotent k v) * y = y) :
    (∀ (i : R) (b : i ⟶ v), signlessPreprojectiveMk k R (ofArrow (reverse b)) * y = 0) ↔
      y = 0 := by
  -- The sums over arrows in the relators need finitely many vertices and arrows; the arrows
  -- `i ⟶ j` embed in the finite star at `i`.
  let := Fintype.ofFinite R
  have (i j : R) : Finite (i ⟶ j) :=
    Finite.of_injective (fun e : i ⟶ j => (Quiver.Star.mk e : Quiver.Star i)) sigma_mk_injective
  let (i j : R) : Fintype (i ⟶ j) := Fintype.ofFinite _
  exact forall_map_ofArrow_reverse_mul_eq_zero_iff_of_ne_reverse k (ε := fun _ _ _ => 1) hσ
    (fun _ => isUnit_one) (signlessPreprojectiveRelator_eq_sum_ofArrow_mul_smul k)
    (signlessPreprojectiveMk_eq_zero_iff_mem_span k R) (signlessPreprojectiveMk_surjective k R) v
    hy

/-- **Exactness of the Koszul complex at its left end, for a graph.** Let `G` be a finite simple
graph and `f` a map sending every vertex to a neighbour, with `f (f v) ≠ v` for every `v`. Then in
the signless algebra of the doubled quiver of `G`, for `y ∈ e_v Π`, `b* y = 0` for every arrow `b`
into `v` exactly when `y = 0`. -/
theorem forall_signlessPreprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_adj {V : Type*}
    [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {f : V → V} (hf : ∀ v, G.Adj v (f v))
    (hff : ∀ v, f (f v) ≠ v) (v : V) {y : signlessPreprojectiveAlgebra k (DoubledQuiver G)}
    (hy : signlessPreprojectiveMk k _ (vertexIdempotent k (DoubledQuiver.vertex G v)) * y = y) :
    (∀ (i : DoubledQuiver G) (b : i ⟶ DoubledQuiver.vertex G v),
      signlessPreprojectiveMk k _ (ofArrow (reverse b)) * y = 0) ↔ y = 0 := by
  -- Choose at every vertex the arrow to its image under `f`.
  let σ : ∀ x : DoubledQuiver G, Quiver.Star x := fun x =>
    ⟨DoubledQuiver.vertex G (f ((DoubledQuiver.vertexEquiv G).symm x)), ⟨by
      simpa only [DoubledQuiver.vertexEquiv_symm_vertex] using
        hf ((DoubledQuiver.vertexEquiv G).symm x)⟩⟩
  -- The head of the arrow chosen at the head of `x ⟶ f x` is `f (f x) ≠ x`.
  have hσ : ∀ x, σ (σ x).1 ≠ Quiver.Star.mk (reverse (σ x).2) := fun x h => by
    have := congrArg (DoubledQuiver.vertexEquiv G).symm (congrArg Sigma.fst h)
    simp only [σ, DoubledQuiver.vertexEquiv_symm_vertex] at this
    exact hff _ this
  exact forall_signlessPreprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_ne_reverse k hσ _ hy

end LeftEnd

end TauCeti
