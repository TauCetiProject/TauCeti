/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Quiver.Star
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
preprojective algebra (`TauCeti.RepresentationTheory.Quiver.Preprojective.Koszul.Complex`) only in
carrying no signs. For the doubled quiver of a finite simple graph `G` the signless algebra is the
quadratic dual of the quadratic zigzag presentation
(`TauCeti.quadraticDualQuadraticZigzagEquivSignless`), and so, when `G` is connected with at least
three vertices and that presentation is the zigzag algebra
(`TauCeti.quadraticZigzagPresentationEquivZigzagQuotient`), the quadratic dual of the zigzag
algebra of `G`. When `G` is bipartite the signless algebra is isomorphic to the
preprojective algebra of a source--sink orientation
(`TauCeti.symmetrifySignlessPreprojectiveAlgebraEquiv`), but when `G` is not bipartite and `2 ≠ 0`
in `k` it is a different algebra, and its Koszul complex must be treated on its own.

This file proves that the two maps compose to zero, that the complex is exact at its middle term,
and that the left-hand map is injective whenever `R` admits a **non-backtracking choice of arrows**:
an arrow `α_u` out of every vertex `u` such that the arrow chosen at the head of `α_u` is never the
reverse of `α_u`. For the doubled quiver of a graph `G` such a choice is a map `f` sending every
vertex to a neighbour with `f (f v) ≠ v`. Following `f` from any vertex eventually runs around a
cycle of `G`, so such an `f` exists only when every connected component of `G` contains a cycle;
conversely every such graph admits one. For the symmetrification of a bipartite quiver `Q`, the
comparison with `Π_k(Q)` carries vertex idempotents to vertex idempotents and arrows to signed
arrows, so left-end exactness of the preprojective Koszul complex gives that of the signless one.
Exactness at `e_v Π` itself, the statement that the classes of positive degree are the sums
`∑_b b z_b`, is not addressed here.

## Main results

* `TauCeti.signlessPreprojectiveRelator_eq_sum_ofArrow_mul`: the signless relator at `v` is
  `∑_{b : i ⟶ v} b b*`, decomposed along the last arrow of its paths.
* `TauCeti.sum_signlessPreprojectiveMk_ofArrow_mul_ofArrow_reverse_mul_eq_zero`: the two maps
  compose to zero.
* `TauCeti.sum_signlessPreprojectiveMk_ofArrow_mul_eq_zero_iff`: **exactness at the middle term.**
* `TauCeti.signlessPreprojectiveMk_ofArrow_mul_eq_zero_iff_of_ne_reverse`: for a
  non-backtracking choice of arrows `α`, left multiplication by `α_v` is injective on `e_v Π`.
* `TauCeti.forall_signlessPreprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_ne_reverse`:
  **exactness at the left end** for a non-backtracking choice of arrows.
* `TauCeti.forall_signlessPreprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_adj`: the same for
  the doubled quiver of a simple graph, given a neighbour map `f` with `f (f v) ≠ v`.
* `TauCeti.forall_signlessPreprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_bipartite`: the same
  for the symmetrification of a bipartite quiver `Q`, given left-end exactness for `Π_k(Q)`.

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
    (signlessPreprojectiveMk_signlessPreprojectiveRelator k) v y

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

/-- **An arrow of a non-backtracking choice acts injectively.** Let `σ` choose an arrow `α_u` out
of every vertex `u` of `R` such that the arrow chosen at the head of `α_u` is never the reverse of
`α_u`. Then for `y ∈ e_v Π`, `α_v y = 0` exactly when `y = 0`. -/
theorem signlessPreprojectiveMk_ofArrow_mul_eq_zero_iff_of_ne_reverse
    {σ : ∀ v : R, Quiver.Star v} (hσ : ∀ v, σ (σ v).1 ≠ Quiver.Star.mk (reverse (σ v).2)) (v : R)
    {y : signlessPreprojectiveAlgebra k R}
    (hy : signlessPreprojectiveMk k R (vertexIdempotent k v) * y = y) :
    signlessPreprojectiveMk k R (ofArrow (σ v).2) * y = 0 ↔ y = 0 := by
  -- Choose enumerations for the sums; the finite-star instance supplies finite arrow types.
  let := Fintype.ofFinite R
  let (i j : R) : Fintype (i ⟶ j) := Fintype.ofFinite _
  exact map_ofArrow_mul_eq_zero_iff_of_ne_reverse k (ε := fun _ _ _ => 1) hσ
    (fun _ => isUnit_one) (signlessPreprojectiveRelator_eq_sum_ofArrow_mul_smul k)
    (signlessPreprojectiveMk_eq_zero_iff_mem_span k R) (signlessPreprojectiveMk_surjective k R) v
    hy

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
  refine ⟨fun h => ?_, fun h i b => by rw [h, mul_zero]⟩
  refine (signlessPreprojectiveMk_ofArrow_mul_eq_zero_iff_of_ne_reverse k hσ v hy).1 ?_
  simpa only [reverse_reverse] using h _ (reverse (σ v).2)

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

section Bipartite

variable {Q : Type u} [Quiver.{v} Q] {c : Q → Bool}

/-- The colour sign of a doubled arrow squares to one. -/
private theorem doubledLabelling_colourSign_mul_self {x y : Symmetrify Q} (b : x ⟶ y) :
    doubledLabelling k (fun _ j _ => if c j then (1 : k) else -1) b *
      doubledLabelling k (fun _ j _ => if c j then (1 : k) else -1) b = 1 := by
  rw [← doubledLabelling_mul]
  have h : (fun (i j : Q) (_ : i ⟶ j) => (if c j then (1 : k) else -1) *
      (if c j then (1 : k) else -1)) = fun _ _ _ => 1 := by
    funext _ j _
    cases c j <;> simp
  rw [h, doubledLabelling_one]

variable [Fintype Q] [∀ i j : Q, Fintype (i ⟶ j)] (hc : ∀ ⦃i j : Q⦄, (i ⟶ j) → c i ≠ c j)

include hc in
/-- **Exactness of the Koszul complex at its left end, for a bipartite quiver.** Let `c` colour
the vertices of `Q` so that the two ends of every arrow have different colours. If the Koszul
complex of the preprojective algebra `Π_k(Q)` is exact at its left end at `v`, then so is the Koszul
complex of the signless algebra of `Quiver.Symmetrify Q`: for `y ∈ e_v Π`, `b* y = 0` for every
arrow `b` into `v` exactly when `y = 0`. The comparison isomorphism
`TauCeti.symmetrifySignlessPreprojectiveAlgebraEquiv` fixes the vertex idempotents and multiplies
every doubled arrow by a sign. -/
theorem forall_signlessPreprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_bipartite (v : Q)
    (hv : ∀ y : preprojectiveAlgebra k Q,
      preprojectiveMk k Q (doubledVertexIdempotent k v) * y = y →
        (∀ (i : Symmetrify Q) (b : i ⟶ Symmetrify.of.obj v),
          preprojectiveMk k Q (ofArrow (reverse b)) * y = 0) → y = 0)
    {y : signlessPreprojectiveAlgebra k (Symmetrify Q)}
    (hy : signlessPreprojectiveMk k _ (vertexIdempotent k (Symmetrify.of.obj v)) * y = y) :
    (∀ (i : Symmetrify Q) (b : i ⟶ Symmetrify.of.obj v),
      signlessPreprojectiveMk k _ (ofArrow (reverse b)) * y = 0) ↔ y = 0 := by
  refine ⟨fun h => ?_, fun h i b => by rw [h, mul_zero]⟩
  suffices symmetrifySignlessPreprojectiveAlgebraEquiv k hc y = 0 by
    rwa [map_eq_zero_iff _ (symmetrifySignlessPreprojectiveAlgebraEquiv k hc).injective] at this
  refine hv _ ?_ fun i b => ?_
  · have hE := congrArg (symmetrifySignlessPreprojectiveAlgebraEquiv k hc) hy
    rwa [map_mul, symmetrifySignlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk,
      rescale_vertexIdempotent, ← doubledVertexIdempotent_def] at hE
  · -- The comparison carries `b* y = 0` to `± b* y = 0`, and the sign is a unit.
    have hb := congrArg (symmetrifySignlessPreprojectiveAlgebraEquiv k hc) (h i b)
    rw [map_mul, symmetrifySignlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk_ofArrow,
      smul_mul_assoc, map_zero] at hb
    rw [← one_smul k (_ * _), ← doubledLabelling_colourSign_mul_self k (reverse b), mul_smul, hb,
      smul_zero]

end Bipartite

end TauCeti
