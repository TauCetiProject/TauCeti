/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.BacktrackRelator
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Basic

/-!
# Preprojective algebras of quivers without sinks

Let `Q` be a finite quiver without sinks, that is, every vertex is the tail of an arrow of `Q`, and
let `Π = Π_k(Q)` be its preprojective algebra over a commutative ring `k`. This file proves that
for every arrow `a : v ⟶ w` of `Q`, left multiplication by `a` is injective on `e_v Π`.

Consequently the left-hand map `y ↦ (ε_b b* y)_b` of the Koszul complex

```text
0 ⟶ e_v Π ⟶ ⨁_{b : i ⟶ v} e_i Π ⟶ e_v Π ⟶ S_v ⟶ 0
```

of `TauCeti.RepresentationTheory.Quiver.Preprojective.KoszulComplex` is injective. Together with
the exactness at the other terms proved there, the complex is a projective resolution of the vertex
module `S_v`, for every vertex `v` and every commutative ring `k`.

The hypothesis is on the orientation, while `Π` does not depend on the orientation up to
isomorphism (`TauCeti.reorientPreprojectiveAlgebraEquiv`). A connected graph admits an orientation
without sinks exactly when it is not a tree, so the non-Dynkin trees, such as `D~ₙ` and `E₆~`,
`E₇~`, `E₈~`, are not covered here.

## Main results

* `TauCeti.preprojectiveMk_ofArrow_mul_eq_zero_iff`: for `y ∈ e_v Π` and an arrow `a` of `Q` out of
  `v`, `a y = 0` exactly when `y = 0`.
* `TauCeti.forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff`: **exactness of the Koszul
  complex at its left end**: `b* y = 0` for every arrow `b` of the doubled quiver into `v` exactly
  when `y = 0`.

## Implementation notes

The local preprojective relators are weighted backtrack relators with the signs
`TauCeti.doubledArrowSign`, and a choice of an arrow of `Q` out of every vertex is non-backtracking
in the doubled quiver, since no arrow of `Q` is the reverse of one. Both results are therefore
instances of `TauCeti.PathAlgebra.map_ofArrow_mul_eq_zero_iff_of_ne_reverse`, which builds a
faithful module from the rewriting rules solving each local relation for one backtrack.

## References

* G. M. Bergman, *The diamond lemma for ring theory*, Adv. Math. 29 (1978), for the construction of
  a module from a rewriting system without ambiguities.
* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, Math.
  Res. Lett. 14 (2007), Sections 2 and 3, for the Koszul complex and the Koszulity of the
  preprojective algebras of non-Dynkin quivers.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- **An arrow of a quiver without sinks acts injectively on `e_v Π`.** If every vertex of `Q` is
the tail of an arrow, `a : v ⟶ w` is an arrow of `Q` and `y = e_v y`, then `a y = 0` exactly when
`y = 0`. -/
theorem preprojectiveMk_ofArrow_mul_eq_zero_iff (hQ : ∀ u : Q, ∃ w, Nonempty (u ⟶ w)) {v w : Q}
    (a : v ⟶ w) {y : preprojectiveAlgebra k Q}
    (hy : preprojectiveMk k Q (doubledVertexIdempotent k v) * y = y) :
    preprojectiveMk k Q (ofArrow (Symmetrify.of.map a)) * y = 0 ↔ y = 0 := by
  classical
  -- Choose an outgoing arrow of `Q` at every vertex, taking `a` at `v`, and read the choice in the
  -- doubled quiver.
  let σ : ∀ u : Q, Σ w : Q, (u ⟶ w) :=
    Function.update (fun u => ⟨(hQ u).choose, (hQ u).choose_spec.some⟩) v ⟨w, a⟩
  let τ : ∀ x : Symmetrify Q, Quiver.Star x := fun x =>
    Quiver.Star.mk (Symmetrify.of.map (V := Q) (σ x).2)
  -- No arrow of `Q` is the reverse of one, so the choice is non-backtracking.
  have hτ : ∀ x, τ (τ x).1 ≠ Quiver.Star.mk (reverse (τ x).2) := fun x h => by
    have := congrArg (fun s : Quiver.Star (τ x).1 => Sum.isLeft s.2) h
    exact Bool.noConfusion (this : true = false)
  have hε : ∀ x, IsUnit (doubledArrowSign k (reverse (τ x).2)) := fun x => by
    have h1 : doubledArrowSign k (τ x).2 = 1 := doubledArrowSign_inl k (σ x).2
    rw [doubledArrowSign_reverse, h1]
    exact isUnit_one.neg
  have hπ : ∀ f, preprojectiveMk k Q f = 0 ↔
      f ∈ TwoSidedIdeal.span (Set.range (localPreprojectiveRelator k (Q := Q))) := fun f => by
    rw [preprojectiveMk_eq_zero_iff, preprojectiveIdeal_eq_span_range_localPreprojectiveRelator]
  have hy' : preprojectiveMk k Q (vertexIdempotent k (Symmetrify.of.obj (V := Q) v)) * y = y := by
    rwa [← doubledVertexIdempotent_def]
  have key := map_ofArrow_mul_eq_zero_iff_of_ne_reverse (R := Symmetrify Q) k hτ hε
    (r := localPreprojectiveRelator k (Q := Q))
    (fun u => localPreprojectiveRelator_eq_sum_ofArrow_mul (Q := Q) k u) hπ
    (preprojectiveMk_surjective k Q) (Symmetrify.of.obj (V := Q) v) hy'
  -- The chosen arrow at `v` is `a`, read in the doubled quiver.
  have hσ : σ v = ⟨w, a⟩ := Function.update_self ..
  have ha : ∀ s : Σ w : Q, (v ⟶ w), s = ⟨w, a⟩ →
      (ofArrow (Symmetrify.of.map s.2) : pathAlgebra k (Symmetrify Q)) =
        ofArrow (Symmetrify.of.map a) := by
    rintro _ rfl
    rfl
  rw [← key]
  exact Iff.of_eq (congrArg (fun f => preprojectiveMk k Q f * y = 0) (ha (σ v) hσ).symm)

/-- **Exactness of the Koszul complex at its left end, for a quiver without sinks.** If every vertex
of `Q` is the tail of an arrow and `y = e_v y`, then `b* y = 0` for every arrow `b` of the doubled
quiver into `v` exactly when `y = 0`: the map `y ↦ (ε_b b* y)_b` of
`TauCeti.sum_preprojectiveMk_ofArrow_mul_eq_zero_iff` is injective. -/
theorem forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff
    (hQ : ∀ u : Q, ∃ w, Nonempty (u ⟶ w)) (v : Q) {y : preprojectiveAlgebra k Q}
    (hy : preprojectiveMk k Q (doubledVertexIdempotent k v) * y = y) :
    (∀ (i : Symmetrify Q) (b : i ⟶ Symmetrify.of.obj v),
      preprojectiveMk k Q (ofArrow (Quiver.reverse b)) * y = 0) ↔ y = 0 := by
  refine ⟨fun h => ?_, fun h i b => by rw [h, mul_zero]⟩
  obtain ⟨w, ⟨a⟩⟩ := hQ v
  refine (preprojectiveMk_ofArrow_mul_eq_zero_iff k hQ a hy).1 ?_
  simpa only [reverse_reverse] using h _ (Quiver.reverse (Symmetrify.of.map a))

end TauCeti
