/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Basic
public import TauCeti.RepresentationTheory.Quiver.Representation.AsModule

/-!
# The moment map of a representation of a doubled quiver

A representation `M` of the doubled quiver `Quiver.Symmetrify Q` assigns to every arrow
`a : i ⟶ j` of `Q` a linear map `x_a : M_i → M_j`, and to its formal reverse a linear map
`x_{a*} : M_j → M_i`. Its **moment map** at a vertex `v` is the endomorphism

```text
μ_v(M) = ∑_{head a = v} x_a x_{a*} - ∑_{tail a = v} x_{a*} x_a   of M_v,
```

and summed over the vertices it is the commutator expression `μ(M) = ∑_a [x_a, x_{a*}]` acting on
`⨁_v M_v`. This file compares that formula with the preprojective relation: the preprojective
relator `ρ = ∑_a (a a* - a* a)` of the path algebra acts on the module `⨁_v M_v` carried by `M` as
`μ(M)`, and its local relator `ρ_v` acts as `μ_v(M)` on the summand `M_v`. Consequently the action
of the doubled path algebra on `⨁_v M_v` factors through the preprojective algebra `Π_k(Q)` exactly
when the moment map vanishes at every vertex, and a representation in the zero fibre of the moment
map therefore makes `⨁_v M_v` a module over `Π_k(Q)`. No converse construction of a doubled-quiver
representation from a `Π_k(Q)`-module, and no equivalence of categories, is established here. The
comparison is purely algebraic: no representation space or quotient by a group action is
constructed.

The products are read in Tau Ceti's later-factor-first convention, in which `a a*` is the loop at
the head of `a` that traverses `a*` first; so the head term of `μ_v` is the composite `x_a ∘ x_{a*}`
of linear maps.

## Main definitions

* `TauCeti.QuiverRep.momentMap`: the moment map `μ_v(M)` of a representation of the doubled quiver
  at a vertex.
* `TauCeti.QuiverRep.preprojectiveToEnd`: the action of `Π_k(Q)` on `⨁_v M_v` carried by a
  representation of the doubled quiver whose moment map vanishes.

## Main results

* `TauCeti.QuiverRep.toEnd_localPreprojectiveRelator`: the local relator `ρ_v` acts as `μ_v(M)` on
  the summand `M_v` and as zero on the other summands.
* `TauCeti.QuiverRep.toEnd_preprojectiveRelator`: the global relator acts as the sum of the vertex
  moment maps.
* `TauCeti.QuiverRep.toEnd_preprojectiveRelator_eq_sum_lie`: the commutator formula
  `ρ ↦ ∑_a [x_a, x_{a*}]`.
* `TauCeti.QuiverRep.toEnd_preprojectiveRelator_eq_zero_iff`: the global relator acts as zero
  exactly when the moment map vanishes at every vertex.
* `TauCeti.QuiverRep.exists_algHom_comp_preprojectiveMk_eq_toEnd_iff`: **the action of the
  doubled path algebra factors through `Π_k(Q)` exactly when the moment map vanishes.**

## References

See W. Crawley-Boevey, *Geometry of the moment map for representations of quivers*, Compositio
Math. 126 (2001), and W. Crawley-Boevey, *Quiver algebras, weighted projective lines,
and the Deligne--Simpson problem*, ICM 2006, Section 1, for the moment map and the identification
of `Π_k(Q)`-modules with its zero fibre.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w t

namespace QuiverRep

variable (k : Type u) {Q : Type v} [Field k] [Quiver.{w + 1} Q]
variable (M : QuiverRep.{u, v, w + 1, t} k (Symmetrify Q))

/-! ### Loops of the doubled quiver acting on a representation -/

section Backtrack

variable [Finite Q] [DecidableEq Q]

/-- A loop of the doubled quiver at `v` acts on `⨁_u M_u` through the summand `M_v` only. -/
private theorem toEnd_ofPath_loop {v : Symmetrify Q} (p : Path v v) :
    toEnd k (Symmetrify Q) M (ofPath ⟨v, v, p⟩) =
      DirectSum.lof k (Symmetrify Q) (vertexSpace k (Symmetrify Q) M) v ∘ₗ
        mapₗ k (Symmetrify Q) M p ∘ₗ
          DirectSum.component k (Symmetrify Q) (vertexSpace k (Symmetrify Q) M) v := by
  rw [toEnd_ofPath]
  exact LinearMap.ext fun z => pathEnd_mk_apply k (Symmetrify Q) M p z

/-- The head backtrack `a a*` of an arrow `a : i ⟶ j` acts on the summand `M_j` as `x_a x_{a*}`. -/
private theorem toEnd_headBacktrackElem {i j : Q} (a : i ⟶ j) :
    toEnd k (Symmetrify Q) M (headBacktrackElem k a) =
      DirectSum.lof k (Symmetrify Q) (vertexSpace k (Symmetrify Q) M) (Symmetrify.of.obj j) ∘ₗ
        (mapₗ k (Symmetrify Q) M (Symmetrify.of.map a).toPath ∘ₗ
          mapₗ k (Symmetrify Q) M (Quiver.reverse (Symmetrify.of.map a)).toPath) ∘ₗ
          DirectSum.component k (Symmetrify Q) (vertexSpace k (Symmetrify Q) M)
            (Symmetrify.of.obj j) := by
  rw [headBacktrackElem_def, toEnd_ofPath_loop, mapₗ_comp]

/-- The tail backtrack `a* a` of an arrow `a : i ⟶ j` acts on the summand `M_i` as `x_{a*} x_a`. -/
private theorem toEnd_tailBacktrackElem {i j : Q} (a : i ⟶ j) :
    toEnd k (Symmetrify Q) M (tailBacktrackElem k a) =
      DirectSum.lof k (Symmetrify Q) (vertexSpace k (Symmetrify Q) M) (Symmetrify.of.obj i) ∘ₗ
        (mapₗ k (Symmetrify Q) M (Quiver.reverse (Symmetrify.of.map a)).toPath ∘ₗ
          mapₗ k (Symmetrify Q) M (Symmetrify.of.map a).toPath) ∘ₗ
          DirectSum.component k (Symmetrify Q) (vertexSpace k (Symmetrify Q) M)
            (Symmetrify.of.obj i) := by
  rw [tailBacktrackElem_def, toEnd_ofPath_loop, mapₗ_comp]

end Backtrack

variable [Fintype Q] [∀ i j : Q, Fintype (i ⟶ j)]

/-! ### The moment map at a vertex -/

/-- The **moment map** of a representation `M` of the doubled quiver at a vertex `v` of `Q`: the
endomorphism `∑_{head a = v} x_a x_{a*} - ∑_{tail a = v} x_{a*} x_a` of the vertex space `M_v`,
where `x_a` and `x_{a*}` are the linear maps of `M` along an arrow `a` of `Q` and along its formal
reverse. -/
noncomputable def momentMap (v : Q) :
    Module.End k (vertexSpace k (Symmetrify Q) M (Symmetrify.of.obj v)) :=
  (∑ i : Q, ∑ a : (i ⟶ v), mapₗ k (Symmetrify Q) M (Symmetrify.of.map a).toPath ∘ₗ
      mapₗ k (Symmetrify Q) M (Quiver.reverse (Symmetrify.of.map a)).toPath) -
    ∑ j : Q, ∑ a : (v ⟶ j), mapₗ k (Symmetrify Q) M (Quiver.reverse (Symmetrify.of.map a)).toPath ∘ₗ
      mapₗ k (Symmetrify Q) M (Symmetrify.of.map a).toPath

/-- The moment map at a vertex, by its defining sum. -/
theorem momentMap_def (v : Q) :
    momentMap k M v =
      (∑ i : Q, ∑ a : (i ⟶ v), mapₗ k (Symmetrify Q) M (Symmetrify.of.map a).toPath ∘ₗ
          mapₗ k (Symmetrify Q) M (Quiver.reverse (Symmetrify.of.map a)).toPath) -
        ∑ j : Q, ∑ a : (v ⟶ j),
          mapₗ k (Symmetrify Q) M (Quiver.reverse (Symmetrify.of.map a)).toPath ∘ₗ
            mapₗ k (Symmetrify Q) M (Symmetrify.of.map a).toPath := by
  rw [momentMap]

/-! ### The action of the preprojective relators -/

variable [DecidableEq Q]

/-- **The local preprojective relator acts as the moment map**: `ρ_v` acts on `⨁_u M_u` as
`μ_v(M)` on the summand `M_v` and as zero on every other summand. -/
theorem toEnd_localPreprojectiveRelator (v : Q) :
    toEnd k (Symmetrify Q) M (localPreprojectiveRelator k v) =
      DirectSum.lof k (Symmetrify Q) (vertexSpace k (Symmetrify Q) M) (Symmetrify.of.obj v) ∘ₗ
        momentMap k M v ∘ₗ
          DirectSum.component k (Symmetrify Q) (vertexSpace k (Symmetrify Q) M)
            (Symmetrify.of.obj v) := by
  refine LinearMap.ext fun z => ?_
  simp only [localPreprojectiveRelator_def, momentMap_def, map_sub, map_sum,
    toEnd_headBacktrackElem, toEnd_tailBacktrackElem, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.comp_apply]

/-- **The global preprojective relator acts as the moment map**: `ρ` acts on `⨁_v M_v` as the sum
over the vertices of the moment maps `μ_v(M)`, each on its own summand. -/
theorem toEnd_preprojectiveRelator :
    toEnd k (Symmetrify Q) M (preprojectiveRelator k Q) =
      ∑ v : Q,
        DirectSum.lof k (Symmetrify Q) (vertexSpace k (Symmetrify Q) M) (Symmetrify.of.obj v) ∘ₗ
          momentMap k M v ∘ₗ
            DirectSum.component k (Symmetrify Q) (vertexSpace k (Symmetrify Q) M)
              (Symmetrify.of.obj v) := by
  rw [← sum_localPreprojectiveRelator, map_sum]
  exact Finset.sum_congr rfl fun v _ => toEnd_localPreprojectiveRelator k M v

/-- **The commutator formula for the moment map**: the global preprojective relator acts on
`⨁_v M_v` as `∑_a [x_a, x_{a*}]`, where `x_a` and `x_{a*}` are the actions of an arrow `a` of `Q`
and of its formal reverse. -/
theorem toEnd_preprojectiveRelator_eq_sum_lie :
    toEnd k (Symmetrify Q) M (preprojectiveRelator k Q) =
      ∑ i : Q, ∑ j : Q, ∑ a : (i ⟶ j),
        ⁅toEnd k (Symmetrify Q) M (ofArrow (Symmetrify.of.map a)),
          toEnd k (Symmetrify Q) M (ofArrow (Quiver.reverse (Symmetrify.of.map a)))⁆ := by
  simp only [preprojectiveRelator_def, map_sum, map_sub, Ring.lie_def, ← map_mul,
    ofArrow_mul_ofArrow_reverse_eq_headBacktrackElem,
    ofArrow_reverse_mul_ofArrow_eq_tailBacktrackElem]

/-- **The preprojective relation holds in a representation exactly when its moment map vanishes**:
the global relator acts as zero on `⨁_v M_v` if and only if `μ_v(M) = 0` at every vertex `v`. -/
theorem toEnd_preprojectiveRelator_eq_zero_iff :
    toEnd k (Symmetrify Q) M (preprojectiveRelator k Q) = 0 ↔ ∀ v : Q, momentMap k M v = 0 := by
  refine ⟨fun h v => ?_, fun h => by simp [toEnd_preprojectiveRelator, h]⟩
  -- the local relator is the corner of the global one, so it too acts as zero
  have hv : toEnd k (Symmetrify Q) M (localPreprojectiveRelator k v) = 0 := by
    rw [← preprojectiveRelator_vertexCorner_eq_localPreprojectiveRelator, map_mul, map_mul, h,
      mul_zero, zero_mul]
  rw [toEnd_localPreprojectiveRelator] at hv
  refine LinearMap.ext fun z => ?_
  have hz := congrArg (DirectSum.component k (Symmetrify Q) (vertexSpace k (Symmetrify Q) M)
    (Symmetrify.of.obj v)) (LinearMap.congr_fun hv
      (DirectSum.lof k (Symmetrify Q) (vertexSpace k (Symmetrify Q) M) (Symmetrify.of.obj v) z))
  simpa only [LinearMap.comp_apply, DirectSum.component.lof_self, LinearMap.zero_apply,
    map_zero] using hz

/-! ### Representations in the zero fibre are modules over the preprojective algebra -/

/-- The action of the preprojective algebra `Π_k(Q)` on `⨁_v M_v` carried by a representation of
the doubled quiver whose moment map vanishes at every vertex: the action
`TauCeti.QuiverRep.toEnd` of the doubled path algebra, which then kills the preprojective
relation, descended to the quotient. -/
noncomputable def preprojectiveToEnd (hM : ∀ v : Q, momentMap k M v = 0) :
    preprojectiveAlgebra k Q →ₐ[k]
      Module.End k (DirectSum (Symmetrify Q) (vertexSpace k (Symmetrify Q) M)) :=
  preprojectiveLift (toEnd k (Symmetrify Q) M)
    ((toEnd_preprojectiveRelator_eq_zero_iff k M).2 hM)

/-- The class of a doubled path acts on `⨁_v M_v` as the path itself does. -/
@[simp]
theorem preprojectiveToEnd_preprojectiveMk (hM : ∀ v : Q, momentMap k M v = 0)
    (x : pathAlgebra k (Symmetrify Q)) :
    preprojectiveToEnd k M hM (preprojectiveMk k Q x) = toEnd k (Symmetrify Q) M x :=
  preprojectiveLift_preprojectiveMk _ _ x

/-- The action of `Π_k(Q)` is the action of the doubled path algebra, descended along the
quotient map. -/
theorem preprojectiveToEnd_comp_preprojectiveMk (hM : ∀ v : Q, momentMap k M v = 0) :
    (preprojectiveToEnd k M hM).comp (preprojectiveMk k Q) = toEnd k (Symmetrify Q) M :=
  preprojectiveLift_comp_preprojectiveMk _ _

/-- **The path-algebra action factors through `Π_k(Q)` exactly on the zero fibre of the moment
map**: the action of the doubled path algebra on `⨁_v M_v` carried by `M` factors through the
quotient map onto `Π_k(Q)` if and only if the moment map of `M` vanishes at every vertex. -/
theorem exists_algHom_comp_preprojectiveMk_eq_toEnd_iff :
    (∃ g : preprojectiveAlgebra k Q →ₐ[k]
        Module.End k (DirectSum (Symmetrify Q) (vertexSpace k (Symmetrify Q) M)),
        g.comp (preprojectiveMk k Q) = toEnd k (Symmetrify Q) M) ↔
      ∀ v : Q, momentMap k M v = 0 := by
  refine ⟨fun ⟨g, hg⟩ => ?_, fun hM => ⟨_, preprojectiveToEnd_comp_preprojectiveMk k M hM⟩⟩
  rw [← toEnd_preprojectiveRelator_eq_zero_iff, ← hg, AlgHom.comp_apply,
    preprojectiveMk_preprojectiveRelator, map_zero]

end QuiverRep

end TauCeti
