/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.FiniteDimensional
public import TauCeti.RepresentationTheory.Quiver.Preprojective.GradedResolution
public import TauCeti.RepresentationTheory.Quiver.Preprojective.HilbertSeries.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.HilbertSeries.FiniteDimensional
public import TauCeti.RepresentationTheory.Quiver.Preprojective.InfiniteDimensional
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Koszul.Superadditive

/-!
# Koszulity of the preprojective algebras of non-Dynkin quivers

Let `Π = Π_k(Q)` be the preprojective algebra of a finite quiver over a field `k`. The Koszul
complex of the vertex module `S_v`,

```text
0 ⟶ e_v Π ⟶ ⨁_{b : w ⟶ v} e_w Π ⟶ e_v Π ⟶ S_v ⟶ 0,
```

is exact except possibly at its left end, whose defect consists of the `y ∈ e_v Π` killed by every
arrow `b*` of the doubled quiver leaving `v`. A connected simple graph which is not a Dynkin
diagram carries, in every orientation, a **positive superadditive weight**: a weight `δ` on the
vertices of the oriented quiver with `δ_i > 0` and
`2 δ_i ≤ ∑_j (#(i ⟶ j) + #(j ⟶ i)) δ_j` at every vertex
(`TauCeti.exists_pos_two_mul_le_sum_orientedQuiver_of_not_exists_dynkinType_iso`). Such a weight
makes the quiver-level Koszul machinery of
`TauCeti.forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_two_mul_le_sum`
(`Koszul/Superadditive.lean`) exact, so for every orientation of a connected non-Dynkin graph,
trees such as `D~ₙ`, `E₆~`, `E₇~` and `E₈~` included, the Koszul complexes are projective
resolutions and the matrix Hilbert series of `Π` is `((1 + t²) I - t A)⁻¹`. This is the theorem of
Etingof and Eu; for orientations of graphs which are not trees it is already
`TauCeti.forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_not_isAcyclic`.

## Main results

* `TauCeti.exists_pos_two_mul_le_sum_orientedQuiver_of_not_exists_dynkinType_iso`: every
  orientation of a connected graph which is not a Dynkin diagram carries a positive superadditive
  weight on its oriented quiver.
* `TauCeti.forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_not_exists_dynkinType_iso`:
  **the Koszul complex of every vertex module of every such orientation is exact at its left
  end.**
* `TauCeti.preprojectiveKoszulLeft_injective_of_not_exists_dynkinType_iso`: injectivity of the
  bundled map.
* `TauCeti.isLinear_preprojectiveGradedKoszulResolution_of_not_exists_dynkinType_iso`: the graded
  Koszul complexes are then linear projective resolutions.
* `TauCeti.mul_preprojectiveHilbertSeries_eq_one_of_not_exists_dynkinType_iso` and
  `TauCeti.preprojectiveHilbertSeries_eq_inv_of_not_exists_dynkinType_iso`: **the matrix Hilbert
  series of the preprojective algebra of a connected non-Dynkin graph in every orientation is
  `((1 + t²) I - t A)⁻¹`.**

* `forall_preprojectiveKoszulLeft_injective_iff` and
  `forall_preprojectiveKoszulLeft_injective_iff_not_finiteDimensional`: **the Koszulity dichotomy
  for preprojective algebras of oriented graphs**: the left Koszul differential is injective at
  every vertex if and only if the graph is not a Dynkin diagram, and if and only if the
  preprojective algebra is infinite-dimensional.

## References

* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, Math.
  Res. Lett. 14 (2007), for the theorem.
* I. M. Gelfand and V. A. Ponomarev, *Model algebras and representations of graphs*, Funct. Anal.
  Appl. 13 (1979), where the preprojective algebra is introduced.
-/


public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

section Graph

open DoubledQuiver

attribute [local instance] Fintype.ofFinite

variable (k : Type w) [Field k] {V : Type u} {G : SimpleGraph V} [Finite V]
  (hG : G.Connected)
  (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix))
  (o : Orientation G)

include hG hD

/-- Every orientation of a connected non-Dynkin graph carries a positive weight on its oriented
quiver which is positive at every vertex and superadditive on its underlying multigraph. -/
theorem exists_pos_two_mul_le_sum_orientedQuiver_of_not_exists_dynkinType_iso :
    ∃ δ : OrientedQuiver G o → ℝ, (∀ i, 0 < δ i) ∧ ∀ i, 2 * δ i ≤
      ∑ j, ((Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i) : ℕ) : ℝ) * δ j := by
  classical
  obtain ⟨δ, hδ, hδle⟩ := SimpleGraph.exists_pos_two_mul_le_sum_of_not_exists_dynkinType_iso hG hD
  set e := OrientedQuiver.vertexEquiv G o
  refine ⟨fun i => δ (e.symm i), fun i => hδ _, fun i => ?_⟩
  obtain ⟨i, rfl⟩ := e.surjective i
  simp only [e, OrientedQuiver.vertexEquiv_apply, OrientedQuiver.vertexEquiv_symm_vertex]
  exact (hδle i).trans_eq (OrientedQuiver.sum_card_hom_add_card_hom_mul G o δ i).symm

/-- **Exactness of the Koszul complex at its left end, for a connected non-Dynkin graph.** Let `G`
be a connected finite simple graph which is not isomorphic to the diagram of any valid Dynkin type,
and `o` any orientation of `G`. If `y = e_v y` in the preprojective algebra of `o` over a field
`k`, then `b* y = 0` for every arrow `b` of the doubled quiver into `v` exactly when `y = 0`. This
covers the non-Dynkin trees, such as the affine diagrams `D~ₙ`, `E₆~`, `E₇~` and `E₈~`. -/
theorem forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_not_exists_dynkinType_iso
    (v : OrientedQuiver G o) {y : preprojectiveAlgebra k (OrientedQuiver G o)}
    (hy : preprojectiveMk k (OrientedQuiver G o) (doubledVertexIdempotent k v) * y = y) :
    (∀ (w : Symmetrify (OrientedQuiver G o)) (b : w ⟶ Symmetrify.of.obj v),
      preprojectiveMk k (OrientedQuiver G o) (ofArrow (Quiver.reverse b)) * y = 0) ↔ y = 0 := by
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_two_mul_le_sum_orientedQuiver_of_not_exists_dynkinType_iso
    hG hD o
  exact forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_two_mul_le_sum k hδ hδle v hy

/-- For every orientation of a connected non-Dynkin graph, the left Koszul differential at each
vertex is injective. -/
theorem preprojectiveKoszulLeft_injective_of_not_exists_dynkinType_iso (v : OrientedQuiver G o) :
    Function.Injective (preprojectiveKoszulLeft k v) := by
  obtain ⟨δ, hδ, hδle⟩ :=
    exists_pos_two_mul_le_sum_orientedQuiver_of_not_exists_dynkinType_iso hG hD o
  exact preprojectiveKoszulLeft_injective_of_two_mul_le_sum k hδ hδle v

/-- The right vertex module of every orientation of a connected non-Dynkin graph has a linear
graded Koszul resolution. Its projective terms are generated in internal degrees zero, one and two,
respectively, and all later terms vanish. -/
theorem isLinear_preprojectiveGradedKoszulResolution_of_not_exists_dynkinType_iso
    (v : OrientedQuiver G o) :
    (preprojectiveGradedKoszulResolution k v
      (preprojectiveKoszulLeft_injective_of_not_exists_dynkinType_iso k hG hD o v)).IsLinear :=
  isLinear_preprojectiveGradedKoszulResolution k v
    (preprojectiveKoszulLeft_injective_of_not_exists_dynkinType_iso k hG hD o v)

variable [DecidableEq (OrientedQuiver G o)]

/-- For every orientation of a connected non-Dynkin graph, `((1 + X²) I - X A) H = I`, where `A`
counts doubled arrows and `H` is the matrix Hilbert series of the preprojective algebra. -/
theorem mul_preprojectiveHilbertSeries_eq_one_of_not_exists_dynkinType_iso :
    (((1 : PowerSeries ℤ) + PowerSeries.X ^ 2) •
        (1 : Matrix (OrientedQuiver G o) (OrientedQuiver G o) (PowerSeries ℤ)) -
      (PowerSeries.X : PowerSeries ℤ) • Matrix.of fun v w : OrientedQuiver G o =>
        (Fintype.card (Symmetrify.of.obj w ⟶ Symmetrify.of.obj v) : PowerSeries ℤ)) *
      preprojectiveHilbertSeries k (OrientedQuiver G o) = 1 := by
  obtain ⟨δ, hδ, hδle⟩ :=
    exists_pos_two_mul_le_sum_orientedQuiver_of_not_exists_dynkinType_iso hG hD o
  exact mul_preprojectiveHilbertSeries_eq_one_of_two_mul_le_sum k hδ hδle

/-- **The Hilbert series of the preprojective algebra of a connected non-Dynkin graph.** For every
orientation of a connected finite simple graph which is not a Dynkin diagram, the matrix Hilbert
series of its preprojective algebra over any field is `((1 + X²) I - X A)⁻¹`. -/
theorem preprojectiveHilbertSeries_eq_inv_of_not_exists_dynkinType_iso :
    preprojectiveHilbertSeries k (OrientedQuiver G o) =
      (((1 : PowerSeries ℤ) + PowerSeries.X ^ 2) •
          (1 : Matrix (OrientedQuiver G o) (OrientedQuiver G o) (PowerSeries ℤ)) -
        (PowerSeries.X : PowerSeries ℤ) • Matrix.of fun v w : OrientedQuiver G o =>
          (Fintype.card (Symmetrify.of.obj w ⟶ Symmetrify.of.obj v) : PowerSeries ℤ))⁻¹ := by
  obtain ⟨δ, hδ, hδle⟩ :=
    exists_pos_two_mul_le_sum_orientedQuiver_of_not_exists_dynkinType_iso hG hD o
  exact preprojectiveHilbertSeries_eq_inv_of_two_mul_le_sum k hδ hδle

end Graph

section Dichotomy

open DoubledQuiver

variable (k : Type w) [Field k] {V : Type u} {G : SimpleGraph V} [Finite V]

/-- For a nonempty finite quiver whose preprojective algebra is finite-dimensional, the left Koszul
differential fails to be injective at some vertex. -/
theorem exists_not_preprojectiveKoszulLeft_injective_of_finiteDimensional
    {Q : Type*} [Quiver Q] [Fintype Q] [∀ i j : Q, Fintype (i ⟶ j)] [Nonempty Q]
    [FiniteDimensional k (preprojectiveAlgebra k Q)] :
    ∃ v : Q, ¬ Function.Injective (preprojectiveKoszulLeft k v) := by
  obtain ⟨v, y, hy, hb, hy0⟩ :=
    exists_ne_zero_forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero k Q
  exact ⟨v, fun h => hy0 ((preprojectiveKoszulLeft_injective_iff k v).1 h y hy hb)⟩

/-- **The Koszulity dichotomy for preprojective algebras of oriented graphs**: for a connected
finite simple graph `G` and any orientation `o` of `G`, the left Koszul differential of
`Π_k(OrientedQuiver G o)` is injective at every vertex if and only if `G` is not isomorphic to the
diagram of any valid Dynkin type. -/
theorem forall_preprojectiveKoszulLeft_injective_iff (hG : G.Connected) (o : Orientation G) :
    (∀ v : OrientedQuiver G o, Function.Injective (preprojectiveKoszulLeft k v)) ↔
      ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix) := by
  refine ⟨fun h ⟨_, _, ⟨e⟩⟩ => ?_,
    fun hD v => preprojectiveKoszulLeft_injective_of_not_exists_dynkinType_iso k hG hD o v⟩
  have _ : Nonempty V := hG.nonempty
  have _ : Nonempty (OrientedQuiver G o) := (OrientedQuiver.vertexEquiv G o).symm.nonempty
  have _ := finiteDimensional_preprojectiveAlgebra_of_iso k e o
  obtain ⟨v, hv⟩ :=
    exists_not_preprojectiveKoszulLeft_injective_of_finiteDimensional k (Q := OrientedQuiver G o)
  exact hv (h v)

/-- For a connected finite simple graph `G` and any orientation `o` of `G`, the left Koszul
differential of `Π_k(OrientedQuiver G o)` is injective at every vertex if and only if
`Π_k(OrientedQuiver G o)` is infinite-dimensional. -/
theorem forall_preprojectiveKoszulLeft_injective_iff_not_finiteDimensional
    (hG : G.Connected) (o : Orientation G) :
    (∀ v : OrientedQuiver G o, Function.Injective (preprojectiveKoszulLeft k v)) ↔
      ¬ FiniteDimensional k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  rw [forall_preprojectiveKoszulLeft_injective_iff k hG o,
    finiteDimensional_preprojectiveAlgebra_orientedQuiver_iff k hG o]

end Dichotomy

end TauCeti
