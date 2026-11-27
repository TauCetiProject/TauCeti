/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Torus
import TauCeti.Analysis.Complex.Circle.Torsion

/-!
# Points of finite order are dense in a torus

A torus `T` of a Lie group `G`, a compact connected commutative Lie subgroup, is isomorphic as a
topological group to a finite power of the circle
(`TauCeti.Lie.IsTorus.nonempty_continuousMulEquiv_pi_circle`). In a finite power of the circle the
points of finite order are dense (`Circle.dense_setOf_isOfFinOrder_pi`), so the same holds in `T`:
every point of `T` is a limit of points of `T` of finite order
(`TauCeti.Lie.IsTorus.subset_closure_setOf_isOfFinOrder`).

Hence a closed condition holding at the points of finite order of a torus holds on the whole torus.
For instance, some element of finite order of the closure of a one-parameter subgroup `exp (t ξ)`
acts nontrivially on a space as soon as one of the `exp (t ξ)` does.

## Main results

* `TauCeti.Lie.IsTorus.subset_closure_setOf_isOfFinOrder`: a torus lies in the closure of its
  points of finite order.
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable (I) in
include I in
/-- **Points of finite order are dense in a torus.** Every point of a torus `T` of a Lie group is
a limit of points of `T` of finite order. -/
theorem IsTorus.subset_closure_setOf_isOfFinOrder {T : Subgroup G} (hT : IsTorus T) :
    (T : Set G) ⊆ closure {g | g ∈ T ∧ IsOfFinOrder g} := by
  obtain ⟨φ⟩ := hT.nonempty_continuousMulEquiv_pi_circle (I := I)
  -- Through `φ`, the points of finite order of `T` are those of a finite power of the circle.
  have hD : Dense {t : T | IsOfFinOrder t} :=
    (Circle.dense_setOf_isOfFinOrder_pi.preimage φ.toHomeomorph.isOpenMap).mono fun _ ht ↦
      (Function.Injective.isOfFinOrder_iff (f := φ.toMulEquiv.toMonoidHom) φ.injective).1 ht
  intro g hg
  have hmem : (⟨g, hg⟩ : T) ∈ closure {t : T | IsOfFinOrder t} := hD.closure_eq ▸ mem_univ _
  refine closure_mono ?_
    (image_closure_subset_closure_image continuous_subtypeVal (mem_image_of_mem _ hmem))
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨t.property, T.subtype.isOfFinOrder ht⟩

end TauCeti.Lie
