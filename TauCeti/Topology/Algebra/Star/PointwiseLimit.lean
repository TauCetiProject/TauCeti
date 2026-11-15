/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Star

/-!
# Pointwise limits of non-unital star algebra homomorphisms

A pointwise limit of non-unital star algebra homomorphisms into a Hausdorff topological
star algebra with continuous operations is again a non-unital star algebra homomorphism.
This is the star-algebra counterpart of Mathlib's `linearMapOfTendsto` and
`mulHomOfTendsto`. It is used to define the limit maps of approximate intertwining
arguments for C⋆-algebras.
-/

public section

open Filter Topology

namespace TauCeti

variable {α R A B : Type*} {l : Filter α} [Monoid R]
  [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
  [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
  [TopologicalSpace B] [T2Space B] [ContinuousAdd B] [ContinuousMul B] [ContinuousStar B]
  [ContinuousConstSMul R B]

/-- Construct a bundled non-unital star algebra homomorphism from a pointwise limit of
non-unital star algebra homomorphisms. -/
def nonUnitalStarAlgHomOfTendsto (f : A → B) (g : α → A →⋆ₙₐ[R] B) [l.NeBot]
    (h : Tendsto (fun a x ↦ g a x) l (𝓝 f)) : A →⋆ₙₐ[R] B where
  toFun := f
  map_smul' r x := tendsto_nhds_unique (tendsto_pi_nhds.mp h (r • x)) <| by
    simpa only [map_smul, MonoidHom.id_apply] using (tendsto_pi_nhds.mp h x).const_smul r
  map_zero' := tendsto_nhds_unique (tendsto_pi_nhds.mp h 0) <| by
    simpa only [map_zero] using tendsto_const_nhds
  map_add' x y := tendsto_nhds_unique (tendsto_pi_nhds.mp h (x + y)) <| by
    simpa only [map_add] using (tendsto_pi_nhds.mp h x).add (tendsto_pi_nhds.mp h y)
  map_mul' x y := tendsto_nhds_unique (tendsto_pi_nhds.mp h (x * y)) <| by
    simpa only [map_mul] using (tendsto_pi_nhds.mp h x).mul (tendsto_pi_nhds.mp h y)
  map_star' x := tendsto_nhds_unique (tendsto_pi_nhds.mp h (star x)) <| by
    simpa only [map_star] using (tendsto_pi_nhds.mp h x).star

@[simp]
theorem coe_nonUnitalStarAlgHomOfTendsto (f : A → B) (g : α → A →⋆ₙₐ[R] B) [l.NeBot]
    (h : Tendsto (fun a x ↦ g a x) l (𝓝 f)) : ⇑(nonUnitalStarAlgHomOfTendsto f g h) = f :=
  (rfl)

@[simp]
theorem nonUnitalStarAlgHomOfTendsto_apply (f : A → B) (g : α → A →⋆ₙₐ[R] B) [l.NeBot]
    (h : Tendsto (fun a x ↦ g a x) l (𝓝 f)) (x : A) :
    nonUnitalStarAlgHomOfTendsto f g h x = f x :=
  (rfl)

end TauCeti
