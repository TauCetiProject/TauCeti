/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.ApproximateUnit
import TauCeti.Analysis.Normed.Module.Convex

/-!
# Convexification of filters in normed rings

Replacing every member of a filter by its real convex hull (`l.lift' (convexHull ℝ)`) preserves
limits of real-linear maps into real seminormed spaces (`Filter.Tendsto.lift'_convexHull`).
For a nonunital seminormed ring `A` over `ℝ`, this applies to left and right multiplication
and to ring commutators `f e * a - a * f e`:

* `Filter.IsApproximateUnit.lift'_convexHull`: real convexification of an approximate unit yields
  a coarser approximate unit.
* `TauCeti.tendsto_commutator_lift'_convexHull`: real convexification preserves limits of
  commutators `f e * a - a * f e` for any `S`-linear map `f` compatible with `ℝ`-scalars
  (in particular, for `y = 0`, it preserves asymptotic centrality).
-/

public section

open Filter Topology

/-- Replacing every member of an approximate unit by its real convex hull yields a coarser
approximate unit. -/
theorem Filter.IsApproximateUnit.lift'_convexHull {A : Type*} [NonUnitalSeminormedRing A]
    [NormedSpace ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] {l : Filter A}
    (hl : l.IsApproximateUnit) :
    (l.lift' (convexHull ℝ)).IsApproximateUnit where
  tendsto_mul_left a :=
    Filter.Tendsto.lift'_convexHull (f := LinearMap.mulLeft ℝ a) (hl.tendsto_mul_left a)
  tendsto_mul_right a :=
    Filter.Tendsto.lift'_convexHull (f := LinearMap.mulRight ℝ a) (hl.tendsto_mul_right a)
  neBot := by
    have := hl.neBot
    exact (lift'_neBot_iff fun _ _ hst => convexHull_mono hst).mpr
      fun _ hs => (nonempty_of_mem hs).convexHull

namespace TauCeti

/-- Real convexification `l.lift' (convexHull ℝ)` preserves limits of ring commutators
`f e * a - a * f e` for any `S`-linear map `f` (compatible with `ℝ`-scalars) into a nonunital
seminormed ring over `ℝ`. In particular, taking `y = 0`, it preserves asymptotic centrality. -/
theorem tendsto_commutator_lift'_convexHull {B A S F : Type*} [Semiring S]
    [AddCommMonoid B] [Module ℝ B] [Module S B]
    [NonUnitalSeminormedRing A] [NormedSpace ℝ A] [Module S A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [LinearMap.CompatibleSMul B A ℝ S]
    [FunLike F B A] [LinearMapClass F S B A]
    {l : Filter B} (f : F) {a y : A}
    (h : Tendsto (fun e => f e * a - a * f e) l (𝓝 y)) :
    Tendsto (fun e => f e * a - a * f e) (l.lift' (convexHull ℝ)) (𝓝 y) :=
  Filter.Tendsto.lift'_convexHull
    (f := (LinearMap.mulRight ℝ a - LinearMap.mulLeft ℝ a).comp
      ((f : B →ₗ[S] A).restrictScalars ℝ)) h

end TauCeti
