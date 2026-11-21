/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Covering
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.OrientedSurface
public import TauCeti.Geometry.Manifold.Morse.CWModel
public import TauCeti.Topology.Covering.Degree
public import TauCeti.Topology.Covering.IsFiniteCover
public import TauCeti.Topology.Covering.Proper

/-!
# Euler characteristic obstruction for finite covers of surfaces

A connected oriented closed surface has Euler characteristic at most two. If it finitely covers
another closed surface, multiplicativity bounds the product of the covering degree and the Euler
characteristic of the base. Consequently a connected oriented double cover cannot lie over a
surface of Euler characteristic two.
-/

public noncomputable section

open Module
open scoped Manifold ContDiff

namespace TauCeti

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]
  {T S : Type} [TopologicalSpace T] [ChartedSpace E T]
  [IsManifold 𝓘(ℝ, E) ∞ T] [ConnectedSpace T]
  [TopologicalSpace S] [T2Space S] [CompactSpace S] [ConnectedSpace S]
  [ChartedSpace F S] [IsManifold 𝓘(ℝ, F) ∞ S]
  {q : T → S}

omit [FiniteDimensional ℝ F] in
/-- The degree of a connected finite cover times the Euler characteristic of a closed surface
is at most two if the covering surface is oriented. -/
theorem IsFiniteCover.natCard_fiber_mul_eulerChar_le_two (hq : IsFiniteCover q)
    (o : Manifold.Orientation 𝓘(ℝ, E) T (Fin 2)) (hn : finrank ℝ E = 2) (y : S) :
    letI := hq.isCoveringMap.t2Space
    letI := hq.isCoveringMap.compactSpace hq.finite_fiber
    letI : FiniteCWType S := FiniteCWType.of_isManifold (I := 𝓘(ℝ, F)) S
    letI : FiniteCWType T := hq.isCoveringMap.finiteCWType hq.finite_fiber
    (Nat.card (q ⁻¹' {y}) : ℤ) * eulerChar S ≤ 2 := by
  let : T2Space T := hq.isCoveringMap.t2Space
  let : CompactSpace T := hq.isCoveringMap.compactSpace hq.finite_fiber
  let : FiniteCWType S := FiniteCWType.of_isManifold (I := 𝓘(ℝ, F)) S
  let : FiniteCWType T := hq.isCoveringMap.finiteCWType hq.finite_fiber
  have hχ : eulerChar T = (Nat.card (q ⁻¹' {y}) : ℤ) * eulerChar S :=
    eulerChar_eq_mul_of_isCoveringMap hq.isCoveringMap hq.finite_fiber
      (fun x ↦ by
        simpa only [IsCoveringMap.degree_apply] using
          hq.isCoveringMap.degree.apply_eq_of_preconnectedSpace x y)
  rw [← hχ]
  exact o.eulerChar_le_two hn

omit [FiniteDimensional ℝ F] in
/-- A connected oriented finite cover of a surface with Euler characteristic two has only one
sheet. In particular such a surface has no connected oriented double cover. -/
theorem IsFiniteCover.natCard_fiber_le_one_of_eulerChar_eq_two (hq : IsFiniteCover q)
    (o : Manifold.Orientation 𝓘(ℝ, E) T (Fin 2)) (hn : finrank ℝ E = 2)
    (hχS :
      haveI := FiniteCWType.of_isManifold (I := 𝓘(ℝ, F)) S
      eulerChar S = 2) (y : S) : Nat.card (q ⁻¹' {y}) ≤ 1 := by
  have h := hq.natCard_fiber_mul_eulerChar_le_two (F := F) o hn y
  rw [hχS] at h
  omega

omit [FiniteDimensional ℝ F] in
/-- A closed surface of Euler characteristic two has no connected oriented two-sheeted
surface cover. -/
theorem IsFiniteCover.natCard_fiber_ne_two_of_eulerChar_eq_two (hq : IsFiniteCover q)
    (o : Manifold.Orientation 𝓘(ℝ, E) T (Fin 2)) (hn : finrank ℝ E = 2)
    (hχS :
      haveI := FiniteCWType.of_isManifold (I := 𝓘(ℝ, F)) S
      eulerChar S = 2) (y : S) : Nat.card (q ⁻¹' {y}) ≠ 2 := by
  have h := hq.natCard_fiber_le_one_of_eulerChar_eq_two (F := F) o hn hχS y
  omega

end TauCeti
