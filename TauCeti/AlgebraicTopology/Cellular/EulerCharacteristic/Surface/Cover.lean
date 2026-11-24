/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Covering
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Surface.Basic
public import TauCeti.Topology.Covering.Degree
public import TauCeti.Topology.Covering.IsFiniteCover
public import TauCeti.Topology.Covering.Proper

/-!
# Euler characteristic obstruction for finite covers of surfaces

A connected homologically oriented closed surface has Euler characteristic at most two. If it
finitely covers a compact Hausdorff connected space of finite CW type, multiplicativity bounds the
product of the covering degree and the Euler characteristic of the base. Consequently a compact
Hausdorff space of finite CW type with Euler characteristic two admits no double cover by a
connected homologically oriented closed surface.
-/

public noncomputable section

open Module

namespace TauCeti

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {T S : Type} [TopologicalSpace T] [ChartedSpace E T] [ConnectedSpace T]
  [TopologicalSpace S] [T2Space S] [CompactSpace S] [FiniteCWType S] {q : T → S}

/-- The degree of a connected finite cover times the Euler characteristic of a compact Hausdorff
base of finite CW type is at most two if the covering surface is homologically oriented. -/
theorem IsFiniteCover.natCard_fiber_mul_eulerChar_le_two (hq : IsFiniteCover q)
    (hn : finrank ℝ E = 2) (o : haveI := hq.isCoveringMap.t2Space
      haveI : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hn
      HomologicalOrientation T E 2) (y : S) :
    (Nat.card (q ⁻¹' {y}) : ℤ) * eulerChar S ≤ 2 := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hn
  let : ConnectedSpace S := hq.connectedSpace
  let : T2Space T := hq.isCoveringMap.t2Space
  let : CompactSpace T := hq.isCoveringMap.compactSpace hq.finite_fiber
  let : FiniteCWType T := hq.isCoveringMap.finiteCWType hq.finite_fiber
  have hχ : eulerChar T = (Nat.card (q ⁻¹' {y}) : ℤ) * eulerChar S :=
    eulerChar_eq_mul_of_isCoveringMap hq.isCoveringMap hq.finite_fiber
      (fun x ↦ by
        simpa only [IsCoveringMap.degree_apply] using
          hq.isCoveringMap.degree.apply_eq_of_preconnectedSpace x y)
  rw [← hχ]
  exact o.eulerChar_le_two hn

/-- A connected homologically oriented surface finitely covering a compact Hausdorff base of
finite CW type with Euler characteristic two has exactly one sheet. -/
theorem IsFiniteCover.natCard_fiber_eq_one_of_eulerChar_eq_two (hq : IsFiniteCover q)
    (hn : finrank ℝ E = 2) (o : haveI := hq.isCoveringMap.t2Space
      haveI : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hn
      HomologicalOrientation T E 2)
    (hχS : eulerChar S = 2) (y : S) : Nat.card (q ⁻¹' {y}) = 1 := by
  have h := hq.natCard_fiber_mul_eulerChar_le_two hn o y
  rw [hχS] at h
  obtain ⟨x, hx⟩ := hq.surjective y
  have hpos : 0 < Nat.card (q ⁻¹' {y}) :=
    Nat.card_pos_iff.mpr ⟨⟨⟨x, hx⟩⟩, hq.finite_fiber y⟩
  omega

end TauCeti
