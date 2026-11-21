/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import TauCeti.Topology.Covering.FinitePullback
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Covering
public import TauCeti.Topology.Covering.Degree

/-!
# Euler characteristic of a pulled-back finite cover

The degree of a finite covering is constant over a connected base. Pulling it back along a
continuous map preserves that degree, so the Euler characteristic of the pullback is the degree
times the Euler characteristic of its base.
-/

public noncomputable section

open Function

namespace TauCeti

universe u

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [PreconnectedSpace Y] [FiniteCWType X] {f : X → Y} {p : Z → Y}

omit [TopologicalSpace X] [FiniteCWType X] in
/-- The pullback of a covering map has the same fibre cardinality as the original cover
over a preconnected base. -/
theorem _root_.IsCoveringMap.natCard_pullback_fst_fiber (hp : IsCoveringMap p)
    (x : X) (y : Y) :
    Nat.card ((Pullback.fst : f.Pullback p → X) ⁻¹' {x}) =
      Nat.card (p ⁻¹' {y}) := by
  rw [Nat.card_congr (Pullback.fstPreimageEquiv x)]
  simpa only [IsCoveringMap.degree_apply] using
    hp.degree.apply_eq_of_preconnectedSpace (f x) y

/-- The Euler characteristic of a pulled-back finite cover is multiplied by the number of
sheets of the original cover. -/
theorem IsFiniteCover.eulerChar_pullback (hp : IsFiniteCover p) (hf : Continuous f) (y : Y) :
    let hq := hp.pullback_fst hf
    letI : FiniteCWType (f.Pullback p) := by
      exact hq.isCoveringMap.finiteCWType hq.finite_fiber
    eulerChar (f.Pullback p) = Nat.card (p ⁻¹' {y}) * eulerChar X := by
  let hq := hp.pullback_fst hf
  let : FiniteCWType (f.Pullback p) := hq.isCoveringMap.finiteCWType hq.finite_fiber
  exact eulerChar_eq_mul_of_isCoveringMap hq.isCoveringMap hq.finite_fiber
    (fun x ↦ hp.isCoveringMap.natCard_pullback_fst_fiber x y)

end TauCeti
