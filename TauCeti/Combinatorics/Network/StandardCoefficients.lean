/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import TauCeti.Algebra.Order.Ring.Cast
public import TauCeti.Combinatorics.Network.Coefficients
public import TauCeti.Data.Rat.Cast.Order

/-!
# Standard coefficient embeddings for flows

The integer and rational casts give the standard order-preserving additive embeddings
`Int.castOrderAddMonoidHom ℚ : ℤ →+o ℚ` and
`Rat.castOrderAddMonoidHom ℝ : ℚ →+o ℝ`. This file specializes change of coefficients for
assignments, networks and flows to these maps.

Finite arrow sums, cut bounds and residual capacities commute with both casts. Mapping a bounded
flow, ordinary flow, prescribed-excess assignment or interval-excess assignment first to `ℚ` and
then to `ℝ` agrees with mapping it directly to `ℝ`. Since the casts are strictly monotone, a flow
is maximum exactly when either of its standard coefficient images is maximum.

## Main results

* `TauCeti.intCast_arrowSum`, `TauCeti.ratCast_arrowSum`: standard casts commute with arrow sums.
* `TauCeti.intCast_cutBound`, `TauCeti.ratCast_cutBound`: standard casts commute with cut bounds.
* `TauCeti.Assignment.intCast_residualCapacity`,
  `TauCeti.Assignment.ratCast_residualCapacity`: standard casts commute with residual capacities.
* `TauCeti.BoundedFlow.map_intCast_ratCast_toFun`,
  `TauCeti.Flow.map_intCast_ratCast_toFun`: mapping through `ℚ` gives the same arrow assignment
  as mapping directly from `ℤ` to `ℝ`.
* `TauCeti.BoundedFlow.isMaximum_map_intCast_rat_iff`,
  `TauCeti.BoundedFlow.isMaximum_map_ratCast_real_iff` and the corresponding `Flow` lemmas:
  the standard embeddings preserve and reflect maximality.
-/

public section

namespace Rat

/-- Composing the standard integer-to-rational and rational-to-real additive order maps gives the
standard integer-to-real map. -/
@[simp]
theorem castOrderAddMonoidHom_comp_intCast :
    (castOrderAddMonoidHom ℝ).comp (Int.castOrderAddMonoidHom ℚ) =
      Int.castOrderAddMonoidHom ℝ := by
  apply OrderAddMonoidHom.ext
  intro z
  simp

end Rat

namespace TauCeti

open Finset

universe u v

variable {V : Type u} {Q : V → V → Type v}

namespace Assignment

/-- Mapping an integer assignment first to `ℚ` and then to `ℝ` is its direct integer cast. -/
theorem map_intCast_ratCast (f : Assignment Q ℤ) :
    (f.map (Int.cast : ℤ → ℚ)).map (Rat.cast : ℚ → ℝ) =
      f.map (Int.cast : ℤ → ℝ) :=
  rfl

/-- Residual capacities commute with the standard embedding `ℤ → ℚ`. -/
theorem intCast_residualCapacity (lo hi f : Assignment Q ℤ) :
    (residualCapacity lo hi f).map (Int.cast : ℤ → ℚ) =
      residualCapacity (lo.map (Int.cast : ℤ → ℚ)) (hi.map (Int.cast : ℤ → ℚ))
        (f.map (Int.cast : ℤ → ℚ)) := by
  simpa using Assignment.map_residualCapacity (Int.castOrderAddMonoidHom ℚ) lo hi f

/-- Residual capacities commute with the standard embedding `ℚ → ℝ`. -/
theorem ratCast_residualCapacity (lo hi f : Assignment Q ℚ) :
    (residualCapacity lo hi f).map (Rat.cast : ℚ → ℝ) =
      residualCapacity (lo.map (Rat.cast : ℚ → ℝ)) (hi.map (Rat.cast : ℚ → ℝ))
        (f.map (Rat.cast : ℚ → ℝ)) := by
  simpa using Assignment.map_residualCapacity (Rat.castOrderAddMonoidHom ℝ) lo hi f

end Assignment

namespace Network

/-- Mapping an integer network first to `ℚ` and then to `ℝ` is its direct integer cast. -/
theorem map_intCast_ratCast (N : Network ℤ V) :
    (N.map (Int.cast : ℤ → ℚ) Int.cast_mono).map (Rat.cast : ℚ → ℝ) Rat.cast_mono =
      N.map (Int.cast : ℤ → ℝ) Int.cast_mono :=
  rfl

end Network

variable [∀ x y, Fintype (Q x y)]

/-- Finite arrow sums commute with the standard embedding `ℤ → ℚ`. -/
theorem intCast_arrowSum (f : Assignment Q ℤ) (S T : Finset V) :
    ((arrowSum f S T : ℤ) : ℚ) = arrowSum (f.map (Int.cast : ℤ → ℚ)) S T := by
  simpa using map_arrowSum (Int.castOrderAddMonoidHom ℚ) f S T

/-- Finite arrow sums commute with the standard embedding `ℚ → ℝ`. -/
theorem ratCast_arrowSum (f : Assignment Q ℚ) (S T : Finset V) :
    ((arrowSum f S T : ℚ) : ℝ) = arrowSum (f.map (Rat.cast : ℚ → ℝ)) S T := by
  simpa using map_arrowSum (Rat.castOrderAddMonoidHom ℝ) f S T

variable [Fintype V]

/-- Cut bounds commute with the standard embedding `ℤ → ℚ`. -/
theorem intCast_cutBound [DecidableEq V] (lo hi : Assignment Q ℤ) (S : Finset V) :
    ((cutBound lo hi S : ℤ) : ℚ) =
      cutBound (lo.map (Int.cast : ℤ → ℚ)) (hi.map (Int.cast : ℤ → ℚ)) S := by
  simpa using map_cutBound (Int.castOrderAddMonoidHom ℚ) lo hi S

/-- Cut bounds commute with the standard embedding `ℚ → ℝ`. -/
theorem ratCast_cutBound [DecidableEq V] (lo hi : Assignment Q ℚ) (S : Finset V) :
    ((cutBound lo hi S : ℚ) : ℝ) =
      cutBound (lo.map (Rat.cast : ℚ → ℝ)) (hi.map (Rat.cast : ℚ → ℝ)) S := by
  simpa using map_cutBound (Rat.castOrderAddMonoidHom ℝ) lo hi S

variable {s t : V}

namespace BoundedFlow

/-- Mapping an integer bounded flow first to `ℚ` and then to `ℝ` gives the same arrow assignment
as mapping it directly to `ℝ`. -/
theorem map_intCast_ratCast_toFun {lo hi : Assignment Q ℤ} (f : BoundedFlow lo hi s t) :
    ((f.map (Int.castOrderAddMonoidHom ℚ)).map
      (Rat.castOrderAddMonoidHom ℝ)).toFun =
      (f.map (Int.castOrderAddMonoidHom ℝ)).toFun := by
  funext x y e
  simp only [map_toFun, Assignment.map_apply, Int.coe_castOrderAddMonoidHom,
    Rat.coe_castOrderAddMonoidHom, Rat.cast_intCast]

/-- Mapping an integer bounded flow to `ℚ` casts its value. -/
theorem val_map_intCast_rat {lo hi : Assignment Q ℤ} (f : BoundedFlow lo hi s t) :
    (f.map (Int.castOrderAddMonoidHom ℚ)).val = (f.val : ℚ) :=
  by simpa only [Int.coe_castOrderAddMonoidHom] using f.val_map (Int.castOrderAddMonoidHom ℚ)

/-- Mapping a rational bounded flow to `ℝ` casts its value. -/
theorem val_map_ratCast_real {lo hi : Assignment Q ℚ} (f : BoundedFlow lo hi s t) :
    (f.map (Rat.castOrderAddMonoidHom ℝ)).val = (f.val : ℝ) :=
  by simpa only [Rat.coe_castOrderAddMonoidHom] using f.val_map (Rat.castOrderAddMonoidHom ℝ)

/-- An integer bounded flow is maximum exactly when its rational image is maximum. -/
theorem isMaximum_map_intCast_rat_iff {lo hi : Assignment Q ℤ}
    (f : BoundedFlow lo hi s t) (hst : s ≠ t) :
    (f.map (Int.castOrderAddMonoidHom ℚ)).IsMaximum ↔ f.IsMaximum := by
  apply BoundedFlow.isMaximum_map_iff hst
  simpa only [Int.coe_castOrderAddMonoidHom] using (Int.cast_strictMono (R := ℚ))

/-- A rational bounded flow is maximum exactly when its real image is maximum. -/
theorem isMaximum_map_ratCast_real_iff {lo hi : Assignment Q ℚ}
    (f : BoundedFlow lo hi s t) (hst : s ≠ t) :
    (f.map (Rat.castOrderAddMonoidHom ℝ)).IsMaximum ↔ f.IsMaximum := by
  apply BoundedFlow.isMaximum_map_iff hst
  simpa only [Rat.coe_castOrderAddMonoidHom] using (Rat.cast_strictMono (K := ℝ))

end BoundedFlow

namespace Flow

/-- Mapping an integer flow first to `ℚ` and then to `ℝ` gives the same arrow assignment as
mapping it directly to `ℝ`. -/
theorem map_intCast_ratCast_toFun {cap : Assignment Q ℤ} (f : Flow cap s t) :
    ((f.map (Int.castOrderAddMonoidHom ℚ)).map
      (Rat.castOrderAddMonoidHom ℝ)).toFun =
      (f.map (Int.castOrderAddMonoidHom ℝ)).toFun := by
  funext x y e
  simp only [map_toFun, Assignment.map_apply, Int.coe_castOrderAddMonoidHom,
    Rat.coe_castOrderAddMonoidHom, Rat.cast_intCast]

/-- Mapping an integer flow to `ℚ` casts its value. -/
theorem val_map_intCast_rat {cap : Assignment Q ℤ} (f : Flow cap s t) :
    (f.map (Int.castOrderAddMonoidHom ℚ)).val = (f.val : ℚ) :=
  by simpa only [Int.coe_castOrderAddMonoidHom] using f.val_map (Int.castOrderAddMonoidHom ℚ)

/-- Mapping a rational flow to `ℝ` casts its value. -/
theorem val_map_ratCast_real {cap : Assignment Q ℚ} (f : Flow cap s t) :
    (f.map (Rat.castOrderAddMonoidHom ℝ)).val = (f.val : ℝ) :=
  by simpa only [Rat.coe_castOrderAddMonoidHom] using f.val_map (Rat.castOrderAddMonoidHom ℝ)

/-- An integer flow is maximum exactly when its rational image is maximum. -/
theorem isMaximum_map_intCast_rat_iff {cap : Assignment Q ℤ} (f : Flow cap s t)
    (hst : s ≠ t) : (f.map (Int.castOrderAddMonoidHom ℚ)).IsMaximum ↔ f.IsMaximum := by
  apply Flow.isMaximum_map_iff hst
  simpa only [Int.coe_castOrderAddMonoidHom] using (Int.cast_strictMono (R := ℚ))

/-- A rational flow is maximum exactly when its real image is maximum. -/
theorem isMaximum_map_ratCast_real_iff {cap : Assignment Q ℚ} (f : Flow cap s t)
    (hst : s ≠ t) : (f.map (Rat.castOrderAddMonoidHom ℝ)).IsMaximum ↔ f.IsMaximum := by
  apply Flow.isMaximum_map_iff hst
  simpa only [Rat.coe_castOrderAddMonoidHom] using (Rat.cast_strictMono (K := ℝ))

end Flow

namespace ExcessFlow

/-- Mapping an integral prescribed-excess assignment first to `ℚ` and then to `ℝ` gives the same
arrow assignment as mapping it directly to `ℝ`. -/
theorem map_intCast_ratCast_val {lo hi : Assignment Q ℤ} {b : V → ℤ}
    (f : ExcessFlow lo hi b) :
    ((f.map (Int.castOrderAddMonoidHom ℚ)).map
      (Rat.castOrderAddMonoidHom ℝ)).val =
      (f.map (Int.castOrderAddMonoidHom ℝ)).val := by
  funext x y e
  simp only [map_val, Assignment.map_apply, Int.coe_castOrderAddMonoidHom,
    Rat.coe_castOrderAddMonoidHom, Rat.cast_intCast]

end ExcessFlow

namespace ExcessIntervalFlow

/-- Mapping an integral interval-excess assignment first to `ℚ` and then to `ℝ` gives the same
arrow assignment as mapping it directly to `ℝ`. -/
theorem map_intCast_ratCast_val {lo hi : Assignment Q ℤ} {a b : V → ℤ}
    (f : ExcessIntervalFlow lo hi a b) :
    ((f.map (Int.castOrderAddMonoidHom ℚ)).map
      (Rat.castOrderAddMonoidHom ℝ)).val =
      (f.map (Int.castOrderAddMonoidHom ℝ)).val := by
  funext x y e
  simp only [map_val, Assignment.map_apply, Int.coe_castOrderAddMonoidHom,
    Rat.coe_castOrderAddMonoidHom, Rat.cast_intCast]

end ExcessIntervalFlow

end TauCeti
