/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.ExtendByZero
public import TauCeti.Topology.PL.Map

/-!
# Piecewise-linear coordinate formulas under injective relabeling

An injective relabeling extends a coordinate vector by zero on unused vertices.
Conjugate a coordinate formula by extension on its output and restriction on its input.
The resulting formula is PL on the relabeled set exactly when the original formula is
PL. Both index types may be infinite: extension and restriction are continuous linear
maps for their product topologies.

This is the coordinate transport needed to compare PL maps of polyhedra described on
different ambient vertex sets, including a common enlarged set used for stellar moves.

Reference: Rourke–Sanderson, *Introduction to Piecewise-Linear Topology*, Chapters 1–2.
-/

public section

open Set Function

namespace TauCeti

variable {ι κ α β : Type*} (e : ι ↪ κ) (d : α ↪ β)
  {f : (ι → ℝ) → (α → ℝ)} {s : Set (ι → ℝ)}

/-- Extending output coordinates by zero and pulling input coordinates back along
injections preserves and reflects PL regularity on the relabeled domain. -/
theorem isPLOn_extendByZero_iff :
    IsPLOn (fun y : κ → ℝ => Function.extend d (f (y ∘ e)) 0)
      ((Function.ExtendByZero.continuousLinearMap ℝ e) '' s) ↔ IsPLOn f s := by
  simpa only [ContinuousLinearMap.coe_toContinuousAffineMap, Function.comp_def,
    Function.ExtendByZero.continuousLinearMap_apply, Function.ExtendByZero.restriction_apply]
    using isPLOn_affine_transport_iff (f := f) (s := s)
    (Function.ExtendByZero.continuousLinearMap ℝ e).toContinuousAffineMap
    (Function.ExtendByZero.restriction ℝ e).toContinuousAffineMap
    (Function.ExtendByZero.continuousLinearMap ℝ d).toContinuousAffineMap
    (Function.ExtendByZero.restriction ℝ d).toContinuousAffineMap
    (fun x _ ↦ Function.ExtendByZero.restriction_leftInverse ℝ e e.injective x)
    (fun x _ ↦ Function.ExtendByZero.restriction_leftInverse ℝ d d.injective (f x))

end TauCeti
