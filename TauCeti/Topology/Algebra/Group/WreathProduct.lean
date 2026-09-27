/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.WreathProduct.Basic
public import Mathlib.Topology.Constructions

/-!
# Coordinate topology on permutation wreath products

The base has the product topology and the permutation group has the topology of pointwise
convergence. Relabeling coordinates continuously preserves this topology.
-/

public section

namespace TauCeti.WreathProduct

universe u v

variable (D : Type u) (ι : Type v) [Group D]

/-- The coordinate topology on a permutation wreath product. The base coordinates have the
product topology, while the permutation has the topology of pointwise convergence. -/
instance instTopologicalSpace [TopologicalSpace D] [TopologicalSpace ι] :
    TopologicalSpace (WreathProduct D ι) :=
  TopologicalSpace.induced
    (fun w : WreathProduct D ι => (w.left, (w.right : ι → ι))) inferInstance

variable {D ι} {κ : Type*} [TopologicalSpace D] [TopologicalSpace ι]
  [TopologicalSpace κ]

/-- Relabeling a wreath product is continuous when the relabeling of its index type is
continuous. Both coordinates are checked in the coordinate topology. -/
theorem continuous_congr (e : ι ≃ κ) (he : Continuous e) :
    Continuous (congr (D := D) e) := by
  have hcoords : Continuous (fun w : WreathProduct D ι =>
      (w.left, (w.right : ι → ι))) := continuous_induced_dom
  apply continuous_induced_rng.mpr
  exact (continuous_pi fun i => by
    simpa only [congr_left, Function.comp_def] using
      (continuous_apply (e.symm i)).comp hcoords.fst).prodMk
      (continuous_pi fun i => by
        simpa only [congr_right, Equiv.permCongr_apply, Function.comp_def] using
          he.comp ((continuous_apply (e.symm i)).comp hcoords.snd))

end TauCeti.WreathProduct
