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

/-- A map into a permutation wreath product is continuous exactly when each base and
permutation coordinate is continuous. -/
theorem continuous_iff {α : Type*} [TopologicalSpace α]
    {f : α → WreathProduct D ι} :
    Continuous f ↔
      (∀ i, Continuous fun a => (f a).left i) ∧
      (∀ i, Continuous fun a => (f a).right i) := by
  constructor
  · intro hf
    have h : Continuous (fun a => ((f a).left, ((f a).right : ι → ι))) :=
      continuous_induced_rng.mp hf
    exact ⟨fun i => (continuous_apply i).comp h.fst,
      fun i => (continuous_apply i).comp h.snd⟩
  · rintro ⟨hl, hr⟩
    exact continuous_induced_rng.mpr ((continuous_pi hl).prodMk (continuous_pi hr))

/-- Evaluation of a base coordinate is continuous. -/
@[continuity, fun_prop] theorem continuous_left (i : ι) :
    Continuous (fun w : WreathProduct D ι => w.left i) :=
  (continuous_iff.mp continuous_id).1 i

/-- Evaluation of a permutation coordinate is continuous. -/
@[continuity, fun_prop] theorem continuous_right (i : ι) :
    Continuous (fun w : WreathProduct D ι => w.right i) :=
  (continuous_iff.mp continuous_id).2 i

/-- Relabeling a wreath product is continuous when the relabeling of its index type is
continuous. -/
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
