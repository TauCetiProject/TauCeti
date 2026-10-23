/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Clopen

/-!
# Continuous maps between disjoint unions of preconnected spaces

Each summand `X i` of a disjoint union `Σ i, X i` is clopen, so a continuous map out of a
preconnected summand lands in a single summand of the target.  This holds summand by summand
without assuming any summand nonempty, unlike `Continuous.exists_lift_sigma`, which lifts a map
out of a connected space.

## Main declarations

* `Continuous.fst_apply_eq_fst_apply_of_fst_eq`: a continuous map `(Σ i, X i) → Σ j, Y j` with
  preconnected summands `X i` sends points of the same summand into the same summand.
-/

public section

open Set

variable {ι κ : Type*} {X : ι → Type*} {Y : κ → Type*} [∀ i, TopologicalSpace (X i)]
  [∀ j, TopologicalSpace (Y j)]

/-- A continuous map between disjoint unions sends each preconnected summand into a single
summand: points of the same summand have images in the same summand. -/
theorem Continuous.fst_apply_eq_fst_apply_of_fst_eq [∀ i, PreconnectedSpace (X i)]
    {f : (Σ i, X i) → Σ j, Y j} (hf : Continuous f) {x y : Σ i, X i} (h : x.1 = y.1) :
    (f x).1 = (f y).1 := by
  obtain ⟨i, a⟩ := x
  obtain ⟨j, b⟩ := y
  subst h
  have hconn : IsPreconnected (range fun c : X i ↦ f ⟨i, c⟩) :=
    isPreconnected_range (hf.comp continuous_sigmaMk)
  obtain ⟨c, hc⟩ := hconn.subset_isClopen (isClopen_range_sigmaMk (i := (f ⟨i, a⟩).1))
    ⟨f ⟨i, a⟩, mem_range_self a, ⟨_, rfl⟩⟩ (mem_range_self b)
  rw [← hc]
