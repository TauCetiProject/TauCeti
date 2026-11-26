/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.Monotone

/-!
# One-sided limits of monotone functions into complete linear orders

A monotone or antitone function from a linearly ordered space into a complete linear order has a
limit on each side of every point `x`, given by the indexed supremum or infimum of its values on
that side. These are the `⨆`/`⨅` forms of Mathlib's `Monotone.tendsto_nhdsLT`,
`Monotone.tendsto_nhdsGT`, `Antitone.tendsto_nhdsLT` and `Antitone.tendsto_nhdsGT`, which state
the limit as `sSup`/`sInf` of an image.

## Main results

* `Monotone.tendsto_nhdsLT_biSup`, `Monotone.tendsto_nhdsGT_biInf`
* `Antitone.tendsto_nhdsLT_biInf`, `Antitone.tendsto_nhdsGT_biSup`
-/

public section

open Filter Set Topology

variable {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [CompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α → β}

/-- A monotone function tends to the supremum of its values to the left of `x` as its argument
tends to `x` from the left. -/
theorem Monotone.tendsto_nhdsLT_biSup (hf : Monotone f) (x : α) :
    Tendsto f (𝓝[<] x) (𝓝 (⨆ y < x, f y)) := by
  have h := hf.tendsto_nhdsLT x
  rwa [sSup_image] at h

/-- A monotone function tends to the infimum of its values to the right of `x` as its argument
tends to `x` from the right. -/
theorem Monotone.tendsto_nhdsGT_biInf (hf : Monotone f) (x : α) :
    Tendsto f (𝓝[>] x) (𝓝 (⨅ y > x, f y)) := by
  have h := hf.tendsto_nhdsGT x
  rwa [sInf_image] at h

/-- An antitone function tends to the infimum of its values to the left of `x` as its argument
tends to `x` from the left. -/
theorem Antitone.tendsto_nhdsLT_biInf (hf : Antitone f) (x : α) :
    Tendsto f (𝓝[<] x) (𝓝 (⨅ y < x, f y)) := by
  have h := hf.tendsto_nhdsLT x
  rwa [sInf_image] at h

/-- An antitone function tends to the supremum of its values to the right of `x` as its argument
tends to `x` from the right. -/
theorem Antitone.tendsto_nhdsGT_biSup (hf : Antitone f) (x : α) :
    Tendsto f (𝓝[>] x) (𝓝 (⨆ y > x, f y)) := by
  have h := hf.tendsto_nhdsGT x
  rwa [sSup_image] at h
