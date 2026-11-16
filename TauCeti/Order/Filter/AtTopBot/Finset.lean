/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Data.Finset.Sigma
public import Mathlib.Order.Filter.AtTopBot.Defs

import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Cofinal finite subsets of a sigma type

When every fibre of `Σ i, κ i` is finite, the finite subsets `s.sigma fun _ ↦ univ` obtained by
filling each fibre over a finite subset `s` of the base are cofinal among all finite subsets of
the sigma type (`TauCeti.tendsto_finset_sigma_univ_atTop`). Partial sums and products of a
family over a sigma type with finite fibres can therefore be taken fibre by fibre.
-/

public section

open Filter

namespace TauCeti

/-- Filling each fiber of a finite subset of the base gives finite subsets of the sigma type
that are cofinal: every finite subset of `Σ i, κ i` is eventually contained in them. -/
theorem tendsto_finset_sigma_univ_atTop {ι : Type*} {κ : ι → Type*} [∀ i, Fintype (κ i)] :
    Tendsto (fun s : Finset ι ↦ s.sigma fun i ↦ (Finset.univ : Finset (κ i))) atTop atTop := by
  classical
  refine tendsto_atTop_atTop.2 fun t ↦ ⟨t.image Sigma.fst, fun s hs p hp ↦ ?_⟩
  exact Finset.mem_sigma.2 ⟨hs (Finset.mem_image_of_mem _ hp), Finset.mem_univ _⟩

end TauCeti
