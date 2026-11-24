/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.AtTopBot.Finset

/-!
# Cofinality of unions of function antidiagonals

For a finite index type `ι` and a commutative monoid `μ` with antidiagonals, every function
`f : ι → μ` belongs to `Finset.piAntidiag Finset.univ (∑ i, f i)`. Taking unions of these function
antidiagonals over finite sets of sums therefore gives a cofinal family of finite subsets of
`ι → μ` (`TauCeti.tendsto_biUnion_piAntidiag`), and in particular the multi-indices in `ι → ℕ` of
total degree `< K` exhaust `ι → ℕ` as `K → ∞` (`TauCeti.tendsto_biUnion_range_piAntidiag`).
-/

public section

open Filter Finset

namespace TauCeti

/-- Unions of `Finset.piAntidiag Finset.univ` over finite sets of target sums are cofinal among
all finite subsets of `ι → μ`. -/
theorem tendsto_biUnion_piAntidiag {ι μ : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] :
    Tendsto (fun s : Finset μ ↦ s.biUnion (piAntidiag (univ : Finset ι))) atTop atTop :=
  tendsto_atTop_finset_of_monotone
    (fun _ _ hs _ h ↦ by
      rcases mem_biUnion.1 h with ⟨n, hn, ha⟩
      exact mem_biUnion.2 ⟨n, hs hn, ha⟩)
    fun f ↦ ⟨{∑ i, f i}, mem_biUnion.2
      ⟨∑ i, f i, mem_singleton_self _, mem_piAntidiag.2 ⟨rfl, fun i _ ↦ mem_univ i⟩⟩⟩

/-- Multi-indices in `ι → ℕ` of total degree `< K` are cofinal among all finite subsets of
`ι → ℕ` as `K → ∞`. -/
theorem tendsto_biUnion_range_piAntidiag {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Tendsto (fun K : ℕ ↦ (range K).biUnion (piAntidiag (univ : Finset ι))) atTop atTop :=
  tendsto_biUnion_piAntidiag.comp tendsto_finset_range

end TauCeti
