/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Reindexing filtered finite sums

This file provides a convenience theorem for reindexing filtered finite sums through mutually
inverse maps. Membership in the unfiltered source and target finsets is exposed as predicates so
that arithmetic descriptions of bounded index sets can be used directly.

## Main results

* `TauCeti.sum_nbij_filter_of_mem_iff`: reindex a filtered finite sum through inverse maps after
  characterizing membership in the unfiltered source and target finsets.
-/

public section

namespace TauCeti

open Finset

/-- Reindex filtered finite sums through inverse maps after expressing membership in the
unfiltered source and target finsets as predicates. -/
theorem sum_nbij_filter_of_mem_iff {ι κ M : Type*} [AddCommMonoid M]
    {s : Finset ι} {t : Finset κ} {S : ι → Prop} {T : κ → Prop}
    {P : ι → Prop} {Q : κ → Prop} [DecidablePred P] [DecidablePred Q] {g : κ → M}
    (hs : ∀ i, i ∈ s ↔ S i) (ht : ∀ j, j ∈ t ↔ T j) (f : ι → κ) (finv : κ → ι)
    (hf : ∀ i, S i ∧ P i → T (f i) ∧ Q (f i))
    (hfinv : ∀ j, T j ∧ Q j → S (finv j) ∧ P (finv j))
    (hleft : ∀ i, S i ∧ P i → finv (f i) = i)
    (hright : ∀ j, T j ∧ Q j → f (finv j) = j) :
    ∑ i ∈ {i ∈ s | P i}, g (f i) = ∑ j ∈ {j ∈ t | Q j}, g j := by
  classical
  exact Finset.sum_nbij' f finv
    (fun i hi =>
      let hi' := Finset.mem_filter.mp hi
      let hfi := hf i ⟨(hs i).mp hi'.1, hi'.2⟩
      Finset.mem_filter.mpr ⟨(ht _).mpr hfi.1, hfi.2⟩)
    (fun j hj =>
      let hj' := Finset.mem_filter.mp hj
      let hfinvj := hfinv j ⟨(ht j).mp hj'.1, hj'.2⟩
      Finset.mem_filter.mpr ⟨(hs _).mpr hfinvj.1, hfinvj.2⟩)
    (fun i hi =>
      let hi' := Finset.mem_filter.mp hi
      hleft i ⟨(hs i).mp hi'.1, hi'.2⟩)
    (fun j hj =>
      let hj' := Finset.mem_filter.mp hj
      hright j ⟨(ht j).mp hj'.1, hj'.2⟩)
    (fun _ _ => rfl)

end TauCeti
