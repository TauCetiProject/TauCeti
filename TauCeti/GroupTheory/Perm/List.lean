/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.FinRange
import Mathlib.Data.List.NodupEquivFin

/-!
# Permutations as lists

A permutation of `Fin n` can be written in one-line notation as a list containing every element
of `Fin n` exactly once. This file packages that correspondence as an equivalence.
-/

public section

namespace TauCeti

open List

/-- Permutations of `Fin n` correspond to lists containing every element of `Fin n` exactly
once, by writing a permutation in one-line notation. -/
noncomputable def permutationWordEquiv (n : ℕ) :
    Equiv.Perm (Fin n) ≃ {w : List (Fin n) // w.Perm (finRange n)} :=
  Equiv.ofBijective
    (fun σ => ⟨ofFn σ, by simpa [List.ofFn_eq_map] using σ.map_finRange_perm⟩)
    ⟨fun σ τ h => Equiv.ext fun i =>
        congrFun (List.ofFn_injective (congrArg Subtype.val h)) i,
      fun w => by
      have hlen : w.val.length = n := w.property.length_eq.trans length_finRange
      have hmem (x : Fin n) : x ∈ w.val := w.property.symm.subset (mem_finRange x)
      let e : Fin n ≃ Fin w.val.length := finCongr hlen.symm
      let σ : Equiv.Perm (Fin n) := e.trans
        ((w.property.nodup_iff.mpr (nodup_finRange n)).getEquivOfForallMemList w.val hmem)
      have hσ (i : Fin n) : σ i = w.val.get (Fin.cast hlen.symm i) := by
        rw [Equiv.trans_apply, Nodup.getEquivOfForallMemList_apply, finCongr_apply]
      refine ⟨σ, Subtype.ext ?_⟩
      calc
        ofFn σ = ofFn (fun i : Fin n => w.val.get (Fin.cast hlen.symm i)) :=
          congrArg ofFn (funext hσ)
        _ = w.val := by rw [← List.ofFn_congr hlen w.val.get, List.ofFn_get]⟩

/-- The forward permutation-to-word equivalence is `List.ofFn`. -/
@[simp]
theorem permutationWordEquiv_apply_coe (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ((permutationWordEquiv n σ : {w : List (Fin n) // w.Perm (finRange n)}) : List (Fin n)) =
      List.ofFn σ :=
  (rfl)

end TauCeti
