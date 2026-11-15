/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Topology.Order.Lattice

/-!
# Continuity of finite indexed suprema and infima

In a conditionally complete lattice with continuous binary suprema, the pointwise supremum
`x ↦ ⨆ i, f i x` of a finite family of continuous functions is continuous, and dually for
infima. An empty family has the constant supremum `sSup ∅`. These are the indexed-supremum
forms of Mathlib's `Continuous.finset_sup'_apply` and `Continuous.finset_inf'_apply`, convenient
when the supremum is written with `⨆` over a finite type, such as a `Finset` coerced to a type.
-/

public section

namespace TauCeti

variable {X L ι : Type*} [TopologicalSpace X] [ConditionallyCompleteLattice L]
  [TopologicalSpace L] [Finite ι]

/-- The pointwise supremum of a finite family of continuous functions is continuous. -/
theorem continuous_ciSup_of_finite [ContinuousSup L] {f : ι → X → L}
    (hf : ∀ i, Continuous (f i)) : Continuous fun x ↦ ⨆ i, f i x := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact continuous_const.congr fun x ↦ (iSup_of_empty' (fun i ↦ f i x)).symm
  · have := Fintype.ofFinite ι
    simp_rw [← Finset.sup'_univ_eq_ciSup]
    exact Continuous.finset_sup'_apply Finset.univ_nonempty fun i _ ↦ hf i

/-- The pointwise infimum of a finite family of continuous functions is continuous. -/
theorem continuous_ciInf_of_finite [ContinuousInf L] {f : ι → X → L}
    (hf : ∀ i, Continuous (f i)) : Continuous fun x ↦ ⨅ i, f i x :=
  continuous_ciSup_of_finite (L := Lᵒᵈ) hf

end TauCeti
