/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Topology.Order.Lattice

/-!
# Continuity of indexed suprema and infima

In a conditionally complete lattice with continuous binary suprema, the pointwise supremum
`x ↦ ⨆ i, f i x` of a finite family of continuous functions is continuous, and dually for
infima. An empty family has the constant supremum `sSup ∅`. These are the indexed-supremum
forms of Mathlib's `Continuous.finset_sup'_apply` and `Continuous.finset_inf'_apply`, convenient
when the supremum is written with `⨆` over a finite type, such as a `Finset` coerced to a type.

For arbitrary index types, a family that is pointwise bounded above and eventually dominated
outside a nonempty finite index set reduces to that finite supremum
(`TauCeti.ciSup_eq_ciSup_of_notMem_le`) and therefore has a continuous pointwise supremum
(`TauCeti.continuous_ciSup_of_eventually_le`).
-/

public section

open Function Set Filter Topology

namespace TauCeti

variable {X L ι : Type*} [TopologicalSpace X] [ConditionallyCompleteLattice L]

/-- The pointwise supremum of a finite family of continuous functions is continuous. -/
theorem continuous_ciSup_of_finite [Finite ι] [TopologicalSpace L] [ContinuousSup L]
    {f : ι → X → L} (hf : ∀ i, Continuous (f i)) : Continuous fun x ↦ ⨆ i, f i x := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact continuous_const.congr fun x ↦ (iSup_of_empty' (fun i ↦ f i x)).symm
  · have := Fintype.ofFinite ι
    simp_rw [← Finset.sup'_univ_eq_ciSup]
    exact Continuous.finset_sup'_apply Finset.univ_nonempty fun i _ ↦ hf i

/-- The pointwise infimum of a finite family of continuous functions is continuous. -/
theorem continuous_ciInf_of_finite [Finite ι] [TopologicalSpace L] [ContinuousInf L]
    {f : ι → X → L} (hf : ∀ i, Continuous (f i)) : Continuous fun x ↦ ⨅ i, f i x :=
  continuous_ciSup_of_finite (L := Lᵒᵈ) hf

/-- If a bounded-above family `f : ι → L` is dominated outside a nonempty finite set `I : Finset ι`
by the finite supremum `⨆ i : I, f i`, then its supremum `⨆ i, f i` equals `⨆ i : I, f i`. -/
theorem ciSup_eq_ciSup_of_notMem_le {f : ι → L} (hbdd : BddAbove (range f))
    {I : Finset ι} (hIne : I.Nonempty) (hI : ∀ j ∉ I, f j ≤ ⨆ i : I, f i) :
    ⨆ i, f i = ⨆ i : I, f i := by
  have : Nonempty I := hIne.to_subtype
  have : Nonempty ι := ⟨hIne.choose⟩
  refine le_antisymm (ciSup_le fun j ↦ ?_) (ciSup_le fun i : I ↦ le_ciSup hbdd i.val)
  by_cases hj : j ∈ I
  · exact le_ciSup (finite_range (fun i : I ↦ f i)).bddAbove ⟨j, hj⟩
  · exact hI j hj

/-- The pointwise supremum of a pointwise bounded-above family of continuous functions into a
conditionally complete lattice with continuous binary suprema is continuous if around every point
it is eventually dominated outside a nonempty finite index set by the supremum over that finite
set. -/
theorem continuous_ciSup_of_eventually_le [TopologicalSpace L] [ContinuousSup L] {f : ι → X → L}
    (hf : ∀ i, Continuous (f i)) (hbdd : ∀ x, BddAbove (range fun i ↦ f i x))
    (hevent : ∀ x₀, ∃ I : Finset ι, I.Nonempty ∧ ∀ᶠ x in 𝓝 x₀, ∀ j ∉ I, f j x ≤ ⨆ i : I, f i x) :
    Continuous fun x ↦ ⨆ i, f i x := by
  refine continuous_iff_continuousAt.mpr fun x₀ ↦ ?_
  obtain ⟨I, hIne, hI⟩ := hevent x₀
  exact (TauCeti.continuous_ciSup_of_finite fun i : I ↦ hf i.val).continuousAt.congr
    (hI.mono fun x hx ↦ (ciSup_eq_ciSup_of_notMem_le (hbdd x) hIne hx).symm)

end TauCeti
