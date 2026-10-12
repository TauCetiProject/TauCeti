/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Submanifold.Basic
public import Mathlib.Topology.DiscreteSubset

/-!
# Zero-dimensional analytic submanifolds

A zero-dimensional analytic submanifold is discrete, and every nonempty discrete subset
of a finite-dimensional scalar space is a zero-dimensional analytic submanifold. In particular,
a preconnected zero-dimensional analytic submanifold consists of one point. This identifies
the bases on which polynomial lifting can use a refinement over a single point.

The chart condition is essential: a totally disconnected set need not be discrete.
Neither finiteness nor closedness of the submanifold is required.

## References

S. G. Krantz and H. R. Parks, *A Primer of Real Analytic Functions*, second edition,
Birkhäuser, 2002, Chapter 2 (analytic submanifolds).
-/

public section

open Set

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ} {S : Set (Fin n → 𝕜)}

/-- A zero-dimensional analytic submanifold is discrete in its subspace topology. -/
theorem IsAnalyticSubmanifold.isDiscrete (hS : IsAnalyticSubmanifold 0 S) : IsDiscrete S := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  obtain ⟨e, hxe, he⟩ := hS.exists_isAnalyticChart x hx
  refine ⟨e.source, e.open_source, ?_⟩
  have hzero (y) (hy : y ∈ e.source) (hyS : y ∈ S) : e y = 0 :=
    funext fun i ↦ (he.mem_iff hy).1 hyS i (Nat.zero_le _)
  ext y
  constructor
  · rintro ⟨hy, hyS⟩
    exact mem_singleton_iff.mpr (e.injOn hy hxe ((hzero y hy hyS).trans
      (hzero x hxe hx).symm))
  · rintro rfl
    exact ⟨hxe, hx⟩

/-- Every nonempty discrete subset is a zero-dimensional analytic submanifold.
The ambient charts are translations restricted to isolating neighborhoods. -/
theorem _root_.IsDiscrete.isAnalyticSubmanifold_zero (hS : IsDiscrete S) (hne : S.Nonempty) :
    IsAnalyticSubmanifold 0 S := by
  refine ⟨hne, Nat.zero_le _, fun x hx ↦ ?_⟩
  obtain ⟨U, hU, hUS⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hS x hx
  obtain ⟨e, hxe, he⟩ := (isAnalyticSubmanifold_singleton x).exists_isAnalyticChart x
    (mem_singleton x)
  have hxU : x ∈ U := (hUS.symm ▸ mem_singleton x).1
  refine ⟨e.restrOpen U hU, ⟨hxe, hxU⟩, (he.restrOpen hU).congr_set ?_⟩
  ext y
  simp only [OpenPartialHomeomorph.restrOpen_source, ← hUS, mem_inter_iff]
  tauto

/-- Zero-dimensional analytic submanifolds are precisely the nonempty discrete subsets. -/
@[simp]
theorem isAnalyticSubmanifold_zero_iff :
    IsAnalyticSubmanifold 0 S ↔ S.Nonempty ∧ IsDiscrete S :=
  ⟨fun hS ↦ ⟨hS.nonempty, hS.isDiscrete⟩,
    fun hS ↦ hS.2.isAnalyticSubmanifold_zero hS.1⟩

end TauCeti
