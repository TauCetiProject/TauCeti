/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Variational.BoundedSublevels
public import TauCeti.Analysis.Normed.Module.DoubleDual
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# The direct method in the weak topology

A weakly lower semicontinuous real energy on a nonempty weakly closed admissible set
attains its minimum if its sublevels are norm bounded and the canonical bidual map is
surjective. No lower bound on the energy is assumed: compactness of one nonempty sublevel
provides it. Every sublevel and the entire set of minimizers are weakly compact.

The reflexivity hypothesis is surjectivity of the continuous bidual inclusion, not
algebraic reflexivity. Completeness is not needed as a separate hypothesis. The proofs
work over any proper nontrivially normed field, and in seminormed spaces.

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2 (the direct method).
* V. Ivrii, *Partial Differential Equations*, §13.1, proof of Theorem 4.
-/

public section

open Set Bornology NormedSpace

namespace TauCeti

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  {E : V → ℝ} {S : Set V}

/-- On a weakly closed set in a reflexive space, a bounded sublevel of a weakly lower
semicontinuous energy is weakly compact. -/
theorem isCompact_sublevel_toWeakSpace
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (b : ℝ) (hb : IsBounded {u ∈ S | E u ≤ b}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  have heq : toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} =
      (toWeakSpace 𝕜 V '' S) ∩
        (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u)) ⁻¹' Iic b := by
    ext u
    simp only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage,
      mem_ofPred_eq, mem_inter_iff, mem_Iic]
  obtain ⟨C, hC, hEC⟩ := lowerSemicontinuousOn_iff_preimage_Iic.1 hE b
  have hclosed : IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
    rw [heq, hEC]
    exact hS.inter hC
  simpa only [hclosed.closure_eq] using isCompact_closure_toWeakSpace hV hb

/-- **The direct method.** A weakly lower semicontinuous energy with bounded sublevels on
a nonempty weakly closed set in a reflexive space attains its minimum. -/
theorem exists_isMinOn_of_weak_closed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hne : S.Nonempty) (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) : ∃ u ∈ S, IsMinOn E S u := by
  obtain ⟨v, hv⟩ := hne
  have hcompact := isCompact_sublevel_toWeakSpace hV hS hE (E v) (hb.isBounded_sublevel (E v))
  have hsubset : toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ E v} ⊆ toWeakSpace 𝕜 V '' S :=
    image_mono fun _ hx ↦ hx.1
  have hnelevel : (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ E v}).Nonempty :=
    ⟨toWeakSpace 𝕜 V v, mem_image_of_mem _ ⟨hv, le_rfl⟩⟩
  obtain ⟨w, hw, hmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn hnelevel hcompact (hE.mono hsubset)
  rw [isMinOn_iff] at hmin
  obtain ⟨u, hu, rfl⟩ := hw
  refine ⟨u, hu.1, ?_⟩
  rw [isMinOn_iff]
  intro x hx
  by_cases hlevel : E x ≤ E v
  · simpa only [LinearEquiv.symm_apply_apply] using
      hmin (toWeakSpace 𝕜 V x) (mem_image_of_mem (toWeakSpace 𝕜 V) ⟨hx, hlevel⟩)
  · exact hu.2.trans (le_of_not_ge hlevel)

/-- The full set of minimizers is weakly compact, including when the admissible set is empty. -/
theorem isCompact_minimizers_toWeakSpace
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) := by
  by_cases hne : S.Nonempty
  swap
  · simp [Set.not_nonempty_iff_eq_empty.1 hne]
  obtain ⟨u, hu, hmin⟩ := exists_isMinOn_of_weak_closed hV hne hS hE hb
  have heq : {x ∈ S | IsMinOn E S x} = {x ∈ S | E x ≤ E u} := by
    ext x
    exact ⟨fun hx ↦ ⟨hx.1, hx.2 hu⟩,
      fun hx ↦ ⟨hx.1, fun y hy ↦ hx.2.trans (hmin hy)⟩⟩
  rw [heq]
  exact isCompact_sublevel_toWeakSpace hV hS hE (E u) (hb.isBounded_sublevel (E u))

end TauCeti
