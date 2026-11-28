/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Semicontinuity.Basic
public import TauCeti.Analysis.Normed.Module.DoubleDual
public import TauCeti.Analysis.Variational.BoundedSublevels
public import TauCeti.Order.Filter.Extr
import TauCeti.Analysis.LocallyConvex.WeakSpace.Basic

/-!
# The direct method in the weak topology

A weakly lower semicontinuous energy taking values in a linear order on a nonempty weakly
closed admissible set attains its minimum if its sublevels are norm bounded and the canonical
bidual map is surjective. No lower bound on the energy is assumed: compactness of one nonempty
sublevel provides it. Every sublevel and the entire set of minimizers are weakly compact.

Over `ℝ` or `ℂ`, an energy with norm-bounded sublevels on `S` is globally weakly lower
semicontinuous on `S` as soon as it is weakly lower semicontinuous on every norm-bounded subset
of `S` (`TauCeti.lowerSemicontinuousOn_comp_toWeakSpace_symm_of_hasBoundedSublevelsOn`).

The reflexivity hypothesis is surjectivity of the continuous bidual inclusion, not
algebraic reflexivity. Completeness is not needed as a separate hypothesis. Except for the
bounded-sublevel localization of weak lower semicontinuity (which uses geometric Hahn–Banach over
`ℝ` or `ℂ`), the proofs work over any proper nontrivially normed field, and in seminormed spaces.

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2 (the direct method).
* V. Ivrii, *Partial Differential Equations*, §13.1, proof of Theorem 4.
-/

public section

open Set Bornology NormedSpace

namespace TauCeti

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}

/-- On a weakly closed set in a reflexive space, a bounded sublevel of a weakly lower
semicontinuous energy is weakly compact. -/
theorem isCompact_toWeakSpace_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (b : β) (hb : IsBounded {u ∈ S | E u ≤ b}) :
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
  simpa only [hclosed.closure_eq] using isCompact_closure_toWeakSpace_of_isBounded hV hb

/-- A single nonempty bounded sublevel suffices for the direct method on a weakly
closed admissible set. -/
theorem exists_isMinOn_of_weak_closed_of_isBounded_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    {b : β} (hne : {u ∈ S | E u ≤ b}.Nonempty)
    (hb : IsBounded {u ∈ S | E u ≤ b}) : ∃ u ∈ S, IsMinOn E S u := by
  have hcompact := isCompact_toWeakSpace_sublevel hV hS hE b hb
  have hsubset : toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} ⊆ toWeakSpace 𝕜 V '' S :=
    image_mono fun _ hx ↦ hx.1
  obtain ⟨w, hw, hmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn (hne.image _) hcompact (hE.mono hsubset)
  obtain ⟨u, hu, rfl⟩ := hw
  refine ⟨u, hu.1, (isMinOn_sublevel_iff hu.2).1 fun x hx ↦ ?_⟩
  simpa only [mem_ofPred_eq, LinearEquiv.symm_apply_apply] using
    hmin (mem_image_of_mem (toWeakSpace 𝕜 V) hx)

/-- **The direct method.** A weakly lower semicontinuous energy with bounded sublevels on
a nonempty weakly closed set in a reflexive space attains its minimum. -/
theorem exists_isMinOn_of_weak_closed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hne : S.Nonempty) (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) : ∃ u ∈ S, IsMinOn E S u := by
  obtain ⟨v, hv⟩ := hne
  exact exists_isMinOn_of_weak_closed_of_isBounded_sublevel hV hS hE
    ⟨v, hv, le_rfl⟩ (hb.isBounded_sublevel (E v))

/-- If the full set of minimizers of a weakly lower semicontinuous energy on a weakly
closed set in a reflexive space is bounded, then that set of minimizers is weakly compact. -/
theorem isCompact_toWeakSpace_minimizers_of_isBounded
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : IsBounded {u ∈ S | IsMinOn E S u}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) := by
  obtain hempty | ⟨u, hu, hmin⟩ := {u ∈ S | IsMinOn E S u}.eq_empty_or_nonempty
  · simp [hempty]
  · rw [hmin.minimizers_eq_sublevel hu] at hb ⊢
    exact isCompact_toWeakSpace_sublevel hV hS hE (E u) hb

/-- For a weakly lower semicontinuous energy with bounded sublevels on a weakly closed set
in a reflexive space, the set of minimizers is weakly compact, including when the admissible
set is empty. -/
theorem isCompact_toWeakSpace_minimizers
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) :=
  isCompact_toWeakSpace_minimizers_of_isBounded hV hS hE hb.isBounded_minimizers

section RCLike

/-- **Sublevel localization of weak lower semicontinuity.** Over `ℝ` or `ℂ`, an energy `E` with
norm-bounded sublevels on `S` is globally weakly lower semicontinuous on `S` as soon as it is
weakly lower semicontinuous on every norm-bounded subset of `S`. No weak closedness assumption on
`S` is needed. -/
theorem lowerSemicontinuousOn_comp_toWeakSpace_symm_of_hasBoundedSublevelsOn {𝕜 V β : Type*}
    [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] [LinearOrder β] {E : V → β}
    {S : Set V} (hb : HasBoundedSublevelsOn E S)
    (hloc : ∀ ⦃B : Set V⦄, B ⊆ S → IsBounded B →
      LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
        (toWeakSpace 𝕜 V '' B)) :
    LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) := by
  let f : WeakSpace 𝕜 V → β := fun w ↦ E ((toWeakSpace 𝕜 V).symm w)
  rw [lowerSemicontinuousOn_iff_preimage_Iic]
  intro b
  -- Every point of `S` with `E u ≤ b` lies in a closed norm ball `closedBall 0 R`, which is weakly
  -- closed by Hahn–Banach.
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : V)).1 (hb.isBounded_sublevel b)
  let B : Set V := S ∩ Metric.closedBall 0 R
  have hB_lsc : LowerSemicontinuousOn f (toWeakSpace 𝕜 V '' B) :=
    hloc inter_subset_left (Metric.isBounded_closedBall.subset inter_subset_right)
  obtain ⟨v₀, hv₀, hBv₀⟩ := lowerSemicontinuousOn_iff_preimage_Iic.1 hB_lsc b
  refine ⟨(toWeakSpace 𝕜 V '' Metric.closedBall 0 R) ∩ v₀,
    (isClosed_toWeakSpace_closedBall (0 : V) R).inter hv₀, ?_⟩
  have hinter : (toWeakSpace 𝕜 V '' S) ∩ ((toWeakSpace 𝕜 V '' Metric.closedBall 0 R) ∩ v₀) =
      (toWeakSpace 𝕜 V '' B) ∩ v₀ := by
    rw [← inter_assoc, ← image_inter (toWeakSpace 𝕜 V).injective]
  rw [hinter, ← hBv₀]
  have hsub : {u ∈ S | E u ≤ b} = {u ∈ B | E u ≤ b} :=
    ((inter_right_comm S (Metric.closedBall (0 : V) R) {u | E u ≤ b}).trans
      (inter_eq_left.2 hR)).symm
  calc (toWeakSpace 𝕜 V '' S) ∩ (f ⁻¹' Iic b)
      = toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} :=
        (image_inter_preimage (toWeakSpace 𝕜 V) S (f ⁻¹' Iic b)).symm
    _ = toWeakSpace 𝕜 V '' {u ∈ B | E u ≤ b} := by rw [hsub]
    _ = (toWeakSpace 𝕜 V '' B) ∩ (f ⁻¹' Iic b) :=
        image_inter_preimage (toWeakSpace 𝕜 V) B (f ⁻¹' Iic b)

end RCLike

end TauCeti
