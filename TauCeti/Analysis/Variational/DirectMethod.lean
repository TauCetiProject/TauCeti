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
import TauCeti.Analysis.Normed.Module.WeakSpace.Closure
import TauCeti.Topology.Algebra.Module.WeakSpace
import TauCeti.Topology.Semicontinuity.Basic

/-!
# The direct method in the weak topology

A weakly lower semicontinuous energy taking values in a linear order on a nonempty weakly
closed admissible set attains its minimum if its sublevels are norm bounded and the canonical
bidual map is surjective. No lower bound on the energy is assumed: compactness of one nonempty
sublevel provides it. Every sublevel and the entire set of minimizers are weakly compact.

More generally, the same conclusions hold whenever the admissible set `S` is only weakly closed on
every closed norm ball `S ∩ closedBall 0 R`
(`TauCeti.exists_isMinOn_of_isClosed_toWeakSpace_inter_closedBall`,
`TauCeti.isCompact_toWeakSpace_minimizers_of_isClosed_toWeakSpace_inter_closedBall`), without
requiring `S` itself to be globally weakly closed. Over `ℝ` or `ℂ`, an energy with norm-bounded
sublevels on `S` is globally weakly lower semicontinuous on `S` as soon as it is weakly lower
semicontinuous on every norm-bounded subset of `S`
(`TauCeti.lowerSemicontinuousOn_comp_toWeakSpace_symm_of_hasBoundedSublevelsOn`).

The reflexivity hypothesis is surjectivity of the continuous bidual inclusion, not
algebraic reflexivity. Completeness is not needed as a separate hypothesis. Except for the
bounded-sublevel localization of weak lower semicontinuity (which uses geometric Hahn–Banach over
`ℝ` or `ℂ`), the proofs work over any proper nontrivially normed field, and in seminormed spaces.

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2 (the direct method).
* V. Ivrii, *Partial Differential Equations*, §13.1, proof of Theorem 4.
-/

public section

open Set Bornology Metric NormedSpace

namespace TauCeti

section WeakTopology

variable {𝕜 V : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid V] [Module 𝕜 V] [TopologicalSpace V]

/-- On a weakly closed admissible set `S`, every sublevel of a weakly lower semicontinuous energy
is weakly closed. -/
theorem isClosed_toWeakSpace_sublevel {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}
    (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (b : β) :
    IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  rw [show {u ∈ S | E u ≤ b} = S ∩ toWeakSpace 𝕜 V ⁻¹'
      ((fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u)) ⁻¹' Iic b) from rfl,
    image_inter_preimage]
  exact hE.isClosed_inter_preimage_Iic hS b

/-- An energy weakly lower semicontinuous on a nonempty weakly compact sublevel
`{u ∈ S | E u ≤ b}` attains its minimum on `S`. -/
theorem exists_isMinOn_of_isCompact_toWeakSpace_sublevel {β : Type*} [LinearOrder β] {E : V → β}
    {S : Set V} {b : β}
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}))
    (hne : {u ∈ S | E u ≤ b}.Nonempty)
    (hcpt : IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b})) :
    ∃ u ∈ S, IsMinOn E S u := by
  have heq : {w ∈ toWeakSpace 𝕜 V '' S | E ((toWeakSpace 𝕜 V).symm w) ≤ b} =
      toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} :=
    (image_inter_preimage (toWeakSpace 𝕜 V) S
      ((fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u)) ⁻¹' Iic b)).symm
  obtain ⟨w, hw, hmin⟩ :=
    (heq ▸ hE).exists_isMinOn_of_isCompact_sublevel (heq ▸ hne.image _) (heq ▸ hcpt)
  obtain ⟨u, hu, rfl⟩ := hw
  exact ⟨u, hu, by
    simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using
      hmin.comp_of_mapsTo (mapsTo_image (toWeakSpace 𝕜 V) S) rfl⟩

/-- If the sublevel at every minimizer of `E` on `S` is weakly compact, then the full set of
minimizers of `E` on `S` is weakly compact (including when it is empty). -/
theorem isCompact_toWeakSpace_minimizers_of_isCompact_sublevel {β : Type*} [Preorder β]
    {E : V → β} {S : Set V}
    (h : ∀ u ∈ S, IsMinOn E S u → IsCompact (toWeakSpace 𝕜 V '' {x ∈ S | E x ≤ E u})) :
    IsCompact (toWeakSpace 𝕜 V '' {x ∈ S | IsMinOn E S x}) := by
  obtain hempty | ⟨u, hu, hmin⟩ := {x ∈ S | IsMinOn E S x}.eq_empty_or_nonempty
  · simp [hempty]
  · rw [hmin.minimizers_eq_sublevel hu]
    exact h u hu hmin

end WeakTopology

section ClosedBallSublevel

variable {𝕜 V : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [SeminormedAddCommGroup V] [Module 𝕜 V]
  {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}

/-- If `S ∩ closedBall 0 R` is weakly closed for every `R : ℝ` and `E` is weakly lower
semicontinuous on `S`, then every norm-bounded sublevel `{u ∈ S | E u ≤ b}` is weakly closed. -/
theorem isClosed_toWeakSpace_sublevel_of_isClosed_toWeakSpace_inter_closedBall
    (hS : ∀ R : ℝ, IsClosed (toWeakSpace 𝕜 V '' (S ∩ closedBall 0 R)))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (b : β) (hb : IsBounded {u ∈ S | E u ≤ b}) :
    IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (0 : V)).1 hb
  have heq : {u ∈ S | E u ≤ b} = {u ∈ S ∩ closedBall 0 R | E u ≤ b} := by
    ext u
    exact ⟨fun hu ↦ ⟨⟨hu.1, hR hu⟩, hu.2⟩, fun hu ↦ ⟨hu.1.1, hu.2⟩⟩
  rw [heq]
  exact isClosed_toWeakSpace_sublevel (hS R) (hE.mono (image_mono inter_subset_left)) b

end ClosedBallSublevel

section Reflexive

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
  have hclosed := isClosed_toWeakSpace_sublevel hS hE b
  simpa only [hclosed.closure_eq] using isCompact_closure_toWeakSpace_of_isBounded hV hb

/-- A single nonempty bounded sublevel suffices for the direct method on a weakly
closed admissible set. -/
theorem exists_isMinOn_of_weak_closed_of_isBounded_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    {b : β} (hne : {u ∈ S | E u ≤ b}.Nonempty)
    (hb : IsBounded {u ∈ S | E u ≤ b}) : ∃ u ∈ S, IsMinOn E S u :=
  exists_isMinOn_of_isCompact_toWeakSpace_sublevel (hE.mono (image_mono (sep_subset S _))) hne
    (isCompact_toWeakSpace_sublevel hV hS hE b hb)

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
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) :=
  isCompact_toWeakSpace_minimizers_of_isCompact_sublevel fun u hu hmin ↦
    isCompact_toWeakSpace_sublevel hV hS hE (E u) (hmin.minimizers_eq_sublevel hu ▸ hb)

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

/-- In a reflexive seminormed space over a proper field, if `S ∩ closedBall 0 R` is weakly closed
for every `R : ℝ` and `E` is weakly lower semicontinuous on `S`, then every norm-bounded sublevel
`{u ∈ S | E u ≤ b}` is weakly compact. -/
theorem isCompact_toWeakSpace_sublevel_of_isClosed_toWeakSpace_inter_closedBall
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : ∀ R : ℝ, IsClosed (toWeakSpace 𝕜 V '' (S ∩ closedBall 0 R)))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (b : β) (hb : IsBounded {u ∈ S | E u ≤ b}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  have hclosed := isClosed_toWeakSpace_sublevel_of_isClosed_toWeakSpace_inter_closedBall hS hE b hb
  simpa only [hclosed.closure_eq] using isCompact_closure_toWeakSpace_of_isBounded hV hb

/-- **Single-sublevel direct method with bounded-ball weak closedness.** In a reflexive seminormed
space over a proper field, if `S ∩ closedBall 0 R` is weakly closed for every `R : ℝ` and `E` is
weakly lower semicontinuous on `S`, then a single nonempty norm-bounded sublevel `{u ∈ S | E u ≤ b}`
suffices for `E` to attain its minimum on `S`. -/
theorem exists_isMinOn_of_isClosed_toWeakSpace_inter_closedBall_of_isBounded_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : ∀ R : ℝ, IsClosed (toWeakSpace 𝕜 V '' (S ∩ closedBall 0 R)))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    {b : β} (hne : {u ∈ S | E u ≤ b}.Nonempty)
    (hb : IsBounded {u ∈ S | E u ≤ b}) : ∃ u ∈ S, IsMinOn E S u :=
  exists_isMinOn_of_isCompact_toWeakSpace_sublevel (hE.mono (image_mono (sep_subset S _))) hne
    (isCompact_toWeakSpace_sublevel_of_isClosed_toWeakSpace_inter_closedBall hV hS hE b hb)

/-- **Direct method with bounded-ball weak closedness.** In a reflexive seminormed space over a
proper field, if `S` is nonempty, `S ∩ closedBall 0 R` is weakly closed for every `R : ℝ`, and `E`
is weakly lower semicontinuous with norm-bounded sublevels on `S`, then `E` attains its minimum on
`S`. -/
theorem exists_isMinOn_of_isClosed_toWeakSpace_inter_closedBall
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hne : S.Nonempty) (hS : ∀ R : ℝ, IsClosed (toWeakSpace 𝕜 V '' (S ∩ closedBall 0 R)))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) : ∃ u ∈ S, IsMinOn E S u := by
  obtain ⟨v, hv⟩ := hne
  exact exists_isMinOn_of_isClosed_toWeakSpace_inter_closedBall_of_isBounded_sublevel hV hS hE
    ⟨v, hv, le_rfl⟩ (hb.isBounded_sublevel (E v))

/-- In a reflexive seminormed space over a proper field, if `S ∩ closedBall 0 R` is weakly closed
for every `R : ℝ`, `E` is weakly lower semicontinuous on `S`, and the set of minimizers of `E` on
`S` is norm-bounded, then that set of minimizers is weakly compact. -/
theorem isCompact_toWeakSpace_minimizers_of_isClosed_toWeakSpace_inter_closedBall_of_isBounded
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : ∀ R : ℝ, IsClosed (toWeakSpace 𝕜 V '' (S ∩ closedBall 0 R)))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : IsBounded {u ∈ S | IsMinOn E S u}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) :=
  isCompact_toWeakSpace_minimizers_of_isCompact_sublevel fun u hu hmin ↦
    isCompact_toWeakSpace_sublevel_of_isClosed_toWeakSpace_inter_closedBall hV hS hE (E u)
      (hmin.minimizers_eq_sublevel hu ▸ hb)

/-- In a reflexive seminormed space over a proper field, if `S ∩ closedBall 0 R` is weakly closed
for every `R : ℝ` and `E` is weakly lower semicontinuous with norm-bounded sublevels on `S`, then
the set of minimizers of `E` on `S` is weakly compact, including when `S` is empty. -/
theorem isCompact_toWeakSpace_minimizers_of_isClosed_toWeakSpace_inter_closedBall
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : ∀ R : ℝ, IsClosed (toWeakSpace 𝕜 V '' (S ∩ closedBall 0 R)))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) :=
  isCompact_toWeakSpace_minimizers_of_isClosed_toWeakSpace_inter_closedBall_of_isBounded hV hS hE
    hb.isBounded_minimizers

end Reflexive

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
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (0 : V)).1 (hb.isBounded_sublevel b)
  let B : Set V := S ∩ closedBall 0 R
  have hB_lsc : LowerSemicontinuousOn f (toWeakSpace 𝕜 V '' B) :=
    hloc inter_subset_left (isBounded_closedBall.subset inter_subset_right)
  obtain ⟨v₀, hv₀, hBv₀⟩ := lowerSemicontinuousOn_iff_preimage_Iic.1 hB_lsc b
  refine ⟨(toWeakSpace 𝕜 V '' closedBall 0 R) ∩ v₀,
    (isClosed_toWeakSpace_closedBall (0 : V) R).inter hv₀, ?_⟩
  have hinter : (toWeakSpace 𝕜 V '' S) ∩ ((toWeakSpace 𝕜 V '' closedBall 0 R) ∩ v₀) =
      (toWeakSpace 𝕜 V '' B) ∩ v₀ := by
    rw [← inter_assoc, ← image_inter (toWeakSpace 𝕜 V).injective]
  rw [hinter, ← hBv₀]
  ext w
  constructor
  · rintro ⟨⟨u, huS, rfl⟩, hfb⟩
    have hu_le : E u ≤ b := by simpa only [f, mem_preimage, mem_Iic,
      LinearEquiv.symm_apply_apply] using hfb
    exact ⟨mem_image_of_mem _ ⟨huS, hR ⟨huS, hu_le⟩⟩, hfb⟩
  · rintro ⟨⟨u, huB, rfl⟩, hfb⟩
    exact ⟨mem_image_of_mem _ huB.1, hfb⟩

end RCLike

end TauCeti
