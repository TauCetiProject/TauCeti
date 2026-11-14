/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Local potentials of continuous one-forms

`TauCeti.HasLocalPotentials s φ` says that the covector field `φ` is the derivative of a `C¹`
function on a ball about each point of `s`. The ambient field is only used on `s`; its continuity
there follows from the potentials. In particular, no differentiability of the field itself is
required, and neither the domain nor the coefficient space needs to be complete.

This is the local input for integrating continuous one-forms along continuous paths by endpoint
differences of potentials. The predicate is local on open covers, is preserved by restriction
to open subsets, and pulls back along `C¹` maps. It is stated for real normed spaces so that
these operations also apply before specializing the domain to the complex plane.
-/

public section

open Set Metric Filter
open scoped Topology ContDiff

namespace TauCeti

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {s t : Set E} {φ ψ : E → E →L[ℝ] F}

/-- A covector field has local potentials on `s` if each point has a ball contained in `s`
on which the field is the derivative of an ambient `C¹` function. -/
def HasLocalPotentials (s : Set E) (φ : E → E →L[ℝ] F) : Prop :=
  ∀ x ∈ s, ∃ r > 0, ball x r ⊆ s ∧ ∃ g : E → F,
    ContDiffOn ℝ 1 g (ball x r) ∧ ∀ y ∈ ball x r, HasFDerivAt g (φ y) y

/-- The ball criterion for local potentials. -/
theorem hasLocalPotentials_iff : HasLocalPotentials s φ ↔
    ∀ x ∈ s, ∃ r > 0, ball x r ⊆ s ∧ ∃ g : E → F,
      ContDiffOn ℝ 1 g (ball x r) ∧ ∀ y ∈ ball x r, HasFDerivAt g (φ y) y := Iff.rfl

/-- Every field has local potentials on the empty domain. -/
@[simp]
theorem hasLocalPotentials_empty : HasLocalPotentials ∅ φ := by
  simp [HasLocalPotentials]

/-- A domain carrying local potentials is open. -/
theorem HasLocalPotentials.isOpen (hφ : HasLocalPotentials s φ) : IsOpen s := by
  exact Metric.isOpen_iff.mpr fun x hx ↦ (hφ x hx).imp fun r hr ↦ ⟨hr.1, hr.2.1⟩

/-- A single `C¹` potential on an open set supplies local potentials. -/
theorem hasLocalPotentials_of_hasFDerivAt (hs : IsOpen s) {g : E → F}
    (hg : ContDiffOn ℝ 1 g s) (hd : ∀ x ∈ s, HasFDerivAt g (φ x) x) :
    HasLocalPotentials s φ := by
  intro x hx
  obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp hs x hx
  exact ⟨r, hr, hrs, g, hg.mono hrs, fun y hy ↦ hd y (hrs hy)⟩

/-- Restrict local potentials to an open subset. -/
theorem HasLocalPotentials.mono (hφ : HasLocalPotentials s φ) (ht : IsOpen t) (hts : t ⊆ s) :
    HasLocalPotentials t φ := by
  intro x hx
  obtain ⟨r, hr, -, g, hg, hd⟩ := hφ x (hts hx)
  obtain ⟨q, hq, hqt⟩ := Metric.isOpen_iff.mp ht x hx
  have hbr : ball x (min r q) ⊆ ball x r := ball_subset_ball (min_le_left _ _)
  exact ⟨min r q, lt_min hr hq, (ball_subset_ball (min_le_right _ _)).trans hqt,
    g, hg.mono hbr, fun y hy ↦ hd y (hbr hy)⟩

/-- Local potentials depend only on the field on their domain. -/
theorem HasLocalPotentials.congr (hφ : HasLocalPotentials s φ) (h : EqOn φ ψ s) :
    HasLocalPotentials s ψ := by
  intro x hx
  obtain ⟨r, hr, hrs, g, hg, hd⟩ := hφ x hx
  exact ⟨r, hr, hrs, g, hg, fun y hy ↦ h (hrs hy) ▸ hd y hy⟩

/-- Equality on the domain preserves and reflects local potentials. -/
theorem hasLocalPotentials_congr (h : EqOn φ ψ s) :
    HasLocalPotentials s φ ↔ HasLocalPotentials s ψ :=
  ⟨fun hφ ↦ hφ.congr h, fun hψ ↦ hψ.congr h.symm⟩

/-- Potentials on a family of domains give potentials on their union. -/
theorem hasLocalPotentials_iUnion {ι : Sort*} {u : ι → Set E}
    (h : ∀ i, HasLocalPotentials (u i) φ) : HasLocalPotentials (⋃ i, u i) φ := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  obtain ⟨r, hr, hrs, g, hg, hd⟩ := h i x hi
  exact ⟨r, hr, hrs.trans (subset_iUnion u i), g, hg, hd⟩

/-- Local potentials can be checked on any open cover. -/
theorem hasLocalPotentials_iUnion_iff {ι : Sort*} {u : ι → Set E}
    (hu : ∀ i, IsOpen (u i)) :
    HasLocalPotentials (⋃ i, u i) φ ↔ ∀ i, HasLocalPotentials (u i) φ :=
  ⟨fun h i ↦ h.mono (hu i) (subset_iUnion u i), hasLocalPotentials_iUnion⟩

/-- A field with local `C¹` potentials is continuous on its domain. -/
theorem HasLocalPotentials.continuousOn (hφ : HasLocalPotentials s φ) : ContinuousOn φ s := by
  intro x hx
  obtain ⟨r, hr, -, g, hg, hd⟩ := hφ x hx
  have hc : ContinuousOn φ (ball x r) :=
    (hg.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).congr
      (fun y hy ↦ (hd y hy).fderiv.symm)
  exact (hc.continuousAt (ball_mem_nhds x hr)).continuousWithinAt

/-- The constant covector field has a linear potential on every open domain. In particular,
the real-part covector on the complex plane has local potentials. -/
theorem hasLocalPotentials_const (hs : IsOpen s) (L : E →L[ℝ] F) :
    HasLocalPotentials s (fun _ ↦ L) :=
  hasLocalPotentials_of_hasFDerivAt hs L.contDiff.contDiffOn fun _ _ ↦ L.hasFDerivAt

/-- The zero form has local potentials on every open domain. -/
theorem hasLocalPotentials_zero (hs : IsOpen s) : HasLocalPotentials s (0 : E → E →L[ℝ] F) :=
  hasLocalPotentials_const hs 0

/-- The sum of two locally potential fields is locally potential. -/
theorem HasLocalPotentials.add (hφ : HasLocalPotentials s φ) (hψ : HasLocalPotentials s ψ) :
    HasLocalPotentials s (φ + ψ) := by
  intro x hx
  obtain ⟨r, hr, hrs, g, hg, hdg⟩ := hφ x hx
  obtain ⟨q, hq, -, h, hh, hdh⟩ := hψ x hx
  have hbr : ball x (min r q) ⊆ ball x r := ball_subset_ball (min_le_left _ _)
  have hbq : ball x (min r q) ⊆ ball x q := ball_subset_ball (min_le_right _ _)
  exact ⟨min r q, lt_min hr hq, hbr.trans hrs, g + h, (hg.mono hbr).add (hh.mono hbq),
    fun y hy ↦ (hdg y (hbr hy)).add (hdh y (hbq hy))⟩

/-- Negating potentials gives potentials for the negative field. -/
theorem HasLocalPotentials.neg (hφ : HasLocalPotentials s φ) : HasLocalPotentials s (-φ) := by
  intro x hx
  obtain ⟨r, hr, hrs, g, hg, hd⟩ := hφ x hx
  exact ⟨r, hr, hrs, -g, hg.neg, fun y hy ↦ (hd y hy).neg⟩

/-- Subtracting locally potential fields preserves local potentials. -/
theorem HasLocalPotentials.sub (hφ : HasLocalPotentials s φ) (hψ : HasLocalPotentials s ψ) :
    HasLocalPotentials s (φ - ψ) := by
  simpa only [sub_eq_add_neg] using hφ.add hψ.neg

/-- Constant scalar multiples preserve local potentials. -/
theorem HasLocalPotentials.smul (hφ : HasLocalPotentials s φ) (c : ℝ) :
    HasLocalPotentials s (c • φ) := by
  intro x hx
  obtain ⟨r, hr, hrs, g, hg, hd⟩ := hφ x hx
  exact ⟨r, hr, hrs, c • g, hg.const_smul c, fun y hy ↦ (hd y hy).const_smul c⟩

/-- Pullback of a locally potential covector field along a `C¹` map of open domains has
local potentials, obtained by composing each potential with the map. -/
theorem HasLocalPotentials.pullback {u : Set G} {f : G → E}
    (hφ : HasLocalPotentials s φ) (hu : IsOpen u) (hf : ContDiffOn ℝ 1 f u)
    (hfs : MapsTo f u s) :
    HasLocalPotentials u (fun x ↦ (φ (f x)).comp (fderiv ℝ f x)) := by
  intro x hx
  obtain ⟨r, hr, -, g, hg, hd⟩ := hφ (f x) (hfs hx)
  have hn : f ⁻¹' ball (f x) r ∩ u ∈ 𝓝 x :=
    inter_mem ((hf.continuousOn.continuousAt (hu.mem_nhds hx)).preimage_mem_nhds
      (ball_mem_nhds _ hr)) (hu.mem_nhds hx)
  obtain ⟨q, hq, hqsub⟩ := Metric.mem_nhds_iff.mp hn
  have hqu : ball x q ⊆ u := fun y hy ↦ (hqsub hy).2
  have hqb : MapsTo f (ball x q) (ball (f x) r) := fun y hy ↦ (hqsub hy).1
  refine ⟨q, hq, hqu, g ∘ f, hg.comp (hf.mono hqu) hqb, fun y hy ↦ ?_⟩
  exact (hd (f y) (hqb hy)).comp y
    ((hf.differentiableOn one_ne_zero y (hqu hy)).differentiableAt
      (hu.mem_nhds (hqu hy))).hasFDerivAt

end TauCeti
