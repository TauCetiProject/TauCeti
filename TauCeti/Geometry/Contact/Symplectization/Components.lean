/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Coorientation
public import TauCeti.Geometry.Contact.Symplectization.Trivialization
public import TauCeti.Topology.VectorBundle.Orientation.PositiveSection
public import TauCeti.Topology.VectorBundle.Orientation.ZeroSectionCompl

/-!
# The connected components of the symplectization of a contact structure

Let `ξ` be a contact structure on a connected finite-dimensional manifold `M`, with no defining
one-form or coorientation chosen. Its symplectization is the complement `ξ⁰ ∖ 0` of the zero
section in the annihilator line `ξ⁰ ⊂ T*M`
(`TauCeti.IsContactDistribution.annihilatorPunctured`), the dual of the contact line
`L = TM ⧸ ξ` with its zero section removed. This file determines its connected components.

* If `ξ` is the kernel of a contact form `α`, the symplectization has exactly two components: the
  covectors `eᵗ α_x`, the image of the trivialization `κ_α : ℝ × M → ξ⁰`
  (`TauCeti.SmoothForm.symplectizationToAnnihilator`), and the covectors `-eᵗ α_x`, the image of
  `κ_(-α)` (`TauCeti.IsContactDistribution.connectedComponent_eq_preimage_range_or_neg`). The
  fibre negation `ℓ ↦ -ℓ` exchanges them
  (`TauCeti.SmoothForm.vectorBundleScalarDiffeomorph_symplectizationToAnnihilator_of_neg`), and
  `κ_α` pulls the symplectic form `dθ` back to the form `d(eᵗ α)` of the symplectization `ℝ × M`
  of `α`.
* If `ξ` is not the kernel of any global contact form, the symplectization is connected, provided
  `M` is Hausdorff and σ-compact. Together with the previous case, connectedness of `ξ⁰ ∖ 0`
  characterizes the contact structures that are not coorientable
  (`TauCeti.IsContactDistribution.connectedSpace_annihilatorPunctured_iff`).

Both statements rest on the topology of real line bundles: the complement of the zero section of a
line bundle over a connected base is connected exactly when the bundle is not orientable
(`TauCeti.connectedSpace_zeroSectionCompl_iff_isEmpty`), and the annihilator line of a contact
structure is orientable exactly when the structure is the kernel of a global contact form
(`TauCeti.IsContactDistribution.exists_isContactForm_kerDistribution_eq_iff_nonempty_orientation`).

For example, the contact structure of the space of contact elements `ℝ² × ℝP¹` of the plane is not
coorientable; its symplectization is identified with the nonzero covectors `T*ℝ² ∖ 0`, which form
a connected space.

## Main results

* `TauCeti.IsContactDistribution.exists_isContactForm_kerDistribution_eq_iff_nonempty_orientation`:
  a contact structure is the kernel of a global contact form exactly when its annihilator line is
  orientable.
* `TauCeti.IsContactDistribution.not_connectedSpace_annihilatorPunctured`: the symplectization of
  the kernel of a contact form is disconnected.
* `TauCeti.IsContactDistribution.connectedSpace_annihilatorPunctured_iff`: the symplectization is
  connected exactly when the contact structure is not coorientable.
* `TauCeti.IsContactDistribution.connectedComponent_eq_preimage_range_or_neg`: for `ξ = ker α`,
  the components of the symplectization are the images of `κ_α` and `κ_(-α)`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Springer, 1989,
  Appendix 4 (the symplectification of a contact manifold and the space of contact elements).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1 and Appendix B (coorientability and the symplectization of a contact structure).
-/

public section

noncomputable section

open Bundle Function Manifold Module Set Topology
open scoped Manifold ContDiff

namespace TauCeti

open CotangentBundle

namespace IsContactDistribution

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {ξ : Π x : M, Submodule ℝ (TangentSpace I x)}

/-- `C^(∞ + 1)` charts, needed by the annihilator bundle construction of
`TauCeti.IsContMDiffDistribution.annihilatorContMDiffVectorBundle` at smoothness `∞`. -/
local instance : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)

variable [Nonempty M] (hξ : IsContactDistribution I ∞ ξ)

/-- If a contact structure `ξ` is the kernel of a contact form `α`, its annihilator line is
orientable: `x ↦ α_x` is a continuous section of `ξ⁰` vanishing nowhere. -/
theorem nonempty_vectorBundleOrientation_of_isContactForm {α : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) (hαξ : α.kerDistribution = ξ) :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    Nonempty (VectorBundleOrientation (Fin 1 → ℝ) (fun x ↦ annihilatorSpace I ξ x) (Fin 1)) :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  by
  have hj := hξ.isContMDiffDistribution.isSmoothEmbedding_annihilatorInclusion (n := ∞)
    hξ.finrank_sub_one_add_one
  -- The covector `α_x` vanishes on `ker α_x = ξ x`.
  have hmem (x : M) : SmoothForm.degreeOneEquiv α x ∈ annihilatorSpace I ξ x := by
    refine mem_annihilatorSpace_iff.2 fun v hv ↦ ?_
    rw [← hαξ, SmoothForm.mem_kerDistribution] at hv
    rw [SmoothForm.degreeOneEquiv_apply_apply_vec, hv]
  let s (x : M) : annihilatorSpace I ξ x := ⟨_, hmem x⟩
  -- Followed by the embedding `ξ⁰ → T*M`, the section `s` is the smooth section `x ↦ α_x`.
  have hs : Continuous fun x ↦ TotalSpace.mk' (Fin 1 → ℝ) x (s x) := by
    refine hj.isEmbedding.isInducing.continuous_iff.2 ?_
    have hcomp :
        annihilatorInclusion I ξ (Fin 1 → ℝ) ∘ (fun x ↦ TotalSpace.mk' (Fin 1 → ℝ) x (s x)) =
          fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x) :=
      funext fun x ↦ by simp [s]
    rw [hcomp]
    exact (SmoothForm.degreeOneEquiv α).contMDiff.continuous
  -- A contact form vanishes nowhere.
  have hs₀ (x : M) : s x ≠ 0 := fun h ↦ by
    obtain ⟨v, hv⟩ := hα.exists_ne_zero x
    have h' := congrArg (fun p : annihilatorSpace I ξ x ↦ (p : TangentSpace I x →L[ℝ] ℝ) v) h
    simp only [s, ZeroMemClass.coe_zero, SmoothForm.degreeOneEquiv_apply_apply_vec] at h'
    exact hv h'
  exact ⟨VectorBundleOrientation.ofContinuousNonvanishingSection
    (fun x ↦ (VectorBundle.continuousLinearEquivAt ℝ (Fin 1 → ℝ) (fun x ↦ annihilatorSpace I ξ x)
      x).toLinearEquiv.finrank_eq.trans (finrank_fin_fun ℝ)) hs hs₀⟩

/-- **Coorientability is orientability of the annihilator line.** On a Hausdorff σ-compact
manifold, a contact structure `ξ` is the kernel of a global contact form exactly when its
annihilator line `ξ⁰`, the dual of the contact line `TM ⧸ ξ`, is orientable. -/
theorem exists_isContactForm_kerDistribution_eq_iff_nonempty_orientation [T2Space M]
    [SigmaCompactSpace M] :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    (∃ α : SmoothForm I M ℝ 1, α.IsContactForm ∧ α.kerDistribution = ξ) ↔
      Nonempty (VectorBundleOrientation (Fin 1 → ℝ) (fun x ↦ annihilatorSpace I ξ x) (Fin 1)) :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  by
  refine ⟨fun ⟨α, hα, hαξ⟩ ↦ hξ.nonempty_vectorBundleOrientation_of_isContactForm hα hαξ,
    fun ⟨o⟩ ↦ ?_⟩
  -- An orientation of `ξ⁰` gives a continuous nowhere-vanishing section of `ξ⁰`, hence of `T*M`.
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨s, hs, hs₀⟩ := o.exists_continuous_section_ne_zero (by simp)
  refine hξ.exists_isContactForm_kerDistribution_eq_iff_exists_continuous.2
    ⟨fun x ↦ s x, ?_, fun x ↦ ⟨fun h ↦ hs₀ x (Subtype.ext h), (s x).property⟩⟩
  refine ((hξ.isContMDiffDistribution.contMDiff_annihilatorInclusion
    hξ.finrank_sub_one_add_one).continuous.comp hs).congr fun x ↦ ?_
  simp

/-- **The symplectization of a non-coorientable contact structure is connected.** On a connected
Hausdorff σ-compact manifold, the complement `ξ⁰ ∖ 0` of the zero section in the annihilator line
of a contact structure `ξ` is connected exactly when `ξ` is not the kernel of any global contact
form. -/
theorem connectedSpace_annihilatorPunctured_iff [ConnectedSpace M] [T2Space M]
    [SigmaCompactSpace M] :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    ConnectedSpace hξ.annihilatorPunctured ↔
      ¬ ∃ α : SmoothForm I M ℝ 1, α.IsContactForm ∧ α.kerDistribution = ξ :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  by
  rw [hξ.exists_isContactForm_kerDistribution_eq_iff_nonempty_orientation, not_nonempty_iff,
    ← connectedSpace_zeroSectionCompl_iff_isEmpty (finrank_fin_fun ℝ),
    ← coe_annihilatorPunctured]
  exact Iff.rfl

/-- **The symplectization of a coorientable contact structure is disconnected.** If `ξ = ker α`
for a contact form `α`, the symplectization `ξ⁰ ∖ 0` is not connected. -/
theorem not_connectedSpace_annihilatorPunctured {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm)
    (hαξ : α.kerDistribution = ξ) :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    ¬ ConnectedSpace hξ.annihilatorPunctured :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  fun h ↦ by
  -- `ξ⁰ ∖ 0` maps onto `M`, through the covectors `α_x`, so `M` is connected too.
  have : ConnectedSpace M := Surjective.connectedSpace
    (f := fun z : hξ.annihilatorPunctured ↦ z.val.proj)
    (fun x ↦ ⟨⟨α.symplectizationToAnnihilator hαξ (0, x), hξ.mem_annihilatorPunctured.2
      (SmoothForm.symplectizationToAnnihilator_snd_ne_zero hαξ hα.apply_ne_zero _)⟩,
      SmoothForm.proj_symplectizationToAnnihilator hαξ _⟩)
    ((FiberBundle.continuous_proj _ _).comp continuous_subtypeVal)
  obtain ⟨o⟩ := hξ.nonempty_vectorBundleOrientation_of_isContactForm hα hαξ
  have h' : ConnectedSpace (zeroSectionCompl (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x) := by
    rw [← coe_annihilatorPunctured]
    exact h
  exact ((connectedSpace_zeroSectionCompl_iff_isEmpty (finrank_fin_fun ℝ)).1 h').false o

/-- For a nowhere vanishing one-form `α` with kernel a contact structure `ξ`, the covectors
`eᵗ α_x` of `ξ⁰ ∖ 0`, the image of `κ_α`, form a preconnected set when `M` is preconnected. -/
private theorem isPreconnected_preimage_range [PreconnectedSpace M] {α : SmoothForm I M ℝ 1}
    (hα₀ : ∀ x, α.val x ≠ 0) (hαξ : α.kerDistribution = ξ) :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    IsPreconnected (Subtype.val ⁻¹' range (α.symplectizationToAnnihilator hαξ) :
      Set hξ.annihilatorPunctured) :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  by
  -- The set is the range of `κ_α`, as a map into `ξ⁰ ∖ 0`.
  let κ (p : ℝ × M) : hξ.annihilatorPunctured :=
    ⟨α.symplectizationToAnnihilator hαξ p,
      hξ.mem_annihilatorPunctured.2 (SmoothForm.symplectizationToAnnihilator_snd_ne_zero hαξ hα₀ p)⟩
  have hκ : Continuous κ :=
    (SmoothForm.contMDiff_symplectizationToAnnihilator hαξ hξ.isContMDiffDistribution
      hξ.finrank_sub_one_add_one).continuous.subtype_mk _
  convert isPreconnected_range hκ using 1
  ext z
  exact ⟨fun ⟨p, hp⟩ ↦ ⟨p, Subtype.ext hp⟩, fun ⟨p, hp⟩ ↦ ⟨p, congrArg Subtype.val hp⟩⟩

/-- **A component of the symplectization of a cooriented contact structure.** Let `ξ = ker α` for a
contact form `α` on a connected manifold. The connected component in `ξ⁰ ∖ 0` of a covector
`eᵗ α_x` is the set of all covectors `eˢ α_y`, the image of the trivialization
`κ_α : (s, y) ↦ eˢ α_y`. -/
theorem connectedComponent_eq_preimage_range [ConnectedSpace M] {α : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) (hαξ : α.kerDistribution = ξ)
    {z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x}
    (hz : z ∈ range (α.symplectizationToAnnihilator hαξ)) :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    ∀ hz' : z ∈ hξ.annihilatorPunctured, connectedComponent (⟨z, hz'⟩ : hξ.annihilatorPunctured) =
      Subtype.val ⁻¹' range (α.symplectizationToAnnihilator hαξ) :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  fun hz' ↦ by
  have hα₀ := hα.apply_ne_zero
  have hαξ' : (-α).kerDistribution = ξ := SmoothForm.kerDistribution_neg.trans hαξ
  have hpos := hξ.isPreconnected_preimage_range hα₀ hαξ
  refine Subset.antisymm (fun w hw ↦ ?_) (hpos.subset_connectedComponent hz)
  -- Every covector of `ξ⁰ ∖ 0` is `eˢ α_y` or `-eˢ α_y`.
  refine ((SmoothForm.mem_range_symplectizationToAnnihilator_or_neg_iff hαξ hα₀).2
    (hξ.mem_annihilatorPunctured.1 w.property)).resolve_right fun hw' ↦ ?_
  -- If the component met the negative half, it would contain both halves, so `ξ⁰ ∖ 0` would be
  -- connected.
  refine hξ.not_connectedSpace_annihilatorPunctured hα hαξ <|
    connectedSpace_iff_connectedComponent.2 ⟨⟨z, hz'⟩, eq_univ_of_forall fun u ↦ ?_⟩
  rcases (SmoothForm.mem_range_symplectizationToAnnihilator_or_neg_iff hαξ hα₀).2
    (hξ.mem_annihilatorPunctured.1 u.property) with hu | hu
  · exact hpos.subset_connectedComponent hz hu
  · rw [connectedComponent_eq hw]
    exact (hξ.isPreconnected_preimage_range (fun x ↦ neg_ne_zero.2 (hα₀ x)) hαξ')
      |>.subset_connectedComponent hw' hu

/-- **The symplectization of a cooriented contact structure has two components.** Let `ξ = ker α`
for a contact form `α` on a connected manifold. Every connected component of `ξ⁰ ∖ 0` is either
the image of `κ_α`, the covectors `eᵗ α_x`, or the image of `κ_(-α)`, the covectors `-eᵗ α_x`.
These two sets are disjoint and nonempty
(`TauCeti.SmoothForm.disjoint_range_symplectizationToAnnihilator_neg`), so `ξ⁰ ∖ 0` has exactly
two components. -/
theorem connectedComponent_eq_preimage_range_or_neg [ConnectedSpace M] {α : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) (hαξ : α.kerDistribution = ξ) :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    ∀ z : hξ.annihilatorPunctured,
      connectedComponent z = Subtype.val ⁻¹' range (α.symplectizationToAnnihilator hαξ) ∨
        connectedComponent z = Subtype.val ⁻¹' range ((-α).symplectizationToAnnihilator
          (SmoothForm.kerDistribution_neg.trans hαξ)) :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  fun z ↦
    ((SmoothForm.mem_range_symplectizationToAnnihilator_or_neg_iff hαξ hα.apply_ne_zero).2
      (hξ.mem_annihilatorPunctured.1 z.property)).imp
      (fun h ↦ hξ.connectedComponent_eq_preimage_range hα hαξ h z.property)
      (fun h ↦ hξ.connectedComponent_eq_preimage_range (SmoothForm.isContactForm_neg_iff.2 hα)
        (SmoothForm.kerDistribution_neg.trans hαξ) h z.property)

end IsContactDistribution

end TauCeti
