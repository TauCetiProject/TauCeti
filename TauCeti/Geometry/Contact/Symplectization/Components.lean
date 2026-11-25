/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Coorientation
public import TauCeti.Geometry.Contact.Symplectization.Trivialization
import TauCeti.Topology.VectorBundle.Orientation.ZeroSectionCompl

/-!
# The connected components of the symplectization

Let `ξ` be a contact structure on a connected Hausdorff σ-compact manifold `M`, and let `ξ⁰ ∖ 0`
be its symplectization: the nonzero covectors annihilating `ξ`
(`TauCeti.IsContactDistribution.annihilatorPunctured`), the complement of the zero section of the
dual `L*` of the contact line. No contact form or coorientation is chosen. This file determines
the connected components of `ξ⁰ ∖ 0`.

* If `ξ` is **not coorientable**, that is, if it is the kernel of no global contact form, the
  symplectization is connected; and conversely
  (`TauCeti.IsContactDistribution.isConnected_annihilatorPunctured_iff`).
* If `ξ = ker α` for a one-form `α`, for instance a contact form, the symplectization has
  exactly two connected components: the covectors `eᵗ α_x`, which form the
  image of the contact-form trivialization `κ_α : ℝ × M → ξ⁰`, and the covectors `-eᵗ α_x`, the
  image of `κ_(-α)`
  (`TauCeti.IsContactDistribution.connectedComponentIn_annihilatorPunctured_eq_range`). The
  covectors of `ξ⁰ ∖ 0` are exactly those of the two images
  (`TauCeti.SmoothForm.mem_range_symplectizationToAnnihilator_or_neg_iff`).

So the trivialized symplectization `ℝ × M` with the form `eᵗ α` is one component of the
symplectization of `ξ`, and the whole of `ξ⁰ ∖ 0` is connected exactly when no such
trivialization exists. For the space of contact elements `ℝ² × ℝP¹` of the plane, whose contact
structure is not coorientable, the symplectization is `T*ℝ² ∖ 0`, which is connected.

Both statements are the case of the contact line of the corresponding facts about the nonzero
vectors of a real line bundle over a connected base
(`TauCeti.connectedSpace_zeroSectionCompl_iff_not_exists_continuous_section_ne_zero`,
`TauCeti.connectedComponent_zeroSectionCompl_eq`), together with the identification of the
coorientable contact structures with those whose annihilator line has a section vanishing nowhere
(`TauCeti.IsContactDistribution.exists_isContactForm_kerDistribution_eq_iff_exists_continuous`).

## Main results

* `TauCeti.IsContactDistribution.isConnected_annihilatorPunctured_iff`: on a connected Hausdorff
  σ-compact manifold, the symplectization of a contact structure is connected exactly when the
  contact structure is not coorientable.
* `TauCeti.IsContactDistribution.connectedComponentIn_annihilatorPunctured_eq_range`: on a
  connected manifold, the image of the trivialization `κ_α` of a defining form `α` is a connected
  component of the symplectization.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Springer, 1989,
  Appendix 4 (the symplectification of a contact manifold).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1 (coorientable contact structures).
-/

public section

noncomputable section

open Bundle Module Set
open scoped Manifold ContDiff

namespace TauCeti

open CotangentBundle

namespace IsContactDistribution

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {ξ : Π x : M, Submodule ℝ (TangentSpace I x)}

/-- `C^(∞ + 1)` charts, needed by the annihilator bundle construction of
`TauCeti.IsContMDiffDistribution.annihilatorFiberBundle` at smoothness `∞`. -/
local instance : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)

/-- **The symplectization of a contact structure is connected exactly when the structure is not
coorientable.** On a connected Hausdorff σ-compact manifold, the nonzero covectors annihilating a
contact structure `ξ` form a connected set exactly when `ξ` is the kernel of no global contact
form. -/
theorem isConnected_annihilatorPunctured_iff [ConnectedSpace M] [T2Space M] [SigmaCompactSpace M]
    (hξ : IsContactDistribution I ∞ ξ) :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    IsConnected (hξ.annihilatorPunctured :
        Set (TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x)) ↔
      ¬ ∃ α : SmoothForm I M ℝ 1, α.IsContactForm ∧ α.kerDistribution = ξ :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  rw [coe_annihilatorPunctured, isConnected_iff_connectedSpace,
    connectedSpace_zeroSectionCompl_iff_not_exists_continuous_section_ne_zero
      (by simp : finrank ℝ (Fin 1 → ℝ) = 1),
    hξ.exists_isContactForm_kerDistribution_eq_iff_exists_continuous,
    exists_continuous_totalSpaceMk_annihilatorSpace_ne_zero_iff]

/-- **The components of the symplectization of a coorientable contact structure.** Let `α` be a
one-form whose kernel is the contact structure `ξ`, on a preconnected manifold.
The image of the trivialization `κ_α : (t, x) ↦ eᵗ α_x` is a connected component of the
symplectization `ξ⁰ ∖ 0`: it is the connected component of each of its points. Applied to `-α`,
the image of `κ_(-α)` is the other component. -/
theorem connectedComponentIn_annihilatorPunctured_eq_range [PreconnectedSpace M] [Nonempty M]
    (hξ : IsContactDistribution I ∞ ξ) {α : SmoothForm I M ℝ 1} (hα : α.kerDistribution = ξ)
    {z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x}
    (hz : z ∈ range (α.symplectizationToAnnihilator hα)) :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    connectedComponentIn (hξ.annihilatorPunctured :
        Set (TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x)) z =
      range (α.symplectizationToAnnihilator hα) :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  by
  have hF : finrank ℝ (Fin 1 → ℝ) = 1 := by simp
  have hα₀ (x : M) : α.val x ≠ 0 := hξ.val_ne_zero_of_kerDistribution_eq (congrFun hα x)
  have hE (x : M) : finrank ℝ (annihilatorSpace I ξ x) = 1 :=
    (VectorBundle.finrank_eq ℝ (Fin 1 → ℝ) (fun x ↦ annihilatorSpace I ξ x) x).trans hF
  -- `α` is a continuous section of the annihilator line vanishing nowhere; it orients the line.
  have hαξ (x : M) := SmoothForm.degreeOneEquiv_ne_zero_and_mem_annihilatorSpace (hα₀ x)
    ((SmoothForm.kerDistribution_eq_ker α x).symm.trans (congrFun hα x))
  let s (x : M) : annihilatorSpace I ξ x := ⟨SmoothForm.degreeOneEquiv α x, (hαξ x).2⟩
  have hs : Continuous fun x ↦ TotalSpace.mk' (Fin 1 → ℝ) x (s x) :=
    continuous_totalSpaceMk_annihilatorSpace_iff.2
      (SmoothForm.degreeOneEquiv α).contMDiff.continuous
  have hs₀ (x : M) : s x ≠ 0 := fun h ↦ (hαξ x).1 (congrArg Subtype.val h)
  set o := VectorBundleOrientation.ofContinuousNonvanishingSection hE hs hs₀
  -- A nonzero covector `w` has the orientation `o` exactly when it is a positive multiple of `α`.
  have key (w : zeroSectionCompl (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x) :
      (zeroSectionComplToOrientationCover _ _ hF w).orientation =
          o (zeroSectionComplToOrientationCover _ _ hF w).proj ↔
        (w : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x) ∈
          range (α.symplectizationToAnnihilator hα) := by
    obtain ⟨⟨x, w⟩, hw⟩ := w
    rw [SmoothForm.mem_range_symplectizationToAnnihilator_iff,
      zeroSectionComplToOrientationCover_apply,
      VectorBundleOrientation.ofContinuousNonvanishingSection_apply]
    refine (orientation_basisSingleton_eq_iff (hE x) (hs₀ x) (mem_zeroSectionCompl.1 hw)).trans ?_
    refine exists_congr fun c ↦ and_congr_right fun _ ↦ ?_
    rw [Subtype.ext_iff, ContinuousLinearMap.ext_iff]
    simp [s, SmoothForm.degreeOneEquiv_apply_apply_vec]
  obtain ⟨p, rfl⟩ := hz
  have hz : α.symplectizationToAnnihilator hα p ∈ zeroSectionCompl (Fin 1 → ℝ) _ :=
    mem_zeroSectionCompl.2 (SmoothForm.symplectizationToAnnihilator_snd_ne_zero hα hα₀ p)
  rw [coe_annihilatorPunctured, connectedComponentIn_eq_image hz,
    connectedComponent_zeroSectionCompl_eq hF o ((key _).2 (mem_range_self p))]
  refine (image_subset_iff.2 fun w hw ↦ mem_preimage.2 ((key w).1 hw)).antisymm ?_
  rintro _ ⟨q, rfl⟩
  exact ⟨⟨_, mem_zeroSectionCompl.2 (SmoothForm.symplectizationToAnnihilator_snd_ne_zero hα hα₀ q)⟩,
    (key _).2 (mem_range_self q), rfl⟩

end IsContactDistribution

end TauCeti
