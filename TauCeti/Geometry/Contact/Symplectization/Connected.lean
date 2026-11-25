/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Coorientation
public import TauCeti.Geometry.Contact.Symplectization.Annihilator
public import TauCeti.Geometry.Contact.Symplectization.Trivialization
public import TauCeti.Topology.VectorBundle.Orientation.Basic
import TauCeti.Topology.VectorBundle.Orientation.Cover.ZeroSectionCompl
import TauCeti.Topology.VectorBundle.Orientation.PositiveSection

/-!
# Connectedness of the symplectization of a contact structure

Let `ξ` be a contact structure on a manifold `M`, with no defining one-form or coorientation
chosen. Its symplectization is the complement `ξ⁰ ∖ 0` of the zero section in the annihilator line
`ξ⁰ ⊂ T*M` (`TauCeti.IsContactDistribution.annihilatorPunctured`), carrying the symplectic form
`dθ` of the tautological one-form.

When `ξ` is the kernel of a global contact form `α`, the covectors `eᵗ α_x` and `-eᵗ α_x` form
two disjoint halves of `ξ⁰ ∖ 0` which together exhaust it
(`TauCeti.SmoothForm.mem_range_symplectizationToAnnihilator_or_neg_iff`), so the symplectization
is disconnected. This file proves that on a connected manifold there is no other way for it to be
disconnected: **the symplectization of a contact structure on a connected manifold is connected
exactly when the contact structure is not coorientable**, that is, when it is the kernel of no
global contact form
(`TauCeti.IsContactDistribution.connectedSpace_annihilatorPunctured_iff`). For example, the
contact structure on the space of contact elements `ℝ² × ℝP¹` of the plane is not coorientable,
and its symplectization `T*ℝ² ∖ 0` is connected.

This is the case of the line bundle `ξ⁰` of the general fact that the nonzero vectors of a real
line bundle over a connected base form a connected space exactly when the bundle is not orientable
(`TauCeti.VectorBundleOrientation.nonempty_iff_not_connectedSpace_zeroSectionCompl`). An
orientation of `ξ⁰` gives a continuous nowhere-zero section of `ξ⁰`
(`TauCeti.VectorBundleOrientation.exists_continuous_section_ne_zero`), hence a global contact
form with kernel `ξ` (`TauCeti.IsContactDistribution.exists_isContactForm_pos_smul`), and
conversely a contact form orients `ξ⁰`.

## Main results

* `TauCeti.IsContactDistribution.nonempty_vectorBundleOrientation_iff`: the annihilator line of a
  contact structure on a Hausdorff σ-compact manifold is orientable exactly when the contact
  structure is the kernel of a global contact form.
* `TauCeti.IsContactDistribution.connectedSpace_annihilatorPunctured_iff`: on a connected
  Hausdorff σ-compact manifold, the symplectization of a contact structure is connected exactly
  when the contact structure is not the kernel of a global contact form.
* `TauCeti.IsContactDistribution.connectedComponent_eq_preimage_range_symplectizationToAnnihilator`:
  when `ξ = ker α` on a connected manifold, the two halves `±eᵗ α_x` are the connected components
  of the symplectization.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Springer, 1989,
  Appendix 4 (the symplectification of a contact manifold).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1 and Appendix B (coorientable contact structures and the symplectization).
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
`TauCeti.IsContMDiffDistribution.annihilatorContMDiffVectorBundle` at smoothness `∞`. -/
local instance : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)

variable [Nonempty M] [T2Space M] [SigmaCompactSpace M]

/-- **A contact structure is coorientable exactly when its annihilator line is orientable.** On a
Hausdorff σ-compact manifold, the annihilator line bundle `ξ⁰` of a contact structure `ξ`
(`TauCeti.IsContMDiffDistribution.annihilatorFiberBundle`) has an orientation exactly when `ξ` is
the kernel of a global contact form. -/
theorem nonempty_vectorBundleOrientation_iff (hξ : IsContactDistribution I ∞ ξ) :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    letI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    Nonempty (VectorBundleOrientation (Fin 1 → ℝ) (fun x ↦ annihilatorSpace I ξ x) (Fin 1)) ↔
      ∃ α : SmoothForm I M ℝ 1, α.IsContactForm ∧ α.kerDistribution = ξ := by
  let := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  let := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  rw [hξ.exists_isContactForm_kerDistribution_eq_iff_exists_continuous]
  constructor
  · -- An orientation of `ξ⁰` has a continuous nowhere-zero section.
    rintro ⟨o⟩
    obtain ⟨s, hs, hs₀⟩ := o.exists_continuous_section_ne_zero (by simp)
    exact ⟨fun x ↦ (s x : TangentSpace I x →L[ℝ] ℝ),
      (continuous_totalSpaceMk_annihilatorSpace_iff (P := Fin 1 → ℝ)).1 hs,
      fun x ↦ ⟨fun h ↦ hs₀ x (Subtype.ext h), (s x).property⟩⟩
  · -- A continuous nowhere-zero section of `ξ⁰` orients it.
    rintro ⟨σ, hσ, hσD⟩
    exact ⟨VectorBundleOrientation.ofContinuousNonvanishingSection
      (fun x ↦ (VectorBundle.finrank_eq ℝ (Fin 1 → ℝ) (fun x ↦ annihilatorSpace I ξ x) x).trans
        (finrank_fin_fun ℝ))
      (s := fun x ↦ ⟨σ x, (hσD x).2⟩)
      ((continuous_totalSpaceMk_annihilatorSpace_iff (P := Fin 1 → ℝ)).2 hσ)
      fun x h ↦ (hσD x).1 (congrArg Subtype.val h)⟩

/-- **The symplectization of a contact structure is connected exactly when the structure is not
coorientable.** On a connected Hausdorff σ-compact manifold, the complement `ξ⁰ ∖ 0` of the zero
section in the annihilator line of a contact structure `ξ` is connected exactly when `ξ` is the
kernel of no global contact form. When `ξ = ker α`, the covectors `eᵗ α_x` and `-eᵗ α_x` are the
two connected components of `ξ⁰ ∖ 0`
(`TauCeti.IsContactDistribution.connectedComponent_eq_preimage_range_symplectizationToAnnihilator`).
-/
theorem connectedSpace_annihilatorPunctured_iff [PreconnectedSpace M]
    (hξ : IsContactDistribution I ∞ ξ) :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    ConnectedSpace hξ.annihilatorPunctured ↔
      ¬ ∃ α : SmoothForm I M ℝ 1, α.IsContactForm ∧ α.kerDistribution = ξ := by
  let := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  let := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  have hP : (hξ.annihilatorPunctured : Set (TotalSpace (Fin 1 → ℝ) _)) =
      zeroSectionCompl (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x :=
    Set.ext fun _ ↦ hξ.mem_annihilatorPunctured.trans mem_zeroSectionCompl.symm
  have : ConnectedSpace M := { toNonempty := inferInstance }
  rw [← hξ.nonempty_vectorBundleOrientation_iff,
    VectorBundleOrientation.nonempty_iff_not_connectedSpace_zeroSectionCompl (finrank_fin_fun ℝ),
    not_not, ← isConnected_iff_connectedSpace, ← hP]
  exact isConnected_iff_connectedSpace.symm

omit [T2Space M] [SigmaCompactSpace M] in
/-- **The two components of the symplectization of a cooriented contact structure.** Let `α` be a
one-form whose kernel is the contact structure `ξ`, on a connected boundaryless manifold. The
covectors `eᵗ α_x`, the image of the trivialization `κ_α`, form a connected component of
`ξ⁰ ∖ 0`. Applied to `-α`, the covectors `-eᵗ α_x` form the other one. -/
theorem connectedComponent_eq_preimage_range_symplectizationToAnnihilator [PreconnectedSpace M]
    [BoundarylessManifold I M] (hξ : IsContactDistribution I ∞ ξ) {α : SmoothForm I M ℝ 1}
    (hαξ : α.kerDistribution = ξ) (p : ℝ × M) :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    connectedComponent (⟨α.symplectizationToAnnihilator hαξ p, hξ.mem_annihilatorPunctured.2
        (SmoothForm.symplectizationToAnnihilator_snd_ne_zero hαξ
          (fun x ↦ hξ.apply_ne_zero_of_kerDistribution_eq (congrFun hαξ x)) p)⟩ :
          hξ.annihilatorPunctured) =
      Subtype.val ⁻¹' range (α.symplectizationToAnnihilator hαξ) := by
  let := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  let := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  let := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  have hαξ' : (-α).kerDistribution = ξ := SmoothForm.kerDistribution_neg.trans hαξ
  have hα₀ (x : M) : α.val x ≠ 0 := hξ.apply_ne_zero_of_kerDistribution_eq (congrFun hαξ x)
  set A : Set hξ.annihilatorPunctured :=
    Subtype.val ⁻¹' range (α.symplectizationToAnnihilator hαξ)
  -- In `ξ⁰ ∖ 0`, the complement of the image of `κ_α` is the image of `κ_(-α)`.
  have hcompl : Aᶜ = Subtype.val ⁻¹' range ((-α).symplectizationToAnnihilator hαξ') := by
    ext z
    have h := (SmoothForm.mem_range_symplectizationToAnnihilator_or_neg_iff hαξ hα₀).2
      (hξ.mem_annihilatorPunctured.1 z.property)
    have hd := SmoothForm.disjoint_range_symplectizationToAnnihilator_neg hαξ hα₀
    exact ⟨h.resolve_left, fun h' h'' ↦ hd.ne_of_mem h'' h' rfl⟩
  -- Both images are open, since the trivializations are local diffeomorphisms.
  have hA : IsClopen A :=
    ⟨isOpen_compl_iff.1 (hcompl ▸
        (SmoothForm.isLocalDiffeomorph_symplectizationToAnnihilator hαξ' hξ).isOpen_range.preimage
          continuous_subtypeVal),
      (SmoothForm.isLocalDiffeomorph_symplectizationToAnnihilator hαξ hξ).isOpen_range.preimage
        continuous_subtypeVal⟩
  -- The image of `κ_α` is connected, as the image of the connected space `ℝ × M`.
  have hrange : A = range fun q : ℝ × M ↦ (⟨α.symplectizationToAnnihilator hαξ q,
      hξ.mem_annihilatorPunctured.2
        (SmoothForm.symplectizationToAnnihilator_snd_ne_zero hαξ hα₀ q)⟩ :
          hξ.annihilatorPunctured) := by
    ext z
    exact ⟨fun ⟨q, hq⟩ ↦ ⟨q, Subtype.ext hq⟩, fun ⟨q, hq⟩ ↦ ⟨q, congrArg Subtype.val hq⟩⟩
  have hconn : IsPreconnected A := by
    rw [hrange]
    exact isPreconnected_range ((SmoothForm.contMDiff_symplectizationToAnnihilator hαξ
      hξ.isContMDiffDistribution hξ.finrank_sub_one_add_one).continuous.subtype_mk _)
  exact (hA.connectedComponent_subset ⟨p, rfl⟩).antisymm
    (hconn.subset_connectedComponent ⟨p, rfl⟩)

end IsContactDistribution

end TauCeti
