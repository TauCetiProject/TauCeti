/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Coorientation
public import TauCeti.Geometry.Contact.Symplectization.Trivialization
public import TauCeti.Topology.VectorBundle.Orientation.ZeroSectionCompl
import TauCeti.Topology.VectorBundle.Orientation.PositiveSection

/-!
# The connected components of the symplectization of a contact structure

Let `ξ` be a contact structure on a connected manifold `M`, with no defining one-form or
coorientation chosen. Its symplectization is the complement `ξ⁰ ∖ 0` of the zero section in the
annihilator line `ξ⁰ ⊂ T*M` (`TauCeti.IsContactDistribution.annihilatorPunctured`), a symplectic
manifold for the exterior derivative of its tautological one-form. This file determines its
connected components.

* On a nonempty, preconnected, Hausdorff, σ-compact manifold, `ξ⁰ ∖ 0` is connected exactly when
  `ξ` is not coorientable, that is, when no global contact form has kernel `ξ`
  (`TauCeti.IsContactDistribution.connectedSpace_annihilatorPunctured_iff`).
* If `ξ = ker α` for a contact form `α`, then `ξ⁰ ∖ 0` is disconnected, with no hypothesis on `M`
  (`TauCeti.IsContactDistribution.not_connectedSpace_annihilatorPunctured`): the section `x ↦ α_x`
  orients the annihilator line. On a connected manifold, `ξ⁰ ∖ 0` has exactly two connected
  components: the images of the trivializations `κ_α : (t, x) ↦ eᵗ α_x` and
  `κ_(-α)` (`TauCeti.SmoothForm.symplectizationToAnnihilator`), that is, the positive multiples of
  `α` and the negative ones
  (`TauCeti.IsContactDistribution.connectedComponentIn_annihilatorPunctured_eq_range`,
  `TauCeti.IsContactDistribution.connectedComponentIn_annihilatorPunctured_eq_or`). On a manifold
  without boundary each of them is a diffeomorphic copy of the cooriented symplectization `ℝ × M`
  (`TauCeti.SmoothForm.isLocalDiffeomorph_symplectizationToAnnihilator`), and the fibre negation
  `ℓ ↦ -ℓ` exchanges them
  (`TauCeti.SmoothForm.vectorBundleScalarDiffeomorph_symplectizationToAnnihilator_of_neg`).

The first statement applies to the annihilator line the criterion that a real line bundle over a
connected base is orientable exactly when the complement of its zero section is disconnected
(`TauCeti.nonempty_vectorBundleOrientation_iff_not_connectedSpace_zeroSectionCompl`), together with
the identification of orientations of `ξ⁰` with global contact forms
(`TauCeti.IsContactDistribution.nonempty_vectorBundleOrientation_annihilatorSpace_iff`): an
orientation has a positive continuous section
(`TauCeti.VectorBundleOrientation.exists_continuous_section_basis_orientation_eq`), which is the
coorientation of a contact form
(`TauCeti.IsContactDistribution.exists_isContactForm_kerDistribution_eq_iff_exists_continuous`).

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1 and Appendix B (the symplectization of a contact structure).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Springer, 1989,
  Appendix 4 (the symplectification of a contact manifold).
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
  [IsManifold I ∞ M] {ξ : Π x : M, Submodule ℝ (TangentSpace I x)} [Nonempty M]
  (hξ : IsContactDistribution I ∞ ξ)

/-- `C^(∞ + 1)` charts, needed by the annihilator bundle construction of
`TauCeti.IsContMDiffDistribution.annihilatorContMDiffVectorBundle` at smoothness `∞`. -/
local instance instIsManifoldSymplectizationComponentsSource :
    IsManifold I ((∞ : WithTop ℕ∞) + 1) M :=
  IsManifold.of_le (n := ∞) (by simp)

/-- **The annihilator line of a contact structure is orientable exactly when the structure is
coorientable.** On a Hausdorff σ-compact manifold, the annihilator line `ξ⁰` of a contact structure
`ξ` has an orientation exactly when `ξ` is the kernel of a global contact form. -/
theorem nonempty_vectorBundleOrientation_annihilatorSpace_iff [T2Space M] [SigmaCompactSpace M] :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    Nonempty (VectorBundleOrientation (Fin 1 → ℝ) (fun x ↦ annihilatorSpace I ξ x) (Fin 1)) ↔
      ∃ α : SmoothForm I M ℝ 1, α.IsContactForm ∧ α.kerDistribution = ξ :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  by
  have hF : finrank ℝ (Fin 1 → ℝ) = 1 := by simp
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  rw [hξ.exists_isContactForm_kerDistribution_eq_iff_exists_continuous]
  constructor
  · -- An orientation of `ξ⁰` has a positive, hence nowhere-zero, continuous section.
    rintro ⟨o⟩
    obtain ⟨s, hs, hpos⟩ :=
      o.exists_continuous_section_basis_orientation_eq ((Fintype.card_fin 1).trans hF.symm)
    refine ⟨fun x ↦ (s x : TangentSpace I x →L[ℝ] ℝ),
      continuous_totalSpaceMk_annihilatorSpace_iff.1 hs, fun x ↦ ⟨fun h ↦ ?_, (s x).property⟩⟩
    obtain ⟨β, hβ, -⟩ := hpos x
    exact β.ne_zero default (hβ.trans (Subtype.ext h))
  · -- A nowhere-zero continuous section of `ξ⁰` orients it.
    rintro ⟨σ, hσ, hσ₀⟩
    exact ⟨VectorBundleOrientation.ofContinuousNonvanishingSection
      (fun x ↦ (VectorBundle.finrank_eq ℝ (Fin 1 → ℝ) (fun x ↦ annihilatorSpace I ξ x) x).trans hF)
      (s := fun x ↦ ⟨σ x, (hσ₀ x).2⟩) (continuous_totalSpaceMk_annihilatorSpace_iff.2 hσ)
      fun x h ↦ (hσ₀ x).1 (congrArg Subtype.val h)⟩

/-- **The symplectization of a noncoorientable contact structure is connected.** On a nonempty
preconnected Hausdorff σ-compact manifold, the symplectization `ξ⁰ ∖ 0` of a contact structure `ξ`
is connected exactly when `ξ` is not the kernel of any global contact form. -/
theorem connectedSpace_annihilatorPunctured_iff [PreconnectedSpace M] [T2Space M]
    [SigmaCompactSpace M] :
    ConnectedSpace hξ.annihilatorPunctured ↔
      ¬ ∃ α : SmoothForm I M ℝ 1, α.IsContactForm ∧ α.kerDistribution = ξ := by
  have : ConnectedSpace M := { toNonempty := inferInstance }
  let := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  have := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  rw [← hξ.nonempty_vectorBundleOrientation_annihilatorSpace_iff,
    nonempty_vectorBundleOrientation_iff_not_connectedSpace_zeroSectionCompl (by simp), not_not,
    ← isConnected_iff_connectedSpace, ← hξ.coe_annihilatorPunctured]
  exact isConnected_iff_connectedSpace.symm

/-- **The symplectization of a coorientable contact structure is disconnected.** If `ξ = ker α`
for a contact form `α`, the symplectization `ξ⁰ ∖ 0` is not connected. No hypothesis on `M` is
needed. -/
theorem not_connectedSpace_annihilatorPunctured {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm)
    (hαξ : α.kerDistribution = ξ) :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    ¬ ConnectedSpace hξ.annihilatorPunctured :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  fun h ↦ by
  -- `ξ⁰ ∖ 0` maps onto `M`, through the covectors `α_x`, so `M` is connected too.
  have : ConnectedSpace M := Function.Surjective.connectedSpace
    (f := fun z : hξ.annihilatorPunctured ↦ z.val.proj)
    (fun x ↦ ⟨⟨α.symplectizationToAnnihilator hαξ (0, x), hξ.mem_annihilatorPunctured.2
      (SmoothForm.symplectizationToAnnihilator_snd_ne_zero hαξ hα.apply_ne_zero _)⟩,
      SmoothForm.proj_symplectizationToAnnihilator hαξ _⟩)
    ((FiberBundle.continuous_proj _ _).comp continuous_subtypeVal)
  obtain ⟨o⟩ := hξ.isContMDiffDistribution.nonempty_vectorBundleOrientation_of_smoothForm_ker_eq
    hξ.finrank_sub_one_add_one (hξ.isContactForm_and_kerDistribution_eq_iff.1 ⟨hα, hαξ⟩)
  exact (nonempty_vectorBundleOrientation_iff_not_connectedSpace_zeroSectionCompl (by simp)).1 ⟨o⟩
    (hξ.connectedSpace_annihilatorPunctured_iff_connectedSpace_zeroSectionCompl.1 h)

variable {α : SmoothForm I M ℝ 1} (hα : α.kerDistribution = ξ)

/-- **The components of the symplectization of a cooriented contact structure.** Let `α` be a
one-form with kernel the contact structure `ξ` on a preconnected manifold. The connected
component of `κ_α(t, x) = eᵗ α_x` in the symplectization `ξ⁰ ∖ 0` is the image of `κ_α`: the
covectors of `ξ⁰` that are positive multiples of `α`. -/
theorem connectedComponentIn_annihilatorPunctured_eq_range [PreconnectedSpace M]
    (p : ℝ × M) :
    connectedComponentIn (hξ.annihilatorPunctured : Set _) (α.symplectizationToAnnihilator hα p) =
      range (α.symplectizationToAnnihilator hα) := by
  let := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  have hαc : α.IsContactForm :=
    SmoothForm.isContactForm_iff_isContactDistribution_kerDistribution.2 (hα ▸ hξ)
  have hα₀ := hαc.apply_ne_zero
  -- The image of `κ_β` is a preconnected subset of `ξ⁰ ∖ 0`, so it lies in one component.
  have hκ {β : SmoothForm I M ℝ 1} (hβ₀ : ∀ x, β.val x ≠ 0) (hβ : β.kerDistribution = ξ)
      (q : ℝ × M) : range (β.symplectizationToAnnihilator hβ) ⊆ connectedComponentIn
        (hξ.annihilatorPunctured : Set _) (β.symplectizationToAnnihilator hβ q) :=
    (isPreconnected_range (SmoothForm.contMDiff_symplectizationToAnnihilator hβ
      hξ.isContMDiffDistribution hξ.finrank_sub_one_add_one).continuous).subset_connectedComponentIn
      (mem_range_self q) <| by
        rintro _ ⟨q, rfl⟩
        exact hξ.mem_annihilatorPunctured.2
          (SmoothForm.symplectizationToAnnihilator_snd_ne_zero hβ hβ₀ q)
  refine subset_antisymm (fun w hw ↦ ?_) (hκ hα₀ hα p)
  have hwS := connectedComponentIn_subset _ _ hw
  refine ((SmoothForm.mem_range_symplectizationToAnnihilator_or_neg_iff hα hα₀).2
    (hξ.mem_annihilatorPunctured.1 hwS)).resolve_right fun ⟨q, hq⟩ ↦ ?_
  -- If the component met the negative half, it would contain both halves, which cover `ξ⁰ ∖ 0`,
  -- so `ξ⁰ ∖ 0` would be connected.
  have hS : (hξ.annihilatorPunctured : Set _) ⊆ connectedComponentIn
      (hξ.annihilatorPunctured : Set _) (α.symplectizationToAnnihilator hα p) := fun u hu ↦
    ((SmoothForm.mem_range_symplectizationToAnnihilator_or_neg_iff hα hα₀).2
      (hξ.mem_annihilatorPunctured.1 hu)).elim (fun h ↦ hκ hα₀ hα p h) fun h ↦ by
        rw [connectedComponentIn_eq hw, ← hq]
        exact hκ (fun x ↦ neg_ne_zero.2 (hα₀ x)) (SmoothForm.kerDistribution_neg.trans hα) q h
  refine hξ.not_connectedSpace_annihilatorPunctured hαc hα <|
    isConnected_iff_connectedSpace.1 ⟨⟨w, hwS⟩, ?_⟩
  rw [subset_antisymm hS (connectedComponentIn_subset _ _)]
  exact isPreconnected_connectedComponentIn

/-- **A cooriented contact structure has a symplectization with two components.** If the contact
structure `ξ` on a preconnected manifold is the kernel of a one-form `α`, every connected
component of its symplectization `ξ⁰ ∖ 0` is the image of `κ_α` or the image of `κ_(-α)`. These
two images are disjoint (`TauCeti.SmoothForm.disjoint_range_symplectizationToAnnihilator_neg`). -/
theorem connectedComponentIn_annihilatorPunctured_eq_or [PreconnectedSpace M]
    {z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x} (hz : z ∈ hξ.annihilatorPunctured) :
    connectedComponentIn (hξ.annihilatorPunctured : Set _) z =
        range (α.symplectizationToAnnihilator hα) ∨
      connectedComponentIn (hξ.annihilatorPunctured : Set _) z =
        range ((-α).symplectizationToAnnihilator (SmoothForm.kerDistribution_neg.trans hα)) := by
  have hα₀ : ∀ x, α.val x ≠ 0 :=
    (SmoothForm.isContactForm_iff_isContactDistribution_kerDistribution.2 (hα ▸ hξ)).apply_ne_zero
  rcases (SmoothForm.mem_range_symplectizationToAnnihilator_or_neg_iff hα hα₀).2
    (hξ.mem_annihilatorPunctured.1 hz) with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · exact .inl (hξ.connectedComponentIn_annihilatorPunctured_eq_range hα p)
  · exact .inr (hξ.connectedComponentIn_annihilatorPunctured_eq_range _ p)

end IsContactDistribution

end TauCeti
