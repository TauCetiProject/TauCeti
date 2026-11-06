/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Levi
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Pow
import TauCeti.LinearAlgebra.BilinearForm.Contact.Volume

/-!
# The volume criterion for contact forms

Let `α` be a smooth real one-form on a manifold `M` of dimension `2 * n + 1`. Then `α` is a contact
form exactly when the top-degree form `α ∧ (dα)ⁿ` vanishes nowhere
(`TauCeti.SmoothForm.isContactForm_iff_forall_wedge_wedgePow_apply_ne_zero`). This is the classical
definition of a contact form. Here contactness is defined intrinsically, by `α_x ≠ 0` and
nondegeneracy of `dα_x` on `ker α_x`, and the volume condition is a theorem. The statement is
pointwise: at each point `x`, the covector `α_x` is contact for `dα_x` exactly when
`(α ∧ (dα)ⁿ)_x ≠ 0` (`TauCeti.SmoothForm.isContact_iff_wedge_wedgePow_apply_ne_zero`). Neither a
chosen orientation nor a normalization of the volume form is involved.

Combined with the description of contactness through the Levi form of `ξ = ker α`
(`TauCeti.SmoothForm.isContactForm_iff_forall_bijective_distributionLeviForm`), the volume
condition is equivalent to `α` vanishing nowhere with `ξ` having nondegenerate Levi form
`ξ_x ≃ Hom(ξ_x, T_x M ⧸ ξ_x)` at every point
(`TauCeti.SmoothForm.forall_wedge_wedgePow_apply_ne_zero_iff_bijective_distributionLeviForm`).

The pointwise statement is the linear criterion
`ContinuousLinearMap.isContact_iff_pairedWedge_wedgePow_ne_zero`, applied to the value of `α` and
of `dα` at each point.

## Main results

* `TauCeti.SmoothForm.isContact_iff_wedge_wedgePow_apply_ne_zero`: the pointwise volume criterion.
* `TauCeti.SmoothForm.isContactForm_iff_forall_wedge_wedgePow_apply_ne_zero`: a one-form on a
  manifold of dimension `2 * n + 1` is contact exactly when `α ∧ (dα)ⁿ` vanishes nowhere.
* `TauCeti.SmoothForm.IsContactForm.wedge_wedgePow_apply_ne_zero`: the volume form `α ∧ (dα)ⁿ` of
  a contact form vanishes nowhere.
* `TauCeti.SmoothForm.forall_wedge_wedgePow_apply_ne_zero_iff_bijective_distributionLeviForm`: the
  volume condition is equivalent to nondegeneracy of the Levi form of `ker α`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Sections 1.1 and 2.1.
-/

public section

open Module Function
open scoped Manifold

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] {α : SmoothForm I M ℝ 1} {n : ℕ}

/-- **The pointwise volume criterion for contact forms.** On a manifold of dimension `2 * n + 1`,
the covector `α_x` is contact for `dα_x`, that is `α_x ≠ 0` and `dα_x` is nondegenerate on
`ker α_x`, exactly when `(α ∧ (dα)ⁿ)_x ≠ 0`. -/
theorem isContact_iff_wedge_wedgePow_apply_ne_zero (hn : finrank ℝ E = 2 * n + 1) (x : M) :
    Module.Dual.IsContact (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
        ((mextDerivₗ I 1 α).bilinFormAt x) ↔
      (wedge α ((mextDerivₗ I 1 α).wedgePow n)).1 x ≠ 0 := by
  have hα : α.1 x = ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ (0 : Fin 1)
      (degreeOneEquiv α x) := by
    ext v
    rw [ContinuousAlternatingMap.ofSubsingleton_apply_apply, degreeOneEquiv_apply_apply]
    exact congrArg (α.1 x) (funext fun i ↦ by rw [Subsingleton.elim i 0])
  have hB : (mextDerivₗ I 1 α).bilinFormAt x =
      ((mextDerivₗ I 1 α).1 x).toMultilinearMap.toBilinMap := by
    ext v w
    simp [SmoothBundleForm.eval₂_apply]
  rw [coe_wedge, RoughForm.wedge_def, RoughForm.wedgeWith_apply', wedgePow_apply, hα, hB]
  exact (degreeOneEquiv α x).isContact_iff_pairedWedge_wedgePow_ne_zero _ hn

/-- **The volume criterion for contact forms.** A smooth one-form `α` on a manifold of dimension
`2 * n + 1` is a contact form exactly when the top-degree form `α ∧ (dα)ⁿ` vanishes nowhere. -/
theorem isContactForm_iff_forall_wedge_wedgePow_apply_ne_zero (hn : finrank ℝ E = 2 * n + 1) :
    α.IsContactForm ↔ ∀ x, (wedge α ((mextDerivₗ I 1 α).wedgePow n)).1 x ≠ 0 := by
  rw [isContactForm_def]
  exact forall_congr' (isContact_iff_wedge_wedgePow_apply_ne_zero hn)

/-- The volume form `α ∧ (dα)ⁿ` of a contact form on a manifold of dimension `2 * n + 1` vanishes
nowhere. -/
theorem IsContactForm.wedge_wedgePow_apply_ne_zero (hα : α.IsContactForm)
    (hn : finrank ℝ E = 2 * n + 1) (x : M) :
    (wedge α ((mextDerivₗ I 1 α).wedgePow n)).1 x ≠ 0 :=
  (isContact_iff_wedge_wedgePow_apply_ne_zero hn x).mp (isContactForm_def.mp hα x)

/-- **The volume condition is Levi nondegeneracy.** On a manifold of dimension `2 * n + 1`, the
form `α ∧ (dα)ⁿ` vanishes nowhere exactly when `α` vanishes nowhere and, at every point `x`, the
Levi form of `ξ = ker α` induces an isomorphism `ξ_x ≃ Hom(ξ_x, T_x M ⧸ ξ_x)`. -/
theorem forall_wedge_wedgePow_apply_ne_zero_iff_bijective_distributionLeviForm
    (hn : finrank ℝ E = 2 * n + 1) :
    (∀ x, (wedge α ((mextDerivₗ I 1 α).wedgePow n)).1 x ≠ 0) ↔
      ∀ x, α.1 x ≠ 0 ∧ Bijective (distributionLeviForm α.kerDistribution x) := by
  rw [← isContactForm_iff_forall_wedge_wedgePow_apply_ne_zero hn,
    isContactForm_iff_forall_bijective_distributionLeviForm]

end SmoothForm

end TauCeti
