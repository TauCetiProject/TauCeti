/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import TauCeti.Geometry.Contact.Reeb
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import TauCeti.Geometry.Manifold.IntegralCurve.Basic

/-!
# Reeb orbits under a locally constant change of contact form

The Reeb vector field depends on the contact form, not only on the contact structure `ξ = ker α`.
Multiplying a contact form by a locally constant function `c`, such as a nonzero constant on each
connected component, divides its Reeb field by `c`
(`TauCeti.SmoothForm.IsContactForm.reebVectorField_eq_inv_smul_of_isLocallyConstant`). So the
integral curves of `R_(c α)` are those of `R_α` run at the speed `1 / c`, backwards where `c < 0`
(`TauCeti.SmoothForm.IsContactForm.isMIntegralCurve_comp_mul_reebVectorField_of_eq_smul`): such a
rescaling keeps `ξ`, and keeps the closed Reeb orbits as subsets of the manifold. Conversely, an
integral curve `γ` of `R_(c α)` along which `c` is nonzero, run at the speed `c(γ 0)`, is an
integral curve of `R_α`, even when `c` vanishes elsewhere
(`TauCeti.SmoothForm.IsContactForm.isMIntegralCurve_comp_mul_of_eq_smul_of_isLocallyConstant`).

On a compact manifold, a rescaling of this kind turns any form with the kernel of a
nowhere-vanishing form `α` into `f α` with `f` above any given bound
(`TauCeti.SmoothForm.exists_isLocallyConstant_smul_eq_smul`). This is how Barraud, Damian,
Humilière and Oancea, in their proof of Corollary E, reduce the existence of closed Reeb orbits for
every contact form defining the contact structure of the boundary of a Liouville domain to the
contact forms `f α` with `f > 1`, which a graph in the symplectization realizes as the restriction
of the ambient Liouville form.

## Main results

* `TauCeti.SmoothForm.IsContactForm.isMIntegralCurve_comp_mul_reebVectorField_of_eq_smul`: for
  `β = c α` with `c` locally constant, `t ↦ γ(t / c(γ 0))` is an integral curve of `R_β` when `γ`
  is one of `R_α`.
* `TauCeti.SmoothForm.IsContactForm.isMIntegralCurve_comp_mul_of_eq_smul_of_isLocallyConstant`:
  conversely, `t ↦ γ(t c(γ 0))` is an integral curve of `R_α` when `γ` is one of `R_β` and
  `c(γ 0) ≠ 0`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, proof of Corollary E.
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {c : M → ℝ}

section IntegralCurve

variable [IsManifold I 2 M] {α β : SmoothForm I M ℝ 1}

/-- **Reeb orbits under a locally constant rescaling.** Let `α` be a contact form and `β = c α` for
a locally constant function `c`. If `γ` is an integral curve of the Reeb field `R_α`, then `γ` run
at the speed `1 / c(γ 0)`, `t ↦ γ(t / c(γ 0))`, is an integral curve of `R_β`; it runs backwards
when `c(γ 0) < 0`. In particular, when `c` vanishes nowhere, every closed Reeb orbit of `α` is, as
a subset, a closed Reeb orbit of `β`. -/
theorem IsContactForm.isMIntegralCurve_comp_mul_reebVectorField_of_eq_smul
    [FiniteDimensional ℝ E] (hα : α.IsContactForm) (hc : IsLocallyConstant c)
    (hβ : ∀ y, β.val y = c y • α.val y) {γ : ℝ → M} (hγ : IsMIntegralCurve γ α.reebVectorField) :
    IsMIntegralCurve (γ ∘ (· * (c (γ 0))⁻¹)) β.reebVectorField := by
  -- The locally constant `c` is constant along the connected curve `γ`.
  have hcγ (t : ℝ) : c (γ t) = c (γ 0) :=
    (hc.comp_continuous hγ.continuous).apply_eq_of_preconnectedSpace t 0
  refine (isMIntegralCurve_congr_vectorField fun t ↦ ?_).1 (hγ.comp_mul (c (γ 0))⁻¹)
  rw [Pi.smul_apply, Function.comp_apply,
    hα.reebVectorField_eq_inv_smul_of_isLocallyConstant hc hβ, hcγ (t * (c (γ 0))⁻¹)]

/-- **Reeb orbits of a locally constant rescaling.** Let `α` be a contact form and `β = c α` for a
locally constant function `c`. Along an integral curve `γ` of `R_β`, `c` takes the constant value
`c₀ = c (γ 0)`, and `R_β = R_α / c₀` there, so if `c₀ ≠ 0`, then `t ↦ γ (t c₀)` is an integral
curve of `R_α`. Unlike `isMIntegralCurve_comp_mul_reebVectorField_of_eq_smul` applied to `β`, this
does not need `β` to be a contact form, so `c` may vanish away from `γ`. -/
theorem IsContactForm.isMIntegralCurve_comp_mul_of_eq_smul_of_isLocallyConstant
    [FiniteDimensional ℝ E] (hα : α.IsContactForm) (hc : IsLocallyConstant c)
    (hβ : ∀ y, β.val y = c y • α.val y) {γ : ℝ → M} (hγ : IsMIntegralCurve γ β.reebVectorField)
    (hc₀ : c (γ 0) ≠ 0) :
    IsMIntegralCurve (γ ∘ (· * c (γ 0))) α.reebVectorField := by
  -- `c` is constant along the connected curve.
  have hcγ (t : ℝ) : c (γ t) = c (γ 0) :=
    (hc.comp_continuous hγ.continuous).apply_eq_of_preconnectedSpace t 0
  refine (isMIntegralCurve_congr_vectorField fun t ↦ ?_).1 (hγ.comp_mul (c (γ 0)))
  rw [Pi.smul_apply, Function.comp_apply,
    hα.reebVectorField_eq_inv_smul_of_isLocallyConstant hc hβ, hcγ (t * c (γ 0)),
    smul_inv_smul₀ hc₀]

end IntegralCurve

end TauCeti.SmoothForm
