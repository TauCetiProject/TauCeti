/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import TauCeti.Geometry.Contact.Reeb
public import TauCeti.Geometry.Contact.Transition
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Topology.LocallyConstant.Sign

/-!
# Reeb orbits under a locally constant change of contact form

The Reeb vector field depends on the contact form, not only on the contact structure `ξ = ker α`.
Multiplying a contact form by a locally constant function `c`, such as a nonzero constant on each
connected component, divides its Reeb field by `c`
(`TauCeti.SmoothForm.IsContactForm.reebVectorField_eq_inv_smul_of_isLocallyConstant`). So the
integral curves of `R_(c α)` are those of `R_α` run at the speed `1 / c`, backwards where `c < 0`
(`TauCeti.SmoothForm.IsContactForm.isMIntegralCurve_comp_mul_reebVectorField_of_eq_smul`): such a
rescaling keeps `ξ`, and keeps the closed Reeb orbits as subsets of the manifold.

On a compact manifold, a rescaling of this kind turns any form with the kernel of a
nowhere-vanishing form `α` into `f α` with `f` above any given bound. If `ker β = ker α`, then
`β = g α` for a smooth nowhere-vanishing function `g`, and multiplying `β` by a constant of the sign
of `g` on each of the sets where that sign is constant turns `g` into a function `f > a`
(`TauCeti.SmoothForm.exists_isLocallyConstant_smul_eq_smul`). This is how Barraud, Damian,
Humilière and Oancea, in their proof of Corollary E, reduce the existence of closed Reeb orbits for
every contact form defining the contact structure of the boundary of a Liouville domain to the
contact forms `f α` with `f > 1`, which a graph in the symplectization realizes as the restriction
of the ambient Liouville form.

## Main results

* `TauCeti.SmoothForm.IsContactForm.isMIntegralCurve_comp_mul_reebVectorField_of_eq_smul`: for
  `β = c α` with `c` locally constant, `t ↦ γ(t / c(γ 0))` is an integral curve of `R_β` when `γ`
  is one of `R_α`.
* `TauCeti.SmoothForm.exists_isLocallyConstant_smul_eq_smul`: on a compact manifold, a form with
  the kernel of a nowhere-vanishing form `α`, multiplied by a suitable locally constant
  nowhere-vanishing function, is `f α` for a smooth `f` above any given bound.

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

end IntegralCurve

section Compact

variable [IsManifold I ∞ M] [CompactSpace M] {α β : SmoothForm I M ℝ 1}

/-- **Rescaling a form with the kernel of `α` above a bound.** Let `α` be a nowhere-vanishing
one-form on a compact manifold and `β` a smooth one-form with the same kernel, `ker β = ker α`, such
as another contact form defining the same contact structure. For every `a`, there is a locally
constant nowhere-vanishing function `c`, a nonzero constant on each connected component, such that
`c β = f α` for a smooth function `f > a`. -/
theorem exists_isLocallyConstant_smul_eq_smul (hα : ∀ x, α.val x ≠ 0)
    (hβ : β.kerDistribution = α.kerDistribution) (a : ℝ) :
    ∃ c f : M → ℝ, IsLocallyConstant c ∧ (∀ x, c x ≠ 0) ∧ ContMDiff I 𝓘(ℝ) ∞ f ∧
      (∀ x, a < f x) ∧ ∀ x, c x • β.val x = f x • α.val x := by
  obtain ⟨g, ⟨hg, hg₀, hgβ⟩, -⟩ := (kerDistribution_eq_iff_existsUnique_fun_smul hα).1 hβ
  obtain ⟨c, hc, hc₀, hcg⟩ := hg.continuous.exists_isLocallyConstant_lt_mul hg₀ a
  exact ⟨c, c * g, hc, hc₀, hc.contMDiff.mul hg, hcg, fun x ↦ by
    rw [hgβ, smul_smul, Pi.mul_apply]⟩

end Compact

end TauCeti.SmoothForm
