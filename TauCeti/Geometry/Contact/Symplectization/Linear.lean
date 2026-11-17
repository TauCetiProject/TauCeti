/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Normed.Module.Alternating.Curry
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# The continuous symplectization form of a covector and a two-form

For a covector `a` and a two-form `b` on a finite-dimensional normed space `V`, the symplectization
form `((s, v), (s', w)) ↦ s a(w) - s' a(v) + b(v, w)` on `𝕜 × V`
(`Module.Dual.symplectizationForm`) is a continuous bilinear map
(`ContinuousAlternatingMap.symplectizationFormCLM`). It depends smoothly on `a` and `b`
(`ContDiffOn.symplectizationFormCLM`), and a real one-form `α` is a contact form at `x` precisely
when the symplectization form of `α x` and `dα x` is invertible
(`TauCeti.isContactFormAt_modelSpace_iff_isInvertible_symplectizationFormCLM`), by
`TauCeti.isContactFormAt_modelSpace_iff_isContact` and
`Module.Dual.isContact_iff_nondegenerate_symplectizationForm`. Since invertibility is open in
finite dimensions, a `C¹` one-form that is contact at `x₀` remains contact on a neighbourhood of
`x₀` (`TauCeti.IsContactFormAt.eventually_modelSpace`).

This is the linear algebra of the contact Moser method: pairing a conformal factor and a vector
field with `𝕜 × V` turns the contact Moser equations into a Moser contraction equation for the
symplectization form.

## Main declarations

* `ContinuousAlternatingMap.symplectizationFormCLM`: the symplectization form as a continuous
  bilinear map, with `ContinuousAlternatingMap.symplectizationFormCLM_apply`.
* `ContDiffOn.symplectizationFormCLM`: smooth dependence on the covector and the two-form.
* `TauCeti.isContactFormAt_modelSpace_iff_isInvertible_symplectizationFormCLM`,
  `TauCeti.IsContactFormAt.isInvertible_symplectizationFormCLM`: invertibility at a contact point.
* `TauCeti.IsContactFormAt.eventually_modelSpace`: openness of the contact condition for `C¹`
  one-forms on finite-dimensional normed spaces.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 2.5.
-/

public section

open scoped Manifold Topology

namespace ContinuousAlternatingMap

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup V]
  [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- The symplectization form `((s, v), (s', w)) ↦ s a(w) - s' a(v) + b(v, w)` on `𝕜 × V` of a
covector `a` and a two-form `b` on `V` (`Module.Dual.symplectizationForm`), as a continuous
bilinear map. -/
noncomputable def symplectizationFormCLM (a : V [⋀^Fin 1]→L[𝕜] 𝕜)
    (b : V [⋀^Fin 2]→L[𝕜] 𝕜) : 𝕜 × V →L[𝕜] 𝕜 × V →L[𝕜] 𝕜 :=
  (Module.Dual.symplectizationForm (toDual a : V →ₗ[𝕜] 𝕜)
    (flatL 𝕜 V 𝕜 b).toLinearMap₁₂).toContinuousBilinearMap

/-- The symplectization form evaluates by `((s, v), (s', w)) ↦ s a(w) - s' a(v) + b(v, w)`. -/
@[simp]
theorem symplectizationFormCLM_apply (a : V [⋀^Fin 1]→L[𝕜] 𝕜) (b : V [⋀^Fin 2]→L[𝕜] 𝕜)
    (p q : 𝕜 × V) :
    a.symplectizationFormCLM b p q = p.1 * a ![q.2] - q.1 * a ![p.2] + b ![p.2, q.2] := by
  simp [symplectizationFormCLM, ← flatL_apply_apply]

end ContinuousAlternatingMap

/-- The symplectization form depends smoothly on the covector and the two-form. -/
theorem ContDiffOn.symplectizationFormCLM {𝕜 V X : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] {a : X → V [⋀^Fin 1]→L[𝕜] 𝕜}
    {b : X → V [⋀^Fin 2]→L[𝕜] 𝕜} {s : Set X} {n : WithTop ℕ∞} (ha : ContDiffOn 𝕜 n a s)
    (hb : ContDiffOn 𝕜 n b s) :
    ContDiffOn 𝕜 n (fun x ↦ (a x).symplectizationFormCLM (b x)) s := by
  refine contDiffOn_clm_apply.2 fun p ↦ contDiffOn_clm_apply.2 fun q ↦ ?_
  simp only [ContinuousAlternatingMap.symplectizationFormCLM_apply]
  have hev {k : ℕ} {f : X → V [⋀^Fin k]→L[𝕜] 𝕜} (hf : ContDiffOn 𝕜 n f s) (m : Fin k → V) :
      ContDiffOn 𝕜 n (fun x ↦ f x m) s :=
    (ContinuousAlternatingMap.apply 𝕜 V 𝕜 m).contDiff.comp_contDiffOn hf
  exact ((contDiffOn_const.mul (hev ha _)).sub (contDiffOn_const.mul (hev ha _))).add (hev hb _)

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- On a finite-dimensional real normed space, a one-form `α` is a contact form at `x` precisely
when the symplectization form of `α x` and `dα x` is invertible. -/
theorem isContactFormAt_modelSpace_iff_isInvertible_symplectizationFormCLM
    {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} {x : V} :
    IsContactFormAt (I := 𝓘(ℝ, V)) α x ↔
      ((α x).symplectizationFormCLM (extDeriv α x)).IsInvertible := by
  rw [isContactFormAt_modelSpace_iff_isContact,
    Module.Dual.isContact_iff_nondegenerate_symplectizationForm,
    ContinuousAlternatingMap.symplectizationFormCLM,
    ContinuousLinearMap.isInvertible_iff_nondegenerate_toBilinForm,
    LinearMap.BilinForm.toBilinForm_toContinuousBilinearMap]

/-- At a point where a one-form is a contact form, its symplectization form is invertible, by
`TauCeti.isContactFormAt_modelSpace_iff_isContact` and
`Module.Dual.isContact_iff_nondegenerate_symplectizationForm`. -/
theorem IsContactFormAt.isInvertible_symplectizationFormCLM
    {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} {x : V} (hc : IsContactFormAt (I := 𝓘(ℝ, V)) α x) :
    ((α x).symplectizationFormCLM (extDeriv α x)).IsInvertible :=
  isContactFormAt_modelSpace_iff_isInvertible_symplectizationFormCLM.1 hc

/-- **Openness of the contact condition.** If a one-form `α` on a finite-dimensional real normed
space is `C¹` at `x₀` and is a contact form at `x₀`, then it is a contact form on a neighbourhood
of `x₀`. -/
theorem IsContactFormAt.eventually_modelSpace {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} {x₀ : V}
    (hc : IsContactFormAt (I := 𝓘(ℝ, V)) α x₀) (hα : ContDiffAt ℝ 1 α x₀) :
    ∀ᶠ x in 𝓝 x₀, IsContactFormAt (I := 𝓘(ℝ, V)) α x := by
  have hcont : ContinuousAt (fun x ↦ (α x).symplectizationFormCLM (extDeriv α x)) x₀ := by
    refine continuousAt_clm_apply.2 fun p ↦ continuousAt_clm_apply.2 fun q ↦ ?_
    simp only [ContinuousAlternatingMap.symplectizationFormCLM_apply]
    have hev (m : Fin 1 → V) : ContinuousAt (fun x ↦ α x m) x₀ :=
      (ContinuousAlternatingMap.apply ℝ V ℝ m).continuous.continuousAt.comp hα.continuousAt
    exact ((continuousAt_const.mul (hev _)).sub (continuousAt_const.mul (hev _))).add
      (continuousAt_extDeriv_apply hα _)
  have hnd : (((α x₀).symplectizationFormCLM (extDeriv α x₀)).toBilinForm).Nondegenerate :=
    ContinuousLinearMap.isInvertible_iff_nondegenerate_toBilinForm.1
      hc.isInvertible_symplectizationFormCLM
  filter_upwards [hcont.eventually_toBilinForm_nondegenerate hnd] with x hx
  exact isContactFormAt_modelSpace_iff_isInvertible_symplectizationFormCLM.2
    (ContinuousLinearMap.isInvertible_iff_nondegenerate_toBilinForm.2 hx)

end TauCeti
