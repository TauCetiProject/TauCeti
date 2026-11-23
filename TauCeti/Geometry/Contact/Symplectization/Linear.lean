/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import TauCeti.Analysis.Normed.Module.Alternating.Curry
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# The continuous symplectization form of a covector and a two-form

For a covector `a` and a two-form `b` on a finite-dimensional normed space `V`, the symplectization
form `((s, v), (s', w)) ↦ s a(w) - s' a(v) + b(v, w)` on `𝕜 × V`
(`Module.Dual.symplectizationForm`) is a continuous bilinear map
(`ContinuousAlternatingMap.symplectizationFormCLM`). It depends smoothly on `a` and `b`
(`ContDiffOn.symplectizationFormCLM`), and at a point where a real one-form `α` is a contact form,
the symplectization form of `α` and `dα` is invertible
(`TauCeti.IsContactFormAt.isInvertible_symplectizationFormCLM`), by
`TauCeti.isContactFormAt_modelSpace_iff_isContact` and
`Module.Dual.isContact_iff_nondegenerate_symplectizationForm`.

This is the linear algebra of the contact Moser method: pairing a conformal factor and a vector
field with `𝕜 × V` turns the contact Moser equations into a Moser contraction equation for the
symplectization form.

## Main declarations

* `ContinuousAlternatingMap.symplectizationFormCLM`: the symplectization form as a continuous
  bilinear map, with `ContinuousAlternatingMap.symplectizationFormCLM_apply`.
* `ContDiffOn.symplectizationFormCLM`: smooth dependence on the covector and the two-form.
* `TauCeti.IsContactFormAt.isInvertible_symplectizationFormCLM`: invertibility at a contact point.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 2.5.
-/

public section

open scoped Manifold

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

/-- At a point where a one-form is a contact form, its symplectization form is invertible, by
`TauCeti.isContactFormAt_modelSpace_iff_isContact` and
`Module.Dual.isContact_iff_nondegenerate_symplectizationForm`. -/
theorem IsContactFormAt.isInvertible_symplectizationFormCLM
    {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} {x : V} (hc : IsContactFormAt (I := 𝓘(ℝ, V)) α x) :
    ((α x).symplectizationFormCLM (extDeriv α x)).IsInvertible :=
  isInvertible_toContinuousBilinearMap_iff_separatingLeft.2
    (Module.Dual.isContact_iff_nondegenerate_symplectizationForm.1
      (isContactFormAt_modelSpace_iff_isContact.1 hc)).1

end TauCeti
