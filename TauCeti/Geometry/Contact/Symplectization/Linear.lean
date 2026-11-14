/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Basic
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import TauCeti.Topology.Algebra.Module.BilinearForm
import TauCeti.Topology.Algebra.Module.Contact

/-!
# The continuous symplectization form of a covector and a two-form

For a covector `a` and a two-form `b` on a finite-dimensional normed space `V`, the symplectization
form `((s, v), (s', w)) ↦ s a(w) - s' a(v) + b(v, w)` on `𝕜 × V`
(`Module.Dual.symplectizationForm`) is a continuous bilinear map
(`ContinuousAlternatingMap.symplectizationFormCLM`). It depends smoothly on `a` and `b`
(`ContDiffOn.symplectizationFormCLM`), and a real one-form `α` is a contact form at `x` if and only
if the symplectization form of `α` and `dα` at `x` is invertible
(`TauCeti.isInvertible_symplectizationFormCLM_iff`,
`TauCeti.IsContactFormAt.isInvertible_symplectizationFormCLM`), by
`TauCeti.isContactFormAt_modelSpace_iff_isContact` and
`Module.Dual.isContact_iff_nondegenerate_symplectizationForm`. Since contactness of a continuous
covector/bilinear-form family is open (`TauCeti.isOpen_setOf_isContact`), a one-form of class `C¹`
at `x` that is a contact form at `x` remains a contact form on a neighbourhood of `x`
(`TauCeti.IsContactFormAt.eventually`).

This is the linear algebra of the contact Moser method: pairing a conformal factor and a vector
field with `𝕜 × V` turns the contact Moser equations into a Moser contraction equation for the
symplectization form.

## Main declarations

* `ContinuousAlternatingMap.symplectizationFormCLM`: the symplectization form as a continuous
  bilinear map, with `ContinuousAlternatingMap.symplectizationFormCLM_apply`.
* `ContDiffOn.symplectizationFormCLM`: smooth dependence on the covector and the two-form.
* `TauCeti.isInvertible_symplectizationFormCLM_iff`,
  `TauCeti.IsContactFormAt.isInvertible_symplectizationFormCLM`: invertibility characterization of
  contactness at a point.
* `TauCeti.IsContactFormAt.eventually`: openness of the pointwise contact condition for `C¹`
  one-forms on a finite-dimensional space.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 2.5.
-/

public section

open Filter
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

/-- On a finite-dimensional real normed space, the symplectization form of `α` and `dα` at `x` is
invertible if and only if `α` is a contact form at `x`. -/
theorem isInvertible_symplectizationFormCLM_iff
    {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} {x : V} :
    ((α x).symplectizationFormCLM (extDeriv α x)).IsInvertible ↔
      IsContactFormAt (I := 𝓘(ℝ, V)) α x := by
  rw [ContinuousLinearMap.isInvertible_iff_nondegenerate_toBilinForm,
    ContinuousAlternatingMap.symplectizationFormCLM,
    LinearMap.BilinForm.toBilinForm_toContinuousBilinearMap,
    isContactFormAt_modelSpace_iff_isContact,
    Module.Dual.isContact_iff_nondegenerate_symplectizationForm]

/-- At a point where a one-form is a contact form, its symplectization form is invertible, by
`TauCeti.isInvertible_symplectizationFormCLM_iff`. -/
theorem IsContactFormAt.isInvertible_symplectizationFormCLM
    {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} {x : V} (hc : IsContactFormAt (I := 𝓘(ℝ, V)) α x) :
    ((α x).symplectizationFormCLM (extDeriv α x)).IsInvertible :=
  isInvertible_symplectizationFormCLM_iff.2 hc

/-- **Openness of the contact condition.** On a finite-dimensional real normed space, a one-form
that is `C¹` at `x` and is a contact form at `x` remains a contact form on a neighbourhood of
`x`. -/
theorem IsContactFormAt.eventually {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} {x : V}
    (hc : IsContactFormAt (I := 𝓘(ℝ, V)) α x) (hα : ContDiffAt ℝ 1 α x) :
    ∀ᶠ y in 𝓝 x, IsContactFormAt (I := 𝓘(ℝ, V)) α y := by
  simp only [isContactFormAt_modelSpace_iff_isContact] at hc ⊢
  have hopen : IsOpen {p : (V [⋀^Fin 1]→L[ℝ] ℝ) × (V [⋀^Fin 2]→L[ℝ] ℝ) |
      Module.Dual.IsContact (ContinuousAlternatingMap.toDual p.1 : V →ₗ[ℝ] ℝ)
        (ContinuousAlternatingMap.flatL ℝ V ℝ p.2).toLinearMap₁₂} :=
    isOpen_setOf_isContact
      (fun v ↦ by
        simp only [ContinuousLinearMap.coe_coe, ContinuousAlternatingMap.toDual_apply]
        exact (ContinuousAlternatingMap.apply ℝ V ℝ (![v] : Fin 1 → V)).continuous.comp
          continuous_fst)
      (fun v w ↦ by
        simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
          ContinuousAlternatingMap.flatL_apply_apply]
        exact (ContinuousAlternatingMap.apply ℝ V ℝ (![v, w] : Fin 2 → V)).continuous.comp
          continuous_snd)
  exact (hα.continuousAt.prodMk
    (contDiffAt_extDeriv hα (r := 0) (by simp)).continuousAt).eventually (hopen.mem_nhds hc)

end TauCeti
