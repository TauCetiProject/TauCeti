/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Contactization
public import TauCeti.Geometry.Contact.Isotropic
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Graph
import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Legendrian lifts and one-jets

Let `θ` be a one-form on a manifold `W`, and consider the contactization `W × ℝ` with the one-form
`α = dz - θ` (`TauCeti.SmoothForm.contactization`). A map `y ↦ (f y, h y)` into `W × ℝ` pulls `α`
back to `dh - f^*θ` (`TauCeti.SmoothForm.mpullback_prodMk_contactization`). Hence it is isotropic
for the distribution `ker α` exactly when `f^*θ = dh`
(`TauCeti.SmoothForm.isIsotropicMap_prodMk_contactization_iff`): the second component is a
primitive of the pulled-back one-form. In particular, if `f` is an exact Lagrangian immersion with
primitive `h`, then its **Legendrian lift** `y ↦ (f y, h y)` is a Legendrian immersion
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsExactLagrangianMap.isLegendrianImmersion_prodMk`).
None of these statements needs `ker α` to be a contact structure, which it is exactly when `-dθ`
is nondegenerate (`TauCeti.SmoothForm.isContactForm_contactization_iff`).

For `W = T*M` with its Liouville form `λ`, the contactization is the one-jet space
`J¹M = T*M × ℝ` with the standard contact form `dz - λ`. Since `λ` is tautological, the map
`x ↦ ((x, α_x), h x)` defined by a one-form `α` and a function `h` pulls `dz - λ` back to
`dh - α`. This gives the **graph criterion**: the map is isotropic exactly when `α = dh`
(`TauCeti.CotangentBundle.isIsotropicMap_section_prodMk_iff`), and then it is a Legendrian
immersion (`TauCeti.CotangentBundle.isLegendrianImmersion_section_prodMk_iff`). For `α = dh`
this map is the **one-jet** `j¹h : x ↦ (x, dh_x, h x)` of a smooth function `h`, so one-jets of
smooth functions are Legendrian.

## Main results

* `TauCeti.SmoothForm.isIsotropicMap_prodMk_contactization_iff`: the lift criterion.
* `TauCeti.SmoothTwoForm.IsNondegenerate.IsExactLagrangianMap.isLegendrianImmersion_prodMk`:
  Legendrian lifts of exact Lagrangian immersions.
* `TauCeti.CotangentBundle.isIsotropicMap_section_prodMk_iff` and
  `TauCeti.CotangentBundle.isLegendrianImmersion_section_prodMk_iff`: the graph criterion in
  `J¹M`; one-jets of smooth functions are Legendrian.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008): the one-jet space `J¹M` and Legendrian one-jets of functions.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (contactization of exact symplectic manifolds).
-/

public section

noncomputable section

open Bundle Module Manifold
open scoped Manifold ContDiff

namespace TauCeti

variable {E H W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace W] [ChartedSpace H W] [IsManifold I ∞ W]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {f : N → W} {h : N → ℝ}

namespace SmoothForm

/-- **The Legendrian lift criterion.** A map `y ↦ (f y, h y)` into the contactization `W × ℝ`, with
`f` and `h` differentiable, is isotropic for the distribution `ker (dz - θ)` exactly when
`f^*θ = dh`. -/
theorem isIsotropicMap_prodMk_contactization_iff (θ : SmoothForm I W ℝ 1)
    (hf : MDifferentiable J I f) (hh : MDifferentiable J 𝓘(ℝ) h) :
    IsIsotropicMap J θ.contactization.kerDistribution (fun y ↦ (f y, h y)) ↔
      TauCeti.mpullback J I f θ.1 = mextDeriv (RoughForm.ofFunction J h) := by
  rw [isIsotropicMap_kerDistribution_iff, mpullback_prodMk_contactization θ hf hh, sub_eq_zero,
    eq_comm]

/-- **Legendrian lifts.** On a finite-dimensional boundaryless manifold `W`, let `f : N → W` be a
smooth map with injective differentials from a boundaryless manifold of half the dimension, and
let `h` be a smooth primitive of `f^*θ`. Then `y ↦ (f y, h y)` is a Legendrian immersion into the
contactization `W × ℝ`, for the distribution `ker (dz - θ)`. -/
theorem isLegendrianImmersion_prodMk_contactization [FiniteDimensional ℝ E] [I.Boundaryless]
    [J.Boundaryless] [IsManifold J ∞ N] (θ : SmoothForm I W ℝ 1) (hf : ContMDiff J I ∞ f)
    (hinj : ∀ y, Function.Injective (mfderiv J I f y)) (hh : ContMDiff J 𝓘(ℝ) ∞ h)
    (hdim : 2 * finrank ℝ E' = finrank ℝ E)
    (hfh : TauCeti.mpullback J I f θ.1 = mextDeriv (RoughForm.ofFunction J h)) :
    IsLegendrianImmersion J θ.contactization.kerDistribution (fun y ↦ (f y, h y)) where
  isImmersion := hf.isImmersion_prodMk hinj hh (by simp)
  isIsotropicMap := (isIsotropicMap_prodMk_contactization_iff θ (hf.mdifferentiable (by simp))
    (hh.mdifferentiable (by simp))).2 hfh
  two_mul_finrank_add_one := by rw [finrank_prod, finrank_self, hdim]

end SmoothForm

/-- **Legendrian lifts of exact Lagrangian immersions.** On a finite-dimensional boundaryless
manifold `W`, if a Lagrangian immersion `f` from a boundaryless manifold is exact for the one-form
`θ`, with primitive `h`, then `y ↦ (f y, h y)` is a Legendrian immersion into the contactization
`W × ℝ`, for the distribution `ker (dz - θ)`. -/
theorem SmoothTwoForm.IsNondegenerate.IsExactLagrangianMap.isLegendrianImmersion_prodMk
    [FiniteDimensional ℝ E] [I.Boundaryless] [J.Boundaryless] [IsManifold J ∞ N]
    {σ : SmoothTwoForm I W} {hσ : σ.IsNondegenerate} {θ : SmoothForm I W ℝ 1}
    (hL : hσ.IsExactLagrangianMap J θ f h) (hf : hσ.IsLagrangianImmersion J f) :
    IsLegendrianImmersion J θ.contactization.kerDistribution (fun y ↦ (f y, h y)) :=
  SmoothForm.isLegendrianImmersion_prodMk_contactization θ hf.isImmersion.contMDiff
    (hf.isImmersion.mfderiv_injective (by simp)) hL.contMDiff_primitive hf.two_mul_finrank
    hL.mpullback_eq

/-! ### One-jets -/

namespace CotangentBundle

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {h : M → ℝ}

/-- **The graph criterion in `J¹M`.** For a smooth one-form `α` and a differentiable function `h`
on `M`, the map `x ↦ ((x, α_x), h x)` into the one-jet space `J¹M = T*M × ℝ` is isotropic for the
contact distribution `ker (dz - λ)` exactly when `α = dh`. -/
theorem isIsotropicMap_section_prodMk_iff (α : SmoothForm I M ℝ 1)
    (hh : MDifferentiable I 𝓘(ℝ) h) :
    IsIsotropicMap I (liouvilleForm I M).contactization.kerDistribution
        (fun x ↦ (TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x), h x)) ↔
      α.1 = mextDeriv (RoughForm.ofFunction I h) := by
  have hs := (SmoothForm.degreeOneEquiv α).contMDiff
  rw [SmoothForm.isIsotropicMap_prodMk_contactization_iff _ (hs.mdifferentiable (by simp)) hh,
    ← SmoothForm.coe_mpullback _ hs, mpullback_liouvilleForm]

/-- **One-jets are Legendrian.** On a finite-dimensional boundaryless manifold `M`, for a smooth
one-form `α` and a smooth function `h`, the map `x ↦ ((x, α_x), h x)` is a Legendrian immersion
into the one-jet space `J¹M = T*M × ℝ`, for the contact distribution `ker (dz - λ)`, exactly when
`α = dh`. For `α = dh` this map is the one-jet `j¹h : x ↦ (x, dh_x, h x)`. -/
theorem isLegendrianImmersion_section_prodMk_iff [FiniteDimensional ℝ E] [I.Boundaryless]
    (α : SmoothForm I M ℝ 1) (hh : ContMDiff I 𝓘(ℝ) ∞ h) :
    IsLegendrianImmersion I (liouvilleForm I M).contactization.kerDistribution
        (fun x ↦ (TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x), h x)) ↔
      α.1 = mextDeriv (RoughForm.ofFunction I h) := by
  refine ⟨fun hL ↦ (isIsotropicMap_section_prodMk_iff α (hh.mdifferentiable (by simp))).1
    hL.isIsotropicMap, fun hα ↦ ?_⟩
  have hs := (SmoothForm.degreeOneEquiv α).contMDiff
  -- The projection `T*M → M` is a left inverse of the section, so its differentials are injective.
  refine SmoothForm.isLegendrianImmersion_prodMk_contactization _ hs
    (fun x ↦ Bundle.mfderiv_injective_of_proj_comp_eq_id (hs.mdifferentiableAt (by simp)) rfl)
    hh ?_ ?_
  · rw [finrank_prod, ContinuousLinearMap.dual_finrank_eq, two_mul]
  · rw [← SmoothForm.coe_mpullback _ hs, mpullback_liouvilleForm, hα]

end CotangentBundle

end TauCeti
