/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Contactization
public import TauCeti.Geometry.Contact.Isotropic
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Graph
import TauCeti.Geometry.Manifold.Immersion.Basic
import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Legendrian lifts and one-jets

Let `θ` be a one-form on a manifold `W`, and give `W × ℝ` the contactization form `dz - θ`
(`TauCeti.SmoothForm.contactization θ`). A smooth map `y ↦ (φ y, h y)` into `W × ℝ` pulls
`dz - θ` back to `dh - φ^* θ`, so it is isotropic for the kernel of `dz - θ` exactly when

`φ^* θ = dh`

(`TauCeti.SmoothForm.isDistributionIsotropicMap_contactization_iff`). When `-dθ` is
nondegenerate, this says that `φ` is an exact Lagrangian map with primitive `h`: an exact
Lagrangian immersion `φ` lifts to the Legendrian immersion `(φ, h)`, its **contact lift**
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsExactLagrangianMap.isLegendrianImmersion_contactization`),
and conversely, for `σ = -dθ`, the projection `φ` of an isotropic map `(φ, h)` with injective
differentials from a manifold of half the dimension of `W` is exact Lagrangian with primitive `h`
(`SmoothTwoForm.IsNondegenerate.isExactLagrangianMap_of_isDistributionIsotropicMap_contactization`).

For `W = T*Q` with its Liouville form `λ`, the contactization is the space of one-jets
`J¹Q = T*Q × ℝ` with its standard contact form `dz - λ`. A section `q ↦ (β_q, g q)` of
`J¹Q → Q`, given by a smooth one-form `β` and a smooth function `g`, is isotropic exactly when
`β = dg` (`TauCeti.CotangentBundle.isDistributionIsotropicMap_contactization_section_iff`): this
is the graph criterion for Legendrian submanifolds of `J¹Q`. In particular the **one-jet**
`j¹g : q ↦ (dg_q, g q)` of a smooth function on a finite-dimensional boundaryless manifold is a
Legendrian embedding (`TauCeti.CotangentBundle.isLegendrianEmbedding_oneJet`).

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Chapter 2 (the space of one-jets and its Legendrian graphs).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Appendix 4
  (Legendrian lifts of exact Lagrangian submanifolds).
-/

public section

noncomputable section

open Set Function Module Bundle Manifold
open scoped Manifold ContDiff

namespace TauCeti

variable {E H W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace W] [ChartedSpace H W] [IsManifold I ∞ W]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {θ : SmoothForm I W ℝ 1} {φ : N → W} {h : N → ℝ}

/-- A smooth map `y ↦ (φ y, h y)` pulls the contactization form `dz - θ` back to `dh - φ^* θ`. -/
theorem SmoothForm.mpullback_contactization (hφ : ContMDiff J I ∞ φ)
    (hh : ContMDiff J 𝓘(ℝ) ∞ h) :
    (mpullback (fun y ↦ (φ y, h y)) (hφ.prodMk hh) θ.contactization).1 =
      mextDeriv (RoughForm.ofFunction J h) - TauCeti.mpullback J I φ θ.1 := by
  rw [contactization_def, map_sub, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← mpullback_comp, ← mpullback_comp, Submodule.coe_sub, coe_mpullback, coe_mpullback]
  -- The components `Prod.snd ∘ (φ, h)` and `Prod.fst ∘ (φ, h)` simplify to `h` and `φ`.
  simp only [Function.comp_def]
  rw [mpullback_realLineCoordForm]

/-- **Isotropic maps into a contactization.** A smooth map `y ↦ (φ y, h y)` into `W × ℝ` is
isotropic for the kernel of the contactization form `dz - θ` exactly when `φ^* θ = dh`. -/
theorem SmoothForm.isDistributionIsotropicMap_contactization_iff (hφ : ContMDiff J I ∞ φ)
    (hh : ContMDiff J 𝓘(ℝ) ∞ h) :
    IsDistributionIsotropicMap J θ.contactization.kerDistribution (fun y ↦ (φ y, h y)) ↔
      TauCeti.mpullback J I φ θ.1 = mextDeriv (RoughForm.ofFunction J h) := by
  rw [isDistributionIsotropicMap_kerDistribution_iff_mpullback_eq_zero (hφ.prodMk hh),
    Subtype.ext_iff, mpullback_contactization hφ hh, ZeroMemClass.coe_zero, sub_eq_zero, eq_comm]

namespace SmoothTwoForm.IsNondegenerate

variable {σ : SmoothTwoForm I W} {hσ : σ.IsNondegenerate}

/-- **Contact lifts of exact Lagrangian maps.** If `φ` is an exact Lagrangian map with primitive
`h`, then its lift `y ↦ (φ y, h y)` is isotropic for the kernel of the contactization form
`dz - θ`. -/
theorem IsExactLagrangianMap.isDistributionIsotropicMap_contactization
    (hL : hσ.IsExactLagrangianMap J θ φ h) (hφ : ContMDiff J I ∞ φ) :
    IsDistributionIsotropicMap J θ.contactization.kerDistribution (fun y ↦ (φ y, h y)) :=
  (SmoothForm.isDistributionIsotropicMap_contactization_iff hφ hL.contMDiff_primitive).2
    hL.mpullback_eq

/-- **Projections of isotropic lifts are exact Lagrangian.** For a primitive `θ` of `σ = -dθ`, if
the lift `y ↦ (φ y, h y)` of a smooth map is isotropic for the kernel of `dz - θ`, and `φ` has
injective differentials from a manifold of half the dimension, then `φ` is an exact Lagrangian map
with primitive `h`. -/
theorem isExactLagrangianMap_of_isDistributionIsotropicMap_contactization [FiniteDimensional ℝ E]
    (hθ : σ = -mextDerivₗ I 1 θ) (hφ : ContMDiff J I ∞ φ) (hh : ContMDiff J 𝓘(ℝ) ∞ h)
    (hiso : IsDistributionIsotropicMap J θ.contactization.kerDistribution (fun y ↦ (φ y, h y)))
    (hinj : ∀ y, Injective (mfderiv J I φ y)) (hdim : 2 * finrank ℝ E' = finrank ℝ E) :
    hσ.IsExactLagrangianMap J θ φ h := by
  have hpull := (SmoothForm.isDistributionIsotropicMap_contactization_iff hφ hh).1 hiso
  exact ⟨(hσ.isIsotropicMap_of_mpullback_eq_mextDeriv hθ hφ (hh.of_le (by simp))
    hpull).isLagrangianMap_of_finrank hinj hdim, hh, hpull⟩

variable [I.Boundaryless] [J.Boundaryless] [FiniteDimensional ℝ E]

/-- **Contact lifts of exact Lagrangian immersions are Legendrian.** If `φ` is an immersion from a
nonempty manifold which is an exact Lagrangian map with primitive `h`, then its lift
`y ↦ (φ y, h y)` is a Legendrian immersion for the contactization form `dz - θ`. -/
theorem IsExactLagrangianMap.isLegendrianImmersion_contactization [Nonempty N]
    (hL : hσ.IsExactLagrangianMap J θ φ h) (hφ : IsImmersion J I ∞ φ) :
    IsLegendrianImmersion J θ.contactization.kerDistribution (fun y ↦ (φ y, h y)) := by
  have hφ' := hφ.contMDiff
  have hh := hL.contMDiff_primitive
  refine ⟨isImmersion_iff_forall_isImmersionAt.2 fun y ↦ ?_,
    (SmoothForm.isDistributionIsotropicMap_contactization_iff hφ' hh).2 hL.mpullback_eq, ?_⟩
  · refine ((hφ'.prodMk hh).contMDiffOn.isImmersionAt_iff_injective_mfderiv isOpen_univ
      (mem_univ y) (by simp)).2 ?_
    -- The first component of the differential of the lift is the injective differential of `φ`.
    rw [mfderiv_prodMk (hφ'.mdifferentiableAt (by simp)) (hh.mdifferentiableAt (by simp))]
    exact fun v w hvw ↦ hφ.mfderiv_injective (by simp) y (congrArg Prod.fst hvw)
  · rw [finrank_prod, Module.finrank_self,
      hL.isLagrangianMap.two_mul_finrank (hφ.mfderiv_injective (by simp) (Classical.arbitrary N))]

end SmoothTwoForm.IsNondegenerate

/-! ### One-jets -/

namespace CotangentBundle

variable {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

/-- **The graph criterion in the space of one-jets.** For a smooth one-form `β` and a smooth
function `g` on `Q`, the section `q ↦ (β_q, g q)` of `J¹Q = T*Q × ℝ` is isotropic for the kernel
of the standard contact form `dz - λ` exactly when `β = dg`. -/
theorem isDistributionIsotropicMap_contactization_section_iff (β : SmoothForm I Q ℝ 1)
    {g : Q → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g) :
    IsDistributionIsotropicMap I (liouvilleForm I Q).contactization.kerDistribution
        (fun q ↦ (TotalSpace.mk' (E →L[ℝ] ℝ) q (SmoothForm.degreeOneEquiv β q), g q)) ↔
      β.1 = mextDeriv (RoughForm.ofFunction I g) := by
  rw [SmoothForm.isDistributionIsotropicMap_contactization_iff
      (SmoothForm.degreeOneEquiv β).contMDiff hg,
    ← SmoothForm.coe_mpullback _ (SmoothForm.degreeOneEquiv β).contMDiff, mpullback_liouvilleForm]

variable [I.Boundaryless] [FiniteDimensional ℝ E]

/-- **One-jets are Legendrian.** On a finite-dimensional boundaryless manifold `Q`, let `β = dg`
be the differential of a smooth function `g`. Then the one-jet `j¹g : q ↦ (dg_q, g q)` is a
Legendrian embedding into `J¹Q = T*Q × ℝ` with its standard contact form `dz - λ`. -/
theorem isLegendrianEmbedding_oneJet (β : SmoothForm I Q ℝ 1) {g : Q → ℝ}
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) (hβ : β.1 = mextDeriv (RoughForm.ofFunction I g)) :
    IsLegendrianEmbedding I (liouvilleForm I Q).contactization.kerDistribution
      (fun q ↦ (TotalSpace.mk' (E →L[ℝ] ℝ) q (SmoothForm.degreeOneEquiv β q), g q)) := by
  have hs := (SmoothForm.degreeOneEquiv β).contMDiff
  have hj := hs.prodMk hg
  -- The projection `J¹Q → Q` is a smooth left inverse of the one-jet.
  have hp : ContMDiff ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) I ∞
      (fun p : CotangentBundle I Q × ℝ ↦ p.1.proj) :=
    (Bundle.contMDiff_proj (fun x : Q ↦ TangentSpace I x →L[ℝ] ℝ)).comp contMDiff_fst
  have himm : IsImmersion I ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) ∞
      (fun q ↦ (TotalSpace.mk' (E →L[ℝ] ℝ) q (SmoothForm.degreeOneEquiv β q), g q)) :=
    isImmersion_iff_forall_isImmersionAt.2 fun q ↦
      hj.contMDiffOn.isImmersionAt_of_comp_eventuallyEq_id isOpen_univ (mem_univ q) (by simp)
        (hp.mdifferentiableAt (by simp)) (Filter.Eventually.of_forall fun _ ↦ rfl)
  refine ⟨⟨himm, (isDistributionIsotropicMap_contactization_section_iff β hg).2 hβ, ?_⟩,
    Topology.IsEmbedding.of_leftInverse (fun _ ↦ rfl) hp.continuous hj.continuous⟩
  rw [finrank_prod, finrank_prod, ContinuousLinearMap.dual_finrank_eq, Module.finrank_self,
    two_mul]

end CotangentBundle

end TauCeti
