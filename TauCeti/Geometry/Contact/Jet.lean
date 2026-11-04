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
# Legendrian graphs in the space of one-jets

For the cotangent bundle `T*Q` with its Liouville form `λ`, the contactization `T*Q × ℝ` is the
space of one-jets `J¹Q` with its standard contact form `dz - λ`. A section `q ↦ (β_q, g q)` of
`J¹Q → Q`, given by a smooth one-form `β` and a smooth function `g`, is isotropic exactly when
`β = dg` (`TauCeti.CotangentBundle.isDistributionIsotropicMap_contactization_section_iff`): this
is the graph criterion for Legendrian submanifolds of `J¹Q`, obtained from the criterion
`φ^* θ = dh` for isotropic maps `y ↦ (φ y, h y)` into a contactization
(`TauCeti.SmoothForm.isDistributionIsotropicMap_contactization_iff`). In particular the
**one-jet** `j¹g : q ↦ (dg_q, g q)` of a smooth function on a finite-dimensional boundaryless
manifold is a Legendrian embedding (`TauCeti.CotangentBundle.isLegendrianEmbedding_oneJet`).

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Chapter 2 (the space of one-jets and its Legendrian graphs).
-/

public section

noncomputable section

open Set Function Module Bundle Manifold
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}

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
