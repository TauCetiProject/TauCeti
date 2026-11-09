/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Contactization
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Graph
import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse

/-!
# One-jets of functions

Let `θ` be a one-form on a manifold `W`, and give `W × ℝ` the contactization form `dz - θ`
(`TauCeti.SmoothForm.contactization`). For smooth maps `ι : L → W` and `h : L → ℝ`, the map
`x ↦ (ι x, h x)` is horizontal for the distribution `ker (dz - θ)`, a contact structure when
`-dθ` is nondegenerate, exactly when `ι^* θ = dh`
(`TauCeti.SmoothForm.isHorizontalMap_contactization_iff`, in
`TauCeti.Geometry.Contact.Contactization`).

For the cotangent bundle `W = T*Q` with its Liouville form `λ`, the contactization `dz - λ` is the
standard contact form of the space of one-jets `J¹Q = T*Q × ℝ`. A smooth one-form `α` and a smooth
function `g` on `Q` give the section `q ↦ (α_q, g q)` of `J¹Q → Q`. Since `λ` is tautological,
this section is horizontal for `ker (dz - λ)` exactly when `α = dg`
(`TauCeti.CotangentBundle.isHorizontalMap_contactization_liouvilleForm_iff`). The **one-jet**
`j¹g : q ↦ (dg_q, g q)` of a smooth function is therefore a Legendrian embedding of `Q`
(`TauCeti.CotangentBundle.isLegendrianEmbedding_contactization_liouvilleForm`), the Legendrian
lift of the exact Lagrangian graph of `dg`.

## Main results

* `TauCeti.CotangentBundle.isHorizontalMap_contactization_liouvilleForm_iff`: the graph criterion
  in `J¹Q`.
* `TauCeti.CotangentBundle.isLegendrianEmbedding_contactization_liouvilleForm`: one-jets of smooth
  functions are Legendrian embeddings.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Chapter 2 (the space of one-jets and Legendrian submanifolds).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer (1989), Appendix 4 (contact structures, Legendre submanifolds and the
  space of one-jets).
-/

public section

noncomputable section

open Bundle Function Module Manifold
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}

/-! ### One-jets of functions -/

namespace CotangentBundle

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {g : M → ℝ}

/-- **The graph criterion in `J¹Q`.** For a smooth one-form `α` and a smooth function `g` on `M`,
the section `q ↦ (α_q, g q)` of the one-jet space `T*M × ℝ` is horizontal for the kernel of the
contact form `dz - λ` exactly when `α = dg`. -/
theorem isHorizontalMap_contactization_liouvilleForm_iff (α : SmoothForm I M ℝ 1)
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) :
    IsHorizontalMap I (liouvilleForm I M).contactization.kerDistribution
        (fun x ↦ (TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x), g x)) ↔
      α.1 = mextDeriv (RoughForm.ofFunction I g) := by
  rw [SmoothForm.isHorizontalMap_contactization_iff _ (SmoothForm.degreeOneEquiv α).contMDiff hg,
    mpullback_liouvilleForm]

variable [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless]

/-- **One-jets of functions are Legendrian.** For a smooth function `g` on `M` with differential
`α = dg`, the one-jet `j¹g : q ↦ (dg_q, g q)` is a Legendrian embedding of `M` into the one-jet
space `T*M × ℝ` with its contact form `dz - λ`. -/
theorem isLegendrianEmbedding_contactization_liouvilleForm (α : SmoothForm I M ℝ 1)
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) (hα : α.1 = mextDeriv (RoughForm.ofFunction I g)) :
    IsLegendrianEmbedding I (liouvilleForm I M).contactization.kerDistribution
      (fun x ↦ (TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x), g x)) := by
  -- The kernel of `dz - λ` is a `C¹` contact structure, which needs a `C²` manifold structure.
  have : IsManifold ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) (1 + 1) (CotangentBundle I M × ℝ) :=
    .of_le (n := ∞) (by norm_num)
  -- The base projection of `T*M × ℝ` is a smooth left inverse of the one-jet.
  have hemb := ((SmoothForm.degreeOneEquiv α).contMDiff.prodMk hg).isSmoothEmbedding_of_leftInverse
    (by simp) ((contMDiff_proj (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)).comp contMDiff_fst)
    (g := fun p ↦ p.1.proj) fun _ ↦ rfl
  refine (isLegendrianEmbedding_iff_of_isSmoothEmbedding hemb).2
    ⟨isContactForm_contactization_liouvilleForm.isContactDistribution_kerDistribution,
      hemb.isImmersion, (isHorizontalMap_contactization_liouvilleForm_iff α hg).2 hα, ?_⟩
  rw [finrank_prod, finrank_prod, finrank_self, ContinuousLinearMap.dual_finrank_eq, two_mul]

/-- For a smooth function `g`, the section `q ↦ (α_q, g q)` of the one-jet space defined by a
smooth one-form `α` is a Legendrian embedding exactly when `α = dg`. -/
theorem isLegendrianEmbedding_contactization_liouvilleForm_iff (α : SmoothForm I M ℝ 1)
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) :
    IsLegendrianEmbedding I (liouvilleForm I M).contactization.kerDistribution
        (fun x ↦ (TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x), g x)) ↔
      α.1 = mextDeriv (RoughForm.ofFunction I g) :=
  ⟨fun h ↦ (isHorizontalMap_contactization_liouvilleForm_iff α hg).1 h.isHorizontalMap,
    isLegendrianEmbedding_contactization_liouvilleForm α hg⟩

end CotangentBundle

end TauCeti
