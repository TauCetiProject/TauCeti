/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Contactization
public import TauCeti.Geometry.Contact.Isotropic
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Graph
public import TauCeti.Geometry.Symplectic.Lagrangian.Exact
import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Legendrian lifts and one-jets of functions

Let `θ` be a one-form on a manifold `W`, and give `W × ℝ` the contactization form `dz - θ`
(`TauCeti.SmoothForm.contactization`). For smooth maps `ι : L → W` and `h : L → ℝ`, the map
`x ↦ (ι x, h x)` pulls `dz - θ` back to `dh - ι^* θ`. Hence it is isotropic for the contact
distribution `ker (dz - θ)` exactly when `ι^* θ = dh`
(`TauCeti.SmoothForm.isIsotropicMap_contactization_iff`). This is the **Legendrian lift**: an
exact Lagrangian map `ι` with primitive `h` lifts to the isotropic map `(ι, h)`, which is a
Legendrian immersion when `ι` is an immersion and a Legendrian embedding when `ι` is an embedding
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsExactLagrangianMap.isLegendrianImmersion_contactization`,
`TauCeti.SmoothTwoForm.IsNondegenerate.IsExactLagrangianMap.isLegendrianEmbedding_contactization`).

For the cotangent bundle `W = T*Q` with its Liouville form `λ`, the contactization `dz - λ` is the
standard contact form of the space of one-jets `J¹Q = T*Q × ℝ`. A smooth one-form `α` and a smooth
function `g` on `Q` give the section `q ↦ (α_q, g q)` of `J¹Q → Q`. Since `λ` is tautological,
this section is isotropic exactly when `α = dg`
(`TauCeti.CotangentBundle.isIsotropicMap_contactization_liouvilleForm_iff`). The **one-jet**
`j¹g : q ↦ (dg_q, g q)` of a smooth function is therefore a Legendrian embedding of `Q`
(`TauCeti.CotangentBundle.isLegendrianEmbedding_oneJet`), the Legendrian lift of the exact
Lagrangian graph of `dg`.

## Main results

* `TauCeti.SmoothForm.mpullback_prodMk_contactization`: `(ι, h)^* (dz - θ) = dh - ι^* θ`.
* `TauCeti.SmoothForm.isIsotropicMap_contactization_iff`: `(ι, h)` is isotropic exactly when
  `ι^* θ = dh`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.IsExactLagrangianMap.isLegendrianImmersion_contactization`:
  the Legendrian lift of an exact Lagrangian immersion.
* `TauCeti.CotangentBundle.isIsotropicMap_contactization_liouvilleForm_iff`: the graph criterion
  in `J¹Q`.
* `TauCeti.CotangentBundle.isLegendrianEmbedding_oneJet`: one-jets of smooth functions are
  Legendrian embeddings.

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

variable {E H W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace W] [ChartedSpace H W] [IsManifold I ∞ W]
  {E' H' L : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace L] [ChartedSpace H' L] [IsManifold J ∞ L]
  {ι : L → W} {h : L → ℝ}

/-! ### Lifts to the contactization -/

namespace SmoothForm

/-- **Legendrian lifts.** The map `x ↦ (ι x, h x)` is isotropic for the kernel of the
contactization form `dz - θ` exactly when `ι` pulls `θ` back to `dh`. -/
theorem isIsotropicMap_contactization_iff (θ : SmoothForm I W ℝ 1) (hι : ContMDiff J I ∞ ι)
    (hh : ContMDiff J 𝓘(ℝ) ∞ h) :
    IsIsotropicMap J θ.contactization.kerDistribution (fun x ↦ (ι x, h x)) ↔
      (mpullback ι hι θ).1 = mextDeriv (RoughForm.ofFunction J h) := by
  rw [isIsotropicMap_kerDistribution_iff_mpullback_eq_zero _ (hι.prodMk hh), ← Subtype.coe_inj,
    mpullback_prodMk_contactization θ hι hh, ZeroMemClass.coe_zero, sub_eq_zero, eq_comm]

end SmoothForm

namespace SmoothTwoForm.IsNondegenerate

variable {σ : SmoothTwoForm I W} {hσ : σ.IsNondegenerate} {θ : SmoothForm I W ℝ 1}

/-- The Legendrian lift `(ι, h)` of an exact Lagrangian map `ι` with primitive `h` is isotropic
for the kernel of the contactization form `dz - θ`. -/
theorem IsExactLagrangianMap.isIsotropicMap_contactization (hL : hσ.IsExactLagrangianMap J θ ι h)
    (hι : ContMDiff J I ∞ ι) :
    TauCeti.IsIsotropicMap J θ.contactization.kerDistribution (fun x ↦ (ι x, h x)) := by
  rw [SmoothForm.isIsotropicMap_contactization_iff θ hι hL.contMDiff_primitive,
    SmoothForm.coe_mpullback]
  exact hL.mpullback_eq

variable [FiniteDimensional ℝ E] [I.Boundaryless] [J.Boundaryless]

/-- **The Legendrian lift of an exact Lagrangian immersion.** If `ι : L → W` is an immersion from
a nonempty manifold which is an exact Lagrangian map with primitive `h`, then
`x ↦ (ι x, h x)` is a Legendrian immersion for the kernel of the contactization form `dz - θ`. -/
theorem IsExactLagrangianMap.isLegendrianImmersion_contactization [Nonempty L]
    (hL : hσ.IsExactLagrangianMap J θ ι h) (hι : IsImmersion J I ∞ ι) :
    IsLegendrianImmersion J θ.contactization.kerDistribution (fun x ↦ (ι x, h x)) where
  isImmersion := hι.prodMk hL.contMDiff_primitive (by simp)
  isIsotropicMap := hL.isIsotropicMap_contactization hι.contMDiff
  two_mul_finrank_add_one := by
    rw [finrank_prod, finrank_self, hL.isLagrangianMap.two_mul_finrank
      (hι.mfderiv_injective (by simp) (Classical.arbitrary L))]

/-- **The Legendrian lift of an exact Lagrangian embedding.** If `ι : L → W` is a smooth embedding
of a nonempty manifold which is an exact Lagrangian map with primitive `h`, then
`x ↦ (ι x, h x)` is a Legendrian embedding for the kernel of the contactization form `dz - θ`. -/
theorem IsExactLagrangianMap.isLegendrianEmbedding_contactization [Nonempty L]
    (hL : hσ.IsExactLagrangianMap J θ ι h) (hι : IsSmoothEmbedding J I ∞ ι) :
    IsLegendrianEmbedding J θ.contactization.kerDistribution (fun x ↦ (ι x, h x)) where
  toIsLegendrianImmersion := hL.isLegendrianImmersion_contactization hι.isImmersion
  isEmbedding := .of_comp (hι.isImmersion.contMDiff.continuous.prodMk
    hL.contMDiff_primitive.continuous) continuous_fst hι.isEmbedding

end SmoothTwoForm.IsNondegenerate

/-! ### One-jets of functions -/

namespace CotangentBundle

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {g : M → ℝ}

/-- **The graph criterion in `J¹Q`.** For a smooth one-form `α` and a smooth function `g` on `M`,
the section `q ↦ (α_q, g q)` of the one-jet space `T*M × ℝ` is isotropic for the kernel of the
contact form `dz - λ` exactly when `α = dg`. -/
theorem isIsotropicMap_contactization_liouvilleForm_iff (α : SmoothForm I M ℝ 1)
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) :
    IsIsotropicMap I (liouvilleForm I M).contactization.kerDistribution
        (fun x ↦ (TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x), g x)) ↔
      α.1 = mextDeriv (RoughForm.ofFunction I g) := by
  rw [SmoothForm.isIsotropicMap_contactization_iff _ (SmoothForm.degreeOneEquiv α).contMDiff hg,
    mpullback_liouvilleForm]

variable [FiniteDimensional ℝ E] [I.Boundaryless]

/-- **One-jets of functions are Legendrian.** For a smooth function `g` on `M` with differential
`α = dg`, the one-jet `j¹g : q ↦ (dg_q, g q)` is a Legendrian embedding of `M` into the one-jet
space `T*M × ℝ` with its contact form `dz - λ`. -/
theorem isLegendrianEmbedding_oneJet (α : SmoothForm I M ℝ 1) (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (hα : α.1 = mextDeriv (RoughForm.ofFunction I g)) :
    IsLegendrianEmbedding I (liouvilleForm I M).contactization.kerDistribution
      (fun x ↦ (TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x), g x)) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  -- The base projection of `T*M × ℝ` is a smooth left inverse of the one-jet.
  have hemb := ((SmoothForm.degreeOneEquiv α).contMDiff.prodMk hg).isSmoothEmbedding_of_leftInverse
    (by simp) ((contMDiff_proj (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)).comp contMDiff_fst)
    (g := fun p ↦ p.1.proj) fun _ ↦ rfl
  refine (isLegendrianEmbedding_iff_of_isSmoothEmbedding hemb).2
    ⟨hemb.isImmersion, (isIsotropicMap_contactization_liouvilleForm_iff α hg).2 hα, ?_⟩
  rw [finrank_prod, finrank_prod, finrank_self, ContinuousLinearMap.dual_finrank_eq, two_mul]

/-- For a smooth function `g`, the section `q ↦ (α_q, g q)` of the one-jet space defined by a
smooth one-form `α` is a Legendrian embedding exactly when `α = dg`. -/
theorem isLegendrianEmbedding_contactization_liouvilleForm_iff (α : SmoothForm I M ℝ 1)
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) :
    IsLegendrianEmbedding I (liouvilleForm I M).contactization.kerDistribution
        (fun x ↦ (TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x), g x)) ↔
      α.1 = mextDeriv (RoughForm.ofFunction I g) :=
  ⟨fun h ↦ (isIsotropicMap_contactization_liouvilleForm_iff α hg).1 h.isIsotropicMap,
    isLegendrianEmbedding_oneJet α hg⟩

end CotangentBundle

end TauCeti
