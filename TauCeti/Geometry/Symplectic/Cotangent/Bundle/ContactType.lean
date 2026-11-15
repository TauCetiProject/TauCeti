/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorField.Transverse
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Codisc
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.EulerField
public import TauCeti.Geometry.Symplectic.Liouville.ContactType

/-!
# The unit cosphere bundle is of restricted contact type

Let `M` be a smooth Riemannian manifold without boundary, with cotangent bundle
`T*M = TauCeti.CotangentBundle I M`, Liouville form `λ = p dq` and canonical symplectic form
`ω = -dλ`. The radial field `Z = p ∂_p`, the Euler vector field of the bundle, is the Liouville
field of the primitive `-λ` of `ω`
(`TauCeti.CotangentBundle.symplecticForm_interior_vectorBundleEulerField`).

Along the fibre ray `t ↦ t • z` the norm of covectors is `t ↦ |t| ‖z.2‖`, so the differential of
the norm sends `Z` to `‖z.2‖` (`TauCeti.CotangentBundle.mfderiv_norm_snd_vectorBundleEulerField`).
On the unit cosphere bundle `S*M = {‖p‖ = 1}`, a regular level of the norm, this is `1 ≠ 0`, so `Z`
is transverse to `S*M`
(`TauCeti.CotangentBundle.isTransverseAlong_vectorBundleEulerField_cosphereBundle`).
Hence `S*M` is a hypersurface of restricted contact type in `(T*M, ω)`, with primitive `-λ`
(`TauCeti.CotangentBundle.isRestrictedContactType_cosphereBundle`). This is the model case of the
hypersurfaces of contact type in cotangent bundles whose closed characteristics are produced from
almost existence.

Consequently the restriction `α_b = -λ|S*M` of the primitive to `S*M` is a contact form
(`TauCeti.CotangentBundle.isContactForm_mpullback_neg_liouvilleForm_cosphereBundle`), and so is
its negative `α_g = λ|S*M`, which defines the opposite coorientation of the same contact
distribution (`TauCeti.CotangentBundle.isContactForm_mpullback_liouvilleForm_cosphereBundle`).

## Main results

* `TauCeti.CotangentBundle.isTransverseAlong_vectorBundleEulerField_cosphereBundle`: `p ∂_p` is
  transverse to `S*M`.
* `TauCeti.CotangentBundle.isRestrictedContactType_cosphereBundle`: `S*M` is of restricted contact
  type, with primitive `-λ` and Liouville field `p ∂_p`.
* `TauCeti.CotangentBundle.isContactForm_mpullback_neg_liouvilleForm_cosphereBundle`,
  `TauCeti.CotangentBundle.isContactForm_mpullback_liouvilleForm_cosphereBundle`: `-λ|S*M` and
  `λ|S*M` are contact forms.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (the unit cotangent bundle as a hypersurface of contact type).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.2.
-/

public section

open Bundle Module
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **The radial field `p ∂_p` is transverse to the unit cosphere bundle** `S*M`: the differential
of the norm of covectors sends it to `1` along `S*M`. -/
theorem isTransverseAlong_vectorBundleEulerField_cosphereBundle :
    IsTransverseAlong 𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ) (vectorBundleEulerField I)
      (Subtype.val : cosphereBundle I M → CotangentBundle I M) := by
  refine isTransverseAlong_iff.2 fun z ↦ ?_
  rw [range_mfderiv_coe_cosphereBundle, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    mfderiv_norm_snd_vectorBundleEulerField (snd_ne_zero_of_mem_cosphereBundle z.prop),
    mem_cosphereBundle.1 z.prop]
  -- The tangent spaces of `ℝ` are `ℝ` itself.
  exact one_ne_zero (α := ℝ)

/-- **The unit cosphere bundle is of restricted contact type.** For the canonical symplectic form
`ω = -dλ` of the cotangent bundle of a Riemannian manifold, `S*M` is a hypersurface of restricted
contact type with primitive `-λ`: its Liouville field is the radial field `p ∂_p`, which is
transverse to `S*M`. -/
theorem isRestrictedContactType_cosphereBundle :
    IsRestrictedContactType 𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ)
      (symplecticForm I M).1 (-(liouvilleForm I M).1)
      (Subtype.val : cosphereBundle I M → CotangentBundle I M) :=
  isRestrictedContactType_iff.2
    ⟨by rw [mextDeriv_neg, ← symplecticForm_eq_neg_mextDeriv], vectorBundleEulerField I,
      contMDiff_vectorBundleEulerField, symplecticForm_interior_vectorBundleEulerField,
      isTransverseAlong_vectorBundleEulerField_cosphereBundle⟩

/-- **The unit cosphere bundle is a contact manifold.** The restriction `α_b = -λ|S*M` of the
primitive `-λ` of the canonical symplectic form `ω = -dλ` to the unit cosphere bundle `S*M` is a
contact form. -/
theorem isContactForm_mpullback_neg_liouvilleForm_cosphereBundle :
    (SmoothForm.mpullback (Subtype.val : cosphereBundle I M → CotangentBundle I M)
      (isSmoothEmbedding_coe_cosphereBundle (I := I) (M := M)).contMDiff
      (-liouvilleForm I M)).IsContactForm := by
  rcases isEmpty_or_nonempty (cosphereBundle I M) with hS | hS
  · exact SmoothForm.isContactForm_def.2 fun s ↦ isEmptyElim s
  obtain ⟨z⟩ := hS
  -- A unit covector exists, so the dimension of `T*M` is positive.
  have : Nontrivial (E →L[ℝ] ℝ) := ⟨⟨z.1.2, 0, snd_ne_zero_of_mem_cosphereBundle z.2⟩⟩
  exact isRestrictedContactType_cosphereBundle.isContactType.isContactForm_mpullback
    (isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate _
    (isSmoothEmbedding_coe_cosphereBundle.isImmersion.mfderiv_injective (by simp))
    (by rw [Module.finrank_fin_fun]; exact Nat.sub_add_cancel Module.finrank_pos)

/-- The restriction `α_g = λ|S*M` of the Liouville form to the unit cosphere bundle, which
defines the opposite coorientation of the contact distribution of `α_b = -λ|S*M`, is a contact
form. -/
theorem isContactForm_mpullback_liouvilleForm_cosphereBundle :
    (SmoothForm.mpullback (Subtype.val : cosphereBundle I M → CotangentBundle I M)
      (isSmoothEmbedding_coe_cosphereBundle (I := I) (M := M)).contMDiff
      (liouvilleForm I M)).IsContactForm := by
  rw [← SmoothForm.isContactForm_neg_iff, ← map_neg]
  exact isContactForm_mpullback_neg_liouvilleForm_cosphereBundle

end CotangentBundle

end TauCeti
