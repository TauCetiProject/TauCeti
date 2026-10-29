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

## Main results

* `TauCeti.CotangentBundle.isTransverseAlong_vectorBundleEulerField_cosphereBundle`: `p ∂_p` is
  transverse to `S*M`.
* `TauCeti.CotangentBundle.isRestrictedContactType_cosphereBundle`: `S*M` is of restricted contact
  type, with primitive `-λ` and Liouville field `p ∂_p`.

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

end CotangentBundle

end TauCeti
