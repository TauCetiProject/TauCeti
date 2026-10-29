/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Codisc
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.EulerField
public import TauCeti.Geometry.Symplectic.Liouville.Domain
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The unit codisc bundle is a Liouville domain

Let `M` be a compact smooth Riemannian manifold without boundary, with cotangent bundle
`T*M = TauCeti.CotangentBundle I M`, Liouville form `λ = p dq` and canonical symplectic form
`ω = -dλ`, which is nondegenerate (`TauCeti.CotangentBundle.isSymplectic_symplecticForm`). The
radial field `Z = p ∂_p`, the Euler vector field of the bundle, is the Liouville field of the
primitive `-λ` of `ω` (`TauCeti.CotangentBundle.symplecticForm_interior_vectorBundleEulerField`).

The unit codisc bundle `D*M = {‖p‖ ≤ 1}` is compact, and it is the sublevel set of the norm of
covectors, which is continuous on `T*M` and smooth off the zero section. Along the fibre ray
`t ↦ t • z` the norm is `t ↦ |t| ‖z.2‖`, so the differential of the norm sends `Z` to `‖z.2‖`
(`TauCeti.CotangentBundle.mfderiv_norm_snd_vectorBundleEulerField`), which is `1 > 0` on the unit
cosphere bundle `S*M = {‖p‖ = 1}`. Hence `(D*M, -λ)` is a Liouville domain in `(T*M, ω)` with
Liouville field `p ∂_p` (`TauCeti.CotangentBundle.isLiouvilleDomain_codiscBundle`). It is the
Liouville domain on which the symplectic homology and the capacities of cotangent bundles are
computed; its boundary is `S*M`, of restricted contact type
(`TauCeti.CotangentBundle.isRestrictedContactType_cosphereBundle`).

## Main results

* `TauCeti.CotangentBundle.isLiouvilleDomain_codiscBundle`: `D*M` is a Liouville domain for the
  canonical symplectic form, with primitive `-λ`.

## References

* K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*, AMS Colloquium Publications 59,
  2012, Section 11.1 (the unit codisc bundle as a Liouville domain).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.2.
-/

public section

open Bundle
open scoped Manifold

namespace TauCeti

namespace CotangentBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x)]

/-- **The unit codisc bundle is a Liouville domain.** For a compact smooth Riemannian manifold
`M` without boundary, the unit codisc bundle `D*M` is a Liouville domain in `T*M` for the
canonical symplectic form `ω = -dλ`, with primitive `-λ`: its Liouville field, the radial field
`p ∂_p`, points strictly outwards along the unit cosphere bundle, the level `‖p‖ = 1` of the norm
of covectors. -/
theorem isLiouvilleDomain_codiscBundle [CompactSpace M] :
    IsLiouvilleDomain (symplecticForm I M) (-liouvilleForm I M) (codiscBundle I M) where
  isNondegenerate := isSymplectic_symplecticForm.isNondegenerate
  mextDeriv_eq := by
    rw [NegMemClass.coe_neg, mextDeriv_neg, ← symplecticForm_eq_neg_mextDeriv]
  isCompact := isCompact_codiscBundle
  subset_interior := by simp [ModelWithCorners.interior_eq_univ]
  exists_liouville_outward := by
    refine ⟨vectorBundleEulerField I, contMDiff_vectorBundleEulerField, ?_,
      fun z ↦ ‖z.2‖, 1, continuous_norm_snd, Set.ext fun _ ↦ mem_codiscBundle, fun z hz ↦
        ⟨contMDiffAt_norm_snd_of_mem_cosphereBundle z hz, ?_⟩⟩
    · rw [NegMemClass.coe_neg, symplecticForm_interior_vectorBundleEulerField]
    · -- `mvfderiv` is `mfderiv` read in `ℝ`, and the norm of covectors sends `p ∂_p` to `‖p‖`.
      rw [mvfderiv_apply_eq_mfderiv_apply,
        mfderiv_norm_snd_vectorBundleEulerField (snd_ne_zero_of_mem_cosphereBundle hz)]
      exact (mem_cosphereBundle.1 hz).symm ▸ one_pos

end CotangentBundle

end TauCeti
