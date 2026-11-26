/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Sphere
public import TauCeti.Geometry.Symplectic.Lagrangian.Presymplectic
import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# The round sphere is coisotropic: its characteristic line is the Hopf direction

For the unit sphere `S` of a finite-dimensional real inner product space `E` with a linear
symplectic form `ω`, the inclusion `S → E` is a coisotropic embedding for the constant form `ω`
(`TauCeti.SymplecticForm.isCoisotropicEmbedding_coe_sphere`): it is a hypersurface, and maps of
codimension at most one with injective differentials are coisotropic
(`TauCeti.SmoothTwoForm.IsNondegenerate.isCoisotropicMap_of_finrank_le_finrank_add_one`). The
kernel of the form it induces is then a line field, the characteristic line field of `S`. The
inclusion pulls `ω` back to `dα`, the exterior derivative of the contact form `α = λ|S` given by
the radial primitive `λₓ(v) = ω(x, v) / 2`
(`TauCeti.SymplecticForm.mpullback_coe_sphere_constSmooth`). So the characteristic line of `S` at
`x` is spanned by the Reeb vector of `α`
(`TauCeti.SymplecticForm.ker_bilinFormAt_mpullback_coe_sphere`): it is a line, of the codimension
one of `S` (`TauCeti.SymplecticForm.finrank_ker_bilinFormAt_mpullback_coe_sphere`).

Read in `E`, this line is spanned by `K x`, where `ω(u, K v) = ⟪u, v⟫` for all `u` and `v`
(`TauCeti.SymplecticForm.map_ker_bilinFormAt_mpullback_coe_sphere`). For a complex structure `J`
compatible with `ω` whose metric is the inner product, `K = J`. For `ℂⁿ` with
`ω = Σⱼ dxⱼ ∧ dyⱼ`, `K` is multiplication by `i`, so the characteristic line of `S²ⁿ⁻¹` at `z` is
`ℝ (i z)`, the tangent line of the Hopf circle `t ↦ e^{it} z` through `z`; this is the form in
which the null directions of `Im ⟪·, ·⟫_ℂ` on `S²ⁿ⁺¹ ⊂ ℂⁿ⁺¹` are used to build the Fubini–Study
form (`TauCeti.ComplexProjectiveSpace.ker_bilinFormAt_mpullback_coe_sphere`). In the compatible case
the Reeb orbits of the sphere, which are tangent to the characteristic line, are these great
circles (`TauCeti.SymplecticForm.isMIntegralCurve_reebVectorField_sphereContactForm_iff`).

## Main results

* `TauCeti.SymplecticForm.isCoisotropicEmbedding_coe_sphere`: the unit sphere of a symplectic
  inner product space is a coisotropic submanifold.
* `TauCeti.SymplecticForm.mpullback_coe_sphere_constSmooth`: the form induced on the sphere is the
  exterior derivative of its contact form.
* `TauCeti.SymplecticForm.ker_bilinFormAt_mpullback_coe_sphere`: the characteristic line of the
  sphere is spanned by its Reeb vector field.
* `TauCeti.SymplecticForm.map_ker_bilinFormAt_mpullback_coe_sphere`: read in the ambient space,
  the characteristic line at `x` is `ℝ (K x)`, the Hopf direction.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 8 (coisotropic submanifolds and the coisotropic embedding theorem).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (hypersurfaces of contact type and their characteristic line bundles).
-/

public section

noncomputable section

open Module Metric
open scoped Manifold RealInnerProductSpace

namespace TauCeti

/-! ### The round sphere -/

namespace SymplecticForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)] (ω : SymplecticForm E)

/-- **The unit sphere is coisotropic.** The inclusion of the unit sphere of a finite-dimensional
real inner product space with a linear symplectic form `ω` is a coisotropic embedding for the
constant form `ω`. -/
theorem isCoisotropicEmbedding_coe_sphere :
    ω.isNondegenerate_constSmooth.IsCoisotropicEmbedding (𝓡 n)
      ((↑) : sphere (0 : E) 1 → E) := by
  refine ⟨contMDiff_coe_sphere.isImmersion_of_injective_mfderiv (by simp)
    injective_mvfderiv_subtypeVal_sphere, Topology.IsEmbedding.subtypeVal, ?_⟩
  refine ω.isNondegenerate_constSmooth.isCoisotropicMap_of_finrank_le_finrank_add_one ?_
    injective_mvfderiv_subtypeVal_sphere
  rw [finrank_euclideanSpace_fin, (Fact.out : finrank ℝ E = n + 1)]

/-- **The form induced on the sphere is exact.** The inclusion of the unit sphere pulls the
constant form `ω` back to `dα`, the exterior derivative of the contact form `α = λ|S` given by the
radial primitive `λₓ(v) = ω(x, v) / 2`. -/
theorem mpullback_coe_sphere_constSmooth :
    SmoothForm.mpullback ((↑) : sphere (0 : E) 1 → E) contMDiff_coe_sphere ω.constSmooth =
      mextDerivₗ (𝓡 n) 1 (ω.sphereContactForm n) := by
  refine SmoothBundleForm.ext_eval₂ fun x v w ↦ ?_
  rw [SmoothForm.eval₂_mpullback, eval₂_constSmooth_mfderiv_eq, SmoothBundleForm.eval₂_apply,
    mextDerivₗ_apply, mextDeriv_sphereContactForm_apply]

/-- **The characteristic line of the sphere is spanned by its Reeb vector field.** At each point
`x` of the unit sphere, the kernel of the form induced by `ω` is the line spanned by the Reeb
vector of the contact form `λ|S`. -/
theorem ker_bilinFormAt_mpullback_coe_sphere (x : sphere (0 : E) 1) :
    LinearMap.ker ((SmoothForm.mpullback ((↑) : sphere (0 : E) 1 → E) contMDiff_coe_sphere
        ω.constSmooth).bilinFormAt x) =
      ℝ ∙ (ω.sphereContactForm n).reebVectorField x := by
  rw [mpullback_coe_sphere_constSmooth, ← SmoothForm.characteristicVectorField_mextDerivₗ]
  exact SmoothForm.ker_bilinFormAt_eq_span_characteristicVectorField
    (SmoothForm.isContactForm_def.1 ω.isContactForm_sphereContactForm x)

/-- The characteristic line of the sphere is a line: the kernel of the form induced by `ω` has
dimension one, the codimension of the sphere. -/
theorem finrank_ker_bilinFormAt_mpullback_coe_sphere (x : sphere (0 : E) 1) :
    finrank ℝ (LinearMap.ker ((SmoothForm.mpullback ((↑) : sphere (0 : E) 1 → E)
      (contMDiff_coe_sphere (n := n)) ω.constSmooth).bilinFormAt x)) = 1 := by
  rw [ker_bilinFormAt_mpullback_coe_sphere]
  exact finrank_span_singleton
    ((ω.isContactForm_sphereContactForm (n := n)).reebVectorField_ne_zero x)

/-- **The characteristic line of the sphere is the Hopf direction.** Let `K` be a map with
`ω(u, K v) = ⟪u, v⟫` for all `u` and `v`, such as a compatible complex structure whose metric is
the inner product. Read in the ambient space, the characteristic line of the unit sphere at `x` is
the line `ℝ (K x)`. For `ℂⁿ` with its standard symplectic form, `K x = i x`, and this is the
direction of the Hopf circle through `x`. -/
theorem map_ker_bilinFormAt_mpullback_coe_sphere {K : E → E} (hK : ∀ u v, ω u (K v) = ⟪u, v⟫)
    (x : sphere (0 : E) 1) :
    (LinearMap.ker ((SmoothForm.mpullback ((↑) : sphere (0 : E) 1 → E) contMDiff_coe_sphere
        ω.constSmooth).bilinFormAt x)).map
        (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x : TangentSpace (𝓡 n) x →ₗ[ℝ] E) =
      ℝ ∙ K x := by
  rw [ker_bilinFormAt_mpullback_coe_sphere, Submodule.map_span, Set.image_singleton,
    ContinuousLinearMap.coe_coe, ω.mvfderiv_reebVectorField_sphereContactForm hK,
    Submodule.span_singleton_smul_eq (IsUnit.mk0 (2 : ℝ) two_ne_zero)]

end SymplecticForm

end TauCeti
