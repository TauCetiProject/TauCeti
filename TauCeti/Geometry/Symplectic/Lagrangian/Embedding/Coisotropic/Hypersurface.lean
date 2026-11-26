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
# Hypersurfaces are coisotropic: the characteristic line of the round sphere

A subspace of codimension at most one of a symplectic vector space is coisotropic: its symplectic
orthogonal has dimension at most one, and every such subspace is isotropic
(`TauCeti.SymplecticForm.isCoisotropic_of_finrank_le_finrank_add_one`). Consequently every map of
codimension at most one with injective differentials, in particular every immersed hypersurface,
is coisotropic
(`TauCeti.SmoothTwoForm.IsNondegenerate.isCoisotropicMap_of_finrank_le_finrank_add_one`). The
kernel of the form it induces is then a line field, the characteristic line field of the
hypersurface. For a hypersurface of contact type it is spanned by a Reeb vector field: if a map
`f` pulls a one-form `θ` back to a contact form `α = f^* θ`, the kernel of `f^* dθ = dα` is the
line spanned by the Reeb vector of `α`
(`TauCeti.SmoothForm.ker_bilinFormAt_mpullback_mextDerivₗ`).

For the unit sphere `S` of a finite-dimensional real inner product space `E` with a linear
symplectic form `ω`, the inclusion `S → E` is a coisotropic embedding for the constant form `ω`
(`TauCeti.SymplecticForm.isCoisotropicEmbedding_coe_sphere`). It pulls `ω` back to `dα`, the
exterior derivative of the contact form `α = λ|S` given by the radial primitive
`λₓ(v) = ω(x, v) / 2` (`TauCeti.SymplecticForm.mpullback_coe_sphere_constSmooth`). So the
characteristic line of `S` at `x` is spanned by the Reeb vector of `α`
(`TauCeti.SymplecticForm.ker_bilinFormAt_mpullback_coe_sphere`): it is a line, of the codimension
one of `S` (`TauCeti.SymplecticForm.finrank_ker_bilinFormAt_mpullback_coe_sphere`).

Read in `E`, this line is spanned by `K x`, where `ω(u, K v) = ⟪u, v⟫` for all `u` and `v`
(`TauCeti.SymplecticForm.map_ker_bilinFormAt_mpullback_coe_sphere`). For a complex structure `J`
compatible with `ω` whose metric is the inner product, `K = J`. For `ℂⁿ` with
`ω = Σⱼ dxⱼ ∧ dyⱼ`, `K` is multiplication by `i`, so the characteristic line of `S²ⁿ⁻¹` at `z` is
`ℝ (i z)`, the tangent line of the Hopf circle `t ↦ e^{it} z` through `z`. In the compatible case
the Reeb orbits of the sphere, which are tangent to the characteristic line, are these great
circles (`TauCeti.SymplecticForm.isMIntegralCurve_reebVectorField_sphereContactForm_iff`).

## Main results

* `TauCeti.SymplecticForm.isCoisotropic_of_finrank_le_finrank_add_one`: a subspace of codimension
  at most one is coisotropic.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isCoisotropicMap_of_finrank_le_finrank_add_one`: a map
  of codimension at most one with injective differentials is coisotropic.
* `TauCeti.SmoothForm.ker_bilinFormAt_mpullback_mextDerivₗ`: the characteristic line of a
  hypersurface of contact type is spanned by the Reeb vector field.
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

open Module Function Metric
open scoped Manifold RealInnerProductSpace

namespace TauCeti

/-! ### Subspaces of codimension at most one -/

namespace SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] {ω : SymplecticForm V}
  {L : Submodule ℝ V}

/-- A subspace of dimension at most one is isotropic, since `ω` vanishes on every pair of
proportional vectors. -/
theorem isIsotropic_of_finrank_le_one (hL : finrank ℝ L ≤ 1) : ω.IsIsotropic L := by
  obtain ⟨u, hu⟩ := finrank_le_one_iff.1 hL
  rw [isIsotropic_iff]
  intro v hv w hw
  obtain ⟨a, ha⟩ := hu ⟨v, hv⟩
  obtain ⟨b, hb⟩ := hu ⟨w, hw⟩
  have hv' : v = a • (u : V) := (congrArg Subtype.val ha).symm.trans (Submodule.coe_smul a u)
  have hw' : w = b • (u : V) := (congrArg Subtype.val hb).symm.trans (Submodule.coe_smul b u)
  subst hv' hw'
  simp [ω.isAlt.self_eq_zero]

/-- **A subspace of codimension at most one is coisotropic.** Its symplectic orthogonal has
dimension at most one, so it is isotropic, and is therefore contained in its own symplectic
orthogonal, which is the subspace itself. -/
theorem isCoisotropic_of_finrank_le_finrank_add_one (hL : finrank ℝ V ≤ finrank ℝ L + 1) :
    ω.IsCoisotropic L := by
  have h : ω.IsIsotropic (ω.orthogonal L) :=
    isIsotropic_of_finrank_le_one (by rw [finrank_orthogonal]; omega)
  rw [isCoisotropic_iff_le]
  exact (isIsotropic_iff_le.1 h).trans (ω.orthogonal_orthogonal L).le

end SymplecticForm

/-! ### Maps of codimension at most one -/

section Map

open scoped ContDiff

namespace SmoothTwoForm.IsNondegenerate

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]
  [IsManifold I ∞ M]
  {F H' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate) {f : N → M}

/-- **Hypersurfaces are coisotropic.** A map into a manifold with a nondegenerate two-form, of
codimension at most one and with injective differentials, such as an immersed hypersurface, has
coisotropic tangent images. -/
theorem isCoisotropicMap_of_finrank_le_finrank_add_one (hdim : finrank ℝ E ≤ finrank ℝ F + 1)
    (hf : ∀ x, Injective (mfderiv J I f x)) : hσ.IsCoisotropicMap J f :=
  isCoisotropicMap_iff.2 fun x ↦ SymplecticForm.isCoisotropic_of_finrank_le_finrank_add_one <| by
    have hE : finrank ℝ (TangentSpace I (f x)) = finrank ℝ E := rfl
    have hF : finrank ℝ (TangentSpace J x) = finrank ℝ F := rfl
    rw [LinearMap.finrank_range_of_inj (hf x), hE, hF]
    exact hdim

end SmoothTwoForm.IsNondegenerate

namespace SmoothForm

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {F H' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} {N : Type*} [TopologicalSpace N]
  [ChartedSpace H' N] [IsManifold J ∞ N] {f : N → M}

/-- **The characteristic line of a hypersurface of contact type.** If a smooth map `f` pulls a
one-form `θ` back to a contact form `α = f^* θ`, then at every point the kernel of the form
`f^* dθ = dα` induced by `dθ` is the line spanned by the Reeb vector of `α`. -/
theorem ker_bilinFormAt_mpullback_mextDerivₗ (hf : ContMDiff J I ∞ f) {θ : SmoothForm I M ℝ 1}
    (hα : (mpullback f hf θ).IsContactForm) (x : N) :
    LinearMap.ker ((mpullback f hf (mextDerivₗ I 1 θ)).bilinFormAt x) =
      ℝ ∙ (mpullback f hf θ).reebVectorField x := by
  rw [← mextDerivₗ_mpullback, ← characteristicVectorField_mextDerivₗ]
  exact ker_bilinFormAt_eq_span_characteristicVectorField (isContactForm_def.1 hα x)

end SmoothForm

end Map

/-! ### The round sphere -/

namespace SymplecticForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)] (ω : SymplecticForm E)

omit [FiniteDimensional ℝ E] in
/-- The inclusion of the unit sphere has injective differentials. -/
private theorem injective_mfderiv_coe_sphere (x : sphere (0 : E) 1) :
    Injective (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x) := fun v w hvw ↦
  injective_mvfderiv_subtypeVal_sphere x <| by
    rw [mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply, hvw]

/-- **The unit sphere is coisotropic.** The inclusion of the unit sphere of a finite-dimensional
real inner product space with a linear symplectic form `ω` is a coisotropic embedding for the
constant form `ω`. -/
theorem isCoisotropicEmbedding_coe_sphere :
    ω.isNondegenerate_constSmooth.IsCoisotropicEmbedding (𝓡 n)
      ((↑) : sphere (0 : E) 1 → E) := by
  refine ⟨contMDiff_coe_sphere.isImmersion_of_injective_mfderiv (by simp)
    injective_mfderiv_coe_sphere, Topology.IsEmbedding.subtypeVal, ?_⟩
  refine ω.isNondegenerate_constSmooth.isCoisotropicMap_of_finrank_le_finrank_add_one ?_
    injective_mfderiv_coe_sphere
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
  have hα := ω.isContactForm_sphereContactForm (n := n)
  rw [sphereContactForm_def] at hα
  have hω : mextDerivₗ 𝓘(ℝ, E) 1 ω.radialPrimitive = ω.constSmooth :=
    Subtype.ext ((mextDerivₗ_apply _ _ _).trans ω.mextDeriv_radialPrimitive)
  rw [← hω, sphereContactForm_def]
  exact SmoothForm.ker_bilinFormAt_mpullback_mextDerivₗ contMDiff_coe_sphere hα x

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
