/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Sphere.RiemannSphere
public import TauCeti.Geometry.Symplectic.Manifold.Energy.Surface

/-!
# The energy of a pseudoholomorphic sphere is the area of its class

Let `X` be a compact boundaryless manifold with a closed two-form `form` and an almost complex
structure `J`, and let `u : OnePoint ℂ → X` be a smooth map of the Riemann sphere which is
pseudoholomorphic for the complex structure of the sphere and `J`. By the energy identity its energy
is its symplectic area `∫_{S²} u^* form`
(`TauCeti.SmoothTwoForm.energy_eq_integralTopForm_mpullback`), and the area of a map of the
Riemann sphere is the integral of `form` over its class `u_*[S²]` in `π₂(X, u ∞)`
(`TauCeti.integralTopForm_mpullback_eq_sphereIntegral`). So the energy of a pseudoholomorphic
sphere depends only on its class (`TauCeti.SmoothTwoForm.energy_eq_sphereIntegral`): it is the
symplectic area `ω(A)` of the class `A = u_*[S²]`, and by
`TauCeti.integralTopForm_mpullback_eq_apply_singularHomologyFunctor_map` it is the value on the
homology class of `u` of any homological period of `form`. This is what makes the energy of
pseudoholomorphic spheres in a fixed class uniformly bounded, the input to Gromov compactness.

When `form` tames `J`, the energy is nonnegative and vanishes only for constant maps, so the same
holds for the area of the class of a pseudoholomorphic sphere
(`TauCeti.SmoothTwoForm.Tames.sphereIntegral_nonneg`,
`TauCeti.SmoothTwoForm.Tames.sphereIntegral_eq_zero_iff`): a class containing a nonconstant
pseudoholomorphic sphere has positive area. In particular, if `form` integrates to zero over every
sphere, every pseudoholomorphic sphere is constant.

## Main results

* `TauCeti.SmoothTwoForm.energy_eq_sphereIntegral`: the energy of a pseudoholomorphic sphere is
  the integral of `form` over its class in `π₂`.
* `TauCeti.SmoothTwoForm.Tames.sphereIntegral_nonneg`,
  `TauCeti.SmoothTwoForm.Tames.sphereIntegral_eq_zero_iff`: for a taming form the class of a
  pseudoholomorphic sphere has nonnegative area, zero exactly when the sphere is constant.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 2.2 (Lemma 2.2.1: the energy of a pseudoholomorphic
  sphere is the symplectic area of its homology class).
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

namespace SmoothTwoForm

attribute [local instance] Complex.finrank_real_complex_fact

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace X]
  [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X] [T2Space X]
  {form : SmoothTwoForm I X} {J : SmoothAlmostComplexStructure I X} {u : OnePoint ℂ → X}

/-- **The energy of a pseudoholomorphic sphere is the area of its class.** For a closed two-form
`form` on a compact boundaryless manifold `X` and a smooth map `u : OnePoint ℂ → X`,
pseudoholomorphic for the complex structure of the Riemann sphere and an almost complex structure
`J` on `X`, the energy of `u` is the integral of `form` over the class `u_*[S²] ∈ π₂(X, u ∞)` of
the image of the standard sphere `TauCeti.riemannSphereSquare`. -/
theorem energy_eq_sphereIntegral (hform : form.IsClosed) (hu : ContMDiff 𝓘(ℝ, ℂ) I ∞ u)
    (hhol : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))
      J u) :
    form.energy J (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))
        ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex))) u =
      sphereIntegral form.val (u OnePoint.infty)
        (HomotopyGroup.map ⟨u, hu.continuous⟩ rfl ⟦riemannSphereSquare⟧) :=
  (energy_eq_integralTopForm_mpullback hhol.isPseudoholomorphicAt).trans
    (integralTopForm_mpullback_eq_sphereIntegral hform hu)

/-- **Pseudoholomorphic spheres have classes of nonnegative area.** If a closed two-form `form`
on a compact boundaryless manifold tames `J`, the integral of `form` over the class
`u_*[S²] ∈ π₂(X, u ∞)` of a smooth pseudoholomorphic map `u : OnePoint ℂ → X` is nonnegative. -/
theorem Tames.sphereIntegral_nonneg (htame : form.Tames J) (hform : form.IsClosed)
    (hu : ContMDiff 𝓘(ℝ, ℂ) I ∞ u)
    (hhol : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))
      J u) :
    0 ≤ sphereIntegral form.val (u OnePoint.infty)
      (HomotopyGroup.map ⟨u, hu.continuous⟩ rfl ⟦riemannSphereSquare⟧) :=
  energy_eq_sphereIntegral hform hu hhol ▸ htame.energy_nonneg
    (SmoothAlmostComplexStructure.orientation_eq_orientationAt_of_apply_one_eq_ofComplexManifold _)

/-- **Pseudoholomorphic spheres of zero area are constant.** If a closed two-form `form` on a
compact boundaryless manifold tames `J`, the integral of `form` over the class
`u_*[S²] ∈ π₂(X, u ∞)` of a smooth pseudoholomorphic map `u : OnePoint ℂ → X` vanishes exactly
when `u` is constant. -/
theorem Tames.sphereIntegral_eq_zero_iff (htame : form.Tames J) (hform : form.IsClosed)
    (hu : ContMDiff 𝓘(ℝ, ℂ) I ∞ u)
    (hhol : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))
      J u) :
    sphereIntegral form.val (u OnePoint.infty)
        (HomotopyGroup.map ⟨u, hu.continuous⟩ rfl ⟦riemannSphereSquare⟧) = 0 ↔
      ∀ z z', u z = u z' := by
  have ho :=
    SmoothAlmostComplexStructure.orientation_eq_orientationAt_of_apply_one_eq_ofComplexManifold
      (N := OnePoint ℂ) ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)
  rw [← energy_eq_sphereIntegral hform hu hhol]
  refine ⟨htame.apply_eq_of_energy_eq_zero ho (hu.of_le (by simp)), fun h ↦ ?_⟩
  refine (htame.energy_eq_zero_iff ho (hu.of_le (by simp))).2 fun z ↦ ?_
  rw [show u = fun _ ↦ u OnePoint.infty from funext fun z' ↦ h z' OnePoint.infty]
  exact mfderiv_const

end SmoothTwoForm

end TauCeti
