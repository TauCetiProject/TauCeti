/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Constancy
public import TauCeti.Geometry.Symplectic.AlmostComplex
import TauCeti.LinearAlgebra.Complex.Module
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import TauCeti.Analysis.Complex.AffineIsotropy
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Finite isotropy of nonconstant pseudoholomorphic spheres with a special point

A bubble in Gromov compactness, or in Gromov–Floer compactness for Floer cylinders and pairs of
pants, is a pseudoholomorphic sphere attached to the rest of the limit configuration at one or two
special points. A sphere with fewer than three special points is not a stable pointed curve: the
Möbius transformations fixing its special points form a positive-dimensional group. A limit
configuration is nevertheless stable when every such component is nonconstant, because a
nonconstant map is fixed by only finitely many of these reparametrizations. This file proves that
statement for spheres with a special point at `∞`.

Write the sphere as `OnePoint ℂ` with the special point at `∞`. The Möbius transformations fixing
`∞` are the complex affine automorphisms `z ↦ a z + b` of `ℂ`, the group `ℂ ≃ᵃ[ℂ] ℂ`, and a map
of the sphere is a map `u : ℂ → X` with a limit `y` at infinity. Its *isotropy* is the set of
affine automorphisms `f` with `u ∘ f = u`. A second special point at `0` cuts the isotropy down to
the `f` with `f 0 = 0`, a subset, so the finiteness below holds for it too.

* **The topological statement** (`Continuous.finite_setOf_comp_eq_iff`, in
  `TauCeti.Analysis.Complex.AffineIsotropy`). For a continuous map `u : ℂ → X` to a Hausdorff
  space with a limit at infinity, the isotropy is finite exactly when `u` is not invariant under
  all rotations `z ↦ z₀ + e^{iθ} (z - z₀)` about any centre `z₀`.
* **Rotation-invariant pseudoholomorphic maps are constant**
  (`MDifferentiable.apply_eq_of_forall_apply_add_exp_mul_I_mul_sub_eq`). This holds for a
  differentiable map `u` from `ℂ` to a manifold `M` solving the Cauchy–Riemann equation
  `∂ₜu = J(u) ∂ₛu` for pointwise complex structures `J(x)` on the tangent spaces of `M`, with no
  regularity or taming assumed of `J`. Invariance kills the angular derivative `du(i (z - z₀))`
  at every `z ≠ z₀`, the Cauchy–Riemann equation then kills the radial derivative, and invariance
  under the point reflection about `z₀` kills `du` at `z₀`.
* **Map stability** (`MDifferentiable.finite_setOf_comp_eq_iff_exists_ne`). Combining the two, a
  pseudoholomorphic sphere with a special point at `∞` has finite isotropy exactly when it is
  nonconstant. Constant spheres with one or two special points have infinite isotropy; they are
  the components that stability excludes.

The isotropy of a nonconstant sphere can be nontrivial: `z ↦ z²` is fixed by `z ↦ -z`. The
argument needs no unique continuation, no somewhere injectivity and no energy bound, only
continuity at `∞`, pointwise differentiability and the Cauchy–Riemann equation.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 5.1,
  on stable maps, and Chapter 4, on bubbling.
* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Section 9.2, on the finiteness of the
  automorphism groups of stable maps.
-/

public section

noncomputable section

open Filter Set Topology
open scoped Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {J : (x : M) → TauCeti.AlmostComplexStructure (TangentSpace I x)} {u : ℂ → M}

namespace TauCeti

/-! ### Rotation-invariant pseudoholomorphic maps -/

/-- A map invariant under the rotations about `z₀` has zero differential at `z₀`: the rotation by
`π` is the point reflection `z ↦ 2 z₀ - z`, so `du = -du` there. -/
private theorem mfderiv_eq_zero_of_forall_apply_rotation_eq (hu : MDifferentiable 𝓘(ℝ, ℂ) I u)
    {z₀ : ℂ} (hrot : ∀ (θ : ℝ) z, u (z₀ + Complex.exp (θ * Complex.I) * (z - z₀)) = u z) :
    mfderiv 𝓘(ℝ, ℂ) I u z₀ = 0 := by
  set ρ : ℂ → ℂ := fun z ↦ z₀ - (z - z₀)
  have hρ : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ρ z₀ (-ContinuousLinearMap.id ℝ ℂ) :=
    hasMFDerivAt_iff_hasFDerivAt.2 (((hasFDerivAt_id z₀).sub_const z₀).const_sub z₀)
  have hρz : ρ z₀ = z₀ := by simp [ρ]
  have huρ : u ∘ ρ = u := funext fun z ↦ by
    simpa [ρ, Complex.exp_pi_mul_I, sub_eq_add_neg] using hrot Real.pi z
  ext v
  have hv := mfderiv_comp_apply_of_eq z₀ (hu z₀) hρ.mdifferentiableAt hρz v
  rw [huρ, hρ.mfderiv] at hv
  -- The equation `du(v) = -du(v)` is read in the model space `E` of the tangent spaces.
  have hv' : @Eq E (mfderiv 𝓘(ℝ, ℂ) I u z₀ v) (-mfderiv 𝓘(ℝ, ℂ) I u z₀ v) := by
    rw [← map_neg]
    exact hv
  have h2 : ∀ w : E, w = -w → w = 0 := fun w hw ↦ by
    simpa [eq_neg_iff_add_eq_zero, ← two_smul ℝ] using hw
  rw [zero_apply]
  exact h2 _ hv'

/-- Along a map invariant under the rotations about `z₀`, the angular derivative
`du(i (x - z₀))` vanishes. -/
private theorem mfderiv_I_mul_sub_eq_zero (hu : MDifferentiable 𝓘(ℝ, ℂ) I u) {z₀ : ℂ}
    (hrot : ∀ (θ : ℝ) z, u (z₀ + Complex.exp (θ * Complex.I) * (z - z₀)) = u z) (x : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) I u x (Complex.I * (x - z₀)) = 0 := by
  set γ : ℝ → ℂ := fun θ ↦ z₀ + Complex.exp (θ * Complex.I) * (x - z₀)
  have hγ' : HasDerivAt γ (Complex.I * (x - z₀)) 0 := by
    have h := HasDerivAt.comp_ofReal (z := 0)
      (((HasDerivAt.cexp ((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const Complex.I)).mul_const
        (x - z₀)).const_add z₀)
    convert h using 1 <;> simp [γ]
  have hγ0 : γ 0 = x := by simp [γ]
  have huγ : u ∘ γ = fun _ ↦ u x := funext fun θ ↦ hrot θ x
  have h := (hγ0 ▸ hu x : MDifferentiableAt _ _ u (γ 0)).curveVelocity_comp_mfderiv hγ'
  rw [huγ, TauCeti.Manifold.curveVelocity_const, hγ0] at h
  exact h.symm

end TauCeti

namespace MDifferentiable

open TauCeti

/-- **Rotation-invariant pseudoholomorphic maps are constant.** Let `u : ℂ → M` be a
differentiable map to a manifold solving the Cauchy–Riemann equation `du(i) = J(u) du(1)` for
pointwise complex structures `J` on the tangent spaces of `M`. If `u` is invariant under all
rotations about a point `z₀`, then `u` is constant. -/
theorem apply_eq_of_forall_apply_add_exp_mul_I_mul_sub_eq [IsManifold I 1 M]
    (hu : MDifferentiable 𝓘(ℝ, ℂ) I u)
    (hJ : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u z Complex.I = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    {z₀ : ℂ} (hrot : ∀ (θ : ℝ) z, u (z₀ + Complex.exp (θ * Complex.I) * (z - z₀)) = u z)
    (z w : ℂ) : u z = u w := by
  refine hu.apply_eq_of_mfderiv_eq_zero (fun x ↦ ?_) z w
  rcases eq_or_ne x z₀ with rfl | hx
  · exact mfderiv_eq_zero_of_forall_apply_rotation_eq hu hrot
  · -- Away from the centre, the angular derivative vanishes, and so does the radial one, by the
    -- Cauchy–Riemann equation.
    have h0 := LinearMap.eq_zero_of_apply_I_eq_of_apply_eq_zero
      (mfderiv 𝓘(ℝ, ℂ) I u x : ℂ →L[ℝ] TangentSpace I (u x)).toLinearMap (hJ x)
      (J (u x)).apply_apply (mul_ne_zero Complex.I_ne_zero (sub_ne_zero.2 hx))
      (mfderiv_I_mul_sub_eq_zero hu hrot x)
    ext v
    rw [zero_apply]
    exact (LinearMap.congr_fun h0 v).trans (LinearMap.zero_apply v)

/-- **Map stability of pseudoholomorphic spheres with a special point.** Let `u : ℂ → M` be a
differentiable map to a Hausdorff manifold solving the Cauchy–Riemann equation
`du(i) = J(u) du(1)` for pointwise complex structures `J`, with a limit at infinity, so that it is
a pseudoholomorphic sphere with a special point at `∞`. Its isotropy, the set of complex affine
automorphisms `f` of `ℂ` with `u ∘ f = u`, is finite exactly when `u` is nonconstant. -/
theorem finite_setOf_comp_eq_iff_exists_ne [IsManifold I 1 M] [T2Space M]
    (hu : MDifferentiable 𝓘(ℝ, ℂ) I u)
    (hJ : ∀ z, mfderiv 𝓘(ℝ, ℂ) I u z Complex.I = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    {y : M} (hy : Tendsto u (cocompact ℂ) (𝓝 y)) :
    {f : ℂ ≃ᵃ[ℂ] ℂ | u ∘ f = u}.Finite ↔ ∃ z w, u z ≠ u w := by
  rw [hu.continuous.finite_setOf_comp_eq_iff hy]
  constructor
  · intro h
    obtain ⟨θ, z, hz⟩ := h 0
    exact ⟨_, _, hz⟩
  · rintro ⟨z, w, hzw⟩ z₀
    by_contra! hrot
    exact hzw (hu.apply_eq_of_forall_apply_add_exp_mul_I_mul_sub_eq hJ hrot z w)

end MDifferentiable
