/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import TauCeti.Geometry.Contact.Sphere
public import TauCeti.Geometry.Symplectic.AlmostComplex.Rotation
public import TauCeti.Geometry.Symplectic.Hamiltonian.Hessian
import TauCeti.Geometry.Symplectic.CompatibleMetric
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Geometry.Manifold.IntegralCurve.Basic

/-!
# Periodic orbits of the quadratic Hamiltonians and the Reeb periods of the sphere

Let `ω` be a linear symplectic form on a finite-dimensional real inner product space `V` whose
inner product is the metric of a compatible complex structure `J`, `ω(u, J v) = ⟪u, v⟫`. For
`ℝ²ⁿ` with `ω = Σ dqⱼ ∧ dpⱼ` and its standard `J` this is the standard ball `D²ⁿ`, whose
Liouville structure is the radial primitive `λₓ(v) = ω(x, v) / 2`, with Liouville field `x / 2`
(`TauCeti.SymplecticForm.isLiouvilleCompletion_closedBall`). This file computes the periodic
orbits of the two flows that enter the symplectic homology of the ball: the Hamiltonian flows of
the quadratic Hamiltonians `a ‖x‖²`, which are linear at infinity with slope `a` on the unit ball
(`TauCeti.isLinearAtInfinity_mul_norm_sq`), and the Reeb flow of the boundary sphere.

Both are rotations along the complex lines of `J`: the solutions of the linear equation
`γ' = θ J γ` are the curves `γ(t) = cos (θ t) γ(0) + sin (θ t) J γ(0)`
(`TauCeti.AlmostComplexStructure.eq_cos_smul_add_sin_smul_of_hasDerivAt`), and for `γ(0) ≠ 0`
such a curve has period `T` exactly when `θ T ∈ 2πℤ`
(`TauCeti.AlmostComplexStructure.periodic_cos_smul_add_sin_smul_iff`).

* The Hamiltonian vector field of `a ‖x‖²` is `-2 a J x`
  (`TauCeti.SymplecticForm.hamiltonianVectorField_mul_norm_sq`). Its integral curves are
  `cos (2 a t) x - sin (2 a t) J x`
  (`TauCeti.SymplecticForm.eq_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq`), and a
  nonconstant one has period `T` exactly when `a T ∈ πℤ`
  (`TauCeti.SymplecticForm.periodic_iff_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq`). So
  `a ‖x‖²` has a nonconstant `1`-periodic orbit exactly when `a ∈ πℤ`
  (`TauCeti.SymplecticForm.exists_periodic_one_ne_zero_hamiltonianVectorField_mul_norm_sq_iff`).
  For a slope `a ∉ πℤ` the only `1`-periodic orbit is the constant orbit at the origin
  (`TauCeti.SymplecticForm.eq_zero_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq_of_periodic`),
  while for `a ∈ πℤ`, such as `a = π`, every orbit is `1`-periodic
  (`TauCeti.SymplecticForm.periodic_one_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq`). In
  particular the degenerate slopes are the multiples of `π`, not of `2π`.
* The Reeb vector field of the contact form `λ|S` of the unit sphere `S`
  (`TauCeti.SymplecticForm.sphereContactForm`) is `2 J x`
  (`TauCeti.SymplecticForm.mvfderiv_reebVectorField_sphereContactForm`). Its orbits are the great
  circles `cos (2 t) x + sin (2 t) J x` of the complex lines through the points of `S`, the
  fibres of the Hopf fibration
  (`TauCeti.SymplecticForm.isMIntegralCurve_reebVectorField_sphereContactForm_iff`). Every orbit
  is closed with minimal period `π`
  (`TauCeti.SymplecticForm.periodic_iff_of_isMIntegralCurve_reebVectorField_sphereContactForm`),
  and the Reeb periods of the sphere are exactly the multiples `k π`
  (`TauCeti.SymplecticForm.exists_periodic_reebVectorField_sphereContactForm_iff`).

These are the dynamical inputs of the computation `SH_*(D²ⁿ) = 0`: the slopes `a ∉ πℤ` are the
admissible ones, and for them the only generator of the Floer complex of `a ‖x‖²` is the constant
orbit at the origin.

## Main results

* `TauCeti.SymplecticForm.eq_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq`: the integral
  curves of `X_{a ‖x‖²} = -2 a J x` are the rotations `cos (2 a t) x - sin (2 a t) J x`.
* `TauCeti.SymplecticForm.periodic_iff_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq`: a
  nonconstant integral curve has period `T` exactly when `a T ∈ πℤ`.
* `TauCeti.SymplecticForm.exists_periodic_one_ne_zero_hamiltonianVectorField_mul_norm_sq_iff`:
  `a ‖x‖²` has a nonconstant `1`-periodic orbit exactly when `a ∈ πℤ`.
* `TauCeti.SymplecticForm.isMIntegralCurve_reebVectorField_sphereContactForm_iff`: the Reeb
  orbits of the unit sphere are the great circles `cos (2 t) x + sin (2 t) J x`.
* `TauCeti.SymplecticForm.periodic_iff_of_isMIntegralCurve_reebVectorField_sphereContactForm`:
  every Reeb orbit has the periods `k π`, and no others.
* `TauCeti.SymplecticForm.exists_periodic_reebVectorField_sphereContactForm_iff`: the Reeb periods
  of the unit sphere are the multiples of `π`.

## References

* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  Section 3 (the ball and the Hamiltonians linear at infinity).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Example 2.1.7 (the Reeb flow of the standard contact sphere and the Hopf fibration).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.
-/

public section

noncomputable section

open Function Metric Module Real
open scoped Manifold RealInnerProductSpace

namespace TauCeti

/-! ### The Hamiltonian flows of the quadratic Hamiltonians -/

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V}

omit [FiniteDimensional ℝ V] in
/-- The rotation `cos (2 a t) x - sin (2 a t) J x` is the rotation by the angle `-2 a t`, the form
in which `TauCeti.AlmostComplexStructure` states the rotations solving `γ' = θ J γ`. -/
private theorem cos_smul_sub_sin_smul_eq (a t : ℝ) (x : V) :
    Real.cos (2 * a * t) • x - Real.sin (2 * a * t) • J x =
      Real.cos (-2 * a * t) • x + Real.sin (-2 * a * t) • J x := by
  simp [neg_mul, Real.cos_neg, Real.sin_neg, sub_eq_add_neg, mul_assoc]

/-- **The flow of a quadratic Hamiltonian is a rotation.** If the inner product of `V` is the
metric `ω(·, J ·)`, the curve `t ↦ cos (2 a t) x - sin (2 a t) J x` is an integral curve of the
Hamiltonian vector field of `y ↦ a ‖y‖²`. -/
theorem hasDerivAt_hamiltonianVectorField_mul_norm_sq (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (a : ℝ)
    (x : V) (t : ℝ) :
    HasDerivAt (fun t ↦ Real.cos (2 * a * t) • x - Real.sin (2 * a * t) • J x)
      (ω.hamiltonianVectorField (fun y ↦ a * ‖y‖ ^ 2)
        (Real.cos (2 * a * t) • x - Real.sin (2 * a * t) • J x)) t := by
  simp only [hamiltonianVectorField_mul_norm_sq hg, cos_smul_sub_sin_smul_eq]
  exact J.hasDerivAt_cos_smul_add_sin_smul (-2 * a) x t

/-- **The integral curves of a quadratic Hamiltonian.** If the inner product of `V` is the metric
`ω(·, J ·)`, every integral curve of the Hamiltonian vector field of `y ↦ a ‖y‖²` is the rotation
`t ↦ cos (2 a t) γ(0) - sin (2 a t) J γ(0)` of its initial value along the complex line of `J`
through it. -/
theorem eq_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    {a : ℝ} {γ : ℝ → V}
    (hγ : ∀ t, HasDerivAt γ (ω.hamiltonianVectorField (fun y ↦ a * ‖y‖ ^ 2) (γ t)) t) (t : ℝ) :
    γ t = Real.cos (2 * a * t) • γ 0 - Real.sin (2 * a * t) • J (γ 0) := by
  simp only [hamiltonianVectorField_mul_norm_sq hg] at hγ
  rw [cos_smul_sub_sin_smul_eq]
  exact J.eq_cos_smul_add_sin_smul_of_hasDerivAt hγ t

/-- **The periods of a quadratic Hamiltonian.** If the inner product of `V` is the metric
`ω(·, J ·)`, an integral curve of the Hamiltonian vector field of `y ↦ a ‖y‖²` has period `T`
exactly when it is the constant orbit at the origin or `a T` is an integer multiple of `π`. -/
theorem periodic_iff_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {a : ℝ} {γ : ℝ → V}
    (hγ : ∀ t, HasDerivAt γ (ω.hamiltonianVectorField (fun y ↦ a * ‖y‖ ^ 2) (γ t)) t) (T : ℝ) :
    Periodic γ T ↔ γ 0 = 0 ∨ ∃ k : ℤ, a * T = k * π := by
  have hγ' : γ = fun t ↦ Real.cos (-2 * a * t) • γ 0 + Real.sin (-2 * a * t) • J (γ 0) := by
    funext t
    rw [eq_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq hg hγ t, cos_smul_sub_sin_smul_eq]
  obtain ⟨x, hx⟩ : ∃ x, γ 0 = x := ⟨_, rfl⟩
  rw [hx] at hγ' ⊢
  rcases eq_or_ne x 0 with h0 | h0
  · refine iff_of_true (fun t ↦ ?_) (Or.inl h0)
    rw [hγ']
    simp [h0]
  · rw [hγ', J.periodic_cos_smul_add_sin_smul_iff h0, or_iff_right h0]
    -- `-2 a T = k (2 π)` exactly when `a T = (-k) π`.
    exact (Equiv.neg ℤ).exists_congr fun k ↦ by
      rw [Equiv.neg_apply, Int.cast_neg]
      constructor <;> intro hk <;> linarith

/-- **The degenerate slopes are the multiples of `π`.** If `V` is nonzero and its inner product is
the metric `ω(·, J ·)`, the Hamiltonian `y ↦ a ‖y‖²` has a nonconstant `1`-periodic orbit exactly
when `a` is an integer multiple of `π`. -/
theorem exists_periodic_one_ne_zero_hamiltonianVectorField_mul_norm_sq_iff [Nontrivial V]
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (a : ℝ) :
    (∃ γ : ℝ → V, (∀ t, HasDerivAt γ (ω.hamiltonianVectorField (fun y ↦ a * ‖y‖ ^ 2) (γ t)) t) ∧
      Periodic γ 1 ∧ γ 0 ≠ 0) ↔ ∃ k : ℤ, a = k * π := by
  constructor
  · rintro ⟨γ, hγ, hper, h0⟩
    simpa [h0] using (periodic_iff_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq hg hγ 1).1 hper
  · rintro ⟨k, hk⟩
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hγ := hasDerivAt_hamiltonianVectorField_mul_norm_sq hg a x
    refine ⟨_, hγ, ?_, by simpa using hx⟩
    exact (periodic_iff_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq hg hγ 1).2
      (Or.inr ⟨k, by rw [mul_one, hk]⟩)

/-- **Admissible slopes have only the constant orbit.** If the inner product of `V` is the metric
`ω(·, J ·)` and `a` is not an integer multiple of `π`, the only `1`-periodic integral curve of the
Hamiltonian vector field of `y ↦ a ‖y‖²` is the constant orbit at the origin. -/
theorem eq_zero_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq_of_periodic
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {a : ℝ} (ha : ∀ k : ℤ, a ≠ k * π) {γ : ℝ → V}
    (hγ : ∀ t, HasDerivAt γ (ω.hamiltonianVectorField (fun y ↦ a * ‖y‖ ^ 2) (γ t)) t)
    (hper : Periodic γ 1) : γ = 0 := by
  have h0 : γ 0 = 0 := by
    simpa [ha] using (periodic_iff_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq hg hγ 1).1 hper
  funext t
  rw [eq_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq hg hγ t, h0]
  simp

/-- **At a degenerate slope every orbit is periodic.** If the inner product of `V` is the metric
`ω(·, J ·)` and `a` is an integer multiple of `π`, for instance `a = π`, every integral curve of
the Hamiltonian vector field of `y ↦ a ‖y‖²` is `1`-periodic. -/
theorem periodic_one_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {a : ℝ} {k : ℤ} (ha : a = k * π) {γ : ℝ → V}
    (hγ : ∀ t, HasDerivAt γ (ω.hamiltonianVectorField (fun y ↦ a * ‖y‖ ^ 2) (γ t)) t) :
    Periodic γ 1 :=
  (periodic_iff_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq hg hγ 1).2
    (Or.inr ⟨k, by rw [mul_one, ha]⟩)

/-! ### The Reeb flow of the unit sphere -/

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)] {ω : SymplecticForm E} {J : AlmostComplexStructure E}

omit [FiniteDimensional ℝ E] in
/-- The great circles `t ↦ cos (θ t) x + sin (θ t) J x` through the points of the unit sphere stay
on it: for a compatible `J` the vectors `x` and `J x` are orthonormal, so the circle is the
isometric image of the unit circle of `ℂ`. -/
private theorem cos_smul_add_sin_smul_mem_sphere (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    {x : E} (hx : x ∈ sphere (0 : E) 1) (θ : ℝ) :
    Real.cos θ • x + Real.sin θ • J x ∈ sphere (0 : E) 1 := by
  have hJ (v w : E) : ⟪J v, J w⟫ = ⟪v, w⟫ := by
    rw [inner_apply_left_eq_of_apply_apply_eq_inner hg, hg]
  have h := J.norm_re_smul_add_im_smul hJ (norm_eq_of_mem_sphere ⟨x, hx⟩)
    (Complex.exp (θ * Complex.I))
  rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.norm_exp_ofReal_mul_I] at h
  rwa [mem_sphere_zero_iff_norm]

/-- **The Reeb orbits of the unit sphere are great circles.** If the inner product of `E` is the
metric `ω(·, J ·)`, a curve `γ` on the unit sphere is an integral curve of the Reeb vector field of
the contact form `λ|S` exactly when it is the rotation `t ↦ cos (2 t) γ(0) + sin (2 t) J γ(0)` of
its initial point along the complex line of `J` through it. These great circles are the fibres of
the Hopf fibration. -/
theorem isMIntegralCurve_reebVectorField_sphereContactForm_iff
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {γ : ℝ → sphere (0 : E) 1} :
    IsMIntegralCurve γ (ω.sphereContactForm n).reebVectorField ↔
      ∀ t, (γ t : E) = Real.cos (2 * t) • (γ 0 : E) + Real.sin (2 * t) • J (γ 0 : E) := by
  -- In ambient coordinates the Reeb field is `x ↦ 2 J x`.
  have hR (x : sphere (0 : E) 1) :
      mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x
        ((ω.sphereContactForm n).reebVectorField x) = (2 : ℝ) • J (x : E) := by
    rw [← mvfderiv_apply_eq_mfderiv_apply]
    exact ω.mvfderiv_reebVectorField_sphereContactForm hg x
  have hcoe (x : sphere (0 : E) 1) :
      HasMFDerivAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x
        (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x) :=
    ((contMDiff_coe_sphere x).mdifferentiableAt one_ne_zero).hasMFDerivAt
  constructor
  · -- The ambient curve solves `γ' = 2 J γ`, so it is a rotation.
    intro hγ
    rw [isMIntegralCurve_iff_isMIntegralCurveOn] at hγ
    have hmap := hγ.map_of_mfderiv_eq (f := ((↑) : sphere (0 : E) 1 → E))
      (W := fun y : E ↦ (2 : ℝ) • J y) (fun t _ ↦ (hcoe (γ t)).mdifferentiableAt)
      (fun t _ ↦ hR (γ t))
    have hint := isMIntegralCurveOn_iff_isIntegralCurveOn.1 hmap
    exact J.eq_cos_smul_add_sin_smul_of_hasDerivAt (γ := fun t ↦ (γ t : E))
      fun t ↦ hasDerivWithinAt_univ.1 (hint t trivial)
  · -- The great circle is smooth on the sphere, and its velocity is the Reeb field since the
    -- differential of the inclusion is injective.
    intro hγ t
    set c : ℝ → E := fun t ↦ Real.cos (2 * t) • (γ 0 : E) + Real.sin (2 * t) • J (γ 0 : E)
    have hc : ContDiff ℝ 1 c := by fun_prop
    have hmem (t : ℝ) : c t ∈ sphere (0 : E) 1 :=
      cos_smul_add_sin_smul_mem_sphere hg (γ 0).property _
    have hγc : γ = Set.codRestrict c (sphere (0 : E) 1) hmem := funext fun t ↦ Subtype.ext (hγ t)
    have hγd : MDifferentiableAt 𝓘(ℝ) (𝓡 n) γ t := by
      rw [hγc]
      exact (hc.contMDiff.codRestrict_sphere hmem).mdifferentiableAt one_ne_zero
    -- The velocity of the ambient curve is `2 J γ`.
    have hv : mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) (γ t)
        (mfderiv 𝓘(ℝ) (𝓡 n) γ t (1 : ℝ)) = (2 : ℝ) • J (γ t : E) := by
      have h1 := (hcoe (γ t)).comp t hγd.hasMFDerivAt
      rw [show ((↑) : sphere (0 : E) 1 → E) ∘ γ = c from funext hγ] at h1
      have h2 : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ, E) c t _ :=
        (J.hasDerivAt_cos_smul_add_sin_smul 2 (γ 0 : E) t).hasFDerivAt.hasMFDerivAt
      -- Evaluating both derivatives of `c` at `1`; `change` unfolds the `TangentSpace` synonyms.
      have h := DFunLike.congr_fun (h1.mfderiv.symm.trans h2.mfderiv) (1 : ℝ)
      change _ = (1 : ℝ) • (2 : ℝ) • J (c t) at h
      rwa [one_smul, ← show (γ t : E) = c t from hγ t] at h
    refine hγd.hasMFDerivAt.congr_mfderiv (ContinuousLinearMap.ext_ring ?_)
    -- Compare the velocities after pushing them forward along the injective inclusion.
    change _ = (1 : ℝ) • (ω.sphereContactForm n).reebVectorField (γ t)
    rw [one_smul]
    refine injective_mvfderiv_subtypeVal_sphere (n := n) (γ t) ?_
    rw [mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply]
    exact hv.trans (hR (γ t)).symm

/-- **The periods of a Reeb orbit of the unit sphere.** If the inner product of `E` is the metric
`ω(·, J ·)`, every integral curve of the Reeb vector field of the contact form `λ|S` has period `T`
exactly when `T` is an integer multiple of `π`: every Reeb orbit is closed, with minimal period
`π`. -/
theorem periodic_iff_of_isMIntegralCurve_reebVectorField_sphereContactForm
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {γ : ℝ → sphere (0 : E) 1}
    (hγ : IsMIntegralCurve γ (ω.sphereContactForm n).reebVectorField) (T : ℝ) :
    Periodic γ T ↔ ∃ k : ℤ, T = k * π := by
  have hγ' : ((↑) : sphere (0 : E) 1 → E) ∘ γ =
      fun t ↦ Real.cos (2 * t) • (γ 0 : E) + Real.sin (2 * t) • J (γ 0 : E) :=
    funext ((isMIntegralCurve_reebVectorField_sphereContactForm_iff hg).1 hγ)
  have h0 : (γ 0 : E) ≠ 0 := ne_zero_of_mem_unit_sphere (γ 0)
  have hper : Periodic γ T ↔ Periodic (((↑) : sphere (0 : E) 1 → E) ∘ γ) T :=
    ⟨fun h t ↦ congrArg Subtype.val (h t), fun h t ↦ Subtype.ext (h t)⟩
  rw [hper, hγ', J.periodic_cos_smul_add_sin_smul_iff h0]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hk]; ring⟩

/-- **The Reeb periods of the unit sphere are the multiples of `π`.** If the inner product of `E`
is the metric `ω(·, J ·)`, the Reeb vector field of the contact form `λ|S` of the unit sphere has a
`T`-periodic integral curve exactly when `T` is an integer multiple of `π`. For `ℝ²ⁿ` with
`ω = Σ dqⱼ ∧ dpⱼ` these are the periods `k π` of the closed Reeb orbits of `∂D²ⁿ`, the `k`-fold
covers of the simple orbits of period `π`, which the slopes of the Hamiltonians defining
`SH_*(D²ⁿ)` must avoid. -/
theorem exists_periodic_reebVectorField_sphereContactForm_iff (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (T : ℝ) :
    (∃ γ : ℝ → sphere (0 : E) 1,
        IsMIntegralCurve γ (ω.sphereContactForm n).reebVectorField ∧ Periodic γ T) ↔
      ∃ k : ℤ, T = k * π := by
  constructor
  · rintro ⟨γ, hγ, hT⟩
    exact (periodic_iff_of_isMIntegralCurve_reebVectorField_sphereContactForm hg hγ T).1 hT
  · intro hT
    have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ E = n + 1)
    obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).2 zero_le_one
    have hmem (t : ℝ) : Real.cos (2 * t) • x + Real.sin (2 * t) • J x ∈ sphere (0 : E) 1 :=
      cos_smul_add_sin_smul_mem_sphere hg hx _
    have hγ : IsMIntegralCurve (fun t ↦ (⟨_, hmem t⟩ : sphere (0 : E) 1))
        (ω.sphereContactForm n).reebVectorField :=
      (isMIntegralCurve_reebVectorField_sphereContactForm_iff hg).2 fun t ↦ by simp
    exact ⟨_, hγ, (periodic_iff_of_isMIntegralCurve_reebVectorField_sphereContactForm hg hγ T).2 hT⟩

end Sphere

end SymplecticForm

end TauCeti
