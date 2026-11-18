/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Radial
import TauCeti.Analysis.Convex.BddAbove

/-!
# Collisions of radial motions in an attractive central potential

A particle of mass `m > 0` in a finite-dimensional inner product space `V`, moving in a central
potential `U`, has the energy `H(q, p) = ‖p‖² / (2m) + U(‖q‖)`. Its squared angular momentum is
`ℓ² = ‖q‖² ‖p‖² - ⟪q, p⟫²`, the squared length of the bivector `q ∧ p`.

In any potential `U` with `U' > 0` on `r > 0`, so attractive at every distance, a motion with
`ℓ = 0` cannot avoid the collision set `q = 0` for all time
(`TauCeti.sq_sub_inner_sq_ne_zero_of_hasDerivAt`). For such a motion the distance `r = ‖q‖` and
the radial momentum `p_r` solve `r' = p_r / m` and `p_r' = -U'(r) < 0`
(`TauCeti.hasDerivAt_radialProjection_comp`). So `r` has a strictly decreasing derivative on all
of `ℝ`: it is concave and not constant, hence not bounded below, while `r > 0`.

For the Kepler potential this gives one half of the Kepler collision domain, in
`TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Collision`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 8.
* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Addison-Wesley, 2002,
  Section 3.7.
-/

public section

noncomputable section

open Set
open scoped InnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Radial motions in an attractive potential collide.** Let the potential `U` have `U' > 0` on
`r > 0`, and let `γ` be an integral curve, defined for all time and avoiding the
collision set `q = 0`, of the Hamiltonian vector field of `‖p‖² / (2m) + U(‖q‖)` with `m > 0`.
Then the angular momentum of `γ` is nonzero: `‖q‖² ‖p‖² - ⟪q, p⟫² ≠ 0` at every time. -/
theorem sq_sub_inner_sq_ne_zero_of_hasDerivAt {m : ℝ} (hm : 0 < m) {U : ℝ → ℝ}
    (hU' : ∀ r, 0 < r → 0 < deriv U r) {γ : ℝ → V × V}
    (hγ : ∀ t, HasDerivAt γ
      ((stdSymplecticForm (V := V)).hamiltonianVectorField (centralForceHamiltonian m U) (γ t)) t)
    (hq : ∀ t, (γ t).1 ≠ 0) (t₀ : ℝ) :
    ‖(γ t₀).1‖ ^ 2 * ‖(γ t₀).2‖ ^ 2 - ⟪(γ t₀).1, (γ t₀).2⟫_ℝ ^ 2 ≠ 0 := by
  intro hℓ
  have hU (r : ℝ) (hr : 0 < r) : DifferentiableAt ℝ U r :=
    differentiableAt_of_deriv_ne_zero (hU' r hr).ne'
  have hr (t : ℝ) : 0 < (radialProjection (γ t)).1 := by
    rw [radialProjection_fst]
    exact norm_pos_iff.2 (hq t)
  -- With zero angular momentum, `(r, p_r)` solves `r' = p_r / m` and `p_r' = -U'(r)`.
  have hρ := hasDerivAt_radialProjection_comp (ℓ := 0) isPreconnected_univ (fun t _ ↦ hγ t)
    (fun t _ ↦ hq t) (fun t _ ↦ hU _ (norm_pos_iff.2 (hq t))) (mem_univ t₀) (by rw [hℓ]; ring)
  have hr' (t : ℝ) : HasDerivAt (fun s ↦ (radialProjection (γ s)).1)
      ((radialProjection (γ t)).2 / m) t :=
    hasDerivAt_fst_of_hasDerivAt_hamiltonianVectorField_effectivePotential (hρ t (mem_univ t))
      (hr t) (hU _ (hr t))
  have hp' (t : ℝ) : HasDerivAt (fun s ↦ (radialProjection (γ s)).2)
      (-deriv U (radialProjection (γ t)).1) t := by
    have h := hρ t (mem_univ t)
    rw [← Prod.mk.eta (p := radialProjection (γ t)),
      stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian_effectivePotential
        (hU _ (hr t)).hasDerivAt (hr t)] at h
    exact ((hasFDerivAt_snd (𝕜 := ℝ) (p := radialProjection (γ t))).comp_hasDerivAt t
      h).congr_deriv (by simp)
  -- So the radial velocity `p_r / m` is strictly decreasing and the radius is concave.
  have hanti : StrictAnti (deriv fun s ↦ (radialProjection (γ s)).1) := by
    have hp : StrictAnti fun s ↦ (radialProjection (γ s)).2 :=
      strictAnti_of_deriv_neg fun t ↦ by rw [(hp' t).deriv]; exact neg_lt_zero.2 (hU' _ (hr t))
    intro a b hab
    rw [(hr' a).deriv, (hr' b).deriv]
    exact div_lt_div_of_pos_right (hp hab) hm
  have hconc := hanti.antitone.concaveOn_univ_of_deriv fun t ↦ (hr' t).differentiableAt
  -- A concave function on `ℝ` bounded below by `0` is constant, so its derivative vanishes.
  have hbdd : BddAbove (range fun s ↦ -(radialProjection (γ s)).1) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact (neg_neg_of_pos (hr s)).le
  have hconst : (fun s ↦ (radialProjection (γ s)).1) = fun _ ↦ (radialProjection (γ 0)).1 :=
    funext fun t ↦ neg_injective (hconc.neg.eq_of_bddAbove hbdd t 0)
  have hderiv : (deriv fun s ↦ (radialProjection (γ s)).1) = fun _ ↦ 0 := by
    rw [hconst]
    exact funext fun _ ↦ deriv_const _ _
  exact (hanti zero_lt_one).ne (by rw [hderiv])

end TauCeti
