/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Complete
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Integrable
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Radial

/-!
# Collisions of central-force motions

A particle of mass `m > 0` moving in a central potential `U` has the Hamiltonian
`H(q, p) = ‖p‖² / (2m) + U(‖q‖)` on the phase space `V × V`. Its radial motion `(r, p_r)` solves
the reduced Hamilton equations `r' = p_r / m`, `p_r' = -U_ℓ'(r)`, for the effective potential
`U_ℓ(r) = ℓ² / (2 m r²) + U(r)` of the conserved squared angular momentum `ℓ²`
(`TauCeti.hasDerivAt_radialProjection_comp`). This file shows which motions run into the
collision set `q = 0`.

* **Inward motions collide.** If the effective force `-U_ℓ'(r)` is nowhere repulsive along a
  motion, its radial momentum decreases, so once the particle moves inwards its distance to the
  origin decreases at a definite rate and would reach `0` in finite time. Equivalently, a motion
  that avoids collision at all later times has nonnegative radial momentum
  (`TauCeti.snd_nonneg_of_forall_hasDerivAt_hamiltonianVectorField_effectivePotential`). By time
  reversal, one that avoids collision at all earlier times has nonpositive radial momentum.
* **Global motions are circular.** Hence a motion avoiding collision at all times, in an effective
  potential that is nowhere repulsive along it, has zero radial momentum, and the effective force
  vanishes along it: it is a circular orbit
  (`TauCeti.radialMomentum_eq_zero_and_deriv_eq_of_forall_hasDerivAt`).
* **Zero angular momentum means collision.** For an attractive potential, `U' > 0`, and zero
  angular momentum, the effective force `-U'(r)` never vanishes, so no such motion avoids
  collision at all times. Every global noncollision motion therefore has nonzero angular momentum
  (`TauCeti.sq_sub_inner_sq_ne_zero_of_hasDerivAt`).
* **Zero angular momentum means motion on a ray.** If the conserved squared angular momentum
  vanishes, the momentum is radial at every time, so the direction `q / ‖q‖` of the position is
  constant: the motion stays on a fixed ray through the origin, with momentum along it
  (`TauCeti.sameRay_fst_of_hasDerivAt`, `TauCeti.snd_eq_radialMomentum_smul_of_hasDerivAt`). This
  holds for every central potential.
* **Incompleteness.** For a non-repulsive potential, `U' ≥ 0`, a particle thrown straight at the
  centre has zero angular momentum and nonzero radial momentum, so it is not on a circular orbit
  and cannot avoid collision at all times. As soon as `V ≠ 0` such states exist, so the
  Hamiltonian flow on the punctured phase space `{(q, p) | q ≠ 0}` is not complete
  (`TauCeti.not_isCompleteVectorField_hamiltonianVectorField_puncturedPhaseSpace`).

Central-force motions are reversible: `s ↦ (q(-s), -p(-s))` is again a motion
(`TauCeti.hasDerivAt_reverse_hamiltonianVectorField_centralForceHamiltonian`), as for the radial
motion (`TauCeti.hasDerivAt_reverse_hamiltonianVectorField_effectivePotential`).

The Kepler potential `-κ / r`, `κ > 0`, is attractive; its collision domain and collision orbits
are treated in `TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Collision`.

The statements about motions are made for curves in `V × V` solving Hamilton's equations
`γ' = X_H(γ)` and avoiding the collision set, with `U` differentiable along them.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 8.
* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Addison-Wesley, 2002,
  Section 3.3.
-/

public section

open Set
open scoped InnerProductSpace Manifold ContDiff

namespace TauCeti

/-! ### The reduced radial motion -/

section Reduced

variable {m ℓ : ℝ} {U : ℝ → ℝ}

/-- **Inward radial motions in a nonrepulsive effective potential collide.** Let `m > 0`, and let
`γ = (r, p_r)` be an integral curve of the reduced Hamiltonian vector field of
`H_ℓ(r, p_r) = p_r² / (2m) + U_ℓ(r)` at all times `t ≥ a`, staying in the half-line `r > 0`, with
`U` differentiable along it. If the effective force is nowhere repulsive along `γ`,
`ℓ² / (m r³) ≤ U'(r)`, then the radial momentum at time `a` is nonnegative: a motion moving inwards
at time `a` cannot avoid the collision `r = 0` at all later times. -/
theorem snd_nonneg_of_forall_hasDerivAt_hamiltonianVectorField_effectivePotential (hm : 0 < m)
    {γ : ℝ → ℝ × ℝ} {a : ℝ}
    (hγ : ∀ t ≥ a, HasDerivAt γ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
      (centralForceHamiltonian m (effectivePotential m ℓ U)) (γ t)) t)
    (hr : ∀ t ≥ a, 0 < (γ t).1) (hU : ∀ t ≥ a, DifferentiableAt ℝ U (γ t).1)
    (hforce : ∀ t ≥ a, ℓ ^ 2 / (m * (γ t).1 ^ 3) ≤ deriv U (γ t).1) :
    0 ≤ (γ a).2 := by
  by_contra! hp
  have hr' (t : ℝ) (ht : t ∈ Ici a) :=
    hasDerivAt_fst_of_hasDerivAt_hamiltonianVectorField_effectivePotential (hγ t ht) (hr t ht)
      (hU t ht)
  have hp' (t : ℝ) (ht : t ∈ Ici a) :=
    hasDerivAt_snd_of_hasDerivAt_hamiltonianVectorField_effectivePotential (hγ t ht) (hr t ht)
      (hU t ht)
  -- The radial momentum has derivative `ℓ² / (m r³) - U'(r) ≤ 0`, so it decreases on `[a, ∞)`.
  have hanti : AntitoneOn (fun s ↦ (γ s).2) (Ici a) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici a)
      (fun t ht ↦ (hp' t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hp' t (interior_subset ht)).hasDerivWithinAt)
      fun t ht ↦ sub_nonpos.2 (hforce t (interior_subset ht))
  -- Hence `r' = p_r / m ≤ p_r(a) / m < 0` on `[a, ∞)`, and `r` vanishes by time
  -- `T = a + r(a) m / (-p_r(a))`.
  set T := a + (γ a).1 * m / -(γ a).2
  have hT : a ≤ T := le_add_of_nonneg_right
    (div_nonneg (mul_nonneg (hr a le_rfl).le hm.le) (neg_nonneg.2 hp.le))
  have hle := (convex_Ici a).image_sub_le_mul_sub_of_deriv_le (f := fun s ↦ (γ s).1)
    (C := (γ a).2 / m) (fun t ht ↦ (hr' t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hr' t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ by
      rw [(hr' t (interior_subset ht)).deriv]
      exact div_le_div_of_nonneg_right (hanti self_mem_Ici (interior_subset ht)
        (interior_subset ht : a ≤ t)) hm.le)
    a self_mem_Ici T hT hT
  have hrT := hr T hT
  have hcalc : (γ a).2 / m * (T - a) = -(γ a).1 := by
    simp only [T, add_sub_cancel_left]
    field_simp [hm.ne', hp.ne]
  simp only [hcalc] at hle
  linarith

/-- **Time reversal of the radial motion.** If `γ = (r, p_r)` is an integral curve of the reduced
Hamiltonian vector field of `H_ℓ(r, p_r) = p_r² / (2m) + U_ℓ(r)` at time `-t`, in the half-line
`r > 0` with `U` differentiable at the radius, then the reversed motion
`s ↦ (r(-s), -p_r(-s))` is an integral curve of the same field at time `t`. -/
theorem hasDerivAt_reverse_hamiltonianVectorField_effectivePotential {γ : ℝ → ℝ × ℝ} {t : ℝ}
    (hγ : HasDerivAt γ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
      (centralForceHamiltonian m (effectivePotential m ℓ U)) (γ (-t))) (-t))
    (hr : 0 < (γ (-t)).1) (hU : DifferentiableAt ℝ U (γ (-t)).1) :
    HasDerivAt (fun s ↦ ((γ (-s)).1, -(γ (-s)).2))
      ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
        (centralForceHamiltonian m (effectivePotential m ℓ U)) ((γ (-t)).1, -(γ (-t)).2)) t := by
  have h₁ := (hasDerivAt_fst_of_hasDerivAt_hamiltonianVectorField_effectivePotential hγ hr
    hU).scomp t (hasDerivAt_neg t)
  have h₂ := (hasDerivAt_snd_of_hasDerivAt_hamiltonianVectorField_effectivePotential hγ hr
    hU).scomp t (hasDerivAt_neg t)
  rw [stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian_effectivePotential
    hU.hasDerivAt hr]
  exact (h₁.prodMk h₂.neg).congr_deriv (by ext <;> simp [neg_div])

/-- **Radial motions avoiding collision in the past move inwards.** Let `m > 0`, and let
`γ = (r, p_r)` be an integral curve of the reduced Hamiltonian vector field at all times `t ≤ a`,
staying in the half-line `r > 0`, with `U` differentiable along it. If the effective force is
nowhere repulsive along `γ`, `ℓ² / (m r³) ≤ U'(r)`, then the radial momentum at time `a` is
nonpositive. -/
theorem snd_nonpos_of_forall_hasDerivAt_hamiltonianVectorField_effectivePotential (hm : 0 < m)
    {γ : ℝ → ℝ × ℝ} {a : ℝ}
    (hγ : ∀ t ≤ a, HasDerivAt γ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
      (centralForceHamiltonian m (effectivePotential m ℓ U)) (γ t)) t)
    (hr : ∀ t ≤ a, 0 < (γ t).1) (hU : ∀ t ≤ a, DifferentiableAt ℝ U (γ t).1)
    (hforce : ∀ t ≤ a, ℓ ^ 2 / (m * (γ t).1 ^ 3) ≤ deriv U (γ t).1) :
    (γ a).2 ≤ 0 := by
  -- The reversed motion avoids collision at all times `t ≥ -a`.
  have h := snd_nonneg_of_forall_hasDerivAt_hamiltonianVectorField_effectivePotential hm
    (γ := fun s ↦ ((γ (-s)).1, -(γ (-s)).2)) (a := -a)
    (fun t ht ↦ hasDerivAt_reverse_hamiltonianVectorField_effectivePotential
      (hγ (-t) (neg_le.1 ht)) (hr (-t) (neg_le.1 ht)) (hU (-t) (neg_le.1 ht)))
    (fun t ht ↦ hr (-t) (neg_le.1 ht)) (fun t ht ↦ hU (-t) (neg_le.1 ht))
    fun t ht ↦ hforce (-t) (neg_le.1 ht)
  simpa using h

/-- **Global radial motions in a nonrepulsive effective potential are circular.** Let `m > 0`, and
let `γ = (r, p_r)` be an integral curve of the reduced Hamiltonian vector field at all times,
staying in the half-line `r > 0`, with `U` differentiable along it. If the effective force is
nowhere repulsive along `γ`, `ℓ² / (m r³) ≤ U'(r)`, then the radial momentum vanishes and the
effective force vanishes, `U'(r) = ℓ² / (m r³)`, at every time. -/
theorem snd_eq_zero_and_deriv_eq_of_forall_hasDerivAt_hamiltonianVectorField_effectivePotential
    (hm : 0 < m) {γ : ℝ → ℝ × ℝ}
    (hγ : ∀ t, HasDerivAt γ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
      (centralForceHamiltonian m (effectivePotential m ℓ U)) (γ t)) t)
    (hr : ∀ t, 0 < (γ t).1) (hU : ∀ t, DifferentiableAt ℝ U (γ t).1)
    (hforce : ∀ t, ℓ ^ 2 / (m * (γ t).1 ^ 3) ≤ deriv U (γ t).1) (t : ℝ) :
    (γ t).2 = 0 ∧ deriv U (γ t).1 = ℓ ^ 2 / (m * (γ t).1 ^ 3) := by
  have hzero (s : ℝ) : (γ s).2 = 0 := le_antisymm
    (snd_nonpos_of_forall_hasDerivAt_hamiltonianVectorField_effectivePotential hm
      (fun t _ ↦ hγ t) (fun t _ ↦ hr t) (fun t _ ↦ hU t) fun t _ ↦ hforce t)
    (snd_nonneg_of_forall_hasDerivAt_hamiltonianVectorField_effectivePotential hm
      (fun t _ ↦ hγ t) (fun t _ ↦ hr t) (fun t _ ↦ hU t) fun t _ ↦ hforce t)
  refine ⟨hzero t, ?_⟩
  -- The radial momentum is identically zero, so its derivative `ℓ² / (m r³) - U'(r)` vanishes.
  have h := hasDerivAt_snd_of_hasDerivAt_hamiltonianVectorField_effectivePotential (hγ t) (hr t)
    (hU t)
  rw [show (fun s ↦ (γ s).2) = fun _ ↦ (0 : ℝ) from funext hzero] at h
  exact (sub_eq_zero.1 (h.unique (hasDerivAt_const t 0))).symm

end Reduced

/-! ### Central-force motions -/

section CentralForce

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {m : ℝ} {U : ℝ → ℝ}

/-- **Global central-force motions in a nonrepulsive effective potential are circular.** Let
`m > 0`, and let `γ` be a solution of Hamilton's equations for `H(q, p) = ‖p‖² / (2m) + U(‖q‖)`
at all times, avoiding the collision set, with `U` differentiable along it. Let `ℓ²` be its
conserved squared angular momentum `‖q‖² ‖p‖² - ⟪q, p⟫²`. If the effective force is nowhere
repulsive along `γ`, `ℓ² / (m ‖q‖³) ≤ U'(‖q‖)`, then at every time the radial momentum vanishes and
`U'(‖q‖) = ℓ² / (m ‖q‖³)`: the motion keeps a constant distance from the origin. -/
theorem radialMomentum_eq_zero_and_deriv_eq_of_forall_hasDerivAt (hm : 0 < m) {γ : ℝ → V × V}
    (hγ : ∀ t, HasDerivAt γ
      ((stdSymplecticForm (V := V)).hamiltonianVectorField (centralForceHamiltonian m U) (γ t)) t)
    (hq : ∀ t, (γ t).1 ≠ 0) (hU : ∀ t, DifferentiableAt ℝ U ‖(γ t).1‖) {ℓ t₀ : ℝ}
    (hℓ : ℓ ^ 2 = ‖(γ t₀).1‖ ^ 2 * ‖(γ t₀).2‖ ^ 2 - ⟪(γ t₀).1, (γ t₀).2⟫_ℝ ^ 2)
    (hforce : ∀ t, ℓ ^ 2 / (m * ‖(γ t).1‖ ^ 3) ≤ deriv U ‖(γ t).1‖) (t : ℝ) :
    radialMomentum (γ t) = 0 ∧ deriv U ‖(γ t).1‖ = ℓ ^ 2 / (m * ‖(γ t).1‖ ^ 3) := by
  -- The radial projection `(‖q‖, p_r)` of `γ` is a global radial motion.
  have h := snd_eq_zero_and_deriv_eq_of_forall_hasDerivAt_hamiltonianVectorField_effectivePotential
    hm (γ := radialProjection ∘ γ)
    (fun t ↦ hasDerivAt_radialProjection_comp isPreconnected_univ (fun t _ ↦ hγ t)
      (fun t _ ↦ hq t) (fun t _ ↦ hU t) (mem_univ t₀) hℓ t (mem_univ t))
    (fun t ↦ by simpa [radialProjection_fst] using hq t)
    (fun t ↦ by simpa [radialProjection_fst] using hU t)
    (fun t ↦ by simpa [radialProjection_fst] using hforce t) t
  simpa [radialProjection_fst, radialProjection_snd] using h

/-- **Global motions in an attractive potential have nonzero angular momentum.** Let `m > 0`, and
let `γ` be a solution of Hamilton's equations for `H(q, p) = ‖p‖² / (2m) + U(‖q‖)` at all times,
avoiding the collision set, with `U` differentiable along it and attractive there, `U'(‖q‖) > 0`.
Then its squared angular momentum `‖q‖² ‖p‖² - ⟪q, p⟫²` is nonzero: a motion with zero angular
momentum cannot avoid the collision set at all times. -/
theorem sq_sub_inner_sq_ne_zero_of_hasDerivAt (hm : 0 < m) {γ : ℝ → V × V}
    (hγ : ∀ t, HasDerivAt γ
      ((stdSymplecticForm (V := V)).hamiltonianVectorField (centralForceHamiltonian m U) (γ t)) t)
    (hq : ∀ t, (γ t).1 ≠ 0) (hU : ∀ t, DifferentiableAt ℝ U ‖(γ t).1‖)
    (hattr : ∀ t, 0 < deriv U ‖(γ t).1‖) (t : ℝ) :
    ‖(γ t).1‖ ^ 2 * ‖(γ t).2‖ ^ 2 - ⟪(γ t).1, (γ t).2⟫_ℝ ^ 2 ≠ 0 := by
  intro h
  -- With zero angular momentum the effective force is the attractive force `-U'`.
  have h₀ := (radialMomentum_eq_zero_and_deriv_eq_of_forall_hasDerivAt hm hγ hq hU (ℓ := 0)
    (t₀ := t) (by rw [h]; ring) (fun s ↦ by simpa using (hattr s).le) t).2
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div] at h₀
  exact (hattr t).ne' h₀

/-- **Non-repulsive central-force flows are not complete.** Let `V ≠ 0`, `m > 0`, and let `U` be
`C²` and non-repulsive, `U' ≥ 0`, on `(0, ∞)`. On the punctured phase space `{(q, p) | q ≠ 0}`,
with the restriction of the standard symplectic form, the Hamiltonian vector field of
`H(q, p) = ‖p‖² / (2m) + U(‖q‖)` is not complete: a particle thrown straight at the centre, from a
point `q ≠ 0` with momentum `-q`, has zero angular momentum and moves inwards, so it cannot avoid
the collision set at all times. This includes the free particle `U = 0`. -/
theorem not_isCompleteVectorField_hamiltonianVectorField_puncturedPhaseSpace [Nontrivial V]
    (hm : 0 < m) (hU : ContDiffOn ℝ 2 U (Ioi 0)) (hU' : ∀ r, 0 < r → 0 ≤ deriv U r) :
    ¬ IsCompleteVectorField (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m U ∘ Subtype.val)) := by
  intro hcomplete
  -- The Hamiltonian is `C²` off the collision set, so its flow gives global motions.
  have hH : ContMDiff 𝓘(ℝ, V × V) 𝓘(ℝ) 2 (centralForceHamiltonian m U ∘
      (Subtype.val : puncturedPhaseSpace V → V × V)) :=
    contMDiff_centralForceHamiltonian_comp_subtypeVal fun _ hr ↦ hU.contDiffAt (Ioi_mem_nhds hr)
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  obtain ⟨γ, hγ₀, hγ⟩ := SymplecticForm.exists_forall_hasDerivAt_of_isCompleteVectorField _ hH
    hcomplete (x := (u, -u)) (mem_puncturedPhaseSpace.2 hu)
  have hq (t : ℝ) : (γ t).1 ≠ 0 := mem_puncturedPhaseSpace.1 (hγ t).1
  have hr (t : ℝ) : 0 < ‖(γ t).1‖ := norm_pos_iff.2 (hq t)
  -- With zero angular momentum the global motion would have zero radial momentum.
  have h := (radialMomentum_eq_zero_and_deriv_eq_of_forall_hasDerivAt hm (fun t ↦ (hγ t).2) hq
    (fun t ↦ (hU.differentiableOn (by norm_num) _ (hr t)).differentiableAt (Ioi_mem_nhds (hr t)))
    (ℓ := 0) (t₀ := 0)
    (by rw [hγ₀]; simp only [inner_neg_right, norm_neg, real_inner_self_eq_norm_sq]; ring)
    (fun t ↦ by simpa using hU' _ (hr t)) 0).1
  -- But the particle thrown at the centre has radial momentum `-‖u‖ ≠ 0`.
  rw [radialMomentum_eq_zero_iff, hγ₀] at h
  simp [hu] at h

/-- **Time reversal of central-force motion.** If `γ = (q, p)` solves Hamilton's equations for
`H(q, p) = ‖p‖² / (2m) + U(‖q‖)` at time `-t`, off the collision set and with `U` differentiable
at `‖q‖`, then the reversed motion `s ↦ (q(-s), -p(-s))` solves them at time `t`. -/
theorem hasDerivAt_reverse_hamiltonianVectorField_centralForceHamiltonian {γ : ℝ → V × V}
    {t : ℝ}
    (hγ : HasDerivAt γ ((stdSymplecticForm (V := V)).hamiltonianVectorField
      (centralForceHamiltonian m U) (γ (-t))) (-t))
    (hq : (γ (-t)).1 ≠ 0) (hU : DifferentiableAt ℝ U ‖(γ (-t)).1‖) :
    HasDerivAt (fun s ↦ ((γ (-s)).1, -(γ (-s)).2))
      ((stdSymplecticForm (V := V)).hamiltonianVectorField (centralForceHamiltonian m U)
        ((γ (-t)).1, -(γ (-t)).2)) t := by
  rw [stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian hU.hasDerivAt hq] at hγ
  rw [stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian
    (x := ((γ (-t)).1, -(γ (-t)).2)) hU.hasDerivAt hq]
  have h := ((ContinuousLinearMap.id ℝ V).prodMap (-ContinuousLinearMap.id ℝ V)).hasFDerivAt
    |>.comp_hasDerivAt t (hγ.scomp t (hasDerivAt_neg t))
  exact h.congr_deriv (by ext <;> simp)

/-- **Motions with zero angular momentum stay on a ray.** Let `γ = (q, p)` solve Hamilton's
equations for `H(q, p) = ‖p‖² / (2m) + U(‖q‖)` on a preconnected set `s` of times, avoiding the
collision set, with `U` differentiable along it. If its squared angular momentum
`‖q‖² ‖p‖² - ⟪q, p⟫²` vanishes at one time `t₀ ∈ s`, then at every time `t ∈ s` the position lies
on the ray through `q(t₀)`. -/
theorem sameRay_fst_of_hasDerivAt {γ : ℝ → V × V} {s : Set ℝ} (hs : IsPreconnected s)
    (hγ : ∀ t ∈ s, HasDerivAt γ
      ((stdSymplecticForm (V := V)).hamiltonianVectorField (centralForceHamiltonian m U) (γ t)) t)
    (hq : ∀ t ∈ s, (γ t).1 ≠ 0) (hU : ∀ t ∈ s, DifferentiableAt ℝ U ‖(γ t).1‖) {t₀ t : ℝ}
    (ht₀ : t₀ ∈ s) (hℓ : ‖(γ t₀).1‖ ^ 2 * ‖(γ t₀).2‖ ^ 2 - ⟪(γ t₀).1, (γ t₀).2⟫_ℝ ^ 2 = 0)
    (ht : t ∈ s) :
    SameRay ℝ (γ t₀).1 (γ t).1 := by
  -- The direction `q / ‖q‖` has derivative `(‖q‖² p - ⟪q, p⟫ q) / (m ‖q‖³)`, which vanishes
  -- since the momentum is radial, `p = p_r (q / ‖q‖)`.
  have hd (u : ℝ) (hu : u ∈ s) :
      HasDerivAt (fun v ↦ ‖(γ v).1‖⁻¹ • (γ v).1) 0 u := by
    have hr : 0 < ‖(γ u).1‖ := norm_pos_iff.2 (hq u hu)
    have hρ := hasDerivAt_radialProjection_comp hs hγ hq hU ht₀ (ℓ := 0) (by rw [hℓ]; ring) u hu
    have h₁ := (hasDerivAt_fst_of_hasDerivAt_hamiltonianVectorField_effectivePotential hρ
      (by simpa [radialProjection_fst] using hr)
      (by simpa [radialProjection_fst] using hU u hu)).inv
      (by simpa [radialProjection_fst] using hr.ne')
    have h₂ := hγ u hu
    rw [stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian (hU u hu).hasDerivAt
      (hq u hu)] at h₂
    have h := h₁.smul ((hasFDerivAt_fst (𝕜 := ℝ) (p := γ u)).comp_hasDerivAt u h₂)
    have hp := (sq_sub_inner_sq_eq_zero_iff (hq u hu)).1
      ((sq_sub_inner_sq_eq_of_hasDerivAt hs hγ ht₀ hu).trans hℓ)
    simp only [Function.comp_def, radialProjection_fst, radialProjection_snd] at h
    convert h using 1
    rw [hp]
    simp only [Pi.inv_apply, ContinuousLinearMap.coe_fst', smul_smul, ← add_smul]
    convert (zero_smul ℝ (γ u).1).symm using 2
    field_simp
    ring
  -- So the direction is constant on `s`.
  have hsub := hs.ordConnected.uIcc_subset ht₀ ht
  have h := (convex_uIcc t₀ t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun v ↦ ‖(γ v).1‖⁻¹ • (γ v).1) (C := 0)
    (fun v hv ↦ (hd v (hsub hv)).hasDerivWithinAt) (fun _ _ ↦ by simp) left_mem_uIcc
    right_mem_uIcc
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at h
  exact (sameRay_iff_inv_norm_smul_eq_of_ne (hq t₀ ht₀) (hq t ht)).2 h.symm

/-- **Motions with zero angular momentum have momentum along their ray.** Under the hypotheses of
`TauCeti.sameRay_fst_of_hasDerivAt`, at every time `t ∈ s` the momentum is the radial momentum
times the unit vector `q(t₀) / ‖q(t₀)‖`. -/
theorem snd_eq_radialMomentum_smul_of_hasDerivAt {γ : ℝ → V × V} {s : Set ℝ}
    (hs : IsPreconnected s)
    (hγ : ∀ t ∈ s, HasDerivAt γ
      ((stdSymplecticForm (V := V)).hamiltonianVectorField (centralForceHamiltonian m U) (γ t)) t)
    (hq : ∀ t ∈ s, (γ t).1 ≠ 0) (hU : ∀ t ∈ s, DifferentiableAt ℝ U ‖(γ t).1‖) {t₀ t : ℝ}
    (ht₀ : t₀ ∈ s) (hℓ : ‖(γ t₀).1‖ ^ 2 * ‖(γ t₀).2‖ ^ 2 - ⟪(γ t₀).1, (γ t₀).2⟫_ℝ ^ 2 = 0)
    (ht : t ∈ s) :
    (γ t).2 = radialMomentum (γ t) • ‖(γ t₀).1‖⁻¹ • (γ t₀).1 := by
  rw [(sameRay_iff_inv_norm_smul_eq_of_ne (hq t₀ ht₀) (hq t ht)).1
    (sameRay_fst_of_hasDerivAt hs hγ hq hU ht₀ hℓ ht)]
  exact (sq_sub_inner_sq_eq_zero_iff (hq t ht)).1
    ((sq_sub_inner_sq_eq_of_hasDerivAt hs hγ ht₀ ht).trans hℓ)

end CentralForce

end TauCeti
