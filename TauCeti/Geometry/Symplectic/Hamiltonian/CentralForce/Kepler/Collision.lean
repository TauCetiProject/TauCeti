/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Collision
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Torus

/-!
# The collision orbits of the Kepler problem

A particle of mass `m > 0` in the attractive Kepler potential `-κ / r`, `κ > 0`, has the energy
`H(q, p) = ‖p‖² / (2m) - κ / ‖q‖`. This file determines which Kepler motions fall into the
collision set `q = 0`.

* **Zero angular momentum.** The Kepler potential is attractive, so a Kepler motion with zero
  angular momentum `ℓ² = ‖q‖² ‖p‖² - ⟪q, p⟫² = 0` cannot avoid collision at all times
  (`TauCeti.sq_sub_inner_sq_ne_zero_of_forall_hasDerivAt`). Hence the Kepler flow on the punctured
  phase space `{(q, p) | q ≠ 0}` is not complete as soon as `V ≠ 0`
  (`TauCeti.not_isCompleteVectorField_hamiltonianVectorField_puncturedPhaseSpace_kepler`).
* **Bound radial motions collide in the future.** A Kepler motion with zero angular momentum and
  negative energy `E` stays in the ball `‖q‖ ≤ κ / (-E)`, where the attraction `κ / ‖q‖²` is at
  least `E² / κ`. So its radial momentum decreases at a definite rate and eventually becomes
  negative, after which the motion cannot avoid collision. Equivalently, a Kepler motion with zero
  angular momentum that avoids collision at all later times has nonnegative energy
  (`TauCeti.centralForceHamiltonian_kepler_nonneg_of_forall_hasDerivAt`, and its reduced form
  `TauCeti.centralForceHamiltonian_effectivePotential_kepler_nonneg_of_forall_hasDerivAt`).
* **The collision orbits of negative energy.** In the plane, with angular momentum
  `L = q₁p₂ - q₂p₁` in an orthonormal basis `b`, a state of negative energy off the collision set
  lies on a Kepler motion avoiding collision at all times exactly when `L ≠ 0`
  (`TauCeti.exists_forall_hasDerivAt_kepler_iff_angularMomentum_ne_zero`). Its motion is then
  defined at all times by the completeness of the Kepler flow on the bound phase space
  (`TauCeti.isCompleteVectorField_hamiltonianVectorField_keplerBoundPhaseSpace`). So among the
  states of negative energy, the collision orbits are exactly those with `L = 0`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 8.
* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Addison-Wesley, 2002,
  Section 3.7.
-/

public section

open Set
open scoped InnerProductSpace Manifold ContDiff

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {m κ : ℝ}

/-- **The Kepler flow is not complete.** Let `V ≠ 0`, `m > 0` and `κ > 0`. On the punctured phase
space `{(q, p) | q ≠ 0}`, the Hamiltonian vector field of the Kepler Hamiltonian
`H(q, p) = ‖p‖² / (2m) - κ / ‖q‖` is not complete: no Kepler motion with zero angular momentum
avoids the collision set at all times. -/
theorem not_isCompleteVectorField_hamiltonianVectorField_puncturedPhaseSpace_kepler [Nontrivial V]
    (hm : 0 < m) (hκ : 0 < κ) :
    ¬ IsCompleteVectorField (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) :=
  not_isCompleteVectorField_hamiltonianVectorField_puncturedPhaseSpace hm
    (contDiffOn_const.div contDiffOn_id fun _ hr ↦ (mem_Ioi.1 hr).ne')
    fun _ hr ↦ by rw [(hasDerivAt_kepler_potential κ hr.ne').deriv]; positivity

/-- **Radial Kepler motions of negative energy are bounded.** Let `m, κ > 0`, and let
`ρ = (r, p_r)` be an integral curve, on the times between `a` and `t`, of the reduced Hamiltonian
vector field of `H_0(r, p_r) = p_r² / (2m) - κ / r`, staying in the half-line `r > 0`. If its
energy `E = H_0(ρ(a))` is negative, then `r(t) ≤ κ / (-E)`. -/
private theorem fst_le_div_neg_of_hasDerivAt_kepler (hm : 0 < m) {ρ : ℝ → ℝ × ℝ} {a t : ℝ}
    (hρ : ∀ s ∈ Icc a t, HasDerivAt ρ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
      (centralForceHamiltonian m (effectivePotential m 0 fun r ↦ -κ / r)) (ρ s)) s)
    (hr : ∀ s ∈ Icc a t, 0 < (ρ s).1) (ht : a ≤ t)
    (hE : centralForceHamiltonian m (effectivePotential m 0 fun r ↦ -κ / r) (ρ a) < 0) :
    (ρ t).1 ≤ κ / -centralForceHamiltonian m (effectivePotential m 0 fun r ↦ -κ / r) (ρ a) := by
  -- By conservation of energy, `-κ / r(t) ≤ p_r(t)² / (2m) - κ / r(t) = E`.
  have hcons := centralForceHamiltonian_effectivePotential_eq_of_hasDerivAt hρ hr
    (fun s hs ↦ (hasDerivAt_kepler_potential κ (hr s hs).ne').differentiableAt) t ⟨ht, le_rfl⟩
  have hrt := hr t ⟨ht, le_rfl⟩
  rw [← Prod.mk.eta (p := ρ t), centralForceHamiltonian_effectivePotential_apply hrt.le] at hcons
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    add_zero] at hcons
  have hp : 0 ≤ (ρ t).2 ^ 2 / (2 * m) := by positivity
  have hmul : -κ / (ρ t).1 * (ρ t).1 ≤
      centralForceHamiltonian m (effectivePotential m 0 fun r ↦ -κ / r) (ρ a) * (ρ t).1 :=
    mul_le_mul_of_nonneg_right (by linarith) hrt.le
  rw [div_mul_cancel₀ _ hrt.ne'] at hmul
  rw [le_div_iff₀ (neg_pos.2 hE)]
  linarith

/-- **Bound radial Kepler motions collide, reduced form.** Let `m, κ > 0`, and let
`ρ = (r, p_r)` be an integral curve, at all times `t ≥ a`, of the reduced Hamiltonian vector field
of the Kepler motion with zero angular momentum, `H_0(r, p_r) = p_r² / (2m) - κ / r`, staying in
the half-line `r > 0`. Then its energy is nonnegative. -/
theorem centralForceHamiltonian_effectivePotential_kepler_nonneg_of_forall_hasDerivAt
    (hm : 0 < m) (hκ : 0 < κ) {ρ : ℝ → ℝ × ℝ} {a : ℝ}
    (hρ : ∀ t ∈ Ici a, HasDerivAt ρ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
      (centralForceHamiltonian m (effectivePotential m 0 fun r ↦ -κ / r)) (ρ t)) t)
    (hr : ∀ t ∈ Ici a, 0 < (ρ t).1) :
    0 ≤ centralForceHamiltonian m (effectivePotential m 0 fun r ↦ -κ / r) (ρ a) := by
  by_contra! hE
  have hU (t : ℝ) (ht : t ∈ Ici a) :=
    hasDerivAt_kepler_potential κ (hr t ht).ne'
  have hp' (t : ℝ) (ht : t ∈ Ici a) :=
    hasDerivAt_snd_of_hasDerivAt_hamiltonianVectorField_effectivePotential (hρ t ht) (hr t ht)
      (hU t ht).differentiableAt
  -- On the ball `r ≤ R = κ / (-E)`, the radial momentum has derivative `-κ / r² ≤ -c` for
  -- `c = κ / R² > 0`.
  set c := κ / (κ / -centralForceHamiltonian m (effectivePotential m 0 fun r ↦ -κ / r) (ρ a)) ^ 2
  have hc : 0 < c := by have := neg_pos.2 hE; positivity
  have hle := (convex_Ici a).image_sub_le_mul_sub_of_deriv_le (f := fun s ↦ (ρ s).2) (C := -c)
    (fun t ht ↦ (hp' t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hp' t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ by
      have ht' : t ∈ Ici a := interior_subset ht
      rw [(hp' t ht').deriv, (hU t ht').deriv]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, zero_sub,
        neg_le_neg_iff, c]
      exact div_le_div_of_nonneg_left hκ.le (pow_pos (hr t ht') 2)
        (pow_le_pow_left₀ (hr t ht').le (fst_le_div_neg_of_hasDerivAt_kepler hm
          (fun s hs ↦ hρ s hs.1) (fun s hs ↦ hr s hs.1) ht' hE) 2))
  -- Hence the radial momentum is negative at time `T = a + (|p_r(a)| + 1) / c`, whereas a
  -- motion avoiding collision at all times after `T` has nonnegative radial momentum at `T`.
  set T := a + (|(ρ a).2| + 1) / c
  have hT : T ∈ Ici a := le_add_of_nonneg_right (by positivity)
  have hnonneg := snd_nonneg_of_forall_hasDerivAt_hamiltonianVectorField_effectivePotential hm
    (a := T) (fun t ht ↦ hρ t (hT.trans ht)) (fun t ht ↦ hr t (hT.trans ht))
    (fun t ht ↦ (hU t (hT.trans ht)).differentiableAt) fun t ht ↦ by
      rw [(hU t (hT.trans ht)).deriv]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
      exact div_nonneg hκ.le (sq_nonneg _)
  have hTa := hle a self_mem_Ici T hT hT
  have hcT : -c * (T - a) = -(|(ρ a).2| + 1) := by
    simp only [T, add_sub_cancel_left]
    field_simp
  linarith [le_abs_self (ρ a).2]

/-- **Bound radial Kepler motions collide.** Let `m, κ > 0`, and let `γ` be a solution of
Hamilton's equations for the Kepler Hamiltonian `H(q, p) = ‖p‖² / (2m) - κ / ‖q‖` at all times
`t ≥ a`, avoiding the collision set, with zero angular momentum `‖q‖² ‖p‖² - ⟪q, p⟫² = 0` at time
`a`. Then its energy is nonnegative: a Kepler motion with zero angular momentum and negative energy
cannot avoid the collision set at all later times. -/
theorem centralForceHamiltonian_kepler_nonneg_of_forall_hasDerivAt (hm : 0 < m) (hκ : 0 < κ)
    {γ : ℝ → V × V} {a : ℝ}
    (hγ : ∀ t ∈ Ici a, HasDerivAt γ ((stdSymplecticForm (V := V)).hamiltonianVectorField
      (centralForceHamiltonian m (fun r ↦ -κ / r)) (γ t)) t)
    (hq : ∀ t ∈ Ici a, (γ t).1 ≠ 0)
    (hℓ : ‖(γ a).1‖ ^ 2 * ‖(γ a).2‖ ^ 2 - ⟪(γ a).1, (γ a).2⟫_ℝ ^ 2 = 0) :
    0 ≤ centralForceHamiltonian m (fun r ↦ -κ / r) (γ a) := by
  -- The radial projection `(‖q‖, p_r)` of `γ` is a radial motion with `ℓ = 0`, of the same energy.
  have h := centralForceHamiltonian_effectivePotential_kepler_nonneg_of_forall_hasDerivAt hm hκ
    (ρ := fun s ↦ radialProjection (γ s)) (a := a)
    (hasDerivAt_radialProjection_comp isPreconnected_Ici hγ hq
      (fun t ht ↦ (hasDerivAt_kepler_potential κ (norm_ne_zero_iff.2 (hq t ht))).differentiableAt)
      self_mem_Ici (by rw [hℓ]; ring))
    fun t ht ↦ by simpa [radialProjection_fst] using hq t ht
  rwa [centralForceHamiltonian_radialProjection (hq a self_mem_Ici) (by rw [hℓ]; ring)] at h

/-- **The collision orbits of negative Kepler energy.** Let `m, κ > 0`, and let `L = q₁p₂ - q₂p₁`
be the angular momentum in an orthonormal basis `b` of the plane `V`. A state `x` off the collision
set with negative Kepler energy `H(x) = ‖p‖² / (2m) - κ / ‖q‖ < 0` lies on a solution of
Hamilton's equations defined and avoiding the collision set at all times exactly when its angular
momentum is nonzero. -/
theorem exists_forall_hasDerivAt_kepler_iff_angularMomentum_ne_zero
    (b : OrthonormalBasis (Fin 2) ℝ V) (hm : 0 < m) (hκ : 0 < κ) {x : V × V} (hq : x.1 ≠ 0)
    (hE : centralForceHamiltonian m (fun r ↦ -κ / r) x < 0) :
    (∃ γ : ℝ → V × V, γ 0 = x ∧ ∀ t, (γ t).1 ≠ 0 ∧ HasDerivAt γ
        ((stdSymplecticForm (V := V)).hamiltonianVectorField
          (centralForceHamiltonian m (fun r ↦ -κ / r)) (γ t)) t) ↔
      angularMomentum (b 0) (b 1) x ≠ 0 := by
  constructor
  · rintro ⟨γ, rfl, hγ⟩
    -- A global noncollision motion in the attractive Kepler potential has `L² = ℓ² ≠ 0`.
    have h := sq_sub_inner_sq_ne_zero_of_forall_hasDerivAt hm (fun t ↦ (hγ t).2)
      (fun t ↦ (hγ t).1)
      (fun t ↦ (hasDerivAt_kepler_potential κ (norm_ne_zero_iff.2 (hγ t).1)).differentiableAt)
      (fun t ↦ by
        rw [(hasDerivAt_kepler_potential κ (norm_ne_zero_iff.2 (hγ t).1)).deriv]
        exact div_pos hκ (pow_pos (norm_pos_iff.2 (hγ t).1) 2)) 0
    rw [← sq_angularMomentum b] at h
    exact pow_ne_zero_iff (n := 2) two_ne_zero |>.1 h
  · intro hL
    -- The state lies in the bound phase space, on which the energy flow is complete.
    have hcomplete := isCompleteVectorField_hamiltonianVectorField_keplerBoundPhaseSpace b hm hκ 0
    have hH := contMDiff_pi_module_iff.1
      (contMDiff_centralForceEnergyMomentum_keplerBoundPhaseSpace b (m := m) (κ := κ)) 0
    rw [show (fun y : keplerBoundPhaseSpace b m κ ↦
        (centralForceEnergyMomentum b m (fun r ↦ -κ / r) ∘ Subtype.val) y 0) =
          centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val from
        funext fun y ↦ centralForceEnergyMomentum_zero b m _ _] at hcomplete hH
    obtain ⟨γ, hγ₀, hγ⟩ := SymplecticForm.exists_forall_hasDerivAt_of_isCompleteVectorField _
      (hH.of_le (by simp)) hcomplete ((mem_keplerBoundPhaseSpace b).2 ⟨hq, hE, hL⟩)
    exact ⟨γ, hγ₀, fun t ↦ ⟨((mem_keplerBoundPhaseSpace b).1 (hγ t).1).1, (hγ t).2⟩⟩

end TauCeti
