/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Integrable
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Radial
public import TauCeti.Geometry.Symplectic.Hamiltonian.Complete
import TauCeti.Analysis.Calculus.Deriv.Second
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Symplectic.Manifold.Opens

/-!
# Radial infall and collisions in attractive central forces

Let `V` be a finite-dimensional real inner product space, with phase space `V × V` and standard
symplectic form, and let `H(q, p) = ‖p‖² / (2m) + U(‖q‖)`, `m > 0`, be a central-force
Hamiltonian (`TauCeti.centralForceHamiltonian`). A motion with zero angular momentum,
`ℓ² = ‖q‖² ‖p‖² - ⟪q, p⟫² = 0`, is purely radial. Away from the collision set `q = 0` its radius
`r = ‖q‖` and radial momentum `p_r = ⟪q, p⟫ / ‖q‖` (`TauCeti.radialMomentum`) satisfy

`r' = p_r / m`,  `p_r' = -U'(r)`,

the reduced Hamilton equations of `TauCeti.hasDerivAt_radialProjection_comp` for `ℓ = 0`.
If the force is attractive with strength at least `a`, that is `U'(r) ≥ a` along the motion, then
`r'' ≤ -a / m`, so `r` lies below each of its osculating parabolas:

`r(t) ≤ r(τ) + p_r(τ) (t - τ) / m - a (t - τ)² / (2m)`

(`TauCeti.norm_fst_le_of_sq_sub_inner_sq_eq_zero`). This holds forwards and backwards in time
and for every real `a`; the attractive case is `a ≥ 0`. Since `r > 0` away from the collision
set, the motion can only exist on times `t` with

`a (t - τ)² / 2 - p_r(τ) (t - τ) < m r(τ)`

(`TauCeti.mul_sq_sub_radialMomentum_mul_lt_of_sq_sub_inner_sq_eq_zero`). For `a = 0`, a
non-repulsive force `U' ≥ 0`, a particle falling inwards with `p_r(τ) < 0` reaches the centre
before the time `τ + m r(τ) / (-p_r(τ))` at which it would arrive with constant velocity
(`TauCeti.lt_add_div_of_radialMomentum_neg`); the force only accelerates it.

If the force is strictly attractive, `U'(r) > 0` for all `r > 0`, then the radial momentum is
strictly decreasing, so it is negative at late times or positive at early times. Hence **no
radial motion exists for all times** in the punctured phase space: each one collides with the
centre in the future or came out of it in the past
(`TauCeti.not_forall_hasDerivAt_and_fst_ne_zero_of_sq_sub_inner_sq_eq_zero`); this includes the
motion released from rest. For a `C²` potential with `U' ≥ 0`, on a nonzero space, the
Hamiltonian vector field of `H` on the punctured phase space `{q ≠ 0}` is therefore **not
complete** (`TauCeti.not_isCompleteVectorField_hamiltonianVectorField_puncturedPhaseSpace`): a
particle thrown straight at the centre reaches it in finite time. This covers the free particle,
the attractive Kepler potential `-κ / r` and all attractive power laws.

Along the way, the energy is conserved along every motion avoiding the collision set
(`TauCeti.centralForceHamiltonian_eq_of_hasDerivAt`).

## Main results

* `TauCeti.centralForceHamiltonian_eq_of_hasDerivAt`: conservation of energy.
* `TauCeti.norm_fst_le_of_sq_sub_inner_sq_eq_zero`: the radius of a radial motion lies below its
  osculating parabola.
* `TauCeti.mul_sq_sub_radialMomentum_mul_lt_of_sq_sub_inner_sq_eq_zero`: the times at which a
  radial motion avoids the collision set.
* `TauCeti.lt_add_div_of_radialMomentum_neg`: an inward radial motion in a non-repulsive force
  collides before the constant-velocity arrival time.
* `TauCeti.not_forall_hasDerivAt_and_fst_ne_zero_of_sq_sub_inner_sq_eq_zero`: in a strictly
  attractive force no radial motion avoids the collision set for all times.
* `TauCeti.not_isCompleteVectorField_hamiltonianVectorField_puncturedPhaseSpace`: the Hamiltonian
  flow of a non-repulsive central force on the punctured phase space is not complete.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 8.
* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Addison-Wesley, 2002,
  Section 3.3.
-/

public section

open Set
open scoped InnerProductSpace Manifold

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {m : ℝ} {U : ℝ → ℝ} {γ : ℝ → V × V} {s : Set ℝ}

/-! ### Conservation of energy -/

/-- **Conservation of energy.** Let `γ` be an integral curve of the Hamiltonian vector field of a
central-force Hamiltonian `H` on a preconnected set `s` of times, avoiding the collision set, with
`U` differentiable along it. Then `H` takes the same value at all times `t₀, t ∈ s`. -/
theorem centralForceHamiltonian_eq_of_hasDerivAt (hs : IsPreconnected s)
    (hγ : ∀ t ∈ s, HasDerivAt γ
      ((stdSymplecticForm (V := V)).hamiltonianVectorField (centralForceHamiltonian m U) (γ t)) t)
    (hq : ∀ t ∈ s, (γ t).1 ≠ 0) (hU : ∀ t ∈ s, DifferentiableAt ℝ U ‖(γ t).1‖) {t₀ t : ℝ}
    (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    centralForceHamiltonian m U (γ t) = centralForceHamiltonian m U (γ t₀) := by
  -- The derivative of `H` along `γ` is `dH(X_H) = 0`.
  have hderiv (u : ℝ) (hu : u ∈ s) :
      HasDerivAt (centralForceHamiltonian m U ∘ γ) 0 u := by
    have hH := hasFDerivAt_centralForceHamiltonian (m := m) (hU u hu).hasDerivAt (hq u hu)
    have h := hH.comp_hasDerivAt u (hγ u hu)
    rwa [← hH.fderiv, SymplecticForm.fderiv_apply_hamiltonianVectorField] at h
  have h := (Real.convex_iff_isPreconnected.2 hs).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := centralForceHamiltonian m U ∘ γ) (f' := fun _ ↦ 0) (C := 0)
    (fun u hu ↦ (hderiv u hu).hasDerivWithinAt) (fun u _ ↦ by simp) ht₀ ht
  exact sub_eq_zero.1 (norm_le_zero_iff.1 (by simpa using h))

/-! ### Radial motions -/

/-- **The radial equations of a motion without angular momentum.** Along an integral curve of a
central-force Hamiltonian vector field on a preconnected set of times, avoiding the collision
set, with zero angular momentum at one time, the radius moves with velocity `r' = p_r / m` and the
radial momentum with velocity `p_r' = -U'(r)`. -/
private theorem hasDerivAt_norm_fst_and_radialMomentum (hs : IsPreconnected s)
    (hγ : ∀ t ∈ s, HasDerivAt γ
      ((stdSymplecticForm (V := V)).hamiltonianVectorField (centralForceHamiltonian m U) (γ t)) t)
    (hq : ∀ t ∈ s, (γ t).1 ≠ 0) (hU : ∀ t ∈ s, DifferentiableAt ℝ U ‖(γ t).1‖) {τ : ℝ}
    (hτ : τ ∈ s) (hℓ : ‖(γ τ).1‖ ^ 2 * ‖(γ τ).2‖ ^ 2 - ⟪(γ τ).1, (γ τ).2⟫_ℝ ^ 2 = 0) {t : ℝ}
    (ht : t ∈ s) :
    HasDerivAt (fun u ↦ ‖(γ u).1‖) (radialMomentum (γ t) / m) t ∧
      HasDerivAt (fun u ↦ radialMomentum (γ u)) (-deriv U ‖(γ t).1‖) t := by
  have h := hasDerivAt_radialProjection_comp (ℓ := 0) hs hγ hq hU hτ (by rw [hℓ]; norm_num) t ht
  have hx : radialProjection (γ t) = (‖(γ t).1‖, radialMomentum (γ t)) :=
    Prod.ext (radialProjection_fst _) (radialProjection_snd _)
  rw [hx, stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian_effectivePotential
      (hU t ht).hasDerivAt (norm_pos_iff.2 (hq t ht))] at h
  have hfst : (fun u ↦ ‖(γ u).1‖) = Prod.fst ∘ radialProjection ∘ γ :=
    funext fun u ↦ (radialProjection_fst (γ u)).symm
  have hsnd : (fun u ↦ radialMomentum (γ u)) = Prod.snd ∘ radialProjection ∘ γ :=
    funext fun u ↦ (radialProjection_snd (γ u)).symm
  rw [hfst, hsnd]
  refine ⟨?_, ?_⟩
  · exact ((hasFDerivAt_fst (𝕜 := ℝ) (p := radialProjection (γ t))).comp_hasDerivAt t h).congr_deriv
      rfl
  · refine ((hasFDerivAt_snd (𝕜 := ℝ) (p := radialProjection (γ t))).comp_hasDerivAt t
      h).congr_deriv ?_
    simp

/-- **A radial motion lies below its osculating parabolas.** Let `γ` be an integral curve of the
Hamiltonian vector field of a central-force Hamiltonian with mass `m ≥ 0` on a preconnected set `s`
of times, avoiding the collision set, with zero angular momentum at a time `τ ∈ s`. If the force
has strength at least `a` along `γ`, `U'(‖q‖) ≥ a`, then for every `t ∈ s`

`‖q(t)‖ ≤ ‖q(τ)‖ + p_r(τ) (t - τ) / m - a (t - τ)² / (2m)`.

For `a = 0` this says that the radius is a concave function of time, below its tangent lines. -/
theorem norm_fst_le_of_sq_sub_inner_sq_eq_zero (hm : 0 ≤ m) {a : ℝ} (hs : IsPreconnected s)
    (hγ : ∀ t ∈ s, HasDerivAt γ
      ((stdSymplecticForm (V := V)).hamiltonianVectorField (centralForceHamiltonian m U) (γ t)) t)
    (hq : ∀ t ∈ s, (γ t).1 ≠ 0) (hU : ∀ t ∈ s, DifferentiableAt ℝ U ‖(γ t).1‖)
    (ha : ∀ t ∈ s, a ≤ deriv U ‖(γ t).1‖) {τ : ℝ} (hτ : τ ∈ s)
    (hℓ : ‖(γ τ).1‖ ^ 2 * ‖(γ τ).2‖ ^ 2 - ⟪(γ τ).1, (γ τ).2⟫_ℝ ^ 2 = 0) {t : ℝ} (ht : t ∈ s) :
    ‖(γ t).1‖ ≤
      ‖(γ τ).1‖ + radialMomentum (γ τ) / m * (t - τ) - a / (2 * m) * (t - τ) ^ 2 := by
  -- The radius has second derivative `-U'(r) / m ≤ -a / m`.
  have h := le_add_mul_sub_add_div_two_mul_sq_of_hasDerivAt hs
    (f' := fun u ↦ radialMomentum (γ u) / m) (f'' := fun u ↦ -deriv U ‖(γ u).1‖ / m)
    (c := -a / m) (fun _ hu ↦ (hasDerivAt_norm_fst_and_radialMomentum hs hγ hq hU hτ hℓ hu).1)
    (fun _ hu ↦ (hasDerivAt_norm_fst_and_radialMomentum hs hγ hq hU hτ hℓ hu).2.div_const m)
    (fun u hu ↦ div_le_div_of_nonneg_right (neg_le_neg (ha u hu)) hm) hτ ht
  have hc : -a / m / 2 * (t - τ) ^ 2 = -(a / (2 * m) * (t - τ) ^ 2) := by ring
  linarith

/-- **The lifetime of a radial motion.** Under the hypotheses of
`TauCeti.norm_fst_le_of_sq_sub_inner_sq_eq_zero`, every time `t ∈ s` satisfies

`a (t - τ)² / 2 - p_r(τ) (t - τ) < m ‖q(τ)‖`.

For `a > 0` this confines `s` to a bounded interval around `τ`: a radial motion in a force of
strength at least `a` collides with the centre in finite time in both directions. -/
theorem mul_sq_sub_radialMomentum_mul_lt_of_sq_sub_inner_sq_eq_zero (hm : 0 < m) {a : ℝ}
    (hs : IsPreconnected s)
    (hγ : ∀ t ∈ s, HasDerivAt γ
      ((stdSymplecticForm (V := V)).hamiltonianVectorField (centralForceHamiltonian m U) (γ t)) t)
    (hq : ∀ t ∈ s, (γ t).1 ≠ 0) (hU : ∀ t ∈ s, DifferentiableAt ℝ U ‖(γ t).1‖)
    (ha : ∀ t ∈ s, a ≤ deriv U ‖(γ t).1‖) {τ : ℝ} (hτ : τ ∈ s)
    (hℓ : ‖(γ τ).1‖ ^ 2 * ‖(γ τ).2‖ ^ 2 - ⟪(γ τ).1, (γ τ).2⟫_ℝ ^ 2 = 0) {t : ℝ} (ht : t ∈ s) :
    a / 2 * (t - τ) ^ 2 - radialMomentum (γ τ) * (t - τ) < m * ‖(γ τ).1‖ := by
  have h := norm_fst_le_of_sq_sub_inner_sq_eq_zero hm.le hs hγ hq hU ha hτ hℓ ht
  have hpos : 0 < ‖(γ t).1‖ := norm_pos_iff.2 (hq t ht)
  have hm' : m * (radialMomentum (γ τ) / m * (t - τ) - a / (2 * m) * (t - τ) ^ 2) =
      radialMomentum (γ τ) * (t - τ) - a / 2 * (t - τ) ^ 2 := by
    field_simp
  nlinarith

/-- **Inward radial motions in a non-repulsive force collide.** Let `γ` be an integral curve of
the Hamiltonian vector field of a central-force Hamiltonian with mass `m > 0` on a preconnected
set `s` of times, avoiding the collision set, with `U' ≥ 0` along it and zero angular momentum at
a time `τ ∈ s` at which the particle moves inwards, `p_r(τ) < 0`. Then every time `t ∈ s` is
earlier than `τ + m ‖q(τ)‖ / (-p_r(τ))`, the time at which the particle would reach the centre
with constant velocity. -/
theorem lt_add_div_of_radialMomentum_neg (hm : 0 < m) (hs : IsPreconnected s)
    (hγ : ∀ t ∈ s, HasDerivAt γ
      ((stdSymplecticForm (V := V)).hamiltonianVectorField (centralForceHamiltonian m U) (γ t)) t)
    (hq : ∀ t ∈ s, (γ t).1 ≠ 0) (hU : ∀ t ∈ s, DifferentiableAt ℝ U ‖(γ t).1‖)
    (hU' : ∀ t ∈ s, 0 ≤ deriv U ‖(γ t).1‖) {τ : ℝ} (hτ : τ ∈ s)
    (hℓ : ‖(γ τ).1‖ ^ 2 * ‖(γ τ).2‖ ^ 2 - ⟪(γ τ).1, (γ τ).2⟫_ℝ ^ 2 = 0)
    (hp : radialMomentum (γ τ) < 0) {t : ℝ} (ht : t ∈ s) :
    t < τ + m * ‖(γ τ).1‖ / -radialMomentum (γ τ) := by
  have h := mul_sq_sub_radialMomentum_mul_lt_of_sq_sub_inner_sq_eq_zero hm hs hγ hq hU hU' hτ hℓ ht
  rw [← sub_lt_iff_lt_add', lt_div_iff₀ (neg_pos.2 hp)]
  nlinarith

/-- **No radial motion in a strictly attractive force lasts forever.** For a mass `m > 0` and a
potential with `U'(r) > 0` for all `r > 0`, there is no curve `γ` defined for all times which
avoids the collision set, solves Hamilton's equations of the central-force Hamiltonian, and has
zero angular momentum at time `0`. Such a motion collides with the centre in the future or came
out of it in the past. -/
theorem not_forall_hasDerivAt_and_fst_ne_zero_of_sq_sub_inner_sq_eq_zero (hm : 0 < m)
    (hU' : ∀ r, 0 < r → 0 < deriv U r)
    (hℓ : ‖(γ 0).1‖ ^ 2 * ‖(γ 0).2‖ ^ 2 - ⟪(γ 0).1, (γ 0).2⟫_ℝ ^ 2 = 0) :
    ¬ ∀ t, HasDerivAt γ
      ((stdSymplecticForm (V := V)).hamiltonianVectorField (centralForceHamiltonian m U) (γ t)) t ∧
        (γ t).1 ≠ 0 := by
  intro h
  have hs : IsPreconnected (univ : Set ℝ) := isPreconnected_univ
  have hγ : ∀ t ∈ univ, HasDerivAt γ
      ((stdSymplecticForm (V := V)).hamiltonianVectorField (centralForceHamiltonian m U) (γ t)) t :=
    fun t _ ↦ (h t).1
  have hq : ∀ t ∈ univ, (γ t).1 ≠ 0 := fun t _ ↦ (h t).2
  have hr (t : ℝ) : 0 < ‖(γ t).1‖ := norm_pos_iff.2 (h t).2
  have hUγ : ∀ t ∈ univ, DifferentiableAt ℝ U ‖(γ t).1‖ :=
    fun t _ ↦ differentiableAt_of_deriv_ne_zero (hU' _ (hr t)).ne'
  have hU'γ : ∀ t ∈ univ, (0 : ℝ) ≤ deriv U ‖(γ t).1‖ := fun t _ ↦ (hU' _ (hr t)).le
  -- The angular momentum vanishes at every time, and the radial momentum strictly decreases.
  have hℓ' (τ : ℝ) :
      ‖(γ τ).1‖ ^ 2 * ‖(γ τ).2‖ ^ 2 - ⟪(γ τ).1, (γ τ).2⟫_ℝ ^ 2 = 0 := by
    rw [sq_sub_inner_sq_eq_of_hasDerivAt hs hγ (mem_univ 0) (mem_univ τ), hℓ]
  have hanti : StrictAnti fun t ↦ radialMomentum (γ t) :=
    strictAnti_of_hasDerivAt_neg
      (fun t ↦ (hasDerivAt_norm_fst_and_radialMomentum hs hγ hq hUγ (mem_univ 0) hℓ
        (mem_univ t)).2) fun t ↦ neg_neg_of_pos (hU' _ (hr t))
  -- At time `τ`, the bound of the lifetime fails at the time `t` of constant-velocity arrival.
  have key (τ t : ℝ) : -radialMomentum (γ τ) * (t - τ) < m * ‖(γ τ).1‖ := by
    simpa using mul_sq_sub_radialMomentum_mul_lt_of_sq_sub_inner_sq_eq_zero hm hs hγ hq hUγ hU'γ
      (mem_univ τ) (hℓ' τ) (mem_univ t)
  rcases le_or_gt (radialMomentum (γ 0)) 0 with h0 | h0
  · -- Moving inwards after time `1`: the particle reaches the centre in the future.
    have h1 : radialMomentum (γ 1) < 0 := (hanti zero_lt_one).trans_le h0
    have := key 1 (1 + m * ‖(γ 1).1‖ / -radialMomentum (γ 1))
    rw [add_sub_cancel_left, mul_div_cancel₀ _ (neg_ne_zero.2 h1.ne)] at this
    exact lt_irrefl _ this
  · -- Moving outwards before time `-1`: the particle came out of the centre in the past.
    have h1 : 0 < radialMomentum (γ (-1)) := h0.trans (hanti (neg_lt_zero.2 zero_lt_one))
    have := key (-1) (-1 - m * ‖(γ (-1)).1‖ / radialMomentum (γ (-1)))
    rw [sub_sub_cancel_left, neg_mul_neg, mul_div_cancel₀ _ h1.ne'] at this
    exact lt_irrefl _ this

/-! ### Incompleteness of the flow on the punctured phase space -/

/-- **Collisions make the flow of a non-repulsive central force incomplete.** For a mass `m > 0`
and a potential `U` which is `C²` on `r > 0` with `U'(r) ≥ 0` there, on a nonzero space `V`, the
Hamiltonian vector field of `H(q, p) = ‖p‖² / (2m) + U(‖q‖)` on the punctured phase space
`{(q, p) | q ≠ 0}`, with the restriction of the standard symplectic form, is not complete. Indeed,
a particle thrown straight at the centre from any point `q ≠ 0`, with momentum `-q`, has zero
angular momentum and moves inwards, so it reaches the centre in finite time. This includes the
free particle `U = 0`. -/
theorem not_isCompleteVectorField_hamiltonianVectorField_puncturedPhaseSpace [Nontrivial V]
    (hm : 0 < m) (hU : ContDiffOn ℝ 2 U (Ioi 0)) (hU' : ∀ r, 0 < r → 0 ≤ deriv U r) :
    ¬ IsCompleteVectorField (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V)
        contMDiff_subtype_val (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m U ∘ Subtype.val)) := by
  intro hcomplete
  have hσ := (SymplecticForm.isNondegenerate_constSmooth
    (stdSymplecticForm (V := V))).mpullback_subtype_val (puncturedPhaseSpace V)
  have hUat (x : V × V) (hq : x.1 ≠ 0) : ContDiffAt ℝ 2 U ‖x.1‖ :=
    hU.contDiffAt (Ioi_mem_nhds (norm_pos_iff.2 hq))
  -- The Hamiltonian is `C²` on the punctured phase space.
  have hH : ContMDiff 𝓘(ℝ, V × V) 𝓘(ℝ) 2
      (centralForceHamiltonian m U ∘ (Subtype.val : puncturedPhaseSpace V → V × V)) := by
    have hHfun : centralForceHamiltonian m U = fun y : V × V ↦ ‖y.2‖ ^ 2 / (2 * m) + U ‖y.1‖ :=
      funext fun y ↦ centralForceHamiltonian_apply m U y.1 y.2
    refine fun x ↦ ContMDiffAt.comp x (ContDiffAt.contMDiffAt ?_) (contMDiff_subtype_val x)
    have hq := mem_puncturedPhaseSpace.1 x.2
    rw [hHfun]
    exact (((contDiff_norm_sq ℝ).comp contDiff_snd).contDiffAt.div_const _).add
      ((hUat _ hq).comp (x : V × V) ((contDiffAt_norm ℝ hq).comp (x : V × V) contDiffAt_fst))
  -- The particle thrown from a point `q ≠ 0` with momentum `-q` has a global integral curve.
  obtain ⟨q, hq⟩ := exists_ne (0 : V)
  obtain ⟨γ, hγ0, hγ⟩ := hcomplete.exists_isMIntegralCurve
    (hσ.contMDiff_hamiltonianVectorField (n := 1) (by simp) (by rwa [one_add_one_eq_two]))
    (⟨(q, -q), mem_puncturedPhaseSpace.2 hq⟩ : puncturedPhaseSpace V)
  -- Its image in `V × V` solves Hamilton's equations of the linear theory.
  have hmap := (hγ.isMIntegralCurveOn univ).map_of_mfderiv_eq (I' := 𝓘(ℝ, V × V))
    (W := fun x ↦ (stdSymplecticForm (V := V)).hamiltonianVectorField
      (centralForceHamiltonian m U) x)
    (fun t _ ↦ contMDiff_subtype_val.mdifferentiableAt one_ne_zero)
    fun t _ ↦ by
      rw [SmoothTwoForm.hamiltonianVectorField_comp_subtype_val, Manifold.mfderiv_subtype_val,
        SymplecticForm.hamiltonianVectorField_constSmooth]
      exact ContinuousLinearEquiv.apply_symm_apply _ _
  replace hmap := TauCeti.isMIntegralCurveOn_iff_isIntegralCurveOn.1 hmap
  have hq' : ∀ t ∈ univ, ((Subtype.val ∘ γ) t).1 ≠ 0 :=
    fun t _ ↦ mem_puncturedPhaseSpace.1 (γ t).2
  have hr (t : ℝ) : 0 < ‖((Subtype.val ∘ γ) t).1‖ := norm_pos_iff.2 (hq' t (mem_univ t))
  have hp : radialMomentum ((Subtype.val ∘ γ) 0) = -‖q‖ := by
    rw [Function.comp_apply, hγ0, radialMomentum_apply, inner_neg_right,
      real_inner_self_eq_norm_sq, neg_div, sq, mul_div_cancel_right₀ _ (norm_ne_zero_iff.2 hq)]
  -- Thrown inwards, the particle cannot outlive its constant-velocity arrival time.
  have h := lt_add_div_of_radialMomentum_neg hm isPreconnected_univ
    (fun t _ ↦ (hmap t (mem_univ t)).hasDerivAt Filter.univ_mem) hq'
    (fun t _ ↦ (hU.differentiableOn two_ne_zero _ (hr t)).differentiableAt (Ioi_mem_nhds (hr t)))
    (fun t _ ↦ hU' _ (hr t)) (mem_univ 0) (by simp [hγ0]; ring)
    (by rw [hp]; exact neg_neg_of_pos (norm_pos_iff.2 hq))
    (mem_univ (0 + m * ‖((Subtype.val ∘ γ) 0).1‖ / -radialMomentum ((Subtype.val ∘ γ) 0)))
  exact lt_irrefl _ h

end TauCeti
