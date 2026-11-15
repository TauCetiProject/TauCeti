/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Collision

/-!
# The collision domain of the Kepler problem

A particle of mass `m > 0` moving in the attractive Kepler potential `-κ / r`, `κ > 0`, has the
energy `H(q, p) = ‖p‖² / (2m) - κ / ‖q‖` on the punctured phase space `{(q, p) | q ≠ 0}`, where
the potential is smooth. Its motions split according to the squared angular momentum
`ℓ² = ‖q‖² ‖p‖² - ⟪q, p⟫²`, which is conserved:

* **Zero angular momentum: collision.** A motion with `ℓ = 0` is radial, and the Kepler force
  `κ / r²` is strictly attractive, so the motion collides with the centre in the future or came
  out of it in the past
  (`TauCeti.not_forall_hasDerivAt_and_fst_ne_zero_of_sq_sub_inner_sq_eq_zero`).
  At negative energy `E` it does both: the radius is at most `κ / (-E)`, so the force is at least
  `E² / κ`, and the radius lies below a downward parabola in time. Hence the set of times on
  which a radial motion of negative energy avoids the collision set is bounded
  (`TauCeti.isBounded_of_hasDerivAt_kepler_of_centralForceHamiltonian_neg`).
* **Nonzero angular momentum: no collision.** The length of the Runge–Lenz vector `A` is
  conserved (`TauCeti.norm_rungeLenz_eq_of_hasDerivAt_kepler`), and at every point
  `ℓ² ≤ ‖q‖ (m κ + ‖A‖)`. So a motion with `ℓ ≠ 0` stays at distance at least
  `ℓ² / (m κ + ‖A‖) > 0` from the centre, the pericentre distance of its conic
  (`TauCeti.sq_sub_inner_sq_div_le_norm_fst_of_hasDerivAt_kepler`,
  `TauCeti.exists_pos_forall_le_norm_fst_of_hasDerivAt_kepler`).

Consequently the Kepler flow on the punctured phase space is not complete
(`TauCeti.not_isCompleteVectorField_hamiltonianVectorField_puncturedPhaseSpace_kepler`), in
contrast with its completeness on the bound phase space of negative energy and nonzero angular
momentum (`TauCeti.isCompleteVectorField_hamiltonianVectorField_keplerBoundPhaseSpace`).

## Main results

* `TauCeti.isBounded_of_hasDerivAt_kepler_of_centralForceHamiltonian_neg`: a radial Kepler motion
  of negative energy exists only for a bounded set of times.
* `TauCeti.norm_rungeLenz_eq_of_hasDerivAt_kepler`: conservation of `‖A‖`.
* `TauCeti.sq_sub_inner_sq_div_le_norm_fst_of_hasDerivAt_kepler`: the pericentre bound
  `ℓ² / (m κ + ‖A‖) ≤ ‖q‖` along a motion.
* `TauCeti.exists_pos_forall_le_norm_fst_of_hasDerivAt_kepler`: a motion with nonzero angular
  momentum stays a positive distance away from the collision set.
* `TauCeti.not_isCompleteVectorField_hamiltonianVectorField_puncturedPhaseSpace_kepler`: the
  Kepler flow on the punctured phase space is not complete.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 8.
* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Addison-Wesley, 2002,
  Sections 3.7–3.9.
-/

public section

open Set
open scoped InnerProductSpace Manifold

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {m κ : ℝ} {γ : ℝ → V × V} {s : Set ℝ}

/-- The Kepler potential `-κ / r` is differentiable at every nonzero radius. -/
private theorem differentiableAt_kepler_potential (κ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    DifferentiableAt ℝ (fun r ↦ -κ / r) r :=
  (hasDerivAt_kepler_potential κ hr).differentiableAt

/-! ### Radial motions of negative energy -/

/-- **Radial Kepler motions of negative energy collide in both directions of time.** For `m > 0`,
let `γ` be an integral curve of the Kepler Hamiltonian vector field on a preconnected set `s` of
times, avoiding the collision set, with zero angular momentum and negative energy at a time
`τ ∈ s`. Then `s` is bounded: the particle falls into the centre in finite time, and it came out of
the centre a finite time ago. -/
theorem isBounded_of_hasDerivAt_kepler_of_centralForceHamiltonian_neg (hm : 0 < m)
    (hs : IsPreconnected s)
    (hγ : ∀ t ∈ s, HasDerivAt γ ((stdSymplecticForm (V := V)).hamiltonianVectorField
      (centralForceHamiltonian m (fun r ↦ -κ / r)) (γ t)) t)
    (hq : ∀ t ∈ s, (γ t).1 ≠ 0) {τ : ℝ} (hτ : τ ∈ s)
    (hℓ : ‖(γ τ).1‖ ^ 2 * ‖(γ τ).2‖ ^ 2 - ⟪(γ τ).1, (γ τ).2⟫_ℝ ^ 2 = 0)
    (hE : centralForceHamiltonian m (fun r ↦ -κ / r) (γ τ) < 0) : Bornology.IsBounded s := by
  set E := centralForceHamiltonian m (fun r ↦ -κ / r) (γ τ) with hEdef
  have hr (t : ℝ) (ht : t ∈ s) : 0 < ‖(γ t).1‖ := norm_pos_iff.2 (hq t ht)
  have hU : ∀ t ∈ s, DifferentiableAt ℝ (fun r ↦ -κ / r) ‖(γ t).1‖ :=
    fun t ht ↦ differentiableAt_kepler_potential κ (hr t ht).ne'
  -- Negative energy forces an attractive coupling.
  have hκ : 0 < κ := by
    have hp : 0 ≤ ‖(γ τ).2‖ ^ 2 / (2 * m) := by positivity
    have hE' : ‖(γ τ).2‖ ^ 2 / (2 * m) + -κ / ‖(γ τ).1‖ < 0 := by
      rwa [hEdef, ← Prod.mk.eta (p := γ τ), centralForceHamiltonian_apply] at hE
    have : 0 < κ / ‖(γ τ).1‖ := by rw [neg_div] at hE'; linarith
    exact (div_pos_iff_of_pos_right (hr τ hτ)).1 this
  -- The energy is conserved, so the radius stays below `κ / (-E)` and the force above `E² / κ`.
  have hforce : ∀ t ∈ s, E ^ 2 / κ ≤ deriv (fun r ↦ -κ / r) ‖(γ t).1‖ := by
    intro t ht
    have hEt : centralForceHamiltonian m (fun r ↦ -κ / r) (γ t) = E :=
      centralForceHamiltonian_eq_of_hasDerivAt hs hγ hq hU hτ ht
    have hle := norm_fst_le_div_neg_centralForceHamiltonian hm.le (hEt.trans_lt hE)
    rw [hEt] at hle
    rw [(hasDerivAt_kepler_potential κ (hr t ht).ne').deriv, div_le_div_iff₀ hκ (by
      have := hr t ht; positivity)]
    have h1 : ‖(γ t).1‖ * -E ≤ κ := by rwa [le_div_iff₀ (neg_pos.2 hE)] at hle
    have h2 : 0 ≤ ‖(γ t).1‖ * -E := mul_nonneg (hr t ht).le (neg_pos.2 hE).le
    nlinarith
  -- The lifetime bound is a quadratic inequality in `t - τ` with positive leading coefficient.
  set a := E ^ 2 / κ
  have hapos : 0 < a := div_pos (by nlinarith) hκ
  set p := radialMomentum (γ τ)
  set R := m * ‖(γ τ).1‖
  have hR : 0 < R := mul_pos hm (hr τ hτ)
  rw [Metric.isBounded_iff_subset_closedBall τ]
  refine ⟨2 * (|p| + R) / a + 1, fun t ht ↦ ?_⟩
  have hlt := mul_sq_sub_radialMomentum_mul_lt_of_sq_sub_inner_sq_eq_zero hm hs hγ hq hU hforce hτ
    hℓ ht
  rw [Metric.mem_closedBall, Real.dist_eq]
  by_contra hfar
  rw [not_le] at hfar
  set x := t - τ
  have hC : a / 2 * (2 * (|p| + R) / a + 1) = |p| + R + a / 2 := by field_simp
  have hC0 : 0 ≤ 2 * (|p| + R) / a := by positivity
  have hx1 : 1 ≤ |x| := by linarith
  have hpx : p * x ≤ |p| * |x| := by rw [← abs_mul]; exact le_abs_self _
  have hsq : a / 2 * x ^ 2 = |x| * (a / 2 * |x|) := by rw [← sq_abs x]; ring
  have hbig : |p| + R + a / 2 < a / 2 * |x| := by
    rw [← hC]; exact mul_lt_mul_of_pos_left hfar (by positivity)
  have h1 : |x| * (R + a / 2) < |x| * (a / 2 * |x| - |p|) :=
    mul_lt_mul_of_pos_left (by linarith) (by linarith)
  have h2 : R + a / 2 ≤ |x| * (R + a / 2) := le_mul_of_one_le_left (by positivity) hx1
  linarith

/-! ### Motions with nonzero angular momentum -/

/-- **Conservation of the length of the Runge–Lenz vector.** For `m ≠ 0`, the length `‖A‖` of
the Runge–Lenz vector is constant along an integral curve of the Kepler Hamiltonian vector field
on a preconnected set of times avoiding the collision set. -/
theorem norm_rungeLenz_eq_of_hasDerivAt_kepler (hm : m ≠ 0) (hs : IsPreconnected s)
    (hγ : ∀ t ∈ s, HasDerivAt γ ((stdSymplecticForm (V := V)).hamiltonianVectorField
      (centralForceHamiltonian m (fun r ↦ -κ / r)) (γ t)) t)
    (hq : ∀ t ∈ s, (γ t).1 ≠ 0) {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    ‖rungeLenz m κ (γ t)‖ = ‖rungeLenz m κ (γ t₀)‖ := by
  have hU : ∀ t ∈ s, DifferentiableAt ℝ (fun r ↦ -κ / r) ‖(γ t).1‖ :=
    fun t ht ↦ differentiableAt_kepler_potential κ (norm_ne_zero_iff.2 (hq t ht))
  -- `‖A‖² = (m κ)² + 2 m H ℓ²`, and both `H` and `ℓ²` are conserved.
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_rungeLenz_sq hm κ (hq t ht),
    norm_rungeLenz_sq hm κ (hq t₀ ht₀), centralForceHamiltonian_eq_of_hasDerivAt hs hγ hq hU ht₀ ht,
    sq_sub_inner_sq_eq_of_hasDerivAt hs hγ ht₀ ht]

/-- **The pericentre bound along a Kepler motion.** For `m ≠ 0`, along an integral curve of the
Kepler Hamiltonian vector field on a preconnected set `s` of times avoiding the collision set, the
distance to the centre at every time `t ∈ s` is at least `ℓ² / (m κ + ‖A‖)`, computed from the
squared angular momentum `ℓ²` and the Runge–Lenz vector `A` at any time `τ ∈ s`. -/
theorem sq_sub_inner_sq_div_le_norm_fst_of_hasDerivAt_kepler (hm : m ≠ 0) (hs : IsPreconnected s)
    (hγ : ∀ t ∈ s, HasDerivAt γ ((stdSymplecticForm (V := V)).hamiltonianVectorField
      (centralForceHamiltonian m (fun r ↦ -κ / r)) (γ t)) t)
    (hq : ∀ t ∈ s, (γ t).1 ≠ 0) {τ t : ℝ} (hτ : τ ∈ s) (ht : t ∈ s) :
    (‖(γ τ).1‖ ^ 2 * ‖(γ τ).2‖ ^ 2 - ⟪(γ τ).1, (γ τ).2⟫_ℝ ^ 2) /
        (m * κ + ‖rungeLenz m κ (γ τ)‖) ≤ ‖(γ t).1‖ := by
  have h := sq_sub_inner_sq_le_norm_fst_mul_add_norm_rungeLenz m κ (γ t)
  rw [sq_sub_inner_sq_eq_of_hasDerivAt hs hγ hτ ht,
    norm_rungeLenz_eq_of_hasDerivAt_kepler hm hs hγ hq hτ ht] at h
  rcases le_or_gt (m * κ + ‖rungeLenz m κ (γ τ)‖) 0 with hD | hD
  · exact (div_nonpos_of_nonneg_of_nonpos (by
      have := real_inner_mul_inner_self_le (γ τ).1 (γ τ).2
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at this
      nlinarith [sq_nonneg ⟪(γ τ).1, (γ τ).2⟫_ℝ]) hD).trans (norm_nonneg _)
  · rwa [div_le_iff₀ hD]

/-- **Kepler motions with nonzero angular momentum do not collide.** For `m ≠ 0`, along an integral
curve of the Kepler Hamiltonian vector field on a preconnected set `s` of times avoiding the
collision set, with nonzero angular momentum at some time `τ ∈ s`, the distance to the centre is
bounded below by a positive constant on all of `s`. -/
theorem exists_pos_forall_le_norm_fst_of_hasDerivAt_kepler (hm : m ≠ 0) (hs : IsPreconnected s)
    (hγ : ∀ t ∈ s, HasDerivAt γ ((stdSymplecticForm (V := V)).hamiltonianVectorField
      (centralForceHamiltonian m (fun r ↦ -κ / r)) (γ t)) t)
    (hq : ∀ t ∈ s, (γ t).1 ≠ 0) {τ : ℝ} (hτ : τ ∈ s)
    (hℓ : ‖(γ τ).1‖ ^ 2 * ‖(γ τ).2‖ ^ 2 - ⟪(γ τ).1, (γ τ).2⟫_ℝ ^ 2 ≠ 0) :
    ∃ c, 0 < c ∧ ∀ t ∈ s, c ≤ ‖(γ t).1‖ := by
  refine ⟨_, ?_, fun t ht ↦ sq_sub_inner_sq_div_le_norm_fst_of_hasDerivAt_kepler hm hs hγ hq hτ ht⟩
  -- At time `τ` itself, `0 < ℓ² ≤ ‖q‖ (m κ + ‖A‖)`, so both factors of the quotient are positive.
  have hℓpos : 0 < ‖(γ τ).1‖ ^ 2 * ‖(γ τ).2‖ ^ 2 - ⟪(γ τ).1, (γ τ).2⟫_ℝ ^ 2 := by
    refine lt_of_le_of_ne ?_ hℓ.symm
    have := real_inner_mul_inner_self_le (γ τ).1 (γ τ).2
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at this
    nlinarith [sq_nonneg ⟪(γ τ).1, (γ τ).2⟫_ℝ]
  have h := sq_sub_inner_sq_le_norm_fst_mul_add_norm_rungeLenz m κ (γ τ)
  have hD : 0 < m * κ + ‖rungeLenz m κ (γ τ)‖ :=
    pos_of_mul_pos_right (hℓpos.trans_le h) (norm_nonneg _)
  exact div_pos hℓpos hD

/-! ### Incompleteness of the Kepler flow -/

/-- **The Kepler flow on the punctured phase space is not complete.** For `m > 0` and `κ ≥ 0`, on
a nonzero space `V`, the Hamiltonian vector field of the Kepler energy
`‖p‖² / (2m) - κ / ‖q‖` on the punctured phase space, with the restriction of the standard
symplectic form, is not complete: a particle thrown straight at the centre reaches it in finite
time. -/
theorem not_isCompleteVectorField_hamiltonianVectorField_puncturedPhaseSpace_kepler [Nontrivial V]
    (hm : 0 < m) (hκ : 0 ≤ κ) :
    ¬ IsCompleteVectorField (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V)
        contMDiff_subtype_val (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) :=
  not_isCompleteVectorField_hamiltonianVectorField_puncturedPhaseSpace hm
    (contDiffOn_const.div contDiffOn_id fun r hr ↦ (mem_Ioi.1 hr).ne') fun r hr ↦ by
      rw [(hasDerivAt_kepler_potential κ hr.ne').deriv]
      positivity

end TauCeti
