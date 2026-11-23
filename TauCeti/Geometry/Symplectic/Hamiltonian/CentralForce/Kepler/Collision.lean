/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Integrable
public import TauCeti.Geometry.Manifold.Flow.Complete
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Collision
import TauCeti.Geometry.Symplectic.Hamiltonian.Complete
import TauCeti.Geometry.Symplectic.Manifold.Opens

/-!
# The Kepler collision domain

A particle of mass `m > 0` in a finite-dimensional inner product space `V`, moving in the
attractive Kepler potential `U(r) = -κ / r`, `κ > 0`, has the energy
`H(q, p) = ‖p‖² / (2m) - κ / ‖q‖` on the punctured phase space `q ≠ 0`
(`TauCeti.puncturedPhaseSpace`). This file determines which motions are defined for all time:
exactly those with nonzero angular momentum. The squared angular momentum is
`ℓ² = ‖q‖² ‖p‖² - ⟪q, p⟫²`, the squared length of the bivector `q ∧ p`; in the plane it is the
square of `L = q₁p₂ - q₂p₁` (`TauCeti.sq_angularMomentum`).

* **Radial motions are not global.** A motion with `ℓ = 0` cannot be defined for all time while
  avoiding the collision set, by the result for attractive central potentials
  (`TauCeti.sq_sub_inner_sq_ne_zero_of_hasDerivAt`). So it leaves the punctured phase space in
  finite time: its maximal interval of existence is bounded above or below.
* **Nonradial Kepler motions never collide.** For `ℓ ≠ 0`, the perihelion bound
  `ℓ² ≤ ‖q‖ (m κ + ‖A‖)` (`TauCeti.sq_sub_inner_sq_le_norm_fst_mul_add_norm_rungeLenz`), for the
  Runge–Lenz vector `A`, keeps `‖q‖` away from zero, since `ℓ²` and
  `‖A‖² = (m κ)² + 2 m H ℓ²` are conserved (`TauCeti.norm_rungeLenz_eq_of_hasDerivAt_kepler`,
  `TauCeti.sq_sub_inner_sq_div_le_norm_fst_of_hasDerivAt_kepler`). Energy conservation then
  bounds the momentum, so the position moves at bounded speed, and over every bounded time
  interval the motion stays in a compact subset of the punctured phase space. By the escape lemma
  for maximal integral curves (`maximalIntegralCurveInterval_eq_univ_of_forall_isCompact_mapsTo`)
  the motion is defined for all time. This holds at every energy, including the unbounded
  parabolic and hyperbolic motions with `H ≥ 0`.

Together these identify the **collision domain**: the maximal integral curve of the Kepler
Hamiltonian vector field on the punctured phase space through a state is defined for all time
exactly when its angular momentum is nonzero
(`TauCeti.maximalIntegralCurveInterval_hamiltonianVectorField_kepler_eq_univ_iff`, and
`TauCeti.maximalIntegralCurveInterval_hamiltonianVectorField_kepler_eq_univ_iff_angularMomentum`
in the plane). In particular, as soon as `V` is nontrivial, the Kepler flow on the punctured phase
space is not complete
(`TauCeti.not_isCompleteVectorField_hamiltonianVectorField_kepler`), unlike its restriction to
the bound phase space
(`TauCeti.isCompleteVectorField_hamiltonianVectorField_keplerBoundPhaseSpace`).

**Bound radial motions collide in the future.** A Kepler motion with zero angular momentum and
negative energy `E` stays in the ball `‖q‖ ≤ κ / (-E)`, where the attraction `κ / ‖q‖²` is at
least `E² / κ`. So its radial momentum decreases at a definite rate and eventually becomes
negative, after which the motion cannot avoid collision
(`TauCeti.snd_nonneg_of_forall_hasDerivAt_hamiltonianVectorField_effectivePotential`). Hence a
Kepler motion with zero angular momentum that avoids collision at all later times has nonnegative
energy (`TauCeti.centralForceHamiltonian_kepler_nonneg_of_forall_hasDerivAt`, and its reduced form
`TauCeti.centralForceHamiltonian_effectivePotential_kepler_nonneg_of_forall_hasDerivAt`).

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 8.
* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Addison-Wesley, 2002,
  Sections 3.7 and 3.9.
-/

public section

noncomputable section

open Set
open scoped InnerProductSpace Manifold ContDiff Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {m κ : ℝ}

/-- The Kepler Hamiltonian is smooth on the punctured phase space. -/
private theorem contMDiff_centralForceHamiltonian_kepler_comp_subtypeVal {n : WithTop ℕ∞} :
    ContMDiff 𝓘(ℝ, V × V) 𝓘(ℝ) n (centralForceHamiltonian m (fun r ↦ -κ / r) ∘
      (Subtype.val : puncturedPhaseSpace V → V × V)) :=
  contMDiff_centralForceHamiltonian_comp_subtypeVal fun _ hr ↦
    contDiffAt_const.div contDiffAt_id hr.ne'

variable [FiniteDimensional ℝ V]

/-- The restriction of the standard symplectic form to the punctured phase space is
nondegenerate. -/
private theorem isNondegenerate_puncturedPhaseSpace :
    SmoothTwoForm.IsNondegenerate (SmoothForm.mpullback
      (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
      (stdSymplecticForm (V := V)).constSmooth) :=
  (SymplecticForm.isNondegenerate_constSmooth _).mpullback_subtype_val _

/-- The Kepler Hamiltonian vector field on the punctured phase space is `C¹`. -/
private theorem contMDiff_hamiltonianVectorField_kepler :
    ContMDiff 𝓘(ℝ, V × V) 𝓘(ℝ, V × V).tangent 1
      (fun y ↦ (⟨y, SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val) y⟩ :
        TangentBundle 𝓘(ℝ, V × V) (puncturedPhaseSpace V))) :=
  isNondegenerate_puncturedPhaseSpace.contMDiff_hamiltonianVectorField (n := 1) (by simp)
    contMDiff_centralForceHamiltonian_kepler_comp_subtypeVal

/-- **Conservation of the length of the Runge–Lenz vector.** For `m ≠ 0`, the length `‖A‖` of
the Runge–Lenz vector is constant along an integral curve of the Kepler Hamiltonian vector field
on a preconnected set of times avoiding the collision set. -/
theorem norm_rungeLenz_eq_of_hasDerivAt_kepler (hm : m ≠ 0) {s : Set ℝ} (hs : IsPreconnected s)
    {γ : ℝ → V × V} (hγ : ∀ t ∈ s, HasDerivAt γ ((stdSymplecticForm (V := V)).hamiltonianVectorField
      (centralForceHamiltonian m (fun r ↦ -κ / r)) (γ t)) t)
    (hq : ∀ t ∈ s, (γ t).1 ≠ 0) {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    ‖rungeLenz m κ (γ t)‖ = ‖rungeLenz m κ (γ t₀)‖ := by
  -- `‖A‖² = (m κ)² + 2 m H ℓ²`, and both `H` and `ℓ²` are conserved.
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_rungeLenz_sq hm κ (hq t ht),
    norm_rungeLenz_sq hm κ (hq t₀ ht₀),
    centralForceHamiltonian_eq_of_hasDerivAt hs hγ hq (fun u hu ↦
      (hasDerivAt_kepler_potential κ (norm_ne_zero_iff.2 (hq u hu))).differentiableAt) ht₀ ht,
    sq_sub_inner_sq_eq_of_hasDerivAt hs hγ ht₀ ht]

/-- **The perihelion bound along a Kepler motion.** For `m ≠ 0`, along an integral curve of the
Kepler Hamiltonian vector field on a preconnected set `s` of times avoiding the collision set, the
distance to the centre at every time `t ∈ s` is at least `ℓ² / (m κ + ‖A‖)`, computed from the
squared angular momentum `ℓ²` and the Runge–Lenz vector `A` at any time `τ ∈ s`. -/
theorem sq_sub_inner_sq_div_le_norm_fst_of_hasDerivAt_kepler (hm : m ≠ 0) {s : Set ℝ}
    (hs : IsPreconnected s) {γ : ℝ → V × V}
    (hγ : ∀ t ∈ s, HasDerivAt γ ((stdSymplecticForm (V := V)).hamiltonianVectorField
      (centralForceHamiltonian m (fun r ↦ -κ / r)) (γ t)) t)
    (hq : ∀ t ∈ s, (γ t).1 ≠ 0) {τ t : ℝ} (hτ : τ ∈ s) (ht : t ∈ s) :
    (‖(γ τ).1‖ ^ 2 * ‖(γ τ).2‖ ^ 2 - ⟪(γ τ).1, (γ τ).2⟫_ℝ ^ 2) /
        (m * κ + ‖rungeLenz m κ (γ τ)‖) ≤ ‖(γ t).1‖ := by
  have h := sq_sub_inner_sq_le_norm_fst_mul_add_norm_rungeLenz m κ (γ t)
  rw [sq_sub_inner_sq_eq_of_hasDerivAt hs hγ hτ ht,
    norm_rungeLenz_eq_of_hasDerivAt_kepler hm hs hγ hq hτ ht] at h
  rcases le_or_gt (m * κ + ‖rungeLenz m κ (γ τ)‖) 0 with hD | hD
  · exact (div_nonpos_of_nonneg_of_nonpos (sq_sub_inner_sq_nonneg (γ τ)) hD).trans
      (norm_nonneg _)
  · rwa [div_le_iff₀ hD]

/-- **Nonradial Kepler motions stay away from the collision set with bounded momentum.** Let `η`
be an integral curve of the Kepler Hamiltonian vector field on a preconnected set `J` of times
containing `0`, avoiding the collision set, with nonzero angular momentum at time `0`. Then on `J`
the distance `‖q‖` to the origin is bounded below by a positive constant `r₀`, by the perihelion
bound `TauCeti.sq_sub_inner_sq_div_le_norm_fst_of_hasDerivAt_kepler`, and the momentum `‖p‖` is
bounded, by energy conservation. -/
private theorem exists_pos_forall_le_norm_fst_and_norm_snd_le_kepler (hm : 0 < m) (hκ : 0 < κ)
    {J : Set ℝ} (hJ : IsPreconnected J) (h0 : (0 : ℝ) ∈ J) {η : ℝ → V × V}
    (hη : ∀ t ∈ J, HasDerivAt η ((stdSymplecticForm (V := V)).hamiltonianVectorField
      (centralForceHamiltonian m (fun r ↦ -κ / r)) (η t)) t)
    (hq : ∀ t ∈ J, (η t).1 ≠ 0)
    (hℓ : ‖(η 0).1‖ ^ 2 * ‖(η 0).2‖ ^ 2 - ⟪(η 0).1, (η 0).2⟫_ℝ ^ 2 ≠ 0) :
    ∃ r₀ > 0, ∃ P, ∀ t ∈ J, r₀ ≤ ‖(η t).1‖ ∧ ‖(η t).2‖ ≤ P := by
  set E := centralForceHamiltonian m (fun r ↦ -κ / r) (η 0)
  -- The perihelion bound keeps the distance to the origin at least `r₀`.
  set r₀ := (‖(η 0).1‖ ^ 2 * ‖(η 0).2‖ ^ 2 - ⟪(η 0).1, (η 0).2⟫_ℝ ^ 2) /
    (m * κ + ‖rungeLenz m κ (η 0)‖)
  have hr₀ : 0 < r₀ := div_pos ((sq_sub_inner_sq_nonneg (η 0)).lt_of_ne hℓ.symm) (by positivity)
  have hr (t : ℝ) (ht : t ∈ J) : r₀ ≤ ‖(η t).1‖ :=
    sq_sub_inner_sq_div_le_norm_fst_of_hasDerivAt_kepler hm.ne' hJ hη hq h0 ht
  -- Energy conservation then bounds the momentum.
  refine ⟨r₀, hr₀, √(2 * m * (E + κ / r₀)), fun t ht ↦ ⟨hr t ht, ?_⟩⟩
  have hH : centralForceHamiltonian m (fun r ↦ -κ / r) (η t) = E :=
    centralForceHamiltonian_eq_of_hasDerivAt hJ hη hq (fun u hu ↦
      (hasDerivAt_kepler_potential κ (norm_ne_zero_iff.2 (hq u hu))).differentiableAt) h0 ht
  rw [centralForceHamiltonian_apply] at hH
  have hp2 : ‖(η t).2‖ ^ 2 = 2 * m * (E + κ / ‖(η t).1‖) := by
    rw [← hH]
    field_simp
    ring
  refine (abs_of_nonneg (norm_nonneg _)).symm.trans_le (Real.abs_le_sqrt ?_)
  rw [hp2]
  gcongr
  exact hr t ht

/-- **Nonradial Kepler motions stay in compact sets off the collision set.** Under the hypotheses
of `exists_pos_forall_le_norm_fst_and_norm_snd_le_kepler`, over each bounded time interval
`[-T, T]` the curve stays in a compact set off the collision set, since its position moves at
bounded speed. -/
private theorem exists_isCompact_forall_mem_of_hasDerivAt_kepler (hm : 0 < m) (hκ : 0 < κ)
    {J : Set ℝ} (hJ : IsPreconnected J) (h0 : (0 : ℝ) ∈ J) {η : ℝ → V × V}
    (hη : ∀ t ∈ J, HasDerivAt η ((stdSymplecticForm (V := V)).hamiltonianVectorField
      (centralForceHamiltonian m (fun r ↦ -κ / r)) (η t)) t)
    (hq : ∀ t ∈ J, (η t).1 ≠ 0)
    (hℓ : ‖(η 0).1‖ ^ 2 * ‖(η 0).2‖ ^ 2 - ⟪(η 0).1, (η 0).2⟫_ℝ ^ 2 ≠ 0) (T : ℝ) :
    ∃ K : Set (V × V), IsCompact K ∧ (∀ y ∈ K, y.1 ≠ 0) ∧ ∀ t ∈ J ∩ Icc (-T) T, η t ∈ K := by
  obtain ⟨r₀, hr₀, P, hb⟩ :=
    exists_pos_forall_le_norm_fst_and_norm_snd_le_kepler hm hκ hJ h0 hη hq hℓ
  -- The position moves at speed at most `P / m`.
  have hv (t : ℝ) (ht : t ∈ J) : HasDerivAt (fun s ↦ (η s).1) (m⁻¹ • (η t).2) t := by
    have h := hη t ht
    rw [stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian
      (hasDerivAt_kepler_potential κ (norm_ne_zero_iff.2 (hq t ht))) (hq t ht)] at h
    exact (hasFDerivAt_fst (𝕜 := ℝ) (p := η t)).comp_hasDerivAt t h
  refine ⟨(Metric.closedBall 0 (‖(η 0).1‖ + P / m * |T|) ×ˢ Metric.closedBall 0 P) ∩
    {y | r₀ ≤ ‖y.1‖}, ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).inter_right
    (isClosed_le continuous_const (continuous_norm.comp continuous_fst)),
    fun y hy ↦ norm_pos_iff.1 (hr₀.trans_le hy.2), fun t ⟨ht, hT⟩ ↦ ?_⟩
  refine ⟨⟨mem_closedBall_zero_iff.2 ?_, mem_closedBall_zero_iff.2 (hb t ht).2⟩, (hb t ht).1⟩
  have hsub := hJ.ordConnected.uIcc_subset h0 ht
  have hmv := (convex_uIcc 0 t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s ↦ (η s).1) (C := P / m) (fun s hs ↦ (hv s (hsub hs)).hasDerivWithinAt)
    (fun s hs ↦ by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hm.le, inv_mul_eq_div]
      exact div_le_div_of_nonneg_right (hb s (hsub hs)).2 hm.le) left_mem_uIcc right_mem_uIcc
  have htT : ‖t - 0‖ ≤ |T| := by
    rw [sub_zero, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hT.1, hT.2, le_abs_self T, neg_abs_le T]
  have hP : 0 ≤ P / m :=
    div_nonneg ((norm_nonneg _).trans (hb 0 h0).2) hm.le
  calc ‖(η t).1‖ ≤ ‖(η 0).1‖ + ‖(η t).1 - (η 0).1‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ ‖(η 0).1‖ + P / m * |T| := by
      gcongr
      exact hmv.trans (mul_le_mul_of_nonneg_left htT hP)

/-- Along the maximal integral curve of the Kepler Hamiltonian vector field on the punctured phase
space, positions and momenta solve Hamilton's equations in `V × V`. -/
private theorem hasDerivAt_coe_maximalIntegralCurve_kepler (x : puncturedPhaseSpace V) {t : ℝ}
    (ht : t ∈ maximalIntegralCurveInterval (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x) :
    HasDerivAt (fun s ↦ ((maximalIntegralCurve (SmoothTwoForm.hamiltonianVectorField
        (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V)
          contMDiff_subtypeVal (stdSymplecticForm (V := V)).constSmooth)
        (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x s :
          puncturedPhaseSpace V) : V × V))
      ((stdSymplecticForm (V := V)).hamiltonianVectorField
        (centralForceHamiltonian m (fun r ↦ -κ / r))
        ((maximalIntegralCurve (SmoothTwoForm.hamiltonianVectorField
          (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V)
            contMDiff_subtypeVal (stdSymplecticForm (V := V)).constSmooth)
          (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x t :
            puncturedPhaseSpace V) : V × V)) t := by
  -- The inclusion carries the restricted Hamiltonian vector field to the ambient one.
  have hγ := (isMIntegralCurveOn_maximalIntegralCurve
    (contMDiff_hamiltonianVectorField_kepler (m := m) (κ := κ)) (x := x)).map_of_mfderiv_eq
    (f := Subtype.val)
    (W := (stdSymplecticForm (V := V)).constSmooth.hamiltonianVectorField
      (centralForceHamiltonian m (fun r ↦ -κ / r)))
    (fun _ _ ↦ (contMDiff_subtypeVal (n := 1)).mdifferentiableAt one_ne_zero) fun s _ ↦ by
      rw [SmoothTwoForm.hamiltonianVectorField_comp_subtype_val, Manifold.mfderiv_subtype_val,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  rw [isMIntegralCurveOn_iff_isIntegralCurveOn] at hγ
  have h := (hγ t ht).hasDerivAt (isOpen_maximalIntegralCurveInterval.mem_nhds ht)
  rw [SymplecticForm.hamiltonianVectorField_constSmooth] at h
  exact h

/-- **Nonradial Kepler motions never collide.** For `m, κ > 0`, the maximal integral curve of the
Kepler Hamiltonian vector field on the punctured phase space through a state with nonzero angular
momentum, `‖q‖² ‖p‖² - ⟪q, p⟫² ≠ 0`, is defined for all time. This holds at every energy. -/
theorem maximalIntegralCurveInterval_hamiltonianVectorField_kepler_eq_univ (hm : 0 < m)
    (hκ : 0 < κ) (x : puncturedPhaseSpace V)
    (hx : ‖(x : V × V).1‖ ^ 2 * ‖(x : V × V).2‖ ^ 2 - ⟪(x : V × V).1, (x : V × V).2⟫_ℝ ^ 2 ≠ 0) :
    maximalIntegralCurveInterval (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x = univ := by
  have hv := contMDiff_hamiltonianVectorField_kepler (V := V) (m := m) (κ := κ)
  have h0 := zero_mem_maximalIntegralCurveInterval (x := x) hv.contMDiffAt
  refine maximalIntegralCurveInterval_eq_univ_of_forall_isCompact_mapsTo hv fun T ↦ ?_
  obtain ⟨K, hK, hK0, hmem⟩ := exists_isCompact_forall_mem_of_hasDerivAt_kepler hm hκ
    isPreconnected_maximalIntegralCurveInterval h0
    (fun t ht ↦ hasDerivAt_coe_maximalIntegralCurve_kepler x ht)
    (fun t _ ↦ mem_puncturedPhaseSpace.1 (maximalIntegralCurve _ x t).property)
    (by rwa [maximalIntegralCurve_zero]) T
  refine ⟨Subtype.val ⁻¹' K, ?_, fun t ht ↦ hmem t ht⟩
  rwa [Subtype.isCompact_iff, image_preimage_eq_of_subset fun y hy ↦
    ⟨⟨y, mem_puncturedPhaseSpace.2 (hK0 y hy)⟩, rfl⟩]

/-- **The collision domain of the Kepler problem.** For `m, κ > 0`, the maximal integral curve of
the Kepler Hamiltonian vector field on the punctured phase space through a state is defined for
all time exactly when the angular momentum of the state is nonzero,
`‖q‖² ‖p‖² - ⟪q, p⟫² ≠ 0`. Every motion with zero angular momentum leaves the punctured phase
space in finite time: its maximal interval of existence is bounded above or below. -/
theorem maximalIntegralCurveInterval_hamiltonianVectorField_kepler_eq_univ_iff (hm : 0 < m)
    (hκ : 0 < κ) (x : puncturedPhaseSpace V) :
    maximalIntegralCurveInterval (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x = univ ↔
      ‖(x : V × V).1‖ ^ 2 * ‖(x : V × V).2‖ ^ 2 - ⟪(x : V × V).1, (x : V × V).2⟫_ℝ ^ 2 ≠ 0 := by
  refine ⟨fun h ↦ ?_, maximalIntegralCurveInterval_hamiltonianVectorField_kepler_eq_univ hm hκ x⟩
  -- A global maximal curve is a global solution of Hamilton's equations avoiding the collision set,
  -- which the attractive Kepler force rules out for zero angular momentum.
  have hU (y : puncturedPhaseSpace V) :
      HasDerivAt (fun r ↦ -κ / r) (κ / ‖(y : V × V).1‖ ^ 2) ‖(y : V × V).1‖ :=
    hasDerivAt_kepler_potential κ (norm_ne_zero_iff.2 (mem_puncturedPhaseSpace.1 y.property))
  have hU' (y : puncturedPhaseSpace V) : 0 < deriv (fun r ↦ -κ / r) ‖(y : V × V).1‖ := by
    rw [(hU y).deriv]
    exact div_pos hκ (pow_pos (norm_pos_iff.2 (mem_puncturedPhaseSpace.1 y.property)) 2)
  have h' := sq_sub_inner_sq_ne_zero_of_hasDerivAt hm
    (fun t ↦ hasDerivAt_coe_maximalIntegralCurve_kepler x (h ▸ mem_univ t))
    (fun t ↦ mem_puncturedPhaseSpace.1 (maximalIntegralCurve _ x t).property)
    (fun t ↦ (hU _).differentiableAt) (fun t ↦ hU' _) 0
  rwa [maximalIntegralCurve_zero] at h'

/-- **The collision domain of the planar Kepler problem.** In the plane, with angular momentum
`L = q₁p₂ - q₂p₁` in an orthonormal basis `b`, the maximal integral curve of the Kepler Hamiltonian
vector field on the punctured phase space through a state is defined for all time exactly when
`L ≠ 0`. -/
theorem maximalIntegralCurveInterval_hamiltonianVectorField_kepler_eq_univ_iff_angularMomentum
    (b : OrthonormalBasis (Fin 2) ℝ V) (hm : 0 < m) (hκ : 0 < κ) (x : puncturedPhaseSpace V) :
    maximalIntegralCurveInterval (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x = univ ↔
      angularMomentum (b 0) (b 1) x ≠ 0 := by
  rw [maximalIntegralCurveInterval_hamiltonianVectorField_kepler_eq_univ_iff hm hκ,
    ← sq_angularMomentum b, pow_ne_zero_iff two_ne_zero]

/-- **The Kepler flow is not complete.** For `m, κ > 0` and a nontrivial space `V`, the Kepler
Hamiltonian vector field on the punctured phase space is not complete: the motion of a particle
released at rest is not defined for all time. -/
theorem not_isCompleteVectorField_hamiltonianVectorField_kepler [Nontrivial V] (hm : 0 < m)
    (hκ : 0 < κ) :
    ¬ IsCompleteVectorField (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) := by
  intro h
  obtain ⟨q, hq⟩ := exists_ne (0 : V)
  have h' := (maximalIntegralCurveInterval_hamiltonianVectorField_kepler_eq_univ_iff hm hκ
    ⟨(q, 0), mem_puncturedPhaseSpace.2 hq⟩).1 (h.maximalIntegralCurveInterval_eq_univ _)
  simp at h'

/-! ### Bound radial motions collide in the future -/

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

end TauCeti
