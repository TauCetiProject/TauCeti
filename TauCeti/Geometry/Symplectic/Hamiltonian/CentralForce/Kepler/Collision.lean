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
  parabolic and hyperbolic motions with `H ≥ 0`. So through every noncollision state with
  `ℓ ≠ 0` passes a global solution of Hamilton's equations in `V × V`
  (`TauCeti.exists_hasDerivAt_kepler_of_sq_sub_inner_sq_ne_zero`).

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

**Radial motions reach the collision set in finite time.** A Kepler motion with zero angular
momentum moves on a fixed ray through the origin (`TauCeti.sameRay_fst_of_hasDerivAt`), and its
maximal interval of existence is bounded above or below. At a finite end the position tends to
the collision point `0` (`TauCeti.tendsto_fst_maximalIntegralCurve_kepler_nhdsLT`,
`TauCeti.tendsto_fst_maximalIntegralCurve_kepler_nhdsGT`), so the motion reaches the collision set
forwards or backwards in time (`TauCeti.exists_tendsto_fst_maximalIntegralCurve_kepler`). Indeed
its radial momentum decreases, so its distance to the origin first increases and then decreases,
and stays bounded over the finite time interval. If the distance did not tend to `0`, it would
stay in a band `[δ, R]` with `δ > 0` near the end, where energy conservation bounds the momentum;
the motion would then stay in a compact subset of the punctured phase space, which the escape
lemma `eventually_notMem_nhdsLT_maximalIntegralCurve` rules out at a finite end. The backward
statement follows by reversing time. A motion of negative energy collides in both directions of
time: its maximal interval of existence is bounded
(`TauCeti.bddAbove_and_bddBelow_maximalIntegralCurveInterval_kepler`).

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 8.
* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Addison-Wesley, 2002,
  Sections 3.7 and 3.9.
-/

public section

noncomputable section

open Filter Set
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

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **Energy bounds the Kepler momentum away from the collision set.** For `m > 0` and `κ ≥ 0`,
a state at distance at least `r₀ > 0` from the origin has momentum `‖p‖ ≤ √(2m (E + κ / r₀))`,
where `E = ‖p‖² / (2m) - κ / ‖q‖` is its energy. -/
private theorem norm_snd_le_sqrt_kepler (hm : 0 < m) (hκ : 0 ≤ κ) {r₀ : ℝ} (hr₀ : 0 < r₀)
    {y : V × V} (hy : r₀ ≤ ‖y.1‖) :
    ‖y.2‖ ≤ √(2 * m * (centralForceHamiltonian m (fun r ↦ -κ / r) y + κ / r₀)) := by
  have hp2 : ‖y.2‖ ^ 2 =
      2 * m * (centralForceHamiltonian m (fun r ↦ -κ / r) y + κ / ‖y.1‖) := by
    rw [centralForceHamiltonian_apply]
    field_simp
    ring
  refine (abs_of_nonneg (norm_nonneg _)).symm.trans_le (Real.abs_le_sqrt ?_)
  rw [hp2]
  gcongr

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
    sq_sub_inner_sq_div_le_norm_fst_of_hasDerivAt_kepler hJ hη hq h0 ht
  -- Energy conservation then bounds the momentum.
  refine ⟨r₀, hr₀, √(2 * m * (E + κ / r₀)), fun t ht ↦ ⟨hr t ht, ?_⟩⟩
  have hH : centralForceHamiltonian m (fun r ↦ -κ / r) (η t) = E :=
    centralForceHamiltonian_eq_of_hasDerivAt hJ hη hq (fun u hu ↦
      (hasDerivAt_kepler_potential κ (norm_ne_zero_iff.2 (hq u hu))).differentiableAt) h0 ht
  rw [← hH]
  exact norm_snd_le_sqrt_kepler hm hκ.le hr₀ (hr t ht)

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

/-- The maximal integral curve of the Kepler Hamiltonian vector field on the punctured phase space
avoids the collision set `q = 0`. -/
private theorem fst_maximalIntegralCurve_kepler_ne_zero (x : puncturedPhaseSpace V) (t : ℝ) :
    ((maximalIntegralCurve (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x t :
        puncturedPhaseSpace V) : V × V).1 ≠ 0 :=
  mem_puncturedPhaseSpace.1 (maximalIntegralCurve _ x t).property

/-- Along the maximal integral curve of the Kepler Hamiltonian vector field on the punctured phase
space, the Kepler potential `-κ / r` is differentiable at the distance to the origin. -/
private theorem differentiableAt_kepler_potential_maximalIntegralCurve (x : puncturedPhaseSpace V)
    (t : ℝ) :
    DifferentiableAt ℝ (fun r ↦ -κ / r) ‖((maximalIntegralCurve
      (SmoothTwoForm.hamiltonianVectorField
        (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
          (stdSymplecticForm (V := V)).constSmooth)
        (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x t :
          puncturedPhaseSpace V) : V × V).1‖ :=
  (hasDerivAt_kepler_potential κ
    (norm_ne_zero_iff.2 (fst_maximalIntegralCurve_kepler_ne_zero x t))).differentiableAt

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

/-- **Global nonradial Kepler motions.** For `m, κ > 0`, through every state `x` with nonzero
angular momentum, `‖q‖² ‖p‖² - ⟪q, p⟫² ≠ 0` (such a state is not a collision), passes a solution
of Hamilton's equations for the Kepler Hamiltonian which is defined for all time and never
collides. -/
theorem exists_hasDerivAt_kepler_of_sq_sub_inner_sq_ne_zero (hm : 0 < m) (hκ : 0 < κ)
    {x : V × V} (hx : ‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 - ⟪x.1, x.2⟫_ℝ ^ 2 ≠ 0) :
    ∃ γ : ℝ → V × V, γ 0 = x ∧ (∀ t, HasDerivAt γ
      ((stdSymplecticForm (V := V)).hamiltonianVectorField
        (centralForceHamiltonian m (fun r ↦ -κ / r)) (γ t)) t) ∧ ∀ t, (γ t).1 ≠ 0 := by
  have hq : x.1 ≠ 0 := by
    rintro h
    simp [h] at hx
  set x' : puncturedPhaseSpace V := ⟨x, mem_puncturedPhaseSpace.2 hq⟩
  have huniv := maximalIntegralCurveInterval_hamiltonianVectorField_kepler_eq_univ hm hκ x' hx
  exact ⟨fun t ↦ ((maximalIntegralCurve (SmoothTwoForm.hamiltonianVectorField
    (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
      (stdSymplecticForm (V := V)).constSmooth)
    (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x' t :
      puncturedPhaseSpace V) : V × V), by simp [x', maximalIntegralCurve_zero],
    fun t ↦ hasDerivAt_coe_maximalIntegralCurve_kepler x' (huniv ▸ mem_univ t),
    fun t ↦ mem_puncturedPhaseSpace.1 (maximalIntegralCurve _ x' t).property⟩

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

/-! ### Motions with zero angular momentum reach the collision set -/

/-- **The radial momentum of a radial Kepler motion decreases.** Let `κ > 0`, and let
`ρ = (r, p_r)` be an integral curve, on the times of `[a, b)`, of the reduced Hamiltonian vector
field of `H_0(r, p_r) = p_r² / (2m) - κ / r`, staying in the half-line `r > 0`. Then `r' = p_r / m`,
and the radial momentum is strictly decreasing, since `p_r' = -κ / r² < 0`. -/
private theorem hasDerivAt_fst_and_strictAntiOn_snd_kepler (hκ : 0 < κ) {ρ : ℝ → ℝ × ℝ}
    {a b : ℝ}
    (hρ : ∀ t ∈ Ico a b, HasDerivAt ρ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
      (centralForceHamiltonian m (effectivePotential m 0 fun r ↦ -κ / r)) (ρ t)) t)
    (hr : ∀ t ∈ Ico a b, 0 < (ρ t).1) :
    (∀ t ∈ Ico a b, HasDerivAt (fun s ↦ (ρ s).1) ((ρ t).2 / m) t) ∧
      StrictAntiOn (fun s ↦ (ρ s).2) (Ico a b) := by
  have hU (t : ℝ) (ht : t ∈ Ico a b) := hasDerivAt_kepler_potential κ (hr t ht).ne'
  have hp' (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivAt (fun s ↦ (ρ s).2) (-(κ / (ρ t).1 ^ 2)) t := by
    have h := hasDerivAt_snd_of_hasDerivAt_hamiltonianVectorField_effectivePotential (hρ t ht)
      (hr t ht) (hU t ht).differentiableAt
    rwa [(hU t ht).deriv, zero_pow two_ne_zero, zero_div, zero_sub] at h
  refine ⟨fun t ht ↦ hasDerivAt_fst_of_hasDerivAt_hamiltonianVectorField_effectivePotential
    (hρ t ht) (hr t ht) (hU t ht).differentiableAt, ?_⟩
  exact strictAntiOn_of_deriv_neg (convex_Ico a b)
    (fun t ht ↦ (hp' t ht).continuousAt.continuousWithinAt) fun t ht ↦ by
      rw [(hp' t (interior_subset ht)).deriv, neg_lt_zero]
      exact div_pos hκ (pow_pos (hr t (interior_subset ht)) 2)

/-- **Radial Kepler motions stay in a band near a finite end of their time interval.** Let
`m, κ > 0`, and let `ρ = (r, p_r)` be an integral curve, on the times `[a, b)`, of the reduced
Hamiltonian vector field of `H_0(r, p_r) = p_r² / (2m) - κ / r`, staying in the half-line `r > 0`.
If `r ≥ ε > 0` at times arbitrarily close to `b`, then on some interval `[t₀, b)` the radius stays
in a band `[δ, R]` with `δ > 0`. The radial momentum decreases, so the radius first increases and
then decreases, and it grows at most at its initial rate. -/
private theorem exists_forall_mem_Icc_of_frequently_le_kepler (hm : 0 < m) (hκ : 0 < κ)
    {ρ : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a < b)
    (hρ : ∀ t ∈ Ico a b, HasDerivAt ρ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
      (centralForceHamiltonian m (effectivePotential m 0 fun r ↦ -κ / r)) (ρ t)) t)
    (hr : ∀ t ∈ Ico a b, 0 < (ρ t).1) {ε : ℝ} (hε : 0 < ε)
    (hfreq : ∃ᶠ t in 𝓝[<] b, ε ≤ (ρ t).1) :
    ∃ δ > 0, ∃ R, ∃ t₀ ∈ Ico a b, ∀ t ∈ Ico t₀ b, (ρ t).1 ∈ Icc δ R := by
  have ha : a ∈ Ico a b := left_mem_Ico.2 hab
  obtain ⟨hr', hanti⟩ := hasDerivAt_fst_and_strictAntiOn_snd_kepler hκ hρ hr
  -- On a subinterval `D` where the radial momentum has a sign, the radius is monotone.
  have hderiv {D : Set ℝ} (hD : D ⊆ Ico a b) (t : ℝ) (ht : t ∈ interior D) :
      deriv (fun s ↦ (ρ s).1) t = (ρ t).2 / m := (hr' t (hD (interior_subset ht))).deriv
  have hcont {D : Set ℝ} (hD : D ⊆ Ico a b) : ContinuousOn (fun s ↦ (ρ s).1) D :=
    fun t ht ↦ (hr' t (hD ht)).continuousAt.continuousWithinAt
  have hdiff {D : Set ℝ} (hD : D ⊆ Ico a b) : DifferentiableOn ℝ (fun s ↦ (ρ s).1) (interior D) :=
    fun t ht ↦ (hr' t (hD (interior_subset ht))).differentiableAt.differentiableWithinAt
  -- The radius grows at most at the rate `|p_r(a)| / m`, so it stays below `R`.
  set R := (ρ a).1 + |(ρ a).2| / m * (b - a)
  have hR (t : ℝ) (ht : t ∈ Ico a b) : (ρ t).1 ≤ R := by
    have h := (convex_Ico a b).image_sub_le_mul_sub_of_deriv_le (hcont subset_rfl)
      (hdiff subset_rfl) (C := |(ρ a).2| / m) (fun s hs ↦ by
        rw [hderiv subset_rfl s hs]
        exact div_le_div_of_nonneg_right ((hanti.antitoneOn ha (interior_subset hs)
          (interior_subset hs).1).trans (le_abs_self _)) hm.le) a ha t ht ht.1
    have hle : |(ρ a).2| / m * (t - a) ≤ |(ρ a).2| / m * (b - a) :=
      mul_le_mul_of_nonneg_left (by linarith [ht.2]) (by positivity)
    linarith
  by_cases hpos : ∀ t ∈ Ico a b, 0 ≤ (ρ t).2
  · -- If the particle never moves inwards, its radius stays at least `r(a)`.
    have hmono := monotoneOn_of_deriv_nonneg (convex_Ico a b) (hcont subset_rfl)
      (hdiff subset_rfl) fun t ht ↦ by
        rw [hderiv subset_rfl t ht]
        exact div_nonneg (hpos t (interior_subset ht)) hm.le
    exact ⟨(ρ a).1, hr a ha, R, a, ha, fun t ht ↦ ⟨hmono ha ht ht.1, hR t ht⟩⟩
  · -- Once it moves inwards, at a time `t₁`, its radius decreases, so it stays at least `ε`.
    push Not at hpos
    obtain ⟨t₁, ht₁, hp₁⟩ := hpos
    have hsub : Ico t₁ b ⊆ Ico a b := Ico_subset_Ico_left ht₁.1
    have hanti' := antitoneOn_of_deriv_nonpos (convex_Ico t₁ b) (hcont hsub) (hdiff hsub)
      fun t ht ↦ by
        have ht' := interior_subset ht
        rw [hderiv hsub t ht]
        exact div_nonpos_of_nonpos_of_nonneg
          ((hanti.antitoneOn ht₁ (hsub ht') ht'.1).trans hp₁.le) hm.le
    refine ⟨ε, hε, R, t₁, ht₁, fun t ht ↦ ⟨?_, hR t (hsub ht)⟩⟩
    obtain ⟨s, hεs, hs⟩ := (hfreq.and_eventually (Ioo_mem_nhdsLT ht.2)).exists
    exact hεs.trans (hanti' ht ⟨ht.1.trans hs.1.le, hs.2⟩ hs.1.le)

/-- **Kepler motions in a band of radii stay in a compact set.** For `m, κ > 0`, if the maximal
integral curve of the Kepler Hamiltonian vector field on the punctured phase space keeps its
distance to the origin in a band `[δ, R]`, `δ > 0`, at the times of a set `S` in its maximal
interval, then at these times it stays in a compact set: energy conservation bounds the
momentum. -/
private theorem exists_isCompact_forall_maximalIntegralCurve_mem_kepler (hm : 0 < m)
    (hκ : 0 < κ) (x : puncturedPhaseSpace V) {S : Set ℝ}
    (hS : S ⊆ maximalIntegralCurveInterval (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x)
    {δ R : ℝ} (hδ : 0 < δ)
    (hband : ∀ t ∈ S, ‖((maximalIntegralCurve (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x t :
        puncturedPhaseSpace V) : V × V).1‖ ∈ Icc δ R) :
    ∃ K : Set (puncturedPhaseSpace V), IsCompact K ∧ ∀ t ∈ S,
      maximalIntegralCurve (SmoothTwoForm.hamiltonianVectorField
        (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
          (stdSymplecticForm (V := V)).constSmooth)
        (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x t ∈ K := by
  have hv := contMDiff_hamiltonianVectorField_kepler (V := V) (m := m) (κ := κ)
  have h0 := zero_mem_maximalIntegralCurveInterval (x := x) hv.contMDiffAt
  set E := centralForceHamiltonian m (fun r ↦ -κ / r) (x : V × V)
  set K₀ : Set (V × V) := (Metric.closedBall 0 R ×ˢ Metric.closedBall 0 √(2 * m * (E + κ / δ)))
    ∩ {y | δ ≤ ‖y.1‖}
  have hK₀ : IsCompact K₀ :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).inter_right
      (isClosed_le continuous_const (continuous_norm.comp continuous_fst))
  refine ⟨Subtype.val ⁻¹' K₀, ?_, fun t ht ↦ ?_⟩
  · rwa [Subtype.isCompact_iff, image_preimage_eq_of_subset fun y hy ↦
      ⟨⟨y, mem_puncturedPhaseSpace.2 (norm_pos_iff.1 (hδ.trans_le hy.2))⟩, rfl⟩]
  -- By energy conservation the energy at time `t` is `E`.
  have hH := centralForceHamiltonian_eq_of_hasDerivAt isPreconnected_maximalIntegralCurveInterval
    (fun s hs ↦ hasDerivAt_coe_maximalIntegralCurve_kepler x hs)
    (fun s _ ↦ fst_maximalIntegralCurve_kepler_ne_zero x s)
    (fun s _ ↦ differentiableAt_kepler_potential_maximalIntegralCurve x s) h0 (hS ht)
  rw [maximalIntegralCurve_zero] at hH
  refine ⟨⟨mem_closedBall_zero_iff.2 (hband t ht).2, mem_closedBall_zero_iff.2 ?_⟩,
    (hband t ht).1⟩
  have hp := norm_snd_le_sqrt_kepler hm hκ.le hδ (hband t ht).1
  rwa [hH] at hp

/-- **The radial motion of a Kepler motion with a finite end.** For `m, κ > 0`, if the interval
of existence of the maximal integral curve of the Kepler Hamiltonian vector field on the punctured
phase space through `x` is not all of `ℝ`, then the angular momentum of `x` vanishes, so the radial
projection `(‖q‖, p_r)` of the curve is an integral curve, on that interval, of the reduced
Hamiltonian vector field of `H_0(r, p_r) = p_r² / (2m) - κ / r`. -/
private theorem hasDerivAt_radialProjection_maximalIntegralCurve_kepler (hm : 0 < m)
    (hκ : 0 < κ) (x : puncturedPhaseSpace V)
    (hI : maximalIntegralCurveInterval (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x ≠ univ) :
    ∀ t ∈ maximalIntegralCurveInterval (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x,
    HasDerivAt (fun s ↦ radialProjection ((maximalIntegralCurve
      (SmoothTwoForm.hamiltonianVectorField
        (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
          (stdSymplecticForm (V := V)).constSmooth)
        (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x s :
          puncturedPhaseSpace V) : V × V))
      ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
        (centralForceHamiltonian m (effectivePotential m 0 fun r ↦ -κ / r))
        (radialProjection ((maximalIntegralCurve (SmoothTwoForm.hamiltonianVectorField
          (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
            (stdSymplecticForm (V := V)).constSmooth)
          (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x t :
            puncturedPhaseSpace V) : V × V))) t := by
  have h0 := zero_mem_maximalIntegralCurveInterval (x := x)
    (contMDiff_hamiltonianVectorField_kepler (V := V) (m := m) (κ := κ)).contMDiffAt
  have hq := fst_maximalIntegralCurve_kepler_ne_zero (m := m) (κ := κ) x
  have hℓ :
      ‖(x : V × V).1‖ ^ 2 * ‖(x : V × V).2‖ ^ 2 - ⟪(x : V × V).1, (x : V × V).2⟫_ℝ ^ 2 = 0 :=
    by_contra fun hℓ ↦
      hI (maximalIntegralCurveInterval_hamiltonianVectorField_kepler_eq_univ hm hκ x hℓ)
  exact hasDerivAt_radialProjection_comp isPreconnected_maximalIntegralCurveInterval
    (fun t ht ↦ hasDerivAt_coe_maximalIntegralCurve_kepler x ht) (fun t _ ↦ hq t)
    (fun t _ ↦ differentiableAt_kepler_potential_maximalIntegralCurve x t) h0
    (ℓ := 0) (by rw [maximalIntegralCurve_zero, hℓ]; ring)

/-- **Kepler motions collide at a finite end of their time interval, forwards in time.** For
`m, κ > 0`, if the maximal integral curve of the Kepler Hamiltonian vector field on the punctured
phase space through `x` has a finite least upper bound `b` of its interval of existence, then its
position tends to the collision point `0` as `t → b⁻`. Such a finite end occurs only for zero
angular momentum (`TauCeti.maximalIntegralCurveInterval_hamiltonianVectorField_kepler_eq_univ_iff`).
-/
theorem tendsto_fst_maximalIntegralCurve_kepler_nhdsLT (hm : 0 < m) (hκ : 0 < κ)
    (x : puncturedPhaseSpace V) {b : ℝ}
    (hb : IsLUB (maximalIntegralCurveInterval (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x) b) :
    Tendsto (fun t ↦ ((maximalIntegralCurve (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x t :
        puncturedPhaseSpace V) : V × V).1) (𝓝[<] b) (𝓝 0) := by
  have hv := contMDiff_hamiltonianVectorField_kepler (V := V) (m := m) (κ := κ)
  have hq := fst_maximalIntegralCurve_kepler_ne_zero (m := m) (κ := κ) x
  -- The radial projection `(‖q‖, p_r)` is a radial motion with `ℓ = 0`.
  have hρ := hasDerivAt_radialProjection_maximalIntegralCurve_kepler hm hκ x fun h ↦
    not_bddAbove_univ (h ▸ hb).bddAbove
  obtain ⟨a, ha, hb0, hsub⟩ := exists_Ioo_subset_maximalIntegralCurveInterval_of_isLUB hb
  have hS : Ico 0 b ⊆ maximalIntegralCurveInterval _ x :=
    fun t ht ↦ hsub ⟨ha.trans_le ht.1, ht.2⟩
  -- If `‖q‖ ≥ ε` at times arbitrarily close to `b`, the motion stays in a compact set near `b`,
  -- which the escape lemma rules out.
  rw [tendsto_zero_iff_norm_tendsto_zero]
  by_contra hlim
  rw [Metric.tendsto_nhds] at hlim
  push Not at hlim
  obtain ⟨ε, hε, hfreq⟩ := hlim
  obtain ⟨δ, hδ, R, t₀, ht₀, hband⟩ := exists_forall_mem_Icc_of_frequently_le_kepler hm hκ hb0
    (fun t ht ↦ hρ t (hS ht))
    (fun t _ ↦ by simpa [radialProjection_fst] using hq t) hε
    (hfreq.mono fun t ht ↦ by simpa [radialProjection_fst] using ht)
  obtain ⟨K, hK, hmem⟩ := exists_isCompact_forall_maximalIntegralCurve_mem_kepler hm hκ x
    (S := Ico t₀ b) (fun t ht ↦ hS ⟨ht₀.1.trans ht.1, ht.2⟩) hδ
    (fun t ht ↦ by simpa [radialProjection_fst] using hband t ht)
  obtain ⟨t, ht, htK⟩ := (Filter.Eventually.and (Ico_mem_nhdsLT ht₀.2)
    (eventually_notMem_nhdsLT_maximalIntegralCurve hv hb hK)).exists
  exact htK (hmem t ht)

/-- **Kepler motions collide at a finite end of their time interval, backwards in time.** For
`m, κ > 0`, if the maximal integral curve of the Kepler Hamiltonian vector field on the punctured
phase space through `x` has a finite greatest lower bound `a` of its interval of existence, then
its position tends to the collision point `0` as `t → a⁺`. -/
theorem tendsto_fst_maximalIntegralCurve_kepler_nhdsGT (hm : 0 < m) (hκ : 0 < κ)
    (x : puncturedPhaseSpace V) {a : ℝ}
    (ha : IsGLB (maximalIntegralCurveInterval (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x) a) :
    Tendsto (fun t ↦ ((maximalIntegralCurve (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x t :
        puncturedPhaseSpace V) : V × V).1) (𝓝[>] a) (𝓝 0) := by
  have hv := contMDiff_hamiltonianVectorField_kepler (V := V) (m := m) (κ := κ)
  have hq := fst_maximalIntegralCurve_kepler_ne_zero (m := m) (κ := κ) x
  -- The radial projection `(‖q‖, p_r)` is a radial motion with `ℓ = 0`.
  have hρ := hasDerivAt_radialProjection_maximalIntegralCurve_kepler hm hκ x fun h ↦
    not_bddBelow_univ (h ▸ ha).bddBelow
  obtain ⟨b, hb, ha0, hsub⟩ := exists_Ioo_subset_maximalIntegralCurveInterval_of_isGLB ha
  have hS {s : ℝ} (hs : s ∈ Ico 0 (-a)) : -s ∈ maximalIntegralCurveInterval _ x :=
    hsub ⟨lt_neg.1 hs.2, (neg_nonpos.2 hs.1).trans_lt hb⟩
  -- Reversing time turns the radial motion near `a` into a radial motion near `-a`, from the
  -- right end of `[0, -a)`, where the forward argument applies.
  rw [tendsto_zero_iff_norm_tendsto_zero]
  by_contra hlim
  rw [Metric.tendsto_nhds] at hlim
  push Not at hlim
  obtain ⟨ε, hε, hfreq⟩ := hlim
  have hneg : Tendsto Neg.neg (𝓝[>] a) (𝓝[<] (-a)) := by
    simpa using tendsto_neg_nhdsGT_neg (a := -a)
  have hfreq' : ∃ᶠ s in 𝓝[<] (-a), ε ≤ ‖((maximalIntegralCurve _ x (-s) :
      puncturedPhaseSpace V) : V × V).1‖ :=
    hneg.frequently (hfreq.mono fun t ht ↦ by simpa using ht)
  obtain ⟨δ, hδ, R, t₀, ht₀, hband⟩ := exists_forall_mem_Icc_of_frequently_le_kepler hm hκ
    (neg_pos.2 ha0)
    (fun s hs ↦ hasDerivAt_reverse_hamiltonianVectorField_effectivePotential (hρ (-s) (hS hs))
      (by simpa [radialProjection_fst] using hq (-s))
      (by simpa [radialProjection_fst] using
        differentiableAt_kepler_potential_maximalIntegralCurve (m := m) x (-s)))
    (fun s _ ↦ by simpa [radialProjection_fst] using hq (-s)) hε
    (hfreq'.mono fun s hs ↦ by simpa [radialProjection_fst] using hs)
  have ht₀' : a < -t₀ := lt_neg.2 ht₀.2
  obtain ⟨K, hK, hmem⟩ := exists_isCompact_forall_maximalIntegralCurve_mem_kepler hm hκ x
    (S := Ioc a (-t₀)) (fun t ht ↦ hsub ⟨ht.1, ht.2.trans_lt ((neg_nonpos.2 ht₀.1).trans_lt hb)⟩)
    hδ (fun t ht ↦ by
      simpa [radialProjection_fst] using hband (-t) ⟨le_neg.1 ht.2, neg_lt_neg ht.1⟩)
  obtain ⟨t, ht, htK⟩ := (Filter.Eventually.and (Ioc_mem_nhdsGT ht₀')
    (eventually_notMem_nhdsGT_maximalIntegralCurve hv ha hK)).exists
  exact htK (hmem t ht)

/-- **Motions with zero angular momentum collide in finite time.** For `m, κ > 0`, the maximal
integral curve of the Kepler Hamiltonian vector field on the punctured phase space through a
state of zero angular momentum, `‖q‖² ‖p‖² - ⟪q, p⟫² = 0`, reaches the collision set forwards or
backwards in time: its interval of existence has a finite least upper bound `b` with `q → 0` as
`t → b⁻`, or a finite greatest lower bound `a` with `q → 0` as `t → a⁺`. -/
theorem exists_tendsto_fst_maximalIntegralCurve_kepler (hm : 0 < m) (hκ : 0 < κ)
    (x : puncturedPhaseSpace V)
    (hℓ : ‖(x : V × V).1‖ ^ 2 * ‖(x : V × V).2‖ ^ 2 - ⟪(x : V × V).1, (x : V × V).2⟫_ℝ ^ 2 = 0) :
    (∃ b, IsLUB (maximalIntegralCurveInterval (SmoothTwoForm.hamiltonianVectorField
        (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
          (stdSymplecticForm (V := V)).constSmooth)
        (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x) b ∧
      Tendsto (fun t ↦ ((maximalIntegralCurve (SmoothTwoForm.hamiltonianVectorField
        (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
          (stdSymplecticForm (V := V)).constSmooth)
        (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x t :
          puncturedPhaseSpace V) : V × V).1) (𝓝[<] b) (𝓝 0)) ∨
    ∃ a, IsGLB (maximalIntegralCurveInterval (SmoothTwoForm.hamiltonianVectorField
        (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
          (stdSymplecticForm (V := V)).constSmooth)
        (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x) a ∧
      Tendsto (fun t ↦ ((maximalIntegralCurve (SmoothTwoForm.hamiltonianVectorField
        (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
          (stdSymplecticForm (V := V)).constSmooth)
        (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x t :
          puncturedPhaseSpace V) : V × V).1) (𝓝[>] a) (𝓝 0) := by
  set X := SmoothTwoForm.hamiltonianVectorField
    (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
      (stdSymplecticForm (V := V)).constSmooth)
    (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)
  have h0 := zero_mem_maximalIntegralCurveInterval (x := x)
    (contMDiff_hamiltonianVectorField_kepler (V := V) (m := m) (κ := κ)).contMDiffAt
  by_cases hup : BddAbove (maximalIntegralCurveInterval X x)
  · exact Or.inl ⟨_, isLUB_csSup ⟨0, h0⟩ hup,
      tendsto_fst_maximalIntegralCurve_kepler_nhdsLT hm hκ x (isLUB_csSup ⟨0, h0⟩ hup)⟩
  · -- The interval of existence is not all of `ℝ`, so it is bounded below.
    have hlow : BddBelow (maximalIntegralCurveInterval X x) := by
      by_contra hlow
      exact (maximalIntegralCurveInterval_hamiltonianVectorField_kepler_eq_univ_iff hm hκ x).1
        (maximalIntegralCurveInterval_eq_univ_of_not_bddAbove_not_bddBelow hup hlow) hℓ
    exact Or.inr ⟨_, isGLB_csInf ⟨0, h0⟩ hlow,
      tendsto_fst_maximalIntegralCurve_kepler_nhdsGT hm hκ x (isGLB_csInf ⟨0, h0⟩ hlow)⟩

/-- **Bound motions with zero angular momentum collide in both directions of time.** For
`m, κ > 0`, the maximal integral curve of the Kepler Hamiltonian vector field on the punctured
phase space through a state of zero angular momentum and negative energy is defined only on a
bounded interval of times. By `TauCeti.tendsto_fst_maximalIntegralCurve_kepler_nhdsLT` and
`TauCeti.tendsto_fst_maximalIntegralCurve_kepler_nhdsGT`, the motion comes out of the collision
set and falls back into it. -/
theorem bddAbove_and_bddBelow_maximalIntegralCurveInterval_kepler (hm : 0 < m) (hκ : 0 < κ)
    (x : puncturedPhaseSpace V)
    (hℓ : ‖(x : V × V).1‖ ^ 2 * ‖(x : V × V).2‖ ^ 2 - ⟪(x : V × V).1, (x : V × V).2⟫_ℝ ^ 2 = 0)
    (hE : centralForceHamiltonian m (fun r ↦ -κ / r) (x : V × V) < 0) :
    BddAbove (maximalIntegralCurveInterval (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x) ∧
    BddBelow (maximalIntegralCurveInterval (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x) := by
  set X := SmoothTwoForm.hamiltonianVectorField
    (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtypeVal
      (stdSymplecticForm (V := V)).constSmooth)
    (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)
  have h0 := zero_mem_maximalIntegralCurveInterval (x := x)
    (contMDiff_hamiltonianVectorField_kepler (V := V) (m := m) (κ := κ)).contMDiffAt
  have hq := fst_maximalIntegralCurve_kepler_ne_zero (m := m) (κ := κ) x
  have hx : ((maximalIntegralCurve X x 0 : puncturedPhaseSpace V) : V × V) = x := by
    rw [maximalIntegralCurve_zero]
  refine ⟨by_contra fun hup ↦ ?_, by_contra fun hlow ↦ ?_⟩
  · -- A motion defined at all later times has nonnegative energy.
    have hIci : Ici 0 ⊆ maximalIntegralCurveInterval X x := fun t ht ↦ by
      obtain ⟨s, hs, hts⟩ := not_bddAbove_iff.1 hup t
      exact ordConnected_maximalIntegralCurveInterval.out h0 hs ⟨ht, hts.le⟩
    have h := centralForceHamiltonian_kepler_nonneg_of_forall_hasDerivAt hm hκ (a := 0)
      (fun t ht ↦ hasDerivAt_coe_maximalIntegralCurve_kepler x (hIci ht)) (fun t _ ↦ hq t)
      (by rw [hx]; exact hℓ)
    rw [hx] at h
    linarith
  · -- So does the reversed motion, if the motion is defined at all earlier times.
    have hIic : Iic 0 ⊆ maximalIntegralCurveInterval X x := fun t ht ↦ by
      obtain ⟨s, hs, hst⟩ := not_bddBelow_iff.1 hlow t
      exact ordConnected_maximalIntegralCurveInterval.out hs h0 ⟨hst.le, ht⟩
    have h := centralForceHamiltonian_kepler_nonneg_of_forall_hasDerivAt hm hκ (a := 0)
      (γ := fun s ↦ (((maximalIntegralCurve X x (-s) : puncturedPhaseSpace V) : V × V).1,
        -((maximalIntegralCurve X x (-s) : puncturedPhaseSpace V) : V × V).2))
      (fun t ht ↦ hasDerivAt_reverse_hamiltonianVectorField_centralForceHamiltonian
        (hasDerivAt_coe_maximalIntegralCurve_kepler x (hIic (neg_nonpos.2 ht))) (hq (-t))
        (differentiableAt_kepler_potential_maximalIntegralCurve x (-t)))
      (fun t _ ↦ hq (-t)) (by simpa [hx] using hℓ)
    simp only [neg_zero, hx, centralForceHamiltonian_apply, norm_neg] at h
    rw [← Prod.mk.eta (p := (x : V × V)), centralForceHamiltonian_apply] at hE
    linarith

end TauCeti
