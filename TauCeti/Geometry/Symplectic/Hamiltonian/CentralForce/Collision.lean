/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Integrable
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Radial
public import TauCeti.Geometry.Manifold.Flow.Complete
import TauCeti.Analysis.Convex.BddAbove
import TauCeti.Geometry.Symplectic.Hamiltonian.Complete
import TauCeti.Geometry.Symplectic.Manifold.Opens

/-!
# Collisions of central-force motions and the Kepler collision domain

A particle of mass `m > 0` in a finite-dimensional inner product space `V`, moving in a central
potential `U`, has the energy `H(q, p) = ‖p‖² / (2m) + U(‖q‖)` on the punctured phase space
`q ≠ 0` (`TauCeti.puncturedPhaseSpace`). This file determines which motions in the attractive
Kepler potential `U(r) = -κ / r`, `κ > 0`, reach the collision set `q = 0` in finite time: exactly
those with zero angular momentum. The squared angular momentum is
`ℓ² = ‖q‖² ‖p‖² - ⟪q, p⟫²`, the squared length of the bivector `q ∧ p`; in the plane it is the
square of `L = q₁p₂ - q₂p₁` (`TauCeti.sq_angularMomentum`).

* **Radial motions collide.** In any potential `U` with `U' > 0` on `r > 0`, so attractive at
  every distance, a motion with `ℓ = 0` cannot avoid the collision set for all time
  (`TauCeti.sq_sub_inner_sq_ne_zero_of_hasDerivAt`). For such a motion the distance `r = ‖q‖` and
  the radial momentum `p_r` solve `r' = p_r / m` and `p_r' = -U'(r) < 0`
  (`TauCeti.hasDerivAt_radialProjection_comp`). So `r` has a strictly decreasing derivative on all
  of `ℝ`: it is concave and not constant, hence not bounded below, while `r > 0`.
* **Nonradial Kepler motions never collide.** For `ℓ ≠ 0`, the perihelion bound
  `ℓ² ≤ ‖q‖ (m κ + ‖A‖)` (`TauCeti.sq_sub_inner_sq_le_norm_fst_mul_add_norm_rungeLenz`), for the
  Runge–Lenz vector `A`, keeps `‖q‖` away from zero, since `ℓ²` and
  `‖A‖² = (m κ)² + 2 m H ℓ²` are conserved. Energy conservation then bounds the momentum, so the
  position moves at bounded speed, and over every bounded time interval the motion stays in a
  compact subset of the punctured phase space. By the escape lemma for maximal integral curves
  (`maximalIntegralCurveInterval_eq_univ_of_forall_isCompact_mapsTo`) the motion is defined for
  all time. This holds at every energy, including the unbounded parabolic and hyperbolic motions
  with `H ≥ 0`.

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

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### Radial motions in an attractive potential -/

section Radial

variable [FiniteDimensional ℝ V]

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

end Radial

/-! ### The Kepler flow on the punctured phase space -/

section Kepler

variable {m κ : ℝ}

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
      (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtype_val
      (stdSymplecticForm (V := V)).constSmooth) :=
  (SymplecticForm.isNondegenerate_constSmooth _).mpullback_subtype_val _

/-- The Kepler Hamiltonian vector field on the punctured phase space is `C¹`. -/
private theorem contMDiff_hamiltonianVectorField_kepler :
    ContMDiff 𝓘(ℝ, V × V) 𝓘(ℝ, V × V).tangent 1
      (fun y ↦ (⟨y, SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtype_val
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val) y⟩ :
        TangentBundle 𝓘(ℝ, V × V) (puncturedPhaseSpace V))) :=
  isNondegenerate_puncturedPhaseSpace.contMDiff_hamiltonianVectorField (n := 1) (by simp)
    contMDiff_centralForceHamiltonian_kepler_comp_subtypeVal

/-- **Nonradial Kepler motions stay away from the collision set with bounded momentum.** Let `η`
be an integral curve of the Kepler Hamiltonian vector field on a preconnected set `J` of times
containing `0`, avoiding the collision set and conserving the energy, with nonzero angular
momentum at time `0`. Then on `J` the distance `‖q‖` to the origin is bounded below by a positive
constant `r₀`, by the perihelion bound and the conservation of the angular momentum and of the
length of the Runge–Lenz vector, and the momentum `‖p‖` is bounded, by energy conservation. -/
private theorem exists_pos_forall_le_norm_fst_and_norm_snd_le_kepler (hm : 0 < m) (hκ : 0 < κ)
    {J : Set ℝ} (hJ : IsPreconnected J) (h0 : (0 : ℝ) ∈ J) {η : ℝ → V × V}
    (hη : ∀ t ∈ J, HasDerivAt η ((stdSymplecticForm (V := V)).hamiltonianVectorField
      (centralForceHamiltonian m (fun r ↦ -κ / r)) (η t)) t)
    (hq : ∀ t ∈ J, (η t).1 ≠ 0)
    (hE : ∀ t ∈ J, centralForceHamiltonian m (fun r ↦ -κ / r) (η t) =
      centralForceHamiltonian m (fun r ↦ -κ / r) (η 0))
    (hℓ : ‖(η 0).1‖ ^ 2 * ‖(η 0).2‖ ^ 2 - ⟪(η 0).1, (η 0).2⟫_ℝ ^ 2 ≠ 0) :
    ∃ r₀ > 0, ∃ P, ∀ t ∈ J, r₀ ≤ ‖(η t).1‖ ∧ ‖(η t).2‖ ≤ P := by
  set E := centralForceHamiltonian m (fun r ↦ -κ / r) (η 0)
  set c := ‖(η 0).1‖ ^ 2 * ‖(η 0).2‖ ^ 2 - ⟪(η 0).1, (η 0).2⟫_ℝ ^ 2
  have hc : 0 < c := by
    refine lt_of_le_of_ne ?_ hℓ.symm
    have h := abs_real_inner_le_norm (η 0).1 (η 0).2
    nlinarith [sq_abs ⟪(η 0).1, (η 0).2⟫_ℝ, abs_nonneg ⟪(η 0).1, (η 0).2⟫_ℝ,
      mul_nonneg (norm_nonneg (η 0).1) (norm_nonneg (η 0).2)]
  -- The angular momentum and the length of the Runge–Lenz vector are conserved.
  have hℓt (t : ℝ) (ht : t ∈ J) : ‖(η t).1‖ ^ 2 * ‖(η t).2‖ ^ 2 - ⟪(η t).1, (η t).2⟫_ℝ ^ 2 = c :=
    sq_sub_inner_sq_eq_of_hasDerivAt hJ hη h0 ht
  have hA (t : ℝ) (ht : t ∈ J) : ‖rungeLenz m κ (η t)‖ = ‖rungeLenz m κ (η 0)‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by
      rw [norm_rungeLenz_sq hm.ne' κ (hq t ht), norm_rungeLenz_sq hm.ne' κ (hq 0 h0), hE t ht,
        hℓt t ht])
  -- The perihelion bound keeps the distance to the origin at least `r₀`.
  set r₀ := c / (m * κ + ‖rungeLenz m κ (η 0)‖)
  have hr₀ : 0 < r₀ := div_pos hc (by positivity)
  have hr (t : ℝ) (ht : t ∈ J) : r₀ ≤ ‖(η t).1‖ := by
    rw [div_le_iff₀ (by positivity)]
    have h := sq_sub_inner_sq_le_norm_fst_mul_add_norm_rungeLenz m κ (η t)
    rwa [hℓt t ht, hA t ht] at h
  -- Energy conservation then bounds the momentum.
  refine ⟨r₀, hr₀, √(2 * m * (E + κ / r₀)), fun t ht ↦ ⟨hr t ht, ?_⟩⟩
  have hH := hE t ht
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
    (hE : ∀ t ∈ J, centralForceHamiltonian m (fun r ↦ -κ / r) (η t) =
      centralForceHamiltonian m (fun r ↦ -κ / r) (η 0))
    (hℓ : ‖(η 0).1‖ ^ 2 * ‖(η 0).2‖ ^ 2 - ⟪(η 0).1, (η 0).2⟫_ℝ ^ 2 ≠ 0) (T : ℝ) :
    ∃ K : Set (V × V), IsCompact K ∧ (∀ y ∈ K, y.1 ≠ 0) ∧ ∀ t ∈ J ∩ Icc (-T) T, η t ∈ K := by
  obtain ⟨r₀, hr₀, P, hb⟩ :=
    exists_pos_forall_le_norm_fst_and_norm_snd_le_kepler hm hκ hJ h0 hη hq hE hℓ
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
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtype_val
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x) :
    HasDerivAt (fun s ↦ ((maximalIntegralCurve (SmoothTwoForm.hamiltonianVectorField
        (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V)
          contMDiff_subtype_val (stdSymplecticForm (V := V)).constSmooth)
        (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x s :
          puncturedPhaseSpace V) : V × V))
      ((stdSymplecticForm (V := V)).hamiltonianVectorField
        (centralForceHamiltonian m (fun r ↦ -κ / r))
        ((maximalIntegralCurve (SmoothTwoForm.hamiltonianVectorField
          (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V)
            contMDiff_subtype_val (stdSymplecticForm (V := V)).constSmooth)
          (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x t :
            puncturedPhaseSpace V) : V × V)) t := by
  -- The inclusion carries the restricted Hamiltonian vector field to the ambient one.
  have hγ := (isMIntegralCurveOn_maximalIntegralCurve
    (contMDiff_hamiltonianVectorField_kepler (m := m) (κ := κ)) (x := x)).map_of_mfderiv_eq
    (f := Subtype.val)
    (W := (stdSymplecticForm (V := V)).constSmooth.hamiltonianVectorField
      (centralForceHamiltonian m (fun r ↦ -κ / r)))
    (fun _ _ ↦ (contMDiff_subtype_val (n := 1)).mdifferentiableAt one_ne_zero) fun s _ ↦ by
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
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtype_val
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x = univ := by
  set X := SmoothTwoForm.hamiltonianVectorField
    (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtype_val
      (stdSymplecticForm (V := V)).constSmooth)
    (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)
  have hv := contMDiff_hamiltonianVectorField_kepler (V := V) (m := m) (κ := κ)
  have h0 := zero_mem_maximalIntegralCurveInterval (x := x) hv.contMDiffAt
  refine maximalIntegralCurveInterval_eq_univ_of_forall_isCompact_mapsTo hv fun T ↦ ?_
  -- The energy is a first integral of itself, so it is constant along the maximal curve.
  have hE (t : ℝ) (ht : t ∈ maximalIntegralCurveInterval X x) :
      centralForceHamiltonian m (fun r ↦ -κ / r)
          ((maximalIntegralCurve X x t : puncturedPhaseSpace V) : V × V) =
        centralForceHamiltonian m (fun r ↦ -κ / r)
          ((maximalIntegralCurve X x 0 : puncturedPhaseSpace V) : V × V) := by
    rw [maximalIntegralCurve_zero]
    exact (SmoothTwoForm.isFirstIntegral_self _).apply_maximalIntegralCurve
      isNondegenerate_puncturedPhaseSpace contMDiff_centralForceHamiltonian_kepler_comp_subtypeVal
      ((contMDiff_centralForceHamiltonian_kepler_comp_subtypeVal (n := 1)).mdifferentiable
        one_ne_zero) ht
  obtain ⟨K, hK, hK0, hmem⟩ := exists_isCompact_forall_mem_of_hasDerivAt_kepler hm hκ
    isPreconnected_maximalIntegralCurveInterval h0
    (fun t ht ↦ hasDerivAt_coe_maximalIntegralCurve_kepler x ht)
    (fun t _ ↦ mem_puncturedPhaseSpace.1 (maximalIntegralCurve _ x t).2) hE
    (by rwa [maximalIntegralCurve_zero]) T
  refine ⟨Subtype.val ⁻¹' K, ?_, fun t ht ↦ hmem t ht⟩
  rwa [Subtype.isCompact_iff, image_preimage_eq_of_subset fun y hy ↦
    ⟨⟨y, mem_puncturedPhaseSpace.2 (hK0 y hy)⟩, rfl⟩]

/-- **The collision domain of the Kepler problem.** For `m, κ > 0`, the maximal integral curve of
the Kepler Hamiltonian vector field on the punctured phase space through a state is defined for
all time exactly when the angular momentum of the state is nonzero,
`‖q‖² ‖p‖² - ⟪q, p⟫² ≠ 0`. Every motion with zero angular momentum reaches the collision set
`q = 0` in finite time, forwards or backwards. -/
theorem maximalIntegralCurveInterval_hamiltonianVectorField_kepler_eq_univ_iff (hm : 0 < m)
    (hκ : 0 < κ) (x : puncturedPhaseSpace V) :
    maximalIntegralCurveInterval (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtype_val
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x = univ ↔
      ‖(x : V × V).1‖ ^ 2 * ‖(x : V × V).2‖ ^ 2 - ⟪(x : V × V).1, (x : V × V).2⟫_ℝ ^ 2 ≠ 0 := by
  refine ⟨fun h ↦ ?_, maximalIntegralCurveInterval_hamiltonianVectorField_kepler_eq_univ hm hκ x⟩
  -- A global maximal curve is a global solution of Hamilton's equations avoiding the collision set,
  -- which the attractive Kepler force rules out for zero angular momentum.
  have hU (r : ℝ) (hr : 0 < r) := hasDerivAt_kepler_potential κ hr.ne'
  have h' := sq_sub_inner_sq_ne_zero_of_hasDerivAt hm
    (fun r hr ↦ by rw [(hU r hr).deriv]; positivity)
    (fun t ↦ hasDerivAt_coe_maximalIntegralCurve_kepler x (h ▸ mem_univ t))
    (fun t ↦ mem_puncturedPhaseSpace.1 (maximalIntegralCurve _ x t).2) 0
  rwa [maximalIntegralCurve_zero] at h'

/-- **The collision domain of the planar Kepler problem.** In the plane, with angular momentum
`L = q₁p₂ - q₂p₁` in an orthonormal basis `b`, the maximal integral curve of the Kepler Hamiltonian
vector field on the punctured phase space through a state is defined for all time exactly when
`L ≠ 0`. -/
theorem maximalIntegralCurveInterval_hamiltonianVectorField_kepler_eq_univ_iff_angularMomentum
    (b : OrthonormalBasis (Fin 2) ℝ V) (hm : 0 < m) (hκ : 0 < κ) (x : puncturedPhaseSpace V) :
    maximalIntegralCurveInterval (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtype_val
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) x = univ ↔
      angularMomentum (b 0) (b 1) x ≠ 0 := by
  rw [maximalIntegralCurveInterval_hamiltonianVectorField_kepler_eq_univ_iff hm hκ,
    ← sq_angularMomentum b, pow_ne_zero_iff two_ne_zero]

/-- **The Kepler flow is not complete.** For `m, κ > 0` and a nontrivial space `V`, the Kepler
Hamiltonian vector field on the punctured phase space is not complete: a particle released at rest
falls into the centre in finite time. -/
theorem not_isCompleteVectorField_hamiltonianVectorField_kepler [Nontrivial V] (hm : 0 < m)
    (hκ : 0 < κ) :
    ¬ IsCompleteVectorField (SmoothTwoForm.hamiltonianVectorField
      (SmoothForm.mpullback (Subtype.val : puncturedPhaseSpace V → V × V) contMDiff_subtype_val
        (stdSymplecticForm (V := V)).constSmooth)
      (centralForceHamiltonian m (fun r ↦ -κ / r) ∘ Subtype.val)) := by
  intro h
  obtain ⟨q, hq⟩ := exists_ne (0 : V)
  have h' := (maximalIntegralCurveInterval_hamiltonianVectorField_kepler_eq_univ_iff hm hκ
    ⟨(q, 0), mem_puncturedPhaseSpace.2 hq⟩).1 (h.maximalIntegralCurveInterval_eq_univ _)
  simp at h'

end Kepler

end TauCeti
