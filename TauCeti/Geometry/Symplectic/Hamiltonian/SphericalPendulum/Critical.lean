/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.PhaseSpace
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Critical points and critical values of the spherical pendulum

Give the phase space `T*S² = {(q, p) : ‖q‖ = 1, ⟪q, p⟫ = 0}` of the spherical pendulum its
structure of a smooth four-manifold, the regular level over `(1, 0)` of the constraint map
`g(q, p) = (‖q‖², ⟪q, p⟫)`. This file determines the critical points and the critical values of
the energy–momentum map `F = (H, J)` restricted to it, `H = ‖p‖² / 2 + q₃` and
`J = q₁ p₂ - q₂ p₁`.

A point `x` is a regular point of `F` on the phase space exactly when `dF_x` maps the tangent
space `ker dg_x` onto `ℝ²` (`TauCeti.isRegularPoint_sphericalPendulumEnergyMomentum_iff`). If it
does not, some nonzero `(l, m)` has `l dH + m dJ` vanishing on `ker dg`, so by the method of
Lagrange multipliers `l dH + m dJ = a dg₁ + b dg₂` on `ℝ³ × ℝ³`. Solving these six linear
equations, the critical points are

* the two equilibria at rest at the poles, `q = (0, 0, ±1)` and `p = 0`, where `dF` vanishes on the
  tangent space;
* the relative equilibria: the horizontal circular motions, with `p₃ = 0`, at a height `z` and
  vertical angular momentum `j ≠ 0` related by `j² z + (1 - z²)² = 0`. These are exactly the
  points where `z` is the minimum `z_j` of the effective potential
  `V_j(z) = j² / (2 (1 - z²)) + z` on `(-1, 1)`, and `r (r dH - J dJ)` vanishes on the tangent
  space there, `r = 1 - z²`

(`TauCeti.not_isRegularPoint_sphericalPendulumEnergyMomentum_iff`). Accordingly the critical
values are `(-1, 0)`, `(1, 0)` and the curve `{(min V_j, j) : j ≠ 0}` of relative equilibria
(`TauCeti.image_setOf_not_isRegularPoint_sphericalPendulumEnergyMomentum`), which bounds the image
of `F` from below. The value `(1, 0)` of the unstable equilibrium, classically the focus–focus
value of the pendulum, is isolated among the critical values: every other value near it is regular
(`TauCeti.eventually_isRegularValue_sphericalPendulumEnergyMomentum_nhdsNE`), since
`min V_j ≤ V_j(0) = j² / 2`. It lies in the interior of the image of `F`
(`TauCeti.mem_interior_image_sphericalPendulumEnergyMomentum`).

## Main results

* `TauCeti.fderiv_sphericalPendulumEnergyMomentum_apply`: the differential of `F`.
* `TauCeti.isRegularPoint_sphericalPendulumEnergyMomentum_iff`: regular points of `F` on the phase
  space, through the tangent space `ker dg`.
* `TauCeti.not_isRegularPoint_sphericalPendulumEnergyMomentum_iff`: the critical points.
* `TauCeti.image_setOf_not_isRegularPoint_sphericalPendulumEnergyMomentum` and
  `TauCeti.isRegularValue_sphericalPendulumEnergyMomentum_iff`: the critical and regular values.
* `TauCeti.eventually_isRegularValue_sphericalPendulumEnergyMomentum_nhdsNE` and
  `TauCeti.mem_interior_image_sphericalPendulumEnergyMomentum`: the value `(1, 0)` is an isolated
  critical value in the interior of the image.

## References

* R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, 2nd ed.,
  Birkhäuser, 2015, Chapter IV (the spherical pendulum, its critical values and the
  relative equilibria).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 15.
-/

public section

open Function Module Set
open scoped InnerProductSpace Manifold ContDiff Topology

namespace TauCeti

/-! ### The differential of the energy–momentum map -/

/-- The energy–momentum map in coordinates. -/
private theorem sphericalPendulumEnergyMomentum_eq_fun :
    sphericalPendulumEnergyMomentum = fun y ↦
      (‖y.2‖ ^ 2 * (1 / 2) + y.1 2, y.1 0 * y.2 1 - y.1 1 * y.2 0) := by
  funext ⟨q, p⟩
  rw [sphericalPendulumEnergyMomentum_apply, Prod.mk.injEq]
  exact ⟨by ring, rfl⟩

/-- A coordinate function of the position. -/
private theorem hasFDerivAt_coord_fst (i : Fin 3)
    (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) ↦ y.1 i)
      ((innerSL ℝ (EuclideanSpace.single i 1)).comp (ContinuousLinearMap.fst ℝ _ _)) x := by
  refine (ContinuousLinearMap.hasFDerivAt _).congr_of_eventuallyEq (.of_forall fun y ↦ ?_)
  simp [EuclideanSpace.inner_single_left]

/-- A coordinate function of the momentum. -/
private theorem hasFDerivAt_coord_snd (i : Fin 3)
    (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) ↦ y.2 i)
      ((innerSL ℝ (EuclideanSpace.single i 1)).comp (ContinuousLinearMap.snd ℝ _ _)) x := by
  refine (ContinuousLinearMap.hasFDerivAt _).congr_of_eventuallyEq (.of_forall fun y ↦ ?_)
  simp [EuclideanSpace.inner_single_left]

/-- The energy–momentum map of the spherical pendulum is smooth on `ℝ³ × ℝ³`. -/
theorem contDiff_sphericalPendulumEnergyMomentum {n : WithTop ℕ∞} :
    ContDiff ℝ n sphericalPendulumEnergyMomentum := by
  have h1 (i : Fin 3) : ContDiff ℝ n
      fun y : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) ↦ y.1 i := by
    convert ((innerSL ℝ (EuclideanSpace.single i (1 : ℝ))).comp
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)))).contDiff
      using 1
    funext; simp [EuclideanSpace.inner_single_left]
  have h2 (i : Fin 3) : ContDiff ℝ n
      fun y : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) ↦ y.2 i := by
    convert ((innerSL ℝ (EuclideanSpace.single i (1 : ℝ))).comp
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)))).contDiff
      using 1
    funext; simp [EuclideanSpace.inner_single_left]
  rw [sphericalPendulumEnergyMomentum_eq_fun]
  exact ((((contDiff_norm_sq ℝ).comp contDiff_snd).mul contDiff_const).add (h1 2)).prodMk
    (((h1 0).mul (h2 1)).sub ((h1 1).mul (h2 0)))

/-- The differential of the energy–momentum map: `dH (a, b) = ⟪p, b⟫ + a₃` and
`dJ (a, b) = a₁ p₂ - a₂ p₁ + q₁ b₂ - q₂ b₁`. -/
theorem fderiv_sphericalPendulumEnergyMomentum_apply
    (x v : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ sphericalPendulumEnergyMomentum x v =
      (⟪x.2, v.2⟫_ℝ + v.1 2, v.1 0 * x.2 1 - v.1 1 * x.2 0 + x.1 0 * v.2 1 - x.1 1 * v.2 0) := by
  have hp : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) ↦ ‖y.2‖ ^ 2)
      _ x := (hasStrictFDerivAt_norm_sq x.2).hasFDerivAt.comp x hasFDerivAt_snd
  have h : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) ↦
      (‖y.2‖ ^ 2 * (1 / 2) + y.1 2, y.1 0 * y.2 1 - y.1 1 * y.2 0)) _ x :=
    ((hp.mul_const (1 / 2 : ℝ)).add (hasFDerivAt_coord_fst 2 x)).prodMk
    (((hasFDerivAt_coord_fst 0 x).mul (hasFDerivAt_coord_snd 1 x)).sub
      ((hasFDerivAt_coord_fst 1 x).mul (hasFDerivAt_coord_snd 0 x)))
  rw [sphericalPendulumEnergyMomentum_eq_fun, h.fderiv]
  simp [EuclideanSpace.inner_single_left]
  ring

/-- A point of the phase space is a regular point of the energy–momentum map `F = (H, J)` on the
phase space exactly when the differential of `F` maps the tangent space `ker dg` onto `ℝ²`. -/
theorem isRegularPoint_sphericalPendulumEnergyMomentum_iff (x : sphericalPendulumPhaseSpace) :
    IsRegularPoint 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, ℝ × ℝ)
        (fun y : sphericalPendulumPhaseSpace ↦ sphericalPendulumEnergyMomentum y) x ↔
      (fderiv ℝ sphericalPendulumConstraint x).ker.map
        (fderiv ℝ sphericalPendulumEnergyMomentum x : _ →ₗ[ℝ] ℝ × ℝ) = ⊤ := by
  have hval := isSmoothEmbedding_coe_sphericalPendulumPhaseSpace.contMDiff.mdifferentiableAt
    (x := x) (by simp)
  have hF : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
      𝓘(ℝ, ℝ × ℝ) sphericalPendulumEnergyMomentum x :=
    (contDiff_sphericalPendulumEnergyMomentum (n := 1)).contMDiff.mdifferentiableAt one_ne_zero
  have hF' (z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, ℝ × ℝ)
        sphericalPendulumEnergyMomentum x z = fderiv ℝ sphericalPendulumEnergyMomentum x z := by
    rw [mfderiv_eq_fderiv]
    -- The two identifications `NormedSpace.fromTangentSpace` are the identity on vectors
    -- (`NormedSpace.fromTangentSpace_apply`); `simp` cannot rewrite across the tangent fibres.
    rfl
  have hrange := range_mfderiv_coe_sphericalPendulumPhaseSpace x
  have hcomp : (fun y : sphericalPendulumPhaseSpace ↦ sphericalPendulumEnergyMomentum y) =
      sphericalPendulumEnergyMomentum ∘ Subtype.val := rfl
  rw [isRegularPoint_iff, hcomp, mfderiv_comp x hF hval, ContinuousLinearMap.coe_comp]
  constructor
  · intro hs
    refine Submodule.eq_top_iff'.2 fun w ↦ ?_
    obtain ⟨u, hu⟩ := hs w
    refine ⟨_, hrange ▸ LinearMap.mem_range_self _ u, ?_⟩
    rw [← hu]
    exact (hF' _).symm
  · intro htop w
    -- `w` lives in the tangent space of `ℝ × ℝ`; read it as a vector of `ℝ × ℝ`.
    let w' : ℝ × ℝ := w
    have hw : w' ∈ (⊤ : Submodule ℝ (ℝ × ℝ)) := Submodule.mem_top
    rw [← htop] at hw
    obtain ⟨v, hv, hvw⟩ := Submodule.mem_map.1 hw
    rw [← hrange] at hv
    obtain ⟨u, rfl⟩ := hv
    exact ⟨u, (hF' _).trans hvw⟩

/-! ### Critical points -/

/-- **The Lagrange multiplier equations.** If `l dH + m dJ = a dg₁ + b dg₂` on `ℝ³ × ℝ³` at a
point of the phase space, with `(l, m) ≠ 0`, then the point is at rest at a pole, or it has
vanishing vertical momentum and `J² q₃ + (1 - q₃²)² = 0` with `J = q₁ p₂ - q₂ p₁ ≠ 0`. The
hypotheses are the six coordinates of the multiplier equation. -/
private theorem lagrange_cases {q0 q1 q2 p0 p1 p2 l m a b : ℝ}
    (hq : q0 ^ 2 + q1 ^ 2 + q2 ^ 2 = 1) (hqp : q0 * p0 + q1 * p1 + q2 * p2 = 0)
    (hlm : l ≠ 0 ∨ m ≠ 0)
    (ea0 : m * p1 = a * (2 * q0) + b * p0) (ea1 : -(m * p0) = a * (2 * q1) + b * p1)
    (ea2 : l = a * (2 * q2) + b * p2)
    (eb0 : l * p0 - m * q1 = b * q0) (eb1 : l * p1 + m * q0 = b * q1) (eb2 : l * p2 = b * q2) :
    (p0 = 0 ∧ p1 = 0 ∧ p2 = 0 ∧ q2 ^ 2 = 1) ∨
      (q0 * p1 - q1 * p0 ≠ 0 ∧ p2 = 0 ∧ (q0 * p1 - q1 * p0) ^ 2 * q2 + (1 - q2 ^ 2) ^ 2 = 0) := by
  have hb : b = 0 := by linear_combination -(q0 * eb0) - q1 * eb1 - q2 * eb2 + l * hqp - b * hq
  subst hb
  by_cases hl : l = 0
  · subst hl
    have hm : m ≠ 0 := hlm.resolve_left (not_not.2 rfl)
    have hq1 : q1 = 0 := by
      have : m * q1 = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hm
    have hq0 : q0 = 0 := by
      have : m * q0 = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hm
    subst hq0 hq1
    have hp1 : p1 = 0 := (mul_eq_zero.1 (by linarith : m * p1 = 0)).resolve_left hm
    have hp0 : p0 = 0 := (mul_eq_zero.1 (by linarith : m * p0 = 0)).resolve_left hm
    have hq2 : q2 ^ 2 = 1 := by linarith
    have hq2' : q2 ≠ 0 := by rintro rfl; norm_num at hq2
    have hp2 : p2 = 0 := (mul_eq_zero.1 (by linarith : q2 * p2 = 0)).resolve_left hq2'
    exact Or.inl ⟨hp0, hp1, hp2, hq2⟩
  · have hp2 : p2 = 0 := (mul_eq_zero.1 (by linarith : l * p2 = 0)).resolve_left hl
    subst hp2
    by_cases hr : q0 ^ 2 + q1 ^ 2 = 0
    · have hq0 : q0 = 0 := by nlinarith [sq_nonneg q0, sq_nonneg q1]
      have hq1 : q1 = 0 := by nlinarith [sq_nonneg q0, sq_nonneg q1]
      subst hq0 hq1
      have hp0 : p0 = 0 := (mul_eq_zero.1 (by linarith : l * p0 = 0)).resolve_left hl
      have hp1 : p1 = 0 := (mul_eq_zero.1 (by linarith : l * p1 = 0)).resolve_left hl
      exact Or.inl ⟨hp0, hp1, rfl, by linarith⟩
    · right
      set J := q0 * p1 - q1 * p0 with hJdef
      set r := q0 ^ 2 + q1 ^ 2 with hrdef
      have hJ : l * J = -(m * r) := by linear_combination q0 * eb1 - q1 * eb0
      have hα : m * J = 2 * a * r := by linear_combination q0 * ea0 + q1 * ea1
      have h1 : r * (l ^ 2 + m ^ 2 * q2) = 0 := by
        linear_combination r * l * ea2 - l * q2 * hα + m * q2 * hJ
      have h2 : l ^ 2 + m ^ 2 * q2 = 0 := (mul_eq_zero.1 h1).resolve_left hr
      have hr' : r = 1 - q2 ^ 2 := by linarith
      have h3 : l ^ 2 * (J ^ 2 * q2 + r ^ 2) = 0 := by
        linear_combination (l * J * q2 - m * r * q2) * hJ + r ^ 2 * h2
      refine ⟨fun hJ0 ↦ ?_, rfl, ?_⟩
      · rw [hJ0, mul_zero, zero_eq_neg] at hJ
        have hm : m = 0 := (mul_eq_zero.1 hJ).resolve_right hr
        rw [hm] at h2
        exact hl (pow_eq_zero_iff two_ne_zero |>.1 (by linarith))
      · rw [← hr']
        exact (mul_eq_zero.1 h3).resolve_left (pow_ne_zero 2 hl)

/-- In coordinates, the differentials of the constraint map and of the energy–momentum map. -/
private theorem fderiv_coords (q p a b : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ sphericalPendulumConstraint (q, p) (a, b) =
        (2 * (q 0 * a 0 + q 1 * a 1 + q 2 * a 2),
          q 0 * b 0 + q 1 * b 1 + q 2 * b 2 + (a 0 * p 0 + a 1 * p 1 + a 2 * p 2)) ∧
      fderiv ℝ sphericalPendulumEnergyMomentum (q, p) (a, b) =
        (p 0 * b 0 + p 1 * b 1 + p 2 * b 2 + a 2,
          a 0 * p 1 - a 1 * p 0 + q 0 * b 1 - q 1 * b 0) := by
  rw [fderiv_sphericalPendulumConstraint_apply, fderiv_sphericalPendulumEnergyMomentum_apply]
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  refine ⟨Prod.ext ?_ ?_, Prod.ext ?_ ?_⟩ <;> dsimp only <;> ring

/-- The coordinates of the constraints `‖q‖² = 1` and `⟪q, p⟫ = 0`. -/
private theorem coords_of_mem_sphericalPendulumPhaseSpace {q p : EuclideanSpace ℝ (Fin 3)}
    (hx : (q, p) ∈ sphericalPendulumPhaseSpace) :
    q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 = 1 ∧ q 0 * p 0 + q 1 * p 1 + q 2 * p 2 = 0 := by
  obtain ⟨hq, hqp⟩ := mem_sphericalPendulumPhaseSpace.1 hx
  have hq2 := EuclideanSpace.real_norm_sq_eq q
  rw [hq, one_pow, Fin.sum_univ_three] at hq2
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] at hqp
  exact ⟨hq2.symm, by linear_combination hqp⟩

/-- Points of the phase space with nonzero vertical angular momentum are away from the poles. -/
private theorem apply_two_mem_Ioo_of_snd_ne_zero
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ sphericalPendulumPhaseSpace) (hJ : (sphericalPendulumEnergyMomentum x).2 ≠ 0) :
    x.1 2 ∈ Ioo (-1) 1 :=
  ((sq_lt_one_iff_abs_lt_one _).trans abs_lt).1 <| lt_of_le_of_ne
    (by nlinarith [(apply_two_mem_Icc_of_mem_sphericalPendulumPhaseSpace hx).1,
      (apply_two_mem_Icc_of_mem_sphericalPendulumPhaseSpace hx).2])
    fun h1 ↦ hJ (snd_sphericalPendulumEnergyMomentum_eq_zero_of_sq_eq_one hx h1)

/-- **Lagrange multipliers.** If `dF` does not map the tangent space `ker dg` of the phase space
onto `ℝ²` at `(q, p)`, then some `(l, m) ≠ 0` and `(a, b)` satisfy `l dH + m dJ = a dg₁ + b dg₂`
on `ℝ³ × ℝ³`, and the point is at rest at a pole or is a relative equilibrium. -/
private theorem pole_or_relativeEquilibrium_of_map_ne_top {q p : EuclideanSpace ℝ (Fin 3)}
    (hx : (q, p) ∈ sphericalPendulumPhaseSpace)
    (hne : (fderiv ℝ sphericalPendulumConstraint (q, p)).ker.map
      (fderiv ℝ sphericalPendulumEnergyMomentum (q, p) : _ →ₗ[ℝ] ℝ × ℝ) ≠ ⊤) :
    (p = 0 ∧ q 2 ^ 2 = 1) ∨ (q 0 * p 1 - q 1 * p 0 ≠ 0 ∧ p 2 = 0 ∧
      (q 0 * p 1 - q 1 * p 0) ^ 2 * q 2 + (1 - q 2 ^ 2) ^ 2 = 0) := by
  obtain ⟨hq, hqp⟩ := coords_of_mem_sphericalPendulumPhaseSpace hx
  -- A nonzero functional `f = l (·).1 + m (·).2` on `ℝ²` kills `dF (ker dg)`.
  obtain ⟨f, hf0, hf⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  set D : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ × ℝ :=
    (fderiv ℝ sphericalPendulumConstraint (q, p)).toLinearMap with hDdef
  set DF : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ × ℝ :=
    (fderiv ℝ sphericalPendulumEnergyMomentum (q, p)).toLinearMap with hDFdef
  have hK : ⨅ i, LinearMap.ker
      (![LinearMap.fst ℝ ℝ ℝ ∘ₗ D, LinearMap.snd ℝ ℝ ℝ ∘ₗ D] i) ≤
        LinearMap.ker (f ∘ₗ DF) := by
    intro v hv
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, Fin.forall_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, LinearMap.coe_comp, comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply] at hv
    have hv' : v ∈ D.ker := Prod.ext hv.1 hv.2
    have hmem : f (DF v) ∈ (D.ker.map DF).map f :=
      ⟨DF v, ⟨v, hv', rfl⟩, rfl⟩
    rw [hf, Submodule.mem_bot] at hmem
    exact hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (mem_span_of_iInf_ker_le_ker hK)
  have hf' (w : ℝ × ℝ) : f w = f (1, 0) * w.1 + f (0, 1) * w.2 := by
    conv_lhs => rw [show w = w.1 • ((1 : ℝ), (0 : ℝ)) + w.2 • ((0 : ℝ), (1 : ℝ)) by
      ext <;> simp]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm, mul_comm w.2]
  have hlm : f (1, 0) ≠ 0 ∨ f (0, 1) ≠ 0 := by
    by_contra! h
    exact hf0 (LinearMap.ext fun w ↦ by rw [hf', h.1, h.2]; simp)
  have hev (a b : EuclideanSpace ℝ (Fin 3)) :
      c 0 * (2 * (q 0 * a 0 + q 1 * a 1 + q 2 * a 2)) +
          c 1 * (q 0 * b 0 + q 1 * b 1 + q 2 * b 2 + (a 0 * p 0 + a 1 * p 1 + a 2 * p 2)) =
        f (1, 0) * (p 0 * b 0 + p 1 * b 1 + p 2 * b 2 + a 2) +
          f (0, 1) * (a 0 * p 1 - a 1 * p 0 + q 0 * b 1 - q 1 * b 0) := by
    have h := LinearMap.congr_fun hc (a, b)
    obtain ⟨hD, hDF⟩ := fderiv_coords q p a b
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.coe_comp, comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, ContinuousLinearMap.coe_coe, smul_eq_mul, hDdef, hDFdef, hD, hDF] at h
    rw [h, hf']
  have ea0 := hev (EuclideanSpace.single 0 1) 0
  have ea1 := hev (EuclideanSpace.single 1 1) 0
  have ea2 := hev (EuclideanSpace.single 2 1) 0
  have eb0 := hev 0 (EuclideanSpace.single 0 1)
  have eb1 := hev 0 (EuclideanSpace.single 1 1)
  have eb2 := hev 0 (EuclideanSpace.single 2 1)
  simp at ea0 ea1 ea2 eb0 eb1 eb2
  -- The six coordinates of the multiplier equation.
  have ea0 := hev (EuclideanSpace.single 0 1) 0
  have ea1 := hev (EuclideanSpace.single 1 1) 0
  have ea2 := hev (EuclideanSpace.single 2 1) 0
  have eb0 := hev 0 (EuclideanSpace.single 0 1)
  have eb1 := hev 0 (EuclideanSpace.single 1 1)
  have eb2 := hev 0 (EuclideanSpace.single 2 1)
  simp at ea0 ea1 ea2 eb0 eb1 eb2
  rcases lagrange_cases (a := c 0) (b := c 1) hq hqp hlm (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) with
    ⟨hp0, hp1, hp2, hq2⟩ | h
  · refine Or.inl ⟨?_, hq2⟩
    ext i
    fin_cases i <;> simp [hp0, hp1, hp2]
  · exact Or.inr h

/-- At a pole at rest, and at a relative equilibrium, `dF` does not map the tangent space
`ker dg` onto `ℝ²`: no tangent vector is sent to `(1, 0)`. -/
private theorem map_ne_top_of_pole_or_relativeEquilibrium {q p : EuclideanSpace ℝ (Fin 3)}
    (hx : (q, p) ∈ sphericalPendulumPhaseSpace)
    (hcase : (p = 0 ∧ q 2 ^ 2 = 1) ∨ (q 0 * p 1 - q 1 * p 0 ≠ 0 ∧ p 2 = 0 ∧
      (q 0 * p 1 - q 1 * p 0) ^ 2 * q 2 + (1 - q 2 ^ 2) ^ 2 = 0)) :
    (fderiv ℝ sphericalPendulumConstraint (q, p)).ker.map
      (fderiv ℝ sphericalPendulumEnergyMomentum (q, p) : _ →ₗ[ℝ] ℝ × ℝ) ≠ ⊤ := by
  obtain ⟨hq, hqp⟩ := coords_of_mem_sphericalPendulumPhaseSpace hx
  intro htop
  -- At a critical point no tangent vector has image `(1, 0)` under `dF`.
  have hw : ((1 : ℝ), (0 : ℝ)) ∈ (⊤ : Submodule ℝ (ℝ × ℝ)) := Submodule.mem_top
  rw [← htop] at hw
  obtain ⟨⟨a, b⟩, hv, hvw⟩ := Submodule.mem_map.1 hw
  obtain ⟨hD, hDF⟩ := fderiv_coords q p a b
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hD, Prod.mk_eq_zero] at hv
  rw [ContinuousLinearMap.coe_coe, hDF, Prod.mk.injEq] at hvw
  rcases hcase with ⟨hp, hq2⟩ | ⟨hJ0, hp2, hcrit⟩
  · -- At a pole at rest, `dH (a, b) = a₃` vanishes on the tangent space.
    have hq0 : q 0 = 0 := by nlinarith [sq_nonneg (q 0), sq_nonneg (q 1)]
    have hq1 : q 1 = 0 := by nlinarith [sq_nonneg (q 0), sq_nonneg (q 1)]
    have hq2' : q 2 ≠ 0 := by rintro h; rw [h] at hq2; norm_num at hq2
    simp only [hp, PiLp.zero_apply, zero_mul, zero_add, hq0, hq1] at hv hvw
    exact hq2' (by nlinarith [hv.1, hvw.1])
  · -- At a relative equilibrium, `r (r dH - J dJ) = 0` on the tangent space, `r = 1 - q₃²`.
    rw [hp2] at hqp hvw
    have hr : q 0 ^ 2 + q 1 ^ 2 = 1 - q 2 ^ 2 := by linarith
    have hK : (q 0 * p 1 - q 1 * p 0) ^ 2 * q 2 + (q 0 ^ 2 + q 1 ^ 2) ^ 2 = 0 := by
      rw [hr]
      exact hcrit
    have key : (q 0 ^ 2 + q 1 ^ 2) * (q 0 ^ 2 + q 1 ^ 2) = 0 := by
      linear_combination ((q 0 ^ 2 + q 1 ^ 2) * b 0 * q 0 + (q 0 ^ 2 + q 1 ^ 2) * b 1 * q 1 -
        (q 0 * p 1 - q 1 * p 0) * (a 0 * q 1 - a 1 * q 0)) * hqp -
        (q 0 * p 1 - q 1 * p 0) ^ 2 / 2 * hv.1 + a 2 * hK -
        (q 0 ^ 2 + q 1 ^ 2) ^ 2 * hvw.1 + (q 0 ^ 2 + q 1 ^ 2) * (q 0 * p 1 - q 1 * p 0) * hvw.2
    -- So `q₁ = q₂ = 0`, which would force `J = 0`.
    have hr0 := mul_self_eq_zero.1 key
    have hq0 : q 0 = 0 := by nlinarith [sq_nonneg (q 0), sq_nonneg (q 1)]
    have hq1 : q 1 = 0 := by nlinarith [sq_nonneg (q 0), sq_nonneg (q 1)]
    exact hJ0 (by rw [hq0, hq1]; ring)


/-- **The critical points of the spherical pendulum.** A point of the phase space is a critical
point of the energy–momentum map `F = (H, J)` exactly when it is an equilibrium at rest at one of
the poles, or a relative equilibrium: a horizontal circular motion with vertical angular momentum
`j ≠ 0` at the height `z_j` minimizing the effective potential `V_j` on `(-1, 1)`. -/
theorem not_isRegularPoint_sphericalPendulumEnergyMomentum_iff (x : sphericalPendulumPhaseSpace) :
    ¬ IsRegularPoint 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, ℝ × ℝ)
        (fun y : sphericalPendulumPhaseSpace ↦ sphericalPendulumEnergyMomentum y) x ↔
      ((x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 = 0 ∧
          (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ^ 2 = 1) ∨
        ((sphericalPendulumEnergyMomentum x).2 ≠ 0 ∧
          (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 = 0 ∧
          IsMinOn (sphericalPendulumEffectivePotential (sphericalPendulumEnergyMomentum x).2)
            (Ioo (-1) 1) ((x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2)) := by
  rw [isRegularPoint_sphericalPendulumEnergyMomentum_iff]
  obtain ⟨⟨q, p⟩, hx⟩ := x
  have hJ : (sphericalPendulumEnergyMomentum (q, p)).2 = q 0 * p 1 - q 1 * p 0 := by
    simp [sphericalPendulumEnergyMomentum_apply]
  -- Away from the poles, minimizing `V_j` is the equation `j² z + (1 - z²)² = 0`.
  have hmin (hJ0 : (sphericalPendulumEnergyMomentum (q, p)).2 ≠ 0) :=
    isMinOn_sphericalPendulumEffectivePotential_iff hJ0 (apply_two_mem_Ioo_of_snd_ne_zero hx hJ0)
  constructor
  · intro hne
    rcases pole_or_relativeEquilibrium_of_map_ne_top hx hne with h | ⟨hJ0, hp2, hcrit⟩
    · exact Or.inl h
    · rw [← hJ] at hJ0 hcrit
      exact Or.inr ⟨hJ0, hp2, (hmin hJ0).2 hcrit⟩
  · rintro (h | ⟨hJ0, hp2, hm⟩)
    · exact map_ne_top_of_pole_or_relativeEquilibrium hx (Or.inl h)
    · have hcrit := (hmin hJ0).1 hm
      rw [hJ] at hJ0 hcrit
      exact map_ne_top_of_pole_or_relativeEquilibrium hx (Or.inr ⟨hJ0, hp2, hcrit⟩)

/-! ### Critical values -/

/-- **The critical values of the spherical pendulum.** The critical values of the energy–momentum
map are the value `(-1, 0)` of the stable equilibrium at the south pole, the value `(1, 0)` of the
unstable equilibrium at the north pole, and the curve of relative equilibria: the points `(h, j)`
with `j ≠ 0` at which `h` is the minimum value of the effective potential `V_j` on `(-1, 1)`. -/
theorem image_setOf_not_isRegularPoint_sphericalPendulumEnergyMomentum :
    (fun y : sphericalPendulumPhaseSpace ↦ sphericalPendulumEnergyMomentum y) ''
        {x | ¬ IsRegularPoint 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, ℝ × ℝ)
          (fun y : sphericalPendulumPhaseSpace ↦ sphericalPendulumEnergyMomentum y) x} =
      {(-1, 0), (1, 0)} ∪
        {c | c.2 ≠ 0 ∧ IsLeast (sphericalPendulumEffectivePotential c.2 '' Ioo (-1) 1) c.1} := by
  ext c
  simp only [mem_image, mem_ofPred_eq, not_isRegularPoint_sphericalPendulumEnergyMomentum_iff]
  constructor
  · rintro ⟨⟨⟨q, p⟩, hx⟩, hcrit, rfl⟩
    rcases hcrit with ⟨hp, hq2⟩ | ⟨hJ0, hp2, hmin⟩
    · -- The poles at rest.
      dsimp only at hp hq2 ⊢
      subst hp
      left
      rcases sq_eq_one_iff.1 hq2 with h | h <;> simp [sphericalPendulumEnergyMomentum_apply, h]
    · -- The relative equilibria.
      dsimp only at hJ0 hp2 hmin ⊢
      right
      have hz : q 2 ∈ Ioo (-1) 1 := apply_two_mem_Ioo_of_snd_ne_zero hx hJ0
      have hH := fst_sphericalPendulumEnergyMomentum_eq hx
        (((sq_lt_one_iff_abs_lt_one _).trans abs_lt).2 hz)
      rw [hp2, zero_pow two_ne_zero, zero_div, add_zero] at hH
      refine ⟨hJ0, ⟨q 2, hz, hH.symm⟩, ?_⟩
      rintro _ ⟨w, hw, rfl⟩
      rw [hH]
      exact hmin hw
  · rintro ((rfl | rfl) | ⟨hj, ⟨z, hz, hzc⟩, hleast⟩)
    · refine ⟨⟨(!₂[0, 0, -1], 0), ?_⟩, Or.inl ⟨rfl, by norm_num⟩, ?_⟩
      · rw [mem_sphericalPendulumPhaseSpace, ← pow_eq_one_iff_of_nonneg (norm_nonneg _)
          two_ne_zero, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
        simp
      · simp [sphericalPendulumEnergyMomentum_apply]
    · refine ⟨⟨(!₂[0, 0, 1], 0), ?_⟩, Or.inl ⟨rfl, by norm_num⟩, ?_⟩
      · rw [mem_sphericalPendulumPhaseSpace, ← pow_eq_one_iff_of_nonneg (norm_nonneg _)
          two_ne_zero, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
        simp
      · simp [sphericalPendulumEnergyMomentum_apply]
    · -- A point of the fibre over the boundary value is a relative equilibrium.
      obtain ⟨h, j⟩ := c
      dsimp only at hj hzc hleast
      have hmin : IsMinOn (sphericalPendulumEffectivePotential j) (Ioo (-1) 1) z :=
        fun w hw ↦ hzc ▸ hleast (mem_image_of_mem _ hw)
      obtain ⟨x, hx, hFx⟩ := (mk_mem_image_sphericalPendulumEnergyMomentum_iff_of_isMinOn hj hz
        hmin h).2 (hzc.le)
      rw [← hzc] at hFx
      obtain ⟨hJ, hxz, hp⟩ := (sphericalPendulumEnergyMomentum_eq_iff_of_isMinOn hj hz hmin hx).1
        hFx
      refine ⟨⟨x, hx⟩, Or.inr ⟨?_, hp, ?_⟩, ?_⟩
      · rw [hJ]
        exact hj
      · rw [hJ, hxz]
        exact hmin
      · rw [hFx, hzc]

/-- **The regular values of the spherical pendulum.** A value of the plane is a regular value of
the energy–momentum map exactly when it is neither `(-1, 0)`, nor `(1, 0)`, nor a point `(h, j)`
with `j ≠ 0` at which `h` is the minimum value of the effective potential `V_j` on `(-1, 1)`. -/
theorem isRegularValue_sphericalPendulumEnergyMomentum_iff (c : ℝ × ℝ) :
    IsRegularValue 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, ℝ × ℝ)
        (fun y : sphericalPendulumPhaseSpace ↦ sphericalPendulumEnergyMomentum y) c ↔
      c ≠ (-1, 0) ∧ c ≠ (1, 0) ∧
        ¬ (c.2 ≠ 0 ∧ IsLeast (sphericalPendulumEffectivePotential c.2 '' Ioo (-1) 1) c.1) := by
  rw [isRegularValue_iff_notMem_image,
    image_setOf_not_isRegularPoint_sphericalPendulumEnergyMomentum]
  simp only [mem_union, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq, not_or, and_assoc,
    ne_eq]

/-- **The focus–focus value is isolated.** Every value of the energy–momentum map close to
`(1, 0)`, other than `(1, 0)` itself, is a regular value: near `(1, 0)` there are no relative
equilibria, whose energies `min V_j ≤ V_j(0) = j² / 2` are small for small `j`. -/
theorem eventually_isRegularValue_sphericalPendulumEnergyMomentum_nhdsNE :
    ∀ᶠ c in 𝓝[≠] ((1 : ℝ), (0 : ℝ)), IsRegularValue 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun y : sphericalPendulumPhaseSpace ↦ sphericalPendulumEnergyMomentum y) c := by
  have hU : {c : ℝ × ℝ | 1 / 2 < c.1 ∧ c.2 ^ 2 < 1} ∈ 𝓝 ((1 : ℝ), (0 : ℝ)) :=
    ((isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt (continuous_snd.pow 2) continuous_const)).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with c ⟨hc1, hc2⟩ hne
  refine (isRegularValue_sphericalPendulumEnergyMomentum_iff c).2
    ⟨fun h ↦ by rw [h] at hc1; norm_num at hc1, hne, fun ⟨_, hleast⟩ ↦ ?_⟩
  -- The minimum of `V_j` is at most `V_j(0) = j² / 2 < 1 / 2`.
  have h0 := hleast.2 (mem_image_of_mem _ (show (0 : ℝ) ∈ Ioo (-1) 1 by norm_num))
  rw [sphericalPendulumEffectivePotential_def] at h0
  norm_num at h0
  linarith

/-- The value `(1, 0)` of the unstable equilibrium lies in the interior of the image of the
energy–momentum map. -/
theorem mem_interior_image_sphericalPendulumEnergyMomentum :
    ((1 : ℝ), (0 : ℝ)) ∈
      interior (sphericalPendulumEnergyMomentum '' sphericalPendulumPhaseSpace) := by
  rw [mem_interior_iff_mem_nhds, image_sphericalPendulumEnergyMomentum]
  have hU : {c : ℝ × ℝ | 1 / 2 < c.1 ∧ c.2 ^ 2 < 1} ∈ 𝓝 ((1 : ℝ), (0 : ℝ)) :=
    ((isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt (continuous_snd.pow 2) continuous_const)).mem_nhds (by norm_num)
  -- The height `z = 0` occurs in every fibre over `{1 / 2 < h, j² < 1}`.
  filter_upwards [hU] with c ⟨hc1, hc2⟩
  exact ⟨0, by norm_num, by linarith, by nlinarith⟩

end TauCeti
