/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.PhaseSpace

/-!
# Critical points and critical values of the spherical pendulum

This file works on the phase space `T*S² = {(q, p) : ‖q‖ = 1, ⟪q, p⟫ = 0}` of the spherical
pendulum, with the smooth four-manifold structure of the regular level over `(1, 0)` of the
constraint map `g(q, p) = (‖q‖², ⟪q, p⟫)` from
`TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.PhaseSpace`. It determines the critical
points and the critical values of the energy–momentum map `F = (H, J)` restricted to it,
`H = ‖p‖² / 2 + q₃` and `J = q₁ p₂ - q₂ p₁`.

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
(`TauCeti.mem_interior_image_sphericalPendulumEnergyMomentum`, proved with the image of `F` in
`TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum`).

## Main results

* `TauCeti.isRegularPoint_sphericalPendulumEnergyMomentum_iff`: regular points of `F` on the phase
  space, through the tangent space `ker dg`.
* `TauCeti.not_isRegularPoint_sphericalPendulumEnergyMomentum_iff`: the critical points.
* `TauCeti.image_setOf_not_isRegularPoint_sphericalPendulumEnergyMomentum` and
  `TauCeti.isRegularValue_sphericalPendulumEnergyMomentum_iff`: the critical and regular values.
* `TauCeti.eventually_isRegularValue_sphericalPendulumEnergyMomentum_nhdsNE`: the value `(1, 0)`
  is an isolated critical value.

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

/-! ### Regular points -/

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
  rw [show (fun y : sphericalPendulumPhaseSpace ↦ sphericalPendulumEnergyMomentum y) =
      sphericalPendulumEnergyMomentum ∘ Subtype.val from rfl, isRegularPoint_comp_iff hF hval,
    range_mfderiv_coe_sphericalPendulumPhaseSpace, mfderiv_eq_fderiv]
  -- The identifications `NormedSpace.fromTangentSpace` of the tangent spaces with `ℝ³ × ℝ³` and
  -- `ℝ × ℝ` are the identity.
  rfl

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

/-- **Lagrange multipliers for a map into the plane.** If a linear map `DF` does not map the kernel
of a linear map `D` onto `ℝ²`, then some `(l, m) ≠ 0` and `c` satisfy
`l DF₁ + m DF₂ = c₀ D₁ + c₁ D₂`. -/
private theorem exists_lagrange_multipliers {E : Type*} [AddCommGroup E] [Module ℝ E]
    {D DF : E →ₗ[ℝ] ℝ × ℝ} (hne : D.ker.map DF ≠ ⊤) :
    ∃ l m : ℝ, (l ≠ 0 ∨ m ≠ 0) ∧ ∃ c : Fin 2 → ℝ,
      ∀ v, l * (DF v).1 + m * (DF v).2 = c 0 * (D v).1 + c 1 * (D v).2 := by
  -- A nonzero functional `f = l (·).1 + m (·).2` on `ℝ²` kills `DF (ker D)`.
  obtain ⟨f, hf0, hf⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
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
  refine ⟨f (1, 0), f (0, 1), ?_, c, fun v ↦ ?_⟩
  · by_contra! h
    exact hf0 (LinearMap.ext fun w ↦ by rw [hf', h.1, h.2]; simp)
  · have h := LinearMap.congr_fun hc v
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.coe_comp, comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, smul_eq_mul] at h
    rw [← hf', ← h]

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
  dsimp only at hq hqp
  obtain ⟨l, m, hlm, c, hc⟩ := exists_lagrange_multipliers hne
  have hev (a b : EuclideanSpace ℝ (Fin 3)) :
      c 0 * (2 * (q 0 * a 0 + q 1 * a 1 + q 2 * a 2)) +
          c 1 * (q 0 * b 0 + q 1 * b 1 + q 2 * b 2 + (a 0 * p 0 + a 1 * p 1 + a 2 * p 2)) =
        l * (p 0 * b 0 + p 1 * b 1 + p 2 * b 2 + a 2) +
          m * (a 0 * p 1 - a 1 * p 0 + q 0 * b 1 - q 1 * b 0) := by
    have h := hc (a, b)
    obtain ⟨hD, hDF⟩ := fderiv_coords q p a b
    simp only [ContinuousLinearMap.coe_coe, hD, hDF] at h
    exact h.symm
  -- The six coordinates of the multiplier equation.
  have ea0 := hev (EuclideanSpace.single 0 1) 0
  have ea1 := hev (EuclideanSpace.single 1 1) 0
  have ea2 := hev (EuclideanSpace.single 2 1) 0
  have eb0 := hev 0 (EuclideanSpace.single 0 1)
  have eb1 := hev 0 (EuclideanSpace.single 1 1)
  have eb2 := hev 0 (EuclideanSpace.single 2 1)
  simp only [Fin.isValue, PiLp.single_eq_same, mul_one, ne_eq, one_ne_zero, not_false_eq_true,
    PiLp.single_eq_of_ne, mul_zero, add_zero, Fin.reduceEq, PiLp.zero_apply, one_mul, zero_mul,
    zero_add, sub_zero, zero_ne_one, zero_sub, mul_neg, sub_self] at ea0 ea1 ea2 eb0 eb1 eb2
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
  dsimp only at hq hqp
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
    isMinOn_sphericalPendulumEffectivePotential_iff hJ0
      (apply_two_mem_Ioo_of_mem_sphericalPendulumPhaseSpace_of_snd_ne_zero hx hJ0)
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
      have hz : q 2 ∈ Ioo (-1) 1 :=
        apply_two_mem_Ioo_of_mem_sphericalPendulumPhaseSpace_of_snd_ne_zero hx hJ0
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

/-- **The value `(1, 0)` of the upper equilibrium is an isolated critical value.** Every value of
the energy–momentum map close to `(1, 0)`, other than `(1, 0)` itself, is a regular value: near
`(1, 0)` there are no relative equilibria, whose energies `min V_j ≤ V_j(0) = j² / 2` are small for
small `j`. -/
theorem eventually_isRegularValue_sphericalPendulumEnergyMomentum_nhdsNE :
    ∀ᶠ c in 𝓝[≠] ((1 : ℝ), (0 : ℝ)), IsRegularValue 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun y : sphericalPendulumPhaseSpace ↦ sphericalPendulumEnergyMomentum y) c := by
  filter_upwards [nhdsWithin_le_nhds
      ((isOpen_lt (f := fun c : ℝ × ℝ ↦ c.2 ^ 2) (by fun_prop) continuous_fst).mem_nhds
        (by norm_num)),
    self_mem_nhdsWithin] with c hc hne
  have hc1 : 0 < c.1 := (sq_nonneg c.2).trans_lt hc
  refine (isRegularValue_sphericalPendulumEnergyMomentum_iff c).2
    ⟨fun h ↦ by rw [h] at hc1; norm_num at hc1, hne, fun ⟨_, hleast⟩ ↦ ?_⟩
  -- The minimum of `V_j` is at most `V_j(0) = j² / 2 < h` for `j² < h`.
  have h0 := hleast.2 (mem_image_of_mem _ (show (0 : ℝ) ∈ Ioo (-1) 1 by norm_num))
  rw [sphericalPendulumEffectivePotential_def] at h0
  norm_num at h0
  linarith

end TauCeti
