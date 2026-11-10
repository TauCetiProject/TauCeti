/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.RegularValue.Level
public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum

import TauCeti.LinearAlgebra.Prod

/-!
# The critical values of the spherical pendulum

The phase space `T*S² = {(q, p) : ‖q‖ = 1, ⟪q, p⟫ = 0}` of the spherical pendulum
(`TauCeti.sphericalPendulumPhaseSpace`) is the level `g⁻¹(1, 0)` of the constraint map
`g(q, p) = (‖q‖², ⟪q, p⟫)` (`TauCeti.sphericalPendulumConstraint`) on `ℝ³ × ℝ³`, and `(1, 0)` is a
regular value of `g` (`TauCeti.isRegularValue_sphericalPendulumConstraint`). So the subtype
`{x // g x = (1, 0)}` carries the regular-level atlas of `TauCeti.regularLevelChartedSpace`: it is
an analytic manifold of dimension four, smoothly embedded in `ℝ³ × ℝ³`, whose tangent space at `x`
is the kernel of `dg_x` (`TauCeti.range_mvfderiv_subtypeVal_sphericalPendulumConstraint`).

This file computes the critical points and the critical values of the energy–momentum map
`F = (H, J)` (`TauCeti.sphericalPendulumEnergyMomentum`), `H = ‖p‖² / 2 + q₃` and
`J = q₁ p₂ - q₂ p₁`, restricted to this manifold.

* **Critical points.** A point `(q, p)` of `T*S²` is a critical point of `F` exactly when
  `p₃ = 0` and `q₃ ‖p‖² = q₃² - 1`
  (`TauCeti.isRegularPoint_sphericalPendulumEnergyMomentum_comp_subtypeVal_iff`). At a pole,
  `q₃² = 1`, this says `p = 0`: these are the two equilibria at rest. Away from the poles it says
  that `q₃ < 0` and the momentum is horizontal, tangent to the circle of latitude, with
  `‖p‖² = (1 - q₃²) / (-q₃)`: these are the relative equilibria, the uniform horizontal circular
  motions.
* **Critical values.** Consequently a value `(h, j)` is a critical value of `F` exactly when it is
  the bottom value `(-1, 0)` of the stable equilibrium at the south pole, the value `(1, 0)` of the
  unstable equilibrium at the north pole, or, for `j ≠ 0`, the minimum value `V_j(z_j)` of the
  effective potential `V_j(z) = j² / (2 (1 - z²)) + z` on `(-1, 1)` with momentum `j`
  (`TauCeti.not_isRegularValue_sphericalPendulumEnergyMomentum_comp_subtypeVal_iff`). The last
  family is the boundary curve of the image of `F` described by
  `TauCeti.mk_mem_image_sphericalPendulumEnergyMomentum_iff_of_isMinOn`. Every other value is a
  regular value. This locates the regular fibres of the pendulum, its Liouville tori, and the
  focus–focus value `(1, 0)` around which its Hamiltonian monodromy is computed.

## Main results

* `TauCeti.isRegularValue_sphericalPendulumConstraint`: `T*S²` is a regular level.
* `TauCeti.isSmoothEmbedding_subtypeVal_sphericalPendulumConstraint`: its inclusion into
  `ℝ³ × ℝ³` is an analytic embedding.
* `TauCeti.range_mvfderiv_subtypeVal_sphericalPendulumConstraint`: its tangent spaces.
* `TauCeti.isRegularPoint_sphericalPendulumEnergyMomentum_comp_subtypeVal_iff`: the critical
  points of the energy–momentum map.
* `TauCeti.not_isRegularValue_sphericalPendulumEnergyMomentum_comp_subtypeVal_iff`: its critical
  values.

## References

* R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, 2nd ed.,
  Birkhäuser, 2015, Chapter IV (the spherical pendulum).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Corollary 5.14 and Proposition 5.38 (regular level sets and their tangent
  spaces).
-/

public section

namespace TauCeti

open Set
open scoped InnerProductSpace ContDiff
open _root_.Manifold

local notation "E" => EuclideanSpace ℝ (Fin 3)

/-- The constraint map `g(q, p) = (‖q‖², ⟪q, p⟫)` on `ℝ³ × ℝ³`. Its level `g⁻¹(1, 0)` is the phase
space `T*S²` of the spherical pendulum (`TauCeti.sphericalPendulumConstraint_eq_iff`), and
`(1, 0)` is a regular value, so this level is a submanifold of dimension four. -/
noncomputable def sphericalPendulumConstraint (x : E × E) : ℝ × ℝ :=
  (‖x.1‖ ^ 2, ⟪x.1, x.2⟫_ℝ)

@[simp]
theorem sphericalPendulumConstraint_apply (q p : E) :
    sphericalPendulumConstraint (q, p) = (‖q‖ ^ 2, ⟪q, p⟫_ℝ) :=
  (rfl)

/-- The level `g⁻¹(1, 0)` of the constraint map is the phase space `T*S²`. -/
theorem sphericalPendulumConstraint_eq_iff {x : E × E} :
    sphericalPendulumConstraint x = (1, 0) ↔ x ∈ sphericalPendulumPhaseSpace := by
  simp [sphericalPendulumConstraint, pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero]

/-- The constraint map is smooth, indeed analytic. -/
theorem contDiff_sphericalPendulumConstraint {n : WithTop ℕ∞} :
    ContDiff ℝ n sphericalPendulumConstraint :=
  ((contDiff_norm_sq ℝ).comp contDiff_fst).prodMk (contDiff_fst.inner ℝ contDiff_snd)

/-- The differential of the constraint map:
`dg_(q, p)(u, v) = (2 ⟪q, u⟫, ⟪q, v⟫ + ⟪u, p⟫)`. -/
theorem fderiv_sphericalPendulumConstraint_apply (x w : E × E) :
    fderiv ℝ sphericalPendulumConstraint x w =
      (2 * ⟪x.1, w.1⟫_ℝ, ⟪x.1, w.2⟫_ℝ + ⟪w.1, x.2⟫_ℝ) := by
  unfold sphericalPendulumConstraint
  rw [((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).norm_sq.prodMk
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).inner ℝ hasFDerivAt_snd)).fderiv]
  simp

/-- The energy–momentum map of the spherical pendulum is smooth, indeed analytic, on
`ℝ³ × ℝ³`. -/
theorem contDiff_sphericalPendulumEnergyMomentum {n : WithTop ℕ∞} :
    ContDiff ℝ n sphericalPendulumEnergyMomentum := by
  have h : sphericalPendulumEnergyMomentum =
      fun x : E × E ↦ (‖x.2‖ ^ 2 / 2 + x.1 2, x.1 0 * x.2 1 - x.1 1 * x.2 0) :=
    funext fun x ↦ sphericalPendulumEnergyMomentum_apply x.1 x.2
  have hc (i : Fin 3) : ContDiff ℝ n fun y : E ↦ y i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff (n := n)
  rw [h]
  exact ((((contDiff_norm_sq ℝ).comp contDiff_snd).div_const 2).add (by fun_prop)).prodMk
    (by fun_prop)

/-- The differential of the energy–momentum map `F = (H, J)`:
`dF_(q, p)(u, v) = (⟪p, v⟫ + u₃, u₁ p₂ + q₁ v₂ - u₂ p₁ - q₂ v₁)`. -/
theorem fderiv_sphericalPendulumEnergyMomentum_apply (x w : E × E) :
    fderiv ℝ sphericalPendulumEnergyMomentum x w =
      (⟪x.2, w.2⟫_ℝ + w.1 2,
        w.1 0 * x.2 1 + x.1 0 * w.2 1 - w.1 1 * x.2 0 - x.1 1 * w.2 0) := by
  have h₂ : HasFDerivAt (fun y : E × E ↦ ‖y.2‖ ^ 2) _ x := hasFDerivAt_snd.norm_sq
  have hF := ((h₂.mul_const (2⁻¹ : ℝ)).add
    ((EuclideanSpace.proj (2 : Fin 3)).comp (ContinuousLinearMap.fst ℝ E E)).hasFDerivAt).prodMk
    (hasFDerivAt_angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) x)
  rw [(hF.congr_of_eventuallyEq (f₁ := sphericalPendulumEnergyMomentum)
    (.of_forall fun ⟨q, p⟩ ↦ Prod.ext (by simp [div_eq_mul_inv])
      (snd_sphericalPendulumEnergyMomentum _))).fderiv]
  simp [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right]
  ring

/-- At a point of `T*S²` the differential of the constraint map is surjective. -/
theorem surjective_fderiv_sphericalPendulumConstraint {x : E × E}
    (hx : x ∈ sphericalPendulumPhaseSpace) :
    Function.Surjective (fderiv ℝ sphericalPendulumConstraint x) := by
  obtain ⟨hq, hqp⟩ := mem_sphericalPendulumPhaseSpace.1 hx
  refine fun c ↦ ⟨((c.1 / 2) • x.1, c.2 • x.1), ?_⟩
  rw [fderiv_sphericalPendulumConstraint_apply]
  simp [real_inner_smul_right, real_inner_smul_left, hq, hqp, mul_div_cancel₀]

/-- `(1, 0)` is a regular value of the constraint map, so `T*S²` is a regular level. -/
theorem isRegularValue_sphericalPendulumConstraint :
    IsRegularValue 𝓘(ℝ, E × E) 𝓘(ℝ, ℝ × ℝ) sphericalPendulumConstraint (1, 0) := by
  refine isRegularValue_iff.2 fun x hx ↦ ?_
  rw [isRegularPoint_iff_surjective_mvfderiv, mvfderiv_eq_fderiv, ContinuousLinearMap.coe_comp,
    ContinuousLinearEquiv.coe_coe]
  exact (surjective_fderiv_sphericalPendulumConstraint
    (sphericalPendulumConstraint_eq_iff.1 hx)).comp (ContinuousLinearEquiv.surjective _)

private theorem finrank_sub_finrank_sphericalPendulumConstraint :
    Module.finrank ℝ (E × E) - Module.finrank ℝ (ℝ × ℝ) = 4 := by
  simp

/-- The constraint map is smooth as a map of manifolds. -/
theorem contMDiff_sphericalPendulumConstraint {n : WithTop ℕ∞} :
    ContMDiff 𝓘(ℝ, E × E) 𝓘(ℝ, ℝ × ℝ) n sphericalPendulumConstraint :=
  contDiff_sphericalPendulumConstraint.contMDiff

/-- The atlas of the phase space `T*S²` of the spherical pendulum, as the regular level `g⁻¹(1, 0)`
of the constraint map: the regular-level atlas `TauCeti.regularLevelChartedSpace`, modelled on
`ℝ⁴`. -/
noncomputable instance instChartedSpaceSphericalPendulumConstraint :
    ChartedSpace (Fin 4 → ℝ) {x // sphericalPendulumConstraint x = (1, 0)} :=
  regularLevelChartedSpace (fun _ _ ↦ contMDiff_sphericalPendulumConstraint.contMDiffAt)
    isRegularValue_sphericalPendulumConstraint (by simp)

/-- The phase space `T*S²` of the spherical pendulum is an analytic manifold of dimension four. -/
instance instIsManifoldSphericalPendulumConstraint :
    IsManifold 𝓘(ℝ, Fin 4 → ℝ) ω {x // sphericalPendulumConstraint x = (1, 0)} :=
  isManifold_regularLevel (by simp) (fun _ _ ↦ contMDiff_sphericalPendulumConstraint.contMDiffAt)
    isRegularValue_sphericalPendulumConstraint finrank_sub_finrank_sphericalPendulumConstraint

/-- The inclusion of the phase space `T*S²` into `ℝ³ × ℝ³` is an analytic embedding. -/
theorem isSmoothEmbedding_subtypeVal_sphericalPendulumConstraint :
    IsSmoothEmbedding 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, E × E) ω
      (Subtype.val : {x // sphericalPendulumConstraint x = (1, 0)} → E × E) :=
  isSmoothEmbedding_coe_regularLevel (by simp)
    (fun _ _ ↦ contMDiff_sphericalPendulumConstraint.contMDiffAt)
    isRegularValue_sphericalPendulumConstraint finrank_sub_finrank_sphericalPendulumConstraint

/-- **The tangent spaces of `T*S²`.** The differential of the inclusion of the phase space into
`ℝ³ × ℝ³` at `x` has image the kernel of the differential of the constraint map,
`{(u, v) | ⟪q, u⟫ = 0, ⟪q, v⟫ + ⟪u, p⟫ = 0}`. -/
theorem range_mvfderiv_subtypeVal_sphericalPendulumConstraint
    (z : {x // sphericalPendulumConstraint x = (1, 0)}) :
    (mvfderiv 𝓘(ℝ, Fin 4 → ℝ) Subtype.val z).range =
      (fderiv ℝ sphericalPendulumConstraint z.1).ker := by
  let e := NormedSpace.fromTangentSpace (𝕜 := ℝ) z.1
  rw [range_mvfderiv, range_mfderiv_coe_regularLevel _ isRegularValue_sphericalPendulumConstraint
    finrank_sub_finrank_sphericalPendulumConstraint z, ← ker_mvfderiv, mvfderiv_eq_fderiv]
  ext w
  simp only [Submodule.mem_map, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  exact ⟨fun ⟨v, hv, hvw⟩ ↦ hvw ▸ hv, fun hw ↦ ⟨e.symm w, by simpa [e] using hw, by simp [e]⟩⟩

/- The critical points are found by the Lagrange multiplier rule. The differential of `F` fails
to map `T_x(T*S²) = ker dg_x` onto `ℝ²` exactly when some nonzero combination `a dH + b dJ`
vanishes on `ker dg_x`, that is, since `dg_x` is surjective, when
`a dH + b dJ = c d(‖q‖²) + d d⟪q, p⟫` for some multipliers `c, d`. Testing this identity on
coordinate vectors gives six polynomial equations, which are solved explicitly. -/

/-- The six coordinate equations of a Lagrange multiplier relation
`a dH + b dJ = c d(‖q‖²) + d d⟪q, p⟫` with `(a, b) ≠ 0`, tested on the coordinate vectors, force
the critical-point condition. -/
private theorem crit_of_multipliers {q₀ q₁ q₂ p₀ p₁ p₂ a b c d : ℝ}
    (hq : q₀ ^ 2 + q₁ ^ 2 + q₂ ^ 2 = 1) (hqp : q₀ * p₀ + q₁ * p₁ + q₂ * p₂ = 0)
    (hab : ¬(a = 0 ∧ b = 0))
    (e₁ : a * p₀ - b * q₁ = d * q₀) (e₂ : a * p₁ + b * q₀ = d * q₁) (e₃ : a * p₂ = d * q₂)
    (e₄ : b * p₁ = 2 * c * q₀ + d * p₀) (e₅ : -(b * p₀) = 2 * c * q₁ + d * p₁)
    (e₆ : a = 2 * c * q₂ + d * p₂) :
    p₂ = 0 ∧ q₂ * (p₀ ^ 2 + p₁ ^ 2 + p₂ ^ 2) = q₂ ^ 2 - 1 := by
  have hd : d = 0 := by linear_combination (-q₀) * e₁ - q₁ * e₂ - q₂ * e₃ + a * hqp - d * hq
  subst hd
  by_cases ha : a = 0
  · subst ha
    have hb : b ≠ 0 := fun hb ↦ hab ⟨rfl, hb⟩
    have h₀ : q₀ = 0 := (mul_eq_zero.1 (by linear_combination e₂)).resolve_left hb
    have h₁ : q₁ = 0 := (mul_eq_zero.1 (by linear_combination -e₁)).resolve_left hb
    have k₀ : p₀ = 0 := (mul_eq_zero.1 (by linear_combination -e₅ - 2 * c * h₁)).resolve_left hb
    have k₁ : p₁ = 0 := (mul_eq_zero.1 (by linear_combination e₄ + 2 * c * h₀)).resolve_left hb
    subst h₀ h₁ k₀ k₁
    have hq₂ : q₂ ≠ 0 := by rintro rfl; norm_num at hq
    have k₂ : p₂ = 0 := (mul_eq_zero.1 (by linear_combination hqp)).resolve_left hq₂
    subst k₂
    exact ⟨rfl, by linear_combination -hq⟩
  · have k₂ : p₂ = 0 := (mul_eq_zero.1 (by linear_combination e₃)).resolve_left ha
    subst k₂
    refine ⟨rfl, (mul_eq_zero.1 (?_ : a ^ 2 * (q₂ * (p₀ ^ 2 + p₁ ^ 2 + 0 ^ 2) - (q₂ ^ 2 - 1)) = 0)
      ).resolve_left (pow_ne_zero 2 ha) |> sub_eq_zero.1⟩
    linear_combination q₂ * (a * p₀ + b * q₁) * e₁ + q₂ * (a * p₁ - b * q₀) * e₂ +
      (q₀ ^ 2 + q₁ ^ 2) * a * e₆ + q₂ * q₀ * (b * e₂ - a * e₄) - q₂ * q₁ * (a * e₅ + b * e₁) +
      -a ^ 2 * hq

/-- At a critical point, multipliers as in `crit_of_multipliers` exist, with `d = 0`. -/
private theorem exists_multipliers {q₀ q₁ q₂ p₀ p₁ p₂ : ℝ}
    (hq : q₀ ^ 2 + q₁ ^ 2 + q₂ ^ 2 = 1) (hqp : q₀ * p₀ + q₁ * p₁ + q₂ * p₂ = 0)
    (hp₂ : p₂ = 0) (hcrit : q₂ * (p₀ ^ 2 + p₁ ^ 2 + p₂ ^ 2) = q₂ ^ 2 - 1) :
    ∃ a b c : ℝ, ¬(a = 0 ∧ b = 0) ∧ a * p₀ - b * q₁ = 0 ∧ a * p₁ + b * q₀ = 0 ∧ a * p₂ = 0 ∧
      b * p₁ = 2 * c * q₀ ∧ -(b * p₀) = 2 * c * q₁ ∧ a = 2 * c * q₂ := by
  subst hp₂
  by_cases hpole : q₀ = 0 ∧ q₁ = 0
  · obtain ⟨rfl, rfl⟩ := hpole
    have hq₂ : q₂ ≠ 0 := by rintro rfl; norm_num at hq
    have hp : p₀ ^ 2 + p₁ ^ 2 = 0 :=
      (mul_eq_zero.1 (by linear_combination hcrit + hq)).resolve_left hq₂
    have k₀ : p₀ = 0 := by nlinarith
    have k₁ : p₁ = 0 := by nlinarith
    exact ⟨0, 1, 0, by simp, by simp, by simp, by simp, by simp [k₁], by simp [k₀], by simp⟩
  · have hq₂ : q₂ ≠ 0 := by
      rintro rfl
      norm_num at hcrit
    have hρ : q₀ ^ 2 + q₁ ^ 2 ≠ 0 := by
      intro h
      exact hpole ⟨by nlinarith, by nlinarith⟩
    refine ⟨(q₀ ^ 2 + q₁ ^ 2) * q₂, q₂ * (p₀ * q₁ - p₁ * q₀), (q₀ ^ 2 + q₁ ^ 2) / 2,
      fun h ↦ mul_ne_zero hρ hq₂ h.1, ?_, ?_, by ring, ?_, ?_, by ring⟩
    · linear_combination q₂ * q₀ * hqp
    · linear_combination q₂ * q₁ * hqp
    · linear_combination q₂ * p₀ * hqp - q₀ * hcrit - q₀ * hq
    · linear_combination q₂ * p₁ * hqp - q₁ * hcrit - q₁ * hq

/-- **The Lagrange multiplier rule.** If the differential of `F = (H, J)` does not map the kernel
of the differential of the constraint map onto `ℝ²`, then some nonzero combination `a dF₁ + b dF₂`
factors through the differential of the constraint map. -/
private theorem exists_multiplier_relation {x : E × E} (hx : x ∈ sphericalPendulumPhaseSpace)
    (hns : ¬∀ c, ∃ w, fderiv ℝ sphericalPendulumConstraint x w = 0 ∧
        fderiv ℝ sphericalPendulumEnergyMomentum x w = c) :
    ∃ a b c d : ℝ, ¬(a = 0 ∧ b = 0) ∧ ∀ w,
      c * (fderiv ℝ sphericalPendulumConstraint x w).1 +
          d * (fderiv ℝ sphericalPendulumConstraint x w).2 =
        a * (fderiv ℝ sphericalPendulumEnergyMomentum x w).1 +
          b * (fderiv ℝ sphericalPendulumEnergyMomentum x w).2 := by
  set g' := fderiv ℝ sphericalPendulumConstraint x
  set F' := fderiv ℝ sphericalPendulumEnergyMomentum x
  -- The image of `ker dg` under `dF` is a proper subspace of `ℝ²`, so it lies in the kernel of a
  -- nonzero linear form `ℓ`, and `ℓ ∘ dF` factors through the surjection `dg`.
  have hV : (LinearMap.ker (g' : E × E →ₗ[ℝ] ℝ × ℝ)).map (F' : E × E →ₗ[ℝ] ℝ × ℝ) < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h ↦ hns fun c ↦ ?_
    obtain ⟨w, hw, hwc⟩ := Submodule.mem_map.1 (h ▸ Submodule.mem_top (x := c))
    exact ⟨w, hw, hwc⟩
  obtain ⟨ℓ, hℓ, hVℓ⟩ := Submodule.exists_le_ker_of_lt_top _ hV
  have hker : LinearMap.ker (g' : E × E →ₗ[ℝ] ℝ × ℝ) ≤
      LinearMap.ker (ℓ ∘ₗ (F' : E × E →ₗ[ℝ] ℝ × ℝ)) :=
    fun w hw ↦ hVℓ ⟨w, hw, rfl⟩
  let μ := (g' : E × E →ₗ[ℝ] ℝ × ℝ).liftOfSurjective
    (surjective_fderiv_sphericalPendulumConstraint hx) ⟨_, hker⟩
  refine ⟨ℓ (1, 0), ℓ (0, 1), μ (1, 0), μ (0, 1), fun ⟨h₁, h₂⟩ ↦
    hℓ (LinearMap.ext fun v ↦ by simp [LinearMap.apply_eq_fst_smul_add_snd_smul ℓ v, h₁, h₂]),
    fun w ↦ ?_⟩
  have h : μ (g' w) = ℓ (F' w) := LinearMap.equivOfSurjective_apply _ hker
  rw [LinearMap.apply_eq_fst_smul_add_snd_smul μ, LinearMap.apply_eq_fst_smul_add_snd_smul ℓ] at h
  simp only [smul_eq_mul] at h
  linear_combination h

/-- The linear criterion: at a point of `T*S²`, the differential of `(H, J)` maps the kernel of the
differential of the constraint onto `ℝ²` exactly away from the critical points. -/
private theorem forall_exists_fderiv_iff {x : E × E} (hx : x ∈ sphericalPendulumPhaseSpace) :
    (∀ c, ∃ w, fderiv ℝ sphericalPendulumConstraint x w = 0 ∧
        fderiv ℝ sphericalPendulumEnergyMomentum x w = c) ↔
      ¬(x.2 2 = 0 ∧ x.1 2 * ‖x.2‖ ^ 2 = x.1 2 ^ 2 - 1) := by
  obtain ⟨hq, hqp⟩ := mem_sphericalPendulumPhaseSpace_iff_coords.1 hx
  have hp : ‖x.2‖ ^ 2 = x.2 0 ^ 2 + x.2 1 ^ 2 + x.2 2 ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct,
      Matrix.vec3_dotProduct, star_trivial]
    ring
  rw [hp]
  constructor
  · -- At a critical point, the explicit multipliers confine the image of `ker dg` to a line.
    rintro hsurj ⟨hp₂, hcrit⟩
    obtain ⟨a, b, c, hab, e₁, e₂, e₃, e₄, e₅, e₆⟩ := exists_multipliers hq hqp hp₂ hcrit
    obtain ⟨w, hw₀, hw⟩ := hsurj (a, b)
    have key : a * (fderiv ℝ sphericalPendulumEnergyMomentum x w).1 +
        b * (fderiv ℝ sphericalPendulumEnergyMomentum x w).2 =
          c * (fderiv ℝ sphericalPendulumConstraint x w).1 := by
      rw [fderiv_sphericalPendulumEnergyMomentum_apply, fderiv_sphericalPendulumConstraint_apply]
      simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.vec3_dotProduct, star_trivial]
      linear_combination w.2 0 * e₁ + w.2 1 * e₂ + w.2 2 * e₃ + w.1 0 * e₄ + w.1 1 * e₅ +
        w.1 2 * e₆
    rw [hw, hw₀, Prod.fst_zero, mul_zero] at key
    exact hab ⟨by nlinarith, by nlinarith⟩
  · -- Otherwise a multiplier relation exists; test it on the six coordinate vectors.
    refine fun hncrit ↦ by_contra fun hns ↦ ?_
    obtain ⟨a, b, c, d, hab, test⟩ := exists_multiplier_relation hx hns
    simp only [fderiv_sphericalPendulumConstraint_apply,
      fderiv_sphericalPendulumEnergyMomentum_apply] at test
    have e₁ := test (0, EuclideanSpace.single 0 1)
    have e₂ := test (0, EuclideanSpace.single 1 1)
    have e₃ := test (0, EuclideanSpace.single 2 1)
    have e₄ := test (EuclideanSpace.single 0 1, 0)
    have e₅ := test (EuclideanSpace.single 1 1, 0)
    have e₆ := test (EuclideanSpace.single 2 1, 0)
    simp only [inner_zero_right, mul_zero, Fin.isValue, EuclideanSpace.inner_single_right,
      conj_trivial, one_mul, inner_zero_left, add_zero, zero_add, PiLp.zero_apply, zero_mul, ne_eq,
      one_ne_zero, not_false_eq_true, PiLp.single_eq_of_ne, sub_self, PiLp.single_eq_same, mul_one,
      zero_sub, mul_neg, sub_zero, zero_ne_one, Fin.reduceEq, EuclideanSpace.inner_single_left]
      at e₁ e₂ e₃ e₄ e₅ e₆
    exact hncrit (crit_of_multipliers (c := c) (d := d) hq hqp hab
      (by linear_combination -e₁) (by linear_combination -e₂) (by linear_combination -e₃)
      (by linear_combination -e₄) (by linear_combination -e₅) (by linear_combination -e₆))

/-- **The critical points of the spherical pendulum.** A point `(q, p)` of the phase space `T*S²`
is a regular point of the energy–momentum map `F = (H, J)` exactly when it does not satisfy
`p₃ = 0` and `q₃ ‖p‖² = q₃² - 1`. The critical points are the two equilibria at rest at the poles
and the relative equilibria, the horizontal circular motions. -/
theorem isRegularPoint_sphericalPendulumEnergyMomentum_comp_subtypeVal_iff
    (z : {x // sphericalPendulumConstraint x = (1, 0)}) :
    IsRegularPoint 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, ℝ × ℝ) (sphericalPendulumEnergyMomentum ∘ Subtype.val) z ↔
      ¬(z.1.2 2 = 0 ∧ z.1.1 2 * ‖z.1.2‖ ^ 2 = z.1.1 2 ^ 2 - 1) := by
  rw [isRegularPoint_iff_surjective_mvfderiv,
    ← forall_exists_fderiv_iff (sphericalPendulumConstraint_eq_iff.1 z.2)]
  have hval : MDifferentiableAt 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, E × E) Subtype.val z :=
    isSmoothEmbedding_subtypeVal_sphericalPendulumConstraint.contMDiff.mdifferentiableAt
      (by simp)
  have hcomp (v) : mvfderiv 𝓘(ℝ, Fin 4 → ℝ) (sphericalPendulumEnergyMomentum ∘ Subtype.val) z v =
      fderiv ℝ sphericalPendulumEnergyMomentum z.1 (mvfderiv 𝓘(ℝ, Fin 4 → ℝ) Subtype.val z v) :=
    mvfderiv_comp_apply_of_differentiableAt
      (contDiff_sphericalPendulumEnergyMomentum (n := 1).differentiable one_ne_zero _) hval v
  have hrange := range_mvfderiv_subtypeVal_sphericalPendulumConstraint z
  refine ⟨fun h c ↦ ?_, fun h c ↦ ?_⟩
  · obtain ⟨v, hv⟩ := h c
    refine ⟨mvfderiv 𝓘(ℝ, Fin 4 → ℝ) Subtype.val z v, ?_, by rw [← hcomp, hv]⟩
    have hmem : mvfderiv 𝓘(ℝ, Fin 4 → ℝ) Subtype.val z v ∈
        (mvfderiv 𝓘(ℝ, Fin 4 → ℝ) Subtype.val z).range := ⟨v, rfl⟩
    rwa [hrange, LinearMap.mem_ker] at hmem
  · obtain ⟨w, hw₀, hw⟩ := h c
    have hmem : w ∈ (mvfderiv 𝓘(ℝ, Fin 4 → ℝ) Subtype.val z).range := by
      rwa [hrange, LinearMap.mem_ker]
    obtain ⟨v, rfl⟩ := hmem
    exact ⟨v, by rw [hcomp]; exact hw⟩

/-- The values of the energy–momentum map at the critical points of `T*S²` are the two pole values
and the minima of the effective potential. -/
private theorem crit_value {q p : E} {c : ℝ × ℝ} (hx : (q, p) ∈ sphericalPendulumPhaseSpace)
    (hp₂ : p 2 = 0) (hcrit : q 2 * ‖p‖ ^ 2 = q 2 ^ 2 - 1)
    (hF : sphericalPendulumEnergyMomentum (q, p) = c) :
    c = (-1, 0) ∨ c = (1, 0) ∨ (c.2 ≠ 0 ∧ ∃ z ∈ Ioo (-1) 1,
      IsMinOn (sphericalPendulumEffectivePotential c.2) (Ioo (-1) 1) z ∧
        sphericalPendulumEffectivePotential c.2 z = c.1) := by
  obtain ⟨hq', hqp⟩ := mem_sphericalPendulumPhaseSpace_iff_coords.1 hx
  have hp : ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct,
      Matrix.vec3_dotProduct, star_trivial]
    ring
  rw [sphericalPendulumEnergyMomentum_apply] at hF
  subst hF
  simp only at hqp
  rw [hp, hp₂] at hcrit
  rw [hp₂, mul_zero, add_zero] at hqp
  rw [hp, hp₂]
  by_cases hρ : q 0 ^ 2 + q 1 ^ 2 = 0
  · have h₀ : q 0 = 0 := by nlinarith
    have h₁ : q 1 = 0 := by nlinarith
    have hq₂ : (q 2 - 1) * (q 2 + 1) = 0 := by linear_combination hq' - hρ
    have hpp : p 0 ^ 2 + p 1 ^ 2 = 0 := by
      rcases mul_eq_zero.1 hq₂ with h | h
      · linear_combination hcrit - (p 0 ^ 2 + p 1 ^ 2 + 0 ^ 2 - q 2 - 1) * h
      · linear_combination -hcrit + (p 0 ^ 2 + p 1 ^ 2 + 0 ^ 2 - q 2 + 1) * h
    have k₀ : p 0 = 0 := by nlinarith
    have k₁ : p 1 = 0 := by nlinarith
    rw [h₀, h₁, k₀, k₁]
    rcases mul_eq_zero.1 hq₂ with h | h
    · exact Or.inr (Or.inl (Prod.ext (by simp; linarith) (by simp)))
    · exact Or.inl (Prod.ext (by simp; linarith) (by simp))
  · have hρpos : 0 < q 0 ^ 2 + q 1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hρ)
    have hz₂ : q 2 < 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
    have hz : q 2 ∈ Ioo (-1) 1 := ⟨by nlinarith, by linarith⟩
    have hS : 0 < p 0 ^ 2 + p 1 ^ 2 := by nlinarith
    have hj₂ : (q 0 * p 1 - q 1 * p 0) ^ 2 = (q 0 ^ 2 + q 1 ^ 2) * (p 0 ^ 2 + p 1 ^ 2) := by
      linear_combination -(q 0 * p 0 + q 1 * p 1) * hqp
    have hj : q 0 * p 1 - q 1 * p 0 ≠ 0 := fun h ↦ by
      rw [h] at hj₂
      nlinarith [mul_pos hρpos hS]
    refine Or.inr (Or.inr ⟨hj, q 2, hz, (isMinOn_sphericalPendulumEffectivePotential_iff hj hz).2
      (by linear_combination q 2 * hj₂ + (q 0 ^ 2 + q 1 ^ 2) * hcrit +
        (q 2 ^ 2 - 1) * hq'), ?_⟩)
    have h1z : 1 - q 2 ^ 2 ≠ 0 := by nlinarith
    rw [sphericalPendulumEffectivePotential_def, hj₂]
    field_simp
    linear_combination (p 0 ^ 2 + p 1 ^ 2) * hq'

/-- The critical values of the energy–momentum map on `T*S²`, in ambient terms. -/
private theorem exists_crit_iff (c : ℝ × ℝ) :
    (∃ x ∈ sphericalPendulumPhaseSpace, (x.2 2 = 0 ∧ x.1 2 * ‖x.2‖ ^ 2 = x.1 2 ^ 2 - 1) ∧
        sphericalPendulumEnergyMomentum x = c) ↔
      c = (-1, 0) ∨ c = (1, 0) ∨ (c.2 ≠ 0 ∧ ∃ z ∈ Ioo (-1) 1,
        IsMinOn (sphericalPendulumEffectivePotential c.2) (Ioo (-1) 1) z ∧
          sphericalPendulumEffectivePotential c.2 z = c.1) := by
  obtain ⟨h, j⟩ := c
  constructor
  · rintro ⟨⟨q, p⟩, hx, ⟨hp₂, hcrit⟩, hF⟩
    exact crit_value hx hp₂ hcrit hF
  · rintro (h | h | ⟨hj, z, hz, hmin, hh⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ h
      refine ⟨(EuclideanSpace.single 2 (-1), 0), ?_, ?_, ?_⟩ <;> simp
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ h
      refine ⟨(EuclideanSpace.single 2 1, 0), ?_, ?_, ?_⟩ <;> simp
    · simp only at hj hmin hh
      obtain ⟨x, hx, hFx⟩ := (mk_mem_image_sphericalPendulumEnergyMomentum_iff_of_isMinOn hj hz hmin
        h).2 hh.le
      obtain ⟨-, hz₀, hp₂⟩ :=
        (sphericalPendulumEnergyMomentum_eq_iff_of_isMinOn hj hz hmin hx).1 (hFx.trans (by rw [hh]))
      refine ⟨x, hx, ⟨hp₂, ?_⟩, hFx⟩
      have hcrit := (isMinOn_sphericalPendulumEffectivePotential_iff hj hz).1 hmin
      have hH := congrArg Prod.fst hFx
      rw [fst_sphericalPendulumEnergyMomentum, ← hh, sphericalPendulumEffectivePotential_def] at hH
      obtain ⟨q, p⟩ := x
      simp only [sphericalPendulumHamiltonian_apply] at hH hz₀ hp₂ ⊢
      subst hz₀
      have h1z : 1 - q 2 ^ 2 ≠ 0 := by nlinarith [hz.1, hz.2]
      field_simp at hH
      refine mul_left_cancel₀ h1z ?_
      linear_combination q 2 * hH + hcrit

/-- **The critical values of the spherical pendulum.** A value `(h, j)` is a critical value of the
energy–momentum map `F = (H, J)` on the phase space `T*S²` exactly when it is `(-1, 0)` (the
equilibrium at the south pole), `(1, 0)` (the equilibrium at the north pole), or, for `j ≠ 0`,
the minimum value `V_j(z)` of the effective potential on `(-1, 1)` (the relative equilibria with
angular momentum `j`). -/
theorem not_isRegularValue_sphericalPendulumEnergyMomentum_comp_subtypeVal_iff (c : ℝ × ℝ) :
    ¬IsRegularValue 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, ℝ × ℝ)
        (sphericalPendulumEnergyMomentum ∘ Subtype.val :
          {x // sphericalPendulumConstraint x = (1, 0)} → ℝ × ℝ) c ↔
      c = (-1, 0) ∨ c = (1, 0) ∨ (c.2 ≠ 0 ∧ ∃ z ∈ Ioo (-1) 1,
        IsMinOn (sphericalPendulumEffectivePotential c.2) (Ioo (-1) 1) z ∧
          sphericalPendulumEffectivePotential c.2 z = c.1) := by
  rw [← exists_crit_iff, isRegularValue_iff]
  push Not
  simp only [isRegularPoint_sphericalPendulumEnergyMomentum_comp_subtypeVal_iff, not_not,
    Function.comp_apply]
  constructor
  · rintro ⟨z, hz, hcrit⟩
    exact ⟨z.1, sphericalPendulumConstraint_eq_iff.1 z.2, hcrit, hz⟩
  · rintro ⟨x, hx, hcrit, hF⟩
    exact ⟨⟨x, sphericalPendulumConstraint_eq_iff.2 hx⟩, hF, hcrit⟩

end TauCeti
