/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Automorphy.Basic
import TauCeti.NumberTheory.ModularForms.Basic

/-!
# Local sections of the automorphy sheaf at a cusp from functions of the cusp coordinate

Let `D` be a normalized cusp datum of `Γ ≤ PSL(2, ℝ)`, and let `s, g ∈ SL(2, ℝ)` lift its scaling
and generator, with `ε ^ k = (-1) ^ r` for the sign `ε` of `s * g * s⁻¹`. The file
`TauCeti.Analysis.Complex.Fuchsian.Cusp.Automorphy.Basic` writes every local section `f` of the
weight-`k` automorphy sheaf on a horodisc as the frame
`TauCeti.Subgroup.CuspDatum.automorphyFrame D s k r` times a function of the cusp coordinate `q`,
its coefficient `TauCeti.Subgroup.CuspDatum.automorphyDescent D s k r f`. This file proves the
converse direction of this local trivialization: the frame times any function `G` of `q`,
`TauCeti.Subgroup.CuspDatum.automorphySection D s k r G`, is a local section. So the local
sections at a regular or irregular cusp are exactly the frame times the functions of the cusp
coordinate, in the width parameter and with the errata order convention built into the frame:
this is the local description at the cusp of the invertible sheaf on the compact quotient that the
weight-`k` transformation data induces (Diamond–Shurman §§3.5–3.6).

* The section is additive and `ℂ`-linear in `G`
  (`TauCeti.Subgroup.CuspDatum.automorphySection_add`,
  `TauCeti.Subgroup.CuspDatum.automorphySection_const_smul`).
* If `G` is holomorphic on the disc of cusp-coordinate values of the horodisc of height `A`, the
  section is holomorphic on that horodisc
  (`TauCeti.Subgroup.CuspDatum.mdifferentiableOn_automorphySection`).
* It satisfies the weight-`k` transformation law for `g` on all of `ℍ`
  (`TauCeti.Subgroup.CuspDatum.automorphySection_smul`).
* It is bounded at the cusp when `G` is continuous there
  (`TauCeti.Subgroup.CuspDatum.isBoundedAtImInfty_slash_automorphySection`).
* Its coefficient is `G`, including at the cusp
  (`TauCeti.Subgroup.CuspDatum.eqOn_automorphyDescent_automorphySection`), and every local section
  is the section of its coefficient
  (`TauCeti.Subgroup.CuspDatum.automorphySection_automorphyDescent`).

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §§2.4, 3.5–3.6, with the corrected irregular-cusp order
  convention of the errata to pp. 74–75.
-/

public section

noncomputable section

open Filter Metric Set UpperHalfPlane

open scoped Manifold MatrixGroups ModularForm Topology

namespace TauCeti.Subgroup.CuspDatum

variable {Γ : Subgroup PSL(2, ℝ)} (D : Γ.CuspDatum)

/-- **The local section of the weight-`k` automorphy sheaf at the cusp of `D` with coefficient
`G`**: the frame `TauCeti.Subgroup.CuspDatum.automorphyFrame D s k r` times `G` of the cusp
coordinate. -/
def automorphySection (s : SL(2, ℝ)) (k : ℤ) (r : ℕ) (G : ℂ → ℂ) (τ : ℍ) : ℂ :=
  automorphyFrame D s k r τ * G (coordinate D τ)

theorem automorphySection_def (s : SL(2, ℝ)) (k : ℤ) (r : ℕ) (G : ℂ → ℂ) (τ : ℍ) :
    automorphySection D s k r G τ = automorphyFrame D s k r τ * G (coordinate D τ) :=
  (rfl)

/-- The local section with zero coefficient is zero. -/
@[simp]
theorem automorphySection_zero (s : SL(2, ℝ)) (k : ℤ) (r : ℕ) :
    automorphySection D s k r 0 = 0 := by
  ext τ
  simp [automorphySection_def]

/-- The local section is additive in its coefficient. -/
theorem automorphySection_add (s : SL(2, ℝ)) (k : ℤ) (r : ℕ) (G H : ℂ → ℂ) :
    automorphySection D s k r (G + H) =
      automorphySection D s k r G + automorphySection D s k r H := by
  ext τ
  simp [automorphySection_def, mul_add]

/-- The local section commutes with scaling its coefficient by a constant. -/
theorem automorphySection_const_smul (s : SL(2, ℝ)) (k : ℤ) (r : ℕ) (c : ℂ) (G : ℂ → ℂ) :
    automorphySection D s k r (c • G) = c • automorphySection D s k r G := by
  ext τ
  simp only [automorphySection_def, Pi.smul_apply, smul_eq_mul]
  ring

variable {D} {s g : SL(2, ℝ)} {k : ℤ} {r : ℕ} {A : ℝ} {G : ℂ → ℂ}

/-- **The local section with a holomorphic coefficient is holomorphic** on the horodisc of height
`A`, when the coefficient is holomorphic on the disc of cusp-coordinate values of that horodisc. -/
theorem mdifferentiableOn_automorphySection (s : SL(2, ℝ)) (k : ℤ) (r : ℕ)
    (hG : DifferentiableOn ℂ G (ball 0 (Real.exp (-2 * Real.pi * A / D.width)))) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (automorphySection D s k r G) (horodisc D A) := fun τ hτ ↦ by
  have hq : coordinate D τ ∈ ball (0 : ℂ) (Real.exp (-2 * Real.pi * A / D.width)) := by
    rw [mem_ball_zero_iff, ← coe_qCoordinate]
    exact (norm_qCoordinate_lt_iff_mem_horodisc D A τ).mpr hτ
  have hGq : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (G ∘ coordinate D) τ :=
    (hG.differentiableAt (isOpen_ball.mem_nhds hq)).comp_mdifferentiableAt
      (mdifferentiable_coordinate D τ)
  exact ((mdifferentiable_automorphyFrame D s k r τ).mul hGq).mdifferentiableWithinAt

/-- **The transformation law of the local section with coefficient `G`.** If `s` and `g` lift the
scaling and the generator of `D`, and `ε ^ k = (-1) ^ r` for the sign `ε` of `s * g * s⁻¹`, then
the local section with any coefficient satisfies the weight-`k` transformation law for `g` on all
of `ℍ`, the cusp coordinate being invariant under `g`. -/
theorem automorphySection_smul (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hg : (g : PSL(2, ℝ)) = D.generator) (hk : ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
    (τ : ℍ) :
    automorphySection D s k r G (g • τ) =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * automorphySection D s k r G τ := by
  have hq : coordinate D (g • τ) = coordinate D τ := by
    rw [← sqrtCoordinate_sq, ← sqrtCoordinate_sq, ← pslMk_smul, hg, sqrtCoordinate_generator_smul,
      neg_sq]
  rw [automorphySection_def, automorphySection_def, automorphyFrame_smul hs hg hk, hq, mul_assoc]

/-- In the scaling coordinate, the local section with coefficient `G` is `q₂ ^ r * G (q₂ ^ 2)`
for the width parameter `q₂`. -/
private theorem slash_inv_automorphySection (hs : (s : PSL(2, ℝ)) = D.scaling) (z : ℍ) :
    (automorphySection D s k r G ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹) z =
      Function.Periodic.qParam (2 * D.width) z ^ r *
        G (Function.Periodic.qParam (2 * D.width) z ^ 2) := by
  obtain ⟨τ, rfl⟩ : ∃ τ : ℍ, z = s • τ := ⟨s⁻¹ • z, (smul_inv_smul s z).symm⟩
  have hsc : D.scaling • τ = s • τ := by rw [← hs, pslMk_smul]
  rw [Matrix.SpecialLinearGroup.slash_mapGL_inv_apply_smul, automorphySection_def,
    automorphyFrame_def, ← mul_assoc, ← mul_assoc, ← zpow_add₀ (denom_ne_zero _ _),
    add_neg_cancel, zpow_zero, one_mul, ← sqrtCoordinate_sq, sqrtCoordinate_def, hsc]

/-- **The local section with a coefficient continuous at the cusp is bounded at the cusp**: if `s`
lifts the scaling of `D` and `G` is continuous at `0`, then
`automorphySection D s k r G ∣[k] s⁻¹` is bounded at `i∞`. In the scaling coordinate this slash is
`q₂ ^ r * G q`, and `q₂ → 0` at `i∞`. -/
theorem isBoundedAtImInfty_slash_automorphySection (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hG : ContinuousAt G 0) :
    IsBoundedAtImInfty
      (automorphySection D s k r G ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹) := by
  have hq := qParam_tendsto_atImInfty (mul_pos two_pos D.width_pos)
  have hG' : ContinuousAt G ((0 : ℂ) ^ 2) := by rwa [zero_pow two_ne_zero]
  rw [funext (slash_inv_automorphySection hs)]
  exact ((hq.pow r).mul (hG'.tendsto.comp (hq.pow 2))).isBigO_one ℝ

/-- On the unit disc, the sum of the `q₂`-expansion of the local section with coefficient `G`
continuous at `0` is `q₂ ↦ q₂ ^ r * G (q₂ ^ 2)`, including at the cusp `q₂ = 0`. -/
private theorem automorphyUntwist_automorphySection (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hG : ContinuousAt G 0) {u : ℂ} (hu : ‖u‖ < 1) :
    automorphyUntwist D s k (automorphySection D s k r G) u = u ^ r * G (u ^ 2) := by
  have hw : 0 < 2 * D.width := mul_pos two_pos D.width_pos
  -- away from `0`, `u` is the width parameter of a point of the upper half-plane
  have hne {u : ℂ} (hu0 : u ≠ 0) (hu : ‖u‖ < 1) :
      ((automorphySection D s k r G ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹) ∘ ofComplex)
        (Function.Periodic.invQParam (2 * D.width) u) = u ^ r * G (u ^ 2) := by
    have him : 0 < (Function.Periodic.invQParam (2 * D.width) u).im := by
      rwa [← Function.Periodic.norm_qParam_lt_iff hw 0,
        Function.Periodic.qParam_right_inv hw.ne' hu0, mul_zero, zero_div, Real.exp_zero]
    rw [Function.comp_apply, ofComplex_apply_of_im_pos him, slash_inv_automorphySection hs,
      UpperHalfPlane.coe_mk, Function.Periodic.qParam_right_inv hw.ne' hu0]
  rw [automorphyUntwist_def, UpperHalfPlane.cuspFunction]
  rcases ne_or_eq u 0 with hu0 | rfl
  · rw [Function.Periodic.cuspFunction_eq_of_ne_zero _ _ hu0]
    exact hne hu0 hu
  -- at `0` the value is the limit, which continuity of `G` at `0` computes
  have hφ : ContinuousAt (fun v : ℂ ↦ v ^ r * G (v ^ 2)) 0 :=
    (continuousAt_id.pow r).mul (hG.comp_of_eq (continuous_pow 2).continuousAt
      (zero_pow two_ne_zero))
  rw [Function.Periodic.cuspFunction, Function.update_self]
  refine Tendsto.limUnder_eq ((hφ.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) one_pos)]
    with v hv0 hv
  exact (hne hv0 (mem_ball_zero_iff.mp hv)).symm

/-- **The coefficient of the local section with coefficient `G` is `G`** on the disc of
cusp-coordinate values of the horodisc of height `A ≥ 0`, including at the cusp `q = 0`, when `s`
lifts the scaling of `D`, `r < 2` and `G` is holomorphic there. -/
theorem eqOn_automorphyDescent_automorphySection (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hA : 0 ≤ A) (hr : r < 2)
    (hG : DifferentiableOn ℂ G (ball 0 (Real.exp (-2 * Real.pi * A / D.width)))) :
    EqOn G (automorphyDescent D s k r (automorphySection D s k r G))
      (ball 0 (Real.exp (-2 * Real.pi * A / D.width))) := by
  have hw : 0 < 2 * D.width := mul_pos two_pos D.width_pos
  set ρ := Real.exp (-2 * Real.pi * A / (2 * D.width))
  have hρ : ρ ^ 2 = Real.exp (-2 * Real.pi * A / D.width) := by
    rw [← Real.exp_natCast_mul]
    congr 1
    field_simp [D.width_pos.ne']
    push_cast
    ring
  have hρ₁ : ρ ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (by nlinarith [Real.pi_pos]) hw.le)
  have hG₂ : DifferentiableOn ℂ G ((· ^ 2) '' ball 0 ρ) := by
    rwa [image_pow_ball (Real.exp_pos _).le, hρ]
  have hU : EqOn (automorphyUntwist D s k (automorphySection D s k r G))
      (fun u ↦ u ^ r * G (u ^ 2)) (ball 0 ρ) := fun u hu ↦
    automorphyUntwist_automorphySection hs
      ((hG₂.continuousOn.continuousAt ((Complex.isOpenQuotientMap_pow 2).isOpenMap _ isOpen_ball
        |>.mem_nhds ⟨0, mem_ball_self (Real.exp_pos _), zero_pow two_ne_zero⟩)))
      ((mem_ball_zero_iff.mp hu).trans_le hρ₁)
  rw [← hρ, ← image_pow_ball (Real.exp_pos _).le, automorphyDescent_def]
  refine eqOn_descendPowTwist isOpen_ball hr (((differentiableOn_id.pow r).mul
    (hG₂.comp (differentiableOn_id.pow 2) (mapsTo_image _ _))).congr hU)
    (fun u hu ↦ apply_rootsOfUnity_two_smul_of_apply_neg ?_) hG₂.continuousOn
    fun u hu ↦ by rw [hU hu, smul_eq_mul]
  have hu' : -u ∈ ball (0 : ℂ) ρ := by rwa [mem_ball_zero_iff, norm_neg, ← mem_ball_zero_iff]
  rw [hU hu', hU hu, smul_eq_mul]
  beta_reduce
  rw [neg_sq, neg_pow, mul_assoc]

/-- **Every local section at a cusp is the local section with its coefficient**: under the
hypotheses of `TauCeti.Subgroup.CuspDatum.automorphyFrame_mul_automorphyDescent`, a function `f`
satisfying the weight-`k` transformation law for `g` on the horodisc of height `A` agrees there with
the local section whose coefficient is `TauCeti.Subgroup.CuspDatum.automorphyDescent D s k r f`. -/
theorem automorphySection_automorphyDescent {f : ℍ → ℂ} (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hg : (g : PSL(2, ℝ)) = D.generator) (hk : ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
    (hf : ∀ τ ∈ horodisc D A, f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    (hr : r < 2) :
    EqOn (automorphySection D s k r (automorphyDescent D s k r f)) f (horodisc D A) :=
  fun _ hτ ↦ automorphyFrame_mul_automorphyDescent hs hg hk hf hr hτ

end TauCeti.Subgroup.CuspDatum
