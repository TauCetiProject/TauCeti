/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Existence
public import TauCeti.Analysis.PDE.Vortex.Reduced.EquationMap
import Mathlib.Analysis.Calculus.ImplicitContDiff
import TauCeti.Analysis.PDE.Schrodinger.Realization
import TauCeti.Analysis.PDE.Vortex.Reduced.Continuity
import TauCeti.Analysis.Polynomial.Monic.OfCoeff
import TauCeti.Analysis.Sobolev.BesselPotential.Laplacian.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Smooth dependence of the reduced vortex solution on the divisor

For coefficients `c ∈ ℂ^m`, `m ≥ 1`, let `P_c = X ^ m + c_(m-1) X ^ (m-1) + ⋯ + c_0`
(`TauCeti.Polynomial.monicOfCoeff c`); the coefficients `c` are the symmetric coordinates of the
zero divisor of `P_c` in `Sym^m ℂ`, collisions of zeros included. Taubes's plane vortex with this
divisor is reconstructed from the smooth solution `w_c = TauCeti.Vortex.reducedSolution P_c` of the
reduced equation `Δw = h_c (exp (2w) - 1) / 8 + k_c`. This file proves that `w_c`, as an element
`u_c = TauCeti.Vortex.sobolevReducedSolution c` of the complex Sobolev space `H²(ℂ)`, depends
smoothly on `c` (`TauCeti.Vortex.contDiff_sobolevReducedSolution`).

The proof is the implicit function theorem for the reduced equation map
`Φ : ℂ^m × H²(ℂ) → L²(ℂ)`, `Φ(c, u) = Δu - h_c (exp (2u) - 1) / 8 - k_c`
(`TauCeti.Vortex.reducedEquationMapOfCoeff`), which is smooth with partial derivative
`D_u Φ(c, u) v = Δv - h_c exp (2u) v / 4` in `u`. Its zero `u_c`
(`TauCeti.Vortex.reducedEquationMapOfCoeff_sobolevReducedSolution`) satisfies:

* **The linearization is invertible.** At `u = u_c`, `-D_u Φ(c, u_c)` realizes the Schrödinger
  operator `-Δ + h_c exp (2 w_c) / 4`
  (`TauCeti.Vortex.integral_neg_reducedLinearizationOfCoeff_mul`), whose potential is bounded,
  nonnegative, and at least `1 / 16` outside a disc, since `h_c → 1` and `w_c → 0` at infinity.
  Every such realization is a bijection `H²(ℂ) → L²(ℂ)`
  (`TauCeti.bijective_of_integral_apply_mul_eq_integral_mul_neg_laplacian_add_mul`), so
  `D_u Φ(c, u_c)` is invertible (`TauCeti.Vortex.bijective_reducedLinearizationOfCoeff`), a
  continuous linear isomorphism `H²(ℂ) ≃ L²(ℂ)` (`TauCeti.Vortex.reducedLinearizationEquivOfCoeff`)
  by the open mapping theorem.
* **Continuity.** `c ↦ u_c` is continuous into `H²(ℂ)`
  (`TauCeti.Vortex.continuous_sobolevReducedSolution`). With `D₀ = D_u Φ(c₀, u_{c₀})`, the
  reduced equations at `c` and `c₀` give, almost everywhere,
  `D₀ (u_c - u_{c₀}) = (h_c - h_{c₀}) (exp (2 w_c) - 1) / 8 + (k_c - k_{c₀}) + R_c / 8`
  with the Taylor remainder
  `R_c = h_{c₀} (exp (2 w_c) - exp (2 w_{c₀}) - 2 exp (2 w_{c₀}) (w_c - w_{c₀}))`. The defects
  `h_c - h_{c₀}` tend to zero uniformly and `k_c - k_{c₀}` in `L²` as `c → c₀`; the reduced
  solutions are uniformly bounded near `c₀` and converge in `L²`, by the continuity of the
  minimizer of Taubes's functional (`TauCeti.Vortex.tendsto_reducedMinimizer`). So
  `D₀ (u_c - u_{c₀}) → 0` in `L²`, and `u_c → u_{c₀}` in `H²` because `D₀` is an isomorphism.
* **Smoothness.** By the implicit function theorem
  (`ContDiffAt.contDiffAt_implicitFunction`) the zeros of `Φ` near `(c₀, u_{c₀})` form the graph
  of a smooth map, and by continuity `c ↦ (c, u_c)` stays in that neighbourhood near `c₀`, so
  `u_c` is that smooth map near `c₀`. Its derivative is `-(D_u Φ)⁻¹ ∘ D_c Φ`
  (`TauCeti.Vortex.hasFDerivAt_sobolevReducedSolution`).

The continuity of the plane-vortex family in the divisor was known in `H¹(ℂ)` and uniformly
(`TauCeti.Vortex.continuous_reducedMinimizer`, `TauCeti.Vortex.tendstoUniformly_reducedSolution`);
the smoothness here is what smooth families of vortices over compact windows of the divisor
space, and of their kernel projections and right inverses, are built from.

## Main definitions

* `TauCeti.Vortex.reducedLinearizationEquivOfCoeff c`: the linearization `D_u Φ(c, u_c)` as a
  continuous linear isomorphism `H²(ℂ) ≃ L²(ℂ)`.

## Main results

* `TauCeti.Vortex.bijective_reducedLinearizationOfCoeff`: `D_u Φ(c, u_c)` is a bijection
  `H²(ℂ) → L²(ℂ)`.
* `TauCeti.Vortex.continuous_sobolevReducedSolution`: `c ↦ u_c` is continuous into `H²(ℂ)`.
* `TauCeti.Vortex.contDiff_sobolevReducedSolution`: `c ↦ u_c` is smooth into `H²(ℂ)`.
* `TauCeti.Vortex.hasFDerivAt_sobolevReducedSolution`: its derivative is
  `-(D_u Φ(c, u_c))⁻¹ ∘ D_c Φ(c, u_c)`.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

open BesselPotentialSpace TemperedDistribution MeasureTheory Filter Complex
  TauCeti.Polynomial
open scoped BesselPotentialSpace Laplacian ContDiff Topology

namespace TauCeti.Vortex

variable {m : ℕ}

/-! ### The linearization is invertible -/

/-- The potential `h_c exp (2 w_c) / 4` of the linearization of the reduced equation at its
solution. -/
private def linearizationPotential (c : Fin m → ℂ) (z : ℂ) : ℝ :=
  backgroundWeight ((monicOfCoeff c).eval ·) z *
    Real.exp (2 * reducedSolution (monicOfCoeff c) z) / 4

private theorem linearizationPotential_nonneg (c : Fin m → ℂ) (z : ℂ) :
    0 ≤ linearizationPotential c z := by
  have := backgroundWeight_nonneg ((monicOfCoeff c).eval ·) z
  unfold linearizationPotential
  positivity

private theorem memLp_top_linearizationPotential (c : Fin m → ℂ) :
    MemLp (linearizationPotential c) ⊤ (volume : Measure ℂ) := by
  obtain ⟨M, hM⟩ := exists_abs_reducedSolution_le (monicOfCoeff c)
  have hcont : Continuous (linearizationPotential c) :=
    (((continuous_backgroundWeight (monicOfCoeff c).continuous).mul
      ((continuous_const.mul (contDiff_reducedSolution _).continuous).rexp)).div_const 4)
  refine memLp_top_of_bound hcont.aestronglyMeasurable (Real.exp (2 * M) / 4)
    (.of_forall fun z ↦ ?_)
  have h1 := (backgroundWeight_lt_one ((monicOfCoeff c).eval ·) z).le
  have hw : 2 * reducedSolution (monicOfCoeff c) z ≤ 2 * M := by
    linarith [(abs_le.1 (hM z)).2]
  rw [Real.norm_eq_abs, abs_of_nonneg (linearizationPotential_nonneg c z)]
  unfold linearizationPotential
  gcongr
  calc backgroundWeight _ z * Real.exp _ ≤ 1 * Real.exp (2 * M) :=
        mul_le_mul h1 (Real.exp_le_exp.2 hw) (Real.exp_pos _).le zero_le_one
    _ = Real.exp (2 * M) := one_mul _

/-- Outside a disc, the potential of the linearization is at least `1 / 16`: there `h_c ≥ 1 / 2`,
since `|P_c| ≥ 1` (`|P_c| → ∞` for `m ≥ 1`, and `P_c = 1` for `m = 0`), and `exp (2 w_c) ≥ 1 / 2`,
since `w_c → 0`. -/
private theorem exists_forall_le_linearizationPotential (c : Fin m → ℂ) :
    ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → 1 / 16 ≤ linearizationPotential c z := by
  have hP : ∀ᶠ z in cocompact ℂ, 1 ≤ ‖(monicOfCoeff c).eval z‖ := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have h1 : monicOfCoeff c = 1 :=
        (monic_monicOfCoeff c).natDegree_eq_zero.1 (natDegree_monicOfCoeff c)
      simp [h1]
    have hdeg : 0 < (monicOfCoeff c).degree :=
      _root_.Polynomial.natDegree_pos_iff_degree_pos.1 (by rwa [natDegree_monicOfCoeff])
    exact (_root_.Polynomial.tendsto_norm_atTop _ hdeg
      tendsto_norm_cocompact_atTop).eventually_ge_atTop 1
  have hw : ∀ᶠ z in cocompact ℂ, -(1 / 4) < reducedSolution (monicOfCoeff c) z :=
    (tendsto_reducedSolution_cocompact _).eventually (lt_mem_nhds (by norm_num))
  rw [← Metric.cobounded_eq_cocompact] at hP hw
  obtain ⟨R, -, hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.1 (hP.and hw)
  refine ⟨R, fun z hz ↦ ?_⟩
  obtain ⟨hPz, hwz⟩ := hR (show R ≤ ‖z‖ from hz.le)
  have hh : 1 / 2 ≤ backgroundWeight ((monicOfCoeff c).eval ·) z := by
    rw [backgroundWeight_eq_one_sub_inv]
    have : (1 + ‖(monicOfCoeff c).eval z‖ ^ 2)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have he : 1 / 2 ≤ Real.exp (2 * reducedSolution (monicOfCoeff c) z) := by
    linarith [Real.add_one_le_exp (2 * reducedSolution (monicOfCoeff c) z)]
  unfold linearizationPotential
  nlinarith

/-- **Green's identity for the linearization.** At the reduced solution, `-D_u Φ(c, u_c)` realizes
the Schrödinger operator `-Δ + h_c exp (2 w_c) / 4`: for every `v ∈ H²(ℂ)` and every smooth
compactly supported real `φ`,
`∫ (-D_u Φ(c, u_c) v) φ = ∫ v (-Δφ + h_c exp (2 w_c) φ / 4)`. -/
theorem integral_neg_reducedLinearizationOfCoeff_mul (c : Fin m → ℂ) (v : H^{2}(ℂ))
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∫ z, (-reducedLinearizationOfCoeff c (sobolevReducedSolution c) v) z * (φ z : ℂ) =
      ∫ z, inclusionLp zero_le_two v z *
        ((-Δ φ z + backgroundWeight ((monicOfCoeff c).eval ·) z *
          Real.exp (2 * reducedSolution (monicOfCoeff c) z) / 4 * φ z : ℝ) : ℂ) := by
  set V := inclusionLp zero_le_two v
  set L := inclusionLp le_rfl (laplacianCLM 0 (inclusion (by norm_num) v))
  set Q := linearizationPotential c
  have hQ := memLp_top_linearizationPotential c
  have hφ2 : MemLp (fun z ↦ (φ z : ℂ)) 2 volume :=
    (hφ.continuous.memLp_of_hasCompactSupport hc).ofReal
  have hΔφ2 : MemLp (fun z ↦ (Δ φ z : ℂ)) 2 volume :=
    ((hφ.of_le (by simp)).continuous_laplacian.memLp_of_hasCompactSupport hc.laplacian).ofReal
  have hQφ2 : MemLp (fun z ↦ ((φ z * Q z : ℝ) : ℂ)) 2 volume :=
    ((hφ.continuous.memLp_of_hasCompactSupport (p := 2) hc).fun_mul hQ :
      MemLp (fun z ↦ φ z * Q z) 2 volume).ofReal
  -- Green's identity moves the Laplacian from `v` to `φ`.
  have hG : ∫ z, L z * (φ z : ℂ) = ∫ z, V z * (Δ φ z : ℂ) := by
    have h := integral_inclusionLp_laplacianCLM_mul le_rfl (inclusion (by norm_num) v) hφ hc
    rwa [inclusionLp_inclusion] at h
  have hl : ∫ z, (-reducedLinearizationOfCoeff c (sobolevReducedSolution c) v) z * (φ z : ℂ) =
      ∫ z, (-(L z * (φ z : ℂ)) + V z * ((φ z * Q z : ℝ) : ℂ)) := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_neg (reducedLinearizationOfCoeff c (sobolevReducedSolution c) v),
      coeFn_reducedLinearizationOfCoeff c (sobolevReducedSolution c) v,
      coeFn_inclusionLp_sobolevReducedSolution c] with z h₀ h₁ h₂
    rw [h₀, Pi.neg_apply, h₁, h₂, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
      ← Complex.ofReal_exp]
    simp only [Q, linearizationPotential]
    push_cast
    ring
  have hr : ∫ z, V z * ((-Δ φ z + backgroundWeight ((monicOfCoeff c).eval ·) z *
        Real.exp (2 * reducedSolution (monicOfCoeff c) z) / 4 * φ z : ℝ) : ℂ) =
      ∫ z, (-(V z * (Δ φ z : ℂ)) + V z * ((φ z * Q z : ℝ) : ℂ)) := by
    refine integral_congr_ae (.of_forall fun z ↦ ?_)
    simp only [Q, linearizationPotential]
    push_cast
    ring
  have i₁ : Integrable fun z ↦ -(L z * (φ z : ℂ)) := ((Lp.memLp L).integrable_mul hφ2).neg
  have i₂ : Integrable fun z ↦ -(V z * (Δ φ z : ℂ)) := ((Lp.memLp V).integrable_mul hΔφ2).neg
  have i₃ : Integrable fun z ↦ V z * ((φ z * Q z : ℝ) : ℂ) := (Lp.memLp V).integrable_mul hQφ2
  rw [hl, hr, integral_add i₁ i₃, integral_add i₂ i₃, integral_neg, integral_neg, hG]

/-- **The linearization of the reduced equation is invertible.** At the reduced solution `u_c`,
the partial derivative `D_u Φ(c, u_c) v = Δv - h_c exp (2 w_c) v / 4` is a bijection
`H²(ℂ) → L²(ℂ)`. -/
theorem bijective_reducedLinearizationOfCoeff (c : Fin m → ℂ) :
    Function.Bijective (reducedLinearizationOfCoeff c (sobolevReducedSolution c)) := by
  obtain ⟨R, hR⟩ := exists_forall_le_linearizationPotential c
  have h := bijective_of_integral_apply_mul_eq_integral_mul_neg_laplacian_add_mul
    (fun v ↦ -reducedLinearizationOfCoeff c (sobolevReducedSolution c) v)
    (P := fun z ↦ backgroundWeight ((monicOfCoeff c).eval ·) z *
      Real.exp (2 * reducedSolution (monicOfCoeff c) z) / 4)
    (memLp_top_linearizationPotential c) (.of_forall (linearizationPotential_nonneg c))
    (by norm_num : (0 : ℝ) < 1 / 16) (.of_forall hR)
    fun v φ hφ hc ↦ integral_neg_reducedLinearizationOfCoeff_mul c v hφ hc
  simpa [Function.comp_def] using neg_bijective.comp h

/-- **The linearization as an isomorphism.** At the reduced solution `u_c`, the partial derivative
`D_u Φ(c, u_c)` of the reduced equation map, as a continuous linear isomorphism
`H²(ℂ) ≃ L²(ℂ)`. -/
def reducedLinearizationEquivOfCoeff (c : Fin m → ℂ) :
    H^{2}(ℂ) ≃L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  .ofBijective (reducedLinearizationOfCoeff c (sobolevReducedSolution c))
    (LinearMap.ker_eq_bot.2 (bijective_reducedLinearizationOfCoeff c).1)
    (LinearMap.range_eq_top.2 (bijective_reducedLinearizationOfCoeff c).2)

@[simp]
theorem coe_reducedLinearizationEquivOfCoeff (c : Fin m → ℂ) :
    (reducedLinearizationEquivOfCoeff c : H^{2}(ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ)) =
      reducedLinearizationOfCoeff c (sobolevReducedSolution c) :=
  ContinuousLinearEquiv.coe_ofBijective _ _ _

@[simp]
theorem reducedLinearizationEquivOfCoeff_apply (c : Fin m → ℂ) (v : H^{2}(ℂ)) :
    reducedLinearizationEquivOfCoeff c v =
      reducedLinearizationOfCoeff c (sobolevReducedSolution c) v := by
  rw [← ContinuousLinearEquiv.coe_coe, coe_reducedLinearizationEquivOfCoeff]

/-! ### Continuity in `H²(ℂ)` -/

/-- The pointwise estimate behind the continuity of `c ↦ u_c`: if `|h - h₀| ≤ ε`, `0 ≤ h₀ ≤ 1`
and `|a|, |b| ≤ M`, then the difference of the reduced equations at `(h, a)` and `(h₀, b)`,
corrected by the linearization at `(h₀, b)`, is at most `ε e^{2M} |a| / 4 + e^{2M} |a - b| / 2`. -/
private theorem abs_reducedDefect_le {h h₀ a b ε M : ℝ} (hε : |h - h₀| ≤ ε) (h₀0 : 0 ≤ h₀)
    (h₀1 : h₀ ≤ 1) (ha : |a| ≤ M) (hb : |b| ≤ M) :
    |(h - h₀) * (Real.exp (2 * a) - 1) / 8 +
        h₀ * (Real.exp (2 * a) - Real.exp (2 * b) - 2 * Real.exp (2 * b) * (a - b)) / 8| ≤
      ε * Real.exp (2 * M) / 4 * |a| + Real.exp (2 * M) / 2 * |a - b| := by
  set e := Real.exp (2 * M)
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans hε
  have h1 : |Real.exp (2 * a) - 1| ≤ 2 * |a| * e :=
    abs_exp_sub_one_le_mul_exp (by rw [abs_mul, abs_two]) (by rw [abs_mul, abs_two]; linarith)
  have h2 : |Real.exp (2 * a) - Real.exp (2 * b)| ≤ e * (2 * |a - b|) := by
    have h := Real.abs_exp_sub_exp_le (a := 2 * a) (b := 2 * b) (M := 2 * M)
      (by linarith [(abs_le.1 ha).2]) (by linarith [(abs_le.1 hb).2])
    rwa [← mul_sub, abs_mul, abs_two] at h
  have h3 : Real.exp (2 * b) ≤ e := Real.exp_le_exp.2 (by linarith [(abs_le.1 hb).2])
  have hX : |(h - h₀) * (Real.exp (2 * a) - 1) / 8| ≤ ε * (2 * |a| * e) / 8 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    gcongr
  have hY : |h₀ * (Real.exp (2 * a) - Real.exp (2 * b) - 2 * Real.exp (2 * b) * (a - b)) / 8| ≤
      (e * (2 * |a - b|) + 2 * e * |a - b|) / 8 := by
    rw [abs_div, abs_mul, abs_of_nonneg h₀0, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    gcongr
    calc h₀ * |Real.exp (2 * a) - Real.exp (2 * b) - 2 * Real.exp (2 * b) * (a - b)|
        ≤ 1 * |Real.exp (2 * a) - Real.exp (2 * b) - 2 * Real.exp (2 * b) * (a - b)| :=
          mul_le_mul_of_nonneg_right h₀1 (abs_nonneg _)
      _ ≤ |Real.exp (2 * a) - Real.exp (2 * b)| + |2 * Real.exp (2 * b) * (a - b)| := by
          rw [one_mul]
          exact abs_sub _ _
      _ ≤ e * (2 * |a - b|) + 2 * e * |a - b| := by
          rw [abs_mul, abs_mul, abs_two, abs_of_pos (Real.exp_pos _)]
          gcongr
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ ε * (2 * |a| * e) / 8 + (e * (2 * |a - b|) + 2 * e * |a - b|) / 8 := add_le_add hX hY
    _ = ε * e / 4 * |a| + e / 2 * |a - b| := by ring

/-- The `L²` function of `u_c - u_{c₀}` is `w_c - w_{c₀}`. -/
private theorem coeFn_inclusionLp_sobolevReducedSolution_sub (c c₀ : Fin m → ℂ) :
    ⇑(inclusionLp zero_le_two (sobolevReducedSolution c - sobolevReducedSolution c₀)) =ᵐ[volume]
      fun z ↦ ((reducedSolution (monicOfCoeff c) - reducedSolution (monicOfCoeff c₀)) z : ℂ) :=
  (coeFn_inclusionLp_sub_ae_eq zero_le_two (coeFn_inclusionLp_sobolevReducedSolution c)
    (coeFn_inclusionLp_sobolevReducedSolution c₀)).mono fun z hz ↦ by
      simp only [hz, Pi.sub_apply, Complex.ofReal_sub]

/-- **The linearization at `c₀` of the difference of two reduced solutions.** With
`D₀ = D_u Φ(c₀, u_{c₀})`, the function `D₀ (u_c - u_{c₀}) - (k_c - k_{c₀})` is almost everywhere
`(h_c - h₀) (exp (2 w_c) - 1) / 8 + h₀ (exp (2 w_c) - exp (2 w₀) - 2 exp (2 w₀) (w_c - w₀)) / 8`,
by the reduced equations of `w_c` and `w₀ = w_{c₀}`. -/
private theorem coeFn_reducedLinearizationOfCoeff_sub_sub (hm : 0 < m) (c c₀ : Fin m → ℂ) :
    ⇑(reducedLinearizationOfCoeff c₀ (sobolevReducedSolution c₀)
        (sobolevReducedSolution c - sobolevReducedSolution c₀) -
        (backgroundSourceLp hm c - backgroundSourceLp hm c₀)) =ᵐ[volume] fun z ↦
      (((backgroundWeight ((monicOfCoeff c).eval ·) z -
            backgroundWeight ((monicOfCoeff c₀).eval ·) z) *
          (Real.exp (2 * reducedSolution (monicOfCoeff c) z) - 1) / 8 +
        backgroundWeight ((monicOfCoeff c₀).eval ·) z *
          (Real.exp (2 * reducedSolution (monicOfCoeff c) z) -
            Real.exp (2 * reducedSolution (monicOfCoeff c₀) z) -
            2 * Real.exp (2 * reducedSolution (monicOfCoeff c₀) z) *
              (reducedSolution (monicOfCoeff c) z - reducedSolution (monicOfCoeff c₀) z)) / 8 :
        ℝ) : ℂ) := by
  have hP : 0 < (monicOfCoeff c).natDegree := by rwa [natDegree_monicOfCoeff]
  have hP₀ : 0 < (monicOfCoeff c₀).natDegree := by rwa [natDegree_monicOfCoeff]
  have hw : ContDiff ℝ 2 (reducedSolution (monicOfCoeff c)) :=
    (contDiff_reducedSolution _).of_le (by simp)
  have hw₀ : ContDiff ℝ 2 (reducedSolution (monicOfCoeff c₀)) :=
    (contDiff_reducedSolution _).of_le (by simp)
  have hδ := coeFn_inclusionLp_sobolevReducedSolution_sub c c₀
  filter_upwards [Lp.coeFn_sub (reducedLinearizationOfCoeff c₀ (sobolevReducedSolution c₀)
      (sobolevReducedSolution c - sobolevReducedSolution c₀))
      (backgroundSourceLp hm c - backgroundSourceLp hm c₀),
    Lp.coeFn_sub (backgroundSourceLp hm c) (backgroundSourceLp hm c₀),
    coeFn_backgroundSourceLp hm c, coeFn_backgroundSourceLp hm c₀,
    coeFn_reducedLinearizationOfCoeff c₀ (sobolevReducedSolution c₀)
      (sobolevReducedSolution c - sobolevReducedSolution c₀),
    coeFn_inclusionLp_laplacianCLM_ae_eq
      (f := reducedSolution (monicOfCoeff c) - reducedSolution (monicOfCoeff c₀)) le_rfl
      (hw.sub hw₀)
      (u := inclusion (by norm_num) (sobolevReducedSolution c - sobolevReducedSolution c₀))
      (by rwa [inclusionLp_inclusion]),
    coeFn_inclusionLp_sobolevReducedSolution c₀, hδ] with z h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  rw [h₁, Pi.sub_apply, h₂, Pi.sub_apply, h₃, h₄, h₅, h₆, h₇, h₈, Pi.sub_apply,
    ContDiffAt.laplacian_sub hw.contDiffAt hw₀.contDiffAt, laplacian_reducedSolution hP,
    laplacian_reducedSolution hP₀, backgroundSource_def, backgroundSource_def,
    ← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  push_cast
  ring

/-- **The linearized difference of two reduced solutions is small.** If `|w_c|, |w_{c₀}| ≤ M`,
then with `D₀ = D_u Φ(c₀, u_{c₀})`,
`‖D₀ (u_c - u_{c₀})‖ ≤ ‖φ_c - φ_{c₀}‖ e^{2M} ‖w_c‖ / 4 + e^{2M} ‖w_c - w_{c₀}‖ / 2 + ‖k_c - k_{c₀}‖`
in `L²`, where `φ_c = 1 - h_c` is the defect of the background weight. -/
private theorem norm_reducedLinearizationOfCoeff_sub_le (hm : 0 < m) {c c₀ : Fin m → ℂ} {M : ℝ}
    (hM : ∀ z, |reducedSolution (monicOfCoeff c) z| ≤ M)
    (hM₀ : ∀ z, |reducedSolution (monicOfCoeff c₀) z| ≤ M) :
    ‖reducedLinearizationOfCoeff c₀ (sobolevReducedSolution c₀)
        (sobolevReducedSolution c - sobolevReducedSolution c₀)‖ ≤
      ‖backgroundDefect (monicOfCoeff c) - backgroundDefect (monicOfCoeff c₀)‖ *
            Real.exp (2 * M) / 4 * ‖inclusionLp zero_le_two (sobolevReducedSolution c)‖ +
          Real.exp (2 * M) / 2 *
            ‖inclusionLp zero_le_two (sobolevReducedSolution c - sobolevReducedSolution c₀)‖ +
        ‖backgroundSourceLp hm c - backgroundSourceLp hm c₀‖ := by
  set ε := ‖backgroundDefect (monicOfCoeff c) - backgroundDefect (monicOfCoeff c₀)‖
  -- The background weights `h = 1 - φ` differ by at most `ε`.
  have hhε (z : ℂ) : |backgroundWeight ((monicOfCoeff c).eval ·) z -
      backgroundWeight ((monicOfCoeff c₀).eval ·) z| ≤ ε := by
    have h :=
      (backgroundDefect (monicOfCoeff c) - backgroundDefect (monicOfCoeff c₀)).norm_coe_le_norm z
    rw [sub_apply, backgroundDefect_apply,
      backgroundDefect_apply, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
    rwa [backgroundWeight_eq_one_sub_inv, backgroundWeight_eq_one_sub_inv,
      show ∀ a b : ℝ, 1 - a - (1 - b) = -(a - b) from fun a b ↦ by ring, abs_neg]
  have hbound : ∀ᵐ z ∂volume,
      ‖(reducedLinearizationOfCoeff c₀ (sobolevReducedSolution c₀)
          (sobolevReducedSolution c - sobolevReducedSolution c₀) -
          (backgroundSourceLp hm c - backgroundSourceLp hm c₀)) z‖ ≤
        ε * Real.exp (2 * M) / 4 * ‖inclusionLp zero_le_two (sobolevReducedSolution c) z‖ +
          Real.exp (2 * M) / 2 *
            ‖inclusionLp zero_le_two (sobolevReducedSolution c - sobolevReducedSolution c₀) z‖ := by
    filter_upwards [coeFn_reducedLinearizationOfCoeff_sub_sub hm c c₀,
      coeFn_inclusionLp_sobolevReducedSolution c,
      coeFn_inclusionLp_sobolevReducedSolution_sub c c₀] with z h₁ h₂ h₃
    rw [h₁, h₂, h₃, Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, Real.norm_eq_abs, Pi.sub_apply]
    exact abs_reducedDefect_le (hhε z) (backgroundWeight_nonneg _ z)
      (backgroundWeight_lt_one _ z).le (hM z) (hM₀ z)
  have h := Lp.norm_le_add_of_ae_norm_le (by positivity) (by positivity) hbound
  calc _ = ‖(reducedLinearizationOfCoeff c₀ (sobolevReducedSolution c₀)
          (sobolevReducedSolution c - sobolevReducedSolution c₀) -
          (backgroundSourceLp hm c - backgroundSourceLp hm c₀)) +
        (backgroundSourceLp hm c - backgroundSourceLp hm c₀)‖ := by rw [sub_add_cancel]
    _ ≤ _ := (norm_add_le _ _).trans (by linarith)

/-- The reduced solutions are uniformly bounded near `c₀`: if `|w_{c₀}| ≤ M`, then eventually
`|w_c| ≤ M + 1`. -/
private theorem eventually_forall_abs_reducedSolution_le (hm : 0 < m) {c₀ : Fin m → ℂ} {M : ℝ}
    (hM : ∀ z, |reducedSolution (monicOfCoeff c₀) z| ≤ M) :
    ∀ᶠ c in 𝓝 c₀, ∀ z, |reducedSolution (monicOfCoeff c) z| ≤ M + 1 := by
  have hunif := tendstoUniformly_reducedSolution (P := fun c : Fin m → ℂ ↦ monicOfCoeff c)
    (l := 𝓝 c₀) (by rwa [natDegree_monicOfCoeff])
    (.of_forall fun c ↦ by rw [natDegree_monicOfCoeff, natDegree_monicOfCoeff])
    fun k ↦ (contDiff_coeff_monicOfCoeff (n := 0) k).continuous.tendsto c₀
  filter_upwards [Metric.tendstoUniformly_iff.1 hunif 1 one_pos] with c hc z
  have h1 := hc z
  rw [Real.dist_eq] at h1
  have h2 := hM z
  have h3 := abs_sub_abs_le_abs_sub (reducedSolution (monicOfCoeff c) z)
    (reducedSolution (monicOfCoeff c₀) z)
  rw [abs_sub_comm] at h1
  linarith

/-- The reduced solutions converge in `L²` as `c → c₀`, since the minimizers of Taubes's
functional converge in `H¹`. -/
private theorem tendsto_norm_inclusionLp_sobolevReducedSolution_sub (hm : 0 < m)
    (c₀ : Fin m → ℂ) :
    Tendsto (fun c ↦
      ‖inclusionLp zero_le_two (sobolevReducedSolution c - sobolevReducedSolution c₀)‖) (𝓝 c₀)
      (𝓝 0) := by
  have hP₀ : 0 < (monicOfCoeff c₀).natDegree := by rwa [natDegree_monicOfCoeff]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun c ↦ ?_)
    (tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_reducedMinimizer hP₀
      (.of_forall fun c ↦ by rw [natDegree_monicOfCoeff, natDegree_monicOfCoeff])
      fun k ↦ (contDiff_coeff_monicOfCoeff (n := 0) k).continuous.tendsto c₀))
  have hP : 0 < (monicOfCoeff c).natDegree := by rwa [natDegree_monicOfCoeff]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  refine le_trans (le_of_eq (integral_congr_ae ?_))
    (integral_reducedSolution_sub_sq_le_norm_sub_sq hP hP₀)
  filter_upwards [coeFn_inclusionLp_sobolevReducedSolution_sub c c₀] with z hz
  rw [hz, Complex.norm_real, Real.norm_eq_abs, sq_abs, Pi.sub_apply]

/-- **The reduced solution depends continuously on the divisor** in `H²(ℂ)`. -/
theorem continuous_sobolevReducedSolution : Continuous (sobolevReducedSolution (m := m)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact continuous_of_const fun c c' ↦ by rw [Subsingleton.elim c c']
  refine continuous_iff_continuousAt.2 fun c₀ ↦ ?_
  set e := reducedLinearizationEquivOfCoeff c₀
  have hδ := tendsto_norm_inclusionLp_sobolevReducedSolution_sub hm c₀
  have hε : Tendsto (fun c : Fin m → ℂ ↦
      ‖backgroundDefect (monicOfCoeff c) - backgroundDefect (monicOfCoeff c₀)‖) (𝓝 c₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1
      (contDiff_backgroundDefect_monicOfCoeff.continuous.tendsto c₀)
  have hK : Tendsto (fun c ↦ ‖backgroundSourceLp hm c - backgroundSourceLp hm c₀‖) (𝓝 c₀)
      (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 ((contDiff_backgroundSourceLp hm).continuous.tendsto c₀)
  obtain ⟨M₀, hM₀⟩ := exists_abs_reducedSolution_le (monicOfCoeff c₀)
  set M := M₀ + 1
  set W₀ := ‖inclusionLp zero_le_two (sobolevReducedSolution c₀)‖
  set C := ‖(e.symm : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] H^{2}(ℂ))‖
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  -- `u_c - u_{c₀} = D₀⁻¹ D₀ (u_c - u_{c₀})`, and `D₀ (u_c - u_{c₀}) → 0` in `L²`.
  refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) ?_ (?_ : Tendsto (fun c ↦ C *
    (‖backgroundDefect (monicOfCoeff c) - backgroundDefect (monicOfCoeff c₀)‖ *
        Real.exp (2 * M) / 4 * (W₀ +
          ‖inclusionLp zero_le_two (sobolevReducedSolution c - sobolevReducedSolution c₀)‖) +
      Real.exp (2 * M) / 2 *
        ‖inclusionLp zero_le_two (sobolevReducedSolution c - sobolevReducedSolution c₀)‖ +
      ‖backgroundSourceLp hm c - backgroundSourceLp hm c₀‖)) (𝓝 c₀) (𝓝 0))
  · filter_upwards [eventually_forall_abs_reducedSolution_le hm hM₀] with c hc
    have hD := norm_reducedLinearizationOfCoeff_sub_le hm hc
      (fun z ↦ (hM₀ z).trans (by linarith))
    have hW : ‖inclusionLp zero_le_two (sobolevReducedSolution c)‖ ≤ W₀ +
        ‖inclusionLp zero_le_two (sobolevReducedSolution c - sobolevReducedSolution c₀)‖ := by
      rw [map_sub]
      exact norm_le_norm_add_norm_sub' _ _
    calc ‖sobolevReducedSolution c - sobolevReducedSolution c₀‖
        = ‖e.symm (reducedLinearizationOfCoeff c₀ (sobolevReducedSolution c₀)
            (sobolevReducedSolution c - sobolevReducedSolution c₀))‖ := by
          rw [← reducedLinearizationEquivOfCoeff_apply, ContinuousLinearEquiv.symm_apply_apply]
      _ ≤ C * ‖reducedLinearizationOfCoeff c₀ (sobolevReducedSolution c₀)
            (sobolevReducedSolution c - sobolevReducedSolution c₀)‖ :=
          (e.symm : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] H^{2}(ℂ)).le_opNorm _
      _ ≤ _ := by
          gcongr
          refine hD.trans ?_
          gcongr
  · have h0 : (0 : ℝ) =
        C * (0 * Real.exp (2 * M) / 4 * (W₀ + 0) + Real.exp (2 * M) / 2 * 0 + 0) := by
      ring
    rw [h0]
    exact tendsto_const_nhds.mul ((((hε.mul_const _).div_const _).mul
      (tendsto_const_nhds.add hδ)).add (hδ.const_mul _) |>.add hK)

/-! ### Smoothness -/

/-- The partial derivative in `u` at `(c₀, u_{c₀})` of the reduced equation map, regarded as a
function on `ℂ^m × H²(ℂ)`, is `D_u Φ(c₀, u_{c₀})`. -/
private theorem fderiv_comp_inr_reducedEquationMapOfCoeff (hm : 0 < m) (c₀ : Fin m → ℂ) :
    fderiv ℝ (fun p : (Fin m → ℂ) × H^{2}(ℂ) ↦ reducedEquationMapOfCoeff hm p.1 p.2)
        (c₀, sobolevReducedSolution c₀) ∘L .inr ℝ (Fin m → ℂ) H^{2}(ℂ) =
      (reducedLinearizationOfCoeff c₀ (sobolevReducedSolution c₀)).restrictScalars ℝ :=
  ((((contDiff_reducedEquationMapOfCoeff hm).differentiable (by simp)) _).hasFDerivAt.comp
    (sobolevReducedSolution c₀) (hasFDerivAt_prodMk_right c₀ (sobolevReducedSolution c₀))).unique
    ((hasFDerivAt_reducedEquationMapOfCoeff hm c₀ _).restrictScalars ℝ)

/-- The partial derivative in `u` at `(c₀, u_{c₀})` of the reduced equation map is invertible. -/
private theorem isInvertible_fderiv_comp_inr_reducedEquationMapOfCoeff (hm : 0 < m)
    (c₀ : Fin m → ℂ) :
    (fderiv ℝ (fun p : (Fin m → ℂ) × H^{2}(ℂ) ↦ reducedEquationMapOfCoeff hm p.1 p.2)
        (c₀, sobolevReducedSolution c₀) ∘L .inr ℝ (Fin m → ℂ) H^{2}(ℂ)).IsInvertible := by
  set e := reducedLinearizationEquivOfCoeff c₀
  rw [fderiv_comp_inr_reducedEquationMapOfCoeff]
  refine .of_inverse
    (g := (e.symm : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] H^{2}(ℂ)).restrictScalars ℝ)
    (ContinuousLinearMap.ext fun v ↦ ?_) (ContinuousLinearMap.ext fun v ↦ ?_)
  · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.id_apply,
      ← reducedLinearizationEquivOfCoeff_apply, e, ContinuousLinearEquiv.apply_symm_apply]
  · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.id_apply,
      ← reducedLinearizationEquivOfCoeff_apply, e, ContinuousLinearEquiv.symm_apply_apply]

/-- Near `c₀`, the reduced solution is the implicit function of `Φ(c, u) = 0` through
`(c₀, u_{c₀})`: the zeros of `Φ` near `(c₀, u_{c₀})` form the graph of that function, and
`c ↦ (c, u_c)` stays near `(c₀, u_{c₀})` by continuity. -/
private theorem implicitFunction_eventuallyEq_sobolevReducedSolution (hm : 0 < m)
    (c₀ : Fin m → ℂ) :
    ((contDiff_reducedEquationMapOfCoeff hm).contDiffAt (x := (c₀, sobolevReducedSolution c₀))
      ).implicitFunction (by simp) (isInvertible_fderiv_comp_inr_reducedEquationMapOfCoeff hm c₀)
      =ᶠ[𝓝 c₀] sobolevReducedSolution := by
  have hcont : Tendsto (fun c ↦ (c, sobolevReducedSolution c)) (𝓝 c₀)
      (𝓝 (c₀, sobolevReducedSolution c₀)) :=
    (continuous_id.prodMk continuous_sobolevReducedSolution).tendsto c₀
  have hΦ := (contDiff_reducedEquationMapOfCoeff hm).contDiffAt
    (x := (c₀, sobolevReducedSolution c₀))
  filter_upwards [hcont.eventually (hΦ.eventually_apply_eq_iff_implicitFunction (by simp)
      (isInvertible_fderiv_comp_inr_reducedEquationMapOfCoeff hm c₀))] with c hc
  exact hc.1 (by simp only [reducedEquationMapOfCoeff_sobolevReducedSolution])

/-- **The reduced solution depends smoothly on the divisor.** The map `c ↦ u_c` from the
symmetric coordinates `c ∈ ℂ^m` of the divisor to `H²(ℂ)` is smooth, collisions of zeros
included. -/
theorem contDiff_sobolevReducedSolution : ContDiff ℝ ∞ (sobolevReducedSolution (m := m)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h : sobolevReducedSolution (m := 0) = fun _ ↦ sobolevReducedSolution default :=
      funext fun c ↦ by rw [Subsingleton.elim c default]
    rw [h]
    exact contDiff_const
  exact contDiff_iff_contDiffAt.2 fun c₀ ↦
    ((contDiff_reducedEquationMapOfCoeff hm).contDiffAt.contDiffAt_implicitFunction (by simp)
      (isInvertible_fderiv_comp_inr_reducedEquationMapOfCoeff hm c₀)).congr_of_eventuallyEq
      (implicitFunction_eventuallyEq_sobolevReducedSolution hm c₀).symm

/-- **The derivative of the reduced solution in the divisor.** The derivative of `c ↦ u_c` is
`-(D_u Φ(c, u_c))⁻¹ ∘ D_c Φ(c, u_c)`: differentiating `Φ(c, u_c) = 0` gives
`D_u Φ(c, u_c) (u_c' x) = -D_c Φ(c, u_c) x` for every direction `x ∈ ℂ^m`. -/
theorem hasFDerivAt_sobolevReducedSolution (hm : 0 < m) (c : Fin m → ℂ) :
    HasFDerivAt sobolevReducedSolution
      (-((reducedLinearizationOfCoeff c (sobolevReducedSolution c)).restrictScalars ℝ).inverse ∘L
        fderiv ℝ (fun c' ↦ reducedEquationMapOfCoeff hm c' (sobolevReducedSolution c)) c) c := by
  have hΦ := ((contDiff_reducedEquationMapOfCoeff hm).differentiable (by simp)
    (c, sobolevReducedSolution c)).hasFDerivAt
  -- The partial derivative of `Φ` in `c` is the derivative of `c' ↦ Φ(c', u_c)`.
  have hc : HasFDerivAt (fun c' ↦ reducedEquationMapOfCoeff hm c' (sobolevReducedSolution c))
      (fderiv ℝ (fun p : (Fin m → ℂ) × H^{2}(ℂ) ↦ reducedEquationMapOfCoeff hm p.1 p.2)
        (c, sobolevReducedSolution c) ∘L .inl ℝ (Fin m → ℂ) H^{2}(ℂ)) c := by
    -- `Φ ∘ (·, u_c)` is `c' ↦ Φ(c', u_c)` up to beta reduction.
    have h := hΦ.comp c (hasFDerivAt_prodMk_left (𝕜 := ℝ) c (sobolevReducedSolution c))
    exact h
  have hinl := hc.fderiv.symm
  have h := ((contDiff_reducedEquationMapOfCoeff hm).contDiffAt.hasStrictFDerivAt_implicitFunction
    (by simp) (isInvertible_fderiv_comp_inr_reducedEquationMapOfCoeff hm c)).hasFDerivAt
  rw [fderiv_comp_inr_reducedEquationMapOfCoeff, hinl] at h
  exact h.congr_of_eventuallyEq (implicitFunction_eventuallyEq_sobolevReducedSolution hm c).symm

end TauCeti.Vortex
