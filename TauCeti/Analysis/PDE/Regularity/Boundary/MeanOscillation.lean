/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Boundary.VariableCoefficientDecay
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.MeanInequalities
import TauCeti.MeasureTheory.Measure.Haar.HalfSpace
import TauCeti.MeasureTheory.Measure.InterBall

/-!
# Mean oscillation of the gradient at a flat boundary

Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `z` lie on its boundary hyperplane, and write
`B_t⁺ = B(z, t) ∩ H`. Let `u ∈ H¹(U)`, `B(z, r) ⊆ U`, vanish on `U ∖ H` and solve

`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly on `U ∩ H`,

so that `u` has zero boundary values on the flat part of the boundary, with a bounded measurable
coefficient matrix `a` that need be neither continuous nor symmetric. Fix any constant matrix `A`,
uniformly elliptic with constants `0 < λ ≤ Λ`, and write `θ(x) = ‖a(x) - A‖` for the deviation of
the coefficients from `A`, in the operator norm of the attached bilinear forms
`TauCeti.PDE.matrixBilinearForm`. This file proves the boundary counterparts of Krylov's mean
oscillation estimates for the gradient on balls, in the `TauCeti.PDE` namespace
(`setIntegral_ball_norm_gradient_sub_setAverage_sq_le_add_of_norm_matrixBilinearForm_sub_le`
in the interior): there is `C`, depending only on `n`, `λ` and `Λ`, such that for `0 < ρ ≤ r`,
every constant vector `c` and every real `t`, with
`E = ∫_{B_r⁺} θ² ‖∇u‖² + ∫_{B_r⁺} ‖G - c‖²`,

* `∫_{B_ρ⁺} ‖∇u‖² ≤ C (ρ / r)^(n + 1) ∫_{B_r⁺} ‖∇u‖² + C E`
  (`exists_setIntegral_ball_inter_norm_gradient_sq_le_add`);
* `∫_{B_ρ⁺} ‖∇u - p_ρ‖² ≤ C (ρ / r)^(n + 3) ∫_{B_r⁺} ‖∇u - t ν‖² + C E`, where `p_ρ` is the
  multiple of `ν` closest to `∇u` in `L²(B_ρ⁺)`
  (`exists_setIntegral_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le_add`).

The square mean oscillation `∫_{B_ρ⁺} ‖∇u - (∇u)_{B_ρ⁺}‖²` is at most the left side of the second
estimate, and its right side with `t = 0` is the `L²` mass of `∇u`. Only multiples of the normal
are compared with `∇u` on the right: they are the gradients of the linear functions
`t (⟪x, ν⟫ - c₀)`, which vanish on the hyperplane. Any constant `c` may be subtracted from `G`,
since a constant field integrates to zero against the gradients of test functions.

The coefficients enter only through `∫_{B_r⁺} θ² ‖∇u‖²`. If `θ ≤ K` on `B_r⁺` and
`∇u ∈ L^{2q}(B_r⁺)` for a pair of Hölder conjugate exponents `q, q'`, Hölder's inequality turns
this term into the mean deviation `⨍_{B_r⁺} θ`, and dividing by the volumes of the half-balls,
which are half those of the balls, gives the scale-invariant form

`⨍_{B_ρ⁺} ‖∇u - p_ρ‖² ≤ C (ρ / r)² ⨍_{B_r⁺} ‖∇u - t ν‖² + C (r / ρ)^(n + 1) (⨍_{B_r⁺} ‖G - c‖² + F)`

with `F = (K^(2q' - 1) ⨍_{B_r⁺} θ)^(1/q') (⨍_{B_r⁺} ‖∇u‖^(2q))^(1/q)`
(`exists_setAverage_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le`). For `A` the
average of `a` over `B_r⁺`, `⨍_{B_r⁺} θ` is a mean oscillation of `a`. So at boundary points, as
in the interior, the gradient of a solution whose coefficients have small mean oscillation
oscillates like that of a solution of a constant-coefficient equation, up to the data and a small
multiple of a higher average of `‖∇u‖`. The frozen matrix `A` is arbitrary: unlike the reflection
argument behind `TauCeti.PDE.exists_eLpNorm_gradient_le_of_setAverage_reflectPrincipal_le`, nothing
requires the coefficients near the boundary to be close to a matrix invariant under the reflection
in the hyperplane, which coefficients of vanishing mean oscillation need not be.

## The argument

On `B_r⁺` let `w` solve the frozen problem `-∂ᵢ(Aⁱʲ ∂ⱼw) = 0` with the boundary values of `u`
(`UniformlyEllipticOn.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball`,
in the `TauCeti.PDE` namespace), and extend `w` to `B(z, r)`, vanishing off `H`, by subtracting the
zero extension of `u - w` from `u` (`TauCeti.PDE.exists_restrictL_eq_of_sub_mem_w1p0Submodule`).
The decay estimates for constant coefficients at a flat boundary
(`TauCeti.PDE.exists_setIntegral_ball_inter_norm_gradient_sq_le` and
`TauCeti.PDE.exists_setIntegral_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le`)
apply to the extension, and transfer to `u` up to the energy distance
`∫_{B_r⁺} ‖∇u - ∇w‖²` (`TauCeti.PDE.setIntegral_ball_inter_norm_gradient_sub_sq_le_add_of_le`).
Since `u` solves the frozen equation on `B_r⁺` with the field `G - c + (A - a) ∇u`, that distance
is at most `(2 / λ²) E` (`TauCeti.PDE.UniformlyEllipticOn.setIntegral_norm_gradient_sub_sq_le`).

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475 (mean oscillation estimates for equations with
  coefficients of vanishing mean oscillation).
* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Sobolev Spaces*, Graduate Studies
  in Mathematics **96**, AMS, 2008 (estimates near a flat boundary).
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Sections 5.3 and 5.4 (comparison with the frozen
  problem, at interior and boundary points).
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped Distributions Gradient InnerProductSpace

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-- **The frozen replacement on a half-ball, with a variable coefficient deviation.** Let
`u ∈ H¹(U)` vanish on `U ∖ H` and solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly on `U ∩ H`, and let
`ball z r ⊆ U`. Let `A` be a constant matrix, uniformly elliptic with lower constant `λ` on
`B_r⁺ = B(z, r) ∩ H`, such that `θ(x) = ‖a(x) - A‖`, in the operator norm of the attached bilinear
forms, is bounded on `B_r⁺`, and let `c` be a constant vector with `G - c ∈ L²(B_r⁺)`. Then there
is `W ∈ H¹(B(z, r))` vanishing on `B(z, r) ∖ H` and solving the frozen problem
`-∂ᵢ(Aⁱʲ ∂ⱼW) = 0` weakly on `B_r⁺`, with

`∫_{B_r⁺} ‖∇u - ∇W‖² ≤ (2 / λ²) (∫_{B_r⁺} θ² ‖∇u‖² + ∫_{B_r⁺} ‖G - c‖²)`. -/
theorem exists_frozen_ball_inter_of_norm_matrixBilinearForm_sub_le
    {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume U 2}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {z c : EuclideanSpace ℝ (Fin (n + 1))} {r lam Lam K : ℝ}
    (hA : UniformlyEllipticOn (ball z r ∩ H) (fun _ => A) lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict (ball z r ∩ H)))
    (haK : ∀ x ∈ ball z r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ K)
    (hu0 : ∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0)
    (hu : ∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
        (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
      ∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    (hGc : MemLp (fun x => G x - c) 2 (volume.restrict (ball z r ∩ H))) (hball : ball z r ⊆ U) :
    ∃ W : W1p volume (⟨ball z r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
      (∀ᵐ x ∂volume.restrict (ball z r), x ∉ H → W1p.value W x = 0) ∧
      (∀ v : W1p0 volume
          ((⟨ball z r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) ⊓ H) 2,
        energyFormH1 (fun _ => A) 0 0 (W1p.restrictL inf_le_left W)
          (v : W1p volume
            ((⟨ball z r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) ⊓ H) 2) = 0) ∧
      ∫ x in ball z r ∩ H, ‖W1p.gradient u x - W1p.gradient W x‖ ^ 2 ≤
        2 / lam ^ 2 * ((∫ x in ball z r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ^ 2 *
          ‖W1p.gradient u x‖ ^ 2) + ∫ x in ball z r ∩ H, ‖G x - c‖ ^ 2) := by
  set B : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball z r, isOpen_ball⟩ ⊓ H
  have hBset : (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ball z r ∩ H := by
    simp only [B, Opens.coe_inf, Opens.coe_mk]
  have hBΩ : B ≤ U ⊓ H := inf_le_inf_right H hball
  have hBU : B ≤ U := hBΩ.trans inf_le_left
  have hA' : UniformlyEllipticOn (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) (fun _ => A) lam Lam :=
    hBset ▸ hA
  -- The replacement `w` of `u` on `B_r⁺` for the frozen operator.
  obtain ⟨w, ⟨hwu, hw⟩, -⟩ :=
    UniformlyEllipticOn.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball
      (Omega := B) (b := 0) (c := 0) hA' aestronglyMeasurable_const aestronglyMeasurable_const
      aestronglyMeasurable_const (beta := 0) (fun _ _ => by simp) (gamma := 0)
      (fun _ _ => by simp) (fun _ _ => le_rfl) (hBset.trans_subset inter_subset_left)
      (by simpa using hA.pos) 0 (W1p.restrictL hBU u)
  have hw0 : ∀ v : W1p0 volume B 2,
      energyFormH1 (fun _ => A) 0 0 w (v : W1p volume B 2) = 0 := fun v => by
    rw [hw v, zero_apply]
  have huw : W1p.restrictL hBU u - w ∈ w1p0Submodule volume B 2 := by
    have h := (ClosedSubmodule.mem_toSubmodule_iff (w - W1p.restrictL hBU u)
      (w1p0Submodule volume B 2)).2 hwu
    exact (ClosedSubmodule.mem_toSubmodule_iff _ _).1 (sub_mem_comm_iff.1 h)
  obtain ⟨W, hW0, hWB⟩ := exists_restrictL_eq_of_sub_mem_w1p0Submodule hu0 hball hBU huw
  refine ⟨W, hW0, fun v => ?_, ?_⟩
  · rw [hWB]
    exact hw0 v
  -- The energy distance from the frozen replacement, on `B_r⁺`.
  have huw' : W1p.restrictL hBΩ (W1p.restrictL inf_le_left u) - w ∈ w1p0Submodule volume B 2 := by
    rwa [W1p.restrictL_restrictL]
  have hcomp := UniformlyEllipticOn.setIntegral_norm_gradient_sub_sq_le hA' hBΩ
    (hBset ▸ ha) (fun x hx => haK x (hBset ▸ hx)) hu (hBset ▸ hGc) huw' hw0
  simp only [hBset] at hcomp
  have hBΩs : ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆
      ((U ⊓ H : Opens (EuclideanSpace ℝ (Fin (n + 1)))) : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
    hBset ▸ hBΩ
  have hBb : B ≤ ⟨ball z r, isOpen_ball⟩ := inf_le_left
  -- On `B_r⁺` the gradients of the restrictions are those of `u` and `W`.
  have hgu : ∀ᵐ x ∂volume.restrict (ball z r ∩ H),
      W1p.gradient (W1p.restrictL inf_le_left u) x = W1p.gradient u x :=
    ae_restrict_of_ae_restrict_of_subset hBΩs (W1p.gradient_restrictL_ae inf_le_left u)
  have hgW : ∀ᵐ x ∂volume.restrict (ball z r ∩ H), W1p.gradient w x = W1p.gradient W x := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hBset.symm.subset
      (W1p.gradient_restrictL_ae hBb W)] with x hx
    rw [← hx, hWB]
  calc _ = ∫ x in ball z r ∩ H,
        ‖W1p.gradient (W1p.restrictL inf_le_left u) x - W1p.gradient w x‖ ^ 2 :=
        integral_congr_ae (by filter_upwards [hgu, hgW] with x h1 h2; rw [h1, h2])
    _ ≤ _ := hcomp
    _ = _ := by
        congr 2
        exact integral_congr_ae (by filter_upwards [hgu] with x hx; rw [hx])

/-- **Transferring decay from the frozen replacement on half-balls.** Let `u ∈ H¹(U)`,
`ball z r ⊆ U`, `W ∈ H¹(B(z, r))` and `0 < ρ ≤ r`, and write `B_t⁺ = B(z, t) ∩ H`. Suppose that `b`
is at least as close to `∇u` in `L²(B_ρ⁺)` as `k`, that `W` decays like
`∫_{B_ρ⁺} ‖∇W - k‖² ≤ D q ∫_{B_r⁺} ‖∇W - c‖²` with `0 ≤ q ≤ 1`, and that the energy distance
`∫_{B_r⁺} ‖∇u - ∇W‖²` is at most `(2 / λ²) e`. Then, with `C = (4 D + 2) (1 + 2 / λ²)`,
`∫_{B_ρ⁺} ‖∇u - b‖² ≤ C q ∫_{B_r⁺} ‖∇u - c‖² + C e`. -/
private theorem setIntegral_ball_inter_le_mul_add_mul_of_frozen
    {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume U 2}
    {z b k c : EuclideanSpace ℝ (Fin (n + 1))} {r ρ D q lam e : ℝ}
    {W : W1p volume (⟨ball z r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    (hball : ball z r ⊆ U) (hρr : ρ ≤ r) (hD : 0 ≤ D) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (he : 0 ≤ e)
    (hbest : ∫ x in ball z ρ ∩ H, ‖W1p.gradient u x - b‖ ^ 2 ≤
      ∫ x in ball z ρ ∩ H, ‖W1p.gradient u x - k‖ ^ 2)
    (hdecay : ∫ x in ball z ρ ∩ H, ‖W1p.gradient W x - k‖ ^ 2 ≤
      D * q * ∫ x in ball z r ∩ H, ‖W1p.gradient W x - c‖ ^ 2)
    (hE : ∫ x in ball z r ∩ H, ‖W1p.gradient u x - W1p.gradient W x‖ ^ 2 ≤ 2 / lam ^ 2 * e) :
    ∫ x in ball z ρ ∩ H, ‖W1p.gradient u x - b‖ ^ 2 ≤
      (4 * D + 2) * (1 + 2 / lam ^ 2) * q * (∫ x in ball z r ∩ H, ‖W1p.gradient u x - c‖ ^ 2) +
        (4 * D + 2) * (1 + 2 / lam ^ 2) * e := by
  have hX := setIntegral_ball_inter_norm_gradient_sub_sq_le_add_of_le hball hρr hD hq0 hq1 hbest
    hdecay
  set S := ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1))))
  -- Collect the constants `4 D ≤ C` and `(4 D + 2) (2 / λ²) ≤ C`.
  have hY : 0 ≤ ∫ x in S, ‖W1p.gradient u x - c‖ ^ 2 :=
    setIntegral_nonneg (measurableSet_ball.inter H.isOpen.measurableSet) fun _ _ => by positivity
  have hl : 0 ≤ 2 / lam ^ 2 := by positivity
  have h0 : 4 * D ≤ (4 * D + 2) * (1 + 2 / lam ^ 2) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * D + 2) hl]
  have h1 := mul_le_mul_of_nonneg_right h0 (mul_nonneg hq0 hY)
  have h2 : (4 * D + 2) * (2 / lam ^ 2 * e) ≤ (4 * D + 2) * (1 + 2 / lam ^ 2) * e := by
    rw [← mul_assoc]
    gcongr
    linarith
  have h3 := mul_le_mul_of_nonneg_left hE (by linarith : (0 : ℝ) ≤ 4 * D + 2)
  simp only [mul_assoc] at hX h1 h2 h3 ⊢
  linarith

/-- **Decay of the `L²` mass of the gradient at a flat boundary, with a coefficient deviation.**
Let `0 < λ`. There is `C > 0`, depending only on `n`, `λ` and `Λ`, with the following property. Let
`H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `z` lie on the boundary hyperplane, and write
`B_t⁺ = B(z, t) ∩ H`. Let `A` be a constant matrix, uniformly elliptic with constants `λ`, `Λ`, and
let `a` be measurable on `B_r⁺` with `θ(x) = ‖a(x) - A‖ ≤ K` there, in the operator norm of the
attached bilinear forms. Let `u ∈ H¹(U)`, `ball z r ⊆ U`, vanish on `U ∖ H` and solve
`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly on `U ∩ H`. Then for `0 < ρ ≤ r` and every constant vector `c` with
`G - c ∈ L²(B_r⁺)`,

`∫_{B_ρ⁺} ‖∇u‖² ≤ C (ρ / r)^(n + 1) ∫_{B_r⁺} ‖∇u‖² + C (∫_{B_r⁺} θ² ‖∇u‖² + ∫_{B_r⁺} ‖G - c‖²)`.

For `a = A` this is the decay estimate for constant coefficients
`TauCeti.PDE.exists_setIntegral_ball_inter_norm_gradient_sq_le` with a divergence datum `G`. -/
theorem exists_setIntegral_ball_inter_norm_gradient_sq_le_add {lam Lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume U 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {ν z c : EuclideanSpace ℝ (Fin (n + 1))} {c₀ r ρ K : ℝ},
      UniformlyEllipticOn (ball z r) (fun _ => A) lam Lam →
      AEStronglyMeasurable a (volume.restrict (ball z r ∩ H)) →
      (∀ x ∈ ball z r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ K) → ν ≠ 0 →
      (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪z, ν⟫_ℝ = c₀ → ball z r ⊆ U →
      (∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
          (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
        ∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      MemLp (fun x => G x - c) 2 (volume.restrict (ball z r ∩ H)) → 0 < ρ → ρ ≤ r →
      ∫ x in ball z ρ ∩ H, ‖W1p.gradient u x‖ ^ 2 ≤
        C * (ρ / r) ^ (n + 1) * (∫ x in ball z r ∩ H, ‖W1p.gradient u x‖ ^ 2) +
          C * ((∫ x in ball z r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ^ 2 *
            ‖W1p.gradient u x‖ ^ 2) + ∫ x in ball z r ∩ H, ‖G x - c‖ ^ 2) := by
  obtain ⟨D, hD, hdec⟩ :=
    exists_setIntegral_ball_inter_norm_gradient_sq_le (ι := Fin (n + 1)) (Lam := Lam) hlam
  refine ⟨(4 * D + 2) * (1 + 2 / lam ^ 2), by positivity, ?_⟩
  intro U H u a A G ν z c c₀ r ρ K hA ha haK hν hH hzc hball hu0 hu hGc hρ hρr
  have hr : 0 < r := hρ.trans_le hρr
  have hz : z ∈ ball z r := mem_ball_self hr
  obtain ⟨W, hW0, hW, hE⟩ := exists_frozen_ball_inter_of_norm_matrixBilinearForm_sub_le
    (hA.mono_set inter_subset_left) ha haK hu0 hu hGc hball
  have hd := hdec (U := ⟨ball z r, isOpen_ball⟩) (hA.lower_bound hz) (hA.upper_bound hz) hν hH
    hzc subset_rfl hW0 hW hρ.le hρr
  rw [Fintype.card_fin] at hd
  have hq0 : 0 ≤ ρ / r := by positivity
  simpa only [sub_zero] using setIntegral_ball_inter_le_mul_add_mul_of_frozen (b := 0) (k := 0)
    (c := 0) (q := (ρ / r) ^ (n + 1)) hball hρr hD.le (pow_nonneg hq0 _)
    (pow_le_one₀ hq0 ((div_le_one hr).2 hρr))
    (add_nonneg (setIntegral_nonneg (measurableSet_ball.inter H.isOpen.measurableSet)
      fun _ _ => by positivity)
      (setIntegral_nonneg (measurableSet_ball.inter H.isOpen.measurableSet)
        fun _ _ => by positivity))
    le_rfl (by simpa only [sub_zero] using hd) hE

/-- **Decay of the gradient's distance to the normal constants at a flat boundary, with a
coefficient deviation.** Let `0 < λ`. There is `C > 0`, depending only on `n`, `λ` and `Λ`, with
the following property. Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `z` lie on the boundary
hyperplane, and write `B_t⁺ = B(z, t) ∩ H`. Let `A` be a constant matrix, uniformly elliptic with
constants `λ`, `Λ`, and let `a` be measurable on `B_r⁺` with `θ(x) = ‖a(x) - A‖ ≤ K` there, in the
operator norm of the attached bilinear forms. Let `u ∈ H¹(U)`, `ball z r ⊆ U`, vanish on `U ∖ H`
and solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly on `U ∩ H`. Then for `0 < ρ ≤ r`, every real `t` and
every constant vector `c` with `G - c ∈ L²(B_r⁺)`,

`∫_{B_ρ⁺} ‖∇u - p_ρ‖² ≤ C (ρ / r)^(n + 3) ∫_{B_r⁺} ‖∇u - t ν‖²`
`  + C (∫_{B_r⁺} θ² ‖∇u‖² + ∫_{B_r⁺} ‖G - c‖²)`,

where `p_ρ = (⟪(∇u)_{B_ρ⁺}, ν⟫ / ‖ν‖²) ν` is the multiple of `ν` closest to `∇u` in `L²(B_ρ⁺)`.
The left side bounds the square mean oscillation of `∇u` on `B_ρ⁺`, and for `t = 0` the first
term on the right is the `L²` mass of `∇u` on `B_r⁺`. For `a = A` this is the decay estimate for
constant coefficients
`TauCeti.PDE.exists_setIntegral_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le`
with a divergence datum `G`. -/
theorem exists_setIntegral_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le_add
    {lam Lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume U 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {ν z c : EuclideanSpace ℝ (Fin (n + 1))} {c₀ r ρ K : ℝ},
      UniformlyEllipticOn (ball z r) (fun _ => A) lam Lam →
      AEStronglyMeasurable a (volume.restrict (ball z r ∩ H)) →
      (∀ x ∈ ball z r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ K) → ν ≠ 0 →
      (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪z, ν⟫_ℝ = c₀ → ball z r ⊆ U →
      (∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
          (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
        ∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      MemLp (fun x => G x - c) 2 (volume.restrict (ball z r ∩ H)) → 0 < ρ → ρ ≤ r → ∀ t : ℝ,
      ∫ x in ball z ρ ∩ H, ‖W1p.gradient u x -
          (⟪⨍ y in ball z ρ ∩ H, W1p.gradient u y, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ^ 2 ≤
        C * (ρ / r) ^ (n + 3) * (∫ x in ball z r ∩ H, ‖W1p.gradient u x - t • ν‖ ^ 2) +
          C * ((∫ x in ball z r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ^ 2 *
            ‖W1p.gradient u x‖ ^ 2) + ∫ x in ball z r ∩ H, ‖G x - c‖ ^ 2) := by
  obtain ⟨D, hD, hdec⟩ :=
    exists_setIntegral_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le
      (ι := Fin (n + 1)) (Lam := Lam) hlam
  refine ⟨(4 * D + 2) * (1 + 2 / lam ^ 2), by positivity, ?_⟩
  intro U H u a A G ν z c c₀ r ρ K hA ha haK hν hH hzc hball hu0 hu hGc hρ hρr t
  have hr : 0 < r := hρ.trans_le hρr
  have hz : z ∈ ball z r := mem_ball_self hr
  obtain ⟨W, hW0, hW, hE⟩ := exists_frozen_ball_inter_of_norm_matrixBilinearForm_sub_le
    (hA.mono_set inter_subset_left) ha haK hu0 hu hGc hball
  have hd := hdec (U := ⟨ball z r, isOpen_ball⟩) (hA.lower_bound hz) (hA.upper_bound hz) hν hH
    hzc subset_rfl hW0 hW hρ.le hρr t
  rw [Fintype.card_fin] at hd
  have hq0 : 0 ≤ ρ / r := by positivity
  -- Among the multiples of `ν`, the projection of the average of `∇u` is the best constant.
  exact setIntegral_ball_inter_le_mul_add_mul_of_frozen (q := (ρ / r) ^ (n + 3)) hball hρr
    hD.le (pow_nonneg hq0 _) (pow_le_one₀ hq0 ((div_le_one hr).2 hρr))
    (add_nonneg (setIntegral_nonneg (measurableSet_ball.inter H.isOpen.measurableSet)
      fun _ _ => by positivity)
      (setIntegral_nonneg (measurableSet_ball.inter H.isOpen.measurableSet)
        fun _ _ => by positivity))
    (setIntegral_norm_sub_inner_setAverage_div_smul_sq_le_of_subset subset_rfl
      measure_ball_inter_ne_top ((Lp.memLp (W1p.gradient u)).mono_measure
        (Measure.restrict_mono (inter_subset_left.trans ((ball_subset_ball hρr).trans hball))
          le_rfl)) ν _) hd hE

/-- **Krylov's mean oscillation estimate for the gradient at a flat boundary, averaged form.** Let
`0 < λ`. There is `C > 0`, depending only on `n`, `λ` and `Λ`, with the following property. Let
`H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `z` lie on the boundary hyperplane, and write
`B_t⁺ = B(z, t) ∩ H`. Let `A` be a constant matrix, uniformly elliptic with constants `λ`, `Λ`, and
let `a` be measurable on `B_r⁺` with `θ(x) = ‖a(x) - A‖ ≤ K` there, in the operator norm of the
attached bilinear forms. Let `u ∈ H¹(U)`, `ball z r ⊆ U`, vanish on `U ∖ H` and solve
`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly on `U ∩ H`, and let `∇u ∈ L^{2q}(B_r⁺)` for a pair of Hölder
conjugate exponents `q, q'`. Then for `0 < ρ ≤ r`, every real `t` and every constant vector `c`
with `G - c ∈ L²(B_r⁺)`,

`⨍_{B_ρ⁺} ‖∇u - p_ρ‖² ≤ C (ρ / r)² ⨍_{B_r⁺} ‖∇u - t ν‖² + C (r / ρ)^(n + 1) (⨍_{B_r⁺} ‖G - c‖² + E)`

with `E = (K^(2q' - 1) ⨍_{B_r⁺} θ)^(1/q') (⨍_{B_r⁺} ‖∇u‖^(2q))^(1/q)`, where `p_ρ` is the multiple
of `ν` closest to `∇u` in `L²(B_ρ⁺)`. Every average is invariant under dilations about `z`, and the
coefficients enter only through the mean deviation `⨍_{B_r⁺} θ`. This is the boundary counterpart
of the interior estimate
`setAverage_ball_norm_gradient_sub_setAverage_sq_le_of_norm_matrixBilinearForm_sub_le`. -/
theorem exists_setAverage_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le
    {lam Lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume U 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {ν z c : EuclideanSpace ℝ (Fin (n + 1))} {c₀ r ρ K q q' : ℝ},
      UniformlyEllipticOn (ball z r) (fun _ => A) lam Lam →
      AEStronglyMeasurable a (volume.restrict (ball z r ∩ H)) →
      (∀ x ∈ ball z r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ K) → ν ≠ 0 →
      (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪z, ν⟫_ℝ = c₀ → ball z r ⊆ U →
      (∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
          (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
        ∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      MemLp (fun x => G x - c) 2 (volume.restrict (ball z r ∩ H)) → q.HolderConjugate q' →
      MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
        (ENNReal.ofReal (2 * q)) (volume.restrict (ball z r ∩ H)) →
      0 < ρ → ρ ≤ r → ∀ t : ℝ,
      ⨍ x in ball z ρ ∩ H, ‖W1p.gradient u x -
          (⟪⨍ y in ball z ρ ∩ H, W1p.gradient u y, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ^ 2 ≤
        C * (ρ / r) ^ 2 * (⨍ x in ball z r ∩ H, ‖W1p.gradient u x - t • ν‖ ^ 2) +
          C * (r / ρ) ^ (n + 1) * ((⨍ x in ball z r ∩ H, ‖G x - c‖ ^ 2) +
            (K ^ (2 * q' - 1) *
                ⨍ x in ball z r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖) ^ q'⁻¹ *
              (⨍ x in ball z r ∩ H, ‖W1p.gradient u x‖ ^ (2 * q)) ^ q⁻¹) := by
  obtain ⟨C, hC, hest⟩ :=
    exists_setIntegral_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le_add
      (n := n) (Lam := Lam) hlam
  refine ⟨C, hC, ?_⟩
  intro U H u a A G ν z c c₀ r ρ K q q' hA ha haK hν hH hzc hball hu0 hu hGc hq hgq hρ hρr t
  have hr : 0 < r := hρ.trans_le hρr
  -- The half-balls have positive measure and scale like the balls.
  have hHs (t : ℝ) : {y | c₀ < ⟪y, ν⟫_ℝ} ∩ ball z t = ball z t ∩ H := by ext; simp [hH, and_comm]
  have hV := volume.addHaar_real_setOf_lt_inner_inter_ball_pos hν hzc hr
  have hVρ := volume.addHaar_real_setOf_lt_inner_inter_ball_eq_div_pow_mul hν hzc hρ.le hr
  simp only [hHs, finrank_euclideanSpace_fin] at hV hVρ
  set S := ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1))))
  set θ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
    fun x => ‖matrixBilinearForm (a x) - matrixBilinearForm A‖
  have hθm : AEStronglyMeasurable θ (volume.restrict S) :=
    aestronglyMeasurable_norm_matrixBilinearForm_sub ha A
  have hθ : ∀ᵐ x ∂volume.restrict S, 0 ≤ θ x ∧ θ x ≤ K :=
    (ae_restrict_mem (measurableSet_ball.inter H.isOpen.measurableSet)).mono fun x hx =>
      ⟨norm_nonneg (matrixBilinearForm (a x) - matrixBilinearForm A), haK x hx⟩
  have key := hest hA ha haK hν hH hzc hball hu0 hu hGc hρ hρr t
  rw [← one_mul (∫ x in S, θ x ^ 2 * ‖W1p.gradient u x‖ ^ 2)] at key
  -- Pass to averages, using `|B_ρ⁺| = (ρ / r)^(n + 1) |B_r⁺|` and Hölder's inequality.
  refine (setAverage_le_of_setIntegral_le_add_sq_mul_norm_sq hV (div_pos hρ hr) hVρ hC.le
    zero_le_one hq hθm hθ hgq key).trans_eq ?_
  rw [inv_div]
  ring

end PDE

end TauCeti
