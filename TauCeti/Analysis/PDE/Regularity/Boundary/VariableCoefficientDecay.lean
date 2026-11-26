/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.FrozenCoefficient
public import TauCeti.Analysis.PDE.Regularity.Boundary.ConstantCoefficientDecay
import TauCeti.Analysis.Sobolev.W1p.Extension
import TauCeti.Analysis.SpecificLimits.CampanatoIteration
import TauCeti.MeasureTheory.Function.Campanato
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Measure.Haar.HalfSpace
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.InterBall

/-!
# Decay estimates at a flat boundary for Hölder coefficients

Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `z` lie on its boundary hyperplane, and write
`B_t⁺ = B(z, t) ∩ H`. Let `u ∈ H¹(U)`, `B(z, R) ⊆ U`, vanish on `U ∖ H` and solve

`-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on `U ∩ H`,

with coefficients `a` and a field `G` that are `α`-Hölder on `B(z, R)`, `a(z)` uniformly elliptic,
and a scalar datum `f`: so `u` has zero boundary values on the flat part of the boundary. This file
proves the decay estimates of Campanato's method at such boundary centres. If the data decay like
`r^{2α} K_G² r^{n+1} + 4 r² ∫_{B_r⁺} f² ≤ V (r / R)^{n+1+2γ}` and `∫_{B_R⁺} ‖∇u‖² ≤ V`, then for
`ρ ≤ θ R`:

* `∫_{B_ρ⁺} ‖∇u‖² ≤ C V (ρ / R)^{n+1}`
  (`TauCeti.PDE.exists_setIntegral_ball_inter_norm_gradient_sq_le_of_holderOnWith`), for all
  `α > 0` and `γ > 0`;
* `∫_{B_ρ⁺} ‖∇u - p_ρ‖² ≤ C V (ρ / R)^{n+1+2γ}`, where `p_ρ` is the multiple of `ν` closest to
  `∇u` in `L²(B_ρ⁺)`, for every `0 < γ < 1` with `γ ≤ α`, in the `TauCeti.PDE` namespace:
  `exists_setIntegral_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le_of_holderOnWith`.

Here `θ ∈ (0, 1]` and `C` depend only on `n`, `α`, `γ`, the ellipticity constants `λ`, `Λ` and a
bound `M ≥ R^α [a]_α`. These are the variable-coefficient versions of the estimates for constant
coefficients in `TauCeti.Analysis.PDE.Regularity.Boundary.ConstantCoefficientDecay`, and the
boundary counterparts of the interior decay behind the Schauder estimate of
`TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder`. Combined with the interior estimate,
they are the input of the `C^{1,γ}` estimate up to a flat boundary.

## The argument

The proof is Campanato's, by comparison with the problem frozen at the boundary centre.

* **Comparison.** On `B_r⁺`, let `w` solve `-∂ᵢ(a(z)ⁱʲ ∂ⱼw) = 0` with the boundary values of `u`,
  so that `u - w ∈ H¹₀(B_r⁺)`
  (`TauCeti.PDE.UniformlyEllipticOn.exists_sub_mem_w1p0Submodule_mul_norm_gradient_sub_le`).
  Subtracting the zero extension of `u - w` from `u` extends `w` to `B(z, r)`, vanishing off `H`.
  So the decay estimates for constant coefficients at a flat boundary
  (`TauCeti.PDE.exists_setIntegral_ball_inter_norm_gradient_sq_le` and
  `TauCeti.PDE.exists_setIntegral_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le`)
  apply to it, and transfer to `u` up to `∫_{B_r⁺} ‖∇u - ∇w‖²`
  (`TauCeti.PDE.setIntegral_ball_inter_norm_gradient_sub_sq_le_add_of_le`, by
  `TauCeti.MeasureTheory.setIntegral_norm_sub_sq_le_add_of_le`), which is of order
  `r^{2α} K_a² ∫_{B_r⁺} ‖∇u‖²` plus the data term.
* **Iteration.** As in the interior, four steps of Campanato's perturbation argument
  (`TauCeti.exists_le_mul_mul_div_rpow_of_le_mul_div_rpow_mul_add` and
  `TauCeti.exists_le_mul_mul_div_rpow_of_le_mul_div_rpow_mul_add_of_le_mul_mul_div_rpow`) raise
  the decay: Morrey decay with exponent `n + 1 - γ`, Campanato decay with exponent `n + 1 + γ`,
  Morrey decay with the full exponent `n + 1`, and Campanato decay with exponent `n + 1 + 2γ`.
  The third step bounds the averages of `∇u` over the half-balls, by Campanato's estimate on the
  half-space, which has density one half in the balls centred on its boundary
  (`TauCeti.MeasureTheory.exists_setIntegral_ball_inter_norm_sq_le_mul_div_pow`).

## References

* S. Campanato, *Equazioni ellittiche del II ordine e spazi `𝓛^{(2,λ)}`*, Ann. Mat. Pura Appl.
  69 (1965), 321–381.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Sections 5.1 and 5.4 (Schauder estimates up to the
  boundary by Campanato's method).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.33 (the `C^{1,α}` estimate up to the boundary).
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped Distributions ENNReal Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

variable {n : ℕ}

section Comparison

/-- **Extending a function on a half-ball by `u`.** Let `u ∈ H¹(U)` vanish on `U ∖ H`, let
`ball z r ⊆ U`, and let `w ∈ H¹(B_r ∩ H)` have the boundary values of `u`, that is
`u - w ∈ H¹₀(B_r ∩ H)`. Then `u` minus the zero extension of `u - w` is a function
`W ∈ H¹(B_r)` that vanishes on `B_r ∖ H` and restricts to `w` on `B_r ∩ H`. -/
theorem exists_restrictL_eq_of_sub_mem_w1p0Submodule
    {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume U 2}
    {z : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ}
    (hu0 : ∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0) (hball : ball z r ⊆ U)
    {w : W1p volume ((⟨ball z r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) ⊓ H) 2}
    (hBU : (⟨ball z r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) ⊓ H ≤ U)
    (hsub : W1p.restrictL hBU u - w ∈ w1p0Submodule volume _ 2) :
    ∃ W : W1p volume (⟨ball z r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
      (∀ᵐ x ∂volume.restrict (ball z r), x ∉ H → W1p.value W x = 0) ∧
      W1p.restrictL inf_le_left W = w := by
  have hUb : (⟨ball z r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) ≤ U := hball
  have hBUb : (⟨ball z r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) ⊓ H ≤
      ⟨ball z r, isOpen_ball⟩ := inf_le_left
  -- The difference `e = u|_{B_r ∩ H} - w` has zero boundary values.
  let e : W1p0 volume ((⟨ball z r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) ⊓ H) 2 :=
    ⟨W1p.restrictL hBU u - w, (ClosedSubmodule.mem_toSubmodule_iff _ _).2 hsub⟩
  refine ⟨W1p.restrictL hUb u - (W1p0.extendByZeroL hBUb e : W1p volume _ 2), ?_, ?_⟩
  · -- `u` vanishes off `H`, and the zero extension of `e` vanishes off `B_r ∩ H`.
    filter_upwards [W1p.value_sub_ae (W1p.restrictL hUb u)
        (W1p0.extendByZeroL hBUb e : W1p volume _ 2), W1p.value_restrictL_ae hUb u,
      W1p0.value_extendByZeroL_ae hBUb e, ae_restrict_of_ae_restrict_of_subset hball hu0]
      with x h1 h2 h3 h4 hxH
    have hxB : x ∉ (((⟨ball z r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) ⊓ H :
        Opens (EuclideanSpace ℝ (Fin (n + 1)))) : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
      fun hx => hxH hx.2
    rw [h1, Pi.sub_apply, h2, h3, indicator_of_notMem hxB, h4 hxH, sub_zero]
  · simp only [map_sub, W1p.restrictL_restrictL, W1p0.restrictL_extendByZeroL, e]
    exact sub_sub_cancel _ _

/-- **The frozen replacement on a half-ball.** Let `u ∈ H¹(U)` vanish on `U ∖ H` and solve
`-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on `U ∩ H`, let `ball z r ⊆ U`, let `a(z)` be uniformly elliptic
with lower constant `λ`, let `a` and `G` be `α`-Hölder on `ball z r` with constants `K_a` and
`K_G`, and let `f ∈ L²(B_r ∩ H)`. Then there is `W ∈ H¹(B_r)` vanishing on `B_r ∖ H` and solving
the problem `-∂ᵢ(a(z)ⁱʲ ∂ⱼW) = 0` frozen at `z` weakly on `B_r ∩ H`, with

`∫_{B_r ∩ H} ‖∇u - ∇W‖² ≤
  3 (1 + ω) (r^{2α} (K_a² ∫_{B_r ∩ H} ‖∇u‖² + K_G² r^{n+1}) + 4 r² ∫_{B_r ∩ H} f²) / λ²`,

where `ω` is the volume of the unit ball. On `B_r ∩ H`, `W` is the frozen replacement with the
boundary values of `u`; it is extended to `B_r` by subtracting from `u` the zero extension of the
difference, which lies in `H¹₀(B_r ∩ H)`. -/
private theorem exists_frozen_ball_inter {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {u : W1p volume U 2}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {s : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {z : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ} {α Ka KG : ℝ≥0} {lam Lam : ℝ}
    (h : UniformlyEllipticOn s a lam Lam) (hz : z ∈ s) (hα : 0 < α)
    (haK : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball z r))
    (hGK : HolderOnWith KG α G (ball z r))
    (hu0 : ∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0)
    (hu : ∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
        (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
      (∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in U ⊓ H, f x * φ x)
    (hf : MemLp f 2 (volume.restrict (ball z r ∩ H))) (hball : ball z r ⊆ U) (hr : 0 < r) :
    ∃ W : W1p volume (⟨ball z r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
      (∀ᵐ x ∂volume.restrict (ball z r), x ∉ H → W1p.value W x = 0) ∧
      (∀ v : W1p0 volume
          ((⟨ball z r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) ⊓ H) 2,
        energyFormH1 (fun _ => a z) 0 0 (W1p.restrictL inf_le_left W)
          (v : W1p volume
            ((⟨ball z r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) ⊓ H) 2) = 0) ∧
      ∫ x in ball z r ∩ H, ‖W1p.gradient u x - W1p.gradient W x‖ ^ 2 ≤
        3 * (1 + volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) *
          ((r ^ (2 * (α : ℝ)) * ((Ka : ℝ) ^ 2 *
            (∫ x in ball z r ∩ H, ‖W1p.gradient u x‖ ^ 2) + (KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) +
              4 * r ^ 2 * ∫ x in ball z r ∩ H, f x ^ 2) / lam ^ 2) := by
  set Ub : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball z r, isOpen_ball⟩
  set B : Opens (EuclideanSpace ℝ (Fin (n + 1))) := Ub ⊓ H
  have hBUb : B ≤ Ub := inf_le_left
  have hBΩ : B ≤ U ⊓ H := inf_le_inf_right H hball
  have hBset : (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ball z r ∩ H := by
    simp only [B, Ub, Opens.coe_inf, Opens.coe_mk]
  have hBr : (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z r := inter_subset_left
  have hBΩs : (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆
      ((U ⊓ H : Opens (EuclideanSpace ℝ (Fin (n + 1)))) : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
    hBΩ
  obtain ⟨w, hsub, hw0, hest⟩ :=
    h.exists_sub_mem_w1p0Submodule_mul_norm_gradient_sub_le hz hα haK hGK hBΩ hBr hu hf
  rw [W1p.restrictL_restrictL] at hsub
  obtain ⟨W, hW0, hWB⟩ := exists_restrictL_eq_of_sub_mem_w1p0Submodule hu0 hball _ hsub
  refine ⟨W, hW0, fun v => ?_, ?_⟩
  · rw [hWB]
    exact hw0 v
  · -- On `B`, `∇W = ∇w`, so the integral is the squared energy of `e`.
    have hE : ∫ x in ball z r ∩ H, ‖W1p.gradient u x - W1p.gradient W x‖ ^ 2 =
        ‖W1p.gradient (W1p.restrictL hBΩ (W1p.restrictL inf_le_left u) - w)‖ ^ 2 := by
      rw [← W1p.setIntegral_norm_gradient_sub_sq_eq hBΩ (W1p.restrictL inf_le_left u) w, ← hBset]
      refine integral_congr_ae ?_
      filter_upwards [W1p.gradient_restrictL_ae hBUb W,
        ae_restrict_of_ae_restrict_of_subset hBΩs
          (W1p.gradient_restrictL_ae inf_le_left u)] with x h1 h2
      rw [← h1, hWB, h2]
    rw [hE]
    have hX : ‖W1p.gradient (W1p.restrictL hBΩ (W1p.restrictL inf_le_left u))‖ ^ 2 =
        ∫ x in ball z r ∩ H, ‖W1p.gradient u x‖ ^ 2 := by
      rw [← Lp.integral_norm_sq_eq_norm_sq, ← hBset]
      refine integral_congr_ae ?_
      filter_upwards [W1p.gradient_restrictL_ae hBΩ (W1p.restrictL inf_le_left u),
        ae_restrict_of_ae_restrict_of_subset hBΩs
          (W1p.gradient_restrictL_ae inf_le_left u)] with x h1 h2
      rw [h1, h2]
    have hY : √(volume.real (B : Set (EuclideanSpace ℝ (Fin (n + 1))))) ^ 2 ≤
        volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * r ^ ((n : ℝ) + 1) := by
      rw [Real.sq_sqrt measureReal_nonneg]
      refine (measureReal_mono hBr measure_ball_lt_top.ne).trans_eq ?_
      rw [(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).addHaar_real_ball_of_pos z hr,
        finrank_euclideanSpace_fin, mul_comm, ← Real.rpow_natCast, Nat.cast_succ]
    have hF : ‖hf.toLp‖ ^ 2 = ∫ x in ball z r ∩ H, f x ^ 2 := by
      simp only [hf.norm_toLp_sq, Real.norm_eq_abs, sq_abs]
    have hr2 : (r ^ (α : ℝ)) ^ 2 = r ^ (2 * (α : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
      ring_nf
    rw [← hr2]
    exact sq_le_of_mul_le_mul_add_mul_add h.pos (norm_nonneg _) measureReal_nonneg
      (by positivity) hest hX hY hF

/-- **Transferring decay from a comparison function on half-balls.** Let `u ∈ H¹(U)`,
`ball z r ⊆ U`, `W ∈ H¹(B(z, r))` and `ρ ≤ r`, and write `B_t⁺ = B(z, t) ∩ H`. Suppose that `b`
is at least as close to `∇u` in `L²(B_ρ⁺)` as `k`, and that `W` decays like
`∫_{B_ρ⁺} ‖∇W - k‖² ≤ D q ∫_{B_r⁺} ‖∇W - c‖²` with `0 ≤ D` and `0 ≤ q ≤ 1`. Then `u` decays in the
same way up to the distance `E = ∫_{B_r⁺} ‖∇u - ∇W‖²`:
`∫_{B_ρ⁺} ‖∇u - b‖² ≤ 4 D q ∫_{B_r⁺} ‖∇u - c‖² + (4 D + 2) E`. -/
theorem setIntegral_ball_inter_norm_gradient_sub_sq_le_add_of_le
    {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume U 2}
    {z b k c : EuclideanSpace ℝ (Fin (n + 1))} {r ρ D q : ℝ}
    {W : W1p volume (⟨ball z r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    (hball : ball z r ⊆ U) (hρr : ρ ≤ r) (hD : 0 ≤ D) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hbest : ∫ x in ball z ρ ∩ H, ‖W1p.gradient u x - b‖ ^ 2 ≤
      ∫ x in ball z ρ ∩ H, ‖W1p.gradient u x - k‖ ^ 2)
    (hdecay : ∫ x in ball z ρ ∩ H, ‖W1p.gradient W x - k‖ ^ 2 ≤
      D * q * ∫ x in ball z r ∩ H, ‖W1p.gradient W x - c‖ ^ 2) :
    ∫ x in ball z ρ ∩ H, ‖W1p.gradient u x - b‖ ^ 2 ≤
      4 * D * q * (∫ x in ball z r ∩ H, ‖W1p.gradient u x - c‖ ^ 2) +
        (4 * D + 2) * ∫ x in ball z r ∩ H, ‖W1p.gradient u x - W1p.gradient W x‖ ^ 2 := by
  set S := ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1))))
  have hS : volume S ≠ ⊤ := measure_ball_inter_ne_top
  have hsS : ball z ρ ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ S :=
    inter_subset_inter_left _ (ball_subset_ball hρr)
  have hfm : MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) 2 (volume.restrict S) :=
    (Lp.memLp (W1p.gradient u)).mono_measure
      (Measure.restrict_mono (inter_subset_left.trans hball) le_rfl)
  have hWm : MemLp (W1p.gradient W : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) 2 (volume.restrict S) :=
    (Lp.memLp (W1p.gradient W)).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  exact setIntegral_norm_sub_sq_le_add_of_le hsS hD hq0 hq1
    (hfm.integrableOn_norm_sub_sq_of_subset subset_rfl hS c)
    (hWm.integrableOn_norm_sub_sq_of_subset hsS (ne_top_of_le_ne_top hS (measure_mono hsS)) k)
    ((hfm.sub hWm).integrable_norm_pow two_ne_zero) hbest hdecay

/-- **Transferring both decay estimates from a comparison function on half-balls.** Let
`u ∈ H¹(U)`, `ball z r ⊆ U` and `W ∈ H¹(B_r)`, write `B_t⁺ = B(z, t) ∩ H`, and suppose that `W`
decays like `∫_{B_ρ⁺} ‖∇W‖² ≤ C₁ (ρ / r)^{n+1} ∫_{B_r⁺} ‖∇W‖²` and
`∫_{B_ρ⁺} ‖∇W - p_ρ‖² ≤ C₂ (ρ / r)^{n+3} ∫_{B_r⁺} ‖∇W - t ν‖²` for every real `t`, where `p_ρ` is
the multiple of `ν` closest to `∇W` in `L²(B_ρ⁺)`. Then `u` decays in the same way up to the
distance `E = ∫_{B_r⁺} ‖∇u - ∇W‖²`:
`∫_{B_ρ⁺} ‖∇u‖² ≤ 4 C₁ (ρ / r)^{n+1} ∫_{B_r⁺} ‖∇u‖² + (4 C₁ + 2) E`, and the same with `C₂`, the
exponent `n + 3` and the distances to the multiples of `ν`. -/
private theorem setIntegral_ball_inter_le_add_of_le {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {u : W1p volume U 2} {ν z : EuclideanSpace ℝ (Fin (n + 1))} {r ρ C₁ C₂ : ℝ}
    {W : W1p volume (⟨ball z r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    (hball : ball z r ⊆ U) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hρ : 0 < ρ) (hρr : ρ ≤ r)
    (hd₁ : ∫ x in ball z ρ ∩ H, ‖W1p.gradient W x‖ ^ 2 ≤
      C₁ * (ρ / r) ^ (n + 1) * ∫ x in ball z r ∩ H, ‖W1p.gradient W x‖ ^ 2)
    (hd₂ : ∀ t : ℝ, ∫ x in ball z ρ ∩ H, ‖W1p.gradient W x -
        (⟪⨍ y in ball z ρ ∩ H, W1p.gradient W y, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ^ 2 ≤
      C₂ * (ρ / r) ^ (n + 1 + 2) * ∫ x in ball z r ∩ H, ‖W1p.gradient W x - t • ν‖ ^ 2) :
    ∫ x in ball z ρ ∩ H, ‖W1p.gradient u x‖ ^ 2 ≤
        4 * C₁ * (ρ / r) ^ (n + 1) * (∫ x in ball z r ∩ H, ‖W1p.gradient u x‖ ^ 2) +
          (4 * C₁ + 2) * ∫ x in ball z r ∩ H, ‖W1p.gradient u x - W1p.gradient W x‖ ^ 2 ∧
      ∫ x in ball z ρ ∩ H, ‖W1p.gradient u x -
          (⟪⨍ y in ball z ρ ∩ H, W1p.gradient u y, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ^ 2 ≤
        4 * C₂ * (ρ / r) ^ (n + 1 + 2) * (∫ x in ball z r ∩ H, ‖W1p.gradient u x -
          (⟪⨍ y in ball z r ∩ H, W1p.gradient u y, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ^ 2) +
          (4 * C₂ + 2) * ∫ x in ball z r ∩ H, ‖W1p.gradient u x - W1p.gradient W x‖ ^ 2 := by
  have hr : 0 < r := hρ.trans_le hρr
  have hq0 : 0 ≤ ρ / r := by positivity
  have hq1 : ρ / r ≤ 1 := (div_le_one hr).2 hρr
  have hs : volume (ball z ρ ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1))))) ≠ ⊤ :=
    measure_ball_inter_ne_top
  refine ⟨?_, setIntegral_ball_inter_norm_gradient_sub_sq_le_add_of_le hball hρr hC₂
    (pow_nonneg hq0 _) (pow_le_one₀ hq0 hq1)
    (setIntegral_norm_sub_inner_setAverage_div_smul_sq_le_of_subset subset_rfl hs
      ((Lp.memLp (W1p.gradient u)).mono_measure (Measure.restrict_mono
        (inter_subset_left.trans ((ball_subset_ball hρr).trans hball)) le_rfl)) ν _) (hd₂ _)⟩
  simpa only [sub_zero] using setIntegral_ball_inter_norm_gradient_sub_sq_le_add_of_le (b := 0)
    (k := 0) (c := 0) hball hρr hC₁ (pow_nonneg hq0 _) (pow_le_one₀ hq0 hq1) le_rfl
    (by simpa only [sub_zero] using hd₁)

/-- **Comparison with the frozen problem on half-balls.** There is `A`, depending only on `n`,
`λ` and `Λ`, such that the following holds. Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `z` lie
on its boundary hyperplane, and write `B_t⁺ = B(z, t) ∩ H`. Let `u ∈ H¹(U)` vanish on `U ∖ H` and
solve `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on `U ∩ H`, let `ball z r ⊆ U`, let `a(z)` be uniformly
elliptic with constants `λ`, `Λ`, let `a` and `G` be `α`-Hölder on `ball z r` with constants
`K_a` and `K_G`, and let `f ∈ L²(B_r⁺)`. Write `Φ(t) = ∫_{B_t⁺} ‖∇u‖²` and
`ψ(t) = ∫_{B_t⁺} ‖∇u - p_t‖²`, where `p_t` is the multiple of `ν` closest to `∇u` in `L²(B_t⁺)`, and
`e = r^{2α} (K_a / λ)² Φ(r) + r^{2α} K_G² r^{n+1} + 4 r² ∫_{B_r⁺} f²`. Then for `0 < ρ ≤ r`,
`Φ(ρ) ≤ A (ρ / r)^{n+1} Φ(r) + A e` and `ψ(ρ) ≤ A (ρ / r)^{n+3} ψ(r) + A e`. -/
private theorem exists_comparison_ball_inter (n : ℕ) (lam Lam : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume U 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {s : Set (EuclideanSpace ℝ (Fin (n + 1)))}
      {ν z : EuclideanSpace ℝ (Fin (n + 1))} {c₀ r ρ : ℝ} {α Ka KG : ℝ≥0},
      UniformlyEllipticOn s a lam Lam → z ∈ s → 0 < α → ν ≠ 0 →
      (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪z, ν⟫_ℝ = c₀ →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball z r) →
      HolderOnWith KG α G (ball z r) →
      (∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
          (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
        (∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in U ⊓ H, f x * φ x) →
      MemLp f 2 (volume.restrict (ball z r ∩ H)) → ball z r ⊆ U → 0 < ρ → ρ ≤ r →
        ∫ x in ball z ρ ∩ H, ‖W1p.gradient u x‖ ^ 2 ≤
            A * (ρ / r) ^ ((n : ℝ) + 1) * (∫ x in ball z r ∩ H, ‖W1p.gradient u x‖ ^ 2) +
              A * (r ^ (2 * (α : ℝ)) * ((Ka : ℝ) / lam) ^ 2 *
                (∫ x in ball z r ∩ H, ‖W1p.gradient u x‖ ^ 2) +
                (r ^ (2 * (α : ℝ)) * ((KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) +
                  4 * r ^ 2 * ∫ x in ball z r ∩ H, f x ^ 2)) ∧
        ∫ x in ball z ρ ∩ H, ‖W1p.gradient u x -
            (⟪⨍ y in ball z ρ ∩ H, W1p.gradient u y, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ^ 2 ≤
            A * (ρ / r) ^ ((n : ℝ) + 1 + 2) * (∫ x in ball z r ∩ H, ‖W1p.gradient u x -
              (⟪⨍ y in ball z r ∩ H, W1p.gradient u y, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ^ 2) +
              A * (r ^ (2 * (α : ℝ)) * ((Ka : ℝ) / lam) ^ 2 *
                (∫ x in ball z r ∩ H, ‖W1p.gradient u x‖ ^ 2) +
                (r ^ (2 * (α : ℝ)) * ((KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) +
                  4 * r ^ 2 * ∫ x in ball z r ∩ H, f x ^ 2)) := by
  by_cases hlam : 0 < lam
  swap
  · exact ⟨0, le_rfl, fun h => absurd h.pos hlam⟩
  obtain ⟨C₁, hC₁, hdec₁⟩ :=
    exists_setIntegral_ball_inter_norm_gradient_sq_le (ι := Fin (n + 1)) (Lam := Lam) hlam
  obtain ⟨C₂, hC₂, hdec₂⟩ :=
    exists_setIntegral_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le
      (ι := Fin (n + 1)) (Lam := Lam) hlam
  set ω := volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  have hω : 0 ≤ ω := measureReal_nonneg
  refine ⟨3 * (1 + ω) * (4 * (C₁ + C₂) + 2) * (1 + (lam ^ 2)⁻¹), by positivity, ?_⟩
  intro U H u a G f s ν z c₀ r ρ α Ka KG h hz hα hν hH hzc haK hGK hu0 hu hf hball hρ hρr
  have hr : 0 < r := hρ.trans_le hρr
  obtain ⟨W, hW0, hW, hE⟩ := exists_frozen_ball_inter h hz hα haK hGK hu0 hu hf hball hr
  have hd₁ := hdec₁ (U := ⟨ball z r, isOpen_ball⟩) (h.lower_bound hz) (h.upper_bound hz) hν hH hzc
    subset_rfl hW0 hW hρ.le hρr
  rw [Fintype.card_fin] at hd₁
  obtain ⟨hY₁, hY₂⟩ := setIntegral_ball_inter_le_add_of_le (H := H) hball hC₁.le hC₂.le hρ hρr hd₁
    fun t => by
      have hd₂ := hdec₂ (U := ⟨ball z r, isOpen_ball⟩) (h.lower_bound hz) (h.upper_bound hz) hν hH
        hzc subset_rfl hW0 hW hρ.le hρr t
      rwa [Fintype.card_fin] at hd₂
  -- The error term of the comparison, with `λ` taken out of the data.
  set S := ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1))))
  have hΦr : 0 ≤ ∫ x in S, ‖W1p.gradient u x‖ ^ 2 :=
    setIntegral_nonneg (measurableSet_ball.inter H.isOpen.measurableSet) fun _ _ => by positivity
  have hI : 0 ≤ ∫ x in S, f x ^ 2 :=
    setIntegral_nonneg (measurableSet_ball.inter H.isOpen.measurableSet) fun _ _ => by positivity
  have he := rpow_mul_add_mul_div_sq_le (α := (α : ℝ)) (Ka := (Ka : ℝ)) (KG := (KG : ℝ))
    (lam := lam) hr.le hΦr (by positivity : (0 : ℝ) ≤ r ^ ((n : ℝ) + 1)) hI
  have he' : 0 ≤ r ^ (2 * (α : ℝ)) * ((Ka : ℝ) / lam) ^ 2 * (∫ x in S, ‖W1p.gradient u x‖ ^ 2) +
      (r ^ (2 * (α : ℝ)) * ((KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) + 4 * r ^ 2 * ∫ x in S, f x ^ 2) :=
    by positivity
  refine ⟨?_, ?_⟩
  · have hrp : (ρ / r) ^ ((n : ℝ) + 1) = (ρ / r) ^ (n + 1) := by
      rw [← Real.rpow_natCast]; push_cast; ring_nf
    rw [hrp]
    exact le_mul_add_mul_of_le_of_le_mul hC₁.le hC₂.le (by positivity) hω (by positivity) he' hY₁
      hE he
  · have hrp : (ρ / r) ^ ((n : ℝ) + 1 + 2) = (ρ / r) ^ (n + 1 + 2) := by
      rw [← Real.rpow_natCast]; push_cast; ring_nf
    rw [hrp, add_comm C₁ C₂]
    exact le_mul_add_mul_of_le_of_le_mul hC₂.le hC₁.le (by positivity) hω (by positivity) he' hY₂
      hE he

end Comparison

section HalfBall

/-- **Morrey decay with the full exponent from Campanato decay, at a flat boundary.** Let `κ > 0`
and `θ ∈ (0, 1]`. There is `C₃`, depending only on `n`, `κ`, `θ` and `C₂`, such that the following
holds. Let `z` lie on the boundary hyperplane of `H = {x | c₀ < ⟪x, ν⟫}`, let `g` be square
integrable on `U ⊇ ball z R`, let `∫_{B_R ∩ H} ‖g‖² ≤ V`, and let
`∫_{B_t ∩ H} ‖g - p_t‖² ≤ C₂ V (t / R)^{n+1+2κ}` for `0 < t ≤ θ R`, where `p_t` is the multiple of
`ν` closest to `g` in `L²(B_t ∩ H)`. Then `∫_{B_t ∩ H} ‖g‖² ≤ C₃ V (t / R)^{n+1}` for
`0 < t ≤ θ R`: the averages of `g` over the half-balls stay bounded. This is the case of the
half-space, which has density one half in the balls centred on its boundary, of
`TauCeti.MeasureTheory.exists_setIntegral_ball_inter_norm_sq_le_mul_div_pow`, since the distance
to the multiples of `ν` bounds the square mean oscillation. -/
private theorem exists_setIntegral_ball_inter_norm_sq_le_rpow {κ θ C₂ : ℝ} (hκ : 0 < κ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hC₂ : 0 ≤ C₂) :
    ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∀ {U : Set (EuclideanSpace ℝ (Fin (n + 1)))}
      {H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {ν z : EuclideanSpace ℝ (Fin (n + 1))} {c₀ R V : ℝ},
      MemLp g 2 (volume.restrict U) → ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪z, ν⟫_ℝ = c₀ →
      ball z R ⊆ U → 0 < R → ∫ x in ball z R ∩ H, ‖g x‖ ^ 2 ≤ V →
      (∀ t, 0 < t → t ≤ θ * R →
        ∫ x in ball z t ∩ H, ‖g x - (⟪⨍ y in ball z t ∩ H, g y, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ^ 2 ≤
          C₂ * V * (t / R) ^ ((n : ℝ) + 1 + 2 * κ)) →
      ∀ t, 0 < t → t ≤ θ * R →
        ∫ x in ball z t ∩ H, ‖g x‖ ^ 2 ≤ C₃ * V * (t / R) ^ ((n : ℝ) + 1) := by
  obtain ⟨C₃, hC₃, h⟩ := exists_setIntegral_ball_inter_norm_sq_le_mul_div_pow
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))))
    (F := EuclideanSpace ℝ (Fin (n + 1))) (c := 2⁻¹) hκ hθ hθ1 hC₂ (by norm_num)
  refine ⟨C₃, hC₃, ?_⟩
  intro U H g ν z c₀ R V hg hν hH hz hball hR hΦR hψ t ht htθ
  have hθR : θ * R ≤ R := mul_le_of_le_one_left hR.le hθ1
  have hgs : ∀ s ≤ R, MemLp g 2 (volume.restrict (ball z s ∩ H)) := fun s hs =>
    hg.mono_measure (Measure.restrict_mono (inter_subset_left.trans
      ((ball_subset_ball hs).trans hball)) le_rfl)
  -- The half-space has density one half in the closed balls centred on its boundary hyperplane.
  have hdens (t : ℝ) : (((2 : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) * volume (closedBall z t) ≤
      volume (closedBall z t ∩ H) := by
    rw [show (H : Set (EuclideanSpace ℝ (Fin (n + 1)))) = {y | c₀ < ⟪y, ν⟫_ℝ} from Set.ext hH]
    exact volume.inv_two_mul_addHaar_closedBall_le_addHaar_closedBall_inter_setOf_lt_inner hν hz.ge
  refine (h (Ω := H) (g := g) (fun t _ _ => hdens t) (hgs R le_rfl) hR hΦR (fun s hs hsθ => ?_) t
    ht htθ).trans_eq ?_
  · -- The distance to the multiples of `ν` bounds the square mean oscillation.
    have hS : volume (ball z s ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1))))) ≠ ⊤ :=
      measure_ball_inter_ne_top
    refine (setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq hS
      ((hgs s (hsθ.trans hθR)).integrableOn_of_subset one_le_two subset_rfl hS)
      ((hgs s (hsθ.trans hθR)).integrableOn_norm_sub_sq_of_subset subset_rfl hS _)).trans
      ((hψ s hs hsθ).trans_eq ?_)
    rw [finrank_euclideanSpace_fin, Real.rpow_add (div_pos hs hR), ← Real.rpow_natCast,
      Nat.cast_succ]
  · rw [finrank_euclideanSpace_fin, ← Real.rpow_natCast, Nat.cast_succ]

end HalfBall

section Decay

/-- **Morrey decay at a boundary centre.** For `α > 0` and `γ > 0` there are `θ ∈ (0, 1]` and
`C`, depending only on `n`, `α`, `γ`, `λ`, `Λ` and `M`, such that, in the setting of the main
theorems, `∫_{B_ρ⁺} ‖∇u‖² ≤ C V (ρ / R)^{n+1-γ}` for `0 < ρ ≤ θ R`. -/
private theorem exists_setIntegral_ball_inter_norm_gradient_sq_le_rpow {α : ℝ≥0} (hα : 0 < α)
    {γ : ℝ} (hγ : 0 < γ) {lam Lam M : ℝ} :
    ∃ θ C : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 0 ≤ C ∧ ∀ {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume U 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {s : Set (EuclideanSpace ℝ (Fin (n + 1)))}
      {ν z : EuclideanSpace ℝ (Fin (n + 1))} {c₀ R V : ℝ} {Ka KG : ℝ≥0},
      UniformlyEllipticOn s a lam Lam → z ∈ s → ν ≠ 0 →
      (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪z, ν⟫_ℝ = c₀ →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball z R) →
      HolderOnWith KG α G (ball z R) →
      (∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
          (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
        (∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in U ⊓ H, f x * φ x) →
      MemLp f 2 (volume.restrict (ball z R ∩ H)) → ball z R ⊆ U → 0 < R →
      (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      (∀ r, 0 < r → r ≤ R → r ^ (2 * (α : ℝ)) * ((KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) +
        4 * r ^ 2 * ∫ x in ball z r ∩ H, f x ^ 2 ≤ V * (r / R) ^ ((n : ℝ) + 1 + 2 * γ)) →
      ∫ x in ball z R ∩ H, ‖W1p.gradient u x‖ ^ 2 ≤ V →
      ∀ ρ, 0 < ρ → ρ ≤ θ * R →
        ∫ x in ball z ρ ∩ H, ‖W1p.gradient u x‖ ^ 2 ≤ C * V * (ρ / R) ^ ((n : ℝ) + 1 - γ) := by
  obtain ⟨A, hA, hcomp⟩ := exists_comparison_ball_inter n lam Lam
  obtain ⟨θ, C, hθ, hθ1, hC, hit⟩ := exists_le_mul_mul_div_rpow_of_le_mul_div_rpow_mul_add
    (d := (n : ℝ) + 1) (M := M / lam) hA (by exact_mod_cast hα) hγ
  refine ⟨θ, C, hθ, hθ1, hC, ?_⟩
  intro U H u a G f s ν z c₀ R V Ka KG h hz hν hH hzc haK hGK hu0 hu hf hball hR hM hD hΦR
  have hV0 : 0 ≤ V := (setIntegral_nonneg (measurableSet_ball.inter H.isOpen.measurableSet)
    fun _ _ => by positivity).trans hΦR
  exact hit (Φ := fun t => ∫ x in ball z t ∩ H, ‖W1p.gradient u x‖ ^ 2)
    (D := fun r => r ^ (2 * (α : ℝ)) * ((KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) +
      4 * r ^ 2 * ∫ x in ball z r ∩ H, f x ^ 2) hR (div_nonneg Ka.property h.pos.le)
    (by rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right hM h.pos.le)
    (((Lp.memLp _).monotoneOn_setIntegral_ball_inter_norm_sq hball).mono Ioc_subset_Iic_self)
    (fun t _ => setIntegral_nonneg (measurableSet_ball.inter H.isOpen.measurableSet)
      fun _ _ => by positivity) hΦR
    (fun r hr hrR => (hD r hr hrR).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge (by positivity) ((div_le_one hR).2 hrR) (by linarith))
      hV0))
    fun ρ r hρ hρr hrR => (hcomp h hz hα hν hH hzc (haK.mono (ball_subset_ball hrR))
      (hGK.mono (ball_subset_ball hrR)) hu0 hu (hf.mono_measure (Measure.restrict_mono
        (inter_subset_inter_left _ (ball_subset_ball hrR)) le_rfl))
      ((ball_subset_ball hrR).trans hball) hρ hρr).1

/-- **Campanato decay at a boundary centre from a Morrey bound.** Let `α > 0`, `θ ∈ (0, 1]` and
`L ≥ 0`, and let `τ < n + 3` with `τ ≤ 2α + β` and `τ ≤ n + 1 + 2γ`. There is `C`, depending only on
`n`, `α`, `τ`, `λ`, `Λ`, `M`, `θ` and `L`, such that, in the setting of the main theorems, if
`∫_{B_t⁺} ‖∇u‖² ≤ L V (t / R)^β` for `0 < t ≤ θ R`, then `∫_{B_ρ⁺} ‖∇u - p_ρ‖² ≤ C V (ρ / R)^τ` for
`0 < ρ ≤ θ R`. -/
private theorem exists_setIntegral_ball_inter_norm_gradient_sub_le_rpow {α : ℝ≥0} (hα : 0 < α)
    {β γ τ : ℝ} (hτβ : τ ≤ 2 * (α : ℝ) + β) (hτγ : τ ≤ (n : ℝ) + 1 + 2 * γ)
    (hτ : τ < (n : ℝ) + 3) {lam Lam M θ L : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume U 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {s : Set (EuclideanSpace ℝ (Fin (n + 1)))}
      {ν z : EuclideanSpace ℝ (Fin (n + 1))} {c₀ R V : ℝ} {Ka KG : ℝ≥0},
      UniformlyEllipticOn s a lam Lam → z ∈ s → ν ≠ 0 →
      (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪z, ν⟫_ℝ = c₀ →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball z R) →
      HolderOnWith KG α G (ball z R) →
      (∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
          (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
        (∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in U ⊓ H, f x * φ x) →
      MemLp f 2 (volume.restrict (ball z R ∩ H)) → ball z R ⊆ U → 0 < R →
      (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      (∀ r, 0 < r → r ≤ R → r ^ (2 * (α : ℝ)) * ((KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) +
        4 * r ^ 2 * ∫ x in ball z r ∩ H, f x ^ 2 ≤ V * (r / R) ^ ((n : ℝ) + 1 + 2 * γ)) →
      ∫ x in ball z R ∩ H, ‖W1p.gradient u x‖ ^ 2 ≤ V →
      (∀ t, 0 < t → t ≤ θ * R →
        ∫ x in ball z t ∩ H, ‖W1p.gradient u x‖ ^ 2 ≤ L * V * (t / R) ^ β) →
      ∀ ρ, 0 < ρ → ρ ≤ θ * R →
        ∫ x in ball z ρ ∩ H, ‖W1p.gradient u x -
            (⟪⨍ y in ball z ρ ∩ H, W1p.gradient u y, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ^ 2 ≤
          C * V * (ρ / R) ^ τ := by
  obtain ⟨A, hA, hcomp⟩ := exists_comparison_ball_inter n lam Lam
  obtain ⟨C, hC, hit⟩ :=
    exists_le_mul_mul_div_rpow_of_le_mul_div_rpow_mul_add_of_le_mul_mul_div_rpow (α := α)
      (κ := (n : ℝ) + 1 + 2 * γ) (δ := (n : ℝ) + 1 + 2) (M := M / lam) hA hτβ hτγ (by linarith) hθ
      hθ1 hL
  refine ⟨C, hC, ?_⟩
  intro U H u a G f s ν z c₀ R V Ka KG h hz hν hH hzc haK hGK hu0 hu hf hball hR hM hD hΦR hΦ
  have hθR : θ * R ≤ R := mul_le_of_le_one_left hR.le hθ1
  have hg : ∀ r ≤ R, MemLp (W1p.gradient u) 2 (volume.restrict (ball z r ∩ H)) := fun r hr =>
    (Lp.memLp (W1p.gradient u)).mono_measure
      (Measure.restrict_mono (inter_subset_left.trans ((ball_subset_ball hr).trans hball)) le_rfl)
  exact hit (φ := fun t => ∫ x in ball z t ∩ H, ‖W1p.gradient u x -
      (⟪⨍ y in ball z t ∩ H, W1p.gradient u y, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ^ 2)
    (Φ := fun t => ∫ x in ball z t ∩ H, ‖W1p.gradient u x‖ ^ 2)
    (D := fun r => r ^ (2 * (α : ℝ)) * ((KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) +
      4 * r ^ 2 * ∫ x in ball z r ∩ H, f x ^ 2) hR (div_nonneg Ka.property h.pos.le)
    (by rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right hM h.pos.le)
    (fun s _ t ht hst => setIntegral_norm_sub_inner_setAverage_div_smul_sq_le_of_subset
      (inter_subset_inter_left _ (ball_subset_ball hst)) measure_ball_inter_ne_top
      (hg t (ht.2.trans hθR)) ν _)
    (fun t _ => setIntegral_nonneg (measurableSet_ball.inter H.isOpen.measurableSet)
      fun _ _ => by positivity)
    ((setIntegral_norm_sub_inner_setAverage_div_smul_sq_le_of_subset
      (inter_subset_inter_left _ (ball_subset_ball hθR)) measure_ball_inter_ne_top
      (hg R le_rfl) ν 0).trans (by simpa only [zero_smul, sub_zero] using hΦR))
    (fun t _ => setIntegral_nonneg (measurableSet_ball.inter H.isOpen.measurableSet)
      fun _ _ => by positivity) hΦ (fun r hr hrθ => hD r hr (hrθ.trans hθR))
    fun ρ r hρ hρr hrθ => (hcomp h hz hα hν hH hzc (haK.mono (ball_subset_ball (hrθ.trans hθR)))
      (hGK.mono (ball_subset_ball (hrθ.trans hθR))) hu0 hu (hf.mono_measure
        (Measure.restrict_mono (inter_subset_inter_left _ (ball_subset_ball (hrθ.trans hθR)))
          le_rfl)) ((ball_subset_ball (hrθ.trans hθR)).trans hball) hρ hρr).2

/-- **Decay at a boundary centre.** Both decay estimates of the main theorems, with one `θ` and
one `C`: the Morrey bound `∫_{B_ρ⁺} ‖∇u‖² ≤ C V (ρ / R)^{n+1}` and the Campanato bound
`∫_{B_ρ⁺} ‖∇u - p_ρ‖² ≤ C V (ρ / R)^{n+1+2γ}` for `0 < ρ ≤ θ R`. -/
private theorem exists_decay_ball_inter_of_holderOnWith {α : ℝ≥0} {γ : ℝ} (hγ : 0 < γ)
    (hγα : γ ≤ α) (hγ1 : γ < 1) {lam Lam M : ℝ} :
    ∃ θ C : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 0 ≤ C ∧ ∀ {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume U 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {s : Set (EuclideanSpace ℝ (Fin (n + 1)))}
      {ν z : EuclideanSpace ℝ (Fin (n + 1))} {c₀ R V : ℝ} {Ka KG : ℝ≥0},
      UniformlyEllipticOn s a lam Lam → z ∈ s → ν ≠ 0 →
      (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪z, ν⟫_ℝ = c₀ →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball z R) →
      HolderOnWith KG α G (ball z R) →
      (∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
          (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
        (∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in U ⊓ H, f x * φ x) →
      MemLp f 2 (volume.restrict (ball z R ∩ H)) → ball z R ⊆ U → 0 < R →
      (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      (∀ r, 0 < r → r ≤ R → r ^ (2 * (α : ℝ)) * ((KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) +
        4 * r ^ 2 * ∫ x in ball z r ∩ H, f x ^ 2 ≤ V * (r / R) ^ ((n : ℝ) + 1 + 2 * γ)) →
      ∫ x in ball z R ∩ H, ‖W1p.gradient u x‖ ^ 2 ≤ V →
      ∀ ρ, 0 < ρ → ρ ≤ θ * R →
        ∫ x in ball z ρ ∩ H, ‖W1p.gradient u x‖ ^ 2 ≤ C * V * (ρ / R) ^ ((n : ℝ) + 1) ∧
        ∫ x in ball z ρ ∩ H, ‖W1p.gradient u x -
            (⟪⨍ y in ball z ρ ∩ H, W1p.gradient u y, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ^ 2 ≤
          C * V * (ρ / R) ^ ((n : ℝ) + 1 + 2 * γ) := by
  have hα : 0 < α := by exact_mod_cast hγ.trans_le hγα
  -- Morrey decay with exponent `n + 1 - γ`.
  obtain ⟨θ, C₁, hθ, hθ1, hC₁, hΦ1⟩ :=
    exists_setIntegral_ball_inter_norm_gradient_sq_le_rpow (n := n) hα hγ (Lam := Lam) (M := M)
  -- Campanato decay with exponent `n + 1 + γ`.
  obtain ⟨C₂, hC₂, hψ2⟩ := exists_setIntegral_ball_inter_norm_gradient_sub_le_rpow (n := n) hα
    (β := (n : ℝ) + 1 - γ) (γ := γ) (τ := (n : ℝ) + 1 + γ) (by linarith) (by linarith)
    (by linarith) (Lam := Lam) (M := M) hθ hθ1 hC₁
  -- Bounded averages, hence Morrey decay with exponent `n + 1`.
  obtain ⟨C₃, hC₃, hΦ3⟩ := exists_setIntegral_ball_inter_norm_sq_le_rpow (n := n) (κ := γ / 2)
    (by positivity) hθ hθ1 hC₂
  -- Campanato decay with exponent `n + 1 + 2γ`.
  obtain ⟨C₄, hC₄, hψ4⟩ := exists_setIntegral_ball_inter_norm_gradient_sub_le_rpow (n := n) hα
    (β := (n : ℝ) + 1) (γ := γ) (τ := (n : ℝ) + 1 + 2 * γ) (by linarith) le_rfl
    (by linarith) (Lam := Lam) (M := M) hθ hθ1 hC₃
  refine ⟨θ, C₃ + C₄, hθ, hθ1, by positivity, ?_⟩
  intro U H u a G f s ν z c₀ R V Ka KG h hz hν hH hzc haK hGK hu0 hu hf hball hR hM hD hΦR
  have hV0 : 0 ≤ V := (setIntegral_nonneg (measurableSet_ball.inter H.isOpen.measurableSet)
    fun _ _ => by positivity).trans hΦR
  have h1 := hΦ1 h hz hν hH hzc haK hGK hu0 hu hf hball hR hM hD hΦR
  have h2 := hψ2 h hz hν hH hzc haK hGK hu0 hu hf hball hR hM hD hΦR h1
  have h3 := hΦ3 (Lp.memLp _) hν hH hzc hball hR hΦR fun t ht htθ =>
    (h2 t ht htθ).trans_eq (by ring_nf)
  have h4 := hψ4 h hz hν hH hzc haK hGK hu0 hu hf hball hR hM hD hΦR h3
  intro ρ hρ hρθ
  refine ⟨(h3 ρ hρ hρθ).trans ?_, (h4 ρ hρ hρθ).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hC₄) hV0) (by positivity)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left hC₃) hV0) (by positivity)

/-- **Morrey decay of the gradient at a flat boundary, for Hölder coefficients.** Let `α > 0`
and `γ > 0`. There are `θ ∈ (0, 1]` and `C ≥ 0`, depending only on `n`, `α`, `γ`, `λ`, `Λ` and
`M`, such that the following holds. Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `z` lie on its
boundary hyperplane, and write `B_t⁺ = B(z, t) ∩ H`. Let `u ∈ H¹(U)` vanish on `U ∖ H` and solve
`-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on `U ∩ H`, that is
`∫ ⟨a ∇u, ∇φ⟩ = ∫ ⟨G, ∇φ⟩ + ∫ f φ` for every test function `φ` on `U ∩ H`. Let `ball z R ⊆ U`, let
`a(z)` be uniformly elliptic with constants `λ`, `Λ`, let `a` and `G` be `α`-Hölder on `ball z R`
with constants `K_a` and `K_G`, the oscillation of `a` measured in the operator norm of the
attached bilinear forms, where `K_a R^α ≤ M`, and let `f ∈ L²(B_R⁺)`. If the data decay like
`r^{2α} K_G² r^{n+1} + 4 r² ∫_{B_r⁺} f² ≤ V (r / R)^{n+1+2γ}` for `0 < r ≤ R` and
`∫_{B_R⁺} ‖∇u‖² ≤ V`, then

`∫_{B_ρ⁺} ‖∇u‖² ≤ C V (ρ / R)^{n+1}` for `0 < ρ ≤ θ R`.

So the gradient stays bounded in `L²` mean up to the flat boundary. A datum `f ∈ L^q`, `q > n + 1`,
decays as required with `γ = min α (1 - (n + 1) / q)`, by Hölder's inequality. -/
theorem exists_setIntegral_ball_inter_norm_gradient_sq_le_of_holderOnWith {α : ℝ≥0}
    (hα : 0 < α) {γ : ℝ} (hγ : 0 < γ) {lam Lam M : ℝ} :
    ∃ θ C : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 0 ≤ C ∧ ∀ {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume U 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {s : Set (EuclideanSpace ℝ (Fin (n + 1)))}
      {ν z : EuclideanSpace ℝ (Fin (n + 1))} {c₀ R V : ℝ} {Ka KG : ℝ≥0},
      UniformlyEllipticOn s a lam Lam → z ∈ s → ν ≠ 0 →
      (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪z, ν⟫_ℝ = c₀ →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball z R) →
      HolderOnWith KG α G (ball z R) →
      (∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
          (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
        (∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in U ⊓ H, f x * φ x) →
      MemLp f 2 (volume.restrict (ball z R ∩ H)) → ball z R ⊆ U → 0 < R →
      (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      (∀ r, 0 < r → r ≤ R → r ^ (2 * (α : ℝ)) * ((KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) +
        4 * r ^ 2 * ∫ x in ball z r ∩ H, f x ^ 2 ≤ V * (r / R) ^ ((n : ℝ) + 1 + 2 * γ)) →
      ∫ x in ball z R ∩ H, ‖W1p.gradient u x‖ ^ 2 ≤ V →
      ∀ ρ, 0 < ρ → ρ ≤ θ * R →
        ∫ x in ball z ρ ∩ H, ‖W1p.gradient u x‖ ^ 2 ≤ C * V * (ρ / R) ^ ((n : ℝ) + 1) := by
  -- The data also decay with the smaller exponent `n + 1 + 2 min γ (min α (1 / 2))`.
  obtain ⟨θ, C, hθ, hθ1, hC, h⟩ := exists_decay_ball_inter_of_holderOnWith (n := n) (α := α)
    (γ := min γ (min (α : ℝ) (1 / 2))) (lt_min hγ (lt_min (by exact_mod_cast hα) one_half_pos))
    ((min_le_right _ _).trans (min_le_left _ _))
    (((min_le_right _ _).trans (min_le_right _ _)).trans_lt one_half_lt_one) (lam := lam)
    (Lam := Lam) (M := M)
  refine ⟨θ, C, hθ, hθ1, hC, ?_⟩
  intro U H u a G f s ν z c₀ R V Ka KG h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ hR hM hD hV ρ hρ hρθ
  have hV0 : 0 ≤ V := (setIntegral_nonneg (measurableSet_ball.inter H.isOpen.measurableSet)
    fun _ _ => by positivity).trans hV
  refine (h h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ hR hM (fun r hr hrR => (hD r hr hrR).trans ?_) hV ρ
    hρ hρθ).1
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge (by positivity)
    ((div_le_one hR).2 hrR) (by linarith [min_le_left γ (min (α : ℝ) (1 / 2))])) hV0

/-- **Campanato decay of the gradient at a flat boundary, for Hölder coefficients.** Let
`0 < γ < 1` with `γ ≤ α`. There are `θ ∈ (0, 1]` and `C ≥ 0`, depending only on `n`, `α`, `γ`,
`λ`, `Λ` and `M`, such that the following holds. Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `z`
lie on its boundary hyperplane, and write `B_t⁺ = B(z, t) ∩ H`. Let `u ∈ H¹(U)` vanish on `U ∖ H`
and solve `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on `U ∩ H`, that is
`∫ ⟨a ∇u, ∇φ⟩ = ∫ ⟨G, ∇φ⟩ + ∫ f φ` for every test function `φ` on `U ∩ H`. Let `ball z R ⊆ U`, let
`a(z)` be uniformly elliptic with constants `λ`, `Λ`, let `a` and `G` be `α`-Hölder on `ball z R`
with constants `K_a` and `K_G`, the oscillation of `a` measured in the operator norm of the
attached bilinear forms, where `K_a R^α ≤ M`, and let `f ∈ L²(B_R⁺)`. If the data decay like
`r^{2α} K_G² r^{n+1} + 4 r² ∫_{B_r⁺} f² ≤ V (r / R)^{n+1+2γ}` for `0 < r ≤ R` and
`∫_{B_R⁺} ‖∇u‖² ≤ V`, then for `0 < ρ ≤ θ R`

`∫_{B_ρ⁺} ‖∇u - p_ρ‖² ≤ C V (ρ / R)^{n+1+2γ}`,

where `p_ρ = (⟪(∇u)_{B_ρ⁺}, ν⟫ / ‖ν‖²) ν` is the multiple of `ν` closest to `∇u` in `L²(B_ρ⁺)`.
This is the decay of the boundary excess behind the `C^{1,γ}` estimate up to a flat boundary on
which `u` vanishes: in square mean, the gradient approaches a normal vector at the rate `ρ^γ`.
For `f = 0` and `G` `α`-Hölder the exponent is `γ = α` for every `α < 1`. -/
theorem
    exists_setIntegral_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le_of_holderOnWith
    {α : ℝ≥0} {γ : ℝ} (hγ : 0 < γ) (hγα : γ ≤ α) (hγ1 : γ < 1) {lam Lam M : ℝ} :
    ∃ θ C : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 0 ≤ C ∧ ∀ {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume U 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {s : Set (EuclideanSpace ℝ (Fin (n + 1)))}
      {ν z : EuclideanSpace ℝ (Fin (n + 1))} {c₀ R V : ℝ} {Ka KG : ℝ≥0},
      UniformlyEllipticOn s a lam Lam → z ∈ s → ν ≠ 0 →
      (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪z, ν⟫_ℝ = c₀ →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball z R) →
      HolderOnWith KG α G (ball z R) →
      (∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
          (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
        (∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in U ⊓ H, f x * φ x) →
      MemLp f 2 (volume.restrict (ball z R ∩ H)) → ball z R ⊆ U → 0 < R →
      (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      (∀ r, 0 < r → r ≤ R → r ^ (2 * (α : ℝ)) * ((KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) +
        4 * r ^ 2 * ∫ x in ball z r ∩ H, f x ^ 2 ≤ V * (r / R) ^ ((n : ℝ) + 1 + 2 * γ)) →
      ∫ x in ball z R ∩ H, ‖W1p.gradient u x‖ ^ 2 ≤ V →
      ∀ ρ, 0 < ρ → ρ ≤ θ * R →
        ∫ x in ball z ρ ∩ H, ‖W1p.gradient u x -
            (⟪⨍ y in ball z ρ ∩ H, W1p.gradient u y, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ^ 2 ≤
          C * V * (ρ / R) ^ ((n : ℝ) + 1 + 2 * γ) := by
  obtain ⟨θ, C, hθ, hθ1, hC, h⟩ := exists_decay_ball_inter_of_holderOnWith (n := n) hγ hγα hγ1
    (lam := lam) (Lam := Lam) (M := M)
  exact ⟨θ, C, hθ, hθ1, hC, fun h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ ρ hρ hρθ =>
    (h h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ ρ hρ hρθ).2⟩

end Decay

end PDE

end TauCeti
