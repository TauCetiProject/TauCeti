/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Interior
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Holder.Interpolation
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.Analysis.SpecificLimits.Absorption
import TauCeti.Topology.MetricSpace.Holder

/-!
# The interior Schauder estimate in scaled form

Let `0 < α < 1`, and let `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` be a non-divergence-form operator on `ℝ^{n+1}`
which is uniformly elliptic and bounded with constants `0 < λ ≤ Λ` on the ball `B_{2r} = B(x₀, 2r)`
(`TauCeti.PDE.UniformlyEllipticOn`), with coefficients `α`-Hölder there with constant `[a]_α`.
This file proves the interior `C^{2,α}` estimate in scaled form,
`exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv_of_mul_rpow_le`:
for every bound `M` there is a constant `C`, depending only on `n`, `α`, `λ`, `Λ` and `M`, such that
whenever `r^α [a]_α ≤ M`, every `u` which is `C²` on `B_{2r}`, with `D²u` `α`-Hölder on each closed
ball `closedBall x₀ ρ`, `ρ < 2r` (with any constants), satisfies

`[D²u]_{α; closedBall x₀ r} ≤ C (r^{-2-α} sup_{B_{2r}} |u| + [L u]_{α; B_{2r}})`.

Both sides scale in the same way under `u ↦ u(x₀ + r ·)`, and `C` depends neither on `r` nor on
the centre. Unlike the estimate on small balls
(`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv`), only
the supremum of `|u|` remains among the lower-order terms: no bounds on `Du` or `D²u` and no
supremum of `L u` are needed. The Hölder continuity of `D²u` on the smaller closed balls enters
only qualitatively.

## The argument

Dilating the estimate on small balls by `y ↦ δ y` gives it on every ball `B(y, δ)` with
`[a]_α δ^α` below a threshold depending only on `n`, `α`, `λ` and `Λ`: there `[D²u]_α` on
`closedBall y (δ / 2)` is at most a constant times
`[L u]_α + δ^{-2-α} sup |u| + δ^{-1-α} sup ‖Du‖ + δ^{-α} sup ‖D²u‖`. For `r ≤ s < t` with `t - s`
small compared with `r`, put `δ = (t - s) / 2`. The local interpolation inequalities
`‖Du‖ ≤ M / ε + H ε^{1+α}` and `‖D²u‖ ≤ 2 M / ε² + 3 H ε^α`
(`HolderOnWith.norm_fderiv_le_of_contDiffOn`,
`HolderOnWith.norm_iteratedFDeriv_two_le_of_contDiffOn`), at a scale `ε = κ δ`
with a small fixed `κ`, bound the first and second derivatives on `closedBall x₀ (s + δ)` by
`sup |u|` and a small multiple of the Hölder constant `Φ(t)` of `D²u` on `closedBall x₀ t`.
Covering `closedBall x₀ s` by the balls `closedBall y (δ / 2)`
(`HolderOnWith.of_dist_lt_of_dist_le`) then gives

`Φ(s) ≤ Φ(t) / 2 + A (t - s)^{-2-α} + C [L u]_α`

with `A` a multiple of `sup |u|`, and the absorption lemma
(`TauCeti.exists_le_mul_mul_rpow_add_of_le_mul_add`) bounds `Φ(r)`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 6.2 and Lemma 6.32 (the interior Schauder estimate and interpolation).
* M. Giaquinta, *Multiple Integrals in the Calculus of Variations and Nonlinear Elliptic
  Systems*, Chapter V, Lemma 3.1 (the absorption lemma).
-/

public section

noncomputable section

open Metric Set
open scoped NNReal

namespace TauCeti.PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- Under a dilation `e y = c y`, the operator `∑ᵢⱼ bᵢⱼ ∂ᵢ∂ⱼ` with constant coefficients `b`,
applied to `u ∘ e` at `y`, is `c²` times the same operator applied to `u` at `e y`. -/
private theorem sum_smul_fderiv_fderiv_comp_dilation (e : E ≃L[ℝ] E) {c : ℝ}
    (he : ∀ y, e y = c • y) (b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (u : E → ℝ) (y : E) :
    ∑ i, ∑ j, b i j • fderiv ℝ (fderiv ℝ (u ∘ e)) y
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      c ^ 2 * ∑ i, ∑ j, b i j • fderiv ℝ (fderiv ℝ u) (e y)
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  simp only [e.fderiv_fderiv_comp_right_apply_apply, he, map_smul, smul_apply,
    smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The estimate on small balls at every radius.** Dilating
`exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv` by `y ↦ δ y` gives a
threshold `c₀` and a constant `C`, depending only on `n`, `α`, `λ` and `Λ`, such that on every ball
`B(x₀, δ)` with `[a]_α δ^α ≤ c₀` the Hölder constant of `D²u` on `closedBall x₀ (δ / 2)` is at most
`C (δ^{2+α} K + N₀ + δ N₁ + δ² N₂) δ^{-2-α}`, where `K` bounds `[L u]_α` and `N₀`, `N₁`, `N₂` bound
`|u|`, `‖Du‖` and `‖D²u‖` on the ball. -/
private theorem exists_holderOnWith_iteratedFDeriv_two_closedBall_half_of_mul_rpow_le
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {lam : ℝ} (hlam : 0 < lam) (Lam : ℝ) :
    ∃ c₀ : ℝ≥0, 0 < c₀ ∧ ∃ C : ℝ≥0,
      ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {x₀ : E} {δ Ka : ℝ≥0}, 0 < δ →
      Ka * δ ^ (α : ℝ) ≤ c₀ →
      (∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a x₀).toQuadraticForm' ξ) →
      (∀ ξ : E, (a x₀).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith Ka α (fun x => a x i j) (closedBall x₀ δ)) →
      (∀ x ∈ closedBall x₀ δ, ∀ i j, |a x i j| ≤ Lam) →
      ∀ {u : E → ℝ} {N₀ N₁ N₂ K V : ℝ≥0}, ContDiffOn ℝ 2 u (ball x₀ δ) →
        (∀ x ∈ ball x₀ δ, |u x| ≤ N₀) → (∀ x ∈ ball x₀ δ, ‖fderiv ℝ u x‖ ≤ N₁) →
        (∀ x ∈ ball x₀ δ, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N₂) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (ball x₀ δ) →
        HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) (ball x₀ δ) →
        HolderOnWith (C * (δ ^ 2 * (K * δ ^ (α : ℝ)) + (N₀ + δ * N₁ + δ ^ 2 * N₂)) *
          δ⁻¹ ^ 2 * δ⁻¹ ^ (α : ℝ)) α (iteratedFDeriv ℝ 2 u) (closedBall x₀ (δ / 2)) := by
  obtain ⟨C₀, -, hball⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv hα hα1 (n := n)
  -- The threshold `c₀` makes the scale condition of the small-ball estimate hold at radius `1`.
  set D : ℝ := 2 * (C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
    (1 + 2 ^ (α : ℝ))
  set c₀ : ℝ≥0 := ⟨lam / (|D| + 1), by positivity⟩
  have hc₀ : 2 * (C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
      ((1 + 2 ^ (α : ℝ)) * c₀ * (1 : ℝ) ^ (α : ℝ)) ≤ lam := by
    have hc : (c₀ : ℝ) = lam / (|D| + 1) := NNReal.coe_mk _ _
    have hD : (|D| + 1) * (c₀ : ℝ) = lam := by rw [hc]; field_simp
    calc _ = D * c₀ := by rw [Real.one_rpow, mul_one]; ring
      _ ≤ |D| * c₀ := mul_le_mul_of_nonneg_right (le_abs_self D) c₀.coe_nonneg
      _ ≤ lam := by nlinarith [c₀.coe_nonneg]
  obtain ⟨C₁, hC₁⟩ := hball (L := c₀) (M := Lam.toNNReal) hlam one_pos hc₀ (ρ := 1 / 2)
    (by norm_num)
  refine ⟨c₀, by rw [← NNReal.coe_pos]; exact div_pos hlam (by positivity), C₁, ?_⟩
  intro a x₀ δ Ka hδ hKa hlo hup hhol hent u N₀ N₁ N₂ K V hu hN₀ hN₁ hN₂ hV hK
  -- The dilation `e y = δ y` maps `B(x₁, ρ)` onto `B(x₀, δ ρ)`, where `x₁ = δ⁻¹ x₀`.
  have hδ' : (0 : ℝ) < δ := hδ
  set e : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 (δ : ℝ) hδ'.ne')
  have he : ∀ y, e y = (δ : ℝ) • y := fun y => by simp [e, Units.smul_def]
  have hnorm : ‖(e : E →L[ℝ] E)‖ ≤ δ :=
    ContinuousLinearMap.opNorm_le_bound _ δ.coe_nonneg fun y => by
      rw [ContinuousLinearEquiv.coe_coe, he, norm_smul, Real.norm_of_nonneg δ.coe_nonneg]
  have hnorms : ‖(e.symm : E →L[ℝ] E)‖₊ ≤ δ⁻¹ := by
    rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_inv]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
    rw [ContinuousLinearEquiv.coe_coe, show e.symm y = (δ : ℝ)⁻¹ • y by
      rw [e.symm_apply_eq, he, smul_inv_smul₀ hδ'.ne'], norm_smul,
      Real.norm_of_nonneg (by positivity)]
  set x₁ : E := (δ : ℝ)⁻¹ • x₀
  have hx₁ : e x₁ = x₀ := by rw [he, smul_inv_smul₀ hδ'.ne']
  have hdist : ∀ y z, dist (e y) (e z) = δ * dist y z := fun y z => by
    rw [he, he, dist_smul₀, Real.norm_of_nonneg δ.coe_nonneg]
  have hlip : LipschitzWith δ e := LipschitzWith.of_dist_le_mul fun y z => (hdist y z).le
  have hmB : MapsTo e (ball x₁ 1) (ball x₀ δ) := fun y hy => by
    rw [mem_ball, ← hx₁, hdist]
    rw [mem_ball] at hy
    nlinarith
  have hmC : MapsTo e (closedBall x₁ 1) (closedBall x₀ δ) := fun y hy => by
    rw [mem_closedBall, ← hx₁, hdist]
    rw [mem_closedBall] at hy
    nlinarith
  have hpre : e ⁻¹' closedBall x₀ (δ / 2) = closedBall x₁ (1 / 2) := by
    ext y
    rw [mem_preimage, mem_closedBall, mem_closedBall, ← hx₁, hdist]
    constructor <;> intro h <;> nlinarith
  -- The bounds for `v = u ∘ e`, which scale with `δ`.
  set Nv : ℝ≥0 := N₀ + δ * N₁ + δ ^ 2 * N₂
  have hNv : (N₀ : ℝ) ≤ Nv ∧ (δ : ℝ) * N₁ ≤ Nv ∧ (δ : ℝ) ^ 2 * N₂ ≤ Nv := by
    have h0 : (0 : ℝ) ≤ δ * N₁ := by positivity
    have h1 : (0 : ℝ) ≤ δ ^ 2 * N₂ := by positivity
    simp only [Nv, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow]
    exact ⟨by linarith [N₀.coe_nonneg], by linarith [N₀.coe_nonneg], by linarith [N₀.coe_nonneg]⟩
  have hb1 : ∀ y ∈ ball x₁ 1, ‖fderiv ℝ (u ∘ e) y‖ ≤ Nv := fun y hy => by
    rw [← norm_iteratedFDeriv_one]
    refine (e.norm_iteratedFDeriv_comp_right_le u y 1).trans ?_
    rw [pow_one, norm_iteratedFDeriv_one]
    exact (mul_le_mul hnorm (hN₁ _ (hmB hy)) (norm_nonneg _) δ.coe_nonneg).trans hNv.2.1
  have hb2 : ∀ y ∈ ball x₁ 1, ‖iteratedFDeriv ℝ 2 (u ∘ e) y‖ ≤ Nv := fun y hy => by
    refine (e.norm_iteratedFDeriv_comp_right_le u y 2).trans ?_
    exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (hN₂ _ (hmB hy))
      (norm_nonneg _) (by positivity)).trans hNv.2.2
  -- The Hessian of `v` is Hölder on `B(x₁, 1)`, with some constant.
  set Lm := ContinuousMultilinearMap.compContinuousLinearMapL (F := ℝ)
    fun _ : Fin 2 => (e : E →L[ℝ] E)
  have hVv := Lm.lipschitzWith.holderWith.comp_holderOnWith
    (hV.comp (hlip.holderWith.holderOnWith (ball x₁ 1)) hmB)
  rw [mul_one, one_mul] at hVv
  have hD2 : iteratedFDeriv ℝ 2 (u ∘ e) = Lm ∘ iteratedFDeriv ℝ 2 u ∘ e := by
    funext y
    simpa [Lm] using e.iteratedFDeriv_comp_right u y 2
  -- The operator applied to `v` is `δ²` times the operator applied to `u`, at `e y`.
  have hKv : HolderOnWith (δ ^ 2 * (K * δ ^ (α : ℝ))) α (fun y => ∑ i, ∑ j, a (e y) i j •
      fderiv ℝ (fderiv ℝ (u ∘ e)) y (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
      (ball x₁ 1) := by
    refine HolderOnWith.of_dist_le fun y hy z hz => ?_
    rw [sum_smul_fderiv_fderiv_comp_dilation e he (a (e y)) u y,
      sum_smul_fderiv_fderiv_comp_dilation e he (a (e z)) u z, Real.dist_eq, ← mul_sub, abs_mul,
      abs_of_nonneg (by positivity), ← Real.dist_eq]
    have h := hK.dist_le (hmB hy) (hmB hz)
    rw [hdist, Real.mul_rpow δ.coe_nonneg dist_nonneg] at h
    push_cast
    calc (δ : ℝ) ^ 2 * dist _ _ ≤ δ ^ 2 * (K * (δ ^ (α : ℝ) * dist y z ^ (α : ℝ))) := by gcongr
      _ = _ := by ring
  have hres := hC₁ (a := fun y => a (e y)) (x₀ := x₁) (by simpa only [hx₁] using hlo)
    (by simpa only [hx₁] using hup)
    (fun i j => by
      have h := (hhol i j).comp (hlip.holderWith.holderOnWith (closedBall x₁ 1)) hmC
      rw [mul_one] at h
      exact h.mono_const hKa)
    (fun y hy i j => (hent (e y) (hmC hy) i j).trans (Real.le_coe_toNNReal _))
    (u := u ∘ e) (N := Nv) (hu.comp e.contDiff.contDiffOn hmB)
    (fun y hy => (hN₀ (e y) (hmB hy)).trans hNv.1) hb1 hb2 (hD2 ▸ hVv) hKv
  -- Back to `u`: precompose with `e⁻¹`, which costs `δ^{-2-α}`.
  have hu' := e.holderOnWith_iteratedFDeriv_of_comp_right (s := closedBall x₀ (δ / 2))
    (by rw [hpre]; exact hres)
  refine hu'.mono_const ?_
  gcongr

/-- The arithmetic of one covering step: the constant of the estimate on a ball of radius `δ`,
with `‖Du‖` and `‖D²u‖` interpolated at scale `κ δ`, plus the contribution of points at distance
at least `δ / 2`. -/
private theorem covering_step_le {C₁ K Mu H δ κ α : ℝ} (hC₁ : 0 ≤ C₁)
    (hMu : 0 ≤ Mu) (hH : 0 ≤ H) (hδ : 0 < δ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) :
    C₁ * (δ ^ 2 * (K * δ ^ α) + (Mu + δ * (Mu / (κ * δ) + H * (κ * δ) ^ (1 + α)) +
        δ ^ 2 * (2 * Mu / (κ * δ) ^ 2 + 3 * H * (κ * δ) ^ α))) * δ⁻¹ ^ 2 * δ⁻¹ ^ α +
      2 * (2 * Mu / (κ * δ) ^ 2 + 3 * H * (κ * δ) ^ α) * (δ / 2) ^ (-α) ≤
    C₁ * K + (4 * C₁ + 8) * κ⁻¹ ^ 2 * δ ^ (-(2 + α)) * Mu + (4 * C₁ + 12) * κ ^ α * H := by
  have hq0 : 0 < δ ^ α := Real.rpow_pos_of_pos hδ α
  have hk0 : 0 ≤ κ ^ α := (Real.rpow_pos_of_pos hκ α).le
  have h2α : (2 : ℝ) ^ α ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα1
  have hkδ : (κ * δ) ^ α = κ ^ α * δ ^ α := Real.mul_rpow hκ.le hδ.le
  have hkδ1 : (κ * δ) ^ (1 + α) = κ * δ * (κ ^ α * δ ^ α) := by
    rw [Real.rpow_add' (by positivity) (by linarith), Real.rpow_one, hkδ]
  have hδinv : δ⁻¹ ^ α = (δ ^ α)⁻¹ := Real.inv_rpow hδ.le α
  have hδneg : δ ^ (-(2 + α)) = (δ ^ 2 * δ ^ α)⁻¹ := by
    rw [Real.rpow_neg hδ.le, Real.rpow_add hδ, Real.rpow_two]
  have hhalf : (δ / 2) ^ (-α) = 2 ^ α * (δ ^ α)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.div_rpow hδ.le (by norm_num), inv_div,
      div_eq_mul_inv]
  rw [hkδ, hkδ1, hδinv, hδneg, hhalf]
  -- With `Y = Mu / (κ² δ² δ^α)`, both sides are linear in `Y` and in `κ^α H`.
  set Y := Mu / (κ ^ 2 * δ ^ 2 * δ ^ α)
  have hY : 0 ≤ Y := by positivity
  have e1 : C₁ * (δ ^ 2 * (K * δ ^ α) + (Mu + δ * (Mu / (κ * δ) + H * (κ * δ * (κ ^ α * δ ^ α))) +
        δ ^ 2 * (2 * Mu / (κ * δ) ^ 2 + 3 * H * (κ ^ α * δ ^ α)))) * δ⁻¹ ^ 2 * (δ ^ α)⁻¹ +
      2 * (2 * Mu / (κ * δ) ^ 2 + 3 * H * (κ ^ α * δ ^ α)) * (2 ^ α * (δ ^ α)⁻¹) =
      C₁ * K + C₁ * κ ^ 2 * Y + C₁ * κ * Y + 2 * C₁ * Y + 4 * 2 ^ α * Y +
        C₁ * κ * (κ ^ α * H) + 3 * C₁ * (κ ^ α * H) + 6 * 2 ^ α * (κ ^ α * H) := by
    simp only [Y]
    field_simp
    ring
  have e2 : C₁ * K + (4 * C₁ + 8) * κ⁻¹ ^ 2 * (δ ^ 2 * δ ^ α)⁻¹ * Mu +
      (4 * C₁ + 12) * κ ^ α * H = C₁ * K + (4 * C₁ + 8) * Y + (4 * C₁ + 12) * (κ ^ α * H) := by
    simp only [Y]
    field_simp
  rw [e1, e2]
  have hkH : 0 ≤ κ ^ α * H := mul_nonneg hk0 hH
  have hκ2 : κ ^ 2 ≤ 1 := pow_le_one₀ hκ.le hκ1
  nlinarith [mul_nonneg (mul_nonneg hC₁ hY) (sub_nonneg.2 hκ2),
    mul_nonneg (mul_nonneg hC₁ hY) (sub_nonneg.2 hκ1), mul_nonneg hY (sub_nonneg.2 h2α),
    mul_nonneg (mul_nonneg hC₁ hkH) (sub_nonneg.2 hκ1), mul_nonneg hkH (sub_nonneg.2 h2α)]

/-- **One covering step.** There are a threshold `c₀ > 0` and a constant `C₁`, depending only on
`n`, `α`, `λ` and `Λ`, with the following property. Let `0 < κ ≤ 1 / 4` with
`(4 C₁ + 12) κ^α ≤ 1 / 2`, let `a` be uniformly elliptic and bounded on `ball x₀ R` with
entrywise Hölder constant `[a]_α`, and let `u` be `C²` on `ball x₀ R` with `|u| ≤ M_u` there and
`[L u]_α ≤ K`. If `s < t < R`, `[a]_α ((t - s) / 2)^α ≤ c₀` and `D²u` is `α`-Hölder on
`closedBall x₀ t` with constant `H`, then the Hölder constant of `D²u` on `closedBall x₀ s` is at
most `H / 2 + (4 C₁ + 8) κ⁻² 2^{2+α} M_u (t - s)^{-2-α} + C₁ K`.

The estimate on small balls is applied on the balls `B(y, δ)`, `δ = (t - s) / 2`, centred in
`closedBall x₀ s`, with `‖Du‖` and `‖D²u‖` interpolated at scale `κ δ`; points at distance at least
`δ / 2` are compared through the bound on `‖D²u‖`. -/
private theorem exists_nnHolderNorm_closedBall_le_of_lt
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {lam : ℝ} (hlam : 0 < lam) (Lam : ℝ) :
    ∃ c₀ : ℝ≥0, 0 < c₀ ∧ ∃ C₁ : ℝ≥0, ∀ {κ : ℝ}, 0 < κ → 4 * κ ≤ 1 →
      (4 * C₁ + 12) * κ ^ (α : ℝ) ≤ 1 / 2 →
      ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {x₀ : E} {R s t : ℝ}
        {Ka Mu K H : ℝ≥0} {u : E → ℝ}, UniformlyEllipticOn (ball x₀ R) a lam Lam →
      (∀ i j, HolderOnWith Ka α (fun x => a x i j) (ball x₀ R)) →
      ContDiffOn ℝ 2 u (ball x₀ R) → (∀ x ∈ ball x₀ R, |u x| ≤ Mu) →
      HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) (ball x₀ R) →
      s < t → t < R → Ka * ((t - s) / 2) ^ (α : ℝ) ≤ c₀ →
      HolderOnWith H α (iteratedFDeriv ℝ 2 u) (closedBall x₀ t) →
      (nnHolderNorm α ((closedBall x₀ s).domRestrict (iteratedFDeriv ℝ 2 u)) : ℝ) ≤
        1 / 2 * H + (4 * C₁ + 8) * κ⁻¹ ^ 2 * 2 ^ (2 + (α : ℝ)) * Mu *
          (t - s) ^ (-(2 + (α : ℝ))) + C₁ * K := by
  obtain ⟨c₀, hc₀, C₁, hC₁⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_closedBall_half_of_mul_rpow_le hα hα1 hlam Lam (n := n)
  refine ⟨c₀, hc₀, C₁, ?_⟩
  intro κ hκ hκ4 hκα a x₀ R s t Ka Mu K H u hA hKa hu hMu hK hst ht hscale hH
  set δ : ℝ≥0 := ⟨(t - s) / 2, by linarith⟩
  have hδ : (δ : ℝ) = (t - s) / 2 := NNReal.coe_mk _ _
  have hδ0 : 0 < δ := by rw [← NNReal.coe_pos, hδ]; linarith
  have hδ0' : (0 : ℝ) < δ := hδ0
  have hε : 0 < κ * δ := by positivity
  -- Points within `s + δ` of `x₀` have their `2 κ δ`-balls in `closedBall x₀ t`, where the
  -- local interpolation inequalities bound `‖Du‖` and `‖D²u‖`.
  have hint : ∀ z, dist z x₀ ≤ s + δ →
      ‖fderiv ℝ u z‖ ≤ Mu / (κ * δ) + H * (κ * δ) ^ (1 + (α : ℝ)) ∧
        ‖iteratedFDeriv ℝ 2 u z‖ ≤ 2 * Mu / (κ * δ) ^ 2 + 3 * H * (κ * δ) ^ (α : ℝ) :=
    fun z hz => by
      have hsub : closedBall z (2 * (κ * δ)) ⊆ closedBall x₀ t := fun w hw => by
        rw [mem_closedBall] at hw ⊢
        have : 2 * (κ * δ) ≤ δ / 2 := by nlinarith
        linarith [dist_triangle w z x₀]
      have hM' : ∀ y ∈ closedBall x₀ t, ‖u y‖ ≤ Mu := fun y hy => by
        rw [Real.norm_eq_abs]
        exact hMu y (closedBall_subset_ball ht hy)
      exact ⟨hH.norm_fderiv_le_of_contDiffOn isOpen_ball hu (closedBall_subset_ball ht) hM' hε
        ((closedBall_subset_closedBall (by linarith)).trans hsub),
        hH.norm_iteratedFDeriv_two_le_of_contDiffOn isOpen_ball hu (closedBall_subset_ball ht)
          hM' hε hsub⟩
  set N₁ : ℝ≥0 := (Mu / (κ * δ) + H * (κ * δ) ^ (1 + (α : ℝ))).toNNReal
  set N₂ : ℝ≥0 := (2 * Mu / (κ * δ) ^ 2 + 3 * H * (κ * δ) ^ (α : ℝ)).toNNReal
  have hN₁ : (N₁ : ℝ) = Mu / (κ * δ) + H * (κ * δ) ^ (1 + (α : ℝ)) :=
    Real.coe_toNNReal _ (by positivity)
  have hN₂ : (N₂ : ℝ) = 2 * Mu / (κ * δ) ^ 2 + 3 * H * (κ * δ) ^ (α : ℝ) :=
    Real.coe_toNNReal _ (by positivity)
  have hscale' : Ka * δ ^ (α : ℝ) ≤ c₀ := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rwa [hδ]
  -- The estimate on small balls on `closedBall y (δ / 2)`, for each `y ∈ closedBall x₀ s`.
  have hloc : ∀ y ∈ closedBall x₀ s, HolderOnWith (C₁ * (δ ^ 2 * (K * δ ^ (α : ℝ)) +
      (Mu + δ * N₁ + δ ^ 2 * N₂)) * δ⁻¹ ^ 2 * δ⁻¹ ^ (α : ℝ)) α (iteratedFDeriv ℝ 2 u)
      (closedBall y (δ / 2)) := fun y hy => by
    have hy' : dist y x₀ ≤ s := hy
    have hCB : closedBall y δ ⊆ ball x₀ R := fun w hw => by
      rw [mem_ball]
      rw [mem_closedBall] at hw
      linarith [dist_triangle w y x₀]
    have hB : ball y δ ⊆ closedBall x₀ t := fun w hw => by
      rw [mem_closedBall]
      rw [mem_ball] at hw
      linarith [dist_triangle w y x₀]
    have hBs : ∀ w ∈ ball y δ, dist w x₀ ≤ s + δ := fun w hw => by
      rw [mem_ball] at hw
      linarith [dist_triangle w y x₀]
    have hyB : y ∈ ball x₀ R := hCB (mem_closedBall_self δ.coe_nonneg)
    exact hC₁ hδ0 hscale' (hA.lower_bound hyB) (hA.toQuadraticForm'_le hyB)
      (fun i j => (hKa i j).mono hCB) (fun w hw i j => hA.abs_apply_le (hCB hw) i j)
      (hu.mono (ball_subset_closedBall.trans hCB))
      (fun w hw => hMu w (hCB (ball_subset_closedBall hw)))
      (fun w hw => hN₁ ▸ (hint w (hBs w hw)).1) (fun w hw => hN₂ ▸ (hint w (hBs w hw)).2)
      (hH.mono hB) (hK.mono (ball_subset_closedBall.trans hCB))
  -- Distant points are compared through the bound on `‖D²u‖`.
  have hfar : ∀ x ∈ closedBall x₀ s, ∀ y ∈ closedBall x₀ s,
      dist (iteratedFDeriv ℝ 2 u x) (iteratedFDeriv ℝ 2 u y) ≤ ((2 * N₂ : ℝ≥0) : ℝ) :=
    fun x hx y hy => by
      refine (dist_le_norm_add_norm _ _).trans ?_
      have h1 := (hint x (by linarith [mem_closedBall.1 hx])).2
      have h2 := (hint y (by linarith [mem_closedBall.1 hy])).2
      push_cast
      rw [hN₂]
      linarith
  have hcov := HolderOnWith.of_dist_lt_of_dist_le (half_pos hδ0)
    (fun x hx y hy hxy => (hloc x hx).dist_le (mem_closedBall_self (by positivity))
      (by rw [mem_closedBall, dist_comm]; exact_mod_cast hxy.le)) hfar
  have hΦs := NNReal.coe_le_coe.2 hcov.holderWith.nnholderNorm_le
  push_cast at hΦs
  rw [hN₁, hN₂] at hΦs
  have harith := covering_step_le (K := K) (H := H) C₁.coe_nonneg Mu.coe_nonneg H.coe_nonneg
    hδ0' hκ (by linarith) α.coe_nonneg hα1.le
  -- `(4 C₁ + 12) κ^α ≤ 1 / 2` and `δ^{-2-α} = 2^{2+α} (t - s)^{-2-α}`.
  have hδp : (δ : ℝ) ^ (-(2 + (α : ℝ))) = 2 ^ (2 + (α : ℝ)) * (t - s) ^ (-(2 + (α : ℝ))) := by
    rw [hδ, Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_inv_eq_mul, mul_comm]
  have hH0 : (0 : ℝ) ≤ H := H.coe_nonneg
  calc _ ≤ C₁ * K + (4 * C₁ + 8) * κ⁻¹ ^ 2 * δ ^ (-(2 + (α : ℝ))) * Mu +
        (4 * C₁ + 12) * κ ^ (α : ℝ) * H := hΦs.trans harith
    _ ≤ C₁ * K + (4 * C₁ + 8) * κ⁻¹ ^ 2 * δ ^ (-(2 + (α : ℝ))) * Mu + 1 / 2 * H := by
        gcongr
    _ = _ := by
        rw [hδp]
        ring

/-- **The interior Schauder estimate in scaled form.** Let `0 < α < 1`, and let `λ`, `Λ` and `M`
be given. Then there is a constant `C ≥ 0`, depending only on `n`, `α`, `λ`, `Λ` and `M`, with the
following property. Let `r > 0`, let `a` be a matrix-valued coefficient which is uniformly elliptic
and bounded with constants `0 < λ ≤ Λ` on `B_{2r} = ball x₀ (2 r)` and `α`-Hölder there entrywise
with constant `[a]_α`, where `r^α [a]_α ≤ M`, and put `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu`. Let `u` be `C²` on
`B_{2r}` with `|u| ≤ M_u` there, and with `D²u` `α`-Hölder on `closedBall x₀ ρ` for every `ρ < 2 r`
(with any constants). If `L u` is `α`-Hölder on `B_{2r}` with constant `K`, then `D²u` is
`α`-Hölder on `closedBall x₀ r` with constant `C (r^{-2-α} M_u + K)`.

The constant is independent of `r`, `x₀`, `u` and of the qualitative Hölder constants of `D²u`
(Gilbarg–Trudinger, Theorem 6.2). -/
theorem exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv_of_mul_rpow_le
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) (lam Lam : ℝ) (M : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {x₀ : E} {r : ℝ}
      {Ka Mu K : ℝ≥0} {u : E → ℝ}, 0 < r → UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam →
      (∀ i j, HolderOnWith Ka α (fun x => a x i j) (ball x₀ (2 * r))) →
      Ka * r ^ (α : ℝ) ≤ M → ContDiffOn ℝ 2 u (ball x₀ (2 * r)) →
      (∀ x ∈ ball x₀ (2 * r), |u x| ≤ Mu) →
      (∀ ρ < 2 * r, ∃ V : ℝ≥0, HolderOnWith V α (iteratedFDeriv ℝ 2 u) (closedBall x₀ ρ)) →
      HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) (ball x₀ (2 * r)) →
      HolderOnWith (C * (r ^ (-(2 + (α : ℝ))) * Mu + K)).toNNReal α
        (iteratedFDeriv ℝ 2 u) (closedBall x₀ r) := by
  -- Without `0 < λ` no coefficient field is uniformly elliptic.
  rcases le_or_gt lam 0 with hlam | hlam
  · exact ⟨0, le_rfl, fun _ hA => absurd hA.pos (not_lt.2 hlam)⟩
  obtain ⟨c₀, hc₀, C₁, hstep₀⟩ := exists_nnHolderNorm_closedBall_le_of_lt hα hα1 hlam Lam (n := n)
  have hα' : (0 : ℝ) < α := hα
  -- The relative radius `θ` below which the estimate on small balls applies, and the ratio `κ`
  -- of the interpolation scale to the radius, small enough to absorb the Hölder constant.
  obtain ⟨θ₀, hθ₀, hθ₀1, hθ₀M⟩ :=
    Real.exists_pos_le_one_mul_rpow_le (M : ℝ) hα' (NNReal.coe_pos.2 hc₀)
  obtain ⟨κ₀, hκ₀, hκ₀1, hκ₀C⟩ :=
    Real.exists_pos_le_one_mul_rpow_le (4 * C₁ + 12) hα' (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨C₃, hC₃, habs⟩ := exists_le_mul_mul_rpow_add_of_le_mul_add (θ := 1 / 2)
    (by norm_num) (by norm_num) (2 + (α : ℝ))
  set θ := θ₀ / 4
  set κ := κ₀ / 4
  set A₀ : ℝ := (4 * C₁ + 8) * κ⁻¹ ^ 2 * 2 ^ (2 + (α : ℝ))
  have hθ : 0 < θ := by positivity
  have hκ : 0 < κ := by positivity
  have hA₀ : 0 ≤ A₀ := by positivity
  refine ⟨C₃ * (A₀ * (2 * θ) ^ (-(2 + (α : ℝ))) + C₁), by positivity, ?_⟩
  intro a x₀ r Ka Mu K u hr hA hKa hKaM hu hMu hV hK
  set r₁ := r + 2 * θ * r
  have hr₁ : r₁ < 2 * r := by simp only [r₁, θ]; nlinarith
  have hrr₁ : r < r₁ := by simp only [r₁]; nlinarith
  -- `ΦN s` is the Hölder constant of `D²u` on `closedBall x₀ s`.
  set ΦN : ℝ → ℝ≥0 := fun s => nnHolderNorm α ((closedBall x₀ s).domRestrict (iteratedFDeriv ℝ 2 u))
  have hΦhol : ∀ s < 2 * r, HolderOnWith (ΦN s) α (iteratedFDeriv ℝ 2 u) (closedBall x₀ s) :=
    fun s hs => by
      obtain ⟨V, hV'⟩ := hV s hs
      exact HolderWith.restrict_iff.1 hV'.holderWith.memHolder.holderWith
  have hΦle : ∀ s (V : ℝ≥0), HolderOnWith V α (iteratedFDeriv ℝ 2 u) (closedBall x₀ s) →
      (ΦN s : ℝ) ≤ V := fun s V h => NNReal.coe_le_coe.2 h.holderWith.nnholderNorm_le
  set A : ℝ := A₀ * Mu
  -- The covering step: `Φ(s) ≤ Φ(t) / 2 + A (t - s)^{-2-α} + C₁ K` for `r ≤ s < t ≤ r₁`.
  have hstep : ∀ s t, r ≤ s → s < t → t ≤ r₁ →
      (ΦN s : ℝ) ≤ 1 / 2 * ΦN t + A * (t - s) ^ (-(2 + (α : ℝ))) + C₁ * K := by
    intro s t hrs hst ht
    have ht2 : t < 2 * r := ht.trans_lt hr₁
    -- The scale condition holds at radius `(t - s) / 2 ≤ θ₀ r`.
    have hscale : (Ka : ℝ) * ((t - s) / 2) ^ (α : ℝ) ≤ c₀ := by
      have hδθ : (t - s) / 2 ≤ θ₀ * r := by simp only [r₁, θ] at ht; nlinarith
      calc (Ka : ℝ) * ((t - s) / 2) ^ (α : ℝ) ≤ Ka * (θ₀ * r) ^ (α : ℝ) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hδθ α.coe_nonneg)
              Ka.coe_nonneg
        _ = θ₀ ^ (α : ℝ) * (Ka * r ^ (α : ℝ)) := by rw [Real.mul_rpow hθ₀.le hr.le]; ring
        _ ≤ θ₀ ^ (α : ℝ) * M := by gcongr
        _ ≤ c₀ := by linarith
    have hκα : (4 * C₁ + 12) * κ ^ (α : ℝ) ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hκ.le (by simp only [κ]; linarith)
        α.coe_nonneg) (by positivity)).trans hκ₀C
    exact hstep₀ hκ (by simp only [κ]; linarith) hκα hA hKa hu hMu hK hst ht2 hscale
      (hΦhol t ht2)
  -- The absorption lemma on `[r, r₁]`, where `r₁ - r = 2 θ r`.
  have hbdd : BddAbove ((fun s => (ΦN s : ℝ)) '' Icc r r₁) := by
    refine ⟨ΦN r₁, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact hΦle s _ ((hΦhol r₁ hr₁).mono (closedBall_subset_closedBall hs.2))
  have hΦr := habs (f := fun s => (ΦN s : ℝ)) hrr₁ (by positivity) (by positivity) hbdd hstep
  have hr₁r : r₁ - r = 2 * θ * r := by simp only [r₁]; ring
  rw [hr₁r, Real.mul_rpow (by positivity) hr.le] at hΦr
  refine (hΦhol r (by linarith)).mono_const ?_
  rw [Real.le_toNNReal_iff_coe_le (by positivity)]
  have hp : 0 ≤ (2 * θ) ^ (-(2 + (α : ℝ))) := by positivity
  have hrp : 0 ≤ r ^ (-(2 + (α : ℝ))) := by positivity
  refine hΦr.trans ?_
  simp only [A]
  have h1 : 0 ≤ (C₃ : ℝ) * (A₀ * (2 * θ) ^ (-(2 + (α : ℝ))) * K) := by positivity
  have h2 : 0 ≤ (C₃ : ℝ) * (C₁ * (r ^ (-(2 + (α : ℝ))) * Mu)) := by positivity
  nlinarith

end TauCeti.PDE
