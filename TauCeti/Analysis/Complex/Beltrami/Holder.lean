/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Holder.Operator
public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.Holder.Bilinear
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.MetricSpace.Contracting
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Topology.MetricSpace.Holder

/-!
# The Beltrami equation with small Hölder coefficient

Let `0 < α < 1` and let `μ` be a bounded `α`-Hölder function on `ℂ` vanishing off the closed disc
`closedBall c r`. This file solves the Beltrami equation `\bar∂ψ = μ ∂ψ` near the disc when the
Hölder norm `‖μ‖ = ‖μ‖_∞ + [μ]_α` is small, with a solution `C¹`-close to the identity.

The solution is `ψ = z + T h`, where `T h(w) = π⁻¹ ∫ (w - z)⁻¹ h(z) dz` is the Cauchy transform
of a source `h` supported in the disc. Since `\bar∂ T h = h` and `∂ T h = B h` for the Beurling
operator `B = ∂ T`, the Beltrami equation for `ψ` is the fixed-point equation
`h = μ (1 + B h)` for its source. On the Banach space of `α`-Hölder functions supported in the
disc, `B` is bounded with values in the Hölder functions on the disc
(`TauCeti.cauchyDerivativeCLM`), and multiplying by `μ` and extending by zero has operator norm
at most `‖μ‖` (`ContinuousLinearMap.compHolder₂ExtendByZero`). So the map
`h ↦ μ (1 + B h)` is a contraction for small `‖μ‖`, and its fixed point gives the solution.

The derivative of `ψ` differs from the identity by `D (T h)`, whose Hölder norm on the disc is
at most a fixed multiple of `‖μ‖`. For small `‖μ‖` the derivative of `ψ` at each point of the
disc is therefore invertible, so `ψ` is a local diffeomorphism there by the inverse function
theorem (`HasStrictFDerivAt.toOpenPartialHomeomorph`).

This is the contraction step in the construction of isothermal coordinates for a Hölder almost
complex structure on a surface, after the Beltrami coefficient has been made small by rescaling.

## Main results

* `TauCeti.exists_conjWirtingerDeriv_eq_mul_wirtingerDeriv`: for `‖μ‖` below a threshold
  depending only on `α`, `c` and `r`, there is a source `h` supported in the disc with
  `‖h‖ ≤ 2 ‖μ‖` such that `ψ = z + T h` is `C¹` on `ball c (r + 1)`, solves `\bar∂ψ = μ ∂ψ` there,
  has derivative within `C ‖μ‖` of the identity at every point of the disc, with `α`-Hölder
  constant at most `C ‖μ‖` there, and has an invertible strict derivative at every point of the
  disc.

## References

* L. V. Ahlfors, *Lectures on Quasiconformal Mappings*, 2nd ed., AMS University Lecture Series
  **38**, 2006, Chapter V (the Beltrami equation solved by a fixed point of `h = μ (1 + B h)`).
* I. N. Vekua, *Generalized Analytic Functions*, Pergamon, 1962, Chapters I–II (the Cauchy and
  Beurling operators on Hölder spaces).
-/

public noncomputable section

open Complex Metric
open scoped NNReal

namespace TauCeti

variable {α : ℝ≥0} {c : ℂ} {r : ℝ}

/-- `(L, a) ↦ ½ (L 1 - i L i) · a`, which sends the real derivative of `f` at `z` and `a` to
`∂f(z) · a`. -/
private def beltramiPairing : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ).comp
    ((2 : ℂ)⁻¹ • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) - I • ContinuousLinearMap.apply ℝ ℂ I))

/-- The linear part `h ↦ μ ∂ T h` of the Beltrami fixed-point map, on sources supported in the
disc. -/
private def beltramiOperator (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r)
    (μ : supportedHolderSubmodule (Y := ℂ) α (closedBall c r)) :
    supportedHolderSubmodule (Y := ℂ) α (closedBall c r) →L[ℝ]
      supportedHolderSubmodule (Y := ℂ) α (closedBall c r) :=
  (beltramiPairing.compHolder₂ExtendByZero μ).comp (cauchyDerivativeCLM hα hα1 hr hr)

private theorem beltramiOperator_apply_of_mem (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r)
    (μ h : supportedHolderSubmodule (Y := ℂ) α (closedBall c r)) {z : ℂ}
    (hz : z ∈ closedBall c r) :
    (beltramiOperator hα hα1 hr μ h : HolderSpace α ℂ ℂ) z =
      wirtingerDeriv (fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ x, (w - x)⁻¹ • (h : HolderSpace α ℂ ℂ) x) z 1 *
        (μ : HolderSpace α ℂ ℂ) z := by
  simp [beltramiOperator, ContinuousLinearMap.compHolder₂ExtendByZero_apply_of_mem _ _ _ hz,
    beltramiPairing, wirtingerDeriv_apply]

private theorem norm_beltramiOperator_le (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r)
    (μ : supportedHolderSubmodule (Y := ℂ) α (closedBall c r)) :
    ‖beltramiOperator hα hα1 hr μ‖ ≤
      ‖beltramiPairing‖ * ‖μ‖ * ‖cauchyDerivativeCLM (F := ℂ) (c := c) hα hα1 hr hr‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans <| by
    gcongr
    exact ContinuousLinearMap.norm_compHolder₂ExtendByZero_le _ _

/-- The source of the Beltrami solution: the fixed point of the contraction `k ↦ μ + μ ∂ T k`
when its linear part has norm at most `1 / 4`, with the bound `‖k‖ ≤ 2 ‖μ‖`. -/
private theorem exists_add_beltramiOperator_eq (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r)
    (μ : supportedHolderSubmodule (Y := ℂ) α (closedBall c r))
    (hA : ‖beltramiOperator hα hα1 hr μ‖ ≤ 4⁻¹) :
    ∃ k, μ + beltramiOperator hα hα1 hr μ k = k ∧ ‖k‖ ≤ 2 * ‖μ‖ := by
  set A := beltramiOperator hα hα1 hr μ
  have hK : ‖A‖₊ < 1 := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
    linarith
  have hΦ : ContractingWith ‖A‖₊ fun k ↦ μ + A k :=
    ⟨hK, LipschitzWith.of_dist_le_mul fun k₁ k₂ ↦ by
      rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← map_sub, coe_nnnorm]
      exact A.le_opNorm _⟩
  set k := ContractingWith.fixedPoint _ hΦ
  have hfix : μ + A k = k := ContractingWith.fixedPoint_isFixedPt hΦ
  refine ⟨k, hfix, ?_⟩
  have hk : ‖k‖ ≤ ‖μ‖ + 4⁻¹ * ‖k‖ := by
    calc ‖k‖ = ‖μ + A k‖ := by rw [hfix]
      _ ≤ ‖μ‖ + ‖A‖ * ‖k‖ := (norm_add_le _ _).trans (by gcongr; exact A.le_opNorm k)
      _ ≤ ‖μ‖ + 4⁻¹ * ‖k‖ := by gcongr
  linarith [norm_nonneg μ]

/-- Regularity of `T h` for a source supported in the disc: it is `C¹` on `ball c (r + 1)` with
`\bar∂ T h = h` there, and on the disc its real derivative is the bounded derivative operator
applied to `h`. -/
private theorem cauchy_regularity (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r)
    (h : supportedHolderSubmodule (Y := ℂ) α (closedBall c r)) :
    let T : ℂ → ℂ := fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • (h : HolderSpace α ℂ ℂ) z
    ContDiffOn ℝ 1 T (ball c (r + 1)) ∧
      (∀ z ∈ ball c (r + 1), conjWirtingerDeriv T z 1 = (h : HolderSpace α ℂ ℂ) z) ∧
      ∀ z (hz : z ∈ closedBall c r), fderiv ℝ T z = cauchyDerivativeCLM hα hα1 hr hr h ⟨z, hz⟩ := by
  obtain ⟨C₀, hC₀⟩ :=
    exists_contDiffOn_holderOnWith_fderiv_pi_inv_smul_integral_sub_inv_smul (F := ℂ) hα hα1 c hr hr
  obtain ⟨hTC, -, -, hTbar⟩ := hC₀ (f := (h : HolderSpace α ℂ ℂ))
    (M := ‖(h : HolderSpace α ℂ ℂ).toBoundedContinuousFunction‖₊)
    (support_subset_of_mem_supportedHolderSubmodule h.2) (h : HolderSpace α ℂ ℂ).holderWith
    (fun z ↦ by simpa using (h : HolderSpace α ℂ ℂ).toBoundedContinuousFunction.norm_coe_le_norm z)
  exact ⟨hTC, hTbar, fun z hz ↦ (cauchyDerivativeCLM_apply hα hα1 hr hr h ⟨z, hz⟩).symm⟩

/-- If the real derivative of `ψ` on the disc is the identity plus the bounded derivative operator
`D` applied to a source `h`, then it is `α`-Hölder there with constant `‖D h‖`. -/
private theorem holderOnWith_fderiv_of_eq_id_add (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r)
    (h : supportedHolderSubmodule (Y := ℂ) α (closedBall c r)) {ψ : ℂ → ℂ}
    (hψ : ∀ z (hz : z ∈ closedBall c r),
      fderiv ℝ ψ z = ContinuousLinearMap.id ℝ ℂ + cauchyDerivativeCLM hα hα1 hr hr h ⟨z, hz⟩) :
    HolderOnWith ‖cauchyDerivativeCLM hα hα1 hr hr h‖₊ α (fderiv ℝ ψ) (closedBall c r) := by
  set Dh := cauchyDerivativeCLM hα hα1 hr hr h
  refine HolderOnWith.of_dist_le fun x hx y hy ↦ ?_
  rw [hψ x hx, hψ y hy, dist_add_left]
  refine (Dh.holderWith.dist_le ⟨x, hx⟩ ⟨y, hy⟩).trans ?_
  gcongr
  · rw [← NNReal.coe_le_coe]
    have hn := Dh.nnHolderNorm_le
    simp only [HolderSpace.coe_toBoundedContinuousFunction] at hn
    exact_mod_cast hn
  · exact (Subtype.dist_eq _ _).le

/-- **The Beltrami equation with small Hölder coefficient.** Let `0 < α < 1`. There are `δ > 0`
and `C` such that every bounded `α`-Hölder function `μ` vanishing off `closedBall c r` with
`‖μ‖ < δ` admits a source `h`, vanishing off the disc with `‖h‖ ≤ 2 ‖μ‖`, for which
`ψ(w) = w + π⁻¹ ∫ (w - z)⁻¹ h(z) dz`

* is `C¹` on `ball c (r + 1)`, with `\bar∂ψ = h` there;
* solves the Beltrami equation `\bar∂ψ = μ ∂ψ` on `ball c (r + 1)`;
* has real derivative within `C ‖μ‖` of the identity at every point of the disc, with
  `α`-Hölder constant at most `C ‖μ‖` there;
* has an invertible strict derivative at every point of the disc, so it is a local
  diffeomorphism near each such point. -/
theorem exists_conjWirtingerDeriv_eq_mul_wirtingerDeriv (hα : 0 < α) (hα1 : α < 1) (c : ℂ)
    (hr : 0 ≤ r) :
    ∃ δ > 0, ∃ C : ℝ≥0, ∀ μ ∈ supportedHolderSubmodule (Y := ℂ) α (closedBall c r), ‖μ‖ < δ →
      ∃ h ∈ supportedHolderSubmodule (Y := ℂ) α (closedBall c r), ‖h‖ ≤ 2 * ‖μ‖ ∧
        let ψ : ℂ → ℂ := fun w ↦ w + (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • h z
        ContDiffOn ℝ 1 ψ (ball c (r + 1)) ∧
        (∀ z ∈ ball c (r + 1), conjWirtingerDeriv ψ z 1 = h z) ∧
        (∀ z ∈ ball c (r + 1), conjWirtingerDeriv ψ z 1 = μ z * wirtingerDeriv ψ z 1) ∧
        (∀ z ∈ closedBall c r, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ C * ‖μ‖) ∧
        HolderOnWith (C * ‖μ‖₊) α (fderiv ℝ ψ) (closedBall c r) ∧
        ∀ z ∈ closedBall c r, ∃ L : ℂ ≃L[ℝ] ℂ, HasStrictFDerivAt ψ (L : ℂ →L[ℝ] ℂ) z := by
  set D := cauchyDerivativeCLM (F := ℂ) (c := c) hα hα1 hr hr
  set b := ‖beltramiPairing‖
  have hb : 0 ≤ b := beltramiPairing.opNorm_nonneg
  have hD : 0 ≤ ‖D‖ := D.opNorm_nonneg
  refine ⟨(4 * (b * ‖D‖ + ‖D‖ + 1))⁻¹, by positivity, 2 * ‖D‖₊, fun μ hμ hμδ ↦ ?_⟩
  have hδ : 4 * (b * ‖D‖ + ‖D‖ + 1) * ‖μ‖ < 1 := by
    have hpos : 0 < 4 * (b * ‖D‖ + ‖D‖ + 1) := by positivity
    calc 4 * (b * ‖D‖ + ‖D‖ + 1) * ‖μ‖
        < 4 * (b * ‖D‖ + ‖D‖ + 1) * (4 * (b * ‖D‖ + ‖D‖ + 1))⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hpos.ne'
  -- The source `h` is the fixed point of `k ↦ μ + μ ∂ T k`.
  set μ' : supportedHolderSubmodule (Y := ℂ) α (closedBall c r) := ⟨μ, hμ⟩
  have hμ' : ‖μ'‖ = ‖μ‖ := (Submodule.norm_coe μ').symm
  have hA : ‖beltramiOperator hα hα1 hr μ'‖ ≤ 4⁻¹ := by
    refine (norm_beltramiOperator_le hα hα1 hr μ').trans ?_
    rw [hμ']
    nlinarith [norm_nonneg μ, mul_nonneg hD (norm_nonneg μ)]
  obtain ⟨h, hfix, hh⟩ := exists_add_beltramiOperator_eq hα hα1 hr μ' hA
  rw [hμ'] at hh
  obtain ⟨hTC, hTbar, hDT⟩ := cauchy_regularity hα hα1 hr h
  set T : ℂ → ℂ := fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • (h : HolderSpace α ℂ ℂ) z
  have hsub : closedBall c r ⊆ ball c (r + 1) := closedBall_subset_ball (by linarith)
  have hTd : ∀ z ∈ ball c (r + 1), DifferentiableAt ℝ T z := fun z hz ↦
    (hTC.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt one_ne_zero
  -- The fixed-point equation, pointwise on the disc.
  have hpt : ∀ z ∈ closedBall c r,
      (h : HolderSpace α ℂ ℂ) z = μ z * (1 + wirtingerDeriv T z 1) := fun z hz ↦ by
    have := congrArg (fun k : supportedHolderSubmodule (Y := ℂ) α (closedBall c r) ↦
      (k : HolderSpace α ℂ ℂ) z) hfix
    simp only [Submodule.coe_add, HolderSpace.add_apply,
      beltramiOperator_apply_of_mem hα hα1 hr _ _ hz] at this
    rw [← this]
    ring
  -- On the disc, `D ψ - id = D T` is controlled by `‖D h‖ ≤ 2 ‖D‖ ‖μ‖`.
  have hDh : ‖D h‖ ≤ 2 * ‖D‖ * ‖μ‖ := by
    calc ‖D h‖ ≤ ‖D‖ * ‖h‖ := D.le_opNorm h
      _ ≤ ‖D‖ * (2 * ‖μ‖) := by gcongr
      _ = 2 * ‖D‖ * ‖μ‖ := by ring
  have hDT' : ∀ z ∈ closedBall c r, ‖fderiv ℝ T z‖ ≤ 2 * ‖D‖ * ‖μ‖ := fun z hz ↦ by
    rw [hDT z hz]
    exact ((D h).norm_apply_le _).trans hDh
  -- On `ball c (r + 1)`, `ψ = id + T` has real derivative `id + D T`.
  have hψT : (fun w ↦ w + T w) = id + T := rfl
  have hψ : ∀ z ∈ ball c (r + 1),
      HasFDerivAt (id + T) (ContinuousLinearMap.id ℝ ℂ + fderiv ℝ T z) z := fun z hz ↦
    (hasFDerivAt_id z).add (hTd z hz).hasFDerivAt
  have hψbar : ∀ z ∈ ball c (r + 1), conjWirtingerDeriv (id + T) z 1 = (h : HolderSpace α ℂ ℂ) z :=
    fun z hz ↦ by
      rw [conjWirtingerDeriv_add differentiableAt_id (hTd z hz), conjWirtingerDeriv_id, zero_add]
      exact hTbar z hz
  refine ⟨h, h.2, hh, contDiffOn_id.add hTC, hψbar, fun z hz ↦ ?_, fun z hz ↦ ?_,
    ?_, fun z hz ↦ ?_⟩
  · rw [hψT, hψbar z hz,
      wirtingerDeriv_add differentiableAt_id (hTd z hz), wirtingerDeriv_id]
    by_cases hz' : z ∈ closedBall c r
    · exact hpt z hz'
    · rw [mem_supportedHolderSubmodule_iff.mp h.2 z hz',
        mem_supportedHolderSubmodule_iff.mp hμ z hz', zero_mul]
  · rw [hψT, (hψ z (hsub hz)).fderiv, add_sub_cancel_left]
    push_cast
    exact hDT' z hz
  · refine (holderOnWith_fderiv_of_eq_id_add hα hα1 hr h fun z hz ↦ ?_).mono_const ?_
    · rw [hψT, (hψ z (hsub hz)).fderiv, hDT z hz]
    · rw [← NNReal.coe_le_coe]
      push_cast
      linarith
  · -- `D ψ(z) = id + D T(z)` is a small perturbation of the identity, so it is invertible.
    have hlt : ‖fderiv ℝ T z‖₊ < ‖((ContinuousLinearEquiv.refl ℝ ℂ).symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ := by
      rw [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
        ContinuousLinearMap.nnnorm_id, inv_one, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
      refine (hDT' z hz).trans_lt ?_
      nlinarith [norm_nonneg μ, mul_nonneg hb (mul_nonneg hD (norm_nonneg μ))]
    obtain ⟨L, hL⟩ := ContinuousLinearMap.isInvertible_of_norm_sub_lt
      (ContinuousLinearEquiv.refl ℝ ℂ) (A := ContinuousLinearMap.id ℝ ℂ + fderiv ℝ T z)
      (by rwa [ContinuousLinearEquiv.coe_refl, add_sub_cancel_left])
    refine ⟨L, ?_⟩
    rw [hL]
    exact (contDiffAt_id.add (hTC.contDiffAt (isOpen_ball.mem_nhds (hsub hz)))).hasStrictFDerivAt
      (hψ z (hsub hz)) one_ne_zero

end TauCeti
