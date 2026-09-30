/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
public import TauCeti.Analysis.Calculus.FDeriv.BoundedContinuousFunction
public import TauCeti.Analysis.ODE.LyapunovPerron.Graph
public import TauCeti.Analysis.ODE.LyapunovPerron.Linear

/-!
# Continuous differentiability of Lyapunov--Perron solutions

Let `A` and `P` be bounded operators on a real Banach space `X` with the forward and backward
exponential estimates of `TauCeti.Analysis.ODE.LyapunovPerron.Basic`, with constant `K` and rate
`α`, and let `N` be globally `ε`-Lipschitz with `2 K ε < α`. The Lyapunov--Perron solution
`lyapunovPerronSolution ξ` is the unique fixed point of the Lyapunov--Perron operator

`γ ↦ (t ↦ exp (t A) (P ξ)) + L (N ∘ γ)`,

where `L` is the Lyapunov--Perron integral `ContinuousLinearMap.lyapunovPerronIntegralCLM`, of
operator norm at most `2 K / α`. The solution depends Lipschitz-continuously on `ξ`
(`ContinuousLinearMap.lipschitzWith_lyapunovPerronSolution`). This file shows that it depends
**continuously differentiably** on `ξ` wherever `N` is
continuously differentiable along the solution, in the uniform sense of
`BoundedContinuousFunction.contDiffAt_comp`: `N` has a derivative `N' x` at every point `x` of a
set `s`, `N'` is uniformly continuous on `s`, and the values of the solution stay a fixed
distance `δ > 0` inside `s`.

The proof is the implicit function theorem applied to
`(ξ, γ) ↦ γ - (t ↦ exp (t A) (P ξ)) - L (N ∘ γ)`. This map is `C¹` because the superposition
operator `γ ↦ N ∘ γ` is. Its partial derivative in `γ` is `1 - L ∘ N'(γ)`. Since `N` is
`ε`-Lipschitz, every `N' x` has norm at most `ε`, so `L ∘ N'(γ)` has norm at most
`2 K ε / α < 1` and the partial derivative is invertible by the Neumann series. Continuity of the
solution in `ξ` identifies it with the implicit function near `ξ`.

Differentiating the fixed-point equation gives the *variational equation*: the derivative in the
direction `v` is the bounded solution of the Lyapunov--Perron equation of the linearization
`z' = A z + N' (y t) z` along the solution `y` with input parameter `v`
(`ContinuousLinearMap.fderiv_lyapunovPerronSolution_apply`), and it is the only such solution
(`ContinuousLinearMap.eq_fderiv_lyapunovPerronSolution_apply`).

Evaluating at time `0`, the Lyapunov--Perron graph map is `C¹` as well. The local stable and
unstable graph maps of `TauCeti.Analysis.ODE.LyapunovPerron.Local` cut the nonlinearity off
outside a ball; the cutoff is invisible to solutions that stay strictly inside the ball, and that
file deduces from the results here that those graph maps are `C¹` on the parameters for which
their graphs describe the local stable and unstable sets. The embedded-submanifold structure of
these graphs is not constructed here.

## Main declarations

* `ContinuousLinearMap.contDiffAt_lyapunovPerronSolution`: the Lyapunov--Perron solution is `C¹`
  in its input parameter.
* `ContinuousLinearMap.fderiv_lyapunovPerronSolution_apply` and
  `ContinuousLinearMap.eq_fderiv_lyapunovPerronSolution_apply`: its derivative is the unique
  bounded solution of the variational equation.
* `ContinuousLinearMap.contDiffAt_lyapunovPerronGraphMap`: the graph map is `C¹`.
* `ContinuousLinearMap.contDiff_lyapunovPerronSolution` and
  `ContinuousLinearMap.contDiff_lyapunovPerronGraphMap`: global forms, for a nonlinearity that is
  differentiable everywhere with derivative uniformly continuous on bounded sets.

## References

* C. Chicone, *Ordinary Differential Equations with Applications*, 2nd ed., Springer, 2006,
  Section 4.3.
* W. A. Coppel, *Dichotomies in Stability Theory*, Lecture Notes in Mathematics 629, Springer,
  1978, Chapter 5.
-/

public section

open Filter Metric NormedSpace Set Topology
open scoped NNReal BoundedContinuousFunction

noncomputable section

namespace ContinuousLinearMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {A P : X →L[ℝ] X} {K α ε : ℝ≥0} {N : X → X}

variable
  (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
  (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
  (hα : 0 < α) (hN : LipschitzWith ε N) (hsmall : 2 * K * ε < α)

omit [CompleteSpace X] in
include hs in
/-- The homogeneous term of the Lyapunov--Perron operator is bounded by `K ‖ξ‖` in forward
time. -/
private theorem norm_exp_smul_apply_le (ξ : X) (t : ℝ≥0) :
    ‖exp ((t : ℝ) • A) (P ξ)‖ ≤ K * ‖ξ‖ :=
  calc ‖exp ((t : ℝ) • A) (P ξ)‖ ≤ K * Real.exp (-α * t) * ‖ξ‖ := hs t t.2 ξ
    _ ≤ K * 1 * ‖ξ‖ := by
      gcongr
      exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 α.coe_nonneg) t.2)
    _ = K * ‖ξ‖ := by ring

/-- The homogeneous term `ξ ↦ (t ↦ exp (t A) (P ξ))` of the Lyapunov--Perron operator, as a
continuous linear map into bounded continuous curves. -/
private def homogeneousCLM : X →L[ℝ] (ℝ≥0 →ᵇ X) :=
  LinearMap.mkContinuous
    { toFun ξ := BoundedContinuousFunction.ofNormedAddCommGroup
        (fun t : ℝ≥0 ↦ exp ((t : ℝ) • A) (P ξ))
        (((differentiable_exp_smul_const ℝ A).continuous.comp NNReal.continuous_coe).clm_apply
          continuous_const)
        (K * ‖ξ‖) (norm_exp_smul_apply_le hs ξ)
      map_add' ξ ζ := by ext; simp
      map_smul' c ξ := by ext; simp }
    K fun ξ ↦ BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity)
      (norm_exp_smul_apply_le hs ξ)

/-- Evaluation of the homogeneous term. -/
private theorem homogeneousCLM_apply (ξ : X) (t : ℝ≥0) :
    homogeneousCLM hs ξ t = exp ((t : ℝ) • A) (P ξ) := by
  simp [homogeneousCLM]

/-- The Lyapunov--Perron operator splits as the homogeneous term plus the Lyapunov--Perron
integral of the superposition by `N`. -/
private theorem lyapunovPerronMap_eq_add (ξ : X) (γ : ℝ≥0 →ᵇ X) :
    lyapunovPerronMap A P N hs hu hα hN ξ γ =
      homogeneousCLM hs ξ + lyapunovPerronIntegralCLM A P hs hu hα (γ.comp N hN) := by
  ext t
  simp [homogeneousCLM_apply]

variable {N' : X → X →L[ℝ] X} {s : Set X} {δ : ℝ} {ξ₀ : X}

include hN hsmall in
/-- Pointwise application of a family of derivatives of the `ε`-Lipschitz map `N`, followed by
the Lyapunov--Perron integral, is a contraction. -/
private theorem norm_lyapunovPerronIntegralCLM_comp_applyCLM_lt
    (hNs : ∀ x ∈ s, HasFDerivAt N (N' x) x) {γ : ℝ≥0 →ᵇ X} (hγ : ∀ t, γ t ∈ s)
    {Φ : ℝ≥0 →ᵇ (X →L[ℝ] X)} (hΦ : ∀ t, Φ t = N' (γ t)) :
    ‖lyapunovPerronIntegralCLM A P hs hu hα ∘L BoundedContinuousFunction.applyCLM Φ‖ < 1 := by
  have hΦε : ‖Φ‖ ≤ ε := (BoundedContinuousFunction.norm_le ε.coe_nonneg).2 fun t ↦ by
    rw [hΦ]
    exact (hNs _ (hγ t)).le_of_lipschitz hN
  calc _ ≤ ‖lyapunovPerronIntegralCLM A P hs hu hα‖ * ‖BoundedContinuousFunction.applyCLM Φ‖ :=
        opNorm_comp_le _ _
    _ ≤ 2 * K / α * ε := by
        gcongr
        · exact norm_lyapunovPerronIntegralCLM_le hs hu hα
        · exact (BoundedContinuousFunction.norm_applyCLM_apply_le Φ).trans hΦε
    _ = ((2 * K * ε / α : ℝ≥0) : ℝ) := by push_cast; ring
    _ < 1 := by exact_mod_cast (div_lt_one hα).2 hsmall

/-- The implicit equation `γ - (t ↦ exp (t A) (P ξ)) - L (N ∘ γ) = 0` of the Lyapunov--Perron
solution. -/
private def implicitEquation (p : X × (ℝ≥0 →ᵇ X)) : ℝ≥0 →ᵇ X :=
  p.2 - homogeneousCLM hs p.1 - lyapunovPerronIntegralCLM A P hs hu hα (p.2.comp N hN)

/-- The zeros of the implicit equation are exactly the pairs `(ξ, lyapunovPerronSolution ξ)`. -/
private theorem implicitEquation_eq_zero_iff (p : X × (ℝ≥0 →ᵇ X)) :
    implicitEquation hs hu hα hN p = 0 ↔ lyapunovPerronSolution A P N hs hu hα hN hsmall p.1 = p.2
    := by
  rw [implicitEquation, sub_sub, sub_eq_zero, ← lyapunovPerronMap_eq_add]
  constructor
  · intro h
    exact (eq_lyapunovPerronSolution hs hu hα hN hsmall fun t ↦ by
      rw [← lyapunovPerronMap_apply hs hu hα hN, ← h]).symm
  · intro h
    rw [← h]
    exact (isFixedPt_lyapunovPerronSolution hs hu hα hN hsmall p.1).symm

variable (hNs : ∀ x ∈ s, HasFDerivAt N (N' x) x) (hN' : UniformContinuousOn N' s) (hδ : 0 < δ)
  (hξ₀ : ∀ t, ball (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ₀ t) δ ⊆ s)
include hNs hN' hδ hξ₀

/-- The Lyapunov--Perron solution agrees near `ξ₀` with the implicit function of its implicit
equation, which is `C¹`; this is the combined output of the implicit function theorem. -/
private theorem exists_contDiffAt_eventuallyEq :
    ∃ ψ : X → ℝ≥0 →ᵇ X, ContDiffAt ℝ 1 ψ ξ₀ ∧
      lyapunovPerronSolution A P N hs hu hα hN hsmall =ᶠ[𝓝 ξ₀] ψ := by
  set y := lyapunovPerronSolution A P N hs hu hα hN hsmall
  set L := lyapunovPerronIntegralCLM A P hs hu hα
  set F := implicitEquation hs hu hα hN
  have hmem : ∀ t, y ξ₀ t ∈ s := fun t ↦ hξ₀ t (mem_ball_self hδ)
  obtain ⟨Φ, hΦ⟩ := BoundedContinuousFunction.exists_eq_comp hN hNs hN'.continuousOn hmem
  have hcomp := BoundedContinuousFunction.hasStrictFDerivAt_comp hN hNs hN' hδ hξ₀ hΦ
  -- The implicit equation is strictly differentiable, with partial derivative `1 - L ∘ N'(γ)`
  -- in the curve.
  have hF : HasStrictFDerivAt F (snd ℝ X _ - homogeneousCLM hs ∘L fst ℝ X _ -
      (L ∘L BoundedContinuousFunction.applyCLM Φ) ∘L snd ℝ X _) (ξ₀, y ξ₀) :=
    (hasStrictFDerivAt_snd.sub ((homogeneousCLM hs).hasStrictFDerivAt.comp _
      hasStrictFDerivAt_fst)).sub
      (L.hasStrictFDerivAt.comp _ (hcomp.comp (ξ₀, y ξ₀) hasStrictFDerivAt_snd))
  have hFC : ContDiffAt ℝ 1 F (ξ₀, y ξ₀) :=
    (contDiffAt_snd.sub ((homogeneousCLM hs).contDiff.contDiffAt.comp _ contDiffAt_fst)).sub
      (L.contDiff.contDiffAt.comp _
        ((BoundedContinuousFunction.contDiffAt_comp hN hNs hN' hδ hξ₀).comp (ξ₀, y ξ₀)
          contDiffAt_snd))
  have hinv : (fderiv ℝ F (ξ₀, y ξ₀) ∘L inr ℝ X _).IsInvertible := by
    rw [hF.hasFDerivAt.fderiv]
    have heq : (snd ℝ X _ - homogeneousCLM hs ∘L fst ℝ X _ -
        (L ∘L BoundedContinuousFunction.applyCLM Φ) ∘L snd ℝ X _) ∘L inr ℝ X _ =
        ContinuousLinearMap.id ℝ _ - L ∘L BoundedContinuousFunction.applyCLM Φ := by
      ext γ : 1
      simp [L]
    rw [heq]
    by_cases htriv : Subsingleton (ℝ≥0 →ᵇ X)
    · let _ := htriv
      rw [Subsingleton.elim (ContinuousLinearMap.id ℝ _ -
        L ∘L BoundedContinuousFunction.applyCLM Φ) (0 : (ℝ≥0 →ᵇ X) →L[ℝ] _)]
      exact ContinuousLinearMap.isInvertible_zero_iff.mpr ⟨inferInstance, inferInstance⟩
    · let _ : Nontrivial (ℝ≥0 →ᵇ X) := not_subsingleton_iff_nontrivial.mp htriv
      apply ContinuousLinearMap.isInvertible_of_norm_sub_lt (ContinuousLinearEquiv.refl ℝ _)
      rw [← NNReal.coe_lt_coe]
      simpa [sub_sub, ContinuousLinearMap.norm_id] using
        (norm_lyapunovPerronIntegralCLM_comp_applyCLM_lt hs hu hα hN hsmall hNs hmem hΦ)
  refine ⟨hFC.implicitFunction one_ne_zero hinv, hFC.contDiffAt_implicitFunction _ _, ?_⟩
  -- Near `ξ₀`, the pair `(ξ, y ξ)` is near `(ξ₀, y ξ₀)` and solves the implicit equation.
  have hy : Tendsto (fun ξ ↦ (ξ, y ξ)) (𝓝 ξ₀) (𝓝 (ξ₀, y ξ₀)) :=
    (continuous_id.prodMk
      (lipschitzWith_lyapunovPerronSolution hs hu hα hN hsmall).continuous).tendsto ξ₀
  filter_upwards [hy.eventually (hFC.eventually_apply_eq_iff_implicitFunction one_ne_zero hinv)]
    with ξ hξ
  have hF0 : ∀ ξ, F (ξ, y ξ) = 0 := fun ξ ↦
    (implicitEquation_eq_zero_iff hs hu hα hN hsmall _).2 rfl
  exact (hξ.1 (by rw [hF0, hF0])).symm

/-- **The Lyapunov--Perron solution is `C¹` in its input parameter.** Suppose that `N` has
derivative `N' x` at every point `x` of `s`, that `N'` is uniformly continuous on `s`, and that
the values of the Lyapunov--Perron solution with input parameter `ξ₀` stay a distance `δ > 0`
inside `s`. Then `ξ ↦ lyapunovPerronSolution ξ` is continuously differentiable at `ξ₀`, for the
sup norm on bounded continuous curves. -/
theorem contDiffAt_lyapunovPerronSolution :
    ContDiffAt ℝ 1 (lyapunovPerronSolution A P N hs hu hα hN hsmall) ξ₀ :=
  have ⟨_, hψ, hyψ⟩ := exists_contDiffAt_eventuallyEq hs hu hα hN hsmall hNs hN' hδ hξ₀
  hψ.congr_of_eventuallyEq hyψ

/-- **The variational equation.** Under the hypotheses of
`ContinuousLinearMap.contDiffAt_lyapunovPerronSolution`, the derivative in the direction `v` of
the Lyapunov--Perron solution `y` with input parameter `ξ₀` solves the Lyapunov--Perron equation
of the linearized equation `z' = A z + N' (y t) z` with input parameter `v`. -/
theorem fderiv_lyapunovPerronSolution_apply (v : X) (t : ℝ≥0) :
    fderiv ℝ (lyapunovPerronSolution A P N hs hu hα hN hsmall) ξ₀ v t =
      exp ((t : ℝ) • A) (P v) + lyapunovPerronIntegral A P
        (fun s ↦ N' (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ₀ s.toNNReal)
          (fderiv ℝ (lyapunovPerronSolution A P N hs hu hα hN hsmall) ξ₀ v s.toNNReal)) t := by
  set y := lyapunovPerronSolution A P N hs hu hα hN hsmall
  set L := lyapunovPerronIntegralCLM A P hs hu hα
  obtain ⟨Φ, hΦ⟩ := BoundedContinuousFunction.exists_eq_comp hN hNs hN'.continuousOn
    fun t ↦ hξ₀ t (mem_ball_self hδ)
  have hy := (contDiffAt_lyapunovPerronSolution hs hu hα hN hsmall hNs hN' hδ hξ₀).differentiableAt
    one_ne_zero |>.hasFDerivAt
  -- Differentiate both sides of the fixed-point equation `y ξ = E ξ + L (N ∘ y ξ)`.
  have hfix : y = homogeneousCLM hs + L ∘ BoundedContinuousFunction.comp N hN ∘ y :=
      funext fun ξ ↦ by
    rw [Pi.add_apply, Function.comp_apply, Function.comp_apply, ← lyapunovPerronMap_eq_add]
    exact (isFixedPt_lyapunovPerronSolution hs hu hα hN hsmall ξ).symm
  have hrhs := (homogeneousCLM hs).hasFDerivAt.add (L.hasFDerivAt.comp ξ₀
    ((BoundedContinuousFunction.hasFDerivAt_comp hN hNs hN' hδ hξ₀ hΦ).comp ξ₀ hy))
  rw [← hfix] at hrhs
  have h := congrArg (fun D : X →L[ℝ] (ℝ≥0 →ᵇ X) ↦ D v t) (hy.unique hrhs)
  simpa [homogeneousCLM_apply, L, hΦ] using h

/-- **Uniqueness in the variational equation.** Under the hypotheses of
`ContinuousLinearMap.contDiffAt_lyapunovPerronSolution`, a bounded continuous curve solving the
Lyapunov--Perron equation of the linearization along the solution with input parameter `v` is the
derivative of the Lyapunov--Perron solution in the direction `v`. -/
theorem eq_fderiv_lyapunovPerronSolution_apply {v : X} {η : ℝ≥0 →ᵇ X}
    (hη : ∀ t : ℝ≥0, η t = exp ((t : ℝ) • A) (P v) + lyapunovPerronIntegral A P
      (fun s ↦ N' (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ₀ s.toNNReal)
        (η s.toNNReal)) t) :
    η = fderiv ℝ (lyapunovPerronSolution A P N hs hu hα hN hsmall) ξ₀ v := by
  set L := lyapunovPerronIntegralCLM A P hs hu hα
  set D := fderiv ℝ (lyapunovPerronSolution A P N hs hu hα hN hsmall) ξ₀
  obtain ⟨Φ, hΦ⟩ := BoundedContinuousFunction.exists_eq_comp hN hNs hN'.continuousOn
    fun t ↦ hξ₀ t (mem_ball_self hδ)
  set T := L ∘L BoundedContinuousFunction.applyCLM Φ
  have hT := norm_lyapunovPerronIntegralCLM_comp_applyCLM_lt hs hu hα hN hsmall hNs
    (fun t ↦ hξ₀ t (mem_ball_self hδ)) hΦ
  -- Both curves are fixed points of the affine contraction `ζ ↦ E v + T ζ`.
  have hfix : ∀ ζ : ℝ≥0 →ᵇ X, (∀ t : ℝ≥0, ζ t = exp ((t : ℝ) • A) (P v) + lyapunovPerronIntegral
      A P (fun s ↦ N' (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ₀ s.toNNReal)
        (ζ s.toNNReal)) t) → ζ = homogeneousCLM hs v + T ζ := fun ζ hζ ↦ by
    ext t
    simp [hζ t, homogeneousCLM_apply, T, L, hΦ]
  have hsub : η - D v = T (η - D v) := by
    rw [map_sub, ← add_sub_add_left_eq_sub (T η) (T (D v)) (homogeneousCLM hs v), ← hfix η hη,
      ← hfix (D v) (fderiv_lyapunovPerronSolution_apply hs hu hα hN hsmall hNs hN' hδ hξ₀ v)]
  have hle : ‖η - D v‖ ≤ ‖T‖ * ‖η - D v‖ := by
    conv_lhs => rw [hsub]
    exact T.le_opNorm (η - D v)
  have hzero : ‖η - D v‖ = 0 := by nlinarith [norm_nonneg (η - D v)]
  exact sub_eq_zero.1 (norm_eq_zero.1 hzero)

/-- **The Lyapunov--Perron graph map is `C¹`** at every input parameter whose Lyapunov--Perron
solution stays a positive distance inside a set on which `N` is differentiable with uniformly
continuous derivative. -/
theorem contDiffAt_lyapunovPerronGraphMap :
    ContDiffAt ℝ 1 (lyapunovPerronGraphMap A P N hs hu hα hN hsmall) ξ₀ := by
  have h : lyapunovPerronGraphMap A P N hs hu hα hN hsmall =
      fun ξ ↦ lyapunovPerronSolution A P N hs hu hα hN hsmall ξ 0 - P ξ := funext fun ξ ↦ by
    rw [lyapunovPerronSolution_zero_eq_add_lyapunovPerronGraphMap, add_sub_cancel_left]
  rw [h]
  exact ((BoundedContinuousFunction.evalCLM ℝ 0).contDiff.contDiffAt.comp ξ₀
    (contDiffAt_lyapunovPerronSolution hs hu hα hN hsmall hNs hN' hδ hξ₀)).sub
    P.contDiff.contDiffAt

omit hNs hN' hδ hξ₀

/-- **The Lyapunov--Perron solution is `C¹`, global form.** If `N` is differentiable everywhere,
with a derivative that is uniformly continuous on every ball about `0`, then the Lyapunov--Perron
solution is continuously differentiable in its input parameter. -/
theorem contDiff_lyapunovPerronSolution (hNd : ∀ x, HasFDerivAt N (N' x) x)
    (hN' : ∀ r, UniformContinuousOn N' (ball 0 r)) :
    ContDiff ℝ 1 (lyapunovPerronSolution A P N hs hu hα hN hsmall) :=
  -- The values of a bounded continuous curve stay at distance `1` inside a ball about `0`.
  contDiff_iff_contDiffAt.2 fun ξ₀ ↦
    let γ := lyapunovPerronSolution A P N hs hu hα hN hsmall ξ₀
    contDiffAt_lyapunovPerronSolution hs hu hα hN hsmall (fun x _ ↦ hNd x) (hN' (‖γ‖ + 1)) one_pos
      fun t ↦ ball_subset_ball' <| by rw [dist_zero_right]; linarith [γ.norm_coe_le_norm t]

/-- **The Lyapunov--Perron graph map is `C¹`, global form.** If `N` is differentiable everywhere,
with a derivative that is uniformly continuous on every ball about `0`, then the Lyapunov--Perron
graph map is continuously differentiable. -/
theorem contDiff_lyapunovPerronGraphMap (hNd : ∀ x, HasFDerivAt N (N' x) x)
    (hN' : ∀ r, UniformContinuousOn N' (ball 0 r)) :
    ContDiff ℝ 1 (lyapunovPerronGraphMap A P N hs hu hα hN hsmall) :=
  contDiff_iff_contDiffAt.2 fun ξ₀ ↦
    let γ := lyapunovPerronSolution A P N hs hu hα hN hsmall ξ₀
    contDiffAt_lyapunovPerronGraphMap hs hu hα hN hsmall (fun x _ ↦ hNd x) (hN' (‖γ‖ + 1)) one_pos
      fun t ↦ ball_subset_ball' <| by rw [dist_zero_right]; linarith [γ.norm_coe_le_norm t]

end ContinuousLinearMap

end
