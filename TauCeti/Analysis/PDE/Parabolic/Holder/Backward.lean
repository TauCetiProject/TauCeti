/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Operator

/-!
# Backward parabolic operators and time reversal

For coefficient fields `A`, `B`, `C` in `C_b^{α,α/2}` on the slab `E × [a, b]`, this file defines
the backward parabolic operator `P_back u = ∂ₜu + A·D_x²u + B·D_xu + C·u` as a bounded linear map
from `C_b^{2+α,1+α/2}` (`ParabolicC2HolderSpace`) to `C_b^{α,α/2}`, and shows that time reversal
turns backward problems with terminal data into forward problems with initial data.

Let `R (x, s) = (x, T - s)`, mapping `E × [T - b, T - a]` onto `E × [a, b]`, and put `v = u ∘ R`,
`A_R = A ∘ R`, `B_R = B ∘ R`, `C_R = C ∘ R`. Since `R` keeps the spatial derivatives and negates the
time derivative, the forward operator `P_R = ∂ₜ - A_R·D_x² - B_R·D_x - C_R` satisfies
`P_R v = -(P_back u) ∘ R`. Hence `P_back u = g` if and only if `P_R v = -g ∘ R`, and the initial
trace of `v` at `T - b` is the terminal trace of `u` at `b`. Consequently the terminal-data map
`u ↦ (P_back u, u(·, b))` is bijective exactly when the initial-data map
`v ↦ (P_R v, v(·, T - b))` of the reversed forward problem is.

On `ℝⁿ = EuclideanSpace ℝ ι` with scalar coefficients `aⁱʲ`, `bⁱ`, `c`, the forward comparison
principle then yields the backward one: for degenerate elliptic `a` and `c ≤ γ` with `0 ≤ γ`,
`P_back u ≥ -K` and `u(·, t₁) ≤ M`, where `0 ≤ M` and `0 ≤ K`, imply
`u(x, t) ≤ exp (γ (t₁ - t)) (M + (t₁ - t) K)`, with the two-sided bound and uniqueness for the
terminal-value problem.

## Main declarations

* `TauCeti.ParabolicC2HolderSpace.backwardParabolicOperatorL`: the operator `P_back = ∂ₜ + L`.
* `TauCeti.ParabolicC2HolderSpace.parabolicOperatorL_timeReverseLIE`: `P_R v = -(P_back u) ∘ R`.
* `TauCeti.ParabolicC2HolderSpace.backwardParabolicOperatorL_eq_iff`:
  `P_back u = g ↔ P_R v = -g ∘ R`.
* `TauCeti.ParabolicC2HolderSpace.bijective_backwardParabolicOperatorL_prod_spatialTraceL_iff`: the
  terminal-data map is bijective iff the reversed initial-data map is.
* `TauCeti.ParabolicC2HolderSpace.euclideanBackwardParabolicOperatorL` with the terminal-value
  bounds `le_exp_mul_mul_add_mul_of_le_euclideanBackwardParabolicOperatorL`,
  `abs_le_exp_mul_mul_add_mul_of_abs_euclideanBackwardParabolicOperatorL_le` and uniqueness
  `eq_of_euclideanBackwardParabolicOperatorL_eq`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004,
  Chapter 4.
* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 2, Section 4.
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime
open scoped NNReal

variable {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A local shortcut for the norm on Hessians; see the same shortcut in the file defining
`parabolicOperatorL`, whose coefficient space needs it for instance search. -/
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on Hessians, needed for the same reason. -/
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

/-! ### The backward operator -/

section Backward

variable {t₀ t₁ : ℝ} {ht : t₀ < t₁}

/-- The backward parabolic operator `P_back u = ∂ₜu + A·D_x²u + B·D_xu + C·u` with coefficient
fields in `C_b^{α,α/2}`, as a continuous linear map from `C_b^{2+α,1+α/2}` to `C_b^{α,α/2}`. -/
def backwardParabolicOperatorL (hα : α ≤ 1)
    (A : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F))
    (B : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] F) →L[ℝ] F))
    (C : HolderSpace α (slab (E := E) t₀ t₁) (F →L[ℝ] F)) :
    ParabolicC2HolderSpace α E F ht →L[ℝ] HolderSpace α (slab (E := E) t₀ t₁) F :=
  timeDerivL + spatialOperatorL hα A B C

variable (hα : α ≤ 1)
  {A A' : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F)}
  {B B' : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] F) →L[ℝ] F)}
  {C C' : HolderSpace α (slab (E := E) t₀ t₁) (F →L[ℝ] F)}

theorem backwardParabolicOperatorL_def :
    backwardParabolicOperatorL (ht := ht) hα A B C = timeDerivL + spatialOperatorL hα A B C :=
  (rfl)

@[simp]
theorem backwardParabolicOperatorL_apply (u : ParabolicC2HolderSpace α E F ht)
    (p : slab (E := E) t₀ t₁) :
    backwardParabolicOperatorL hα A B C u p =
      timeDerivL u p + (A p (spatialSecondFDerivL u p) + B p (spatialFDerivL u p) +
        C p (u p)) := by
  simp [backwardParabolicOperatorL]

/-- **The operator bound for the backward operator.**
`‖P_back‖ ≤ 1 + ‖A‖ + 24 (‖B‖ + ‖C‖)`, uniformly over the spaces and the slab. -/
theorem norm_backwardParabolicOperatorL_le :
    ‖backwardParabolicOperatorL (ht := ht) hα A B C‖ ≤ 1 + ‖A‖ + 24 * (‖B‖ + ‖C‖) := by
  rw [backwardParabolicOperatorL_def, add_assoc]
  exact (norm_add_le _ _).trans (add_le_add norm_timeDerivL_le_one (norm_spatialOperatorL_le hα))

/-- **Lipschitz dependence on the coefficients.** In operator norm,
`‖P_back_{A,B,C} - P_back_{A',B',C'}‖ ≤ ‖A - A'‖ + 24 (‖B - B'‖ + ‖C - C'‖)`. -/
theorem norm_backwardParabolicOperatorL_sub_le :
    ‖backwardParabolicOperatorL (ht := ht) hα A B C - backwardParabolicOperatorL hα A' B' C'‖ ≤
      ‖A - A'‖ + 24 * (‖B - B'‖ + ‖C - C'‖) := by
  rw [backwardParabolicOperatorL_def, backwardParabolicOperatorL_def, add_sub_add_left_eq_sub,
    ← spatialOperatorL_sub]
  exact norm_spatialOperatorL_le hα

end Backward

/-! ### Time reversal of the backward operator -/

section TimeReversal

variable {a b a' b' T : ℝ} {hab : a < b} {ha : a' = T - b} {hb : b' = T - a} (hα : α ≤ 1)
  {A : HolderSpace α (slab (E := E) a b) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F)}
  {B : HolderSpace α (slab (E := E) a b) ((E →L[ℝ] F) →L[ℝ] F)}
  {C : HolderSpace α (slab (E := E) a b) (F →L[ℝ] F)}

/-- **Time reversal of the backward operator.** With `R (x, s) = (x, T - s)` and `v = u ∘ R`,
the forward operator with the reversed coefficients `A ∘ R`, `B ∘ R`, `C ∘ R` satisfies
`P_R v = -(P_back u) ∘ R`. -/
theorem parabolicOperatorL_timeReverseLIE (u : ParabolicC2HolderSpace α E F hab) :
    parabolicOperatorL hα
        (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith A)
        (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith B)
        (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith C)
        (timeReverseLIE T ha hb u) =
      -HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith
        (backwardParabolicOperatorL hα A B C u) := by
  ext p
  simp only [parabolicOperatorL_apply, timeDerivL_timeReverseLIE,
    spatialSecondFDerivL_timeReverseLIE, spatialFDerivL_timeReverseLIE, timeReverseLIE_apply,
    HolderSpace.compLipschitzL_apply, HolderSpace.neg_apply, backwardParabolicOperatorL_apply]
  abel

/-- **Backward problems are reversed forward problems.** With `R (x, s) = (x, T - s)`,
`P_back u = g` holds if and only if the time reversal `v = u ∘ R` solves the forward equation
`P_R v = -g ∘ R` with the reversed coefficients `A ∘ R`, `B ∘ R`, `C ∘ R`. -/
theorem backwardParabolicOperatorL_eq_iff (u : ParabolicC2HolderSpace α E F hab)
    (g : HolderSpace α (slab (E := E) a b) F) :
    backwardParabolicOperatorL hα A B C u = g ↔
      parabolicOperatorL hα
          (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith A)
          (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith B)
          (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith C)
          (timeReverseLIE T ha hb u) =
        -HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith g := by
  rw [parabolicOperatorL_timeReverseLIE, neg_inj]
  refine ⟨fun h ↦ h ▸ rfl, fun h ↦ ?_⟩
  ext q
  have hq := congrArg (fun w : HolderSpace α (slab (E := E) a' b') F ↦
    w ((slabTimeReverse T ha hb).symm q)) h
  simpa only [HolderSpace.compLipschitzL_apply, IsometryEquiv.apply_symm_apply] using hq

/-- **Solvability of the terminal-value problem by time reversal.** With
`R (x, s) = (x, T - s)`, the terminal-data map `u ↦ (P_back u, u(·, b))` of the backward problem
on `E × [a, b]` is bijective if and only if the initial-data map `v ↦ (P_R v, v(·, T - b))` of
the forward problem on `E × [T - b, T - a]` with the reversed coefficients `A ∘ R`, `B ∘ R`,
`C ∘ R` is bijective. -/
theorem bijective_backwardParabolicOperatorL_prod_spatialTraceL_iff :
    Function.Bijective ((backwardParabolicOperatorL (ht := hab) hα A B C).prod
        (spatialTraceL ⟨b, right_mem_Icc.2 hab.le⟩)) ↔
      Function.Bijective ((parabolicOperatorL (ht := ha ▸ hb ▸ sub_lt_sub_left hab T) hα
          (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith A)
          (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith B)
          (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith C)).prod
        (spatialTraceL ⟨a', left_mem_Icc.2 (ha ▸ hb ▸ sub_lt_sub_left hab T).le⟩)) := by
  set R := slabTimeReverse (E := E) T ha hb
  -- The data of the reversed problem are those of the backward problem transported by
  -- `Φ (g, h) = (-g ∘ R, h)`, a bijection with inverse `(g, h) ↦ (-g ∘ R⁻¹, h)`.
  set Φ : HolderSpace α (slab (E := E) a b) F × CkHolderSpace 2 α E F →
      HolderSpace α (slab (E := E) a' b') F × CkHolderSpace 2 α E F :=
    fun gh ↦ (-HolderSpace.compLipschitzL _ R.isometry.lipschitzWith gh.1, gh.2) with hΦ
  have hΦb : Function.Bijective Φ := by
    refine Function.bijective_iff_has_inverse.2
      ⟨fun gh ↦ (-HolderSpace.compLipschitzL _ R.symm.isometry.lipschitzWith gh.1, gh.2),
        fun gh ↦ ?_, fun gh ↦ ?_⟩ <;>
      ext <;> simp [hΦ]
  have hcomp : ⇑((parabolicOperatorL (ht := ha ▸ hb ▸ sub_lt_sub_left hab T) hα
        (HolderSpace.compLipschitzL _ R.isometry.lipschitzWith A)
        (HolderSpace.compLipschitzL _ R.isometry.lipschitzWith B)
        (HolderSpace.compLipschitzL _ R.isometry.lipschitzWith C)).prod
        (spatialTraceL ⟨a', left_mem_Icc.2 (ha ▸ hb ▸ sub_lt_sub_left hab T).le⟩)) ∘
        timeReverseLIE T ha hb =
      Φ ∘ (backwardParabolicOperatorL (ht := hab) hα A B C).prod
        (spatialTraceL ⟨b, right_mem_Icc.2 hab.le⟩) := by
    funext u
    simp only [Function.comp_apply, ContinuousLinearMap.prod_apply, spatialTraceL_apply, hΦ,
      parabolicOperatorL_timeReverseLIE, spatialTrace_timeReverseLIE_left, R]
  rw [← Function.Bijective.of_comp_iff' hΦb, ← hcomp,
    Function.Bijective.of_comp_iff _ (timeReverseLIE T ha hb).bijective]

end TimeReversal

/-! ### Reversal of a slab onto itself -/

section SelfReversal

variable {t₀ t₁ : ℝ} {ht : t₀ < t₁}

/-- Time reversal about `t₀ + t₁` exchanges the endpoints `t₀` and `t₁`, so it maps the slab
`E × [t₀, t₁]` onto itself. -/
private theorem left_eq_add_sub : t₀ = t₀ + t₁ - t₁ := by ring

private theorem right_eq_add_sub : t₁ = t₀ + t₁ - t₀ := by ring

/-- The time reversal of `u` about `t₀ + t₁` evaluated at the initial time `t₀` is `u` at the
terminal time `t₁`. -/
private theorem timeReverseLIE_slabMk_left
    (u : ParabolicC2HolderSpace α E F ht) (x : E) :
    timeReverseLIE (t₀ + t₁) left_eq_add_sub right_eq_add_sub u
        (slabMk x ⟨t₀, left_mem_Icc.2 ht.le⟩) =
      u (slabMk x ⟨t₁, right_mem_Icc.2 ht.le⟩) := by
  rw [timeReverseLIE_apply, slabTimeReverse_slabMk]
  congr
  ring

/-- The time reversal of `u` about `t₀ + t₁`, evaluated at the reversal of `p`, is `u p`. -/
private theorem timeReverseLIE_symm_apply
    (u : ParabolicC2HolderSpace α E F ht)
    (p : slab (E := E) t₀ t₁) :
    timeReverseLIE (t₀ + t₁) left_eq_add_sub right_eq_add_sub u
        ((slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).symm p) = u p := by
  rw [timeReverseLIE_apply, IsometryEquiv.apply_symm_apply]

omit [NormedSpace ℝ E] in
/-- The time elapsed since `t₀` at the reversal of `p` is the time remaining from `p` to the
terminal time `t₁`. -/
private theorem slabTime_slabTimeReverse_symm_sub (p : slab (E := E) t₀ t₁) :
    (slabTime ((slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).symm p) : ℝ) - t₀ =
      t₁ - slabTime p := by
  simp only [slabTimeReverse_symm, coe_slabTime, coe_slabTimeReverse, time_timeReverse]
  ring

end SelfReversal

/-! ### Coordinate coefficients on Euclidean space -/

section Euclidean

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {t₀ t₁ : ℝ} {ht : t₀ < t₁}

/-- The backward parabolic operator `P_back u = ∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u` on
`ℝⁿ = EuclideanSpace ℝ ι` with scalar coefficients `aⁱʲ`, `bⁱ`, `c` in `C_b^{α,α/2}`, as a
continuous linear map from `C_b^{2+α,1+α/2}` to `C_b^{α,α/2}`. -/
def euclideanBackwardParabolicOperatorL (hα : α ≤ 1)
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ) :
    ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht →L[ℝ]
      HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ :=
  backwardParabolicOperatorL hα (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b)
    (euclideanZerothOrderCoeff c)

variable (hα : α ≤ 1)

theorem euclideanBackwardParabolicOperatorL_def
    {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
    {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
    {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ} :
    euclideanBackwardParabolicOperatorL (ht := ht) hα a b c =
      backwardParabolicOperatorL hα (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b)
        (euclideanZerothOrderCoeff c) := (rfl)

@[simp]
theorem euclideanBackwardParabolicOperatorL_apply
    {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
    {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
    {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht)
    (p : slab (E := EuclideanSpace ℝ ι) t₀ t₁) :
    euclideanBackwardParabolicOperatorL hα a b c u p = timeDerivL u p +
      (∑ i, ∑ j, a i j p * spatialSecondFDerivL u p (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + ∑ i, b i p * spatialFDerivL u p (EuclideanSpace.single i 1) +
        c p * u p) := by
  simp [euclideanBackwardParabolicOperatorL]

/-- **Time reversal of the Euclidean backward operator.** With `R (x, s) = (x, T - s)` and
`v = u ∘ R`, the forward operator with the reversed coefficients `aⁱʲ ∘ R`, `bⁱ ∘ R`, `c ∘ R`
satisfies `P_R v = -(P_back u) ∘ R`. -/
theorem euclideanParabolicOperatorL_timeReverseLIE {a b a' b' T : ℝ} {hab : a < b}
    {ha : a' = T - b} {hb : b' = T - a}
    {A : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) a b) ℝ}
    {B : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) a b) ℝ}
    {C : HolderSpace α (slab (E := EuclideanSpace ℝ ι) a b) ℝ}
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hab) :
    euclideanParabolicOperatorL hα
        (fun i j ↦ HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith
          (A i j))
        (fun i ↦ HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith
          (B i))
        (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith C)
        (timeReverseLIE T ha hb u) =
      -HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith
        (euclideanBackwardParabolicOperatorL hα A B C u) := by
  ext p
  simp only [euclideanParabolicOperatorL_apply, timeDerivL_timeReverseLIE,
    spatialSecondFDerivL_timeReverseLIE, spatialFDerivL_timeReverseLIE, timeReverseLIE_apply,
    HolderSpace.compLipschitzL_apply, HolderSpace.neg_apply,
    euclideanBackwardParabolicOperatorL_apply]
  ring

variable {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}

/-- **The one-sided a priori bound for the terminal-value problem.** Let `a` be degenerate
elliptic and `c ≤ γ` with `0 ≤ γ`. If `u ∈ C_b^{2+α,1+α/2}` on `ℝⁿ × [t₀, t₁]` satisfies
`P_back u ≥ -K` and `u(·, t₁) ≤ M` with `0 ≤ M` and `0 ≤ K`, then
`u(x, t) ≤ exp (γ (t₁ - t)) (M + (t₁ - t) K)`. -/
theorem le_exp_mul_mul_add_mul_of_le_euclideanBackwardParabolicOperatorL
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι), 0 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    {γ : ℝ} (hc : ∀ p, c p ≤ γ) (hγ : 0 ≤ γ) {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht)
    (hP : ∀ p, -K ≤ euclideanBackwardParabolicOperatorL hα a b c u p)
    (hterm : ∀ x, u (slabMk x ⟨t₁, right_mem_Icc.2 ht.le⟩) ≤ M)
    (p : slab (E := EuclideanSpace ℝ ι) t₀ t₁) :
    u p ≤ Real.exp (γ * (t₁ - slabTime p)) * (M + (t₁ - slabTime p) * K) := by
  -- Reverse time about `t₀ + t₁`, which maps the slab onto itself, and apply the forward bound.
  have h := le_exp_mul_mul_add_mul_of_euclideanParabolicOperatorL_le hα
    (a := fun i j ↦ HolderSpace.compLipschitzL _
      (slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).isometry.lipschitzWith (a i j))
    (b := fun i ↦ HolderSpace.compLipschitzL _
      (slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).isometry.lipschitzWith (b i))
    (c := HolderSpace.compLipschitzL _
      (slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).isometry.lipschitzWith c)
    (fun q ξ ↦ by simpa using ha _ ξ) (fun q ↦ by simpa using hc _) hγ hM hK
    (timeReverseLIE (t₀ + t₁) left_eq_add_sub right_eq_add_sub u)
    (fun q ↦ by
      rw [euclideanParabolicOperatorL_timeReverseLIE, HolderSpace.neg_apply,
        HolderSpace.compLipschitzL_apply]
      exact neg_le.1 (hP _))
    (fun x ↦ by rw [timeReverseLIE_slabMk_left]; exact hterm x)
    ((slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).symm p)
  rwa [timeReverseLIE_symm_apply, slabTime_slabTimeReverse_symm_sub] at h

/-- **The a priori bound for the terminal-value problem.** Let `a` be degenerate elliptic and
`c ≤ γ` with `0 ≤ γ`. If `u ∈ C_b^{2+α,1+α/2}` on `ℝⁿ × [t₀, t₁]` satisfies `|P_back u| ≤ K` and
`|u(·, t₁)| ≤ M`, then `|u(x, t)| ≤ exp (γ (t₁ - t)) (M + (t₁ - t) K)`. -/
theorem abs_le_exp_mul_mul_add_mul_of_abs_euclideanBackwardParabolicOperatorL_le
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι), 0 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    {γ : ℝ} (hc : ∀ p, c p ≤ γ) (hγ : 0 ≤ γ) {M K : ℝ}
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht)
    (hP : ∀ p, |euclideanBackwardParabolicOperatorL hα a b c u p| ≤ K)
    (hterm : ∀ x, |u (slabMk x ⟨t₁, right_mem_Icc.2 ht.le⟩)| ≤ M)
    (p : slab (E := EuclideanSpace ℝ ι) t₀ t₁) :
    |u p| ≤ Real.exp (γ * (t₁ - slabTime p)) * (M + (t₁ - slabTime p) * K) := by
  have h := abs_le_exp_mul_mul_add_mul_of_abs_euclideanParabolicOperatorL_le hα
    (a := fun i j ↦ HolderSpace.compLipschitzL _
      (slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).isometry.lipschitzWith (a i j))
    (b := fun i ↦ HolderSpace.compLipschitzL _
      (slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).isometry.lipschitzWith (b i))
    (c := HolderSpace.compLipschitzL _
      (slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).isometry.lipschitzWith c)
    (fun q ξ ↦ by simpa using ha _ ξ) (fun q ↦ by simpa using hc _) hγ
    (timeReverseLIE (t₀ + t₁) left_eq_add_sub right_eq_add_sub u)
    (fun q ↦ by
      rw [euclideanParabolicOperatorL_timeReverseLIE, HolderSpace.neg_apply,
        HolderSpace.compLipschitzL_apply, abs_neg]
      exact hP _)
    (fun x ↦ by rw [timeReverseLIE_slabMk_left]; exact hterm x)
    ((slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).symm p)
  rwa [timeReverseLIE_symm_apply, slabTime_slabTimeReverse_symm_sub] at h

/-- **Uniqueness for the terminal-value problem.** For degenerate elliptic `a`, an element of
`C_b^{2+α,1+α/2}` on `ℝⁿ × [t₀, t₁]` is determined by `P_back u` and its terminal trace
`u(·, t₁)`. -/
theorem eq_of_euclideanBackwardParabolicOperatorL_eq
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι), 0 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    {u v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht}
    (hP : euclideanBackwardParabolicOperatorL hα a b c u =
      euclideanBackwardParabolicOperatorL hα a b c v)
    (hterm : ∀ x, u (slabMk x ⟨t₁, right_mem_Icc.2 ht.le⟩) =
      v (slabMk x ⟨t₁, right_mem_Icc.2 ht.le⟩)) :
    u = v := by
  refine (timeReverseLIE (t₀ + t₁) left_eq_add_sub right_eq_add_sub).injective
    (eq_of_euclideanParabolicOperatorL_eq hα
      (a := fun i j ↦ HolderSpace.compLipschitzL _
        (slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).isometry.lipschitzWith (a i j))
      (b := fun i ↦ HolderSpace.compLipschitzL _
        (slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).isometry.lipschitzWith (b i))
      (c := HolderSpace.compLipschitzL _
        (slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).isometry.lipschitzWith c)
      (fun q ξ ↦ by simpa using ha _ ξ) ?_ fun x ↦ ?_)
  · rw [euclideanParabolicOperatorL_timeReverseLIE, euclideanParabolicOperatorL_timeReverseLIE,
      hP]
  · rw [timeReverseLIE_slabMk_left, timeReverseLIE_slabMk_left, hterm]

end Euclidean

end TauCeti.ParabolicC2HolderSpace
