/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.ConstantCoefficient.CauchyProblem
public import TauCeti.Analysis.PDE.Parabolic.Holder.Cutoff
public import TauCeti.Analysis.PDE.Parabolic.Holder.Freezing
public import TauCeti.Analysis.PDE.Parabolic.Holder.Localization
public import TauCeti.Analysis.PDE.Parabolic.Holder.Patching

/-!
# The global Schauder estimate for parabolic operators with Hölder coefficients

On `ℝⁿ = EuclideanSpace ℝ ι` and a time slab `ℝⁿ × [0, T]`, let

`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

have coefficients `aⁱʲ`, `bⁱ`, `c` in the bounded parabolic Hölder space `C_b^{α,α/2}`, with
`0 < α < 1`, and let `a` be uniformly elliptic: `λ ‖ξ‖² ≤ ξᵀ a(p) ξ ≤ Λ ‖ξ‖²` at every point `p`,
with `0 < λ`. This file proves the global Schauder estimate in the bounded order-two parabolic
Hölder space `C_b^{2+α,1+α/2}`: there is a constant `C`, depending only on `n`, `α`, `λ`, `Λ`, a
bound `K` on the Hölder norms of the coefficients and a bound `T₀` on the horizon, with

`‖u‖_{2+α,par} ≤ C (‖P u‖_{α,par} + ‖u(·, 0)‖_{2,α})`

for every `u ∈ C_b^{2+α,1+α/2}`
(`TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL`). No symmetry of `a`
and no sign condition on `c` is needed. This is the a priori estimate through which the method of
continuity, started from the heat operator, solves the Cauchy problem `P u = f`, `u(·, 0) = u₀`.

## The argument

The proof is the classical localization of the constant-coefficient estimate
(`TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL_const`).

1. **Small support.** If `w` vanishes outside a parabolic ball of small radius about a point
   `p`, freeze the principal coefficient at `p`. The operator `P_{a(p)}` with constant
   coefficients differs from `P` by the principal error `(a - a(p))·D²w`, which is small since
   `a` oscillates little on the ball (`exists_norm_spatialOperatorL_sub_const_apply_le`), and by
   the lower-order terms, which interpolation bounds by a small multiple of `‖w‖` and a multiple
   of `‖w‖_∞`. Absorbing both gives
   `‖w‖ ≤ C (‖P w‖ + ‖w(·, 0)‖ + ‖w‖_∞)`
   (`exists_norm_le_euclideanParabolicOperatorL_add_of_forall_lt_dist`).
2. **Localization.** For a cutoff `χ_p` centred at each point `p`, apply step 1 to `χ_p u`. The
   commutator `P (χ_p u) - χ_p P u` involves only `u` and `D u`, so it is again at most a small
   multiple of `‖u‖` plus a multiple of `‖u‖_∞`
   (`exists_norm_parabolicOperatorL_mul_sub_mul_parabolicOperatorL_le`). When `u(·, 0) = 0` the
   localizations also vanish at the initial time. Patching the local bounds
   (`norm_le_of_forall_eqOn_ball`) and absorbing gives
   `‖u‖ ≤ C (‖P u‖ + ‖u‖_∞)`.
3. **Initial data.** Subtracting the solution of a constant-coefficient Cauchy problem with the
   same initial datum reduces the general case to the case `u(·, 0) = 0`, which gives
   `‖u‖ ≤ C (‖P u‖ + ‖u(·, 0)‖ + ‖u‖_∞)`
   (`exists_norm_le_euclideanParabolicOperatorL_add`).
4. **The supremum term.** The comparison principle bounds `‖u‖_∞` by
   `exp (‖c‖ T) (‖u(·, 0)‖_∞ + T ‖P u‖_∞)`
   (`abs_le_exp_mul_mul_add_mul_of_abs_euclideanParabolicOperatorL_le`), which removes it.

## Main declarations

All declarations are in the `TauCeti.ParabolicC2HolderSpace` namespace.

* `exists_norm_le_euclideanParabolicOperatorL_add_of_forall_lt_dist`: the estimate for maps
  supported in a small parabolic ball.
* `exists_norm_le_euclideanParabolicOperatorL_add`: the global estimate with the supremum norm of
  `u` on the right.
* `exists_norm_le_euclideanParabolicOperatorL`: the global Schauder estimate.

## References

* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8 (Theorem 8.9.2 and its proof by localization).
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.1 (the elliptic analogue).
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set Metric ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

variable {α : ℝ≥0} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A local shortcut for the norm on covectors, needed for scalar operations on gradient
coefficients: the norm instance on the domain of the coefficient space only arises as a nested
instance problem during unification. -/
private local instance instCovectorNorm : NormedAddCommGroup (EuclideanSpace ℝ ι →L[ℝ] ℝ) :=
  inferInstance
/-- A local shortcut for scalar operations on covectors. -/
private local instance instCovectorSpace : NormedSpace ℝ (EuclideanSpace ℝ ι →L[ℝ] ℝ) :=
  inferInstance
/-- A local shortcut for the norm on Euclidean Hessians, needed for the same reason. -/
private local instance instHessianNorm :
    NormedAddCommGroup (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) :=
  inferInstance
/-- A local shortcut for scalar operations on Euclidean Hessians. -/
private local instance instHessianSpace :
    NormedSpace ℝ (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) :=
  inferInstance

/-! ### Freezing the coefficients at a point -/

section Freezing

variable {t₀ t₁ : ℝ} {ht : t₀ < t₁}

/-- Freezing the coefficients at `p`: the operator `∂ₜ - aⁱʲ(p) ∂ᵢ∂ⱼ` with the principal
coefficients frozen at `p` and no lower-order terms is `P` plus the principal error
`(a - a(p))·D²` plus the lower-order part of `P`. -/
private theorem euclideanParabolicOperatorL_const_apply_eq (hα : α ≤ 1)
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (p : slab (E := EuclideanSpace ℝ ι) t₀ t₁)
    (w : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht) :
    euclideanParabolicOperatorL hα (fun i j ↦ HolderSpace.const (a i j p)) 0 0 w =
      euclideanParabolicOperatorL hα a b c w +
        spatialOperatorL hα (euclideanSecondOrderCoeff a -
          HolderSpace.const (euclideanSecondOrderCoeff a p)) 0 0 w +
        spatialOperatorL hα 0 (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c) w := by
  ext q
  simp only [euclideanParabolicOperatorL_apply, HolderSpace.add_apply, spatialOperatorL_apply,
    HolderSpace.sub_apply, HolderSpace.const_apply, HolderSpace.zero_apply, Pi.zero_apply,
    _root_.sub_apply, _root_.zero_apply, euclideanSecondOrderCoeff_apply,
    euclideanFirstOrderCoeff_apply, euclideanZerothOrderCoeff_apply, zero_mul,
    Finset.sum_const_zero]
  ring

end Freezing

/-! ### Localization by cutoffs -/

section Cutoff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ} {hab : a < b}

/-- A localization `χ u` vanishes where the cutoff `χ` does. -/
private theorem mul_apply_eq_zero {χ u : ParabolicC2HolderSpace α E ℝ hab} (hα : α ≤ 1)
    {q : slab (E := E) a b} (h : χ q = 0) :
    (ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u q = 0 := by
  simp [h]

/-- The local bound behind the patching argument. If the localization `w = χ u` satisfies
`‖w‖ ≤ C₁ (‖P w‖ + ‖w‖_∞)` and the commutator `P w - χ P u` is at most `η ‖u‖ + K ‖u‖_∞`, then
`‖w‖ ≤ C₁ (24 C_χ ‖P u‖ + η ‖u‖ + (K + 1) ‖u‖_∞)`, where `C_χ` bounds the norm of the cutoff. -/
private theorem norm_mul_le_of_norm_le (hα : α ≤ 1)
    (P : ParabolicC2HolderSpace α E ℝ hab →L[ℝ] HolderSpace α (slab (E := E) a b) ℝ)
    {χ u : ParabolicC2HolderSpace α E ℝ hab} {C₁ Cχ η K : ℝ} (hC₁ : 0 ≤ C₁)
    (hχ : ∀ q, χ q ∈ Icc 0 1) (hχn : ‖χ‖ ≤ Cχ)
    (hw : ‖(ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u‖ ≤
      C₁ * (‖P ((ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u)‖ +
        ‖valueL ((ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u)‖))
    (hc : ‖P ((ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u) -
      (ContinuousLinearMap.mul ℝ ℝ).compHolder₂ (valueHolderL hα χ) (P u)‖ ≤
        η * ‖u‖ + K * ‖valueL u‖) :
    ‖(ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u‖ ≤
      C₁ * (24 * Cχ * ‖P u‖ + η * ‖u‖ + (K + 1) * ‖valueL u‖) := by
  -- Multiplication by the cutoff costs at most its `C_b^{α,α/2}` norm, which is `≤ 24 ‖χ‖`.
  have hQ : ‖valueHolderL hα χ‖ ≤ 24 * Cχ :=
    (norm_valueHolderL_le_mul hα χ).trans (mul_le_mul_of_nonneg_left hχn (by norm_num))
  have hχP := ((ContinuousLinearMap.mul ℝ ℝ).norm_compHolder₂_apply_le
    (valueHolderL hα χ) (P u)).trans (mul_le_mul_of_nonneg_right (mul_le_mul
      (ContinuousLinearMap.opNorm_mul_le ℝ ℝ) hQ (norm_nonneg _) zero_le_one) (norm_nonneg (P u)))
  have hPw := norm_sub_norm_le (P ((ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u))
    ((ContinuousLinearMap.mul ℝ ℝ).compHolder₂ (valueHolderL hα χ) (P u))
  -- Multiplication by a cutoff with values in `[0, 1]` does not increase the supremum norm.
  have hχ₁ : ‖valueL χ‖ ≤ 1 := (BoundedContinuousFunction.norm_le zero_le_one).2 fun q ↦ by
    rw [valueL_apply, Real.norm_of_nonneg (hχ q).1]
    exact (hχ q).2
  have hv := ((ContinuousLinearMap.mul ℝ ℝ).norm_valueL_compParabolicC2Holder₂_le hα χ u).trans
    (mul_le_of_le_one_left (norm_nonneg _) ((mul_le_mul (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)
      hχ₁ (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)))
  refine hw.trans (mul_le_mul_of_nonneg_left ?_ hC₁)
  linarith

end Cutoff

/-! ### The Schauder estimate -/

section Schauder

variable {lam Lam : ℝ}

/-- Coefficients with Hölder norms at most `K` give second- and first-order coefficient fields of
norms at most constants `KA` and `KB` depending only on `n` and `K` (namely `n² K` and `n K`). -/
private theorem exists_norm_euclideanCoeff_le (K : ℝ≥0) :
    ∃ KA KB : ℝ, 0 ≤ KA ∧ 0 ≤ KB ∧ ∀ {t₀ t₁ : ℝ}
      {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
      {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ},
      (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) →
        ‖euclideanSecondOrderCoeff a‖ ≤ KA ∧ ‖euclideanFirstOrderCoeff b‖ ≤ KB :=
  ⟨Fintype.card ι * (Fintype.card ι * K), Fintype.card ι * K, by positivity, by positivity,
    fun ha hb ↦ ⟨(norm_euclideanSecondOrderCoeff_le _).trans <| by
      simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦
        Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ ha i j,
    (norm_euclideanFirstOrderCoeff_le _).trans <| by
      simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hb i⟩⟩

/-- **The Schauder estimate for maps of small support.** For `0 < α < 1`, ellipticity constants
`λ > 0` and `Λ`, a bound `K` on the Hölder norms of the coefficients and a bound `T₀` on the
horizon, there are a radius `r₀ > 0` and a constant `C` with the following property. On
`ℝⁿ × [0, T]`, `T ≤ T₀`, every `w ∈ C_b^{2+α,1+α/2}` vanishing outside the closed parabolic ball
of radius `r ≤ r₀` about some point satisfies
`‖w‖_{2+α,par} ≤ C (‖P w‖_{α,par} + ‖w(·, 0)‖_{2,α} + ‖w‖_∞)`. -/
theorem exists_norm_le_euclideanParabolicOperatorL_add_of_forall_lt_dist (hα₀ : 0 < α)
    (hα₁ : α < 1) (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ r₀ > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ),
        (∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
        (∀ p (ξ : EuclideanSpace ℝ ι),
          (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ∀ (w : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT)
          (p : slab (E := EuclideanSpace ℝ ι) 0 T) {r : ℝ}, 0 ≤ r → r ≤ r₀ →
          (∀ q, r < dist q p → w q = 0) →
          ‖w‖ ≤ C * (‖euclideanParabolicOperatorL hα₁.le a b c w‖ +
            ‖w.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖ + ‖valueL w‖) := by
  obtain ⟨C₀, hC₀, hconst⟩ :=
    exists_norm_le_euclideanParabolicOperatorL_const (ι := ι) hα₀ hα₁ (Lam := Lam) hlam
  -- The constant-coefficient estimate holds with the constant `Ct` on every horizon `T ≤ T₀`.
  obtain ⟨Ct, hCt₀, hCt⟩ : ∃ Ct : ℝ, 0 ≤ Ct ∧ Ct = C₀ * (1 + T₀) := ⟨_, by positivity, rfl⟩
  obtain ⟨KA, KB, hKA₀, hKB₀, hcoeff⟩ := exists_norm_euclideanCoeff_le (ι := ι) (α := α) K
  -- Smallness parameters: each absorbed error costs at most a quarter of `‖w‖`.
  have hη₁ : 0 < 1 / (4 * (Ct + 1)) := by positivity
  have hη₂ : 0 < 1 / (4 * (Ct + 1) * (KB + K + 1)) := by positivity
  obtain ⟨r₀, hr₀, Cf, hfreeze⟩ := exists_norm_spatialOperatorL_sub_const_apply_le
    (E := EuclideanSpace ℝ ι) (F := ℝ) hα₀ hα₁.le KA.toNNReal hη₁
  obtain ⟨Kl, hKl⟩ := exists_norm_valueHolderL_add_norm_spatialFDerivHolderL_le
    (E := EuclideanSpace ℝ ι) (F := ℝ) hα₁ hη₂
  have hCf : 0 ≤ max Cf 0 := le_max_right _ _
  have hKl₀ : 0 ≤ max Kl 0 := le_max_right _ _
  refine ⟨r₀, hr₀, 2 * Ct * (1 + max Cf 0 + (KB + K) * max Kl 0), by positivity,
    fun T hT hTT₀ a b c ha ha' hak hbk hck w p r hr hrr hw ↦ ?_⟩
  obtain ⟨hA, hB⟩ := hcoeff hak hbk
  have hC := (norm_euclideanZerothOrderCoeff_le c).trans hck
  -- The constant-coefficient estimate for the operator frozen at `p`.
  have h₀ := hconst (Matrix.of fun i j ↦ a i j p) (ha p) (ha' p) T hT w
  simp only [Matrix.of_apply] at h₀
  rw [euclideanParabolicOperatorL_const_apply_eq hα₁.le a b c p w] at h₀
  have hTC : C₀ * (1 + T) ≤ Ct := by
    rw [hCt]
    gcongr
  -- The principal error is small, since `a` oscillates little where `D²w` lives.
  have hF := hfreeze (euclideanSecondOrderCoeff a) p w (r := r)
    (by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hKA₀]
      simpa only [HolderSpace.coe_toBoundedContinuousFunction] using
        (HolderSpace.nnHolderNorm_le _).trans hA)
    hr hrr fun q hq ↦ spatialSecondFDerivL_eq_zero_of_forall_lt_dist hw q hq
  -- The lower-order terms are absorbed by interpolation.
  have hL : ‖spatialOperatorL hα₁.le 0 (euclideanFirstOrderCoeff b)
      (euclideanZerothOrderCoeff c) w‖ ≤
      (KB + K) * (1 / (4 * (Ct + 1) * (KB + K + 1)) * ‖w‖ + max Kl 0 * ‖valueL w‖) := by
    refine (norm_spatialOperatorL_apply_le hα₁.le w).trans ?_
    have hKl' : ‖valueHolderL hα₁.le w‖ + ‖spatialFDerivHolderL hα₁.le w‖ ≤
        1 / (4 * (Ct + 1) * (KB + K + 1)) * ‖w‖ + max Kl 0 * ‖valueL w‖ :=
      (hKl w).trans (by gcongr; exact le_max_left Kl 0)
    rw [norm_zero, zero_mul, zero_add]
    calc
      _ ≤ KB * ‖spatialFDerivHolderL hα₁.le w‖ + K * ‖valueHolderL hα₁.le w‖ :=
        add_le_add (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hC (norm_nonneg _))
      _ ≤ (KB + K) * (‖valueHolderL hα₁.le w‖ + ‖spatialFDerivHolderL hα₁.le w‖) := by
        rw [add_mul, mul_add, mul_add]
        linarith [mul_nonneg hKB₀ (norm_nonneg (valueHolderL hα₁.le w)),
          mul_nonneg K.coe_nonneg (norm_nonneg (spatialFDerivHolderL hα₁.le w))]
      _ ≤ _ := mul_le_mul_of_nonneg_left hKl' (by positivity)
  -- Combine and absorb.
  have hF' := hF.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_max_left Cf 0)
    (norm_nonneg (valueL w))))
  have h₁ := h₀.trans (mul_le_mul hTC (add_le_add norm_add₃_le le_rfl) (by positivity) hCt₀)
  have hq₁ : Ct * (1 / (4 * (Ct + 1))) ≤ 1 / 4 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hq₂ : Ct * ((KB + K) * (1 / (4 * (Ct + 1) * (KB + K + 1)))) ≤ 1 / 4 := by
    have hk₀ : 0 ≤ KB + K := add_nonneg hKB₀ K.coe_nonneg
    have := mul_le_mul (le_add_of_nonneg_right zero_le_one : Ct ≤ Ct + 1)
      (le_add_of_nonneg_right zero_le_one : KB + K ≤ KB + K + 1) hk₀ (by positivity)
    rw [mul_one_div, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  -- Each error contributes at most a quarter of `‖w‖`, which is moved to the left.
  have hk₀ : 0 ≤ KB + K := add_nonneg hKB₀ K.coe_nonneg
  linarith [mul_le_mul_of_nonneg_left hF' hCt₀, mul_le_mul_of_nonneg_left hL hCt₀,
    mul_le_mul_of_nonneg_right hq₁ (norm_nonneg w), mul_le_mul_of_nonneg_right hq₂ (norm_nonneg w),
    mul_nonneg (mul_nonneg hCt₀ (add_nonneg hCf (mul_nonneg hk₀ hKl₀)))
      (add_nonneg (norm_nonneg (euclideanParabolicOperatorL hα₁.le a b c w))
        (norm_nonneg (w.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩))),
    mul_nonneg hCt₀ (norm_nonneg (valueL w))]

/-- **The Schauder estimate with zero initial values.** Localizing the estimate for maps of small
support by cutoffs centred at every point gives `‖u‖_{2+α,par} ≤ C (‖P u‖_{α,par} + ‖u‖_∞)` for
every `u ∈ C_b^{2+α,1+α/2}` with `u(·, 0) = 0`. -/
private theorem exists_norm_le_euclideanParabolicOperatorL_add_of_spatialTrace_eq_zero
    (hα₀ : 0 < α) (hα₁ : α < 1) (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ),
        (∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
        (∀ p (ξ : EuclideanSpace ℝ ι),
          (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ∀ u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
          u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩ = 0 →
          ‖u‖ ≤ C * (‖euclideanParabolicOperatorL hα₁.le a b c u‖ + ‖valueL u‖) := by
  obtain ⟨r₀, hr₀, C₁, hC₁, hloc⟩ :=
    exists_norm_le_euclideanParabolicOperatorL_add_of_forall_lt_dist (ι := ι) hα₀ hα₁
      (Lam := Lam) hlam K T₀
  -- Cutoffs one on parabolic balls of radius `r₀ / 4` and vanishing beyond radius `r₀`.
  obtain ⟨Cχ, hCχ, hfam⟩ := exists_cutoff_family (E := EuclideanSpace ℝ ι) hα₁.le
    (ρ := r₀ / 2) (by positivity)
  obtain ⟨Cp, hCp₀, hCp⟩ : ∃ Cp : ℝ, 0 < Cp ∧ Cp = 6 + 4 * (r₀ / 2 / 2) ^ (-(α : ℝ)) :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨KA, KB, hKA₀, hKB₀, hcoeff⟩ := exists_norm_euclideanCoeff_le (ι := ι) (α := α) K
  -- The commutator with a cutoff costs a small multiple of `‖u‖` and a multiple of `‖u‖_∞`.
  obtain ⟨K₃, hK₃, hcomm⟩ := exists_norm_parabolicOperatorL_mul_sub_mul_parabolicOperatorL_le
    (E := EuclideanSpace ℝ ι) hα₁ (M := Cχ + KA * Cχ + (KB + 2 * KA) * (24 * Cχ))
    (by positivity) (η := 1 / (2 * Cp * (C₁ + 1))) (by positivity)
  refine ⟨2 * Cp * C₁ * (24 * Cχ + (K₃ + 1) + 1), by positivity,
    fun T hT hTT₀ a b c ha ha' hak hbk hck u hu ↦ ?_⟩
  obtain ⟨χ, hχn, hχmem, hχone, hχzero⟩ := hfam 0 T hT
  obtain ⟨hA, hB⟩ := hcoeff hak hbk
  -- The local bound for the localization `χ_p u` at every point `p`.
  have hlocal : ∀ p, ‖(ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα₁.le (χ p) u‖ ≤
      C₁ * (24 * Cχ * ‖euclideanParabolicOperatorL hα₁.le a b c u‖ +
        1 / (2 * Cp * (C₁ + 1)) * ‖u‖ + (K₃ + 1) * ‖valueL u‖) := by
    intro p
    have hχd : ‖spatialFDerivHolderL hα₁.le (χ p)‖ ≤ 24 * Cχ :=
      (norm_spatialFDerivHolderL_le_mul hα₁.le (χ p)).trans
        (mul_le_mul_of_nonneg_left (hχn p) (by norm_num))
    have hχM : ‖timeDerivL (χ p)‖ + ‖euclideanSecondOrderCoeff a‖ *
        ‖spatialSecondFDerivL (χ p)‖ + (‖euclideanFirstOrderCoeff b‖ +
          2 * ‖euclideanSecondOrderCoeff a‖) * ‖spatialFDerivHolderL hα₁.le (χ p)‖ ≤
        Cχ + KA * Cχ + (KB + 2 * KA) * (24 * Cχ) := by
      have ht := (norm_timeDerivL_le (χ p)).trans (hχn p)
      have hs := (norm_spatialSecondFDerivL_le (χ p)).trans (hχn p)
      exact add_le_add (add_le_add ht (mul_le_mul hA hs (norm_nonneg _) hKA₀))
        (mul_le_mul (add_le_add hB (mul_le_mul_of_nonneg_left hA zero_le_two)) hχd
          (norm_nonneg _) (by positivity))
    have hc := hcomm (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b)
      (euclideanZerothOrderCoeff c) (χ p) hχM u
    rw [← euclideanParabolicOperatorL_def] at hc
    have hw := hloc T hT hTT₀ a b c ha ha' hak hbk hck
      ((ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα₁.le (χ p) u) p hr₀.le le_rfl
      fun q hq ↦ mul_apply_eq_zero hα₁.le (hχzero p q (by linarith))
    rw [(ContinuousLinearMap.mul ℝ ℝ).spatialTrace_compParabolicC2Holder₂_eq_zero hα₁.le (χ p) hu,
      norm_zero, add_zero] at hw
    exact norm_mul_le_of_norm_le hα₁.le _ hC₁ (hχmem p) (hχn p) hw hc
  -- Patch the local bounds and absorb.
  have hpatch : ‖u‖ ≤ (6 + 4 * (r₀ / 2 / 2) ^ (-(α : ℝ))) *
      (C₁ * (24 * Cχ * ‖euclideanParabolicOperatorL hα₁.le a b c u‖ +
        1 / (2 * Cp * (C₁ + 1)) * ‖u‖ + (K₃ + 1) * ‖valueL u‖)) :=
    norm_le_of_forall_eqOn_ball (r := r₀ / 2 / 2) (by positivity) fun p ↦
      ⟨_, hlocal p, fun q hq ↦ by simp [hχone p q hq]⟩
  rw [← hCp] at hpatch
  have hη : Cp * C₁ * (1 / (2 * Cp * (C₁ + 1))) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  -- The `‖u‖` term on the right costs at most half of `‖u‖`, which is moved to the left.
  have hc : 0 ≤ Cp * C₁ := mul_nonneg hCp₀.le hC₁
  have hP₀ := norm_nonneg (euclideanParabolicOperatorL hα₁.le a b c u)
  have hV₀ := norm_nonneg (valueL u)
  have hA₀ : (0 : ℝ) ≤ 24 * Cχ := by positivity
  have hB₀ : 0 ≤ K₃ + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hη (norm_nonneg u), mul_nonneg hc (mul_nonneg hA₀ hV₀),
    mul_nonneg hc (mul_nonneg hB₀ hP₀), mul_nonneg hc hP₀, mul_nonneg hc hV₀]

/-- **The global Schauder estimate with the supremum norm.** For `0 < α < 1`, ellipticity
constants `λ > 0` and `Λ`, a bound `K` on the Hölder norms of the coefficients and a bound `T₀` on
the horizon, there is a constant `C` such that on `ℝⁿ × [0, T]`, `T ≤ T₀`, every
`u ∈ C_b^{2+α,1+α/2}` satisfies
`‖u‖_{2+α,par} ≤ C (‖P u‖_{α,par} + ‖u(·, 0)‖_{2,α} + ‖u‖_∞)`.
No sign condition on `c` is needed. -/
theorem exists_norm_le_euclideanParabolicOperatorL_add (hα₀ : 0 < α) (hα₁ : α < 1)
    (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ),
        (∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
        (∀ p (ξ : EuclideanSpace ℝ ι),
          (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ∀ u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
          ‖u‖ ≤ C * (‖euclideanParabolicOperatorL hα₁.le a b c u‖ +
            ‖u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖ + ‖valueL u‖) := by
  obtain ⟨C₂, hC₂, hzero⟩ :=
    exists_norm_le_euclideanParabolicOperatorL_add_of_spatialTrace_eq_zero (ι := ι) hα₀ hα₁
      (Lam := Lam) hlam K T₀
  obtain ⟨Cs, hCs, hsol⟩ :=
    exists_solutionOperator_euclideanParabolicOperatorL_const_prod (ι := ι) hα₀ hα₁ (Lam := Lam)
      hlam
  obtain ⟨KA, KB, hKA₀, hKB₀, hcoeff⟩ := exists_norm_euclideanCoeff_le (ι := ι) (α := α) K
  -- `N` bounds the operator norm of `P`, and `Cz` the solution operator of the frozen problem.
  obtain ⟨N, hN₀, hN⟩ : ∃ N : ℝ, 0 ≤ N ∧ N = 1 + KA + 24 * (KB + K) := ⟨_, by positivity, rfl⟩
  refine ⟨C₂ + (C₂ * (N + 1) + 1) * (Cs * (1 + T₀)), by positivity,
    fun T hT hTT₀ a b c ha ha' hak hbk hck u ↦ ?_⟩
  -- Subtract the solution `z` of the problem frozen at a point with the initial datum of `u`.
  obtain ⟨L, hL, hLiff⟩ := hsol (Matrix.of fun i j ↦ a i j (slabMk 0 ⟨0, left_mem_Icc.2 hT.le⟩))
    (ha _) (ha' _) T hT
  obtain ⟨z, hzL⟩ : ∃ z, z = L (0, u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩) := ⟨_, rfl⟩
  have hz : z.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩ = u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩ :=
    ((hLiff _ _ z).2 hzL).2
  have hzn : ‖z‖ ≤ Cs * (1 + T₀) * ‖u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖ := by
    have h := L.le_opNorm (0, u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩)
    rw [← hzL, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)] at h
    refine h.trans ?_
    refine mul_le_mul_of_nonneg_right (hL.trans ?_) (norm_nonneg _)
    gcongr
  -- The difference has zero initial values.
  have hv := hzero T hT hTT₀ a b c ha ha' hak hbk hck (u - z)
    (by rw [spatialTrace_sub, hz, sub_self])
  have hP : ‖euclideanParabolicOperatorL (ht := hT) hα₁.le a b c‖ ≤ N := by
    rw [euclideanParabolicOperatorL_def, hN]
    refine (norm_parabolicOperatorL_le hα₁.le).trans ?_
    obtain ⟨hA, hB⟩ := hcoeff hak hbk
    have hC := (norm_euclideanZerothOrderCoeff_le c).trans hck
    linarith
  have hPv : ‖euclideanParabolicOperatorL hα₁.le a b c (u - z)‖ ≤
      ‖euclideanParabolicOperatorL hα₁.le a b c u‖ + N * ‖z‖ := by
    rw [map_sub]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl
      (((euclideanParabolicOperatorL hα₁.le a b c).le_opNorm z).trans
        (mul_le_mul_of_nonneg_right hP (norm_nonneg z))))
  have hVv : ‖valueL (u - z)‖ ≤ ‖valueL u‖ + ‖z‖ := by
    rw [map_sub]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_valueL_le z))
  have hX : ‖u‖ ≤ ‖u - z‖ + ‖z‖ := by
    simpa using norm_add_le (u - z) z
  -- Combine the four bounds.
  have hk : 0 ≤ C₂ * (N + 1) + 1 := by positivity
  have hP₀ := norm_nonneg (euclideanParabolicOperatorL hα₁.le a b c u)
  have hV₀ := norm_nonneg (valueL u)
  have hG₀ := norm_nonneg (u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩)
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add hPv hVv) hC₂,
    mul_le_mul_of_nonneg_left hzn hk, mul_nonneg hC₂ hG₀,
    mul_nonneg (mul_nonneg hk (by positivity : (0 : ℝ) ≤ Cs * (1 + T₀))) hP₀,
    mul_nonneg (mul_nonneg hk (by positivity : (0 : ℝ) ≤ Cs * (1 + T₀))) hV₀]

/-- **The global Schauder estimate.** For `0 < α < 1`, ellipticity constants `λ > 0` and `Λ`, a
bound `K` on the Hölder norms of the coefficients and a bound `T₀` on the horizon, there is a
constant `C` such that on `ℝⁿ × [0, T]`, `T ≤ T₀`, every `u ∈ C_b^{2+α,1+α/2}` satisfies
`‖u‖_{2+α,par} ≤ C (‖P u‖_{α,par} + ‖u(·, 0)‖_{2,α})`,
where `P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`. In particular `u` is determined by `P u` and
`u(·, 0)`, with a bound uniform over the coefficients. -/
theorem exists_norm_le_euclideanParabolicOperatorL (hα₀ : 0 < α) (hα₁ : α < 1)
    (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ),
        (∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
        (∀ p (ξ : EuclideanSpace ℝ ι),
          (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ∀ u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
          ‖u‖ ≤ C * (‖euclideanParabolicOperatorL hα₁.le a b c u‖ +
            ‖u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖) := by
  obtain ⟨C₃, hC₃, hest⟩ :=
    exists_norm_le_euclideanParabolicOperatorL_add (ι := ι) hα₀ hα₁ (Lam := Lam) hlam K T₀
  obtain ⟨E₀, hE₀, hE⟩ : ∃ E₀ : ℝ, 0 ≤ E₀ ∧ E₀ = Real.exp (K * T₀) * (1 + T₀) :=
    ⟨_, by positivity, rfl⟩
  refine ⟨C₃ * (1 + E₀), by positivity, fun T hT hTT₀ a b c ha ha' hak hbk hck u ↦ ?_⟩
  set P := ‖euclideanParabolicOperatorL hα₁.le a b c u‖
  set G := ‖u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖
  -- The comparison principle bounds the supremum of `u` by its initial values and `P u`.
  have hV : ‖valueL u‖ ≤ E₀ * (P + G) := by
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun p ↦ ?_
    have hmax := abs_le_exp_mul_mul_add_mul_of_abs_euclideanParabolicOperatorL_le hα₁.le
      (b := b) (fun q ξ ↦ (mul_nonneg hlam.le (sq_nonneg ‖ξ‖)).trans (ha q ξ))
      (fun q ↦ (le_abs_self _).trans ((HolderSpace.norm_apply_le c q).trans hck))
      K.coe_nonneg u (fun q ↦ by
        simpa only [Real.norm_eq_abs] using HolderSpace.norm_apply_le
          (euclideanParabolicOperatorL hα₁.le a b c u) q)
      (fun x ↦ by simpa using CkHolderSpace.norm_apply_le (u.spatialTrace ⟨0, _⟩) x) p
    obtain ⟨ht₀, htT⟩ := (slabTime p).2
    have htT₀ : (slabTime p : ℝ) ≤ T₀ := htT.trans (by exact_mod_cast hTT₀)
    rw [valueL_apply, Real.norm_eq_abs, hE]
    refine hmax.trans ?_
    rw [sub_zero]
    have hP₀ : 0 ≤ P := norm_nonneg _
    have hG₀ : 0 ≤ G := norm_nonneg _
    have hexp : Real.exp (K * (slabTime p : ℝ)) ≤ Real.exp (K * T₀) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htT₀ K.coe_nonneg)
    have hlin : G + (slabTime p : ℝ) * P ≤ (1 + T₀) * (P + G) := by
      nlinarith [mul_le_mul_of_nonneg_right htT₀ hP₀, T₀.coe_nonneg]
    calc
      _ ≤ Real.exp (K * T₀) * (G + (slabTime p : ℝ) * P) :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
      _ ≤ Real.exp (K * T₀) * ((1 + T₀) * (P + G)) :=
        mul_le_mul_of_nonneg_left hlin (Real.exp_pos _).le
      _ = _ := by ring
  have h := hest T hT hTT₀ a b c ha ha' hak hbk hck u
  have : 0 ≤ P := norm_nonneg _
  have : 0 ≤ G := norm_nonneg _
  calc
    ‖u‖ ≤ C₃ * (P + G + ‖valueL u‖) := h
    _ ≤ C₃ * (P + G + E₀ * (P + G)) := by gcongr
    _ = C₃ * (1 + E₀) * (P + G) := by ring

end Schauder

end TauCeti.ParabolicC2HolderSpace
