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
# The Schauder estimate for parabolic equations with variable coefficients

Let `P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u` on the slab `ℝⁿ × [0, T]`, with coefficients `aⁱʲ`,
`bⁱ`, `c` in the bounded parabolic Hölder space `C_b^{α,α/2}` for some `0 < α < 1`, uniformly
elliptic, `lam ‖ξ‖² ≤ aⁱʲ(z) ξᵢ ξⱼ` with `0 < lam`, and with Hölder norms at most `K`. No symmetry
of `a` and no sign of `c` is assumed. For every maximal horizon `T₀` there is a constant `C`,
depending only on the dimension, `α`, `lam`, `K` and `T₀`, such that for every `0 < T ≤ T₀` and
every `u` in the order-two space `C_b^{2+α,1+α/2}`,

`‖u‖_{2+α,par} ≤ C (‖P u‖_{α,par} + ‖u(·, 0)‖_{2,α})`

(`TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL`). This is the
global a priori estimate on which the method of continuity from the heat operator rests: it is
uniform along every path of coefficients with the same ellipticity and coefficient bounds, so
invertibility of `u ↦ (P u, u(·, 0))` passes from the heat operator to `P`. The constant cannot
be independent of `T₀`: `u = t` solves `∂ₜu = 1` with `u(·, 0) = 0`, and its norm is at least
`T`.

## The proof

1. *Small support.* If `v` has zero initial trace and its Hessian vanishes outside a parabolic
   ball of small radius `r₀` about `p`, the coefficients are frozen at `p`. The
   constant-coefficient estimate
   (`TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL_const`) applies to
   the frozen operator, the freezing error
   (`TauCeti.ParabolicC2HolderSpace.exists_norm_spatialOperatorL_sub_const_apply_le`) and the
   lower-order terms
   (`TauCeti.ParabolicC2HolderSpace.exists_norm_valueHolderL_add_norm_spatialFDerivHolderL_le`)
   are absorbed, and `‖v‖ ≤ C ‖P v‖ + C' ‖v‖_∞`.
2. *Zero initial trace.* The localizations `χ_p u` by the cutoffs
   `TauCeti.ParabolicC2HolderSpace.exists_cutoff_family` satisfy step 1, and
   `P (χ_p u) = χ_p P u + [P, χ_p] u`, where the commutator involves only `u` and `D_x u`
   (`exists_norm_parabolicOperatorL_mul_sub_mul_parabolicOperatorL_le`).
   Patching the localizations
   (`TauCeti.ParabolicC2HolderSpace.norm_le_of_forall_eqOn_ball`) and absorbing the commutator
   gives `‖u‖ ≤ C (‖P u‖ + ‖u‖_∞)`.
3. *Arbitrary initial trace.* Subtracting the solution of the heat equation with the same initial
   datum reduces to step 2, giving
   `‖u‖ ≤ C (‖P u‖ + ‖u(·, 0)‖_{2,α} + ‖u‖_∞)`
   (`TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL_add_valueL`).
4. *The supremum norm.* The comparison principle bounds
   `‖u‖_∞ ≤ exp (K T) (‖u(·, 0)‖_∞ + T ‖P u‖_∞)`
   (`abs_le_exp_mul_mul_add_mul_of_abs_euclideanParabolicOperatorL_le`).

## Main declarations

* `TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL_add_valueL`: the
  Schauder estimate up to the supremum norm.
* `TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL`: the global
  Schauder estimate.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 3 (localization
  and a priori estimates).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.1 (freezing the coefficients and passing from local to global Schauder estimates).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8 (parabolic Schauder estimates).
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set Metric ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ℝ≥0}

-- Reuse the operator module's Hessian shortcuts for instance search in coefficient types.
attribute [local instance] instNormedAddCommGroupContinuousLinearMapRealId
  instNormedSpaceRealContinuousLinearMapId

/-- Freezing the principal coefficients at `p` and dropping the lower-order terms changes the
operator `P = ∂ₜ - 𝒜·D_x² - ℬ·D_x - 𝒞` by the frozen principal error and the lower-order part. -/
private theorem euclideanParabolicOperatorL_const_apply_eq_add (hα : α ≤ 1) {T : ℝ≥0}
    {hT : (0 : ℝ) < T} (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    {𝒜 : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T)
      ((EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) →L[ℝ] ℝ)}
    {ℬ : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ((EuclideanSpace ℝ ι →L[ℝ] ℝ) →L[ℝ] ℝ)}
    {𝒞 : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) (ℝ →L[ℝ] ℝ)}
    (h𝒜 : euclideanSecondOrderCoeff a = 𝒜) (hℬ : euclideanFirstOrderCoeff b = ℬ)
    (h𝒞 : euclideanZerothOrderCoeff c = 𝒞) (p : slab (E := EuclideanSpace ℝ ι) 0 T)
    (v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) :
    euclideanParabolicOperatorL hα
        (fun i j ↦ HolderSpace.const ((Matrix.of fun i j ↦ a i j p) i j)) 0 0 v =
      parabolicOperatorL hα 𝒜 ℬ 𝒞 v + spatialOperatorL hα (𝒜 - HolderSpace.const (𝒜 p)) 0 0 v +
        spatialOperatorL hα 0 ℬ 𝒞 v := by
  subst h𝒜 hℬ h𝒞
  ext q
  simp only [euclideanParabolicOperatorL_apply, parabolicOperatorL_apply, HolderSpace.add_apply,
    spatialOperatorL_apply, HolderSpace.sub_apply, _root_.sub_apply, HolderSpace.const_apply,
    euclideanSecondOrderCoeff_apply, euclideanFirstOrderCoeff_apply,
    euclideanZerothOrderCoeff_apply, Matrix.of_apply, HolderSpace.zero_apply, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, _root_.zero_apply, add_zero, zero_add]
  ring

/-- **The estimate for functions of small support.** Freezing the principal coefficients at `p`
and absorbing the lower-order terms by interpolation, a function with zero initial trace whose
Hessian vanishes outside a small parabolic ball about `p` satisfies
`‖v‖_{2+α,par} ≤ C ‖P v‖_{α,par} + C' ‖v‖_∞`. -/
private theorem exists_norm_le_of_spatialSecondFDerivL_eq_zero (hα₀ : 0 < α) (hα₁ : α < 1)
    {lam K T₀ : ℝ} (hlam : 0 < lam) :
    ∃ r₀ > 0, ∃ C : ℝ, 0 ≤ C ∧ ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), (T : ℝ) ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ),
      (∀ p (ξ : EuclideanSpace ℝ ι),
        lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
      (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
      ∀ (p : slab (E := EuclideanSpace ℝ ι) 0 T)
        (v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT),
        v.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩ = 0 →
        (∀ q, r₀ < dist q p → spatialSecondFDerivL v q = 0) →
        ‖v‖ ≤ C * ‖euclideanParabolicOperatorL hα₁.le a b c v‖ + C' * ‖valueL v‖ := by
  set n : ℝ := (Fintype.card ι : ℝ)
  set K' := max K 0
  set MA := n * n * K'
  set MB := n * K'
  have hK' : 0 ≤ K' := le_max_right _ _
  have hMA : 0 ≤ MA := by positivity
  have hMB : 0 ≤ MB := by positivity
  -- The constant-coefficient estimate, uniform over the frozen matrices.
  obtain ⟨C₀, hC₀, hconst⟩ :=
    exists_norm_le_euclideanParabolicOperatorL_const (ι := ι) hα₀ hα₁ (Lam := MA) hlam
  set C₁ := C₀ * (1 + max T₀ 0)
  have hC₁ : 0 ≤ C₁ := by positivity
  -- The freezing error and the lower-order terms are absorbed with the small constant `η`.
  set η := (4 * (C₁ + 1))⁻¹
  have hη : 0 < η := by positivity
  obtain ⟨r₀, hr₀, Cf, hfreeze⟩ := exists_norm_spatialOperatorL_sub_const_apply_le
    (E := EuclideanSpace ℝ ι) (F := ℝ) hα₀ hα₁.le MA.toNNReal hη
  obtain ⟨Kl, hKl⟩ := exists_norm_valueHolderL_add_norm_spatialFDerivHolderL_le
    (E := EuclideanSpace ℝ ι) (F := ℝ) hα₁ (η := η / (MB + K' + 1)) (by positivity)
  set K₁ := max Cf 0 + (MB + K') * max Kl 0
  refine ⟨r₀, hr₀, 2 * C₁, by positivity, 2 * C₁ * K₁, by positivity,
    fun T hT hTT₀ a b c ha hab hb hc p v hv0 hvsupp ↦ ?_⟩
  obtain ⟨𝒜, h𝒜⟩ : ∃ A, euclideanSecondOrderCoeff a = A := ⟨_, rfl⟩
  obtain ⟨ℬ, hℬ⟩ : ∃ B, euclideanFirstOrderCoeff b = B := ⟨_, rfl⟩
  obtain ⟨𝒞, h𝒞⟩ : ∃ C, euclideanZerothOrderCoeff c = C := ⟨_, rfl⟩
  have hA : ‖𝒜‖ ≤ MA := h𝒜 ▸ norm_euclideanSecondOrderCoeff_le_of_norm_le hab
  have hB : ‖ℬ‖ ≤ MB := hℬ ▸ norm_euclideanFirstOrderCoeff_le_of_norm_le hb
  have hC : ‖𝒞‖ ≤ K' :=
    h𝒞 ▸ (norm_euclideanZerothOrderCoeff_le c).trans (hc.trans (le_max_left _ _))
  have hAsemi : nnHolderNorm α (𝒜 : slab (E := EuclideanSpace ℝ ι) 0 T → _) ≤ MA.toNNReal := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hMA]
    have h := HolderSpace.nnHolderNorm_le 𝒜
    rw [HolderSpace.coe_toBoundedContinuousFunction] at h
    exact h.trans hA
  have hC₀T : C₀ * (1 + T) ≤ C₁ :=
    mul_le_mul_of_nonneg_left (by linarith [le_max_left T₀ 0]) hC₀
  obtain ⟨P, hPdef⟩ : ∃ P, euclideanParabolicOperatorL (ht := hT) hα₁.le a b c = P := ⟨_, rfl⟩
  have hP : P = parabolicOperatorL hα₁.le 𝒜 ℬ 𝒞 := by
    rw [← hPdef, ← h𝒜, ← hℬ, ← h𝒞]
    exact euclideanParabolicOperatorL_def hα₁.le
  rw [hPdef]
  -- The constant-coefficient estimate with the coefficients frozen at `p`.
  have hentry : ∀ i j, |(Matrix.of fun i j ↦ a i j p) i j| ≤ K' := fun i j ↦ by
    rw [Matrix.of_apply]
    exact ((Real.norm_eq_abs _).symm.trans_le (HolderSpace.norm_apply_le _ _)).trans
      ((hab i j).trans (le_max_left _ _))
  -- An entrywise bound on the frozen matrix bounds its quadratic form above.
  have hupper : ∀ ξ : EuclideanSpace ℝ ι,
      (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ ≤ MA * ‖ξ‖ ^ 2 := fun ξ ↦ by
    refine (PDE.toQuadraticForm'_le_norm_matrixBilinearForm_mul_sq _ ξ).trans
      (mul_le_mul_of_nonneg_right ((PDE.norm_matrixBilinearForm_le_sum_abs _).trans ?_)
        (sq_nonneg _))
    calc ∑ i, ∑ j, |(Matrix.of fun i j ↦ a i j p) i j| ≤ ∑ _i : ι, ∑ _j : ι, K' :=
          Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hentry i j
      _ = MA := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, MA, n]; ring
  have h0 := hconst (Matrix.of fun i j ↦ a i j p) (ha p) hupper T hT v
  rw [hv0, norm_zero, add_zero,
    euclideanParabolicOperatorL_const_apply_eq_add hα₁.le a b c h𝒜 hℬ h𝒞, ← hP] at h0
  -- The freezing error and the lower-order part.
  have hfr := hfreeze 𝒜 p v hAsemi hr₀.le le_rfl hvsupp
  have hlow : ‖spatialOperatorL hα₁.le 0 ℬ 𝒞 v‖ ≤
      η * ‖v‖ + (MB + K') * max Kl 0 * ‖valueL v‖ := by
    have h := norm_spatialOperatorL_apply_le (A := 0) (B := ℬ) (C := 𝒞) hα₁.le v
    rw [norm_zero, zero_mul, zero_add] at h
    have hk := (hKl v).trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (le_max_left Kl 0) (norm_nonneg (valueL v))))
    have hX := norm_nonneg (spatialFDerivHolderL hα₁.le v)
    have hY := norm_nonneg (valueHolderL hα₁.le v)
    have hsum : ‖ℬ‖ * ‖spatialFDerivHolderL hα₁.le v‖ + ‖𝒞‖ * ‖valueHolderL hα₁.le v‖ ≤
        (MB + K') * (‖valueHolderL hα₁.le v‖ + ‖spatialFDerivHolderL hα₁.le v‖) := by
      linarith only [mul_le_mul_of_nonneg_right hB hX, mul_le_mul_of_nonneg_right hC hY,
        mul_nonneg hMB hY, mul_nonneg hK' hX]
    have hfrac : (MB + K') * (η / (MB + K' + 1)) ≤ η := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      linarith only [hη]
    calc _ ≤ (MB + K') * (η / (MB + K' + 1) * ‖v‖ + max Kl 0 * ‖valueL v‖) :=
          h.trans (hsum.trans (mul_le_mul_of_nonneg_left hk (by positivity)))
      _ = (MB + K') * (η / (MB + K' + 1)) * ‖v‖ + (MB + K') * max Kl 0 * ‖valueL v‖ := by
          ring
      _ ≤ _ := by gcongr
  -- Combine and absorb the terms in `‖v‖`.
  have hP₀ : ‖P v + spatialOperatorL hα₁.le (𝒜 - HolderSpace.const (𝒜 p)) 0 0 v +
      spatialOperatorL hα₁.le 0 ℬ 𝒞 v‖ ≤ ‖P v‖ + K₁ * ‖valueL v‖ + 2 * η * ‖v‖ := by
    refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
    have hCf : Cf * ‖valueL v‖ ≤ max Cf 0 * ‖valueL v‖ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    simp only [K₁]
    linarith only [hfr, hlow, hCf]
  have hηC : C₁ * (2 * η) ≤ 1 / 2 := by
    rw [show C₁ * (2 * η) = C₁ / (C₁ + 1) / 2 by simp only [η]; field_simp; ring]
    have : C₁ / (C₁ + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    linarith
  have hv : ‖v‖ ≤ C₁ * (‖P v‖ + K₁ * ‖valueL v‖) + C₁ * (2 * η) * ‖v‖ := by
    calc ‖v‖ ≤ C₀ * (1 + T) * _ := h0
      _ ≤ C₁ * (‖P v‖ + K₁ * ‖valueL v‖ + 2 * η * ‖v‖) :=
          mul_le_mul hC₀T hP₀ (norm_nonneg _) hC₁
      _ = _ := by ring
  linarith only [hv, mul_le_mul_of_nonneg_right hηC (norm_nonneg v)]

section Cutoff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {t₀ t₁ : ℝ} {ht : t₀ < t₁}
  (hα : α ≤ 1) {χ u : ParabolicC2HolderSpace α E ℝ ht}

/-- Localizing by a cutoff with values in `[0, 1]` does not increase the supremum norm. -/
private theorem norm_valueL_mul_le (hχ : ∀ q, χ q ∈ Icc (0 : ℝ) 1) :
    ‖valueL ((ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u)‖ ≤ ‖valueL u‖ := by
  refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun q ↦ ?_
  rw [valueL_apply, ContinuousLinearMap.compParabolicC2Holder₂_apply,
    ContinuousLinearMap.mul_apply', norm_mul]
  have hq := (valueL u).norm_coe_le_norm q
  rw [valueL_apply] at hq
  calc ‖χ q‖ * ‖u q‖ ≤ 1 * ‖u q‖ := by
        gcongr
        rw [Real.norm_eq_abs, abs_of_nonneg (hχ q).1]
        exact (hχ q).2
    _ ≤ _ := by rwa [one_mul]

/-- Localizing by a cutoff preserves a vanishing spatial trace. -/
private theorem spatialTrace_mul_eq_zero {t : Icc t₀ t₁} (hu : u.spatialTrace t = 0) :
    ((ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u).spatialTrace t = 0 := by
  ext x
  have hx := congrArg (fun f : CkHolderSpace 2 α E ℝ ↦ f x) hu
  simp only [spatialTrace_apply, CkHolderSpace.coe_zero, Pi.zero_apply] at hx ⊢
  rw [ContinuousLinearMap.compParabolicC2Holder₂_apply, hx, map_zero]

/-- Localizing by a cutoff vanishing at parabolic distance at least `r` from `p` gives a Hessian
vanishing at distance greater than `r`. -/
private theorem spatialSecondFDerivL_mul_eq_zero {p : slab (E := E) t₀ t₁} {r : ℝ}
    (hχ : ∀ q, r ≤ dist q p → χ q = 0) (q : slab (E := E) t₀ t₁) (hq : r < dist q p) :
    spatialSecondFDerivL ((ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u) q = 0 :=
  spatialSecondFDerivL_eq_zero_of_forall_lt_dist (fun q' hq' ↦ by
    rw [ContinuousLinearMap.compParabolicC2Holder₂_apply, hχ q' hq'.le, map_zero,
      _root_.zero_apply]) q hq

end Cutoff

/-- **The estimate for functions of zero initial trace.** Localizing by cutoffs, applying the
estimate for functions of small support to each localization and patching gives
`‖u‖_{2+α,par} ≤ C (‖P u‖_{α,par} + ‖u‖_∞)` whenever `u(·, 0) = 0`. -/
private theorem exists_norm_le_of_spatialTrace_eq_zero (hα₀ : 0 < α) (hα₁ : α < 1)
    {lam K T₀ : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), (T : ℝ) ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ),
      (∀ p (ξ : EuclideanSpace ℝ ι),
        lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
      (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
      ∀ u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
        u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩ = 0 →
        ‖u‖ ≤ C * (‖euclideanParabolicOperatorL hα₁.le a b c u‖ + ‖valueL u‖) := by
  set n : ℝ := (Fintype.card ι : ℝ)
  set K' := max K 0
  set MA := n * n * K'
  set MB := n * K'
  have hK' : 0 ≤ K' := le_max_right _ _
  have hMA : 0 ≤ MA := by positivity
  have hMB : 0 ≤ MB := by positivity
  obtain ⟨r₀, hr₀, C₁, hC₁, C₂, hC₂, hsmall⟩ :=
    exists_norm_le_of_spatialSecondFDerivL_eq_zero (ι := ι) hα₀ hα₁ (K := K) (T₀ := T₀) hlam
  -- Cutoffs vanishing at parabolic distance `r₀`, so that the small-support estimate applies.
  set ρ := r₀ / 2
  have hρ : 2 * ρ = r₀ := by simp only [ρ]; ring
  obtain ⟨Cχ, hCχ, hχfam⟩ := exists_cutoff_family (E := EuclideanSpace ℝ ι) hα₁.le
    (ρ := ρ) (by positivity)
  set Cp := 6 + 4 * (ρ / 2) ^ (-(α : ℝ))
  have hCp : 0 < Cp := by positivity
  -- The localization error is absorbed by the patching with the small constant `η`.
  set M := Cχ * (1 + MA + 24 * (MB + 2 * MA))
  set η := (4 * Cp * (C₁ + 1))⁻¹
  obtain ⟨K₂, hK₂, hloc⟩ := exists_norm_parabolicOperatorL_mul_sub_mul_parabolicOperatorL_le
    (E := EuclideanSpace ℝ ι) hα₁ (M := M) (η := η) (by positivity) (by positivity)
  set K₃ := C₁ * K₂ + C₂
  have hK₃ : 0 ≤ K₃ := by positivity
  refine ⟨2 * Cp * (24 * C₁ * Cχ + K₃), by positivity,
    fun T hT hTT₀ a b c ha hab hb hc u hu ↦ ?_⟩
  obtain ⟨χ, hχn, hχmem, hχone, hχzero⟩ := hχfam 0 T hT
  obtain ⟨𝒜, h𝒜⟩ : ∃ A, euclideanSecondOrderCoeff a = A := ⟨_, rfl⟩
  obtain ⟨ℬ, hℬ⟩ : ∃ B, euclideanFirstOrderCoeff b = B := ⟨_, rfl⟩
  obtain ⟨𝒞, h𝒞⟩ : ∃ C, euclideanZerothOrderCoeff c = C := ⟨_, rfl⟩
  have hA : ‖𝒜‖ ≤ MA := h𝒜 ▸ norm_euclideanSecondOrderCoeff_le_of_norm_le hab
  have hB : ‖ℬ‖ ≤ MB := hℬ ▸ norm_euclideanFirstOrderCoeff_le_of_norm_le hb
  obtain ⟨P, hPdef⟩ : ∃ P, euclideanParabolicOperatorL (ht := hT) hα₁.le a b c = P := ⟨_, rfl⟩
  have hP : P = parabolicOperatorL hα₁.le 𝒜 ℬ 𝒞 := by
    rw [← hPdef, ← h𝒜, ← hℬ, ← h𝒞]
    exact euclideanParabolicOperatorL_def hα₁.le
  -- The estimate for each localization `χ p u`.
  have hlocal : ∀ p, ‖(ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα₁.le (χ p) u‖ ≤
      24 * C₁ * Cχ * ‖P u‖ + C₁ * η * ‖u‖ + K₃ * ‖valueL u‖ := by
    intro p
    have hs := hsmall T hT hTT₀ a b c ha hab hb hc p _ (spatialTrace_mul_eq_zero hα₁.le hu)
      (spatialSecondFDerivL_mul_eq_zero hα₁.le fun q hq ↦ hχzero p q (hρ ▸ hq))
    rw [hPdef] at hs
    have hsup := norm_valueL_mul_le hα₁.le (u := u) (hχmem p)
    -- The localized equation: `P (χ u) = χ P u + [P, χ] u`.
    have hPv : ‖P ((ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα₁.le (χ p) u)‖ ≤
        24 * Cχ * ‖P u‖ + (η * ‖u‖ + K₂ * ‖valueL u‖) := by
      rw [← add_sub_cancel ((ContinuousLinearMap.mul ℝ ℝ).compHolder₂
        (valueHolderL hα₁.le (χ p)) (P u)) (P _)]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · have h2 : ‖valueHolderL hα₁.le (χ p)‖ ≤ 24 * Cχ := by
          have := norm_valueHolderL_add_norm_spatialFDerivHolderL_le_mul hα₁.le (χ p)
          linarith only [this, norm_nonneg (spatialFDerivHolderL hα₁.le (χ p)), hχn p]
        calc _ ≤ ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖valueHolderL hα₁.le (χ p)‖ * ‖P u‖ :=
              (ContinuousLinearMap.mul ℝ ℝ).norm_compHolder₂_apply_le _ _
          _ ≤ 1 * (24 * Cχ) * ‖P u‖ := by
              gcongr
              exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ
          _ = _ := by ring
      · rw [hP]
        refine hloc 𝒜 ℬ 𝒞 (χ p) ?_ u
        have h1 := norm_valueHolderL_add_norm_spatialFDerivHolderL_le_mul hα₁.le (χ p)
        have hD : ‖spatialFDerivHolderL hα₁.le (χ p)‖ ≤ 24 * Cχ := by
          linarith only [h1, norm_nonneg (valueHolderL hα₁.le (χ p)), hχn p]
        have e1 := (norm_timeDerivL_le (χ p)).trans (hχn p)
        have e2 : ‖𝒜‖ * ‖spatialSecondFDerivL (χ p)‖ ≤ MA * Cχ :=
          mul_le_mul hA ((norm_spatialSecondFDerivL_le _).trans (hχn p)) (norm_nonneg _) hMA
        have e3 : (‖ℬ‖ + 2 * ‖𝒜‖) * ‖spatialFDerivHolderL hα₁.le (χ p)‖ ≤
            (MB + 2 * MA) * (24 * Cχ) :=
          mul_le_mul (by linarith only [hA, hB]) hD (norm_nonneg _) (by positivity)
        have hM : Cχ + MA * Cχ + (MB + 2 * MA) * (24 * Cχ) = M := by ring
        exact hM ▸ add_le_add (add_le_add e1 e2) e3
    have h1 := mul_le_mul_of_nonneg_left hPv hC₁
    have h2 := mul_le_mul_of_nonneg_left hsup hC₂
    simp only [K₃]
    linarith only [hs, h1, h2]
  -- Patch the localizations and absorb the term in `‖u‖`.
  have hglob : ‖u‖ ≤ Cp * (24 * C₁ * Cχ * ‖P u‖ + C₁ * η * ‖u‖ + K₃ * ‖valueL u‖) :=
    norm_le_of_forall_eqOn_ball (by positivity) fun p ↦ ⟨_, hlocal p, fun q hq ↦ by
      rw [ContinuousLinearMap.compParabolicC2Holder₂_apply, hχone p q hq,
        ContinuousLinearMap.mul_apply', one_mul]⟩
  have hη : Cp * (C₁ * η) ≤ 1 / 2 := by
    rw [show Cp * (C₁ * η) = C₁ / (C₁ + 1) / 4 by simp only [η]; field_simp]
    have : C₁ / (C₁ + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    linarith
  have hfin : 24 * C₁ * Cχ * ‖P u‖ + K₃ * ‖valueL u‖ ≤
      (24 * C₁ * Cχ + K₃) * (‖P u‖ + ‖valueL u‖) := by
    have h24 : 0 ≤ 24 * C₁ * Cχ := by positivity
    linarith only [mul_nonneg h24 (norm_nonneg (valueL u)), mul_nonneg hK₃ (norm_nonneg (P u))]
  have hu' := mul_le_mul_of_nonneg_left hfin hCp.le
  rw [hPdef]
  linarith only [hglob, hu', mul_le_mul_of_nonneg_right hη (norm_nonneg u)]

/-- **The Schauder estimate for variable coefficients, up to the supremum norm.** For `0 < α < 1`,
an ellipticity constant `0 < lam`, a bound `K` on the coefficient norms and a maximal horizon
`T₀`, there is a constant `C` such that for every horizon `0 < T ≤ T₀`, all coefficients
`aⁱʲ`, `bⁱ`, `c` in `C_b^{α,α/2}` on `ℝⁿ × [0, T]` with `lam ‖ξ‖² ≤ aⁱʲ(z) ξᵢ ξⱼ` and Hölder norms
at most `K`, and every `u ∈ C_b^{2+α,1+α/2}`,
`‖u‖_{2+α,par} ≤ C (‖P u‖_{α,par} + ‖u(·, 0)‖_{2,α} + ‖u‖_∞)`,
where `P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`. -/
theorem exists_norm_le_euclideanParabolicOperatorL_add_valueL (hα₀ : 0 < α) (hα₁ : α < 1)
    {lam K T₀ : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), (T : ℝ) ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ),
      (∀ p (ξ : EuclideanSpace ℝ ι),
        lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
      (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
      ∀ u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
        ‖u‖ ≤ C * (‖euclideanParabolicOperatorL hα₁.le a b c u‖ +
          ‖u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖ + ‖valueL u‖) := by
  obtain ⟨C, hC, hzero⟩ :=
    exists_norm_le_of_spatialTrace_eq_zero (ι := ι) hα₀ hα₁ (K := K) (T₀ := T₀) hlam
  -- The initial datum is carried by the solution of the heat equation with the same datum.
  obtain ⟨CH, hCH, hheat⟩ := exists_solutionOperator_euclideanParabolicOperatorL_const (ι := ι)
    hα₁.le (lam := 1) (Lam := 1) one_pos
  obtain ⟨CH', hCH', hheat'⟩ := exists_norm_le_euclideanParabolicOperatorL_const (ι := ι)
    hα₀ hα₁ (lam := 1) (Lam := 1) one_pos
  set n : ℝ := (Fintype.card ι : ℝ)
  set K' := max K 0
  set MP := 1 + n * n * K' + 24 * (n * K' + K')
  have hMP : 0 ≤ MP := by positivity
  set CH₁ := CH' * (1 + max T₀ 0)
  refine ⟨(C + 1) * (1 + (MP + 1) * CH₁), by positivity,
    fun T hT hTT₀ a b c ha hab hb hc u ↦ ?_⟩
  obtain ⟨L, -, hLu⟩ := hheat 1 (fun ξ ↦ by simp) (fun ξ ↦ by simp) T hT
  set g := u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩
  obtain ⟨h, hhdef⟩ : ∃ h, L g = h := ⟨_, rfl⟩
  have hh := (hLu g h).2 hhdef.symm
  have hhn : ‖h‖ ≤ CH₁ * ‖g‖ := by
    have h1 := hheat' 1 (fun ξ ↦ by simp) (fun ξ ↦ by simp) T hT h
    rw [hh.1, hh.2, norm_zero, zero_add] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact mul_le_mul_of_nonneg_left (by linarith [le_max_left T₀ 0]) hCH'
  -- The difference `u - h` has zero initial trace.
  have hw := hzero T hT hTT₀ a b c ha hab hb hc (u - h) (by rw [spatialTrace_sub, hh.2, sub_self])
  obtain ⟨P, hPdef⟩ : ∃ P, euclideanParabolicOperatorL (ht := hT) hα₁.le a b c = P := ⟨_, rfl⟩
  rw [hPdef] at hw ⊢
  have hPn : ‖P‖ ≤ MP := by
    rw [← hPdef, euclideanParabolicOperatorL_def]
    refine (norm_parabolicOperatorL_le _).trans ?_
    have hA := norm_euclideanSecondOrderCoeff_le_of_norm_le hab
    have hB := norm_euclideanFirstOrderCoeff_le_of_norm_le hb
    have hC' : ‖euclideanZerothOrderCoeff c‖ ≤ K' :=
      (norm_euclideanZerothOrderCoeff_le c).trans (hc.trans (le_max_left _ _))
    simp only [MP]
    linarith only [hA, hB, hC']
  have hPw : ‖P (u - h)‖ ≤ ‖P u‖ + MP * ‖h‖ := by
    rw [map_sub]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl ((P.le_opNorm h).trans
      (mul_le_mul_of_nonneg_right hPn (norm_nonneg h))))
  have hvw : ‖valueL (u - h)‖ ≤ ‖valueL u‖ + ‖h‖ := by
    rw [map_sub]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_valueL_le h))
  have hu : ‖u‖ ≤ ‖u - h‖ + ‖h‖ := by
    simpa using norm_add_le (u - h) h
  -- Combine: `‖u‖ ≤ C (‖P u‖ + (MP + 1) ‖h‖ + ‖u‖_∞) + ‖h‖` with `‖h‖ ≤ CH ‖g‖`.
  have h1 : ‖u - h‖ ≤ C * (‖P u‖ + (MP + 1) * ‖h‖ + ‖valueL u‖) :=
    hw.trans (mul_le_mul_of_nonneg_left (by linarith only [hPw, hvw]) hC)
  have hh' : (MP + 1) * ‖h‖ ≤ (MP + 1) * CH₁ * ‖g‖ := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hhn (by positivity)
  have hPu := norm_nonneg (P u)
  have hvu := norm_nonneg (valueL u)
  have hg := norm_nonneg g
  have hhn' := norm_nonneg h
  have key : C * (‖P u‖ + (MP + 1) * ‖h‖ + ‖valueL u‖) + ‖h‖ ≤
      (C + 1) * (1 + (MP + 1) * CH₁) * (‖P u‖ + ‖g‖ + ‖valueL u‖) := by
    have e1 : C * ((MP + 1) * ‖h‖) ≤ C * ((MP + 1) * CH₁ * ‖g‖) :=
      mul_le_mul_of_nonneg_left hh' hC
    have hCH₁ : 0 ≤ CH₁ := by positivity
    have hD : 0 ≤ (C + 1) * ((MP + 1) * CH₁) := by positivity
    have hW₁ : C ≤ (C + 1) * (1 + (MP + 1) * CH₁) := by linarith only [hD]
    have hW₂ : C * ((MP + 1) * CH₁) + CH₁ ≤ (C + 1) * (1 + (MP + 1) * CH₁) := by
      linarith only [hC, mul_nonneg hMP hCH₁]
    have hRHS : (C + 1) * (1 + (MP + 1) * CH₁) * (‖P u‖ + ‖g‖ + ‖valueL u‖) =
        (C + 1) * (1 + (MP + 1) * CH₁) * ‖P u‖ + (C + 1) * (1 + (MP + 1) * CH₁) * ‖g‖ +
          (C + 1) * (1 + (MP + 1) * CH₁) * ‖valueL u‖ := by ring
    have hLHS : C * (‖P u‖ + (MP + 1) * ‖h‖ + ‖valueL u‖) + ‖h‖ =
        C * ‖P u‖ + C * ((MP + 1) * ‖h‖) + C * ‖valueL u‖ + ‖h‖ := by ring
    have hg' : (C * ((MP + 1) * CH₁) + CH₁) * ‖g‖ = C * ((MP + 1) * CH₁ * ‖g‖) + CH₁ * ‖g‖ := by
      ring
    rw [hRHS, hLHS]
    linarith only [e1, hhn, mul_le_mul_of_nonneg_right hW₁ hPu,
      mul_le_mul_of_nonneg_right hW₁ hvu, mul_le_mul_of_nonneg_right hW₂ hg, hg']
  linarith only [hu, h1, key]

/-- **The global Schauder estimate for the variable-coefficient Cauchy problem.** For `0 < α < 1`,
an ellipticity constant `0 < lam`, a bound `K` on the coefficient norms and a maximal horizon
`T₀`, there is a constant `C` such that for every horizon `0 < T ≤ T₀`, all coefficients
`aⁱʲ`, `bⁱ`, `c` in `C_b^{α,α/2}` on `ℝⁿ × [0, T]` with `lam ‖ξ‖² ≤ aⁱʲ(z) ξᵢ ξⱼ` and Hölder norms
at most `K`, and every `u ∈ C_b^{2+α,1+α/2}`,
`‖u‖_{2+α,par} ≤ C (‖P u‖_{α,par} + ‖u(·, 0)‖_{2,α})`,
where `P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`. -/
theorem exists_norm_le_euclideanParabolicOperatorL (hα₀ : 0 < α) (hα₁ : α < 1)
    {lam K T₀ : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), (T : ℝ) ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ),
      (∀ p (ξ : EuclideanSpace ℝ ι),
        lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
      (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
      ∀ u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
        ‖u‖ ≤ C * (‖euclideanParabolicOperatorL hα₁.le a b c u‖ +
          ‖u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖) := by
  obtain ⟨C, hC, hest⟩ :=
    exists_norm_le_euclideanParabolicOperatorL_add_valueL (ι := ι) hα₀ hα₁ (K := K) (T₀ := T₀)
      hlam
  set K' := max K 0
  set T₁ := max T₀ 0
  set E := Real.exp (K' * T₁)
  refine ⟨C * (1 + E * (1 + T₁)), by positivity, fun T hT hTT₀ a b c ha hab hb hc u ↦ ?_⟩
  have h := hest T hT hTT₀ a b c ha hab hb hc u
  set g := u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩
  obtain ⟨P, hPdef⟩ : ∃ P, euclideanParabolicOperatorL (ht := hT) hα₁.le a b c = P := ⟨_, rfl⟩
  rw [hPdef] at h ⊢
  -- The comparison principle bounds the supremum norm by the data.
  have hT₁ : (T : ℝ) ≤ T₁ := hTT₀.trans (le_max_left _ _)
  have hsup : ‖valueL u‖ ≤ E * (‖g‖ + T₁ * ‖P u‖) := by
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun p ↦ ?_
    have hp := abs_le_exp_mul_mul_add_mul_of_abs_euclideanParabolicOperatorL_le hα₁.le
      (fun q ξ ↦ (mul_nonneg hlam.le (sq_nonneg ‖ξ‖)).trans (ha q ξ))
      (γ := K') (fun q ↦ (le_abs_self _).trans ((HolderSpace.norm_apply_le c q).trans
        (hc.trans (le_max_left _ _)))) (le_max_right _ _) (M := ‖g‖) (K := ‖P u‖) u
      (fun q ↦ by rw [hPdef]; exact HolderSpace.norm_apply_le (P u) q)
      (fun x ↦ by simpa [g, spatialTrace_apply] using CkHolderSpace.norm_apply_le g x) p
    have ht0 : 0 ≤ (slabTime p : ℝ) := (slabTime p).2.1
    have htT : (slabTime p : ℝ) ≤ T₁ := (slabTime p).2.2.trans hT₁
    rw [sub_zero] at hp
    rw [valueL_apply, Real.norm_eq_abs]
    refine hp.trans (mul_le_mul (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htT
      (le_max_right _ _))) (add_le_add le_rfl (mul_le_mul_of_nonneg_right htT (norm_nonneg _)))
      (by positivity) (Real.exp_pos _).le)
  have hT₁0 : 0 ≤ T₁ := le_max_right _ _
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hPu := norm_nonneg (P u)
  have hg := norm_nonneg g
  have key : ‖P u‖ + ‖g‖ + E * (‖g‖ + T₁ * ‖P u‖) ≤
      (1 + E * (1 + T₁)) * (‖P u‖ + ‖g‖) := by
    nlinarith only [hE, hT₁0, hPu, hg, mul_nonneg hE hPu, mul_nonneg (mul_nonneg hE hT₁0) hg]
  calc ‖u‖ ≤ C * (‖P u‖ + ‖g‖ + ‖valueL u‖) := h
    _ ≤ C * (‖P u‖ + ‖g‖ + E * (‖g‖ + T₁ * ‖P u‖)) := by gcongr
    _ ≤ C * ((1 + E * (1 + T₁)) * (‖P u‖ + ‖g‖)) := mul_le_mul_of_nonneg_left key hC
    _ = _ := by ring

end TauCeti.ParabolicC2HolderSpace
