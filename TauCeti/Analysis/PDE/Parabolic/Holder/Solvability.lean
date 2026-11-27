/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.CauchyProblem
import TauCeti.Analysis.Normed.Operator.ContinuousLinearEquiv

/-!
# The initial-data and terminal-data isomorphisms of parabolic problems

On `ℝⁿ = EuclideanSpace ℝ ι` and a time slab `ℝⁿ × [0, T]`, let

`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

have coefficients `aⁱʲ`, `bⁱ`, `c` in the bounded parabolic Hölder space `C_b^{α,α/2}`, with
`0 < α < 1`, and let `a` be uniformly elliptic: `λ ‖ξ‖² ≤ ξᵀ a(p) ξ` at every point `p`, with
`0 < λ`. The Cauchy problem `P u = f`, `u(·, 0) = g` has exactly one solution in
`C_b^{2+α,1+α/2}`
(`TauCeti.ParabolicC2HolderSpace.bijective_euclideanParabolicOperatorL_prod_spatialTraceL`).
This file packages the initial-data map `u ↦ (P u, u(·, 0))` as an isomorphism of Banach spaces
`C_b^{2+α,1+α/2} ≃ C_b^{α,α/2} × C_b^{2,α}`. Its inverse, the solution operator, is bounded
uniformly over coefficients with a fixed ellipticity constant and a fixed bound on their Hölder
norms and over horizons `T ≤ T₀`, and it depends Lipschitz continuously on the coefficients in
operator norm.

The same holds for the terminal-value problem `P_back u = f`, `u(·, T) = g` of the backward
operator `P_back u = ∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u`: the terminal-data map
`u ↦ (P_back u, u(·, T))` is an isomorphism `C_b^{2+α,1+α/2} ≃ C_b^{α,α/2} × C_b^{2,α}`, and its
inverse has the same uniform bound and Lipschitz dependence on the coefficients.

## The argument

The uniform bound is the global Schauder estimate
(`TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL`). The resolvent
identity `e⁻¹ - e'⁻¹ = e⁻¹ (e' - e) e'⁻¹` together with the Lipschitz dependence of `P` on its
coefficients (`TauCeti.ParabolicC2HolderSpace.norm_euclideanParabolicOperatorL_sub_le`) gives the
Lipschitz dependence of the solution operator.

The terminal-value problem reduces to a Cauchy problem by time reversal `R (x, s) = (x, T - s)`:
`u` solves `P_back u = f`, `u(·, T) = g` exactly when `u ∘ R` solves `P_R v = -f ∘ R`,
`v(·, 0) = g`, where `P_R` is the forward operator with the reversed coefficients `aⁱʲ ∘ R`,
`bⁱ ∘ R`, `c ∘ R`. Time reversal is an isometry of the solution space and does not increase the
norms of the coefficients and data, so the bounds for the backward solution operator are those
for the forward one.

## Main declarations

All declarations are in the `TauCeti.ParabolicC2HolderSpace` namespace.

* `euclideanInitialDataCLE`: the initial-data isomorphism `u ↦ (P u, u(·, 0))`, with
  `euclideanInitialDataCLE_apply`, and the equation and initial condition for its inverse,
  `euclideanParabolicOperatorL_euclideanInitialDataCLE_symm_apply`,
  `spatialTrace_euclideanInitialDataCLE_symm_apply` and
  `euclideanInitialDataCLE_symm_apply_slabMk_zero`.
* `exists_norm_euclideanInitialDataCLE_symm_le`: the uniform bound on the solution operators.
* `exists_norm_euclideanInitialDataCLE_symm_sub_le`: their Lipschitz dependence on the
  coefficients.
* `euclideanTerminalDataCLE`: the terminal-data isomorphism `u ↦ (P_back u, u(·, T))`, with
  `euclideanTerminalDataCLE_apply` and the equation and terminal condition for its inverse,
  `euclideanBackwardParabolicOperatorL_euclideanTerminalDataCLE_symm_apply`,
  `spatialTrace_euclideanTerminalDataCLE_symm_apply` and
  `euclideanTerminalDataCLE_symm_apply_slabMk_right`.
* `timeReverseLIE_euclideanTerminalDataCLE_symm_apply`: the time reversal of the solution of the
  terminal-value problem solves the reversed Cauchy problem, and
  `timeReverseLIE_comp_euclideanTerminalDataCLE_symm` states this as an identity of continuous
  linear maps.
* `exists_norm_euclideanTerminalDataCLE_symm_le` and
  `exists_norm_euclideanTerminalDataCLE_symm_sub_le`: the uniform bound on the backward solution
  operators and their Lipschitz dependence on the coefficients.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 5.2 (the method of continuity) and its use in Theorem 6.8 (the elliptic analogue).
* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 2, Section 4
  (backward equations and time reversal).
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime
open scoped NNReal

variable {α : ℝ≥0} {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}

/-- The global Schauder estimate in the norm of the data space: with the upper ellipticity bound
derived from the coefficient bound, `‖u‖ ≤ C ‖(P u, u(·, 0))‖`, uniformly over the coefficients
and horizons in the given bounds. -/
private theorem exists_norm_le_mul_norm_prod (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ}
    (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ),
        (∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ∀ u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
          ‖u‖ ≤ C * ‖(euclideanParabolicOperatorL hα₁.le a b c u,
            u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩)‖ := by
  obtain ⟨C, hC, hest⟩ := exists_norm_le_euclideanParabolicOperatorL (ι := ι) hα₀ hα₁
    (Lam := ∑ _i : ι, ∑ _j : ι, (K : ℝ)) hlam K T₀
  refine ⟨2 * C, by positivity, fun T hT hTT₀ a b c ha hak hbk hck u ↦ ?_⟩
  -- The coefficient bound gives the upper ellipticity bound.
  have hup := toQuadraticForm'_le_of_norm_coeff_le hak
  have h := hest T hT hTT₀ a b c ha hup hak hbk hck u
  have h₁ := norm_fst_le (euclideanParabolicOperatorL hα₁.le a b c u,
    u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩)
  have h₂ := norm_snd_le (euclideanParabolicOperatorL hα₁.le a b c u,
    u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩)
  nlinarith

/-- **The initial-data isomorphism.** For `0 < α < 1` and coefficients `aⁱʲ`, `bⁱ`, `c` in
`C_b^{α,α/2}(ℝⁿ × [0, T])` with `a` uniformly elliptic, `λ ‖ξ‖² ≤ ξᵀ a ξ` with `0 < λ`, the map
`u ↦ (∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u, u(·, 0))` as an isomorphism of Banach spaces from
`C_b^{2+α,1+α/2}(ℝⁿ × [0, T])` onto `C_b^{α,α/2}(ℝⁿ × [0, T]) × C_b^{2,α}(ℝⁿ)`. Its inverse is
the solution operator of the Cauchy problem `P u = f`, `u(·, 0) = g`. -/
def euclideanInitialDataCLE (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T)
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT ≃L[ℝ]
      HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
        CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ :=
  have hbij := ha.elim fun _ h ↦
    bijective_euclideanParabolicOperatorL_prod_spatialTraceL hα₀ hα₁ hT b c h.1 h.2
  ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.2 hbij.1)
    (LinearMap.range_eq_top.2 hbij.2)

section InitialDataCLE

variable {hα₀ : 0 < α} {hα₁ : α < 1} {hT : (0 : ℝ) < T}
  {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
  {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
  {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
  {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
    lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ}

/-- The initial-data isomorphism sends `u` to its forcing `P u` and its initial trace. -/
@[simp]
theorem euclideanInitialDataCLE_apply (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) :
    euclideanInitialDataCLE hα₀ hα₁ hT a b c ha u =
      (euclideanParabolicOperatorL hα₁.le a b c u, u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩) := by
  simp [euclideanInitialDataCLE, spatialTraceL_apply]

/-- The solution of the Cauchy problem with forcing `f` and initial datum `g` has forcing `f`. -/
@[simp]
theorem euclideanParabolicOperatorL_euclideanInitialDataCLE_symm_apply
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    euclideanParabolicOperatorL hα₁.le a b c
      ((euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm d) = d.1 := by
  have h := (euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).apply_symm_apply d
  rw [euclideanInitialDataCLE_apply] at h
  exact congrArg Prod.fst h

/-- The solution of the Cauchy problem with forcing `f` and initial datum `g` has initial
trace `g`. -/
@[simp]
theorem spatialTrace_euclideanInitialDataCLE_symm_apply
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    ((euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm d).spatialTrace
      ⟨0, left_mem_Icc.2 hT.le⟩ = d.2 := by
  have h := (euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).apply_symm_apply d
  rw [euclideanInitialDataCLE_apply] at h
  exact congrArg Prod.snd h

/-- The solution of the Cauchy problem with initial datum `g` takes the value `g x` at `(x, 0)`. -/
@[simp]
theorem euclideanInitialDataCLE_symm_apply_slabMk_zero
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) (x : EuclideanSpace ℝ ι) :
    (euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm d (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩) =
      d.2 x := by
  rw [← spatialTrace_apply, spatialTrace_euclideanInitialDataCLE_symm_apply]

end InitialDataCLE

/-- **The Schauder estimate for the Cauchy problem.** For `0 < α < 1`, an ellipticity constant
`λ > 0`, a bound `K` on the Hölder norms of the coefficients and a bound `T₀` on the horizon,
the solution operators of the Cauchy problems on `ℝⁿ × [0, T]`, `T ≤ T₀`, are bounded uniformly:
the solution `u` of `P u = f`, `u(·, 0) = g` satisfies
`‖u‖_{2+α,par} ≤ C max (‖f‖_{α,par}) (‖g‖_{2,α})`. -/
theorem exists_norm_euclideanInitialDataCLE_symm_le (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ}
    (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ),
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ‖(euclideanInitialDataCLE hα₀ hα₁ hT a b c ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap‖ ≤
          C := by
  obtain ⟨C, hC, hest⟩ := exists_norm_le_mul_norm_prod (ι := ι) hα₀ hα₁ hlam K T₀
  refine ⟨C, hC, fun T hT hTT₀ a b c ha hak hbk hck ↦
    ContinuousLinearMap.opNorm_le_bound _ hC fun d ↦ ?_⟩
  simpa using hest T hT hTT₀ a b c ha hak hbk hck
    ((euclideanInitialDataCLE hα₀ hα₁ hT a b c ⟨lam, hlam, ha⟩).symm d)

/-- **Lipschitz dependence of the solution operator on the coefficients.** Under the bounds of
`exists_norm_euclideanInitialDataCLE_symm_le`, the solution operators of two Cauchy problems
differ in operator norm by at most `C (∑ᵢⱼ ‖aⁱʲ - a'ⁱʲ‖ + ∑ᵢ ‖bⁱ - b'ⁱ‖ + ‖c - c'‖)`. -/
theorem exists_norm_euclideanInitialDataCLE_symm_sub_le (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ}
    (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a a' : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b b' : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c c' : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
        (ha' : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a' i j p).toQuadraticForm' ξ),
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        (∀ i j, ‖a' i j‖ ≤ K) → (∀ i, ‖b' i‖ ≤ K) → ‖c'‖ ≤ K →
        ‖(euclideanInitialDataCLE hα₀ hα₁ hT a b c ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap -
          (euclideanInitialDataCLE hα₀ hα₁ hT a' b' c'
            ⟨lam, hlam, ha'⟩).symm.toContinuousLinearMap‖ ≤
          C * (∑ i, ∑ j, ‖a i j - a' i j‖ + ∑ i, ‖b i - b' i‖ + ‖c - c'‖) := by
  obtain ⟨C, -, hest⟩ := exists_norm_euclideanInitialDataCLE_symm_le (ι := ι) hα₀ hα₁ hlam K T₀
  refine ⟨24 * C ^ 2, by positivity,
    fun T hT hTT₀ a a' b b' c c' ha ha' hak hbk hck hak' hbk' hck' ↦ ?_⟩
  set e := euclideanInitialDataCLE hα₀ hα₁ hT a b c ⟨lam, hlam, ha⟩
  set e' := euclideanInitialDataCLE hα₀ hα₁ hT a' b' c' ⟨lam, hlam, ha'⟩
  set δ := ∑ i, ∑ j, ‖a i j - a' i j‖ + ∑ i, ‖b i - b' i‖ + ‖c - c'‖
  -- The two operators differ only in their forcing component.
  have hdiff : ‖e'.toContinuousLinearMap - e.toContinuousLinearMap‖ ≤ 24 * δ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
    have hP := (euclideanParabolicOperatorL hα₁.le a' b' c' -
      euclideanParabolicOperatorL hα₁.le a b c).le_opNorm u
    have hL := norm_euclideanParabolicOperatorL_sub_le (ht := hT) hα₁.le a' a b' b c' c
    have hδ : ∑ i, ∑ j, ‖a' i j - a i j‖ + 24 * (∑ i, ‖b' i - b i‖ + ‖c' - c‖) ≤ 24 * δ := by
      simp only [δ, norm_sub_rev (a' _ _), norm_sub_rev (b' _), norm_sub_rev c']
      nlinarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦
        Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) ↦ norm_nonneg (a i j - a' i j)]
    calc ‖(e'.toContinuousLinearMap - e.toContinuousLinearMap) u‖
        = ‖(euclideanParabolicOperatorL hα₁.le a' b' c' -
            euclideanParabolicOperatorL hα₁.le a b c) u‖ := by
          simp [e, e', Prod.norm_def]
      _ ≤ 24 * δ * ‖u‖ := hP.trans (mul_le_mul_of_nonneg_right (hL.trans hδ) (norm_nonneg u))
  have h := ContinuousLinearEquiv.norm_coe_symm_sub_coe_symm_le_of_le
    (hest T hT hTT₀ a b c ha hak hbk hck) (hest T hT hTT₀ a' b' c' ha' hak' hbk' hck') hdiff
  -- The resolvent bound and the goal differ in instance arguments on the spaces of operators,
  -- which `trans` fails to unify, as in `exists_norm_euclideanTerminalDataCLE_symm_sub_le`.
  convert h.trans_eq (by ring : C * (24 * δ) * C = 24 * C ^ 2 * δ) using 1

/-! ### The terminal-value problem -/

/-- **The terminal-data isomorphism.** For `0 < α < 1` and coefficients `aⁱʲ`, `bⁱ`, `c` in
`C_b^{α,α/2}(ℝⁿ × [0, T])` with `a` uniformly elliptic, `λ ‖ξ‖² ≤ ξᵀ a ξ` with `0 < λ`, the map
`u ↦ (∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u, u(·, T))` as an isomorphism of Banach spaces from
`C_b^{2+α,1+α/2}(ℝⁿ × [0, T])` onto `C_b^{α,α/2}(ℝⁿ × [0, T]) × C_b^{2,α}(ℝⁿ)`. Its inverse is
the solution operator of the terminal-value problem `P_back u = f`, `u(·, T) = g`. -/
def euclideanTerminalDataCLE (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T)
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT ≃L[ℝ]
      HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
        CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ :=
  have hbij := ha.elim fun _ h ↦
    bijective_euclideanBackwardParabolicOperatorL_prod_spatialTraceL hα₀ hα₁ hT b c h.1 h.2
  ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.2 hbij.1)
    (LinearMap.range_eq_top.2 hbij.2)

section TerminalDataCLE

variable {hα₀ : 0 < α} {hα₁ : α < 1} {hT : (0 : ℝ) < T}
  {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
  {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
  {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
  {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
    lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ}

/-- The terminal-data isomorphism sends `u` to its forcing `P_back u` and its terminal trace. -/
@[simp]
theorem euclideanTerminalDataCLE_apply
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) :
    euclideanTerminalDataCLE hα₀ hα₁ hT a b c ha u =
      (euclideanBackwardParabolicOperatorL hα₁.le a b c u,
        u.spatialTrace ⟨T, right_mem_Icc.2 hT.le⟩) := by
  simp [euclideanTerminalDataCLE, spatialTraceL_apply]

/-- The solution of the terminal-value problem with forcing `f` and terminal datum `g` has
forcing `f`. -/
@[simp]
theorem euclideanBackwardParabolicOperatorL_euclideanTerminalDataCLE_symm_apply
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    euclideanBackwardParabolicOperatorL hα₁.le a b c
      ((euclideanTerminalDataCLE hα₀ hα₁ hT a b c ha).symm d) = d.1 := by
  have h := (euclideanTerminalDataCLE hα₀ hα₁ hT a b c ha).apply_symm_apply d
  rw [euclideanTerminalDataCLE_apply] at h
  exact congrArg Prod.fst h

/-- The solution of the terminal-value problem with forcing `f` and terminal datum `g` has
terminal trace `g`. -/
@[simp]
theorem spatialTrace_euclideanTerminalDataCLE_symm_apply
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    ((euclideanTerminalDataCLE hα₀ hα₁ hT a b c ha).symm d).spatialTrace
      ⟨T, right_mem_Icc.2 hT.le⟩ = d.2 := by
  have h := (euclideanTerminalDataCLE hα₀ hα₁ hT a b c ha).apply_symm_apply d
  rw [euclideanTerminalDataCLE_apply] at h
  exact congrArg Prod.snd h

/-- The solution of the terminal-value problem with terminal datum `g` takes the value `g x` at
`(x, T)`. -/
@[simp]
theorem euclideanTerminalDataCLE_symm_apply_slabMk_right
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) (x : EuclideanSpace ℝ ι) :
    (euclideanTerminalDataCLE hα₀ hα₁ hT a b c ha).symm d (slabMk x ⟨T, right_mem_Icc.2 hT.le⟩) =
      d.2 x := by
  rw [← spatialTrace_apply, spatialTrace_euclideanTerminalDataCLE_symm_apply]

/-- **The terminal-value problem is a reversed Cauchy problem.** With `R (x, s) = (x, T - s)`, the
time reversal `u ∘ R` of the solution `u` of `P_back u = f`, `u(·, T) = g` is the solution of the
Cauchy problem `P_R v = -f ∘ R`, `v(·, 0) = g` for the forward operator `P_R` with the reversed
coefficients `aⁱʲ ∘ R`, `bⁱ ∘ R`, `c ∘ R`. -/
theorem timeReverseLIE_euclideanTerminalDataCLE_symm_apply
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    timeReverseLIE (T : ℝ) (sub_self (T : ℝ)).symm (sub_zero (T : ℝ)).symm
        ((euclideanTerminalDataCLE hα₀ hα₁ hT a b c ha).symm d) =
      (euclideanInitialDataCLE hα₀ hα₁ hT
        (fun i j ↦ HolderSpace.compLipschitzL _ (slabTimeReverse (T : ℝ) (sub_self (T : ℝ)).symm
          (sub_zero (T : ℝ)).symm).isometry.lipschitzWith (a i j))
        (fun i ↦ HolderSpace.compLipschitzL _ (slabTimeReverse (T : ℝ) (sub_self (T : ℝ)).symm
          (sub_zero (T : ℝ)).symm).isometry.lipschitzWith (b i))
        (HolderSpace.compLipschitzL _ (slabTimeReverse (T : ℝ) (sub_self (T : ℝ)).symm
          (sub_zero (T : ℝ)).symm).isometry.lipschitzWith c)
        (ha.imp fun _ h ↦
          ⟨h.1, mul_norm_sq_le_toQuadraticForm'_compLipschitzL _ h.2⟩)).symm
        (-HolderSpace.compLipschitzL _ (slabTimeReverse (T : ℝ) (sub_self (T : ℝ)).symm
          (sub_zero (T : ℝ)).symm).isometry.lipschitzWith d.1, d.2) := by
  rw [ContinuousLinearEquiv.eq_symm_apply, euclideanInitialDataCLE_apply,
    euclideanParabolicOperatorL_timeReverseLIE, spatialTrace_timeReverseLIE_left,
    euclideanBackwardParabolicOperatorL_euclideanTerminalDataCLE_symm_apply,
    spatialTrace_euclideanTerminalDataCLE_symm_apply]

/-- **The terminal-value solution operator is a reversed Cauchy solution operator.** As continuous
linear maps, time reversal `u ↦ u ∘ R` after the solution operator of the terminal-value problem
for `P_back` is the solution operator of the Cauchy problem for the reversed forward operator
`P_R` after the data reversal `(f, g) ↦ (-f ∘ R, g)`. -/
theorem timeReverseLIE_comp_euclideanTerminalDataCLE_symm :
    (timeReverseLIE (T : ℝ) (sub_self (T : ℝ)).symm
        (sub_zero (T : ℝ)).symm).toLinearIsometry.toContinuousLinearMap.comp
        (euclideanTerminalDataCLE hα₀ hα₁ hT a b c ha).symm.toContinuousLinearMap =
      (euclideanInitialDataCLE hα₀ hα₁ hT
        (fun i j ↦ HolderSpace.compLipschitzL _ (slabTimeReverse (T : ℝ) (sub_self (T : ℝ)).symm
          (sub_zero (T : ℝ)).symm).isometry.lipschitzWith (a i j))
        (fun i ↦ HolderSpace.compLipschitzL _ (slabTimeReverse (T : ℝ) (sub_self (T : ℝ)).symm
          (sub_zero (T : ℝ)).symm).isometry.lipschitzWith (b i))
        (HolderSpace.compLipschitzL _ (slabTimeReverse (T : ℝ) (sub_self (T : ℝ)).symm
          (sub_zero (T : ℝ)).symm).isometry.lipschitzWith c)
        (ha.imp fun _ h ↦ ⟨h.1,
          mul_norm_sq_le_toQuadraticForm'_compLipschitzL _ h.2⟩)).symm.toContinuousLinearMap.comp
        ((-HolderSpace.compLipschitzL _ (slabTimeReverse (T : ℝ) (sub_self (T : ℝ)).symm
          (sub_zero (T : ℝ)).symm).isometry.lipschitzWith).prodMap
          (ContinuousLinearMap.id ℝ (CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ))) :=
  ContinuousLinearMap.ext timeReverseLIE_euclideanTerminalDataCLE_symm_apply

end TerminalDataCLE

omit [DecidableEq ι] in
/-- The data reversal `(f, g) ↦ (-f ∘ R, g)` of the reversed Cauchy problem does not increase the
norm of the data. -/
private theorem norm_prodMap_neg_compLipschitzL_slabTimeReverse_le :
    ‖(-HolderSpace.compLipschitzL (α := α) (Y := ℝ) _ (slabTimeReverse (E := EuclideanSpace ℝ ι)
      (T : ℝ) (sub_self (T : ℝ)).symm (sub_zero (T : ℝ)).symm).isometry.lipschitzWith).prodMap
        (ContinuousLinearMap.id ℝ (CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun d ↦ by
    simpa [Prod.norm_def] using max_le_max (HolderSpace.norm_compLipschitzL_apply_le _ d.1) le_rfl

/-- **The Schauder estimate for the terminal-value problem.** For `0 < α < 1`, an ellipticity
constant `λ > 0`, a bound `K` on the Hölder norms of the coefficients and a bound `T₀` on the
horizon, the solution operators of the terminal-value problems on `ℝⁿ × [0, T]`, `T ≤ T₀`, are
bounded uniformly: the solution `u` of `P_back u = f`, `u(·, T) = g` satisfies
`‖u‖_{2+α,par} ≤ C max (‖f‖_{α,par}) (‖g‖_{2,α})`. -/
theorem exists_norm_euclideanTerminalDataCLE_symm_le (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ}
    (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ),
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ‖(euclideanTerminalDataCLE hα₀ hα₁ hT a b c ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap‖ ≤
          C := by
  obtain ⟨C, hC, hest⟩ := exists_norm_euclideanInitialDataCLE_symm_le (ι := ι) hα₀ hα₁ hlam K T₀
  refine ⟨C, hC, fun T hT hTT₀ a b c ha hak hbk hck ↦ ?_⟩
  have hR := HolderSpace.norm_compLipschitzL_apply_le (α := α) (Y := ℝ)
    (slabTimeReverse (E := EuclideanSpace ℝ ι) (T : ℝ) (sub_self (T : ℝ)).symm
      (sub_zero (T : ℝ)).symm).isometry.lipschitzWith
  -- The Cauchy problem with the reversed coefficients satisfies the same bounds.
  have h := hest T hT hTT₀ _ _ _
    (mul_norm_sq_le_toQuadraticForm'_compLipschitzL _ ha)
    (fun i j ↦ (hR (a i j)).trans (hak i j)) (fun i ↦ (hR (b i)).trans (hbk i))
    ((hR c).trans hck)
  rw [← (timeReverseLIE (T : ℝ) (sub_self (T : ℝ)).symm
      (sub_zero (T : ℝ)).symm).toLinearIsometry.norm_toContinuousLinearMap_comp,
    timeReverseLIE_comp_euclideanTerminalDataCLE_symm]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans <| (mul_le_mul h
    norm_prodMap_neg_compLipschitzL_slabTimeReverse_le (norm_nonneg _) hC).trans_eq (mul_one C)

/-- **Lipschitz dependence of the terminal-value solution operator on the coefficients.** Under
the bounds of `exists_norm_euclideanTerminalDataCLE_symm_le`, the solution operators of two
terminal-value problems differ in operator norm by at most
`C (∑ᵢⱼ ‖aⁱʲ - a'ⁱʲ‖ + ∑ᵢ ‖bⁱ - b'ⁱ‖ + ‖c - c'‖)`. -/
theorem exists_norm_euclideanTerminalDataCLE_symm_sub_le (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ}
    (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a a' : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b b' : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c c' : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
        (ha' : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a' i j p).toQuadraticForm' ξ),
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        (∀ i j, ‖a' i j‖ ≤ K) → (∀ i, ‖b' i‖ ≤ K) → ‖c'‖ ≤ K →
        ‖(euclideanTerminalDataCLE hα₀ hα₁ hT a b c ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap -
          (euclideanTerminalDataCLE hα₀ hα₁ hT a' b' c'
            ⟨lam, hlam, ha'⟩).symm.toContinuousLinearMap‖ ≤
          C * (∑ i, ∑ j, ‖a i j - a' i j‖ + ∑ i, ‖b i - b' i‖ + ‖c - c'‖) := by
  obtain ⟨C, hC, hest⟩ :=
    exists_norm_euclideanInitialDataCLE_symm_sub_le (ι := ι) hα₀ hα₁ hlam K T₀
  refine ⟨C, hC, fun T hT hTT₀ a a' b b' c c' ha ha' hak hbk hck hak' hbk' hck' ↦ ?_⟩
  have hR := HolderSpace.norm_compLipschitzL_apply_le (α := α) (Y := ℝ)
    (slabTimeReverse (E := EuclideanSpace ℝ ι) (T : ℝ) (sub_self (T : ℝ)).symm
      (sub_zero (T : ℝ)).symm).isometry.lipschitzWith
  -- The Cauchy problems with the reversed coefficients satisfy the same bounds, and reversing
  -- does not increase the distance between the coefficients.
  have h := hest T hT hTT₀ _ _ _ _ _ _
    (mul_norm_sq_le_toQuadraticForm'_compLipschitzL _ ha)
    (mul_norm_sq_le_toQuadraticForm'_compLipschitzL _ ha')
    (fun i j ↦ (hR (a i j)).trans (hak i j)) (fun i ↦ (hR (b i)).trans (hbk i))
    ((hR c).trans hck) (fun i j ↦ (hR (a' i j)).trans (hak' i j))
    (fun i ↦ (hR (b' i)).trans (hbk' i)) ((hR c').trans hck')
  simp only [← map_sub] at h
  have hδ := h.trans (mul_le_mul_of_nonneg_left (add_le_add (add_le_add
    (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hR (a i j - a' i j))
    (Finset.sum_le_sum fun i _ ↦ hR (b i - b' i))) (hR (c - c'))) hC)
  rw [← (timeReverseLIE (T : ℝ) (sub_self (T : ℝ)).symm
      (sub_zero (T : ℝ)).symm).toLinearIsometry.norm_toContinuousLinearMap_comp,
    ContinuousLinearMap.comp_sub, timeReverseLIE_comp_euclideanTerminalDataCLE_symm,
    timeReverseLIE_comp_euclideanTerminalDataCLE_symm, ← ContinuousLinearMap.sub_comp]
  refine ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _)
    norm_prodMap_neg_compLipschitzL_slabTimeReverse_le)).trans ?_
  -- The goal and `hδ` differ only in instance arguments. Chiefly, on the data space
  -- `C_b^{α,α/2} × C_b^{2,α}` the forward bound in `hδ` has the product topology
  -- `instTopologicalSpaceProd`, while composing with the data reversal gives the topology of the
  -- product uniform structure. `exact hδ` fails to unify these definitionally equal instances.
  convert hδ using 1

end TauCeti.ParabolicC2HolderSpace
