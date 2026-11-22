/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.CauchyProblem

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

By time reversal about `t₁`, the same holds on any closed time slab `ℝⁿ × [t₀, t₁]` (`t₀ < t₁`)
for the backward parabolic operator `P_back u = ∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u` and the terminal
trace `u(·, t₁)`: the terminal-data map `u ↦ (P_back u, u(·, t₁))` is an isomorphism of Banach
spaces, with uniform Schauder bound and Lipschitz dependence on the coefficients over slabs of
duration `t₁ - t₀ ≤ T₀`.

## The argument

The uniform bound is the global Schauder estimate
(`TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL`). The resolvent
identity `e⁻¹ - e'⁻¹ = e⁻¹ (e' - e) e'⁻¹` together with the Lipschitz dependence of `P` on its
coefficients (`TauCeti.ParabolicC2HolderSpace.norm_euclideanParabolicOperatorL_sub_le`) gives the
Lipschitz dependence of the solution operator. Time reversal `R(x, s) = (x, t₁ - s)` transports
the slab `ℝⁿ × [0, t₁ - t₀]` isometrically onto `ℝⁿ × [t₀, t₁]`, carrying the forward initial-data
problem onto the backward terminal-data problem without loss in the constants: `u` solves
`P_back u = f`, `u(·, t₁) = g` exactly when `u ∘ R` solves `P_R v = -f ∘ R`, `v(·, 0) = g`.

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
* `euclideanTerminalDataCLE`: the terminal-data isomorphism `u ↦ (P_back u, u(·, t₁))` on
  `ℝⁿ × [t₀, t₁]`, with `euclideanTerminalDataCLE_apply`,
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
  obtain ⟨C, hC, hest⟩ := exists_norm_euclideanInitialDataCLE_symm_le (ι := ι) hα₀ hα₁ hlam K T₀
  refine ⟨24 * C ^ 2, by positivity,
    fun T hT hTT₀ a a' b b' c c' ha ha' hak hbk hck hak' hbk' hck' ↦ ?_⟩
  set e := euclideanInitialDataCLE hα₀ hα₁ hT a b c ⟨lam, hlam, ha⟩
  set e' := euclideanInitialDataCLE hα₀ hα₁ hT a' b' c' ⟨lam, hlam, ha'⟩
  set δ := ∑ i, ∑ j, ‖a i j - a' i j‖ + ∑ i, ‖b i - b' i‖ + ‖c - c'‖
  -- The resolvent identity `e⁻¹ - e'⁻¹ = e⁻¹ (e' - e) e'⁻¹`.
  have hres : e.symm.toContinuousLinearMap - e'.symm.toContinuousLinearMap =
      e.symm.toContinuousLinearMap ∘L (e'.toContinuousLinearMap - e.toContinuousLinearMap) ∘L
        e'.symm.toContinuousLinearMap :=
    ContinuousLinearMap.ext fun d ↦ by simp
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
  have h₁ := hest T hT hTT₀ a b c ha hak hbk hck
  have h₂ := hest T hT hTT₀ a' b' c' ha' hak' hbk' hck'
  rw [hres]
  calc _ ≤ ‖e.symm.toContinuousLinearMap‖ *
        (‖e'.toContinuousLinearMap - e.toContinuousLinearMap‖ *
          ‖e'.symm.toContinuousLinearMap‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ C * (24 * δ * C) := by gcongr
    _ = 24 * C ^ 2 * δ := by ring

/-! ### The terminal-data isomorphism -/

section Terminal

/-- **The terminal-data isomorphism.** For `0 < α < 1`, `t₀ < t₁`, and coefficients `aⁱʲ`, `bⁱ`, `c`
in `C_b^{α,α/2}(ℝⁿ × [t₀, t₁])` with `a` uniformly elliptic, `λ ‖ξ‖² ≤ ξᵀ a ξ` with `0 < λ`, the
map `u ↦ (∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u, u(·, t₁))` as an isomorphism of Banach spaces from
`C_b^{2+α,1+α/2}(ℝⁿ × [t₀, t₁])` onto `C_b^{α,α/2}(ℝⁿ × [t₀, t₁]) × C_b^{2,α}(ℝⁿ)`. Its inverse is
the solution operator of the terminal-value problem `P_back u = f`, `u(·, t₁) = g`. -/
def euclideanTerminalDataCLE {t₀ t₁ : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht ≃L[ℝ]
      HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ ×
        CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ :=
  have hbij := ha.elim fun _ h ↦
    bijective_euclideanBackwardParabolicOperatorL_prod_spatialTraceL hα₀ hα₁ ht b c h.1 h.2
  ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.2 hbij.1)
    (LinearMap.range_eq_top.2 hbij.2)

section TerminalDataCLE

variable {t₀ t₁ : ℝ} {hα₀ : 0 < α} {hα₁ : α < 1} {ht : t₀ < t₁}
  {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
    lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ}

/-- The terminal-data isomorphism sends `u` to its backward forcing `P_back u` and its terminal
trace `u(·, t₁)`. -/
@[simp]
theorem euclideanTerminalDataCLE_apply (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht) :
    euclideanTerminalDataCLE hα₀ hα₁ ht a b c ha u =
      (euclideanBackwardParabolicOperatorL hα₁.le a b c u,
        u.spatialTrace ⟨t₁, right_mem_Icc.2 ht.le⟩) := by
  simp [euclideanTerminalDataCLE, spatialTraceL_apply]

/-- The solution of the terminal-value problem with forcing `f` and terminal datum `g` has
backward forcing `f`. -/
@[simp]
theorem euclideanBackwardParabolicOperatorL_euclideanTerminalDataCLE_symm_apply
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    euclideanBackwardParabolicOperatorL hα₁.le a b c
      ((euclideanTerminalDataCLE hα₀ hα₁ ht a b c ha).symm d) = d.1 := by
  have h := (euclideanTerminalDataCLE hα₀ hα₁ ht a b c ha).apply_symm_apply d
  rw [euclideanTerminalDataCLE_apply] at h
  exact congrArg Prod.fst h

/-- The solution of the terminal-value problem with forcing `f` and terminal datum `g` has
terminal trace `g`. -/
@[simp]
theorem spatialTrace_euclideanTerminalDataCLE_symm_apply
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    ((euclideanTerminalDataCLE hα₀ hα₁ ht a b c ha).symm d).spatialTrace
      ⟨t₁, right_mem_Icc.2 ht.le⟩ = d.2 := by
  have h := (euclideanTerminalDataCLE hα₀ hα₁ ht a b c ha).apply_symm_apply d
  rw [euclideanTerminalDataCLE_apply] at h
  exact congrArg Prod.snd h

/-- The solution of the terminal-value problem with terminal datum `g` takes the value `g x` at
`(x, t₁)`. -/
@[simp]
theorem euclideanTerminalDataCLE_symm_apply_slabMk_right
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) (x : EuclideanSpace ℝ ι) :
    (euclideanTerminalDataCLE hα₀ hα₁ ht a b c ha).symm d (slabMk x ⟨t₁, right_mem_Icc.2 ht.le⟩) =
      d.2 x := by
  rw [← spatialTrace_apply, spatialTrace_euclideanTerminalDataCLE_symm_apply]

/-- **The terminal-value problem is a reversed Cauchy problem.** With `R (x, s) = (x, t₁ - s)` and
`T = t₁ - t₀`, the time reversal `u ∘ R` of the solution `u` of `P_back u = f`, `u(·, t₁) = g` is
the solution of the Cauchy problem `P_R v = -f ∘ R`, `v(·, 0) = g` for the forward operator `P_R`
with the reversed coefficients `aⁱʲ ∘ R`, `bⁱ ∘ R`, `c ∘ R`. -/
theorem timeReverseLIE_euclideanTerminalDataCLE_symm_apply
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) {T : ℝ≥0} (hT : (T : ℝ) = t₁ - t₀) :
    timeReverseLIE t₁ (sub_self t₁).symm hT
        ((euclideanTerminalDataCLE hα₀ hα₁ ht a b c ha).symm d) =
      (euclideanInitialDataCLE hα₀ hα₁ (hT ▸ sub_pos.2 ht)
        (fun i j ↦ HolderSpace.compLipschitzL _
          (slabTimeReverse t₁ (sub_self t₁).symm hT).isometry.lipschitzWith (a i j))
        (fun i ↦ HolderSpace.compLipschitzL _
          (slabTimeReverse t₁ (sub_self t₁).symm hT).isometry.lipschitzWith (b i))
        (HolderSpace.compLipschitzL _
          (slabTimeReverse t₁ (sub_self t₁).symm hT).isometry.lipschitzWith c)
        (ha.imp fun _ h ↦
          ⟨h.1, mul_norm_sq_le_toQuadraticForm'_compLipschitzL _ h.2⟩)).symm
        (-HolderSpace.compLipschitzL _
          (slabTimeReverse t₁ (sub_self t₁).symm hT).isometry.lipschitzWith d.1, d.2) := by
  rw [ContinuousLinearEquiv.eq_symm_apply, euclideanInitialDataCLE_apply,
    euclideanParabolicOperatorL_timeReverseLIE, spatialTrace_timeReverseLIE_left,
    euclideanBackwardParabolicOperatorL_euclideanTerminalDataCLE_symm_apply,
    spatialTrace_euclideanTerminalDataCLE_symm_apply]

/-- **The terminal-value solution operator is a reversed Cauchy solution operator.** As continuous
linear maps, time reversal `u ↦ u ∘ R` after the solution operator of the terminal-value problem
for `P_back` is the solution operator of the Cauchy problem for the reversed forward operator
`P_R` after the data reversal `(f, g) ↦ (-f ∘ R, g)`. -/
theorem timeReverseLIE_comp_euclideanTerminalDataCLE_symm {T : ℝ≥0} (hT : (T : ℝ) = t₁ - t₀) :
    (timeReverseLIE t₁ (sub_self t₁).symm hT).toLinearIsometry.toContinuousLinearMap.comp
        (euclideanTerminalDataCLE hα₀ hα₁ ht a b c ha).symm.toContinuousLinearMap =
      (euclideanInitialDataCLE hα₀ hα₁ (hT ▸ sub_pos.2 ht)
        (fun i j ↦ HolderSpace.compLipschitzL _
          (slabTimeReverse t₁ (sub_self t₁).symm hT).isometry.lipschitzWith (a i j))
        (fun i ↦ HolderSpace.compLipschitzL _
          (slabTimeReverse t₁ (sub_self t₁).symm hT).isometry.lipschitzWith (b i))
        (HolderSpace.compLipschitzL _
          (slabTimeReverse t₁ (sub_self t₁).symm hT).isometry.lipschitzWith c)
        (ha.imp fun _ h ↦ ⟨h.1,
          mul_norm_sq_le_toQuadraticForm'_compLipschitzL _ h.2⟩)).symm.toContinuousLinearMap.comp
        ((-HolderSpace.compLipschitzL _
          (slabTimeReverse t₁ (sub_self t₁).symm hT).isometry.lipschitzWith).prodMap
          (ContinuousLinearMap.id ℝ (CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ))) :=
  ContinuousLinearMap.ext fun d ↦ timeReverseLIE_euclideanTerminalDataCLE_symm_apply d hT

end TerminalDataCLE

omit [DecidableEq ι] in
/-- The data reversal `(f, g) ↦ (-f ∘ R, g)` of the reversed Cauchy problem does not increase the
norm of the data. -/
private theorem norm_prodMap_neg_compLipschitzL_slabTimeReverse_le {t₀ t₁ : ℝ} {T : ℝ≥0}
    (hT : (T : ℝ) = t₁ - t₀) :
    ‖(-HolderSpace.compLipschitzL (α := α) (Y := ℝ) _ (slabTimeReverse (E := EuclideanSpace ℝ ι)
      t₁ (sub_self t₁).symm hT).isometry.lipschitzWith).prodMap
        (ContinuousLinearMap.id ℝ (CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun d ↦ by
    simpa [Prod.norm_def] using max_le_max (HolderSpace.norm_compLipschitzL_apply_le _ d.1) le_rfl

/-- **The Schauder estimate for the terminal-value problem.** For `0 < α < 1`, an ellipticity
constant `λ > 0`, a bound `K` on the Hölder norms of the coefficients and a bound `T₀` on the
slab duration, the solution operators of the terminal-value problems on `ℝⁿ × [t₀, t₁]`,
`t₁ - t₀ ≤ T₀`, are bounded uniformly: `‖u‖_{2+α,par} ≤ C max (‖f‖_{α,par}) (‖g‖_{2,α})`. -/
theorem exists_norm_euclideanTerminalDataCLE_symm_le (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ}
    (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t₀ t₁ : ℝ} (ht : t₀ < t₁), t₁ - t₀ ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
        (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ),
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ‖(euclideanTerminalDataCLE hα₀ hα₁ ht a b c ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap‖ ≤
          C := by
  obtain ⟨C, hC, hest⟩ := exists_norm_euclideanInitialDataCLE_symm_le (ι := ι) hα₀ hα₁ hlam K T₀
  refine ⟨C, hC, fun {t₀ t₁} ht hTT₀ a b c ha hak hbk hck ↦ ?_⟩
  let T : ℝ≥0 := ⟨t₁ - t₀, (sub_pos.2 ht).le⟩
  have hT : (T : ℝ) = t₁ - t₀ := rfl
  have hR := HolderSpace.norm_compLipschitzL_apply_le (α := α) (Y := ℝ)
    (slabTimeReverse (E := EuclideanSpace ℝ ι) t₁ (sub_self t₁).symm hT).isometry.lipschitzWith
  -- The Cauchy problem with the reversed coefficients satisfies the same bounds.
  have h := hest T (hT ▸ sub_pos.2 ht) (by exact_mod_cast hTT₀) _ _ _
    (mul_norm_sq_le_toQuadraticForm'_compLipschitzL _ ha)
    (fun i j ↦ (hR (a i j)).trans (hak i j)) (fun i ↦ (hR (b i)).trans (hbk i))
    ((hR c).trans hck)
  rw [← (timeReverseLIE t₁ (sub_self t₁).symm hT).toLinearIsometry.norm_toContinuousLinearMap_comp,
    timeReverseLIE_comp_euclideanTerminalDataCLE_symm hT]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans <| (mul_le_mul h
    (norm_prodMap_neg_compLipschitzL_slabTimeReverse_le hT) (norm_nonneg _) hC).trans_eq (mul_one C)

/-- **Lipschitz dependence of the terminal-value solution operator on the coefficients.** Under
the bounds of `exists_norm_euclideanTerminalDataCLE_symm_le`, the solution operators of two
terminal-value problems on `ℝⁿ × [t₀, t₁]` differ in operator norm by at most
`C (∑ᵢⱼ ‖aⁱʲ - a'ⁱʲ‖ + ∑ᵢ ‖bⁱ - b'ⁱ‖ + ‖c - c'‖)`. -/
theorem exists_norm_euclideanTerminalDataCLE_symm_sub_le (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ}
    (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t₀ t₁ : ℝ} (ht : t₀ < t₁), t₁ - t₀ ≤ T₀ →
      ∀ (a a' : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
        (b b' : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
        (c c' : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
        (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
        (ha' : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a' i j p).toQuadraticForm' ξ),
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        (∀ i j, ‖a' i j‖ ≤ K) → (∀ i, ‖b' i‖ ≤ K) → ‖c'‖ ≤ K →
        ‖(euclideanTerminalDataCLE hα₀ hα₁ ht a b c ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap -
          (euclideanTerminalDataCLE hα₀ hα₁ ht a' b' c'
            ⟨lam, hlam, ha'⟩).symm.toContinuousLinearMap‖ ≤
          C * (∑ i, ∑ j, ‖a i j - a' i j‖ + ∑ i, ‖b i - b' i‖ + ‖c - c'‖) := by
  obtain ⟨C, hC, hest⟩ :=
    exists_norm_euclideanInitialDataCLE_symm_sub_le (ι := ι) hα₀ hα₁ hlam K T₀
  refine ⟨C, hC, fun {t₀ t₁} ht hTT₀ a a' b b' c c' ha ha' hak hbk hck hak' hbk' hck' ↦ ?_⟩
  let T : ℝ≥0 := ⟨t₁ - t₀, (sub_pos.2 ht).le⟩
  have hT : (T : ℝ) = t₁ - t₀ := rfl
  have hR := HolderSpace.norm_compLipschitzL_apply_le (α := α) (Y := ℝ)
    (slabTimeReverse (E := EuclideanSpace ℝ ι) t₁ (sub_self t₁).symm hT).isometry.lipschitzWith
  -- The Cauchy problems with the reversed coefficients satisfy the same bounds, and reversing
  -- does not increase the distance between the coefficients.
  have h := hest T (hT ▸ sub_pos.2 ht) (by exact_mod_cast hTT₀) _ _ _ _ _ _
    (mul_norm_sq_le_toQuadraticForm'_compLipschitzL _ ha)
    (mul_norm_sq_le_toQuadraticForm'_compLipschitzL _ ha')
    (fun i j ↦ (hR (a i j)).trans (hak i j)) (fun i ↦ (hR (b i)).trans (hbk i))
    ((hR c).trans hck) (fun i j ↦ (hR (a' i j)).trans (hak' i j))
    (fun i ↦ (hR (b' i)).trans (hbk' i)) ((hR c').trans hck')
  simp only [← map_sub] at h
  have hδ := h.trans (mul_le_mul_of_nonneg_left (add_le_add (add_le_add
    (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hR (a i j - a' i j))
    (Finset.sum_le_sum fun i _ ↦ hR (b i - b' i))) (hR (c - c'))) hC)
  rw [← (timeReverseLIE t₁ (sub_self t₁).symm hT).toLinearIsometry.norm_toContinuousLinearMap_comp,
    ContinuousLinearMap.comp_sub, timeReverseLIE_comp_euclideanTerminalDataCLE_symm hT,
    timeReverseLIE_comp_euclideanTerminalDataCLE_symm hT, ← ContinuousLinearMap.sub_comp]
  refine ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _)
    (norm_prodMap_neg_compLipschitzL_slabTimeReverse_le hT))).trans ?_
  -- The goal and `hδ` differ only in instance arguments. Chiefly, on the data space
  -- `C_b^{α,α/2} × C_b^{2,α}` the forward bound in `hδ` has the product topology
  -- `instTopologicalSpaceProd`, while composing with the data reversal gives the topology of the
  -- product uniform structure. `exact hδ` fails to unify these definitionally equal instances.
  convert hδ using 1

end Terminal

end TauCeti.ParabolicC2HolderSpace
