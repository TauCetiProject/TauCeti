/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.CauchyProblem
import TauCeti.Analysis.Matrix.QuadraticBounds

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

Time reversal `(x, τ) ↦ (x, t₁ - τ)` transports the backward parabolic terminal-value problem
`P_back u = ∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u = f`, `u(·, t₁) = g` on an arbitrary slab
`ℝⁿ × [t₀, t₁]` (`t₀ < t₁`) onto the forward problem on `ℝⁿ × [0, t₁ - t₀]`, yielding the
corresponding terminal-data Banach isomorphism `euclideanTerminalDataCLE`, uniform Schauder bound,
and Lipschitz dependence on the coefficients.

## The argument

The uniform bound is the global Schauder estimate
(`TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL`). The resolvent
identity `e⁻¹ - e'⁻¹ = e⁻¹ (e' - e) e'⁻¹` together with the Lipschitz dependence of `P` on its
coefficients (`TauCeti.ParabolicC2HolderSpace.norm_euclideanParabolicOperatorL_sub_le`) gives the
Lipschitz dependence of the solution operator, and time reversal (`timeReverseLIE`,
`slabTimeReverse`) transfers both bounds to `euclideanTerminalDataCLE`.

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
* `euclideanTerminalDataCLE`: the backward terminal-data isomorphism `u ↦ (P_back u, u(·, t₁))` on
  `ℝⁿ × [t₀, t₁]`, with `euclideanTerminalDataCLE_apply`,
  `euclideanBackwardParabolicOperatorL_euclideanTerminalDataCLE_symm_apply`,
  `spatialTrace_euclideanTerminalDataCLE_symm_apply`,
  `euclideanTerminalDataCLE_symm_apply_slabMk_right`,
  `exists_norm_euclideanTerminalDataCLE_symm_le`, and
  `exists_norm_euclideanTerminalDataCLE_symm_sub_le`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 5.2 (the method of continuity) and its use in Theorem 6.8 (the elliptic analogue).
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
  have hup : ∀ p (ξ : EuclideanSpace ℝ ι), (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ ≤
      (∑ _i : ι, ∑ _j : ι, (K : ℝ)) * ‖ξ‖ ^ 2 := fun p ↦
    Matrix.toQuadraticForm'_le_of_forall_abs_le fun i j ↦
      ((Real.norm_eq_abs _).symm.trans_le (HolderSpace.norm_apply_le (a i j) p)).trans (hak i j)
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

/-! ### The terminal-data isomorphism of the backward problem on `[t₀, t₁]` -/

section TerminalData

private def slabDuration {t₀ t₁ : ℝ} (ht : t₀ < t₁) : ℝ≥0 := ⟨t₁ - t₀, sub_nonneg.2 ht.le⟩

private theorem coe_slabDuration {t₀ t₁ : ℝ} (ht : t₀ < t₁) : (slabDuration ht : ℝ) = t₁ - t₀ := rfl

private theorem slabDuration_pos {t₀ t₁ : ℝ} (ht : t₀ < t₁) : (0 : ℝ) < slabDuration ht :=
  sub_pos.2 ht

private def timeReverseHolderCLE {E F : Type*} [MetricSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {t₀ t₁ : ℝ} (ht : t₀ < t₁) :
    HolderSpace α (slab (E := E) t₀ t₁) F ≃L[ℝ]
      HolderSpace α (slab (E := E) 0 (slabDuration ht)) F :=
  ContinuousLinearEquiv.equivOfInverse
    (HolderSpace.compLipschitzL _ (slabTimeReverse (a' := 0) (b' := (slabDuration ht : ℝ)) t₁
      (sub_self t₁).symm (coe_slabDuration ht)).isometry.lipschitzWith)
    (HolderSpace.compLipschitzL _ (slabTimeReverse (a' := 0) (b' := (slabDuration ht : ℝ)) t₁
      (sub_self t₁).symm (coe_slabDuration ht)).symm.isometry.lipschitzWith)
    (fun f ↦ by ext p; rw [HolderSpace.compLipschitzL_apply, HolderSpace.compLipschitzL_apply,
      IsometryEquiv.apply_symm_apply])
    (fun g ↦ by ext q; rw [HolderSpace.compLipschitzL_apply, HolderSpace.compLipschitzL_apply,
      IsometryEquiv.symm_apply_apply])

@[simp] private theorem timeReverseHolderCLE_apply {E F : Type*} [MetricSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {t₀ t₁ : ℝ} (ht : t₀ < t₁)
    (f : HolderSpace α (slab (E := E) t₀ t₁) F) (q : slab (E := E) 0 (slabDuration ht)) :
    timeReverseHolderCLE ht f q =
      f (slabTimeReverse (a' := 0) (b' := (slabDuration ht : ℝ)) t₁
        (sub_self t₁).symm (coe_slabDuration ht) q) :=
  HolderSpace.compLipschitzL_apply _ _ _

private theorem norm_timeReverseHolderCLE_apply_le {E F : Type*} [MetricSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {t₀ t₁ : ℝ} (ht : t₀ < t₁)
    (f : HolderSpace α (slab (E := E) t₀ t₁) F) : ‖timeReverseHolderCLE ht f‖ ≤ ‖f‖ := by
  simpa using (timeReverseHolderCLE ht).toContinuousLinearMap.le_of_opNorm_le
    (HolderSpace.norm_compLipschitzL_le_one _) f

private def terminalDataBridgeCLE {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {t₀ t₁ : ℝ} (ht : t₀ < t₁) :
    (HolderSpace α (slab (E := E) t₀ t₁) F × CkHolderSpace 2 α E F) ≃L[ℝ]
      (HolderSpace α (slab (E := E) 0 (slabDuration ht)) F × CkHolderSpace 2 α E F) :=
  ((timeReverseHolderCLE ht).trans (ContinuousLinearEquiv.neg ℝ)).prodCongr
    (ContinuousLinearEquiv.refl ℝ _)

private theorem norm_terminalDataBridgeCLE_le_one {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {t₀ t₁ : ℝ} (ht : t₀ < t₁) :
    ‖(terminalDataBridgeCLE (α := α) (E := E) (F := F) ht).toContinuousLinearMap‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun d ↦ by
    rw [one_mul, Prod.norm_def, Prod.norm_def]
    have h₁ : ‖(terminalDataBridgeCLE ht d).1‖ ≤ ‖d.1‖ := by
      simpa [terminalDataBridgeCLE] using norm_timeReverseHolderCLE_apply_le ht d.1
    have h₂ : ‖(terminalDataBridgeCLE ht d).2‖ ≤ ‖d.2‖ := by simp [terminalDataBridgeCLE]
    exact max_le (h₁.trans (le_max_left _ _)) (h₂.trans (le_max_right _ _))

private theorem ellipticity_timeReverseHolderCLE {t₀ t₁ : ℝ} (ht : t₀ < t₁)
    {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ} {lam : ℝ}
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (q : slab (E := EuclideanSpace ℝ ι) 0 (slabDuration ht)) (ξ : EuclideanSpace ℝ ι) :
    lam * ‖ξ‖ ^ 2 ≤
      (Matrix.of fun i j ↦ timeReverseHolderCLE ht (a i j) q).toQuadraticForm' ξ := by
  simpa using ha _ ξ

/-- **The terminal-data isomorphism.** For `0 < α < 1`, `t₀ < t₁`, and coefficients `aⁱʲ`, `bⁱ`, `c`
in `C_b^{α,α/2}(ℝⁿ × [t₀, t₁])` with `a` uniformly elliptic (`λ ‖ξ‖² ≤ ξᵀ a ξ`, `0 < λ`), the map
`u ↦ (∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u, u(·, t₁))` as an isomorphism of Banach spaces from
`C_b^{2+α,1+α/2}(ℝⁿ × [t₀, t₁])` onto `C_b^{α,α/2}(ℝⁿ × [t₀, t₁]) × C_b^{2,α}(ℝⁿ)`. -/
def euclideanTerminalDataCLE {t₀ t₁ : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht ≃L[ℝ]
      HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ ×
        CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ :=
  (timeReverseLIE (α := α) (E := EuclideanSpace ℝ ι) (F := ℝ) (hab := ht) (a' := 0)
      (b' := (slabDuration ht : ℝ)) t₁ (sub_self t₁).symm
      (coe_slabDuration ht)).toContinuousLinearEquiv.trans <|
    (euclideanInitialDataCLE hα₀ hα₁ (slabDuration_pos ht)
      (fun i j ↦ timeReverseHolderCLE ht (a i j)) (fun i ↦ timeReverseHolderCLE ht (b i))
      (timeReverseHolderCLE ht c)
      (ha.elim fun lam h ↦ ⟨lam, h.1, ellipticity_timeReverseHolderCLE ht h.2⟩)).trans
      (terminalDataBridgeCLE ht).symm

/-- The terminal-data isomorphism sends `u` to its backward forcing `P_back u` and its terminal
trace `u(·, t₁)`. -/
@[simp] theorem euclideanTerminalDataCLE_apply {t₀ t₁ : ℝ} {hα₀ : 0 < α} {hα₁ : α < 1}
    {ht : t₀ < t₁} {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
    {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
    {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
    {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ}
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht) :
    euclideanTerminalDataCLE hα₀ hα₁ ht a b c ha u =
      (euclideanBackwardParabolicOperatorL hα₁.le a b c u,
        u.spatialTrace ⟨t₁, right_mem_Icc.2 ht.le⟩) := by
  apply (terminalDataBridgeCLE ht).injective
  simp only [euclideanTerminalDataCLE, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply, euclideanInitialDataCLE_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, spatialTrace_timeReverseLIE_left,
    terminalDataBridgeCLE, ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.neg_apply,
    ContinuousLinearEquiv.refl_apply]
  congr 1; exact euclideanParabolicOperatorL_timeReverseLIE hα₁.le u

section TerminalDataCLE

variable {t₀ t₁ : ℝ} {hα₀ : 0 < α} {hα₁ : α < 1} {ht : t₀ < t₁}
  {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
    lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ}

/-- The solution of the terminal-value problem with forcing `f` and terminal datum `g` has
backward forcing `f`. -/
@[simp] theorem euclideanBackwardParabolicOperatorL_euclideanTerminalDataCLE_symm_apply
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    euclideanBackwardParabolicOperatorL hα₁.le a b c
      ((euclideanTerminalDataCLE hα₀ hα₁ ht a b c ha).symm d) = d.1 := by
  have h := (euclideanTerminalDataCLE hα₀ hα₁ ht a b c ha).apply_symm_apply d
  rw [euclideanTerminalDataCLE_apply] at h; exact congrArg Prod.fst h

/-- The solution of the terminal-value problem with forcing `f` and terminal datum `g` has
terminal trace `g`. -/
@[simp] theorem spatialTrace_euclideanTerminalDataCLE_symm_apply
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    ((euclideanTerminalDataCLE hα₀ hα₁ ht a b c ha).symm d).spatialTrace
      ⟨t₁, right_mem_Icc.2 ht.le⟩ = d.2 := by
  have h := (euclideanTerminalDataCLE hα₀ hα₁ ht a b c ha).apply_symm_apply d
  rw [euclideanTerminalDataCLE_apply] at h; exact congrArg Prod.snd h

/-- The solution of the terminal-value problem with terminal datum `g` takes the value `g x` at
`(x, t₁)`. -/
@[simp] theorem euclideanTerminalDataCLE_symm_apply_slabMk_right
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) (x : EuclideanSpace ℝ ι) :
    (euclideanTerminalDataCLE hα₀ hα₁ ht a b c ha).symm d
      (slabMk x ⟨t₁, right_mem_Icc.2 ht.le⟩) = d.2 x := by
  rw [← spatialTrace_apply, spatialTrace_euclideanTerminalDataCLE_symm_apply]

end TerminalDataCLE

private def timeReverseSymmL {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {t₀ t₁ : ℝ} (ht : t₀ < t₁) :
    ParabolicC2HolderSpace α E F (slabDuration_pos ht) →L[ℝ] ParabolicC2HolderSpace α E F ht :=
  (timeReverseLIE (α := α) (E := E) (F := F) (hab := ht) (a' := 0) (b' := (slabDuration ht : ℝ))
    t₁ (sub_self t₁).symm (coe_slabDuration ht)).symm.toContinuousLinearEquiv.toContinuousLinearMap

private theorem norm_comp_timeReverse_bridges_le {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {t₀ t₁ : ℝ} (ht : t₀ < t₁)
    (T : HolderSpace α (slab (E := E) 0 (slabDuration ht)) F × CkHolderSpace 2 α E F →L[ℝ]
      ParabolicC2HolderSpace α E F (slabDuration_pos ht)) :
    ‖timeReverseSymmL ht ∘L T ∘L (terminalDataBridgeCLE ht).toContinuousLinearMap‖ ≤ ‖T‖ := by
  have h₁ : ‖timeReverseSymmL (α := α) (E := E) (F := F) ht‖ ≤ 1 :=
    (timeReverseLIE (α := α) (E := E) (F := F) (hab := ht) (a' := 0) (b' := (slabDuration ht : ℝ))
      t₁ (sub_self t₁).symm
      (coe_slabDuration ht)).symm.toLinearIsometry.norm_toContinuousLinearMap_le
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans <|
    (mul_le_of_le_one_left (norm_nonneg _) h₁).trans <|
    (ContinuousLinearMap.opNorm_comp_le _ _).trans <|
    mul_le_of_le_one_right (norm_nonneg _) (norm_terminalDataBridgeCLE_le_one ht)

/-- **The Schauder estimate for the backward terminal-value problem.** For `0 < α < 1`, an
ellipticity constant `λ > 0`, a bound `K` on the Hölder norms of the coefficients, and a horizon
bound `T₀`, the inverse terminal-data operators on `ℝⁿ × [t₀, t₁]` (`t₁ - t₀ ≤ T₀`) are bounded
uniformly in operator norm. -/
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
  refine ⟨C, hC, fun {t₀ t₁} ht hT₀ a b c ha hak hbk hck ↦ ?_⟩
  let eInit := (euclideanInitialDataCLE hα₀ hα₁ (slabDuration_pos ht)
    (fun i j ↦ timeReverseHolderCLE ht (a i j)) (fun i ↦ timeReverseHolderCLE ht (b i))
    (timeReverseHolderCLE ht c)
    ⟨lam, hlam, ellipticity_timeReverseHolderCLE ht ha⟩).symm.toContinuousLinearMap
  have hcomp :
      (euclideanTerminalDataCLE hα₀ hα₁ ht a b c ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap =
      timeReverseSymmL ht ∘L eInit ∘L (terminalDataBridgeCLE ht).toContinuousLinearMap := rfl
  rw [hcomp]
  exact (norm_comp_timeReverse_bridges_le ht eInit).trans <|
    hest (slabDuration ht) (slabDuration_pos ht) (by exact_mod_cast hT₀) _ _ _
      (ellipticity_timeReverseHolderCLE ht ha)
      (fun i j ↦ (norm_timeReverseHolderCLE_apply_le ht _).trans (hak i j))
      (fun i ↦ (norm_timeReverseHolderCLE_apply_le ht _).trans (hbk i))
      ((norm_timeReverseHolderCLE_apply_le ht _).trans hck)

/-- **Lipschitz dependence of the backward terminal-value solution operator on the coefficients.**
Under the uniform bounds of `exists_norm_euclideanTerminalDataCLE_symm_le`, the inverse
terminal-data operators for `(a, b, c)` and `(a', b', c')` on `ℝⁿ × [t₀, t₁]` differ in operator
norm by at most `C (∑ᵢⱼ ‖aⁱʲ - a'ⁱʲ‖ + ∑ᵢ ‖bⁱ - b'ⁱ‖ + ‖c - c'‖)`. -/
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
  refine ⟨C, hC, fun {t₀ t₁} ht hT₀ a a' b b' c c' ha ha' hak hbk hck hak' hbk' hck' ↦ ?_⟩
  have h0 := hest (slabDuration ht) (slabDuration_pos ht) (by exact_mod_cast hT₀) _ _ _ _ _ _
    (ellipticity_timeReverseHolderCLE ht ha) (ellipticity_timeReverseHolderCLE ht ha')
    (fun i j ↦ (norm_timeReverseHolderCLE_apply_le ht _).trans (hak i j))
    (fun i ↦ (norm_timeReverseHolderCLE_apply_le ht _).trans (hbk i))
    ((norm_timeReverseHolderCLE_apply_le ht _).trans hck)
    (fun i j ↦ (norm_timeReverseHolderCLE_apply_le ht _).trans (hak' i j))
    (fun i ↦ (norm_timeReverseHolderCLE_apply_le ht _).trans (hbk' i))
    ((norm_timeReverseHolderCLE_apply_le ht _).trans hck')
  set eInit := (euclideanInitialDataCLE hα₀ hα₁ (slabDuration_pos ht)
    (fun i j ↦ timeReverseHolderCLE ht (a i j)) (fun i ↦ timeReverseHolderCLE ht (b i))
    (timeReverseHolderCLE ht c)
    ⟨lam, hlam, ellipticity_timeReverseHolderCLE ht ha⟩).symm.toContinuousLinearMap
  set eInit' := (euclideanInitialDataCLE hα₀ hα₁ (slabDuration_pos ht)
    (fun i j ↦ timeReverseHolderCLE ht (a' i j)) (fun i ↦ timeReverseHolderCLE ht (b' i))
    (timeReverseHolderCLE ht c')
    ⟨lam, hlam, ellipticity_timeReverseHolderCLE ht ha'⟩).symm.toContinuousLinearMap
  have hsub :
      (euclideanTerminalDataCLE hα₀ hα₁ ht a b c ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap -
        (euclideanTerminalDataCLE hα₀ hα₁ ht a' b' c'
          ⟨lam, hlam, ha'⟩).symm.toContinuousLinearMap =
      timeReverseSymmL ht ∘L (eInit - eInit') ∘L (terminalDataBridgeCLE ht).toContinuousLinearMap :=
    ContinuousLinearMap.ext fun d ↦ by
      rw [_root_.sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        _root_.sub_apply, map_sub]
      exact congrArg₂ HSub.hSub rfl rfl
  rw [hsub]
  refine (norm_comp_timeReverse_bridges_le ht _).trans <|
    h0.trans (mul_le_mul_of_nonneg_left (add_le_add (add_le_add ?_ ?_) ?_) hC)
  · exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ by
      rw [← map_sub]; exact norm_timeReverseHolderCLE_apply_le ht _
  · exact Finset.sum_le_sum fun i _ ↦ by
      rw [← map_sub]; exact norm_timeReverseHolderCLE_apply_le ht _
  · rw [← map_sub]; exact norm_timeReverseHolderCLE_apply_le ht _

end TerminalData

end TauCeti.ParabolicC2HolderSpace
