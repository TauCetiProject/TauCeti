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

The same holds for the backward operator `P_back u = ∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u` with terminal
data: the terminal-value problem `P_back u = f`, `u(·, T) = g` has exactly one solution in
`C_b^{2+α,1+α/2}`, the terminal-data map `u ↦ (P_back u, u(·, T))` is an isomorphism of Banach
spaces, and its inverse is bounded uniformly and depends Lipschitz continuously on the
coefficients, with the same kind of bounds.

## The argument

The uniform bound is the global Schauder estimate
(`TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL`). The resolvent
identity `e⁻¹ - e'⁻¹ = e⁻¹ (e' - e) e'⁻¹` together with the Lipschitz dependence of `P` on its
coefficients (`TauCeti.ParabolicC2HolderSpace.norm_euclideanParabolicOperatorL_sub_le`) gives the
Lipschitz dependence of the solution operator.

The backward problem is reduced to the forward one by the time reversal `R (x, s) = (x, T - s)`,
which maps the slab `ℝⁿ × [0, T]` onto itself: `P_back u = f` holds exactly when `v = u ∘ R`
solves `P_R v = -f ∘ R`, where `P_R` is the forward operator with the reversed coefficients
`aⁱʲ ∘ R`, `bⁱ ∘ R`, `c ∘ R`
(`TauCeti.ParabolicC2HolderSpace.euclideanParabolicOperatorL_timeReverseLIE`), and the initial
trace of `v` is the terminal trace of `u`. Time reversal is an isometry and keeps
the ellipticity constant and the coefficient norms, so the bounds transfer.

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
  `euclideanTerminalDataCLE_apply`, and the equation and terminal condition for its inverse,
  `euclideanBackwardParabolicOperatorL_euclideanTerminalDataCLE_symm_apply`,
  `spatialTrace_euclideanTerminalDataCLE_symm_apply` and
  `euclideanTerminalDataCLE_symm_apply_slabMk_right`.
* `exists_norm_euclideanTerminalDataCLE_symm_le` and
  `exists_norm_euclideanTerminalDataCLE_symm_sub_le`: the uniform bound on the solution operators
  of the terminal-value problems and their Lipschitz dependence on the coefficients.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 5.2 (the method of continuity) and its use in Theorem 6.8 (the elliptic analogue).
* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 2, Section 4, for
  backward equations with terminal data.
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

/-! ### The terminal-data isomorphism of the backward problem -/

section TerminalData

/-- Time reversal `(x, s) ↦ (x, T - s)`, mapping the slab `ℝⁿ × [0, T]` onto itself. -/
private abbrev slabReverse (T : ℝ≥0) :
    slab (E := EuclideanSpace ℝ ι) 0 T ≃ᵢ slab (E := EuclideanSpace ℝ ι) 0 T :=
  slabTimeReverse (T : ℝ) (sub_self _).symm (sub_zero _).symm

/-- Time reversal of maps on `ℝⁿ × [0, T]`: precomposition with `slabReverse T`. -/
private abbrev reverseL (T : ℝ≥0) :
    HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ →L[ℝ]
      HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ :=
  HolderSpace.compLipschitzL _ (slabReverse T).isometry.lipschitzWith

omit [DecidableEq ι] in
private theorem reverseL_apply (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (p : slab (E := EuclideanSpace ℝ ι) 0 T) : reverseL T f p = f (slabReverse T p) :=
  HolderSpace.compLipschitzL_apply _ f p

omit [DecidableEq ι] in
private theorem reverseL_reverseL (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ) :
    reverseL T (reverseL T f) = f := by
  ext p
  have h := (slabReverse T).apply_symm_apply p
  rw [slabTimeReverse_symm] at h
  rw [reverseL_apply, reverseL_apply, h]

/-- Time reversal preserves the uniform ellipticity of a coefficient matrix. -/
private theorem reverseL_elliptic
    {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ} {lam : ℝ}
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (p : slab (E := EuclideanSpace ℝ ι) 0 T) (ξ : EuclideanSpace ℝ ι) :
    lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ reverseL T (a i j) p).toQuadraticForm' ξ := by
  simpa only [reverseL_apply] using ha _ ξ

private theorem exists_reverseL_elliptic
    {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ reverseL T (a i j) p).toQuadraticForm' ξ :=
  ha.imp fun _ h ↦ ⟨h.1, reverseL_elliptic h.2⟩

omit [DecidableEq ι] in
private theorem norm_reverseL_apply_le (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ) :
    ‖reverseL T f‖ ≤ ‖f‖ :=
  (ContinuousLinearMap.le_of_opNorm_le _ (HolderSpace.norm_compLipschitzL_le_one _) f).trans_eq
    (one_mul _)

/-- The data of a backward problem on `ℝⁿ × [0, T]` transported to those of the reversed forward
problem, `(g, h) ↦ (-g ∘ R, h)`. It is an involution. -/
private def reverseDataCLE (T : ℝ≥0) :
    (HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
        CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) ≃L[ℝ]
      HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
        CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ :=
  (ContinuousLinearEquiv.equivOfInverse (-reverseL T) (-reverseL T)
    (fun f ↦ by simp [reverseL_reverseL]) (fun f ↦ by simp [reverseL_reverseL])).prodCongr
    (ContinuousLinearEquiv.refl ℝ _)

omit [DecidableEq ι] in
private theorem reverseDataCLE_apply
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    reverseDataCLE T d = (-reverseL T d.1, d.2) :=
  (rfl)

omit [DecidableEq ι] in
private theorem reverseDataCLE_symm_apply
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    (reverseDataCLE T).symm d = (-reverseL T d.1, d.2) :=
  (rfl)

omit [DecidableEq ι] in
private theorem norm_reverseDataCLE_symm_apply_le
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    ‖(reverseDataCLE T).symm d‖ ≤ ‖d‖ := by
  rw [reverseDataCLE_symm_apply, Prod.norm_def, Prod.norm_def, norm_neg]
  exact max_le_max (norm_reverseL_apply_le _) le_rfl

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
  (timeReverseLIE (T : ℝ) (sub_self _).symm (sub_zero _).symm).toContinuousLinearEquiv.trans
    ((euclideanInitialDataCLE hα₀ hα₁ hT (fun i j ↦ reverseL T (a i j)) (fun i ↦ reverseL T (b i))
      (reverseL T c) (exists_reverseL_elliptic ha)).trans (reverseDataCLE T))

section TerminalDataCLE

variable {hα₀ : 0 < α} {hα₁ : α < 1} {hT : (0 : ℝ) < T}
  {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
  {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
  {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
  {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
    lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ}

/-- The terminal-data isomorphism sends `u` to its forcing `P_back u` and its terminal trace. -/
@[simp]
theorem euclideanTerminalDataCLE_apply (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) :
    euclideanTerminalDataCLE hα₀ hα₁ hT a b c ha u =
      (euclideanBackwardParabolicOperatorL hα₁.le a b c u,
        u.spatialTrace ⟨T, right_mem_Icc.2 hT.le⟩) := by
  simp only [euclideanTerminalDataCLE, ContinuousLinearEquiv.trans_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, euclideanInitialDataCLE_apply,
    reverseDataCLE_apply, euclideanParabolicOperatorL_timeReverseLIE, map_neg, neg_neg,
    reverseL_reverseL]
  exact Prod.ext rfl (spatialTrace_timeReverseLIE_left u)

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

/-- The inverse of the terminal-data isomorphism is the inverse of the initial-data isomorphism
of the reversed forward problem, read through time reversal. -/
private theorem euclideanTerminalDataCLE_symm_apply
    (d : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    (euclideanTerminalDataCLE hα₀ hα₁ hT a b c ha).symm d =
      (timeReverseLIE (T : ℝ) (sub_self _).symm (sub_zero _).symm).symm
        ((euclideanInitialDataCLE hα₀ hα₁ hT (fun i j ↦ reverseL T (a i j))
          (fun i ↦ reverseL T (b i)) (reverseL T c) (exists_reverseL_elliptic ha)).symm
            ((reverseDataCLE T).symm d)) :=
  (rfl)

end TerminalDataCLE

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
  refine ⟨C, hC, fun T hT hTT₀ a b c ha hak hbk hck ↦
    ContinuousLinearMap.opNorm_le_bound _ hC fun d ↦ ?_⟩
  have h := hest T hT hTT₀ (fun i j ↦ reverseL T (a i j)) (fun i ↦ reverseL T (b i))
    (reverseL T c) (reverseL_elliptic ha) (fun i j ↦ (norm_reverseL_apply_le _).trans (hak i j))
    (fun i ↦ (norm_reverseL_apply_le _).trans (hbk i)) ((norm_reverseL_apply_le _).trans hck)
  rw [ContinuousLinearEquiv.coe_coe, euclideanTerminalDataCLE_symm_apply]
  calc _ = ‖(euclideanInitialDataCLE hα₀ hα₁ hT (fun i j ↦ reverseL T (a i j))
          (fun i ↦ reverseL T (b i)) (reverseL T c) ⟨lam, hlam, reverseL_elliptic ha⟩).symm
            ((reverseDataCLE T).symm d)‖ :=
        (timeReverseLIE (T : ℝ) (sub_self _).symm (sub_zero _).symm).symm.norm_map _
    _ ≤ C * ‖(reverseDataCLE T).symm d‖ := by
        simpa only [ContinuousLinearEquiv.coe_coe] using
          ContinuousLinearMap.le_of_opNorm_le _ h ((reverseDataCLE T).symm d)
    _ ≤ C * ‖d‖ := mul_le_mul_of_nonneg_left (norm_reverseDataCLE_symm_apply_le d) hC

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
  have hrev (f f' : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ) :
      ‖reverseL T f - reverseL T f'‖ ≤ ‖f - f'‖ := by
    rw [← map_sub]
    exact norm_reverseL_apply_le _
  -- The forward estimate for the reversed coefficients, whose differences are no larger.
  have h := (hest T hT hTT₀ (fun i j ↦ reverseL T (a i j)) (fun i j ↦ reverseL T (a' i j))
    (fun i ↦ reverseL T (b i)) (fun i ↦ reverseL T (b' i)) (reverseL T c) (reverseL T c')
    (reverseL_elliptic ha) (reverseL_elliptic ha')
    (fun i j ↦ (norm_reverseL_apply_le _).trans (hak i j))
    (fun i ↦ (norm_reverseL_apply_le _).trans (hbk i)) ((norm_reverseL_apply_le _).trans hck)
    (fun i j ↦ (norm_reverseL_apply_le _).trans (hak' i j))
    (fun i ↦ (norm_reverseL_apply_le _).trans (hbk' i))
    ((norm_reverseL_apply_le _).trans hck')).trans
    (mul_le_mul_of_nonneg_left (add_le_add (add_le_add
      (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hrev _ _)
      (Finset.sum_le_sum fun i _ ↦ hrev _ _)) (hrev _ _)) hC)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun d ↦ ?_
  set f := euclideanInitialDataCLE hα₀ hα₁ hT (fun i j ↦ reverseL T (a i j))
    (fun i ↦ reverseL T (b i)) (reverseL T c) ⟨lam, hlam, reverseL_elliptic ha⟩
  set f' := euclideanInitialDataCLE hα₀ hα₁ hT (fun i j ↦ reverseL T (a' i j))
    (fun i ↦ reverseL T (b' i)) (reverseL T c') ⟨lam, hlam, reverseL_elliptic ha'⟩
  set y := (reverseDataCLE T).symm d
  rw [_root_.sub_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe,
    euclideanTerminalDataCLE_symm_apply, euclideanTerminalDataCLE_symm_apply]
  calc _ = ‖(timeReverseLIE (hab := hT) (T : ℝ) (sub_self _).symm (sub_zero _).symm).symm
          (f.symm y - f'.symm y)‖ := by rw [map_sub]
    _ = ‖f.symm y - f'.symm y‖ :=
        (timeReverseLIE (hab := hT) (T : ℝ) (sub_self _).symm (sub_zero _).symm).symm.norm_map _
    _ ≤ C * (∑ i, ∑ j, ‖a i j - a' i j‖ + ∑ i, ‖b i - b' i‖ + ‖c - c'‖) * ‖y‖ := by
        simpa only [_root_.sub_apply, ContinuousLinearEquiv.coe_coe] using
          ContinuousLinearMap.le_of_opNorm_le _ h y
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_reverseDataCLE_symm_apply_le d) (by positivity)

end TerminalData

end TauCeti.ParabolicC2HolderSpace
