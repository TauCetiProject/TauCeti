/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Schauder
import TauCeti.Analysis.Matrix.QuadraticBounds
import TauCeti.Analysis.Normed.Operator.MethodOfContinuity
import TauCeti.Analysis.PDE.Ellipticity.Basic

/-!
# The parabolic Cauchy problem with Hölder coefficients

On `ℝⁿ = EuclideanSpace ℝ ι` and a time slab `ℝⁿ × [0, T]`, let

`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

have coefficients `aⁱʲ`, `bⁱ`, `c` in the bounded parabolic Hölder space `C_b^{α,α/2}`, with
`0 < α < 1`, and let `a` be uniformly elliptic: `λ ‖ξ‖² ≤ ξᵀ a(p) ξ` at every point `p`, with
`0 < λ`. This file proves that the Cauchy problem

`P u = f`,  `u(·, 0) = g`

has exactly one solution `u` in the bounded order-two parabolic Hölder space `C_b^{2+α,1+α/2}`
for every forcing `f ∈ C_b^{α,α/2}` and initial datum `g ∈ C_b^{2,α}`: the map
`u ↦ (P u, u(·, 0))` is an isomorphism of Banach spaces
`C_b^{2+α,1+α/2} ≃ C_b^{α,α/2} × C_b^{2,α}`. No symmetry of `a` and no sign condition on `c` is
needed. The solution operators are bounded uniformly over coefficients with a fixed ellipticity
constant and a fixed bound on their Hölder norms and over horizons `T ≤ T₀`, and they depend
Lipschitz continuously on the coefficients in operator norm.

## The argument

This is the method of continuity (`ContinuousLinearMap.surjective_iff_of_forall_norm_le_lineMap`)
started from the heat operator. Along the segment of coefficients
`((1 - t) δᵢⱼ + t aⁱʲ, t bⁱ, t c)`, `t ∈ [0, 1]`, the initial-data maps `u ↦ (P_t u, u(·, 0))` are
the points of the segment between the initial-data maps of the heat operator and of `P`. Every
`P_t` has ellipticity constant `min 1 λ` and coefficients bounded by a common constant, so the
global Schauder estimate
(`TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL`) bounds `‖u‖` by a
multiple of `‖(P_t u, u(·, 0))‖` uniformly in `t`. The initial-data map of the heat operator is
surjective
(`TauCeti.ParabolicC2HolderSpace.bijective_euclideanParabolicOperatorL_const_prod_spatialTraceL`),
hence so is that of `P`, and the Schauder estimate makes it injective. The same estimate bounds
the inverse, and the resolvent identity `e⁻¹ - e'⁻¹ = e⁻¹ (e' - e) e'⁻¹` together with the
Lipschitz dependence of `P` on its coefficients
(`TauCeti.ParabolicC2HolderSpace.norm_euclideanParabolicOperatorL_sub_le`) gives the Lipschitz
dependence of the solution operator.

## Main declarations

All declarations are in the `TauCeti.ParabolicC2HolderSpace` namespace.

* `bijective_euclideanParabolicOperatorL_prod_spatialTraceL`: existence and uniqueness for the
  Cauchy problem.
* `euclideanInitialDataCLE`: the initial-data isomorphism `u ↦ (P u, u(·, 0))`, with
  `euclideanInitialDataCLE_apply`, and the equation and initial condition for its inverse,
  `euclideanParabolicOperatorL_euclideanInitialDataCLE_symm_apply`,
  `spatialTrace_euclideanInitialDataCLE_symm_apply` and
  `euclideanInitialDataCLE_symm_apply_slabMk_zero`.
* `exists_norm_euclideanInitialDataCLE_symm_le`: the uniform bound on the solution operators.
* `exists_norm_euclideanInitialDataCLE_symm_sub_le`: their Lipschitz dependence on the
  coefficients.

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

/-- The forcing-and-initial-trace operator along the segment of coefficients from the heat
operator `(δᵢⱼ, 0, 0)` to `(a, b, c)` is the operator with the interpolated coefficients. -/
private theorem lineMap_euclideanParabolicOperatorL_prod_apply (hα : α ≤ 1) (hT : (0 : ℝ) < T)
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ) (t : ℝ)
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) :
    AffineMap.lineMap
      ((euclideanParabolicOperatorL hα (fun i j ↦ HolderSpace.const ((1 : Matrix ι ι ℝ) i j))
        0 0).prod (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩))
      ((euclideanParabolicOperatorL hα a b c).prod
        (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩)) t u =
      (euclideanParabolicOperatorL hα
        (fun i j ↦ (1 - t) • HolderSpace.const ((1 : Matrix ι ι ℝ) i j) + t • a i j)
        (t • b) (t • c) u, u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩) := by
  rw [AffineMap.lineMap_apply_module]
  refine Prod.ext (HolderSpace.ext fun p ↦ ?_) ?_
  · simp [euclideanParabolicOperatorL_apply, HolderSpace.add_apply, HolderSpace.smul_apply,
      add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  · simp [spatialTraceL_apply, ← add_smul]


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

omit [DecidableEq ι] in
/-- A common bound `K ≥ 1` for the Hölder norms of the coefficients, which then also bounds the
coefficients `(δᵢⱼ, 0, 0)` of the heat operator. -/
private theorem exists_one_le_and_norm_le
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ) :
    ∃ K : ℝ≥0, 1 ≤ (K : ℝ) ∧ (∀ i j, ‖a i j‖ ≤ K) ∧ (∀ i, ‖b i‖ ≤ K) ∧ ‖c‖ ≤ K := by
  have hA : 0 ≤ ∑ i, ∑ j, ‖a i j‖ := by positivity
  have hB : 0 ≤ ∑ i, ‖b i‖ := by positivity
  refine ⟨1 + ∑ i, ∑ j, ‖a i j‖₊ + ∑ i, ‖b i‖₊ + ‖c‖₊, ?_, fun i j ↦ ?_, fun i ↦ ?_, ?_⟩ <;>
    push_cast
  · linarith [norm_nonneg c]
  · have h₁ := Finset.single_le_sum (f := fun j ↦ ‖a i j‖) (fun _ _ ↦ norm_nonneg _)
      (Finset.mem_univ j)
    have h₂ := Finset.single_le_sum (f := fun i ↦ ∑ j, ‖a i j‖) (fun _ _ ↦ by positivity)
      (Finset.mem_univ i)
    linarith [norm_nonneg c]
  · have h₁ := Finset.single_le_sum (f := fun i ↦ ‖b i‖) (fun _ _ ↦ norm_nonneg _)
      (Finset.mem_univ i)
    linarith [norm_nonneg c]
  · linarith

/-- **Solvability of the parabolic Cauchy problem.** For `0 < α < 1`, coefficients `aⁱʲ`, `bⁱ`,
`c` in `C_b^{α,α/2}(ℝⁿ × [0, T])` with `a` uniformly elliptic, `λ ‖ξ‖² ≤ ξᵀ a ξ` with `0 < λ`,
the map `u ↦ (∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u, u(·, 0))` from `C_b^{2+α,1+α/2}(ℝⁿ × [0, T])` to
`C_b^{α,α/2}(ℝⁿ × [0, T]) × C_b^{2,α}(ℝⁿ)` is bijective: for every forcing `f` and initial datum
`g` the Cauchy problem `P u = f`, `u(·, 0) = g` has exactly one solution. -/
theorem bijective_euclideanParabolicOperatorL_prod_spatialTraceL (hα₀ : 0 < α) (hα₁ : α < 1)
    (hT : (0 : ℝ) < T) {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ) {lam : ℝ} (hlam : 0 < lam)
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    Function.Bijective ((euclideanParabolicOperatorL hα₁.le a b c).prod
      (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩)) := by
  obtain ⟨K, hK₁, hak, hbk, hck⟩ := exists_one_le_and_norm_le a b c
  obtain ⟨C, -, hest⟩ := exists_norm_le_mul_norm_prod (ι := ι) hα₀ hα₁ (lt_min one_pos hlam) K T
  -- The Schauder estimate holds uniformly along the segment from the heat operator to `P`.
  have hpath : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u, ‖u‖ ≤ C * ‖AffineMap.lineMap
      ((euclideanParabolicOperatorL hα₁.le
        (fun i j ↦ HolderSpace.const ((1 : Matrix ι ι ℝ) i j)) 0 0).prod
        (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩))
      ((euclideanParabolicOperatorL hα₁.le a b c).prod
        (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩)) t u‖ := by
    rintro t ⟨ht₀, ht₁⟩ u
    rw [lineMap_euclideanParabolicOperatorL_prod_apply]
    have hδ : ∀ i j, ‖HolderSpace.const (α := α) (X := slab (E := EuclideanSpace ℝ ι) 0 T)
        ((1 : Matrix ι ι ℝ) i j)‖ ≤ K := fun i j ↦ (HolderSpace.norm_const_le _).trans <| by
      rw [Matrix.one_apply]
      split_ifs <;> simp [hK₁]
    have hseg : ∀ i j, ‖(1 - t) • HolderSpace.const ((1 : Matrix ι ι ℝ) i j) + t • a i j‖ ≤ K :=
      fun i j ↦ mem_closedBall_zero_iff.1 <| convex_closedBall 0 (K : ℝ)
        (mem_closedBall_zero_iff.2 (hδ i j)) (mem_closedBall_zero_iff.2 (hak i j))
        (sub_nonneg.2 ht₁) ht₀ (sub_add_cancel 1 t)
    refine hest T hT le_rfl _ _ _ (fun p ξ ↦ ?_) hseg (fun i ↦ ?_) ?_ u
    · -- The segment matrices are uniformly elliptic with constant `min 1 λ`.
      convert PDE.min_mul_le_toQuadraticForm'_smul_add_smul (A := 1)
        (fun ξ ↦ (one_mul _).trans_le (PDE.toQuadraticForm'_one ξ).ge) (ha p)
        (sub_nonneg.2 ht₁) ht₀ (sub_add_cancel 1 t) ξ using 3
      ext i j
      simp [HolderSpace.add_apply, HolderSpace.smul_apply]
    · simpa [norm_smul, Real.norm_of_nonneg ht₀] using
        (mul_le_of_le_one_left (norm_nonneg _) ht₁).trans (hbk i)
    · simpa [norm_smul, Real.norm_of_nonneg ht₀] using
        (mul_le_of_le_one_left (norm_nonneg _) ht₁).trans hck
  refine ⟨ContinuousLinearMap.injective_of_forall_norm_le fun u ↦ by
      simpa using hpath 1 (right_mem_Icc.2 zero_le_one) u,
    (ContinuousLinearMap.surjective_iff_of_forall_norm_le_lineMap hpath).1 ?_⟩
  -- The method of continuity starts from the heat operator.
  exact (bijective_euclideanParabolicOperatorL_const_prod_spatialTraceL hα₀ hα₁ one_pos
    (fun ξ ↦ by rw [one_mul, PDE.toQuadraticForm'_one]) hT).2

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
    have hL := norm_euclideanParabolicOperatorL_sub_le (ht := hT) hα₁.le (a := a') (b := b')
      (c := c') a b c
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

end TauCeti.ParabolicC2HolderSpace
