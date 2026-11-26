/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Algebra
public import TauCeti.Analysis.Holder.Bilinear
public import TauCeti.Analysis.Holder.LipschitzDomain
public import TauCeti.Analysis.Holder.OpenSet.Frontier
public import TauCeti.Analysis.Holder.OpenSet.Laplacian
public import TauCeti.Analysis.Holder.OpenSet.Zero
import TauCeti.Analysis.Holder.Coefficient
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence.Basic

/-!
# Second-order operators in non-divergence form on `C^{2,α}(Ω)`

Let `Ω ⊆ ℝⁿ = EuclideanSpace ℝ ι` be a bounded Lipschitz domain and `α ≤ 1`. For coefficients
`aⁱʲ`, `bⁱ`, `c` in the bounded `α`-Hölder functions on `Ω`, this file defines the operator

`L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + ∑ᵢ bⁱ ∂ᵢu + c u`

as a continuous linear map from the Hölder space `C^{2,α}(Ω)` (`TauCeti.CkHolderSpaceOn 2 α Ω ℝ`)
to `C^{0,α}(Ω)`, in the form of the bounded `α`-Hölder functions on `Ω`
(`TauCeti.HolderSpace α Ω ℝ`). These are the spaces and the operator of the method of continuity
for the Dirichlet problem `L u = f` in `Ω`, `u = 0` on `∂Ω` (Gilbarg–Trudinger, Theorem 6.8, and
Theorem 6.14 on domains with `C^{2,α}` boundary): it deforms `L` to the Laplacian along the segment
`t ↦ (1 - t) Δ + t L` and transports solvability from `Δ` to `L`. The sign convention is that of
Gilbarg–Trudinger and of the maximum principle
`TauCeti.PDE.abs_le_mul_of_abs_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le_of_eq_zero_frontier`:
`a` is positive definite, and `c ≤ 0` is the sign condition for uniqueness.

The lower-order terms are where the geometry enters. The norm of `C^{2,α}(Ω)` only asks the
second derivatives to be Hölder on `Ω`; on a bounded Lipschitz domain the first derivatives and the
values are then Hölder too (`TauCeti.CkHolderSpaceOn.inclusionSuccLOfIsLipschitzDomain`), so that
`∂ᵢu` and `u` are multiplied by Hölder coefficients within `C^{0,α}(Ω)`. Across a slit this fails.

## Main declarations

* `TauCeti.CkHolderSpaceOn.nonDivergenceOperatorL`: the operator `L` with coefficients `a`, `b`,
  `c`, and `TauCeti.CkHolderSpaceOn.nonDivergenceOperatorL_apply`, its value at a point in terms of
  Mathlib's derivatives of any function agreeing with `u` on `Ω`.
* `TauCeti.CkHolderSpaceOn.nonDivergenceOperatorL_eq_laplacianL`: with `a` the identity matrix and
  `b = c = 0` it is the Laplacian `TauCeti.CkHolderSpaceOn.laplacianL`.
* `TauCeti.CkHolderSpaceOn.nonDivergenceOperatorL_lineMap`,
  `TauCeti.CkHolderSpaceOn.nonDivergenceOperatorL_sub_nonDivergenceOperatorL` and
  `TauCeti.CkHolderSpaceOn.exists_norm_nonDivergenceOperatorL_le`: `L` is affine in its
  coefficients and bounded by them, with a constant depending only on `Ω` and `α`, hence
  Lipschitz continuous in them in operator norm.
* `TauCeti.CkHolderSpaceOn.abs_apply_le_mul_norm_nonDivergenceOperatorL` and
  `TauCeti.CkHolderSpaceOn.injOn_nonDivergenceOperatorL`: for elliptic `a` and `c ≤ 0`, the maximum
  principle bounds `sup |u|` by a multiple of `sup |L u|` on the elements vanishing on `∂Ω`
  (`TauCeti.CkHolderSpaceOn.vanishingOnFrontierSubmodule`), so `L` is injective there.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 3.7 (the a priori bound by the maximum principle), Theorem 5.2 (the method of continuity)
  and Theorems 6.8 and 6.14 (its application to the Dirichlet problem in Hölder spaces).
-/

public section

noncomputable section

namespace TauCeti.CkHolderSpaceOn

open Set TopologicalSpace
open InnerProductSpace
open scoped NNReal Laplacian

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ℝ≥0}
  {Ω : Opens (EuclideanSpace ℝ ι)} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- The second-order part `u ↦ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu` of
`TauCeti.CkHolderSpaceOn.nonDivergenceOperatorL`. -/
private def secondOrderL (a : ι → ι → HolderSpace α Ω ℝ) :
    CkHolderSpaceOn 2 α Ω ℝ →L[ℝ] HolderSpace α Ω ℝ :=
  ∑ i, ∑ j, (ContinuousLinearMap.mul ℝ ℝ).compHolder₂ (a i j) ∘L
    HolderSpace.compLeftL (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 ↦ EuclideanSpace ℝ ι) ℝ
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) ∘L iteratedFDerivHolderL

/-- The first-order part `u ↦ ∑ᵢ bⁱ ∂ᵢu` of `TauCeti.CkHolderSpaceOn.nonDivergenceOperatorL`. -/
private def firstOrderL (hΩ : (Ω : Set (EuclideanSpace ℝ ι)).IsLipschitzDomain E')
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) (hα : α ≤ 1)
    (b : ι → HolderSpace α Ω ℝ) : CkHolderSpaceOn 2 α Ω ℝ →L[ℝ] HolderSpace α Ω ℝ :=
  ∑ i, (ContinuousLinearMap.mul ℝ ℝ).compHolder₂ (b i) ∘L
    HolderSpace.compLeftL (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 ↦ EuclideanSpace ℝ ι) ℝ
      ![EuclideanSpace.single i 1]) ∘L
    iteratedFDerivHolderL ∘L inclusionSuccLOfIsLipschitzDomain hΩ hb hα

/-- The zeroth-order part `u ↦ c u` of `TauCeti.CkHolderSpaceOn.nonDivergenceOperatorL`. -/
private def zerothOrderL (hΩ : (Ω : Set (EuclideanSpace ℝ ι)).IsLipschitzDomain E')
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) (hα : α ≤ 1)
    (c : HolderSpace α Ω ℝ) : CkHolderSpaceOn 2 α Ω ℝ →L[ℝ] HolderSpace α Ω ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).compHolder₂ c ∘L
    (zeroEquivHolderSpace (α := α) (Ω := Ω) (F := ℝ)).toContinuousLinearEquiv.toContinuousLinearMap
      ∘L inclusionSuccLOfIsLipschitzDomain hΩ hb hα ∘L inclusionSuccLOfIsLipschitzDomain hΩ hb hα

/-- The second-order operator `L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + ∑ᵢ bⁱ ∂ᵢu + c u` in non-divergence form on a
bounded Lipschitz domain `Ω ⊆ ℝⁿ`, with coefficients in the bounded `α`-Hölder functions on `Ω`, as
a continuous linear map from `C^{2,α}(Ω)` to the bounded `α`-Hölder functions on `Ω`. -/
def nonDivergenceOperatorL (hΩ : (Ω : Set (EuclideanSpace ℝ ι)).IsLipschitzDomain E')
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) (hα : α ≤ 1)
    (a : ι → ι → HolderSpace α Ω ℝ) (b : ι → HolderSpace α Ω ℝ) (c : HolderSpace α Ω ℝ) :
    CkHolderSpaceOn 2 α Ω ℝ →L[ℝ] HolderSpace α Ω ℝ :=
  secondOrderL a + firstOrderL hΩ hb hα b + zerothOrderL hΩ hb hα c

variable (hΩ : (Ω : Set (EuclideanSpace ℝ ι)).IsLipschitzDomain E')
  (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) (hα : α ≤ 1)

variable {a a' : ι → ι → HolderSpace α Ω ℝ} {b b' : ι → HolderSpace α Ω ℝ}
  {c c' : HolderSpace α Ω ℝ}

/-- The value of `L u` at a point of `Ω`, computed from any function `g` on `ℝⁿ` agreeing with `u`
on `Ω`: `L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼg + ∑ᵢ bⁱ ∂ᵢg + c g`. -/
theorem nonDivergenceOperatorL_apply (u : CkHolderSpaceOn 2 α Ω ℝ)
    {g : EuclideanSpace ℝ ι → ℝ} (hg : ∀ x : Ω, g x = u x) (x : Ω) :
    nonDivergenceOperatorL hΩ hb hα a b c u x =
      ∑ i, ∑ j, a i j x * fderiv ℝ (fderiv ℝ g) x (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) +
        ∑ i, b i x * fderiv ℝ g x (EuclideanSpace.single i 1) + c x * g x := by
  have h2 := u.iteratedFDeriv_eq hg (Fin.last 2) x
  have h1 := u.iteratedFDeriv_eq hg (Fin.castSucc (Fin.last 1)) x
  simp only [Fin.val_last, Fin.val_castSucc] at h1 h2
  simp only [nonDivergenceOperatorL, secondOrderL, firstOrderL, zerothOrderL, _root_.add_apply,
    FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.comp_apply, HolderSpace.add_apply, HolderSpace.sum_apply,
    ContinuousLinearMap.compHolder₂_apply, HolderSpace.compLeftL_apply,
    iteratedFDerivHolderL_apply, coe_iteratedFDerivHolder,
    iteratedFDeriv_inclusionSuccLOfIsLipschitzDomain, ContinuousLinearMap.mul_apply',
    ContinuousMultilinearMap.apply_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, zeroEquivHolderSpace_apply,
    inclusionSuccLOfIsLipschitzDomain_apply, ← hg, ← h1, ← h2, iteratedFDeriv_two_apply,
    iteratedFDeriv_one_apply]
  rfl

/-- With the identity matrix as principal coefficient and no lower-order terms, the operator is the
Laplacian. -/
theorem nonDivergenceOperatorL_eq_laplacianL :
    nonDivergenceOperatorL hΩ hb hα (fun i j ↦ if i = j then 1 else 0) 0 0 =
      laplacianL α Ω ℝ := by
  ext u x
  rw [nonDivergenceOperatorL_apply hΩ hb hα u u.extend_apply, laplacianL_apply_eq_laplacian_extend,
    laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun ι ℝ)]
  have hδ (i j : ι) :
      (if i = j then (1 : HolderSpace α Ω ℝ) else 0) x = if i = j then 1 else 0 := by
    split_ifs <;> simp [HolderSpace.one_apply, HolderSpace.zero_apply]
  simp [hδ, iteratedFDeriv_two_apply, HolderSpace.zero_apply]

/-- The operator is affine in its coefficients: along the segment between two sets of
coefficients it moves along the segment between the two operators. With `a₀ = I` and
`b₀ = c₀ = 0` this is the path `t ↦ (1 - t) Δ + t L` of the method of continuity. -/
theorem nonDivergenceOperatorL_lineMap (a₀ a₁ : ι → ι → HolderSpace α Ω ℝ)
    (b₀ b₁ : ι → HolderSpace α Ω ℝ) (c₀ c₁ : HolderSpace α Ω ℝ) (t : ℝ) :
    nonDivergenceOperatorL hΩ hb hα (AffineMap.lineMap a₀ a₁ t) (AffineMap.lineMap b₀ b₁ t)
        (AffineMap.lineMap c₀ c₁ t) =
      AffineMap.lineMap (nonDivergenceOperatorL hΩ hb hα a₀ b₀ c₀)
        (nonDivergenceOperatorL hΩ hb hα a₁ b₁ c₁) t := by
  ext u x
  simp only [AffineMap.lineMap_apply_module, _root_.add_apply, FunLike.coe_smul, Pi.smul_apply,
    HolderSpace.add_apply, HolderSpace.smul_apply,
    nonDivergenceOperatorL_apply hΩ hb hα u u.extend_apply, Pi.add_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

/-- The difference of two operators is the operator of the differences of the coefficients. -/
theorem nonDivergenceOperatorL_sub_nonDivergenceOperatorL :
    nonDivergenceOperatorL hΩ hb hα a b c - nonDivergenceOperatorL hΩ hb hα a' b' c' =
      nonDivergenceOperatorL hΩ hb hα (a - a') (b - b') (c - c') := by
  ext u x
  simp only [_root_.sub_apply, HolderSpace.sub_apply,
    nonDivergenceOperatorL_apply hΩ hb hα u u.extend_apply, Pi.sub_apply, sub_mul,
    Finset.sum_sub_distrib]
  ring

omit [DecidableEq ι] in
/-- Multiplication by a coefficient `f` has operator norm at most `‖f‖` on the bounded Hölder
functions. -/
private theorem norm_mul_compHolder₂_le (f : HolderSpace α Ω ℝ) :
    ‖(ContinuousLinearMap.mul ℝ ℝ).compHolder₂ (α := α) (X := Ω) f‖ ≤ ‖f‖ :=
  ((ContinuousLinearMap.mul ℝ ℝ).compHolder₂.le_opNorm f).trans
    (mul_le_of_le_one_left (norm_nonneg f) ((ContinuousLinearMap.norm_compHolder₂_le _).trans
      (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)))

omit [DecidableEq ι] in
/-- Evaluating a field of multilinear maps on vectors of norm at most one has operator norm at
most one on the bounded Hölder functions. -/
private theorem norm_compLeftL_apply_le_one {m : ℕ} {v : Fin m → EuclideanSpace ℝ ι}
    (hv : ∀ i, ‖v i‖ ≤ 1) :
    ‖HolderSpace.compLeftL (α := α) (X := Ω)
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m ↦ EuclideanSpace ℝ ι) ℝ v)‖ ≤ 1 := by
  refine (HolderSpace.norm_compLeftL_le _).trans
    (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦ ?_)
  rw [one_mul, ContinuousMultilinearMap.apply_apply]
  exact (f.le_opNorm v).trans (mul_le_of_le_one_right (norm_nonneg f)
    (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ hv i))

private theorem norm_secondOrderL_le (a : ι → ι → HolderSpace α Ω ℝ) :
    ‖secondOrderL a‖ ≤ ∑ i, ∑ j, ‖a i j‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun j _ ↦ ?_))
  calc _ ≤ _ * (_ * _) := (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ ‖a i j‖ * (1 * 1) := by
        gcongr
        · exact norm_mul_compHolder₂_le _
        · exact norm_compLeftL_apply_le_one (Fin.forall_fin_two.2 ⟨by simp, by simp⟩)
        · exact norm_iteratedFDerivHolderL_le_one
    _ = ‖a i j‖ := by ring

private theorem norm_firstOrderL_le (b : ι → HolderSpace α Ω ℝ) :
    ‖firstOrderL hΩ hb hα b‖ ≤
      ‖inclusionSuccLOfIsLipschitzDomain (k := 1) (F := ℝ) hΩ hb hα‖ * ∑ i, ‖b i‖ := by
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  calc _ ≤ _ * (_ * (_ * _)) := (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (by gcongr; refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
              gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ ‖b i‖ * (1 * (1 * ‖inclusionSuccLOfIsLipschitzDomain (k := 1) (F := ℝ) hΩ hb hα‖)) := by
        gcongr
        · exact norm_mul_compHolder₂_le _
        · exact norm_compLeftL_apply_le_one (Fin.forall_fin_one.2 (by simp))
        · exact norm_iteratedFDerivHolderL_le_one
    _ = _ := by ring

omit [DecidableEq ι] in
private theorem norm_zerothOrderL_le (c : HolderSpace α Ω ℝ) :
    ‖zerothOrderL hΩ hb hα c‖ ≤
      ‖inclusionSuccLOfIsLipschitzDomain (k := 0) (F := ℝ) hΩ hb hα‖ *
        ‖inclusionSuccLOfIsLipschitzDomain (k := 1) (F := ℝ) hΩ hb hα‖ * ‖c‖ := by
  calc _ ≤ _ * (_ * (_ * _)) := (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (by gcongr; refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
              gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ ‖c‖ * (1 * (‖inclusionSuccLOfIsLipschitzDomain (k := 0) (F := ℝ) hΩ hb hα‖ *
          ‖inclusionSuccLOfIsLipschitzDomain (k := 1) (F := ℝ) hΩ hb hα‖)) := by
        gcongr
        · exact norm_mul_compHolder₂_le _
        · exact LinearIsometry.norm_toContinuousLinearMap_le zeroEquivHolderSpace.toLinearIsometry
    _ = _ := by ring

/-- **The operator bound.** There is a constant `C`, depending only on `Ω` and `α`, such that
`‖L‖ ≤ C (∑ᵢⱼ ‖aⁱʲ‖ + ∑ᵢ ‖bⁱ‖ + ‖c‖)` in operator norm from `C^{2,α}(Ω)` to `C^{0,α}(Ω)`. With
`TauCeti.CkHolderSpaceOn.nonDivergenceOperatorL_sub_nonDivergenceOperatorL` this makes `L`
Lipschitz continuous in its coefficients. -/
theorem exists_norm_nonDivergenceOperatorL_le :
    ∃ C : ℝ, ∀ (a : ι → ι → HolderSpace α Ω ℝ) (b : ι → HolderSpace α Ω ℝ)
      (c : HolderSpace α Ω ℝ),
      ‖nonDivergenceOperatorL hΩ hb hα a b c‖ ≤
        C * (∑ i, ∑ j, ‖a i j‖ + ∑ i, ‖b i‖ + ‖c‖) := by
  set I₂ := ‖inclusionSuccLOfIsLipschitzDomain (k := 1) (F := ℝ) hΩ hb hα‖
  set I₁ := ‖inclusionSuccLOfIsLipschitzDomain (k := 0) (F := ℝ) hΩ hb hα‖
  refine ⟨1 + I₂ + I₁ * I₂, fun a b c ↦ ?_⟩
  have hI₂ : 0 ≤ I₂ := norm_nonneg _
  have hI₁ : 0 ≤ I₁ := norm_nonneg _
  have hA := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦
    Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) ↦ norm_nonneg (a i j)
  have hB := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦ norm_nonneg (b i)
  have hC := norm_nonneg c
  refine (norm_add_le _ _).trans
    ((add_le_add (norm_add_le _ _) (norm_zerothOrderL_le hΩ hb hα c)).trans ?_)
  refine (add_le_add (add_le_add (norm_secondOrderL_le a) (norm_firstOrderL_le hΩ hb hα b))
    le_rfl).trans ?_
  nlinarith [mul_nonneg hI₂ hA, mul_nonneg hI₂ hC, mul_nonneg (mul_nonneg hI₁ hI₂) hA,
    mul_nonneg (mul_nonneg hI₁ hI₂) hB]

/-- **The a priori bound by the maximum principle.** Let `a` be uniformly elliptic with constant
`λ > 0` on `Ω` and let `c ≤ 0` on `Ω`. Every `u ∈ C^{2,α}(Ω)` vanishing on the frontier of `Ω`
satisfies `|u| ≤ D sup_Ω |L u|` on `Ω`, with `D = (exp ((β / λ + 1) diam Ω) - 1) / λ` and
`β = ∑ᵢ ‖bⁱ‖`. -/
theorem abs_apply_le_mul_norm_nonDivergenceOperatorL [Nonempty ι] {lam : ℝ} (hlam : 0 < lam)
    (ha : ∀ (x : Ω) (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j x).toQuadraticForm' ξ)
    (hc : ∀ x : Ω, c x ≤ 0) {u : CkHolderSpaceOn 2 α Ω ℝ}
    (hu : u ∈ vanishingOnFrontierSubmodule 2 α Ω ℝ) (x : Ω) :
    |u x| ≤ (Real.exp (((∑ i, ‖b i‖) / lam + 1) *
        Metric.diam (closure (Ω : Set (EuclideanSpace ℝ ι)))) - 1) / lam *
      ‖nonDivergenceOperatorL hΩ hb hα a b c u‖ := by
  classical
  -- The coefficients, extended by zero to functions on `ℝⁿ`.
  obtain ⟨A, hA⟩ : ∃ A : EuclideanSpace ℝ ι → Matrix ι ι ℝ,
      ∀ y (hy : y ∈ Ω), A y = Matrix.of fun i j ↦ a i j ⟨y, hy⟩ :=
    ⟨fun y ↦ if hy : y ∈ Ω then Matrix.of fun i j ↦ a i j ⟨y, hy⟩ else 0,
      fun y hy ↦ by simp only [hy, dite_true]⟩
  obtain ⟨B, hB⟩ : ∃ B : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι,
      ∀ y (hy : y ∈ Ω), B y = ∑ i, b i ⟨y, hy⟩ • EuclideanSpace.single i 1 :=
    ⟨fun y ↦ if hy : y ∈ Ω then ∑ i, b i ⟨y, hy⟩ • EuclideanSpace.single i 1 else 0,
      fun y hy ↦ by simp only [hy, dite_true]⟩
  obtain ⟨C', hC'⟩ : ∃ C' : EuclideanSpace ℝ ι → ℝ, ∀ y (hy : y ∈ Ω), C' y = c ⟨y, hy⟩ :=
    ⟨fun y ↦ if hy : y ∈ Ω then c ⟨y, hy⟩ else 0, fun y hy ↦ by simp only [hy, dite_true]⟩
  have h := PDE.abs_le_mul_of_abs_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le_of_eq_zero_frontier
    (a := A) (b := B) (c := C') (f := u.extend) hb hΩ.interior_closure hlam
    (fun y hy ξ ↦ hA y hy ▸ ha ⟨y, hy⟩ ξ)
    (fun y hy ↦ hB y hy ▸ HolderSpace.norm_sum_apply_smul_single_le_sum_norm b _)
    (fun y hy ↦ hC' y hy ▸ hc ⟨y, hy⟩)
    (Finset.sum_nonneg fun i _ ↦ norm_nonneg (b i)) (norm_nonneg _)
    (continuousOn_extend_closure hu)
    (fun y hy ↦ u.contDiffOn_extend.contDiffAt (Ω.isOpen.mem_nhds hy))
    (fun y hy ↦ by
      have h := HolderSpace.abs_apply_le_norm (nonDivergenceOperatorL hΩ hb hα a b c u) ⟨y, hy⟩
      rw [nonDivergenceOperatorL_apply hΩ hb hα u u.extend_apply] at h
      rw [hA y hy, hB y hy, hC' y hy]
      simpa only [Matrix.of_apply, map_sum, map_smul, smul_eq_mul] using h)
    (fun y hy ↦ u.extend_apply_of_mem_frontier hy) (subset_closure x.property)
  rwa [u.extend_apply] at h

/-- **Uniqueness for the Dirichlet problem.** For uniformly elliptic `a` and `c ≤ 0` on `Ω`, the
operator `L` is injective on the elements of `C^{2,α}(Ω)` vanishing on the frontier of `Ω`. -/
theorem injOn_nonDivergenceOperatorL [Nonempty ι] {lam : ℝ} (hlam : 0 < lam)
    (ha : ∀ (x : Ω) (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j x).toQuadraticForm' ξ)
    (hc : ∀ x : Ω, c x ≤ 0) :
    InjOn (nonDivergenceOperatorL hΩ hb hα a b c) (vanishingOnFrontierSubmodule 2 α Ω ℝ) := by
  intro u hu v hv huv
  have hsub := (vanishingOnFrontierSubmodule 2 α Ω ℝ).sub_mem hu hv
  rw [← sub_eq_zero]
  ext x
  have h := abs_apply_le_mul_norm_nonDivergenceOperatorL hΩ hb hα (b := b) hlam ha hc hsub x
  rw [map_sub, sub_eq_zero.2 huv, norm_zero, mul_zero, abs_nonpos_iff] at h
  rw [h, coe_zero, Pi.zero_apply]

end TauCeti.CkHolderSpaceOn
