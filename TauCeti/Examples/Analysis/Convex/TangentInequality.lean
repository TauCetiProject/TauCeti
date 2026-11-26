/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Strong
public import TauCeti.Analysis.MeanInequalities
public import TauCeti.Analysis.MvPolynomial.Hyperbolic.Esymm

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Checks: Hessian quotients and the tangent inequality in the plane

The tangent inequality for a function `g` that is concave and positively homogeneous of degree
one on an open convex cone `Γ` reads `g(μ) ≤ Dg(λ) μ` for `λ, μ ∈ Γ` with `g` differentiable at
`λ` (`ConcaveOn.le_apply_of_hasFDerivAt_of_homogeneous`). In `ℝ²`:

* For `σ₂ / σ₁ = λ₁λ₂ / (λ₁ + λ₂)`, the value at `(4, 1)` and at `(1, 4)` is `4/5`, and at the
  midpoint `(5/2, 5/2)` it is `5/4 ≥ 4/5` (`hessianQuotient_four_one`,
  `hessianQuotient_one_four`, `hessianQuotient_midpoint`).
* `σ₂` itself is not concave on `Γ₂`, the open quadrant: `σ₂(t e) = t²`
  (`eval_smul_one_esymm_two`, `not_concaveOn_esymm_two`).
* For `g = σ₁` the tangent inequality is an equality, `Dg(λ) μ = g(μ)`
  (`fderiv_sum_apply`). For the geometric mean `g = σ₂^{1/2}` at `λ = (1, 4)` and `μ = (4, 1)` it
  reads `2 ≤ 4·1 + 1·(1/4) = 17/4` (`geomMean_four_one`, `fderiv_geomMean_apply`,
  `geomMean_le_fderiv_geomMean`).
* Differentiability at `λ` is needed: `g = min(x, y)` is concave and positively homogeneous on the
  open quadrant (`concaveOn_minFun`, `minFun_smul`), but it is not differentiable at `(1, 1)`
  (`not_differentiableAt_minFun`), where its total derivative is therefore `0`, and the
  inequality at `λ = μ = (1, 1)` would read `1 ≤ 0` (`not_minFun_le_fderiv_minFun`). At the point
  of differentiability `λ = (1, 2)`, where `∇g = (1, 0)`, it reads `g(2, 1) = 1 ≤ 2`
  (`hasFDerivAt_minFun`, `minFun_le_fderiv_minFun`).
-/

public section

noncomputable section

open MvPolynomial Filter Topology

namespace TauCeti.Examples.TangentInequality

/-- The open positive quadrant of `ℝ²`. -/
abbrev quadrant : Set (Fin 2 → ℝ) := {μ | ∀ i, 0 < μ i}

/-- The open quadrant is convex. -/
theorem convex_quadrant : Convex ℝ quadrant := by
  simpa [Set.pi] using convex_pi (s := Set.univ) fun i _ ↦ convex_Ioi (0 : ℝ)

/-! ### The quotient `σ₂ / σ₁` -/

/-- The Hessian quotient `σ₂ / σ₁ = λ₁λ₂ / (λ₁ + λ₂)` in two variables. -/
def hessianQuotient (μ : Fin 2 → ℝ) : ℝ := μ 0 * μ 1 / (μ 0 + μ 1)

/-- `σ₂ / σ₁` at `(4, 1)` is `4/5`. -/
theorem hessianQuotient_four_one : hessianQuotient ![4, 1] = 4 / 5 := by
  norm_num [hessianQuotient]

/-- `σ₂ / σ₁` at `(1, 4)` is `4/5`. -/
theorem hessianQuotient_one_four : hessianQuotient ![1, 4] = 4 / 5 := by
  norm_num [hessianQuotient]

/-- At the midpoint `(5/2, 5/2)` of `(4, 1)` and `(1, 4)`, `σ₂ / σ₁` takes the value `5/4`, at
least the common value `4/5` at the endpoints, as concavity requires. -/
theorem hessianQuotient_midpoint :
    hessianQuotient ((1 / 2 : ℝ) • ![4, 1] + (1 / 2 : ℝ) • ![1, 4]) = 5 / 4 ∧
      (4 / 5 : ℝ) ≤ 5 / 4 := by
  refine ⟨?_, by norm_num⟩
  norm_num [hessianQuotient]

/-! ### `σ₂` is not concave on `Γ₂` -/

/-- `σ₂` in two variables is the product of the coordinates. -/
theorem eval_esymm_two (μ : Fin 2 → ℝ) : eval μ (esymm (Fin 2) ℝ 2) = μ 0 * μ 1 := by
  simpa [Fin.prod_univ_two] using congrArg (eval μ) (esymm_card (σ := Fin 2) (R := ℝ))

/-- `σ₂(t e) = t²` on the diagonal of `ℝ²`. -/
theorem eval_smul_one_esymm_two (t : ℝ) :
    eval (t • 1 : Fin 2 → ℝ) (esymm (Fin 2) ℝ 2) = t ^ 2 := by
  simp [eval_esymm_two, sq]

/-- `Γ₂` in `ℝ²` is the open quadrant. -/
theorem gardingCone_esymm_two : gardingCone (esymm (Fin 2) ℝ 2) 1 = quadrant := by
  have h := gardingCone_esymm_card (σ := Fin 2)
  rw [Fintype.card_fin] at h
  exact h

/-- **`σ₂` is not concave on `Γ₂ ⊂ ℝ²`**: on the diagonal it is `t ↦ t²`, and its value `4` at
`2e` is less than the average `5` of its values `1` at `e` and `9` at `3e`. -/
theorem not_concaveOn_esymm_two :
    ¬ ConcaveOn ℝ (gardingCone (esymm (Fin 2) ℝ 2) 1) fun μ ↦ eval μ (esymm (Fin 2) ℝ 2) := by
  rw [gardingCone_esymm_two]
  intro h
  have := h.2 (show (1 : ℝ) • (1 : Fin 2 → ℝ) ∈ quadrant from fun i ↦ by simp)
    (show (3 : ℝ) • (1 : Fin 2 → ℝ) ∈ quadrant from fun i ↦ by simp)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hmid : (1 / 2 : ℝ) • ((1 : ℝ) • (1 : Fin 2 → ℝ)) + (1 / 2 : ℝ) • ((3 : ℝ) • 1) =
      (2 : ℝ) • 1 := by
    rw [smul_smul, smul_smul, ← add_smul]
    norm_num
  rw [hmid] at this
  simp only [eval_smul_one_esymm_two, smul_eq_mul] at this
  norm_num at this

/-! ### The tangent inequality for `σ₁` and for the geometric mean -/

/-- **The tangent inequality for `σ₁` is an equality**: `σ₁` is linear, so `Dσ₁(λ) μ = σ₁(μ)`. -/
theorem fderiv_sum_apply {ι : Type*} [Fintype ι] (lam μ : ι → ℝ) :
    fderiv ℝ (fun x : ι → ℝ ↦ ∑ i, x i) lam μ = ∑ i, μ i := by
  rw [show (fun x : ι → ℝ ↦ ∑ i, x i) = ∑ i, fun x : ι → ℝ ↦ x i by ext; simp,
    (HasFDerivAt.sum (u := Finset.univ) (A := fun i (x : ι → ℝ) ↦ x i)
      fun i _ ↦ hasFDerivAt_apply i lam).fderiv]
  simp

/-- The geometric mean `σ₂^{1/2} = (λ₁λ₂)^{1/2}` on `ℝ²`, in the form of
`Real.concaveOn_prod_rpow`. -/
def geomMean (μ : Fin 2 → ℝ) : ℝ := (∏ i, μ i) ^ (Fintype.card (Fin 2) : ℝ)⁻¹

/-- The geometric mean on `ℝ²` written out. -/
theorem geomMean_eq (μ : Fin 2 → ℝ) : geomMean μ = (μ 0 * μ 1) ^ (2⁻¹ : ℝ) := by
  simp [geomMean, Fin.prod_univ_two]

/-- `(4 : ℝ) ^ (1/2) = 2`. -/
theorem four_rpow_inv_two : (4 : ℝ) ^ (2⁻¹ : ℝ) = 2 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← Nat.cast_ofNat (R := ℝ) (n := 2),
    Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]

/-- `σ₂(4, 1)^{1/2} = 2`. -/
theorem geomMean_four_one : geomMean ![4, 1] = 2 := by
  rw [geomMean_eq]
  norm_num [four_rpow_inv_two]

/-- The derivative of the geometric mean at a point of the open quadrant. -/
theorem hasFDerivAt_geomMean {lam : Fin 2 → ℝ} (hlam : lam ∈ quadrant) :
    HasFDerivAt geomMean (((Fintype.card (Fin 2) : ℝ)⁻¹ *
        (∏ i, lam i) ^ ((Fintype.card (Fin 2) : ℝ)⁻¹ - 1)) •
      ∑ i, (∏ j ∈ Finset.univ.erase i, lam j) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) i) lam :=
  (hasFDerivAt_finsetProd (u := Finset.univ) (x := lam)).rpow_const
    (Or.inl (Finset.prod_pos fun i _ ↦ hlam i).ne')

/-- **`Dg(1, 4)(4, 1) = 4·1 + 1·(1/4) = 17/4`** for the geometric mean `g = σ₂^{1/2}`: its
partial derivatives at `(1, 4)` are `1` and `1/4`. -/
theorem fderiv_geomMean_apply : fderiv ℝ geomMean ![1, 4] ![4, 1] = 17 / 4 := by
  rw [(hasFDerivAt_geomMean (lam := ![1, 4]) fun i ↦ by fin_cases i <;> norm_num).fderiv]
  have h : (2⁻¹ - 1 : ℝ) = -2⁻¹ := by norm_num
  have hu : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  have hv : (Finset.univ.erase (1 : Fin 2)) = {0} := by decide
  simp [Fin.prod_univ_two, Fin.sum_univ_two, hu, hv, h, Real.rpow_neg, four_rpow_inv_two]
  norm_num

/-- `σ₂^{1/2}` is positively homogeneous of degree one on the quadrant. -/
theorem eventually_geomMean_smul {lam : Fin 2 → ℝ} (hlam : lam ∈ quadrant) :
    ∀ᶠ t in 𝓝 (1 : ℝ), geomMean (t • lam) = t * geomMean lam := by
  filter_upwards [lt_mem_nhds one_pos] with t ht
  simpa [geomMean] using Real.prod_mul_rpow_inv_card ht.le fun i ↦ (hlam i).le

/-- **The tangent inequality for `σ₂^{1/2}` at `λ = (1, 4)`, `μ = (4, 1)`**:
`g(4, 1) = 2 ≤ 17/4 = Dg(1, 4)(4, 1)`, an instance of
`ConcaveOn.le_apply_of_hasFDerivAt_of_homogeneous`. -/
theorem geomMean_le_fderiv_geomMean :
    geomMean ![4, 1] ≤ fderiv ℝ geomMean ![1, 4] ![4, 1] := by
  have hlam : (![1, 4] : Fin 2 → ℝ) ∈ quadrant := fun i ↦ by fin_cases i <;> norm_num
  exact (Real.concaveOn_prod_rpow.subset (fun μ hμ i ↦ (hμ i).le)
    convex_quadrant).le_apply_of_hasFDerivAt_of_homogeneous hlam
    (fun i ↦ by fin_cases i <;> norm_num)
    (hasFDerivAt_geomMean hlam).differentiableAt.hasFDerivAt (eventually_geomMean_smul hlam)

/-! ### `min(x, y)`: differentiability is needed -/

/-- The function `g(x, y) = min(x, y)` on `ℝ²`. -/
def minFun (μ : Fin 2 → ℝ) : ℝ := min (μ 0) (μ 1)

/-- `min(x, y)` is concave, as the minimum of two linear functions. -/
theorem concaveOn_minFun : ConcaveOn ℝ quadrant minFun :=
  ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0).concaveOn convex_quadrant).inf
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1).concaveOn convex_quadrant)

/-- `min(x, y)` is positively homogeneous of degree one. -/
theorem minFun_smul {t : ℝ} (ht : 0 ≤ t) (μ : Fin 2 → ℝ) : minFun (t • μ) = t * minFun μ := by
  simp [minFun, mul_min_of_nonneg _ _ ht]

/-- If `g ≤ φ` with equality at `λ`, and both are differentiable at `λ`, then their derivatives
at `λ` agree: `g - φ` has a maximum at `λ`. -/
private theorem fderiv_eq_of_le_of_eq {g φ : (Fin 2 → ℝ) → ℝ} {lam : Fin 2 → ℝ}
    (hle : ∀ μ, g μ ≤ φ μ) (heq : g lam = φ lam) (hg : DifferentiableAt ℝ g lam)
    (hφ : DifferentiableAt ℝ φ lam) : fderiv ℝ g lam = fderiv ℝ φ lam := by
  have hmax : IsLocalMax (fun μ ↦ g μ - φ μ) lam :=
    Eventually.of_forall fun μ ↦ by simp only [heq, sub_self, sub_nonpos]; exact hle μ
  have := IsLocalMax.fderiv_eq_zero hmax
  rw [fderiv_fun_sub hg hφ, sub_eq_zero] at this
  exact this

/-- **`min(x, y)` is not differentiable at `(1, 1)`**: its derivative there would have to be both
coordinate projections, since `min(x, y) ≤ x`, `min(x, y) ≤ y` with equality at `(1, 1)`. -/
theorem not_differentiableAt_minFun : ¬ DifferentiableAt ℝ minFun ![1, 1] := by
  intro h
  have h0 := fderiv_eq_of_le_of_eq (φ := fun μ ↦ μ 0) (fun μ ↦ min_le_left _ _)
    (by simp) h (differentiableAt_apply 0 _)
  have h1 := fderiv_eq_of_le_of_eq (φ := fun μ ↦ μ 1) (fun μ ↦ min_le_right _ _)
    (by simp) h (differentiableAt_apply 1 _)
  have := congrArg (fun L ↦ L (Pi.single 0 1)) (h0.symm.trans h1)
  simp [fderiv_apply] at this

/-- **Without differentiability the tangent inequality fails**: at `λ = μ = (1, 1)` the total
derivative of `min(x, y)` is `0` (Mathlib's value at a point of non-differentiability), and the
inequality would read `1 ≤ 0`. -/
theorem not_minFun_le_fderiv_minFun : ¬ minFun ![1, 1] ≤ fderiv ℝ minFun ![1, 1] ![1, 1] := by
  rw [fderiv_zero_of_not_differentiableAt not_differentiableAt_minFun]
  norm_num [minFun]

/-- Near `(1, 2)`, `min(x, y) = x`, so the derivative of `min(x, y)` at `(1, 2)` is the first
coordinate projection, `∇g = (1, 0)`. -/
theorem hasFDerivAt_minFun :
    HasFDerivAt minFun (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0)
      ![1, 2] := by
  refine (hasFDerivAt_apply 0 _).congr_of_eventuallyEq ?_
  have hc : Continuous fun μ : Fin 2 → ℝ ↦ μ 1 - μ 0 := by fun_prop
  filter_upwards [hc.continuousAt.eventually (lt_mem_nhds (show (0 : ℝ) < 2 - 1 by norm_num))]
    with μ hμ
  simp only [sub_pos] at hμ
  exact min_eq_left hμ.le

/-- **The tangent inequality for `min(x, y)` at the point of differentiability `λ = (1, 2)`**,
`μ = (2, 1)`: `g(2, 1) = 1 ≤ 2 = Dg(1, 2)(2, 1)`. -/
theorem minFun_le_fderiv_minFun : minFun ![2, 1] ≤ fderiv ℝ minFun ![1, 2] ![2, 1] := by
  have hlam : (![1, 2] : Fin 2 → ℝ) ∈ quadrant := fun i ↦ by fin_cases i <;> norm_num
  refine concaveOn_minFun.le_apply_of_hasFDerivAt_of_homogeneous hlam
    (fun i ↦ by fin_cases i <;> norm_num) hasFDerivAt_minFun.differentiableAt.hasFDerivAt ?_
  filter_upwards [lt_mem_nhds one_pos] with t ht
  exact minFun_smul ht.le _

/-- The two sides of `minFun_le_fderiv_minFun` are `1` and `2`. -/
theorem minFun_two_one_and_fderiv :
    minFun ![2, 1] = 1 ∧ fderiv ℝ minFun ![1, 2] ![2, 1] = 2 := by
  refine ⟨by norm_num [minFun], ?_⟩
  rw [hasFDerivAt_minFun.fderiv]
  simp

end TauCeti.Examples.TangentInequality
