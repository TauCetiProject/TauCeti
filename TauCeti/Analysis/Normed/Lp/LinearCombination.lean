/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.NormedSpace
import TauCeti.Analysis.Normed.Lp.Basic

/-!
# The universal property of `ℓ¹`

Let `R` be a normed ring, `ι` an arbitrary index type, and `M` a Banach `R`-module with contractive
scalar action (`IsBoundedSMul R M`). Every bounded family `e : lp (fun _ : ι ↦ M) ∞` defines a
continuous `R`-linear map

`lp.linearCombination R e : lp (fun _ : ι ↦ R) 1 →L[R] M`, `a ↦ ∑' i, a i • e i`.

The series converges unconditionally because `‖a i • e i‖ ≤ ‖e‖ * ‖a i‖` and the coordinates of `a`
have summable norms (`lp.hasSum_norm_one`). The resulting sum has norm at most `‖e‖ * ‖a‖`, sends
each coordinate vector `lp.single 1 i r` to `r • e i`, and is uniquely determined among continuous
`R`-linear maps by its values on the unit coordinate vectors `lp.single 1 i 1`.

Over a nontrivially normed field `𝕜`, the operator norm of `lp.linearCombination 𝕜 e` equals `‖e‖`,
and every continuous linear map `u : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] M` arises from the bounded family
`i ↦ u (lp.single 1 i 1)`. Bundling this correspondence yields the linear isometric equivalence

`lp.linearCombinationEquiv 𝕜 ι M : lp (fun _ : ι ↦ M) ∞ ≃ₗᵢ[𝕜] (lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] M)`.

For `M = 𝕜` over `ℝ` or `ℂ`, this recovers the `(ℓ¹)* ≃ₗᵢ ℓ∞` case of `lp.dualEquiv` in
`TauCeti.Analysis.Normed.Lp.Dual`, while extending it to vector-valued targets and arbitrary
nontrivially normed fields. In the nonarchimedean setting, the analogous universal property of
`C₀(ι, R)` is developed in `TauCeti.Topology.ContinuousMap.ZeroAtInfty.LinearCombination`.

## Main definitions

* `lp.linearCombination`: the continuous `R`-linear map `lp (fun _ : ι ↦ R) 1 →L[R] M` sending `a`
  to `∑' i, a i • e i`.
* `lp.linearCombinationEquiv`: the linear isometric equivalence between bounded families
  `lp (fun _ : ι ↦ M) ∞` and continuous linear maps `lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] M`.

## Main results

* `lp.hasSum_linearCombination`: the unconditional expansion `HasSum (fun i ↦ a i • e i) (...)`.
* `lp.linearCombination_single`: evaluation on a coordinate vector `lp.single 1 i r`.
* `lp.eq_linearCombination_iff`: characterization by values at the unit coordinate vectors.
* `lp.norm_linearCombination`: over a nontrivially normed field, `‖linearCombination 𝕜 e‖ = ‖e‖`.
* `lp.linearCombination_injective` and `lp.linearCombination_surjective`: bijectivity of the
  correspondence between bounded families and continuous linear maps out of `ℓ¹`.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, 2nd ed., Springer, 2016, Chapter 1.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press, 1987, Chapter 1.
-/

public section

open scoped ENNReal NNReal

namespace lp

section Construction

variable {ι R M : Type*} [NormedRing R] [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

private theorem norm_smul_apply_le (a : lp (fun _ : ι ↦ R) 1) (e : lp (fun _ : ι ↦ M) ∞)
    (i : ι) : ‖a i • e i‖ ≤ ‖e‖ * ‖a i‖ :=
  calc ‖a i • e i‖ ≤ ‖a i‖ * ‖e i‖ := norm_smul_le (a i) (e i)
    _ ≤ ‖a i‖ * ‖e‖ :=
        mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm ENNReal.top_ne_zero e i) (norm_nonneg _)
    _ = ‖e‖ * ‖a i‖ := mul_comm _ _

/-- Pairing an `ℓ¹` scalar sequence with an `ℓ∞` vector family produces an absolutely summable
family of norms. -/
theorem summable_norm_smul (a : lp (fun _ : ι ↦ R) 1) (e : lp (fun _ : ι ↦ M) ∞) :
    Summable fun i ↦ ‖a i • e i‖ :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_smul_apply_le a e)
    ((lp.hasSum_norm_one a).mul_left ‖e‖).summable

/-- The unconditional sum `∑' i, a i • e i` is bounded in norm by `‖e‖ * ‖a‖`, without assuming
completeness of `M`. -/
theorem norm_tsum_smul_le (a : lp (fun _ : ι ↦ R) 1) (e : lp (fun _ : ι ↦ M) ∞) :
    ‖∑' i, a i • e i‖ ≤ ‖e‖ * ‖a‖ :=
  tsum_of_norm_bounded ((lp.hasSum_norm_one a).mul_left ‖e‖) (norm_smul_apply_le a e)

variable [CompleteSpace M]

/-- In a complete module, pairing an `ℓ¹` scalar sequence with an `ℓ∞` vector family gives an
unconditionally summable series. -/
theorem summable_smul (a : lp (fun _ : ι ↦ R) 1) (e : lp (fun _ : ι ↦ M) ∞) :
    Summable fun i ↦ a i • e i :=
  .of_norm (summable_norm_smul a e)

variable (R) in
/-- The **linear combination map** attached to a bounded family `e` in a complete module: the
continuous `R`-linear map `lp (fun _ : ι ↦ R) 1 →L[R] M` sending `a` to `∑' i, a i • e i`. -/
noncomputable def linearCombination (e : lp (fun _ : ι ↦ M) ∞) :
    lp (fun _ : ι ↦ R) 1 →L[R] M :=
  LinearMap.mkContinuous
    { toFun a := ∑' i, a i • e i
      map_add' a b := by
        simp only [lp.coeFn_add, Pi.add_apply, add_smul]
        exact (summable_smul a e).tsum_add (summable_smul b e)
      map_smul' c a := by
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
        exact (summable_smul a e).tsum_const_smul c }
    ‖e‖ fun a ↦ norm_tsum_smul_le a e

/-- The value of the linear combination map is the unconditional sum `∑' i, a i • e i`. -/
theorem linearCombination_apply (e : lp (fun _ : ι ↦ M) ∞) (a : lp (fun _ : ι ↦ R) 1) :
    linearCombination R e a = ∑' i, a i • e i :=
  (rfl)

/-- **Unconditional expansion**: `linearCombination R e a` is the unconditional sum of the terms
`a i • e i`. -/
theorem hasSum_linearCombination (e : lp (fun _ : ι ↦ M) ∞) (a : lp (fun _ : ι ↦ R) 1) :
    HasSum (fun i ↦ a i • e i) (linearCombination R e a) :=
  (summable_smul a e).hasSum

/-- The linear combination map sends the coordinate vector `lp.single 1 i r` to `r • e i`. -/
@[simp]
theorem linearCombination_single [DecidableEq ι] (e : lp (fun _ : ι ↦ M) ∞) (i : ι) (r : R) :
    linearCombination R e (lp.single 1 i r) = r • e i := by
  rw [linearCombination_apply, tsum_eq_single i fun j hj ↦ by simp [hj], lp.single_apply_self]

/-- A continuous `R`-linear map out of `ℓ¹` equals `linearCombination R e` if and only if it sends
each unit coordinate vector `lp.single 1 i 1` to `e i`. -/
theorem eq_linearCombination_iff [DecidableEq ι] {e : lp (fun _ : ι ↦ M) ∞}
    {u : lp (fun _ : ι ↦ R) 1 →L[R] M} :
    u = linearCombination R e ↔ ∀ i, u (lp.single 1 i 1) = e i := by
  refine ⟨by rintro rfl i; simp, fun h ↦ ?_⟩
  refine lp.ext_continuousLinearMap ENNReal.one_ne_top fun i ↦ ContinuousLinearMap.ext_ring ?_
  simp [h i]

/-- Pairing the single-coordinate family `lp.single ∞ i m` with `a` gives `a i • m`. -/
@[simp]
theorem linearCombination_lpSingle [DecidableEq ι] (i : ι) (m : M) (a : lp (fun _ : ι ↦ R) 1) :
    linearCombination R (lp.single ∞ i m) a = a i • m := by
  rw [linearCombination_apply, tsum_eq_single i fun j hj ↦ by simp [hj], lp.single_apply_self]

/-- Pointwise norm bound for the linear combination map. -/
theorem norm_linearCombination_apply_le (e : lp (fun _ : ι ↦ M) ∞) (a : lp (fun _ : ι ↦ R) 1) :
    ‖linearCombination R e a‖ ≤ ‖e‖ * ‖a‖ :=
  norm_tsum_smul_le a e

/-- The zero family induces the zero continuous linear map. -/
@[simp]
theorem linearCombination_zero : linearCombination R (0 : lp (fun _ : ι ↦ M) ∞) = 0 := by
  classical
  exact (eq_linearCombination_iff.mpr fun _ ↦ rfl).symm

/-- The linear combination map is additive in the bounded family. -/
theorem linearCombination_add (e f : lp (fun _ : ι ↦ M) ∞) :
    linearCombination R (e + f) = linearCombination R e + linearCombination R f := by
  classical
  exact (eq_linearCombination_iff.mpr fun i ↦ by simp).symm

/-- The linear combination map commutes with negation of the bounded family. -/
@[simp]
theorem linearCombination_neg (e : lp (fun _ : ι ↦ M) ∞) :
    linearCombination R (-e) = -linearCombination R e := by
  classical
  exact (eq_linearCombination_iff.mpr fun i ↦ by simp).symm

/-- The linear combination map is subtractive in the bounded family. -/
theorem linearCombination_sub (e f : lp (fun _ : ι ↦ M) ∞) :
    linearCombination R (e - f) = linearCombination R e - linearCombination R f := by
  classical
  exact (eq_linearCombination_iff.mpr fun i ↦ by simp).symm

/-- A bounded family is uniquely determined by its linear combination map. -/
theorem linearCombination_injective :
    Function.Injective
      (linearCombination R : lp (fun _ : ι ↦ M) ∞ → lp (fun _ : ι ↦ R) 1 →L[R] M) := by
  classical
  intro e f h
  ext i
  simpa using congr($h (lp.single 1 i (1 : R)))

end Construction

section CommRing

variable {ι R M : Type*} [NormedCommRing R]

/-- Over a commutative normed ring, the linear combination map is homogeneous in the family. -/
theorem linearCombination_smul [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
    [CompleteSpace M] (c : R) (e : lp (fun _ : ι ↦ M) ∞) :
    linearCombination R (c • e) = c • linearCombination R e := by
  classical
  exact (eq_linearCombination_iff.mpr fun i ↦ by simp).symm

/-- For scalar-valued families over a complete commutative normed ring, the linear combination map
is the series pairing `∑' i, b i * a i`. -/
theorem linearCombination_eq_tsum_mul [CompleteSpace R] (b : lp (fun _ : ι ↦ R) ∞)
    (a : lp (fun _ : ι ↦ R) 1) :
    linearCombination R b a = ∑' i, b i * a i := by
  simp_rw [linearCombination_apply, smul_eq_mul, mul_comm]

end CommRing

section Field

variable {𝕜 ι M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup M] [NormedSpace 𝕜 M]

/-- The values of any continuous linear map out of `ℓᵖ` (`1 ≤ p`) on the unit coordinate vectors
form a bounded family, bounded in norm by the operator norm. -/
theorem memℓp_infty_apply_single [DecidableEq ι] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : lp (fun _ : ι ↦ 𝕜) p →L[𝕜] M) :
    Memℓp (fun i ↦ u (lp.single p i 1)) ∞ := by
  refine memℓp_infty ⟨‖u‖, ?_⟩
  rintro _ ⟨i, rfl⟩
  simpa [lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p))] using
    u.le_opNorm (lp.single p i (1 : 𝕜))

variable [CompleteSpace M]

/-- The operator norm of `linearCombination 𝕜 e` is at most `‖e‖`. -/
theorem norm_linearCombination_le (e : lp (fun _ : ι ↦ M) ∞) :
    ‖linearCombination 𝕜 e‖ ≤ ‖e‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg e) (norm_linearCombination_apply_le e)

/-- **Operator norm of a linear combination map**: over a nontrivially normed field, the operator
norm of `linearCombination 𝕜 e` equals the `ℓ∞` norm `‖e‖` of the family. -/
@[simp]
theorem norm_linearCombination (e : lp (fun _ : ι ↦ M) ∞) :
    ‖linearCombination 𝕜 e‖ = ‖e‖ := by
  classical
  refine le_antisymm (norm_linearCombination_le e)
    (lp.norm_le_of_forall_le (norm_nonneg _) fun i ↦ ?_)
  simpa [lp.norm_single zero_lt_one] using
    (linearCombination 𝕜 e).le_opNorm (lp.single 1 i (1 : 𝕜))

/-- Nonnegative operator norm of `linearCombination 𝕜 e`. -/
@[simp]
theorem nnNorm_linearCombination (e : lp (fun _ : ι ↦ M) ∞) :
    ‖linearCombination 𝕜 e‖₊ = ‖e‖₊ :=
  NNReal.eq (norm_linearCombination e)

/-- Every continuous linear map out of `ℓ¹` is the linear combination map of its values at the unit
coordinate vectors. -/
theorem linearCombination_self [DecidableEq ι] (u : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] M) :
    linearCombination 𝕜 ⟨fun i ↦ u (lp.single 1 i 1), memℓp_infty_apply_single u⟩ = u :=
  (eq_linearCombination_iff.mpr fun _ ↦ rfl).symm

/-- Over a nontrivially normed field, every continuous linear map from `ℓ¹` into a Banach space is
the linear combination map of some bounded family. -/
theorem linearCombination_surjective :
    Function.Surjective
      (linearCombination 𝕜 : lp (fun _ : ι ↦ M) ∞ → lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] M) := by
  classical
  exact fun u ↦ ⟨_, linearCombination_self u⟩

variable (𝕜 ι M) in
/-- **The universal property of `ℓ¹`.** Bounded families `ι → M` in a Banach space over a
nontrivially normed field correspond isometrically to continuous linear maps
`lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] M`, sending `e` to `linearCombination 𝕜 e` and `u` to its values on
the unit coordinate vectors. -/
noncomputable def linearCombinationEquiv :
    lp (fun _ : ι ↦ M) ∞ ≃ₗᵢ[𝕜] (lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] M) :=
  LinearIsometryEquiv.ofSurjective
    { toFun := linearCombination 𝕜
      map_add' := linearCombination_add
      map_smul' := linearCombination_smul
      norm_map' := norm_linearCombination }
    linearCombination_surjective

/-- The forward map of `linearCombinationEquiv` is `linearCombination`. -/
@[simp]
theorem linearCombinationEquiv_apply (e : lp (fun _ : ι ↦ M) ∞) :
    linearCombinationEquiv 𝕜 ι M e = linearCombination 𝕜 e :=
  (rfl)

/-- The inverse of `linearCombinationEquiv` evaluates an operator at each unit coordinate vector. -/
@[simp]
theorem linearCombinationEquiv_symm_apply [DecidableEq ι]
    (u : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] M) (i : ι) :
    (linearCombinationEquiv 𝕜 ι M).symm u i = u (lp.single 1 i 1) := by
  have h := congrArg (fun g : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] M ↦ g (lp.single 1 i 1))
    ((linearCombinationEquiv 𝕜 ι M).apply_symm_apply u)
  simpa only [linearCombinationEquiv_apply, linearCombination_single, one_smul] using h

end Field

end lp
