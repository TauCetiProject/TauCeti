/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.Integral
public import TauCeti.Algebra.HopfAlgebra.Opposite

/-!
# Basis-free Frobenius dual-basis reconstruction from integrals and cointegrals

Over an arbitrary commutative semiring, normalized integrals and cointegrals on a Hopf algebra `H`
satisfy explicit basis-free Frobenius dual-basis reconstruction formulas (and their partner
formulas) without assuming finite-dimensionality, the Orzech property, or a base field.

## Main results

* `TauCeti.IsRightCointegral.sum_apply_mul_smul_antipode`:
  `∑ φ (x * t₁) • S(t₂) = x` for a right cointegral `φ` and normalized left integral `t`.
* `TauCeti.IsLeftCointegral.sum_apply_mul_smul_antipode`:
  `∑ φ (t₂ * x) • S(t₁) = x` for a left cointegral `φ` and normalized right integral `t`.
* `TauCeti.IsRightCointegral.sum_apply_mul_smul_eq_antipode`:
  `∑ φ (t₁ * x) • t₂ = S(x)` for a right cointegral `φ` and normalized right integral `t`.
* `TauCeti.IsLeftCointegral.sum_apply_mul_smul_eq_antipode`:
  `∑ φ (x * t₂) • t₁ = S(x)` for a left cointegral `φ` and normalized left integral `t`.
* `TauCeti.IsRightCointegral.sum_apply_mul_smul_inverseAntipode`:
  `∑ φ (t₁ * x) • S⁻¹(t₂) = x` when `S` is bijective.
* `TauCeti.IsLeftCointegral.sum_apply_mul_smul_inverseAntipode`:
  `∑ φ (x * t₂) • S⁻¹(t₁) = x` when `S` is bijective.
* `TauCeti.IsRightCointegral.sum_apply_antipode_mul_smul`,
  `TauCeti.IsLeftCointegral.sum_apply_mul_antipode_smul`,
  `TauCeti.IsRightCointegral.sum_apply_mul_inverseAntipode_smul`,
  `TauCeti.IsLeftCointegral.sum_apply_inverseAntipode_mul_smul`: dual-basis partner formulas over
  an arbitrary commutative semiring.

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. 91 (1969), 75–94.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, AMS, 1993, Chapter 2.
* D. Fischman, S. Montgomery, and H.-J. Schneider, *Frobenius extensions of subalgebras of Hopf
  algebras*, Trans. Amer. Math. Soc. 349 (1997), 4857–4895, Lemma 1.5.
-/

public section

open scoped Coalgebra TensorProduct

namespace TauCeti

universe u v

section Semiring

variable {R : Type u} {H : Type v} [CommSemiring R] [Semiring H] [HopfAlgebra R H]

private theorem apply_mul_of_mem_leftIntegral {φ : Module.Dual R H} {t : H}
    (ht : t ∈ leftIntegral R H) (htφ : φ t = 1) (y : H) :
    φ (y * t) = Coalgebra.counit (R := R) y := by
  simp [(mem_leftIntegral_iff.mp ht) y, htφ]

private theorem apply_mul_of_mem_rightIntegral {φ : Module.Dual R H} {t : H}
    (ht : t ∈ rightIntegral R H) (htφ : φ t = 1) (y : H) :
    φ (t * y) = Coalgebra.counit (R := R) y := by
  simp [(mem_rightIntegral_iff.mp ht) y, htφ]

/-- Reconstruction from a right cointegral and a normalized left integral:
`∑ φ (x * t₁) • S(t₂) = x`. -/
theorem IsRightCointegral.sum_apply_mul_smul_antipode {φ : Module.Dual R H}
    (hφ : IsRightCointegral φ) {t : H} (ht : t ∈ leftIntegral R H) (htφ : φ t = 1)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (x * r.left i) • HopfAlgebra.antipode R (r.right i) = x := by
  classical
  rw [← (LinearMap.isRightInvariantIntegral_iff_isRightCointegral.mpr hφ).strong_invariance
    (ℛ R x) r]
  simpa only [apply_mul_of_mem_leftIntegral ht htφ] using Coalgebra.sum_counit_smul (ℛ R x)

/-- Reconstruction from a left cointegral and a normalized right integral:
`∑ φ (t₂ * x) • S(t₁) = x`. -/
theorem IsLeftCointegral.sum_apply_mul_smul_antipode {φ : Module.Dual R H}
    (hφ : IsLeftCointegral φ) {t : H} (ht : t ∈ rightIntegral R H) (htφ : φ t = 1)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (r.right i * x) • HopfAlgebra.antipode R (r.left i) = x := by
  classical
  rw [← (LinearMap.isLeftInvariantIntegral_iff_isLeftCointegral.mpr hφ).strong_invariance
    (ℛ R x) r]
  simpa only [apply_mul_of_mem_rightIntegral ht htφ] using Coalgebra.sum_smul_counit (ℛ R x)

/-- Applying strong right invariance to a normalized right integral yields the antipode:
`∑ φ (t₁ * x) • t₂ = S(x)`. -/
theorem IsRightCointegral.sum_apply_mul_smul_eq_antipode {φ : Module.Dual R H}
    (hφ : IsRightCointegral φ) {t : H} (ht : t ∈ rightIntegral R H) (htφ : φ t = 1)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (r.left i * x) • r.right i = HopfAlgebra.antipode R x := by
  classical
  rw [(LinearMap.isRightInvariantIntegral_iff_isRightCointegral.mpr hφ).strong_invariance
    r (ℛ R x)]
  simpa only [apply_mul_of_mem_rightIntegral ht htφ, ← map_smul, ← map_sum] using
    congrArg (HopfAlgebra.antipode R) (Coalgebra.sum_counit_smul (ℛ R x))

/-- Applying strong left invariance to a normalized left integral yields the antipode:
`∑ φ (x * t₂) • t₁ = S(x)`. -/
theorem IsLeftCointegral.sum_apply_mul_smul_eq_antipode {φ : Module.Dual R H}
    (hφ : IsLeftCointegral φ) {t : H} (ht : t ∈ leftIntegral R H) (htφ : φ t = 1)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (x * r.right i) • r.left i = HopfAlgebra.antipode R x := by
  classical
  rw [(LinearMap.isLeftInvariantIntegral_iff_isLeftCointegral.mpr hφ).strong_invariance
    r (ℛ R x)]
  simpa only [apply_mul_of_mem_leftIntegral ht htφ, ← map_smul, ← map_sum] using
    congrArg (HopfAlgebra.antipode R) (Coalgebra.sum_smul_counit (ℛ R x))

/-- Reconstruction from a right cointegral and a normalized right integral using the inverse
antipode: `∑ φ (t₁ * x) • S⁻¹(t₂) = x`. -/
theorem IsRightCointegral.sum_apply_mul_smul_inverseAntipode {φ : Module.Dual R H}
    (hφ : IsRightCointegral φ) {t : H} (ht : t ∈ rightIntegral R H) (htφ : φ t = 1)
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H))
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (r.left i * x) • TauCeti.HopfAlgebra.inverseAntipode hS (r.right i) = x := by
  have h := congrArg (TauCeti.HopfAlgebra.inverseAntipode hS)
    (hφ.sum_apply_mul_smul_eq_antipode ht htφ r x)
  simpa only [map_sum, map_smul, TauCeti.HopfAlgebra.inverseAntipode_antipode] using h

/-- Reconstruction from a left cointegral and a normalized left integral using the inverse
antipode: `∑ φ (x * t₂) • S⁻¹(t₁) = x`. -/
theorem IsLeftCointegral.sum_apply_mul_smul_inverseAntipode {φ : Module.Dual R H}
    (hφ : IsLeftCointegral φ) {t : H} (ht : t ∈ leftIntegral R H) (htφ : φ t = 1)
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H))
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (x * r.right i) • TauCeti.HopfAlgebra.inverseAntipode hS (r.left i) = x := by
  have h := congrArg (TauCeti.HopfAlgebra.inverseAntipode hS)
    (hφ.sum_apply_mul_smul_eq_antipode ht htφ r x)
  simpa only [map_sum, map_smul, TauCeti.HopfAlgebra.inverseAntipode_antipode] using h

private theorem IsRightCointegral.sum_apply_antipode_mul_smul_eq {φ : Module.Dual R H}
    (hφ : IsRightCointegral φ) {t : H} (ht : t ∈ leftIntegral R H)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (y : H) :
    ∑ i ∈ r.index, φ (HopfAlgebra.antipode R (r.right i) * y) • r.left i =
      φ (HopfAlgebra.antipode R t) • y := by
  have hcomp := (LinearMap.isRightInvariantIntegral_iff_isRightCointegral.mpr hφ).comp_antipode
  have hrid (z : H ⊗[R] H) :
      TensorProduct.rid R H (φ.lTensor H ((LinearMap.mulLeft R y).rTensor H z)) =
        y * TensorProduct.rid R H (φ.lTensor H z) := by
    induction z using TensorProduct.inductionOn with
    | add u v hu hv => simp [map_add, mul_add, hu, hv]
    | tmul a b => simp
  have hL :
      TensorProduct.rid R H (φ.lTensor H ((LinearMap.mulLeft R y).rTensor H
        ((HopfAlgebra.antipode R).lTensor H (Coalgebra.comul (R := R) t)))) =
        φ (HopfAlgebra.antipode R t) • y := by
    rw [hrid, ← LinearMap.lTensor_comp_apply, (LinearMap.isLeftInvariantIntegral_iff.mp hcomp) t]
    simp [Algebra.smul_def, Algebra.commutes]
  have hR :
      TensorProduct.rid R H (φ.lTensor H
        (((LinearMap.mulRight R y ∘ₗ HopfAlgebra.antipode R).lTensor H)
          (Coalgebra.comul (R := R) t))) =
        ∑ i ∈ r.index, φ (HopfAlgebra.antipode R (r.right i) * y) • r.left i := by
    rw [← r.eq]
    simp [map_sum]
  rw [← hR, ← rTensor_mulLeft_lTensor_antipode_comul_of_mem_leftIntegral ht y, hL]

/-- For a right cointegral `φ` and a left integral `t` such that `φ t` is a unit,
`φ (S t) = φ t`. -/
theorem IsRightCointegral.apply_antipode_of_mem_leftIntegral {φ : Module.Dual R H}
    (hφ : IsRightCointegral φ) {t : H} (ht : t ∈ leftIntegral R H) (hu : IsUnit (φ t)) :
    φ (HopfAlgebra.antipode R t) = φ t := by
  classical
  let r := ℛ R t
  have hLHS : ∑ i ∈ r.index, φ (HopfAlgebra.antipode R (r.right i) * t) • r.left i =
      φ t • t := by
    calc ∑ i ∈ r.index, φ (HopfAlgebra.antipode R (r.right i) * t) • r.left i
        = ∑ i ∈ r.index, φ (Coalgebra.counit (R := R) (r.right i) • t) • r.left i := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [(mem_leftIntegral_iff.mp ht) _, HopfAlgebra.counit_antipode]
      _ = φ t • ∑ i ∈ r.index, Coalgebra.counit (R := R) (r.right i) • r.left i := by
          simp [smul_smul, mul_comm, Finset.smul_sum]
      _ = φ t • t := by rw [Coalgebra.sum_smul_counit r]
  have hφ_eq := congrArg φ (hLHS.symm.trans (hφ.sum_apply_antipode_mul_smul_eq ht r t))
  simp only [map_smul, smul_eq_mul] at hφ_eq
  exact hu.mul_right_cancel hφ_eq.symm

/-- Dual-basis partner of `IsRightCointegral.sum_apply_mul_smul_antipode`: for a right cointegral
`φ` and a left integral `t` with `φ t = 1`, `∑ φ (S(t₂) * x) • t₁ = x`. -/
theorem IsRightCointegral.sum_apply_antipode_mul_smul {φ : Module.Dual R H}
    (hφ : IsRightCointegral φ) {t : H} (ht : t ∈ leftIntegral R H) (htφ : φ t = 1)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (HopfAlgebra.antipode R (r.right i) * x) • r.left i = x := by
  have hSt : φ (HopfAlgebra.antipode R t) = 1 :=
    (hφ.apply_antipode_of_mem_leftIntegral ht (htφ ▸ isUnit_one)).trans htφ
  simpa [hSt] using hφ.sum_apply_antipode_mul_smul_eq ht r x

/-- Dual-basis partner of `IsLeftCointegral.sum_apply_mul_smul_antipode`: for a left cointegral
`φ` and a right integral `t` with `φ t = 1`, `∑ φ (x * S(t₁)) • t₂ = x`. -/
theorem IsLeftCointegral.sum_apply_mul_antipode_smul {φ : Module.Dual R H}
    (hφ : IsLeftCointegral φ) {t : H} (ht : t ∈ rightIntegral R H) (htφ : φ t = 1)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (x * HopfAlgebra.antipode R (r.left i)) • r.right i = x := by
  let f : (Coop H)ᵐᵒᵖ ≃ₗ[R] H := Coop.unopLinearEquiv R H
  let φ' : Module.Dual R (Coop H)ᵐᵒᵖ := φ ∘ₗ f.toLinearMap
  have hφ' : IsRightCointegral φ' := hφ.opCoop
  have ht' : f.symm t ∈ leftIntegral R (Coop H)ᵐᵒᵖ := by simpa [f] using ht
  have htφ' : φ' (f.symm t) = 1 := by simpa [φ'] using htφ
  have hres := congrArg f (hφ'.sum_apply_antipode_mul_smul ht' htφ' r.coop.op (f.symm x))
  simpa [f, φ', map_sum, map_smul, ← MulOpposite.op_mul, ← Coop.mk_mul] using hres

/-- Dual-basis partner of `IsRightCointegral.sum_apply_mul_smul_inverseAntipode`: for a right
cointegral `φ` and a right integral `t` with `φ t = 1`, `∑ φ (x * S⁻¹(t₂)) • t₁ = x`. -/
theorem IsRightCointegral.sum_apply_mul_inverseAntipode_smul {φ : Module.Dual R H}
    (hφ : IsRightCointegral φ) {t : H} (ht : t ∈ rightIntegral R H) (htφ : φ t = 1)
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H))
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (x * TauCeti.HopfAlgebra.inverseAntipode hS (r.right i)) • r.left i = x := by
  let _ := MulOpposite.hopfAlgebra hS
  let φ' : Module.Dual R Hᵐᵒᵖ := φ ∘ₗ (MulOpposite.opLinearEquiv R).symm.toLinearMap
  have hφ' : IsRightCointegral φ' := hφ.op
  have ht' : MulOpposite.op t ∈ leftIntegral R Hᵐᵒᵖ := by simpa using ht
  have htφ' : φ' (MulOpposite.op t) = 1 := by simpa [φ'] using htφ
  have hres := congrArg MulOpposite.unop
    (hφ'.sum_apply_antipode_mul_smul ht' htφ' r.op (MulOpposite.op x))
  simpa [φ', map_sum, map_smul, ← MulOpposite.op_mul,
    MulOpposite.antipode_op_hopfAlgebra hS] using hres

/-- Dual-basis partner of `IsLeftCointegral.sum_apply_mul_smul_inverseAntipode`: for a left
cointegral `φ` and a left integral `t` with `φ t = 1`, `∑ φ (S⁻¹(t₁) * x) • t₂ = x`. -/
theorem IsLeftCointegral.sum_apply_inverseAntipode_mul_smul {φ : Module.Dual R H}
    (hφ : IsLeftCointegral φ) {t : H} (ht : t ∈ leftIntegral R H) (htφ : φ t = 1)
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H))
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (TauCeti.HopfAlgebra.inverseAntipode hS (r.left i) * x) • r.right i = x := by
  let _ := MulOpposite.hopfAlgebra hS
  let φ' : Module.Dual R Hᵐᵒᵖ := φ ∘ₗ (MulOpposite.opLinearEquiv R).symm.toLinearMap
  have hφ' : IsLeftCointegral φ' := hφ.op
  have ht' : MulOpposite.op t ∈ rightIntegral R Hᵐᵒᵖ := by simpa using ht
  have htφ' : φ' (MulOpposite.op t) = 1 := by simpa [φ'] using htφ
  have hres := congrArg MulOpposite.unop
    (hφ'.sum_apply_mul_antipode_smul ht' htφ' r.op (MulOpposite.op x))
  simpa [φ', map_sum, map_smul, ← MulOpposite.op_mul,
    MulOpposite.antipode_op_hopfAlgebra hS] using hres

end Semiring

end TauCeti

