/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.OrzechProperty
public import TauCeti.Algebra.HopfAlgebra.Integral
public import TauCeti.Algebra.HopfAlgebra.InverseAntipode
import TauCeti.LinearAlgebra.BilinearForm.Dual.Reconstruction

/-!
# Basis-free Frobenius dual-basis reconstruction from integrals and cointegrals

Over an arbitrary commutative semiring (and for the partner formulas, over any commutative semiring
satisfying `OrzechProperty`, such as any commutative ring or finite commutative semiring),
normalized integrals and cointegrals on a Hopf algebra `H` satisfy explicit basis-free Frobenius
dual-basis reconstruction formulas without assuming finite-dimensionality or a base field.

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
  a commutative semiring satisfying `OrzechProperty` via
  `LinearMap.BilinForm.sum_apply_smul_eq_of_forall`.

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. 91 (1969), 75–94.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, AMS, 1993, Chapter 2.
* D. Fischman, S. Montgomery, and H.-J. Schneider, *Frobenius extensions of subalgebras of Hopf
  algebras*, Trans. Amer. Math. Soc. 349 (1997), 4857–4895, Lemma 1.5.
-/

public section

open scoped Coalgebra

namespace TauCeti

universe u v

section Semiring

variable {R : Type u} {H : Type v} [CommSemiring R] [Semiring H] [HopfAlgebra R H]

/-- Reconstruction from a right cointegral and a normalized left integral:
`∑ φ (x * t₁) • S(t₂) = x`. -/
theorem IsRightCointegral.sum_apply_mul_smul_antipode {φ : Module.Dual R H}
    (hφ : IsRightCointegral φ) {t : H} (ht : t ∈ leftIntegral R H) (htφ : φ t = 1)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (x * r.left i) • HopfAlgebra.antipode R (r.right i) = x := by
  classical
  have hxt (y : H) : φ (y * t) = Coalgebra.counit (R := R) y := by
    simp [(mem_leftIntegral_iff.mp ht) y, htφ]
  rw [← (LinearMap.isRightInvariantIntegral_iff_isRightCointegral.mpr hφ).strong_invariance
    (ℛ R x) r]
  simpa only [hxt] using Coalgebra.sum_counit_smul (ℛ R x)

/-- Reconstruction from a left cointegral and a normalized right integral:
`∑ φ (t₂ * x) • S(t₁) = x`. -/
theorem IsLeftCointegral.sum_apply_mul_smul_antipode {φ : Module.Dual R H}
    (hφ : IsLeftCointegral φ) {t : H} (ht : t ∈ rightIntegral R H) (htφ : φ t = 1)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (r.right i * x) • HopfAlgebra.antipode R (r.left i) = x := by
  classical
  have htx (y : H) : φ (t * y) = Coalgebra.counit (R := R) y := by
    simp [(mem_rightIntegral_iff.mp ht) y, htφ]
  rw [← (LinearMap.isLeftInvariantIntegral_iff_isLeftCointegral.mpr hφ).strong_invariance
    (ℛ R x) r]
  simpa only [htx] using Coalgebra.sum_smul_counit (ℛ R x)

/-- Applying strong right invariance to a normalized right integral yields the antipode:
`∑ φ (t₁ * x) • t₂ = S(x)`. -/
theorem IsRightCointegral.sum_apply_mul_smul_eq_antipode {φ : Module.Dual R H}
    (hφ : IsRightCointegral φ) {t : H} (ht : t ∈ rightIntegral R H) (htφ : φ t = 1)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (r.left i * x) • r.right i = HopfAlgebra.antipode R x := by
  classical
  have htx (y : H) : φ (t * y) = Coalgebra.counit (R := R) y := by
    simp [(mem_rightIntegral_iff.mp ht) y, htφ]
  rw [(LinearMap.isRightInvariantIntegral_iff_isRightCointegral.mpr hφ).strong_invariance
    r (ℛ R x)]
  simpa only [htx, ← map_smul, ← map_sum] using
    congrArg (HopfAlgebra.antipode R) (Coalgebra.sum_counit_smul (ℛ R x))

/-- Applying strong left invariance to a normalized left integral yields the antipode:
`∑ φ (x * t₂) • t₁ = S(x)`. -/
theorem IsLeftCointegral.sum_apply_mul_smul_eq_antipode {φ : Module.Dual R H}
    (hφ : IsLeftCointegral φ) {t : H} (ht : t ∈ leftIntegral R H) (htφ : φ t = 1)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (x * r.right i) • r.left i = HopfAlgebra.antipode R x := by
  classical
  have hxt (y : H) : φ (y * t) = Coalgebra.counit (R := R) y := by
    simp [(mem_leftIntegral_iff.mp ht) y, htφ]
  rw [(LinearMap.isLeftInvariantIntegral_iff_isLeftCointegral.mpr hφ).strong_invariance
    r (ℛ R x)]
  simpa only [hxt, ← map_smul, ← map_sum] using
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

end Semiring

section Orzech

variable {R : Type u} {H : Type v} [CommSemiring R] [OrzechProperty R] [Semiring H]
  [HopfAlgebra R H]

/-- Dual-basis partner of `IsRightCointegral.sum_apply_mul_smul_antipode`: for a right cointegral
`φ` and a left integral `t` with `φ t = 1`, `∑ φ (S(t₂) * x) • t₁ = x`. -/
theorem IsRightCointegral.sum_apply_antipode_mul_smul {φ : Module.Dual R H}
    (hφ : IsRightCointegral φ) {t : H} (ht : t ∈ leftIntegral R H) (htφ : φ t = 1)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (HopfAlgebra.antipode R (r.right i) * x) • r.left i = x :=
  LinearMap.BilinForm.sum_apply_smul_eq_of_forall ((LinearMap.mul R H).flip.compr₂ φ)
    r.index r.left (fun i ↦ HopfAlgebra.antipode R (r.right i))
    (hφ.sum_apply_mul_smul_antipode ht htφ r) x

/-- Dual-basis partner of `IsLeftCointegral.sum_apply_mul_smul_antipode`: for a left cointegral
`φ` and a right integral `t` with `φ t = 1`, `∑ φ (x * S(t₁)) • t₂ = x`. -/
theorem IsLeftCointegral.sum_apply_mul_antipode_smul {φ : Module.Dual R H}
    (hφ : IsLeftCointegral φ) {t : H} (ht : t ∈ rightIntegral R H) (htφ : φ t = 1)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (x * HopfAlgebra.antipode R (r.left i)) • r.right i = x :=
  LinearMap.BilinForm.sum_apply_smul_eq_of_forall ((LinearMap.mul R H).compr₂ φ)
    r.index r.right (fun i ↦ HopfAlgebra.antipode R (r.left i))
    (hφ.sum_apply_mul_smul_antipode ht htφ r) x

/-- Dual-basis partner of `IsRightCointegral.sum_apply_mul_smul_inverseAntipode`: for a right
cointegral `φ` and a right integral `t` with `φ t = 1`, `∑ φ (x * S⁻¹(t₂)) • t₁ = x`. -/
theorem IsRightCointegral.sum_apply_mul_inverseAntipode_smul {φ : Module.Dual R H}
    (hφ : IsRightCointegral φ) {t : H} (ht : t ∈ rightIntegral R H) (htφ : φ t = 1)
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H))
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (x * TauCeti.HopfAlgebra.inverseAntipode hS (r.right i)) • r.left i = x :=
  LinearMap.BilinForm.sum_apply_smul_eq_of_forall ((LinearMap.mul R H).compr₂ φ)
    r.index r.left (fun i ↦ TauCeti.HopfAlgebra.inverseAntipode hS (r.right i))
    (hφ.sum_apply_mul_smul_inverseAntipode ht htφ hS r) x

/-- Dual-basis partner of `IsLeftCointegral.sum_apply_mul_smul_inverseAntipode`: for a left
cointegral `φ` and a left integral `t` with `φ t = 1`, `∑ φ (S⁻¹(t₁) * x) • t₂ = x`. -/
theorem IsLeftCointegral.sum_apply_inverseAntipode_mul_smul {φ : Module.Dual R H}
    (hφ : IsLeftCointegral φ) {t : H} (ht : t ∈ leftIntegral R H) (htφ : φ t = 1)
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H))
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (TauCeti.HopfAlgebra.inverseAntipode hS (r.left i) * x) • r.right i = x :=
  LinearMap.BilinForm.sum_apply_smul_eq_of_forall ((LinearMap.mul R H).flip.compr₂ φ)
    r.index r.right (fun i ↦ TauCeti.HopfAlgebra.inverseAntipode hS (r.left i))
    (hφ.sum_apply_mul_smul_inverseAntipode ht htφ hS r) x

end Orzech

end TauCeti
